#include <iostream>
#include <queue>
#include <set>
#include <math.h>
#include<fstream>
#include <iomanip>  

#include <GL/glut.h>

using namespace std;

// Notation for working with points
typedef pair<double, double> point;
#define x first
#define y second

// Arc, event, and segment datatypes
struct arc;
struct seg;

struct event
{
	double x;
	point p;
	arc *a;
	bool valid;

	event(double xx, point pp, arc *aa)
		: x(xx), p(pp), a(aa), valid(true) {}
};

struct arc
{
	point p;
	arc *prev, *next;
	event *e;

	seg *s0, *s1;

	arc(point pp, arc *a = 0, arc *b = 0)
		: p(pp), prev(a), next(b), e(0), s0(0), s1(0) {}
};

vector<seg*> output;  // Array of output segments.

struct seg
{
	point start, end;
	bool done;

	seg(point p)
		: start(p), end(0, 0), done(false)
	{
		output.push_back(this);
	}

	// Set the end point and mark as "done."
	void finish(point p) { if (done) return; end = p; done = true; }
};

arc *root = 0; // First item in the parabolic front linked list.


// "Greater than" comparison, for reverse sorting in priority queue.
struct gt
{
	bool operator()(point a, point b) { return a.x == b.x ? a.y>b.y : a.x>b.x; }
	bool operator()(event *a, event *b) { return a->x>b->x; }
};

// Bounding box coordinates.
double box_x0 = 0, box_x1 = 0, box_y0 = 0, box_y1 = 0;

priority_queue<point, vector<point>, gt> sites; // site events
priority_queue<point, vector<point>, gt> sites_1; // site events
priority_queue<event*, vector<event*>, gt> circles; // circle events

// Find the rightmost point on the circle through a,b,c.
bool circle(point a, point b, point c, double *x, point *o)
{
	// Check that bc is a "right turn" from ab.
	if ((b.x - a.x)*(c.y - a.y) - (c.x - a.x)*(b.y - a.y) > 0)
		return false;

	// Algorithm from O'Rourke 2ed p. 189.
	double A = b.x - a.x, B = b.y - a.y,
		C = c.x - a.x, D = c.y - a.y,
		E = A*(a.x + b.x) + B*(a.y + b.y),
		F = C*(a.x + c.x) + D*(a.y + c.y),
		G = 2 * (A*(c.y - b.y) - B*(c.x - b.x));

	if (G == 0) return false;  // Points are co-linear.

	// Point o is the center of the circle.
	o->x = (D*E - B*F) / G;
	o->y = (A*F - C*E) / G;

	// o.x plus radius equals max x coordinate.
	*x = o->x + sqrt(pow(a.x - o->x, 2) + pow(a.y - o->y, 2));
	return true;
}

// Look for a new circle event for arc i.
void check_circle_event(arc *i, double x0)
{
	// Invalidate any old event.
	if (i->e && i->e->x != x0)
		i->e->valid = false;
	i->e = NULL;

	if (!i->prev || !i->next)
		return;

	double x;
	point o;

	if (circle(i->prev->p, i->p, i->next->p, &x, &o) && x > x0)
	{
		// Create new event.
		i->e = new event(x, o, i);
		circles.push(i->e);
	}
}


// Where do two parabolas intersect?
point intersection(point p0, point p1, double l)
{
	point res, p = p0;

	double z0 = 2 * (p0.x - l);
	double z1 = 2 * (p1.x - l);

	if (p0.x == p1.x)
		res.y = (p0.y + p1.y) / 2;
	else if (p1.x == l)
		res.y = p1.y;
	else if (p0.x == l)
	{
		res.y = p0.y;
		p = p1;
	}
	else
	{
		// Use the quadratic formula.
		double a = 1 / z0 - 1 / z1;
		double b = -2 * (p0.y / z0 - p1.y / z1);
		double c = (p0.y*p0.y + p0.x*p0.x - l*l) / z0
			- (p1.y*p1.y + p1.x*p1.x - l*l) / z1;

		res.y = (-b - sqrt(b*b - 4 * a*c)) / (2 * a);
	}
	// Plug back into one of the parabola equations.
	res.x = (p.x*p.x + (p.y - res.y)*(p.y - res.y) - l*l) / (2 * p.x - 2 * l);
	return res;
}



// Will a new parabola at point p intersect with arc i?
bool intersect(point p, arc *i, point *result)
{
	if (i->p.x == p.x) return false;

	double a, b;
	if (i->prev) // Get the intersection of i->prev, i.
		a = intersection(i->prev->p, i->p, p.x).y;
	if (i->next) // Get the intersection of i->next, i.
		b = intersection(i->p, i->next->p, p.x).y;

	if ((!i->prev || a <= p.y) && (!i->next || p.y <= b))
	{
		result->y = p.y;

		result->x = (i->p.x*i->p.x + (i->p.y - result->y)*(i->p.y - result->y) - p.x*p.x)
			/ (2 * i->p.x - 2 * p.x);

		return true;
	}
	return false;
}

void front_insert(point p)
{
	if (!root) {
		root = new arc(p);
		return;
	}

	// Find the current arc(s) at height p.y (if there are any).
	for (arc *i = root; i; i = i->next) {
		point z, zz;
		if (intersect(p, i, &z))
		{
			// New parabola intersects arc i.  If necessary, duplicate i.
			if (i->next && !intersect(p, i->next, &zz))
			{
				i->next->prev = new arc(i->p, i, i->next);
				i->next = i->next->prev;
			}
			else i->next = new arc(i->p, i);
			i->next->s1 = i->s1;

			// Add p between i and i->next.
			i->next->prev = new arc(p, i, i->next);
			i->next = i->next->prev;

			i = i->next; // Now i points to the new arc.

			// Add new half-edges connected to i's endpoints.
			i->prev->s1 = i->s0 = new seg(z);
			i->next->s0 = i->s1 = new seg(z);

			// Check for new circle events around the new arc:
			check_circle_event(i, p.x);
			check_circle_event(i->prev, p.x);
			check_circle_event(i->next, p.x);

			return;
		}
	}

	// Special case: If p never intersects an arc, append it to the list.
	arc *i;
	for (i = root; i->next; i = i->next); // Find the last node.

	i->next = new arc(p, i);
	// Insert segment between p and i
	point start;
	start.x = box_x0;
	start.y = (i->next->p.y + i->p.y) / 2;
	i->s1 = i->next->s0 = new seg(start);
}

void site_event()
{
	// Get the next point from the queue.
	point p = sites.top();
	sites.pop();

	// Add a new arc to the parabolic front.
	front_insert(p);
}


void circle_event()
{
	// Get the next event from the queue.
	event *e = circles.top();
	circles.pop();

	if (e->valid) {
		// Start a new edge.
		seg *s = new seg(e->p);

		// Remove the associated arc from the front.
		arc *a = e->a;
		if (a->prev)
		{
			a->prev->next = a->next;
			a->prev->s1 = s;
		}
		if (a->next)
		{
			a->next->prev = a->prev;
			a->next->s0 = s;
		}

		// Finish the edges before and after a.
		if (a->s0) a->s0->finish(e->p);
		if (a->s1) a->s1->finish(e->p);

		// Recheck circle events on either side of p:
		if (a->prev) check_circle_event(a->prev, e->x);
		if (a->next) check_circle_event(a->next, e->x);
	}
	delete e;
}


void finish_edges()
{
	// Advance the sweep line so no parabolas can cross the bounding box.
	double l = box_x1 + (box_x1 - box_x0) + (box_y1 - box_y0);

	// Extend each remaining segment to the new parabola intersections.
	for (arc *i = root; i->next; i = i->next)
		if (i->s1) i->s1->finish(intersection(i->p, i->next->p, l * 2));
}

void print_output()
{
	// Bounding box coordinates.
	cout << "Bounding box coordinates : " << endl;
	cout << box_x0 << " " << box_x1 << " " << box_y0 << " " << box_y1 << endl;

	// Each output segment in four-column format.
	vector<seg*>::iterator i;
	for (i = output.begin(); i != output.end(); i++)
	{
		point p0 = (*i)->start;
		point p1 = (*i)->end;
		cout << setprecision(2) << fixed << "(" << p0.x << "," << p0.y << ")     (" << p1.x << "," << p1.y << ")" << endl;
	}
}

void Voronoi()
{
	ifstream fin("input.txt");
	cout << "-------------Voronoi Diagram-------------\n";
	int N;
	fin >> N;
	for (int i = 0; i<N; i++)
	{
		point p;
		fin >> p.x >> p.y;

		sites.push(p);

		if (p.x < box_x0) box_x0 = p.x;
		if (p.y < box_y0) box_y0 = p.y;
		if (p.x > box_x1) box_x1 = p.x;
		if (p.y > box_y1) box_y1 = p.y;
	}
	sites_1 = sites;

	double dx = (box_x1 - box_x0 + 1) / 5.0; double dy = (box_y1 - box_y0 + 1) / 5.0;
	box_x0 -= dx*5; box_x1 += dx; box_y0 -= dy; box_y1 += dy;

	// Process the queues; select the top element with smaller x coordinate.
	while (!sites.empty())
		if (!circles.empty() && circles.top()->x <= sites.top().x)
			circle_event();
		else
			site_event();

	// After all points are processed, do the remaining circle events.
	while (!circles.empty()) circle_event();

	finish_edges(); // Clean up dangling edges.
	print_output(); // Output the voronoi diagram.

}

void display(void)
{
	glClear(GL_COLOR_BUFFER_BIT);
	glColor3f(255, 255, 255);

	// Each output segment in four-column format.
	vector<seg*>::iterator i;
	for (i = output.begin(); i != output.end(); i++) {
		point p0 = (*i)->start;
		point p1 = (*i)->end;
		glBegin(GL_LINES);
		glVertex2f(p0.x, p0.y);
		glVertex2f(p1.x, p1.y);
		glEnd();

	}

	glPointSize(4.0);

	glBegin(GL_POINTS);
	while (!sites_1.empty())
	{
		glVertex2f(sites_1.top().x, sites_1.top().y);
		sites_1.pop();
	}
	glEnd();

	glFlush();

}
void init(){

	/* clears the window according to RGBA */
	glClearColor(0.0, 0.0, 0.0, 0.0);

	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	//gluOrtho2D(GLdouble  left,  GLdouble  right,  GLdouble  bottom,  GLdouble  top);
	gluOrtho2D(-36 / 2.0, 100 / 2.0, -35 / 2.0, 78 / 2.0);

}

int main(int argc, char** argv)
{
	Voronoi();
	glutInit(&argc, argv);
	glutInitWindowSize(800, 600);
	glutCreateWindow("");
	init();
	glutDisplayFunc(display);
	glutMainLoop();
	return 0;
}