// raytracer.cpp : This file contains the 'main' function. Program execution begins and ends there.
//

#include <iostream>
#include<fstream>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <iterator>
#include "vec.h"
#include "mat.h"
#include <float.h>

#define EPSILON 1e-2

using namespace std;

string FILENAME;

struct Ray {
	vec3 o, d;
	Ray(const vec3& o, const vec3& d) : o(o), d(d) {}
};

struct Base {
	virtual vec3 getNormal(const vec3& P) const { return 0; }
	virtual bool intersect(Ray R, double& t) { return false; }
};

struct Sphere : Base {
	vec3 center;
	double radius;
	Sphere(const vec3& center, double radius) : center(center), radius(radius) {}
	vec3 getNormal(const vec3& P) const { return (P - center); }
	bool intersect(Ray R, double& t) {
		vec3 dir = center - R.o;
		double delta = pow((-2 * dot(R.d, dir)), 2) - 4 * dot(R.d, R.d) * (dot(dir, dir) - radius * radius);
		if (delta < 0)
			return false;
		double t1 = (-1 * (-2 * dot(R.d, dir)) - sqrt(delta)) / (2 * dot(R.d, R.d));
		double t2 = (-1 * (-2 * dot(R.d, dir)) + sqrt(delta)) / (2 * dot(R.d, R.d));
		if (t1 >= EPSILON && t2 >= EPSILON) {
			t = min(t1, t2);
		}
		else if (t1 >= EPSILON && t2 < EPSILON) {
			t = t1;
		}
		else if (t1 < EPSILON && t2 >= EPSILON) {
			t = t2;
		}
		else {
			return false;
		}
		return true;
	}
};

const int MAX_DEPTH = 4; // recursion depth for reflections
const long double TO_RADIANS = 3.141592653589793238L / 180.f;
const long double PI = 3.141592653589793238L;
const vec3 background_color = (0.5, 0.5, 0.5); //grey

vector<string> lines;
string outputFileName;
int nRows, nCols;
double aspectRatio;

vec3 camera, at, up;
double fovy;

int numberOfLightSource;
vector<vec3> lightPos; // light position
vector<vec3> lightIntensity; // light intensity
vector<vec3> lightCoef; // light coef (a+b*d+c*d*d)

int numP;
vector<vec3> pigments; // pigments

int numF;
vector<vector<double>> surfaces; // ambient coefficient ka, diffuse coefficient kd, specularcoefficient ks, the shininess a, reflectivity coefficient kr, refractivity coefficient kt and ior value

int numObjects;
vector<int> objectPigment;
vector<int> objectSurface;
vector<Base*> objects;
enum objType { SPHERE, TRIANGLE };
vector<objType> objectTypes;

bool visible(vec3 P, int lightIndex, int shapeHit) { // Visible(...) returns 1 if the lightIndex-th light source is visible to P, returns 0 otherwise 
	vec3 rayOrigin = lightPos[lightIndex];
	vec3 rayDirection = normalize(P - rayOrigin);
	Ray shadowRay(rayOrigin, rayDirection);

	double minT = DBL_MAX;
	int shapeHitLocal = -1;
	double t = DBL_MAX;

	for (int i = 0; i < objects.size(); i++) {
		bool hit = objects[i]->intersect(shadowRay, t);
		if (hit && t < minT + EPSILON) {
			minT = t;
			shapeHitLocal = i;
		}
	}

	vec3 newPoint = rayOrigin + minT * rayDirection;
	if (abs(newPoint.x - P.x) > EPSILON || abs(newPoint.y - P.y) > EPSILON || abs(newPoint.z - P.z) > EPSILON)
		return false;
	else if (shapeHitLocal == shapeHit)
		return true;
	else
		return false;
}

vec3 phong(int i, vec3 P, vec3 normal, int shapeHit) { // compute the local color at point P
	vec3 viewDir = normalize(camera - P); // view direction
	vec3 lightDir = normalize(lightPos[i] - P); // light direction
	vec3 h = normalize(lightDir + viewDir); // halfway vector
	double d = length(lightPos[i] - P); // length of lightDir

	vec3 diffuse = lightIntensity[i] * surfaces[objectSurface[shapeHit]][1]; // diffuse
	diffuse = diffuse * max(0.0f, dot(lightDir, normal)) * pigments[objectPigment[shapeHit]];

	vec3 specular = lightIntensity[i] * surfaces[objectSurface[shapeHit]][2]; // specular
	specular = specular * pow(max(0.0f, dot(h, normal)), surfaces[objectSurface[shapeHit]][3]);

	vec3 color = (diffuse + specular) / (lightCoef[i].x + lightCoef[i].y * d + lightCoef[i].z * d * d);
	return color;
}

Ray reflect(Ray R, vec3 P, vec3 normal) { // calculate reflected Ray
	vec3 v = normalize(-R.d);
	return Ray(P + normal * 1e-3, 2 * dot(normal, v) * normal - v);
}

Ray transmit(Ray R, vec3 P, vec3 n, int shapeHit, bool isInside, bool& isReflect) { // calculate refracted Ray
	isReflect = false;
	double ior = surfaces[objectSurface[shapeHit]][6];
	double iorRate;
	if (isInside)
		iorRate = ior;
	else
		iorRate = 1 / ior;
	vec3 v = -normalize(R.d);
	vec3 u1 = dot(v, n) * n;
	vec3 w1 = u1 - v;
	vec3 w2 = (iorRate)*w1;
	double cosTheta1 = dot(v, n);
	double sqrtInside = 1 - pow((iorRate), 2) * (1 - dot(v, n) * dot(v, n));
	double cosTheta2 = sqrt(sqrtInside);
	vec3 u2 = -(cosTheta2)*n;

	if (sqrtInside < EPSILON) { // total internal reflection
		isReflect = true;
		return reflect(R, P, n);
	}
	else {
		vec3 dir = normalize(R.d * iorRate + n * (iorRate * cosTheta1 - sqrt(sqrtInside)));
		return Ray(P - n * EPSILON, dir);
	}
}

vec3 trace(Ray R, int depth) {
	vec3 localC(0, 0, 0), reflectedC(0, 0, 0), transmittedC(0, 0, 0);
	vec3 P; vec3 normal;
	if (depth > MAX_DEPTH) return background_color;

	Sphere* sphere = NULL;
	double minT = DBL_MAX;
	double t = DBL_MAX;
	int shapeHit = -1;

	for (int i = 0; i < objects.size(); i++) { // find closest object
		bool hit = objects[i]->intersect(R, t);
		if (hit && t < minT + EPSILON) {
			minT = t;
			if (objectTypes[i] == SPHERE) {
				sphere = dynamic_cast<Sphere*>(objects[i]);
			}
			shapeHit = i;
		}
	}

	if (shapeHit == -1) { // if ray does not hit any object, returns background color
		return background_color;
	}

	P = R.o + (minT * R.d); // calculate intersected point
	if (objectTypes[shapeHit] == SPHERE)
		normal = normalize(sphere->getNormal(P));

	bool isInside = false;
	if (dot(normal, R.d) > 0) { // if Ray in inside of sphere
		normal = vec3(-normal.x, -normal.y, -normal.z);
		isInside = true;
	}

	localC.x = 0; localC.y = 0; localC.z = 0;
	vec3 ambient = lightIntensity[0] * surfaces[objectSurface[shapeHit]][0]; // ambient
	localC += ambient * pigments[objectPigment[shapeHit]];

	for (int i = 1; i < numberOfLightSource; i++) {
		if (visible(P, i, shapeHit)) {
			localC += phong(i, P, normal, shapeHit);
		}
	}

	if (surfaces[objectSurface[shapeHit]][4] > EPSILON) { // reflective surface
		Ray Rr = reflect(R, P, normal);
		reflectedC = trace(Rr, depth + 1);
	}

	if (surfaces[objectSurface[shapeHit]][5] > 0) { // tranparent  surface
		bool isReflect; false;
		Ray Rt = transmit(R, P, normal, shapeHit, isInside, isReflect);
		if (isReflect)
			reflectedC += trace(Rt, depth + 1);
		else
			transmittedC = trace(Rt, depth + 1);
	}

	return localC + surfaces[objectSurface[shapeHit]][4] * reflectedC + surfaces[objectSurface[shapeHit]][5] * transmittedC;
}

Ray generateRay(int x, int y) {
	vec3 cO = camera;
	vec3 cZ = -normalize(at - camera);
	vec3 cX = normalize(cross(up, cZ));
	vec3 cY = cross(cZ, cX);
	double h = tan(TO_RADIANS * fovy / 2);
	double w = h * aspectRatio;

	vec3 p;
	p.x = (2 * ((x + 0.5f) / nCols) - 1) * w;
	p.y = (1 - 2 * ((y + 0.5f) / nRows)) * h;
	p.z = -1;

	vec3 Pij = camera + p.x * cX + p.y * cY + p.z * cZ;
	return Ray(camera, normalize(Pij - camera));
}

void render() {
	vec3* image = new vec3[nRows * nCols];
	for (int i = 0; i < nCols; i++) {
		for (int j = 0; j < nRows; j++) {
			const Ray ray = generateRay(i, j);
			image[nRows * j + i] = trace(ray, 0);
		}
	}

	// Save result to a PPM image (keep these flags if you compile under Windows)
	std::ofstream ofs("./" + outputFileName, std::ios::out | std::ios::binary);
	ofs << "P6\n" << nRows << " " << nCols << "\n255\n";
	for (unsigned i = 0; i < nRows * nCols; ++i) {
		ofs << (unsigned char)(min(float(1), image[i].x) * 255) <<
			(unsigned char)(min(float(1), image[i].y) * 255) <<
			(unsigned char)(min(float(1), image[i].z) * 255);
	}
	ofs.close();
}

int main(int argc, char* argv[]) {
	if (argc == 1) {
		cout << "Argument Error - Input file is required" << endl;
		return 0;
	}
	else if (argc != 2) {
		cout << "Argument Error - Input file not found" << endl;
		return 0;
	}
	else {
		FILENAME = argv[1];
	}

	fstream newfile;
	newfile.open(FILENAME, ios::in); //open a file to perform read operation using file object
	if (newfile.is_open()) {   //checking whether the file is open
		string tp;
		while (getline(newfile, tp)) { //read data from file object and put it into string.
			lines.push_back(tp);
		}
		newfile.close(); //close the file object.
	}

	outputFileName = lines[0];

	nRows = stod(string(lines[1].cbegin(), find(lines[1].cbegin(), lines[1].cend(), ' ')));
	nCols = stod(lines[1].substr(lines[1].find(' ') + 1, lines[1].size()));
	aspectRatio = nRows / nCols;

	camera.x = stod(lines[2].substr(0, lines[2].find(' ')));
	camera.y = stod(lines[2].substr(lines[2].find(' '), lines[2].find_last_of(' ')));
	camera.z = stod(lines[2].substr(lines[2].find_last_of(' '), lines[2].size()));

	at.x = stod(lines[3].substr(0, lines[3].find(' ')));
	at.y = stod(lines[3].substr(lines[3].find(' '), lines[3].find_last_of(' ')));
	at.z = stod(lines[3].substr(lines[3].find_last_of(' '), lines[3].size()));

	up.x = stod(lines[4].substr(0, lines[4].find(' ')));
	up.y = stod(lines[4].substr(lines[4].find(' '), lines[2].find_last_of(' ')));
	up.z = stod(lines[4].substr(lines[4].find_last_of(' '), lines[4].size()));

	fovy = stod(lines[5]);

	int counter = 7;
	numberOfLightSource = stod(lines[6]);
	for (int i = 0; i < numberOfLightSource; i++) {
		string line = lines[counter];
		istringstream iss(line);
		vector<string> tokens;
		copy(istream_iterator<string>(iss),
			istream_iterator<string>(),
			back_inserter(tokens));

		vec3 pos; vec3 color; vec3 coef;
		pos.x = stod(tokens[0]); pos.y = stod(tokens[1]); pos.z = stod(tokens[2]);
		color.x = stod(tokens[3]); color.y = stod(tokens[4]); color.z = stod(tokens[5]);
		coef.x = stod(tokens[6]); coef.y = stod(tokens[7]); coef.z = stod(tokens[8]);
		lightPos.push_back(pos);
		lightIntensity.push_back(color);
		lightCoef.push_back(coef);
		counter++;
	}

	numP = stod(lines[counter++]);
	for (int i = 0; i < numP; i++) {
		string line = lines[counter];
		istringstream iss(line);
		vector<string> tokens;
		copy(istream_iterator<string>(iss),
			istream_iterator<string>(), back_inserter(tokens));

		if (tokens[0].compare("solid") == 0) {
			vec3 color;
			color.x = stod(tokens[1]); color.y = stod(tokens[2]); color.z = stod(tokens[3]);
			pigments.push_back(color);
		}
		counter++;
	}

	numF = stod(lines[counter++]);
	for (int i = 0; i < numF; i++) {
		string line = lines[counter];
		istringstream iss(line);
		vector<string> tokens;
		copy(istream_iterator<string>(iss),
			istream_iterator<string>(), back_inserter(tokens));

		vector<double> surface;
		surface.push_back(stod(tokens[0])); // ambient
		surface.push_back(stod(tokens[1])); // diffuse
		surface.push_back(stod(tokens[2])); // specular
		surface.push_back(stod(tokens[3])); // shininess
		surface.push_back(stod(tokens[4])); // reflectivity
		if (tokens.size() == 7) { // if refractivity is enabled
			surface.push_back(stod(tokens[5])); // kt
			surface.push_back(stod(tokens[6])); // refract n2
		}
		else {
			surface.push_back(0.0); // kt
			surface.push_back(0.0); // refract n2
		}
		surfaces.push_back(surface);
		counter++;
	}

	numObjects = stod(lines[counter++]);
	for (int i = 0; i < numObjects; i++) {
		string line = lines[counter];
		istringstream iss(line);
		vector<string> tokens;
		copy(istream_iterator<string>(iss),
			istream_iterator<string>(), back_inserter(tokens));

		objectPigment.push_back(stod(tokens[0]));
		objectSurface.push_back(stod(tokens[1]));

		if (tokens[2].compare("sphere") == 0) {
			vec3 pos;
			pos.x = stod(tokens[3]); pos.y = stod(tokens[4]); pos.z = stod(tokens[5]);
			double radius = stod(tokens[6]);

			Sphere* sphere = new Sphere(pos, radius);
			objects.push_back(sphere);
			objectTypes.push_back(SPHERE);
		}
		counter++;
	}
	render();
}