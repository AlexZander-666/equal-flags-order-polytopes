"""Derive both face lattices from integer coordinates and count codimension-three faces."""
from collections import Counter
from itertools import combinations
import json

HEXAGONAL_PYRAMID = tuple((i, i*i, 0) for i in range(6)) + ((0, 0, 1),)
TRUNCATED_BIPYRAMID = ((0,0,0), (6,0,0), (0,6,0), (2,2,-2), (1,1,1), (4,1,1), (1,4,1))

def determinant(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) + a[1]*(b[2]*c[0]-b[0]*c[2])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))

def difference(a,b):
    return tuple(x-y for x,y in zip(a,b))

def face_lattice(vertices):
    facets = set()
    for i,j,k in combinations(range(len(vertices)),3):
        a = difference(vertices[j],vertices[i])
        b = difference(vertices[k],vertices[i])
        values = [determinant(a,b,difference(x,vertices[i])) for x in vertices]
        if min(values)==0<max(values) or min(values)<0==max(values):
            facets.add(frozenset(v for v,h in enumerate(values) if h==0))
    faces = {frozenset(range(len(vertices)))}
    for facet in facets:
        faces.update([f & facet for f in faces])
    levels = sorted(faces,key=lambda f:(len(f),sorted(f)))
    covers = [(i+1,j+1) for i,a in enumerate(levels) for j,b in enumerate(levels)
              if a < b and not any(a < f < b for f in faces)]
    bottom,top = 0,len(faces)+1
    covers += [(bottom,1),(top-1,top)]
    edges = [f for f in faces if len(f)==2]
    points = [f for f in faces if len(f)==1]
    flags = [1,len(points),len(edges),len(facets),
             sum(v<e for v in points for e in edges),sum(v<f for v in points for f in facets),
             sum(e<f for e in edges for f in facets),sum(v<e<f for v in points for e in edges for f in facets)]
    return top+1,sorted(covers),flags,[sorted(f) for f in sorted(facets,key=lambda f:sorted(f))]

def add_arrow(rows,i,j):
    bit = 1 << i
    future = rows[j]
    for u,row in enumerate(rows):
        if row & bit:
            rows[u] = row | future

def count_faces(vertices):
    n,arcs,flags,facets = face_lattice(vertices)
    initial = [1<<i for i in range(n)]
    for i,j in arcs:
        add_arrow(initial,i,j)
    multiplicity = Counter()
    for triple in combinations(arcs,3):
        rows = initial.copy()
        for i,j in triple:
            add_arrow(rows,j,i)
        if rows[-1] & 1:
            continue
        # Equal rows in a reflexive transitive closure identify exactly the SCCs.
        if len(set(rows)) != n-3:
            continue
        # The same blocks determine the same quotient of the fixed initial order.
        # Equal row tuples give a canonical key for the resulting face.
        multiplicity[tuple(rows)] += 1
    return dict(facets=facets,flag_vector=flags,dimensions=[3,n-2],covers=len(arcs),
                triples=sum(multiplicity.values()),multiplicities=sorted(Counter(multiplicity.values()).items()),
                f25=len(multiplicity))

if __name__ == '__main__':
    result = [count_faces(v) for v in (HEXAGONAL_PYRAMID,TRUNCATED_BIPYRAMID)]
    assert [r['f25'] for r in result] == [35946,35944]
    assert all(r['flag_vector']==[1,7,12,7,24,24,24,48] and r['covers']==64 for r in result)
    print(json.dumps(result,indent=2))
