# The elementary circuit detection algorithm presented by Johnson.


class Vertex:
    """
    This class represents a vertex of a graph.
    It can be blocked as defined by Johnson's algorithm to find the elementary circuits.
    """

    def __init__(self, id):
        self.id = id
        self.is_blocked = False
        self.blocks = set()

    def __eq__(self, other):
        return self.id == other.id if isinstance(self, other.__class__) else False

    def __ne__(self, other):
        return not self.__eq__(other) if isinstance(self, other.__class__) else True

    def __hash__(self):
        return hash(self.id)

    def __str__(self):
        return str(self.id)

    def block_self(self):
        """Indicate that this vertex is blocked."""
        self.is_blocked = True

    def block_other(self, v):
        """Indicate that the provided vertex is blocked by this vertex."""
        self.blocks.add(v)

    def reset_block(self):
        """Resets the blocking caused by this vertex."""
        self.is_blocked = False
        self.blocks = set()

    def unblock(self):
        """Unblocks this vertex along with any other vertex that may have been blocked by this one."""
        self.is_blocked = False

        for v in self.blocks:
            if v.is_blocked:
                v.unblock()

        self.blocks.clear()


class Graph:
    """
    The class represents a graph in the elementary circuit algorithm presented by Johnson.
    """

    def __init__(self, dependency_graph):
        self.vertices = []
        self.edges_outgoing = {}
        self.edges_incoming = {}

        _vertices = {}

        for src, outgoing in dependency_graph.items():
            v = _vertices.get(src, Vertex(src))

            if src not in _vertices:
                # The source vertex is not yet defined, define it.
                _vertices[src] = v
                self.vertices.append(v)

                # Initialize its edge collections.
                self.edges_outgoing[v] = []
                self.edges_incoming[v] = []

            for tgt, labels in outgoing.items():
                w = _vertices.get(tgt, Vertex(tgt))

                if tgt not in _vertices:
                    # The target vertex is not yet defined, define it.
                    _vertices[tgt] = w
                    self.vertices.append(w)

                    # Initialize its edge collections.
                    self.edges_outgoing[w] = []
                    self.edges_incoming[w] = []

                # Define the edge in the graph.
                self.edges_outgoing[v].append(w)
                self.edges_incoming[w].append(v)

    def __len__(self):
        return len(self.vertices)

    def start(self):
        """Returns the start vertex (smallest index) of the graph."""
        return self.vertices[0] if len(self.vertices) > 0 else None

    def reset_block(self):
        """Resets the block of all vertices in the graph."""
        for i in range(0, len(self)):
            self.vertices[i].reset_block()

    def remove_vertex(self, v):
        """Removes the vertex from the graph along with any edges from- and to that vertex."""
        self.vertices.remove(v)

        for w in self.edges_outgoing[v]:
            self.edges_incoming[w].remove(v)
        del self.edges_outgoing[v]

        for w in self.edges_incoming[v]:
            self.edges_outgoing[w].remove(v)
        del self.edges_incoming[v]

    def pop_start(self):
        """Removes the start vertex from the graph and returns it."""
        s = self.start()
        self.remove_vertex(s)
        return s

    def circuit(self):
        """Returns the circuits of the graph that start at the `start' vertex."""

        # Initializes the stack that keeps track of the currently traversed path.
        stack = []

        # Keeps track of the found circuits.
        found_circuits = []

        def _circuit(v):
            has_circuit = False

            stack.append(v)
            v.block_self()

            # Check every vertex that can be reached directly from the current vertex.
            for w in self.edges_outgoing[v]:
                if w is self.start():
                    # A circuit has been found.
                    circuit = stack[:] + [self.start()]
                    found_circuits.append(circuit)

                    has_circuit = True
                elif not w.is_blocked:
                    # If the next vertex is not blocked, continue recursively.
                    if _circuit(w):
                        # Somewhere on the path a circuit has been found.
                        has_circuit = True

            if has_circuit:
                v.unblock()
            else:
                for w in self.edges_outgoing[v]:
                    w.block_other(v)

            _ = stack.pop()
            return has_circuit

        # Call the recursive function.
        _ = _circuit(self.start())

        return found_circuits


def findCircuits(dependency_graph):
    """
    Finds and returns the collection of elementary circuits in the dependency_graph. An elementary circuit is a sequence
    of vertices that together specify a sequential path through the dependency_graph such that the first and last vertex
    are the same.
    """

    # The collection of circuits that have been found.
    circuits = []

    # Construct a graph instance from the provided dependency graph.
    graph = Graph(dependency_graph)

    while len(graph) > 0:

        # Remove the blockage of all the vertices in the graph.
        graph.reset_block()

        # Get the circuits in the graph.
        circuits += graph.circuit()

        # Pop the start/lowest vertex from the graph and remove any edges to/from that vertex.
        _ = graph.pop_start()

    return [[vertex.id for vertex in circuit] for circuit in circuits]
