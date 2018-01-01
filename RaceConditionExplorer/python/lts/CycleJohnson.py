# The elementary circuit detection algorithm presented by Johnson.

# TODO: excludes self loops. Is by definition also an elementary circuit.
# TODO: excludes duplicate edges.


class Vertex:

    def __init__(self, index, edges_to):
        self.index = index
        self.edges_to = edges_to
        self.is_blocked = False
        self.blocks = set()

    def __eq__(self, other):
        return self.index == other.index if isinstance(self, other.__class__) else False

    def __ne__(self, other):
        return not self.__eq__(other) if isinstance(self, other.__class__) else True

    def __hash__(self):
        return hash(self.index)

    def block_self(self):
        self.is_blocked = True

    def block_other(self, v):
        self.blocks.append(v)

    def reset_block(self):
        self.is_blocked = False
        self.blocks = set()

    def unblock(self):
        self.is_blocked = False

        for v in self.blocks:
            self.blocks.remove(v)

            if v.is_blocked:
                v.unblock()

    def circuit(self, stack, found_circuits):
        has_circuit = False

        stack.append(self)
        self.block_self()

        for v in self.edges_to:
            if v is self:
                # A circuit has been found.
                found_circuits.append(stack[:])
                has_circuit = True
            elif not v.is_blocked:
                # If the next vertex is not blocked, continue.
                if v.circuit(stack, found_circuits):
                    # Somewhere on the path a circuit has been found.
                    has_circuit = True

        if has_circuit:
            self.unblock()
        else:
            for v in self.edges_to:
                v.block_other.append(self)

        stack.pop()
        return has_circuit


def findCycles(graph):
    # TODO: does the order of the vertices matter?
    v_order = graph.keys()
    n = len(v_order)

    cycles = []

    stack = []
    s = 1

    while s < n:
        # TODO: how to compute?
        strong_component = []

        if strong_component is not None:
            s = s # TODO: least vertex of strong_component?

            for v in strong_component:
                v.reset_block()

            _ = s.circuit(stack, cycles)
            s += 1
        else:
            s = n

    return cycles
