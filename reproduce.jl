# Reproduces every number reported for the 5/6-Poly-Density Question (arXiv:2411.06292, Q6.1).
# Run: julia -t 8 reproduce.jl > output.txt
using Base.Threads

# poly density = fractional weighted chromatic index with weights 1/f (Edmonds):
# max( max_v sum_{e∋v} 1/f_e , max_{odd S,|S|>=3} sum_{e⊆S} 1/f_e / ((|S|-1)/2) )
function polydensity(n, edges, f)
    best = 0//1
    for S in 1:(1<<n)-1
        k = count_ones(S)
        w = 0//1
        if k == 1
            v = trailing_zeros(S)
            for (i, (a, b)) in enumerate(edges)
                (a == v || b == v) && (w += 1//f[i])
            end
            best = max(best, w)
        elseif isodd(k)
            for (i, (a, b)) in enumerate(edges)
                (S >> a) & 1 == 1 && (S >> b) & 1 == 1 && (w += 1//f[i])
            end
            best = max(best, w / ((k - 1) ÷ 2))
        end
    end
    best
end

# maximal matchings as edge bitmasks
function maxmatchings(n, edges)
    m = length(edges)
    res = Int[]
    for M in 0:(1<<m)-1
        used = 0; ok = true
        for i in 1:m
            if (M >> (i-1)) & 1 == 1
                a, b = edges[i]
                if (used >> a) & 1 == 1 || (used >> b) & 1 == 1; ok = false; break; end
                used |= (1 << a) | (1 << b)
            end
        end
        ok || continue
        maximal = true
        for i in 1:m
            if (M >> (i-1)) & 1 == 0
                a, b = edges[i]
                if (used >> a) & 1 == 0 && (used >> b) & 1 == 0; maximal = false; break; end
            end
        end
        maximal && push!(res, M)
    end
    res
end

# exact feasibility: state r_e ∈ 1..f_e (days left until deadline); greatest fixed point over reachable states
function feasible(n, edges, f; maxstates = 5_000_000)
    m = length(edges)
    Ms = maxmatchings(n, edges)
    start = Tuple(f)
    succs(s) = begin
        out = NTuple{length(f),Int}[]
        for M in Ms
            ok = true
            for i in 1:m
                if s[i] == 1 && (M >> (i-1)) & 1 == 0; ok = false; break; end
            end
            ok || continue
            push!(out, ntuple(i -> (M >> (i-1)) & 1 == 1 ? f[i] : s[i] - 1, m))
        end
        out
    end
    idx = Dict(start => 1); states = [start]; adj = Vector{Vector{Int}}()
    q = 1
    while q <= length(states)
        s = states[q]; q += 1
        nb = Int[]
        for t in succs(s)
            j = get(idx, t, 0)
            if j == 0
                push!(states, t); j = length(states); idx[t] = j
                length(states) > maxstates && return missing
            end
            push!(nb, j)
        end
        push!(adj, nb)
    end
    N = length(states)
    # prune states with no surviving successor
    alive = trues(N); outdeg = [length(a) for a in adj]
    pred = [Int[] for _ in 1:N]
    for i in 1:N, j in adj[i]; push!(pred[j], i); end
    stack = [i for i in 1:N if outdeg[i] == 0]
    for i in stack; alive[i] = false; end
    while !isempty(stack)
        j = pop!(stack)
        for i in pred[j]
            if alive[i]
                outdeg[i] -= 1
                if outdeg[i] == 0; alive[i] = false; push!(stack, i); end
            end
        end
    end
    alive[1]
end


# Exhaustive frontier sweep: all connected graphs on n vertices with <= mmax edges (up to isomorphism),
# all frequency vectors in 2..F with d <= TH that are minimal (lowering any f_e pushes d above TH).
# Feasibility is monotone in f, so an infeasible instance with d <= TH (and f <= F) exists iff a frontier one does.
perms_of(v) = length(v) <= 1 ? [v] : [vcat([v[i]], p) for i in eachindex(v) for p in perms_of(deleteat!(copy(v), i))]
function sweep(n, mmax, F, TH)
    allpairs = [(a, b) for a in 0:n-1 for b in a+1:n-1]
    perms = perms_of(collect(0:n-1))
    canon(E) = minimum(sort([minmax(p[a+1], p[b+1]) for (a, b) in E]) for p in perms)
    function connected(E)
        seen = 1; ch = true
        while ch
            ch = false
            for (a, b) in E
                if ((seen >> a) & 1) ⊻ ((seen >> b) & 1) == 1; seen |= (1 << a) | (1 << b); ch = true; end
            end
        end
        seen == (1 << n) - 1
    end
    gs = Set{Vector{Tuple{Int,Int}}}()
    for mask in 0:(1<<length(allpairs))-1
        count_ones(mask) <= mmax || continue
        E = [allpairs[i] for i in eachindex(allpairs) if (mask>>(i-1))&1==1]
        connected(E) && push!(gs, canon(E))
    end
    gs = collect(gs)
    function frontier(E)
        m = length(E); out = Vector{Vector{Int}}(); f = fill(F, m)
        function rec(i)
            if i > m
                polydensity(n, E, f) <= TH || return
                for j in 1:m
                    if f[j] > 2
                        f[j] -= 1; d = polydensity(n, E, f); f[j] += 1
                        d <= TH && return
                    end
                end
                push!(out, copy(f)); return
            end
            for v in 2:F
                f[i] = v
                for j in i+1:m; f[j] = F; end   # lower bound on d over completions
                polydensity(n, E, f) <= TH || continue
                rec(i + 1)
            end
            f[i] = F
        end
        rec(1); out
    end
    lk = ReentrantLock(); tested = Atomic{Int}(0); bad = Tuple{Vector{Tuple{Int,Int}},Vector{Int}}[]
    @threads for g in gs
        for f in frontier(g)
            r = feasible(n, g, f)
            atomic_add!(tested, 1)
            r === true || lock(() -> push!(bad, (g, f)), lk)
        end
    end
    length(gs), tested[], sort(bad)
end

println("== 1. sanity checks")
K3 = [(0,1),(1,2),(0,2)]
for f in ([2,3,7], [2,4,8], [3,3,4])
    println("  triangle f=", f, "  d=", polydensity(3, K3, f), "  feasible=", feasible(3, K3, f))
end

println("== 2. gadget: triangle 0-1-2, pendants 0-3, 1-4; f(01)=X, f(02)=4, f(03)=2, f(12)=4, f(14)=2")
G = [(0,1),(0,2),(0,3),(1,2),(1,4)]
println("  maximal matchings (edge masks): ", maxmatchings(5, G))
for X in vcat(1:40, [60, 100])
    f = [X, 4, 2, 4, 2]
    d = polydensity(5, G, f)
    @assert d == 3//4 + 1//X
    r = feasible(5, G, f)
    @assert r == false
    X in (1, 2, 12, 13, 24, 40, 100) && println("  X=$X  d=$d ≈ $(round(Float64(d), digits=4))  feasible=$r")
end
println("  all X in 1..40, 60, 100: d = 3/4 + 1/X and infeasible  (d < 5/6 iff X ≥ 13)")
# primal certificate (fractional schedule) and dual weighting, exact rationals, X = 13
X = 13; f = [X, 4, 2, 4, 2]
y = Dict([1] => 1//X, [2,5] => 1//4, [3,4] => 1//4, [3,5] => 1//4)   # edges 1-based
cover = [sum(v for (M, v) in y if e in M; init = 0//1) for e in 1:5]
@assert all(cover .>= [1//fe for fe in f]) && sum(values(y)) == 3//4 + 1//X
D = 3//4 + 1//X; z = [1//(X*D), 1//(4D), 1//(2D), 0, 0]
@assert sum(z) == 1 && maximum(sum(z[e]*f[e] for e in M) for M in keys(y)) == 1/D
println("  X=13: primal certificate sum y = ", sum(values(y)), ", dual z = ", z, " both give d = ", D)
# variants: relaxing the frequency-4 edges
for (a, b) in ((4,5), (5,4), (5,5), (4,6), (6,4))
    println("  f(02)=$a f(12)=$b, f(01)=100: feasible=", feasible(5, G, [100, a, 2, b, 2]))
end

println("== 3. exhaustive frontier sweeps")
for (n, mmax, F, TH) in ((4, 6, 12, 5//6), (5, 7, 12, 5//6), (5, 7, 12, 3//4))
    ng, nt, bad = sweep(n, mmax, F, TH)
    println("  n=$n, edges<=$mmax, f<=$F, d<=$TH: $ng graphs, $nt frontier instances, $(length(bad)) infeasible")
    for (g, f) in bad[1:min(end, 5)]
        println("    e.g. ", g, " f=", f, " d=", polydensity(n, g, f))
    end
    flush(stdout)
end
