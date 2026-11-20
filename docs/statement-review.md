# Independent AI review of the two theorem statements

Reviewed on 20 November 2026. This review was performed by an AI agent independent of the AI agent writing the challenge. The byline for the mathematical work is Vjekoslav Kovač and Ivica Smolić. No human sign-off is represented by this review.

## Source comparison

The uploaded `RuncornConverse.tex` has SHA-256 `6f47ad0b088e8e9f8ba568d7d7c8173968f2990cb628d64dbb0ff1b88eb5371b`. I compared its definitions and theorem environments at lines 82–96 and 146–197 with §1.1–1.2 of the primary source. The theorem labels `thm:varying` and `thm:fixed` correspond to Theorems 1 and 2 respectively. The test functions, integrals, dimension split, exponent ranges, basis convention and type of convergence agree. This comparison covers the mathematical text of the two theorems. [arXiv:2607.18379v1, 20 July 2026](https://arxiv.org/abs/2607.18379v1) · [Original theorem texts](https://arxiv.org/html/2607.18379v1#S1.SS2)

## Quantifiers and domains

| Item | Meaning in both theorems |
|---|---|
| Dimension and ambient space | Any integer $n\ge2$, with the Euclidean norm and Lebesgue volume on $\mathbb R^n$. |
| Radii | Finite real numbers $0<r_-<r_+$. The endpoints belong to neither the open shell nor the interval of admissible subannulus radii. |
| Geometry | $U=\{\|x\|<r_+\}$, $V=\{r_-<\|x\|\}$, and $A_{a,b}=\{a\le\|x\|\le b\}$. |
| Tests | Every complex harmonic $u$ on all of $U$ and every complex harmonic $v$ on all of $V$, with $v(x)\to0$ as $\|x\|\to\infty$. There is no exterior condition on $u$. |
| Integrand | Multiply $f$ by $\sum_{i=1}^n (\partial_i u)(\partial_i v)$ using derivatives along real coordinate axes. The pairing is complex bilinear. |
| Constants | The tested integral equals the complex number zero. The results have no tolerance, numerical bound, implicit constant, or discretization parameter. |

### Theorem 1 — varying annuli

For each complex continuous $f$ on $U\cap V$, the following three conditions are equivalent.

1. Every admissible harmonic pair gives zero volume integral on **every** $A_{a,b}$ with $r_-<a<b<r_+$.
2. Every admissible pair gives zero integral against Euclidean surface area on **every** sphere of radius $r\in(r_-,r_+)$. In unit sphere coordinates this area is $r^{n-1}dS(\sigma)$.
3. For $n\ge3$, a single radial profile gives $f(x)=g(\|x\|)$ throughout the open shell. For $n=2$, three complex profiles continuous on $(r_-,r_+)$ give $f(r\cos t,r\sin t)=g_{-1}(r)e^{-it}+g_0(r)+g_1(r)e^{it}$ for **every** admissible radius and real angle. The positive and negative modes are independent for complex data.

In the first branch continuity of the profile follows by restricting $f$ to any ray. Both the sphere condition and the mode representation hold pointwise in the radius. Two equivalences with a common condition suffice to express the three-way equivalence.

### Theorem 2 — a fixed annulus

First choose $r_-<a<b<r_+$. For each $k\in\mathbb N$, the angular space consists of restrictions to the unit sphere of complex harmonic homogeneous polynomials on $\mathbb R^n$ of degree $k$. Choose **any** orthogonal basis $Y_{k,j}$ for that space in spherical surface measure. The basis vectors can have arbitrary nonzero norms. The index has size $d_n(0)=1$, $d_n(1)=n$, and $d_n(k)=\binom{n+k-1}{n-1}-\binom{n+k-3}{n-1}$ for $k\ge2$.

| Dimension | Degree | Set of Laurent exponents $m$ |
|---|---|---|
| All $n\ge2$ | $k=0$ | Empty |
| $n=2$ | $k=1$ | Empty |
| $n=2$ | $k\ge2$ | $2\ell-k$ for integers $0\le\ell\le k-2$ |
| $n\ge3$ | $k\ge1$ | $2\ell-k-n+2$ for integers $0\le\ell\le k-1$ |

A permissible coefficient belongs to the complex $L^2$ space with measure $r^{n-1}dr$ restricted to $[a,b]$. For **each** exponent in its row it satisfies $\int_{[a,b]}g(r)r^m r^{n-1}dr=0$. The conjugation of the second entry in the source inner product fixes the real monomial. Negative powers, including the example $m=-2$ for $(n,k)=(2,2)$, are essential. As a second check, $(n,k)=(3,1)$ has the single exponent $-2$, and $(3,2)$ has $-3,-1$.

For **every** complex $f$ in $L^2(A_{a,b},dV)$, the volume test for every admissible pair is equivalent to existence of such a coefficient for **each** $k,j$, with the finite-in-$j$ partial sums of $g_{k,j}(r)Y_{k,j}(\sigma)$ tending to $f(r\sigma)$ in annular $L^2$ as the degree cutoff tends to infinity. This allows almost-everywhere changes of representatives. No assumption of continuity, pointwise convergence, orthonormality, or decay rate is made on $f$. Equation (1.4) after Theorem 2 gives the canonical coefficient by division by the squared angular norm. A statement using only its moments requires a separate proof of annular expansion to obtain the displayed conclusion.

## Source proof checkpoints

* Lemma 3 spans every degree by powers of complex linear forms with bilinear null vector. Its reverse inclusion uses the vanishing ideal of the null quadric and Fischer orthogonality to multiples of the squared radius.
* Lemma 4 uses $p\ge1$, $q\ge0$ in $n\ge3$, and $q\ge1$ in the plane. Differentiating an interior null power and an exterior Kelvin transform gives the nonzero factor $-p(n+2q-2)$.
* Lemma 5 uses the harmonic decomposition of the product. Its final sum stops at $\min(p-1,q)$ in dimension at least three and at $\min(p-1,q-1)$ in the plane. The coefficient at $\ell=q$ in the plane vanishes.
* Fixed necessity uses polar integration, the span, and the conjugated basis in the angular projection. The weight after the Jacobian is $r^{k-1-2q}$. Fixed sufficiency expands arbitrary harmonic tests, including their first derivatives uniformly on the closed shell, and applies Lemma 5 term by term.
* Varying annuli and spheres are linked by polar integration and continuity in the radius. Applying the fixed theorem on each compact subinterval annihilates the forbidden degrees. The integrals determining them have weights $r^{k-1}$ in dimension at least three and $r^{k-3}$ in the plane. Positivity away from zero and continuity give pointwise vanishing. Full support of surface measure (or uniqueness of continuous representatives) passes from angular $L^2$ reconstruction to the pointwise statement. The converse uses the unconstrained degrees in Theorem 2.

## Comparison with the Lean challenge

I reviewed the self-contained `Challenge.lean` and the implementation’s parallel `Runcorn/Definitions.lean`, including all definition bodies. The challenge imports only Mathlib. A source diff confirmed that the matching definitions have identical code. The 29 common definitions and abbreviations agree. I checked both original theorem signatures in the final Challenge and compared both with their implementations in Solution.

| Lean declaration or definition | Review against the paper |
|---|---|
| `Space`, `annulus`, `shell` | Euclidean finite-dimensional coordinates distinguish the closed test annulus and open ambient shell. |
| `Admissible`, `gradDot` | Mathlib's harmonicity predicate asks for twice continuously differentiable functions with vanishing Laplacian locally. It is applied only on the two open domains. The source filter in the exterior limit expresses that the norm tends to infinity. The derivative is real-linear in the coordinate direction, and the product has no conjugation. |
| `FixedTests`, `AllAnnularTests`, `AllSurfaceTests` | Quantifier order is equivalent because the radii and test functions have independent scopes. `surfaceIntegral` supplies the surface Jacobian explicitly. The unit sphere measure is defined from Euclidean volume by `Measure.toSphere`; its whole-sphere mass is dimension times unit-ball volume. |
| `AngularForm`, `RadialOn`, `ThreeModes` | The bound on dimension makes the two implications exhaustive and mutually exclusive. At dimension two, coordinates 0 and 1 of `polarPoint` are respectively the cosine and sine coordinates. The three profiles are continuous on the open radius interval and may have arbitrary complex values. |
| `varyingAnnuli` and `VaryingStatement` | Both equivalences share the annular condition. The conjunction implies all three pairwise equivalences. |
| `IsSphericalHarmonic`, `IsAngularBasis` | Each function is a restriction of an actual harmonic homogeneous polynomial. Independence and the pointwise finite spanning condition are on functions restricted to the unit sphere. Each distinct pair in the degree has integral pairing zero. No unit normalization or completeness across all degrees is assumed. |
| `harmonicDimension` | The index set is zero-based and has the explicit source cardinality. Taking a basis as data mirrors the paper's setup. The auxiliary theorem `Runcorn.exists_angularBasis` constructs such a family from the polynomial dimension formula and orthogonalization in spherical L². |
| `momentExponent`, `radialMeasure`, `InMomentSpace` | Natural index bounds avoid subtraction at degrees zero and one. Exponent arithmetic and exponentiation use signed integers. The restricted measure incorporates the weight once. The factor in the integral is real-valued before coercion to the complexes. |
| `partialExpansion`, `HasMomentExpansion` | At a nonzero point the angular argument is its unit direction. Every admissible annulus avoids the origin. The degree cutoff runs through all natural numbers, with every basis index included in each completed degree. Each partial sum is square integrable and the extended square-integral seminorm of its difference from the target tends to zero. |
| `fixedAnnulus` and `FixedStatement` | The test and expansion are linked in both directions for every admissible basis, every square-integrable datum, and each fixed allowed annulus. |

The use of globally defined representatives introduces no extra regularity outside the open domains or the restricted measures. Any function given on one of the specified domains admits a total extension. Surface and annular tests only use values on those domains, and the derivatives are local because the harmonicity domains are open. Changes to square-integrable data on annular null sets preserve both sides of the fixed-annulus statement.

**Finding.** I found no substantive discrepancy between either of the two full Lean propositions and the corresponding theorem in the original. This assessment covers mathematical meaning. Each of the two reference declarations has a placeholder in the standalone Challenge. The implementation has its own definitions and both completed proofs. The separate checks below address the implementation.

**Reviewed snapshots (SHA-256).**

- `Challenge.lean` — `df02f2babb6d22d4417e2e96b5b6e07e02048deaa7ec44e1f5c14682ecd57c60`
- `Solution.lean` — `d7721c1b2ca12bdd81e9c10204c474643f5deae57812d359c73903c094941a78`
- `Runcorn/Definitions.lean` — `f55d346690a6b805203164c349b134b6e8e49a9fd03e1b948eb6bd512eb3e2da`

The statement reviewer also wrote `Quadric.lean`, `Symbol.lean`, `Orthogonality.lean`, and `PlanarExterior.lean` under `Runcorn/`. This report makes no claim of independent authorship review for those modules. The primary supervising AI independently inspected the null-quadric argument, including its application to the reducible binary form.

## Independent review of the completed proofs

I traced both final declarations in `Solution.lean` and the dependencies that discharge their hypotheses. The separate proof review compares the construction to the paper’s Lemmas 3–5 in detail. [Proof correspondence and departures](proof-review.md)

| Direction | Review of the proof and its hypotheses |
|---|---|
| Theorem 1, volume ⇔ surface | Compact subannuli provide integrability of the continuous tested product. Polar integration gives the integral of its continuous surface integral over the radii. Vanishing on every subinterval is equivalent to pointwise vanishing on the open interval. |
| Theorem 1, volume ⇒ angular form | One allowed Laurent exponent suffices to force the continuous angular moment of a given degree to vanish at each radius. The construction uses a different terminal exponent in the planar case. Angular density and full support of the surface measure turn vanishing high-degree moments into pointwise equality on each sphere. Evaluation along fixed rays supplies the planar profiles and their continuity. |
| Theorem 1, angular form ⇒ volume | The surviving constant and planar linear angular functions are orthogonal to each degree with a moment condition. The separated moments therefore vanish on every allowed subannulus. Continuity of the datum supplies the square integrability used by fixed-annulus sufficiency. |
| Theorem 2, volume ⇒ expansion | The null-power span and explicit gradient identities produce all signed moment exponents. The angular projections divide by each basis vector's positive squared norm and conjugate that vector. The product-space proof establishes an almost-everywhere angular expansion, its convergence by degree in product L², and its transport to the original annular L² norm. |
| Theorem 2, expansion ⇒ volume | Each finite angular sum annihilates the required separated tests. Passing to the given L² limit is valid because each test weight is bounded on the fixed annulus. The homogeneous product decomposition then gives the finite gradient tests. Arbitrary harmonic tests are reached by approximating the two gradients successively. In each limit the fixed gradient multiplies the L² datum by a bounded function on the annulus. |

The last step follows the paper’s interior and Kelvin mode strategy using a different approximation theorem. Uniform approximation of the boundary values, a maximum principle, and a local energy estimate give L² convergence of the gradients. In the plane the exterior approximation may include a constant. That constant has zero gradient, and the logarithmic barrier applies to its bounded difference from the original decaying trace extension. The theorem still quantifies over every original admissible pair. I found no additional assumptions on the two target theorems.

To check implementation independence, I followed the local imports reachable from `Solution` to 50 project modules including `Solution` itself. They contain no import of `Challenge`. A source scan of that graph after removing comments found no `sorry`, `admit`, custom `axiom`, or `native_decide`. I also ran the following on the finished implementation. Both example declarations typechecked; the last two lines of output list all transitive axioms of the named proofs.

```bash
lake env lean --stdin <<'LEAN'
import Solution
example : Runcorn.VaryingStatement := Runcorn.varyingAnnuli
example : Runcorn.FixedStatement := Runcorn.fixedAnnulus
#print axioms Runcorn.varyingAnnuli
#print axioms Runcorn.fixedAnnulus
LEAN
```

```text
'Runcorn.varyingAnnuli' depends on axioms: [propext, Classical.choice, Quot.sound]
'Runcorn.fixedAnnulus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

I checked the final comparator transcript against the reviewed reference digest and the exported names. The reference and the solution exports both list `Runcorn.varyingAnnuli` and `Runcorn.fixedAnnulus`. The allowlist contains exactly the three axioms above. The con-ron kernel accepted 59,732 exported declarations, NanoDa accepted the solution, and Lean’s default kernel accepted it. The process exited with status 0. These checks validate both completed proofs against the final declarations. The human interpretation of the paper’s notation is covered by the separately attributed AI statement review above. [Input hashes](../verification/comparator-inputs.txt) · [Comparator and kernel output](../verification/comparator.txt) · [Principal axiom output](../verification/principal-axioms.txt)

## Clarity and exact arithmetic

For a first reading, open the two final `theorem` declarations in `Challenge.lean`. Read the two sides of each `↔` as implications in both directions. Follow the names `AngularForm` and `HasMomentExpansion` up to their definitions in that file. Then open the identically named theorems in `Solution.lean`. Each application there names the lemma that proves one part of the source theorem. The statement review concerns the mathematical interpretation. The kernel checks the deductions from the stated axioms.

I independently wrote four small Lean checks covering five exceptional or low-degree cases in the table above. Running `lake env lean verification/MomentCases.lean` verifies the full integer exponent sets in those cases. Each check uses only `propext` and `Quot.sound`. The exponent formulas for arbitrary allowed dimensions and degrees are covered by the proofs of the two main theorems. [Executable checks](../verification/MomentCases.lean) · [Actual output](../verification/moment-cases.txt)
