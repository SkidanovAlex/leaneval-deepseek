import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# The flower/petal construction for a parabolic germ of order `q+1`

`Work.Horn.flower_q` needs the Leau–Fatou flower of the germ
`f z = z + a z ^ (q+1) + o (z ^ (q+1))` (`q ≥ 1`, `a ≠ 0`): `q` disjoint open connected
"petals" `V j`, accumulating at `0`, invariant under `f`, on each of which `f` is injective,
whose union captures the whole parabolic basin, and which form a Markov partition of the basin
(the local constancy of the index).

This file fixes the vocabulary.  With `c = cc q a = -1/(q a)` the *chart* is
`chartQ z = c / z^q`; the attracting petals are the `q` connected components of
`bigPetal M = {z | c / z^q ∈ ball (c/(2M)) (‖c‖/(2M))}`, i.e. of the set where `Re (c / z^q) > M`.
Because `z ↦ z^q` is a `q`-sheeted cover of `ℂ*`, that set splits into `q` components, each of
which is an explicit biholomorphic image of the disc `DM M`:

* `DM M  = {s | M * ‖s‖ ^ 2 < Re (c * star s)} = ball (c/(2M)) (‖c‖/(2M))`  (the "root disc"),
* `zeta j = exp ((log c + 2πi j)/q)` (the `q`-th roots of `c`; `zeta 0` is the principal one),
* `rootFun j s = zeta j * exp (log (s/c)/q)` (the `j`-th branch of the `q`-th root),
* `petal M j = rootFun j '' DM M`.

Since `(rootFun j s)^q = s` for `s ∈ DM M` and `rootFun j = zeta j * exp (log (s/c)/q)`, the
petals are exactly the pieces of `bigPetal M` meeting the `q` "attracting directions"; the point
of the chart is that the germ becomes the translation `w ↦ w + 1 + o(1)` in the `w = c/z^q`
coordinate, so the petals are invariant and capture the basin.
-/

namespace Work.Horn.Flower

open MandelDim Complex Filter Topology
open scoped Topology

noncomputable section

/-- `c = -1/(q a)`: the constant of the chart `w = c / z ^ q`. -/
def cc (q : ℕ) (a : ℂ) : ℂ := -1 / ((q : ℂ) * a)

/-- The `j`-th `q`-th root of `c`, `ζ j = exp ((log c + 2πi j)/q)`. -/
def zeta (q : ℕ) (a : ℂ) (j : Fin q) : ℂ :=
  Complex.exp ((Complex.log (cc q a) + 2 * Real.pi * Complex.I * (j : ℂ)) / (q : ℂ))

/-- The `j`-th branch of the `q`-th root of `s / c`, normalised by `rootFun j c = ζ j`. -/
def rootFun (q : ℕ) (a : ℂ) (j : Fin q) (s : ℂ) : ℂ :=
  zeta q a j * Complex.exp (Complex.log (s / cc q a) / (q : ℂ))

/-- The root disc `DM M = {s | Re (c * star s) > M * ‖s‖ ^ 2}` — the world of the petals. -/
def DM (q : ℕ) (a : ℂ) (M : ℝ) : Set ℂ :=
  {s : ℂ | M * Complex.normSq s < (cc q a * star s).re}

/-- The `j`-th petal: the `j`-th branch of the `q`-th root of the root disc. -/
def petal (q : ℕ) (a : ℂ) (M : ℝ) (j : Fin q) : Set ℂ := rootFun q a j '' DM q a M

/-- The union of the petals: the set where the chart value has real part `> M`. -/
def bigPetal (q : ℕ) (a : ℂ) (M : ℝ) : Set ℂ := {z : ℂ | z ^ q ∈ DM q a M}

/-- The chart `w = c / z ^ q` (`0` is junk). -/
def chartQ (q : ℕ) (a : ℂ) (z : ℂ) : ℂ := cc q a / z ^ q

/-- The germ factor: `f z = z + z ^ (q+1) * Hfun f q a z` by construction, `Hfun f q a 0 = a`. -/
def Hfun (f : ℂ → ℂ) (q : ℕ) (a : ℂ) (z : ℂ) : ℂ :=
  if z = 0 then a else (f z - z) / z ^ (q + 1)

/-- The hypotheses of `Work.Horn.flower_q`, collected. -/
structure Setup (f : ℂ → ℂ) (D : Set ℂ) (q : ℕ) (a : ℂ) : Prop where
  hD : IsOpen D
  hconn : IsPreconnected D
  h0 : (0 : ℂ) ∈ D
  hf : DifferentiableOn ℂ f D
  hq : 1 ≤ q
  ha : a ≠ 0
  hfix : f 0 = 0
  hgerm : Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
    (nhdsWithin 0 {0}ᶜ) (nhds 0)

/-- The quantitative local data extracted from a parabolic germ of order `q + 1` on a disc of
radius `ρ`.  Besides the germ form and the chart estimate this records exactly the smallness
facts that the branch/argument computation for the petals consumes. -/
structure Bounds (f : ℂ → ℂ) (D : Set ℂ) (q : ℕ) (a : ℂ) (ρ : ℝ) : Prop where
  hρ : 0 < ρ
  hsub : Metric.ball (0 : ℂ) ρ ⊆ D
  hq : 1 ≤ q
  ha : a ≠ 0
  hfix : f 0 = 0
  /-- the germ decomposition (exact, by definition of `Hfun`) -/
  hf_eq : ∀ z : ℂ, f z = z * (1 + z ^ q * Hfun f q a z)
  /-- `f'` is close to `1` on the disc, hence `f` is injective there -/
  hderiv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv f z - 1‖ ≤ 1 / 2
  /-- the chart is a translation up to `1/4` -/
  hchart : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
    ‖chartQ q a (f z) - chartQ q a z - 1‖ ≤ 1 / 4
  /-- `1 + z^q H z` does not vanish on the disc -/
  hunit_ne : ∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 + z ^ q * Hfun f q a z ≠ 0
  /-- `(1 + z^q H z)^q` has positive real part on the disc -/
  hunit_re : ∀ z ∈ Metric.ball (0 : ℂ) ρ, 0 < ((1 + z ^ q * Hfun f q a z) ^ q).re
  /-- `|arg (1 + z^q H z)| * q < π` on the disc (so that the principal `q`-th root of
  `(1 + z^q H z)^q` is `1 + z^q H z`) -/
  hunit_arg : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
    |(1 + z ^ q * Hfun f q a z).arg| * (q : ℝ) < Real.pi

/-- The algebra and set geometry of the petals (all facts about `cc`, `zeta`, `rootFun`, `DM`,
`petal`, `bigPetal` alone, with no reference to `f`). -/
structure PetalFacts (q : ℕ) (a : ℂ) (M : ℝ) : Prop where
  cc_ne_zero : cc q a ≠ 0
  DM_eq_ball : DM q a M = Metric.ball (cc q a / (2 * M)) (‖cc q a‖ / (2 * M))
  DM_subset_ball : ∀ s ∈ DM q a M, ‖s‖ < ‖cc q a‖ / M
  zeta_pow : ∀ j : Fin q, (zeta q a j) ^ q = cc q a
  zeta_ne_zero : ∀ j : Fin q, zeta q a j ≠ 0
  zeta_ne_iff : ∀ i j : Fin q, zeta q a i = zeta q a j ↔ i = j
  rootFun_pow : ∀ (j : Fin q) (s : ℂ), s ∈ DM q a M → (rootFun q a j s) ^ q = s
  rootFun_ne_zero : ∀ (j : Fin q) (s : ℂ), s ∈ DM q a M → rootFun q a j s ≠ 0
  rootFun_eq_of_pow_eq : ∀ (j : Fin q) (s t : ℂ), s ∈ DM q a M → t ∈ DM q a M →
    rootFun q a j s = rootFun q a j t → s = t
  rootFun_inj_index : ∀ (j k : Fin q) (s : ℂ), s ∈ DM q a M →
    rootFun q a j s = rootFun q a k s → j = k
  isOpen_petal : ∀ j : Fin q, IsOpen (petal q a M j)
  isConnected_petal : ∀ j : Fin q, IsConnected (petal q a M j)
  disjoint_petal : ∀ i j : Fin q, i ≠ j → Disjoint (petal q a M i) (petal q a M j)
  not_mem_petal_zero : ∀ j : Fin q, (0 : ℂ) ∉ petal q a M j
  zero_mem_closure_petal : ∀ j : Fin q, (0 : ℂ) ∈ closure (petal q a M j)
  petal_subset_bigPetal : ∀ j : Fin q, petal q a M j ⊆ bigPetal q a M
  iUnion_petal_eq_bigPetal : (⋃ j, petal q a M j) = bigPetal q a M
  petal_norm_pow_lt : ∀ (j : Fin q) (z : ℂ), z ∈ petal q a M j → ‖z‖ ^ q < ‖cc q a‖ / M
  mem_petal_iff : ∀ (j : Fin q) (z : ℂ),
    z ∈ petal q a M j ↔ 0 < ‖z‖ ∧ z ^ q ∈ DM q a M ∧ rootFun q a j (z ^ q) = z

/-- Elementary facts about the parabolic basin of the germ, for the `Setup` hypotheses. -/
structure BasinFacts (f : ℂ → ℂ) (D : Set ℂ) : Prop where
  isOpen : IsOpen (ParabolicBasin f D)
  mapsTo : Set.MapsTo f (ParabolicBasin f D) (ParabolicBasin f D)
  back : ∀ z ∈ D, f z ∈ ParabolicBasin f D → z ∈ ParabolicBasin f D
  zero_notMem : (0 : ℂ) ∉ ParabolicBasin f D
  orbit_ne_zero : ∀ z ∈ ParabolicBasin f D, ∀ n : ℕ, f^[n] z ≠ 0
  tendsto_zero : ∀ z ∈ ParabolicBasin f D, Tendsto (fun n : ℕ => f^[n] z) atTop (𝓝 0)
  mem_of_iterate : ∀ z ∈ D, ∀ n : ℕ, (∀ k < n, f^[k] z ∈ D) →
    f^[n] z ∈ ParabolicBasin f D → z ∈ ParabolicBasin f D

end

end Work.Horn.Flower
