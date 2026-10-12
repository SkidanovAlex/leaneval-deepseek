import ChallengeDeps
import Submission.Work.TrialState.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/SecondOrder` — the quasi-free (pair-excited) trial state

This chapter builds the **second-order** (Bogoliubov) trial-state vocabulary in
the corpus's per-sector language, i.e. the family of states that *does* reach
the `(μa³)^{1/2}`-rate required by the residual
`Work.TrialState.SecondOrderUpperBound` (the named residual of the TrialState
chapter; see `Submission/Work/TrialState/NOTES.md` §3).

## Why a *different* family from `TrialState.trial`

`TrialState.trial N φ f = ∏ᵢ φ(xᵢ) · ∏_{p ∈ pairSet N} f(x_{p.1} − x_{p.2})` is a
*product* of pair factors (a Jastrow/product state).  Its energy is exactly its
Hartree (mean-field) value up to relative errors `≈ ρ r³ + a/r` — the Dyson
level `(ρa³)^{1/3}`, not `(ρa³)^{1/2}` (`NOTES.md` §3.2, ESY arXiv:0806.4873 §1).

The states that reach `(ρa³)^{1/2}` are the **quasi-free (squeezed /
pair-excited) states** of Bogoliubov theory.  In a fixed-`N` sector, the
`N`-particle component of the squeezed state
`exp(½ Σ_k c_k a†_k a†_{−k}) (a†_0)^{n₀}|0⟩` (ESY's trial state, with the
generalization to *soft pairs*: a general two-point pairing kernel) has the
position-space form

    Ψ(x) = (∏ᵢ ψ(xᵢ)) · Σ_{m ≥ 0} w_m · Σ_{partial matchings M, |M| = m}
                                            ∏_{{a,b} ∈ M} G(x_a, x_b) ,

i.e. a **weighted sum over partial matchings** (`pairState` below) — a sum over
*pairings*, where the Jastrow family is a *product* over all pairs.  The
`m`-th term is the `2m`-excited-particle component and the `N − 2m` unmatched
particles are the condensate.  For the pure exponential (squeezing) weights
`w_m = c^m/(2^m m!)` the amplitude is exactly the hafnian of the pairing
kernel, which is what makes the configuration integrals of `Ψ²` computable by
Wick pairing (`NOTES.md` §4, step 1).

## What this module fixes

* `IsPMatch`, `pmatch N` — a partial matching of `Fin N` as an *involutive*
  self-map of the particle labels (fixed points = condensate particles);
* `pairIdx`, `pairRep`, `nPair` — the paired labels, one canonical
  representative per pair, and the number of pairs;
* `pairAmp`, `pairState` — the weighted partial-matching amplitude and the
  quasi-free trial state;
* `bogWeight`, `bogKernel`, `quasiFreeState` — the *concrete* squeezing choice:
  weight `c^m/(2^m m!)` and the two-point kernel obtained from the scattering
  solution `om` with the long-range tail cut at `r` (the same cutoff as
  `TrialState.pairCorr`, so the family stays in the dilute admissible class);
* `pairStateE` — its `H_Λ(μ)`-energy word (`kinWord + qLHSword`, the corpus
  per-sector transcription of FS `eq:aprioriPsi`'s left-hand side);
* `PairFamilyBound`, `QuasiFreeBound` — the residual restricted to the family;
* `SecondOrderUpperBound'` — the *hypothesis-corrected* form of the TrialState
  residual (see `NOTES.md` §2: the unguarded form is false at `N = 0`).

Everything about the definitions is in `Defs.lean`; the API (permutation
invariance, continuity, the collapse of the many-body integrals, the graph
expansion) is in the subdirectories `Pmatch/`, `State/`, `Reduce/`, and the
reductions to the named residuals are in `Main.lean`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.SecondOrder

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Partial matchings of the particle labels -/

/-- A **partial matching** of `Fin N`, as an involutive self-map of the labels:
the non-fixed points come in 2-cycles (the pairs), the fixed points are the
"condensate" (unpaired) labels. -/
def IsPMatch {N : ℕ} (p : Fin N → Fin N) : Prop := ∀ i, p (p i) = i

/-- The finite set of partial matchings of `Fin N`. -/
noncomputable def pmatch (N : ℕ) : Finset (Fin N → Fin N) :=
  Finset.univ.filter (fun p : Fin N → Fin N => ∀ i : Fin N, p (p i) = i)

/-- The set of **paired** labels of `p` (the labels moved by `p`). -/
noncomputable def pairIdx {N : ℕ} (p : Fin N → Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => p i ≠ i)

/-- One canonical representative per pair: the smaller label of the pair. -/
noncomputable def pairRep {N : ℕ} (p : Fin N → Fin N) : Finset (Fin N) :=
  (pairIdx p).filter (fun i : Fin N => (p i).val < i.val)

/-- The number of pairs of a partial matching. -/
noncomputable def nPair {N : ℕ} (p : Fin N → Fin N) : ℕ := (pairIdx p).card / 2

/-- The set of *oriented* pairs of a partial matching, one per pair (the
canonical representative `i ∈ pairRep p` oriented as `(i, p i)`).  This is the
edge set of the matching inside the ordered-pair set `pairSet N`, and is what
identifies the partial matchings of `pairAmp` with the degree-`≤ 1` graphs of
the Jastrow expansion (`Reduce.jastrow_graph_expansion`). -/
noncomputable def pmatchSet {N : ℕ} (p : Fin N → Fin N) : Finset (Fin N × Fin N) :=
  (pairRep p).image (fun i => (i, p i))

/-! ## The weighted partial-matching amplitude and the pair-excited state -/

/-- The **pair amplitude** of the quasi-free state: the weighted sum over
partial matchings of `Fin N` of the product of the pairing kernel over the
pairs, one factor per pair. -/
noncomputable def pairAmp (N : ℕ) (wt : ℕ → ℝ) (G : ℝ³ → ℝ³ → ℝ) (x : X N) : ℝ :=
  ∑ p ∈ pmatch N, wt (nPair p) * ∏ i ∈ pairRep p, G (x i) (x (p i))

/-- The **pair-excited (quasi-free) trial state**: the condensate orbital
`∏ᵢ ψ(xᵢ)` times the weighted partial-matching amplitude.  This is the
fixed-`N` position-space form of the squeezed state
`exp(½Σ_k c_k a†_k a†_{−k})(a†_0)^{n₀}|0⟩` with a general pairing kernel
(hence including the *soft pairs* needed for the `(ρa³)^{1/2}`-rate). -/
noncomputable def pairState (N : ℕ) (ψ : ℝ³ → ℝ) (wt : ℕ → ℝ) (G : ℝ³ → ℝ³ → ℝ)
    (x : X N) : ℝ :=
  (∏ i : Fin N, ψ (x i)) * pairAmp N wt G x

/-- The `L²`-norm square of the pair-excited state over the centred box. -/
noncomputable def pairStateZ (N : ℕ) (ℓ : ℝ) (ψ : ℝ³ → ℝ) (wt : ℕ → ℝ) (G : ℝ³ → ℝ³ → ℝ) : ℝ :=
  ∫ x in abox N ℓ, (pairState N ψ wt G x) ^ 2

/-- The `H_Λ(μ)`-energy word of the pair-excited state: the corpus kinetic word
plus the corpus potential word at the chosen kernels `w = wPairC ℓ v`,
`w₁ = wPairC ℓ (g₀)` — the left-hand side of FS `eq:aprioriPsi`. -/
noncomputable def pairStateE (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ψ : ℝ³ → ℝ) (wt : ℕ → ℝ)
    (G : ℝ³ → ℝ³ → ℝ) : ℝ :=
  kinWord N ℓ (pairState N ψ wt G)
    + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (pairState N ψ wt G)

/-- The `p`-th **matching component** of the pair-excited state: the condensate
factor `∏ᵢ ψ(xᵢ)` times the product of the pairing kernel over the pairs of `p`
(the `p`-summand of `pairAmp`).  The pair state is the weighted sum of these
components, and its energy is a quadratic form in them (see
`Reduce/pairStateE_eq_quadratic`). -/
noncomputable def pairComp (N : ℕ) (psi : ℝ³ → ℝ) (G : ℝ³ → ℝ³ → ℝ)
    (p : Fin N → Fin N) (x : X N) : ℝ :=
  (∏ i : Fin N, psi (x i)) * ∏ i ∈ pairRep p, G (x i) (x (p i))

/-- The `L²(abox)` **overlap** of two matching components — the entries of the
Gram matrix of the family `pairComp`.  `pairStateZ` is the weighted double sum
of these entries (`Reduce.pairStateZ_eq_doubleSum`). -/
noncomputable def pairOverlap (N : ℕ) (ℓ : ℝ) (psi : ℝ³ → ℝ) (G : ℝ³ → ℝ³ → ℝ)
    (p q : Fin N → Fin N) : ℝ :=
  ∫ x in abox N ℓ, pairComp N psi G p x * pairComp N psi G q x

/-- The **Bogoliubov bilinear form** of the family: the pairing of two matching
components by the `H_Λ(μ)` energy (kinetic overlap plus potential overlap at the
chosen kernels).  The energy of the pair state is the weighted double sum of
these pairings (`Reduce.pairStateE_eq_quadratic`): the energy is a quadratic
form in the matching amplitudes, which is what makes the second-order
(Bogoliubov) evaluation possible. -/
noncomputable def pairBilin (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (psi : ℝ³ → ℝ)
    (G : ℝ³ → ℝ³ → ℝ) (p q : Fin N → Fin N) : ℝ :=
  (∑ i : Fin N, ∑ k : Fin 3, ∫ x in abox N ℓ,
      fderiv ℝ (pairComp N psi G p) x (kcDir N i k)
        * fderiv ℝ (pairComp N psi G q) x (kcDir N i k))
    + ∫ x in abox N ℓ, pairComp N psi G p x * pairComp N psi G q x *
        (- μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
          + (1 / 2) * (∑ r ∈ pairSet N, wPairC ℓ v (x r.1) (x r.2)))

/-! ## The concrete squeezing data -/

/-- The squeezing weight `w_m = c^m/(2^m m!)` — the coefficient of the
`m`-pair term of `exp(½ Σ_k c_k a†_k a†_{−k})`. -/
noncomputable def bogWeight (c : ℝ) : ℕ → ℝ :=
  fun m => c ^ m / ((2 : ℝ) ^ m * (m.factorial : ℝ))

/-- The **Bogoliubov pair kernel**: the pair-correlation function of the
scattering solution with the long-range tail cut at `r`, as a symmetric
two-point kernel `G x y = f(x − y)`, `f = 1 − omχ_r` (the same `f` as
`TrialState.pairCorr`). -/
noncomputable def bogKernel (r : ℝ) (hr : 0 < r) (om : ℝ³ → ℝ) : ℝ³ → ℝ³ → ℝ :=
  fun x y => TrialState.pairCorr r hr om (x - y)

/-- The concrete quasi-free trial state: uniform condensate orbital `orbConst s`
(the free amplitude `s` is exactly the normalization degree of freedom of the
family), squeezing weights `bogWeight c`, and the Bogoliubov pair kernel
`bogKernel r hr om`. -/
noncomputable def quasiFreeState (N : ℕ) (s c r : ℝ) (hr : 0 < r) (om : ℝ³ → ℝ) : X N → ℝ :=
  pairState N (TrialState.orbConst s) (bogWeight c) (bogKernel r hr om)

/-! ## The residual, restricted to the family -/

/-- **The pair-family residual.**  Some member of the pair-excited family of
`pairState` (with a symmetric pairing kernel, and a continuous instance) is
box-normalized and reaches the second-order energy threshold.  This is the
"reduce to a concrete variational family" form of
`TrialState.SecondOrderUpperBound`: the state is no longer an arbitrary
continuous function but an explicit function of `(ψ, wt, G)`; the regularity
requested is the weakest one that makes it an admissible state. -/
def PairFamilyBound (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ ψ : ℝ³ → ℝ, ∃ wt : ℕ → ℝ, ∃ G : ℝ³ → ℝ³ → ℝ,
    (∀ x y : ℝ³, G x y = G y x) ∧ Continuous (pairState N ψ wt G) ∧
        pairStateZ N ℓ ψ wt G = 1 ∧
          pairStateE N ℓ μ v h ψ wt G
            ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-- **The concrete quasi-free residual.**  Some `(c, r)` gives a normalized,
admissible member of the *concrete* squeezing family `quasiFreeState N s c r hr om`
whose energy reaches the second-order threshold.  This is the form in which the
ESY/Yau–Yin variational computation is naturally phrased (choose the squeezing
amplitude `c` and the cutoff `r`). -/
def QuasiFreeBound (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ s c r : ℝ, ∃ hr : 0 < r,
    Continuous (quasiFreeState N s c r hr (Classical.choose h)) ∧
    (∫ x in abox N ℓ, (quasiFreeState N s c r hr (Classical.choose h) x) ^ 2) = 1 ∧
      (kinWord N ℓ (quasiFreeState N s c r hr (Classical.choose h))
        + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h))
            (quasiFreeState N s c r hr (Classical.choose h)))
        ≤ - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-- **The dilute-regime pair-family residual.**  The form in which the
quasi-free construction is expected to deliver `PairFamilyBound`: only in the
dilute window `μ(a v)³ ≤ ε` and in the nonempty sector `1 ≤ N`. -/
def PairFamilyBound' (N : ℕ) (ℓ μ C ε : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  1 ≤ N → μ * (a v) ^ 3 ≤ ε → PairFamilyBound N ℓ μ C v h

/-- **The dilute-regime quasi-free residual.**  `QuasiFreeBound` restricted to
the dilute window: this is *the* named residual of the chapter (the ESY /
Yau–Yin variational computation). -/
def QuasiFreeBound' (N : ℕ) (ℓ μ C ε : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  1 ≤ N → μ * (a v) ^ 3 ≤ ε → QuasiFreeBound N ℓ μ C v h

/-- **The hypothesis-corrected second-order residual.**  `SecondOrderUpperBound`
with the two hypotheses that are *needed for it to be true* (see `NOTES.md` §2):
a nonempty particle sector `1 ≤ N` and the dilute (admissible-cutoff) regime
`μ(a v)³ ≤ ε` (the latter enters the quasi-free construction through the kernel
cutoff).  The unguarded `TrialState.SecondOrderUpperBound` is refuted at `N = 0`
by `Main.not_secondOrderUpperBound_zero`. -/
def SecondOrderUpperBound' (N : ℕ) (ℓ μ C ε : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  1 ≤ N → μ * (a v) ^ 3 ≤ ε → TrialState.SecondOrderUpperBound N ℓ μ C v h

end Work.SecondOrder
