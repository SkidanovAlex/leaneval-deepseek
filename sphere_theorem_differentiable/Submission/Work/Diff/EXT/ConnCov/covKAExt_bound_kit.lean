import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.conn_diff_bound_of_shibounds
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.tower_aOf_hasDerivAt
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_local
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_sliceT
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_locBdd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `aOf`-tower bound (self-contained copy) and its assembly from a parametric reaction bound

This module is a *copy* of the proved assembly of
`Submission.Work.Diff.EXT.ConnCov.covKAExt_bound` (the grid/monotone-envelope Gronwall argument
that turns a parametric reaction bound into the uniform bound
`∀ k ∃ Ck, ∀ t ∈ [T/2,T), ‖∇^{G 0,k}aOf(G t)‖ ≤ Ck · qf`), placed in the fresh namespace
`Work.Diff.EXT.ConnCov.V2` so that it can be used **without** importing the module carrying the
stalled `dAOfTowerBoundShiPar` (and hence without its `sorryAx`), and with the reaction bound taken
as an explicit hypothesis:

* `Work.Diff.EXT.ConnCov.V2.covKAExt_bound_of_react` — the assembly, from the parametric reaction
  bound `hReact` (the only input that the original module does not prove itself).

Everything else below (the `qf`-vocabulary, the comparison lemmas, the `ψ`/`Mt` envelope, its
monotonicity and the grid step `Mt_step`) is copied verbatim from the proved material of
`Submission.Work.Diff.EXT.ConnCov.covKAExt_bound`; the two lemmas of that module which *call* the
stalled `dAOfTowerBoundShiPar` are omitted (they are the per-time form of the hypothesis `hReact`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.V2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The base case `k = 0` of `covKAExt_bound`.**  At order `0` the tower is `aOf`, and the bound
is `conn_diff_bound_of_shibounds` (the *proved* uniform estimate for the connection difference)
followed by Cauchy–Schwarz. -/
theorem covKAExt_bound_zero
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M, ∀ a b c : TangentSpace I x,
      |Work.Diff.EXT.aOf G t (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x b) (Submission.Diff.smoothExt x c) x|
        ≤ C0 * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c) := by
  obtain ⟨C', hC'0, hC'⟩ :=
    Work.Diff.EXT.conn_diff_bound_of_shibounds (I := I) (M := M) hLC G T C hT hC hflow hbound
      hmet hShi
  refine ⟨C', hC'0, ?_⟩
  intro t ht x a b c
  have hD := hC' t ht x a b
  set D : TangentSpace I x :=
    Submission.Diff.lcOf (G t) (Submission.Diff.smoothExt x b) x a
      - Submission.Diff.lcOf (G 0) (Submission.Diff.smoothExt x b) x a with hDdef
  have hval : Work.Diff.EXT.aOf G t (Submission.Diff.smoothExt x a)
        (Submission.Diff.smoothExt x b) (Submission.Diff.smoothExt x c) x
      = (G t).inner x D c := by
    simp only [Work.Diff.EXT.aOf, hDdef, Work.Diff.GE.smoothExt_apply]
  rw [hval]
  calc |(G t).inner x D c| ≤ Real.sqrt ((G t).inner x D D) * Real.sqrt ((G t).inner x c c) :=
        Work.Diff.EXT.smet_cauchy' (G t) x D c
    _ ≤ (C' * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))
          * Real.sqrt ((G t).inner x c c) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        simpa only [hDdef] using hD
    _ = C' * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) := by ring

/-- **The *moving* curvature tower is bounded by Shi's estimate.**  A short corollary of the
proved `Work.Diff.EXT.covKRmExt_eval_bound` (which bounds `|∇^k Rm|` by
`C·(1 + √(curvNormK g x k))` times the product of the metric norms of the arguments) together with
`ShiBounds` at `σ = T/2`.  This is the honest input for the Ricci terms of the `dAOfBase` reaction:
by the contraction identity `∇^{g,j}Ric = (contraction of ∇^{g,j}Rm)` it supersedes every bound
phrased with `baseRic` (see the warning in the module docstring). -/
theorem covKRmExt_bound_moving
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M)) :
    ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c d : TangentSpace I x),
      |Work.Diff.EXT.covKRmExt (G t) k (fun i => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
          (Submission.Diff.smoothExt x c) (Submission.Diff.smoothExt x d) x|
        ≤ Ck * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d) := by
  intro k
  obtain ⟨Ce, hCe0, hCeb⟩ := Work.Diff.EXT.covKRmExt_eval_bound (I := I) (M := M) hLC k
  obtain ⟨Cr, hCr⟩ :=
    hShi (G := G) (T := T) (C := C) (σ := T / 2) hT hflow hbound (by linarith) (by linarith) k
  refine ⟨Ce * (1 + Real.sqrt (max Cr 0)), mul_nonneg hCe0 (by positivity), ?_⟩
  intro t ht x v a b c d
  have hK : Real.sqrt (Work.Diff.EXT.curvNormK (G t) x k) ≤ Real.sqrt (max Cr 0) :=
    Real.sqrt_le_sqrt (le_trans (hCr t ht x) (le_max_left _ _))
  refine le_trans (hCeb (G t) x v a b c d) ?_
  calc Ce * (1 + Real.sqrt (Work.Diff.EXT.curvNormK (G t) x k)) *
        (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d))
      ≤ Ce * (1 + Real.sqrt (max Cr 0)) *
        (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCe0) (by positivity)
    _ = (Ce * (1 + Real.sqrt (max Cr 0))
            * Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d) := by ring

/-- **The `valOp` form of the Clairaut identity.**  This is the `hclairaut` input of the plan in
`conn_diff_cov_bounds_v2.lean`: the time derivative of the `∇^{G 0}`-tower of `aOf`, evaluated on
the `smoothExt x ·` extensions.  It is an immediate corollary of the *proved*
`Work.Diff.EXT.ConnCov.tower_aOf_hasDerivAt` (`valOp` is that tower evaluated on the
`Classical.epsilon`-chosen smooth fields, and those are smooth by `smoothExt_spec`). -/
theorem tower_aOf_valOp_hasDerivAt
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (k : ℕ) (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    HasDerivAt (fun s : ℝ => Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G s) k) x v a b c)
      (Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (dAOfBase G t) k) x v a b c) t := by
  have hv : ∀ i, Work.Diff.EXT.ATower.SmE I M
      (Submission.Diff.smoothExt x (v i)) :=
    fun i => (Work.Diff.GE.smoothExt_spec (I := I) x (v i)).1
  have ha : Work.Diff.EXT.ATower.SmE I M (Submission.Diff.smoothExt x a) :=
    (Work.Diff.GE.smoothExt_spec (I := I) x a).1
  have hb : Work.Diff.EXT.ATower.SmE I M (Submission.Diff.smoothExt x b) :=
    (Work.Diff.GE.smoothExt_spec (I := I) x b).1
  have hc : Work.Diff.EXT.ATower.SmE I M (Submission.Diff.smoothExt x c) :=
    (Work.Diff.GE.smoothExt_spec (I := I) x c).1
  simpa only [Work.Diff.EXT.ATower.valOp] using
    tower_aOf_hasDerivAt (I := I) (M := M) hLC hflow ht k
      (fun i => Submission.Diff.smoothExt x (v i))
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
      (Submission.Diff.smoothExt x c) hv ha hb hc x

/-- **The `G s`-vs-`G t` comparison of the quadratic forms on `[T/2,T)`.**  From `hmet` at the two
times: `e^{-2nCt}·e^{-2nCs}` and the fact that the exponential factor is `≤ e^{4nCT}`.  This is the
model proof `smet_quadForm_le_of_flow` of `conn_diff_cov_bounds_v2.lean`, kept here so that the
closing Gronwall does not have to import that (non-compiling) file. -/
theorem smet_quadForm_le_of_hmet
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) :
    ∀ (s t : ℝ), s ∈ Set.Ico 0 T → t ∈ Set.Ico 0 T → ∀ (x : M) (u : TangentSpace I x),
      (G s).inner x u u
        ≤ Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T) * (G t).inner x u u := by
  intro s t hs ht x u
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hnC : 0 ≤ (Module.finrank ℝ E : ℝ) * C := mul_nonneg hn0 hC
  have hnt : 0 ≤ (G t).inner x u u := by
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    have h2 : (G t).inner x u u = ‖u‖ ^ 2 := by
      rw [show (G t).inner x u u = Inner.inner ℝ u u from rfl, real_inner_self_eq_norm_sq]
    rw [h2]; positivity
  have h1 := (hmet s hs x u).1
  have h2 := (hmet t ht x u).2
  have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * s)
      * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
      ≤ Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [hs.2.le, ht.2.le, hs.1, ht.1, hnC]
  calc (G s).inner x u u
      ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * s) * (G 0).inner x u u := h1
    _ ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * s)
          * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
    _ = (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * s)
          * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)) * (G t).inner x u u := by ring
    _ ≤ Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T) * (G t).inner x u u :=
        mul_le_mul_of_nonneg_right hexp hnt

/-- **The induced comparison of the `√⟨·,·⟩`-products.**  If `G' ≤ K·G` as quadratic forms then
every factor is dominated by `√K` times the corresponding `G`-factor, giving a factor
`(√K)^{k+3}` for `k` direction vectors and three argument vectors.  (Elementwise from
`Real.sqrt_le_sqrt` and `Real.sqrt_mul`; the model is `prod_sqrt_le_of_quadForm_le` in the
non-compiling `conn_diff_cov_bounds_v2.lean`.  NB: `gcongr` is not available in this import set,
and the resolved `Finset.prod_le_prod` is the `MulLeftMono`-flavoured version which does not apply
to `ℝ`; the ℝ statement is `Finset.prod_le_prod₀`, with the nonnegativity hypotheses first.) -/
theorem prod_sqrt_le_of_quadForm_le
    {G G' : Submission.Diff.SMet I M} {x : M} {K : ℝ} (hK0 : 0 ≤ K) (k : ℕ)
    (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x)
    (h : ∀ u : TangentSpace I x, G'.inner x u u ≤ K * (G.inner x u u)) :
    (Finset.univ.prod (fun i : Fin k => Real.sqrt (G'.inner x (v i) (v i))))
        * Real.sqrt (G'.inner x a a) * Real.sqrt (G'.inner x b b) * Real.sqrt (G'.inner x c c)
      ≤ (Real.sqrt K) ^ (k + 3) *
          ((Finset.univ.prod (fun i : Fin k => Real.sqrt (G.inner x (v i) (v i))))
            * Real.sqrt (G.inner x a a) * Real.sqrt (G.inner x b b)
            * Real.sqrt (G.inner x c c)) := by
  have hfac : ∀ u : TangentSpace I x,
      Real.sqrt (G'.inner x u u) ≤ Real.sqrt K * Real.sqrt (G.inner x u u) := by
    intro u
    refine le_trans (Real.sqrt_le_sqrt (h u)) ?_
    rw [Real.sqrt_mul hK0]
  have hprod : Finset.univ.prod (fun i : Fin k => Real.sqrt (G'.inner x (v i) (v i)))
      ≤ (Real.sqrt K) ^ k
          * Finset.univ.prod (fun i : Fin k => Real.sqrt (G.inner x (v i) (v i))) := by
    calc Finset.univ.prod (fun i : Fin k => Real.sqrt (G'.inner x (v i) (v i)))
        ≤ Finset.univ.prod
            (fun i : Fin k => Real.sqrt K * Real.sqrt (G.inner x (v i) (v i))) :=
          Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => hfac (v i))
      _ = (Real.sqrt K) ^ k
            * Finset.univ.prod (fun i : Fin k => Real.sqrt (G.inner x (v i) (v i))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (Finset.univ.prod (fun i : Fin k => Real.sqrt (G'.inner x (v i) (v i))))
        * Real.sqrt (G'.inner x a a) * Real.sqrt (G'.inner x b b) * Real.sqrt (G'.inner x c c)
      ≤ ((Real.sqrt K) ^ k
            * Finset.univ.prod (fun i : Fin k => Real.sqrt (G.inner x (v i) (v i))))
          * (Real.sqrt K * Real.sqrt (G.inner x a a))
          * (Real.sqrt K * Real.sqrt (G.inner x b b))
          * (Real.sqrt K * Real.sqrt (G.inner x c c)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul hprod (hfac a)
          (Real.sqrt_nonneg _) (by positivity)) (hfac b)
          (Real.sqrt_nonneg _) (by positivity)) (hfac c)
          (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt K) ^ (k + 3) *
          ((Finset.univ.prod (fun i : Fin k => Real.sqrt (G.inner x (v i) (v i))))
            * Real.sqrt (G.inner x a a) * Real.sqrt (G.inner x b b)
            * Real.sqrt (G.inner x c c)) := by
        rw [pow_add]
        ring

/-- **The derivative scaffold for the Gronwall step.**  For `s ∈ (T/2, t)` with `t ∈ [T/2, T)` the
function

  `ψ : ℝ → ℝ := fun r ↦ valOp (tower (lcOf (G 0)) (fun _ => aOf G r) k) x v a b c`

(unnormalised; the constant product `y := ∏√(G t-norms)` is carried through untouched by the
Gronwall) is differentiable at `s`, with derivative the level-`k` reaction evaluated at the same
tuple.  This is `tower_aOf_valOp_hasDerivAt` (proved above) with its interior-time hypothesis
`· ∈ Ioo 0 T` discharged from the interval data `T/2 < s < t < T`. -/
theorem towerVal_hasDerivAt
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T) {s : ℝ} (hs : s ∈ Set.Ioo (T / 2) t)
    (k : ℕ) (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    HasDerivAt (fun r : ℝ => Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G r) k) x v a b c)
      (Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (dAOfBase G s) k) x v a b c) s :=
  tower_aOf_valOp_hasDerivAt (I := I) (M := M) hLC G hflow
    ⟨by linarith [hs.1, hT], by linarith [hs.2, ht.2]⟩ k x v a b c

/-! ## The closing Grönwall assembly

The lemmas in this section are the *assembly* of step (4) of the module docstring.  They turn

* the **Clairaut identity** `tower_aOf_valOp_hasDerivAt` (proved above),
* the **parametric reaction bound** (taken here as the explicit
  hypothesis `hreact` below (in the original module this is the delegated `dAOfTowerBoundShiPar`)),
* the **slice bound** at `t = T/2` (`covKAExt_bound_sliceT`, proved) and
* the **`G s`-vs-`G t` comparison** (`smet_quadForm_le_of_hmet`, `prod_sqrt_le_of_quadForm_le`,
  proved above)

into the uniform bound `∀ t ∈ [T/2,T), ValBound G t k (∇^{G 0,k}aOf(G t)) Cf`.

The mechanism is the mean-value inequality on *small* time steps together with the *monotone*
envelope

  `Mt τ := sSup {psi s : s ∈ [T/2,τ]}`,   `psi s := sInf {U ≥ 0 : ValBound G s k (∇^{G 0,k}aOf(G s)) U}`

(so `psi s` is the least valid operator-norm constant at time `s`).  On a step `[τ,τ']` the
reaction bound may be applied with the *single* constant `Mt τ'` — it dominates `psi r` for every
`r ≤ τ'` — and the mean-value inequality then gives

  `Mt τ' ≤ K·(Mt τ + (τ'-τ)·C·(1 + Σ_{j<k}B_j + Mt τ'))`,

which closes for `K(τ'-τ)C ≤ 1/2`; iterating over a grid of fixed step from `T/2` up to the last
grid point below `T` (the final jump uses the *target* time) gives a single constant valid for all
`t ∈ [T/2,T)`.  This is the *integral* form of the Grönwall, in the discretised shape that avoids
any measurability issue: the monotone envelope supplies at each step the finiteness that a
one-sided differential Grönwall lacks (see the warning in the module docstring). -/

/-- The `√⟨·,·⟩`-product of `ATower.ValBound`, as a single factor. -/
noncomputable def qf {k : ℕ} (G : ℝ → Submission.Diff.SMet I M) (s : ℝ) (x : M)
    (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) : ℝ :=
  (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G s).inner x (v i) (v i))))
    * Real.sqrt ((G s).inner x a a) * Real.sqrt ((G s).inner x b b)
    * Real.sqrt ((G s).inner x c c)

lemma qf_nonneg {k : ℕ} (G : ℝ → Submission.Diff.SMet I M) (s : ℝ) (x : M)
    (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) : 0 ≤ qf G s x v a b c :=
  mul_nonneg (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- `ATower.ValBound`, written with the single product factor `qf`. -/
lemma valBound_iff {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {s U : ℝ}
    {τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k} :
    Work.Diff.EXT.ATower.ValBound G s k τ U ↔
      ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp τ x v a b c| ≤ U * qf G s x v a b c := by
  constructor
  · intro h x v a b c
    calc |Work.Diff.EXT.ATower.valOp τ x v a b c|
        ≤ U * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G s).inner x (v i) (v i))))
          * Real.sqrt ((G s).inner x a a) * Real.sqrt ((G s).inner x b b)
          * Real.sqrt ((G s).inner x c c) := h x v a b c
      _ = U * qf G s x v a b c := by rw [qf]; ring
  · intro h x v a b c
    calc |Work.Diff.EXT.ATower.valOp τ x v a b c|
        ≤ U * qf G s x v a b c := h x v a b c
      _ = U * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G s).inner x (v i) (v i))))
          * Real.sqrt ((G s).inner x a a) * Real.sqrt ((G s).inner x b b)
          * Real.sqrt ((G s).inner x c c) := by rw [qf]; ring

/-- The level-`k` tower of `aOf G s` with respect to the fixed connection `∇^{G 0}`. -/
noncomputable def levT (G : ℝ → Submission.Diff.SMet I M) (k : ℕ) (s : ℝ) :
    Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k :=
  Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G s) k

/-- The level-`k` tower of the reaction `∂ₜ aOf`. -/
noncomputable def levR (G : ℝ → Submission.Diff.SMet I M) (k : ℕ) (s : ℝ) :
    Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k :=
  Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
    (Work.Diff.EXT.ConnCov.dAOfBase G s) k

/-- The *least* valid operator-norm constant of the level-`k` tower of `aOf G s`. -/
noncomputable def psi (G : ℝ → Submission.Diff.SMet I M) (k : ℕ) (s : ℝ) : ℝ :=
  sInf {U : ℝ | 0 ≤ U ∧ Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U}

/-- The monotone envelope of `psi` over `[T/2,τ]`. -/
noncomputable def Mt (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (k : ℕ) (τ : ℝ) : ℝ :=
  sSup (psi G k '' Set.Icc (T / 2) τ)

/-- `psi` is below every valid constant. -/
lemma psi_le_of_mem {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {s U : ℝ} (hU0 : 0 ≤ U)
    (hV : Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U) :
    psi G k s ≤ U :=
  csInf_le ⟨0, fun _ hy => hy.1⟩ ⟨hU0, hV⟩

/-- `psi` is nonnegative as soon as a valid constant exists. -/
lemma psi_nonneg {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {s U : ℝ} (hU0 : 0 ≤ U)
    (hV : Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U) : 0 ≤ psi G k s :=
  le_csInf ⟨U, hU0, hV⟩ fun _ hb => hb.1

/-- `psi` is itself a valid constant. -/
lemma psi_valBound {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {s U₀ : ℝ} (hU₀ : 0 ≤ U₀)
    (hV₀ : Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U₀) :
    Work.Diff.EXT.ATower.ValBound G s k (levT G k s) (psi G k s) := by
  have hV₀' := valBound_iff.mp hV₀
  rw [valBound_iff]
  intro x v a b c
  by_cases hq : qf G s x v a b c = 0
  · have h1 := hV₀' x v a b c
    have hzero : |Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c| = 0 :=
      le_antisymm (by rw [hq, mul_zero] at h1; exact h1) (abs_nonneg _)
    rw [hzero, hq, mul_zero]
  · have hqpos : 0 < qf G s x v a b c := lt_of_le_of_ne (qf_nonneg G s x v a b c) (Ne.symm hq)
    have hle : |Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c| / qf G s x v a b c
        ≤ psi G k s :=
      le_csInf ⟨U₀, hU₀, hV₀⟩ fun W' hW' => by
        rw [div_le_iff₀ hqpos]
        exact (valBound_iff.mp hW'.2) x v a b c
    calc |Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c|
        = (|Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c| / qf G s x v a b c)
            * qf G s x v a b c := (div_mul_cancel₀ _ hq).symm
      _ ≤ psi G k s * qf G s x v a b c := mul_le_mul_of_nonneg_right hle hqpos.le

/-- `ValBound` is monotone in the constant. -/
lemma valBound_mono {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {s U U' : ℝ}
    {τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k}
    (h : Work.Diff.EXT.ATower.ValBound G s k τ U) (hle : U ≤ U') :
    Work.Diff.EXT.ATower.ValBound G s k τ U' := by
  rw [valBound_iff] at h ⊢
  intro x v a b c
  exact le_trans (h x v a b c) (mul_le_mul_of_nonneg_right hle (qf_nonneg G s x v a b c))

/-- `psi s ≤ Mt τ` for `s ∈ [T/2,τ]`. -/
lemma psi_le_Mt {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {T τ s : ℝ}
    (hbd : BddAbove (psi G k '' Set.Icc (T / 2) τ)) (hs : s ∈ Set.Icc (T / 2) τ) :
    psi G k s ≤ Mt G T k τ :=
  le_csSup hbd (Set.mem_image_of_mem _ hs)

/-- `Mt τ` is below any bound valid on `[T/2,τ]`. -/
lemma Mt_le {k : ℕ} {G : ℝ → Submission.Diff.SMet I M} {T τ q : ℝ}
    (hne : (psi G k '' Set.Icc (T / 2) τ).Nonempty)
    (h : ∀ s ∈ Set.Icc (T / 2) τ, psi G k s ≤ q) : Mt G T k τ ≤ q :=
  csSup_le hne fun b hb => by
    obtain ⟨s, hs, rfl⟩ := hb
    exact h s hs

/-- **The Grönwall recursion on one time step.**  If the reaction is bounded by
`Cd·(1 + Σ_{j<k}B_j + U)` whenever `U` is a valid level-`k` constant, then the monotone envelope
satisfies `Mt τ' ≤ 2K₁·Mt τ + 2K₁·(τ'-τ)·Cd·(1 + Σ_{j<k}B_j)` for steps with
`K₁·(τ'-τ)·Cd ≤ 1/2`.

The bound is obtained by the mean-value inequality from `τ` to `τ'`, using the *single* constant
`Mt τ'` in the reaction bound (it dominates `psi r` for every `r ≤ τ'`). -/
theorem Mt_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (k : ℕ) (B : ℕ → ℝ) {K₁ Cd : ℝ}
    (hK₁ : 1 ≤ K₁) (hCd0 : 0 ≤ Cd) (hB : ∀ j, 0 ≤ B j)
    (hcmp : ∀ (s r : ℝ), s ∈ Set.Ico (T / 2) T → r ∈ Set.Ico (T / 2) T → ∀ (x : M)
      (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
      qf G r x v a b c ≤ K₁ * qf G s x v a b c)
    (hvalid : ∀ s ∈ Set.Ico (T / 2) T, ∃ U : ℝ, 0 ≤ U ∧
      Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U)
    (hreact : ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k (levT G k t) U →
      ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp (levR G k t) x v a b c|
          ≤ Cd * (1 + Finset.sum (Finset.range k) B + U) * qf G t x v a b c)
    (hLB : ∀ τ ∈ Set.Ico (T / 2) T, BddAbove (psi G k '' Set.Icc (T / 2) τ))
    {τ τ' : ℝ} (hτ : τ ∈ Set.Ico (T / 2) T) (hτ' : τ' ∈ Set.Ioo τ T)
    (hsmall : K₁ * (τ' - τ) * Cd ≤ 1 / 2) :
    Mt G T k τ' ≤ 2 * K₁ * Mt G T k τ
      + 2 * K₁ * (τ' - τ) * Cd * (1 + Finset.sum (Finset.range k) B) := by
  have hBsum : 0 ≤ Finset.sum (Finset.range k) B := Finset.sum_nonneg fun j _ => hB j
  have hτ'T : τ' ∈ Set.Ico (T / 2) T := ⟨hτ.1.trans hτ'.1.le, hτ'.2⟩
  have hMbd : BddAbove (psi G k '' Set.Icc (T / 2) τ') := hLB τ' hτ'T
  have hM0 : 0 ≤ Mt G T k τ := by
    obtain ⟨U, hU0, hV⟩ := hvalid τ hτ
    exact le_trans (psi_nonneg hU0 hV) (psi_le_Mt (hLB τ hτ) ⟨hτ.1, le_refl τ⟩)
  have hMt0 : 0 ≤ Mt G T k τ' := by
    obtain ⟨U, hU0, hV⟩ := hvalid (T / 2) ⟨le_refl _, lt_of_le_of_lt hτ.1 hτ.2⟩
    exact le_trans (psi_nonneg hU0 hV)
      (psi_le_Mt hMbd ⟨le_refl _, le_of_lt (lt_of_le_of_lt hτ.1 hτ'.1)⟩)
  -- the value estimate on `(τ, τ']`: this is the mean-value inequality
  have hkey : ∀ s ∈ Set.Ioc τ τ', ∀ (x : M) (v : Fin k → TangentSpace I x)
      (a b c : TangentSpace I x),
      |Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c|
        ≤ K₁ * (Mt G T k τ + (τ' - τ) * (Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ')))
            * qf G s x v a b c := by
    intro s hs x v a b c
    have hsT : s ∈ Set.Ico (T / 2) T := ⟨hτ.1.trans hs.1.le, lt_of_le_of_lt hs.2 hτ'.2⟩
    -- the derivative bound at every interior point
    have hderiv : ∀ r ∈ Set.Icc τ s, HasDerivWithinAt
        (fun u : ℝ => Work.Diff.EXT.ATower.valOp (levT G k u) x v a b c)
        (Work.Diff.EXT.ATower.valOp (levR G k r) x v a b c) (Set.Icc τ s) r := by
      intro r hr
      have hrT : r ∈ Set.Ioo 0 T :=
        ⟨by linarith [hτ.1, hτ.2, hr.1], lt_of_le_of_lt hr.2 (lt_of_le_of_lt hs.2 hτ'.2)⟩
      exact (tower_aOf_valOp_hasDerivAt (I := I) (M := M) hLC G hflow hrT k x v a b c).hasDerivWithinAt
    have hbd : ∀ r ∈ Set.Ico τ s,
        ‖Work.Diff.EXT.ATower.valOp (levR G k r) x v a b c‖
          ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁ * qf G s x v a b c := by
      intro r hr
      have hrT : r ∈ Set.Ico (T / 2) T :=
        ⟨hτ.1.trans hr.1, lt_of_lt_of_le (lt_of_lt_of_le hr.2 hs.2) hτ'.2.le⟩
      have hrIcc : r ∈ Set.Icc (T / 2) τ' :=
        ⟨hrT.1, le_of_lt (lt_of_lt_of_le hr.2 hs.2)⟩
      have hpsi : psi G k r ≤ Mt G T k τ' := psi_le_Mt hMbd hrIcc
      have hVU : Work.Diff.EXT.ATower.ValBound G r k (levT G k r) (Mt G T k τ') :=
        valBound_mono (psi_valBound (hvalid r hrT).choose_spec.1 (hvalid r hrT).choose_spec.2) hpsi
      have hrc := hreact r hrT (Mt G T k τ') hMt0 hVU x v a b c
      have hcmp2 : qf G r x v a b c ≤ K₁ * qf G s x v a b c := hcmp s r hsT hrT x v a b c
      have hfac0 : 0 ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') :=
        mul_nonneg hCd0 (by linarith)
      rw [Real.norm_eq_abs]
      calc |Work.Diff.EXT.ATower.valOp (levR G k r) x v a b c|
          ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * qf G r x v a b c := hrc
        _ ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ')
              * (K₁ * qf G s x v a b c) := mul_le_mul_of_nonneg_left hcmp2 hfac0
        _ = Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁
              * qf G s x v a b c := by ring
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbd s ⟨hs.1.le, le_refl s⟩
    simp only [Real.norm_eq_abs] at hmv
    -- the value at `τ`
    have htau : |Work.Diff.EXT.ATower.valOp (levT G k τ) x v a b c|
        ≤ Mt G T k τ * K₁ * qf G s x v a b c := by
      have hpsi : psi G k τ ≤ Mt G T k τ := psi_le_Mt (hLB τ hτ) ⟨hτ.1, le_refl τ⟩
      have hVU := psi_valBound (hvalid τ hτ).choose_spec.1 (hvalid τ hτ).choose_spec.2
      have hv := (valBound_iff.mp hVU) x v a b c
      have hcmp2 : qf G τ x v a b c ≤ K₁ * qf G s x v a b c := hcmp s τ hsT hτ x v a b c
      calc |Work.Diff.EXT.ATower.valOp (levT G k τ) x v a b c|
          ≤ psi G k τ * qf G τ x v a b c := hv
        _ ≤ Mt G T k τ * (K₁ * qf G s x v a b c) :=
            mul_le_mul hpsi hcmp2 (qf_nonneg G τ x v a b c) (le_trans (psi_nonneg
              (hvalid τ hτ).choose_spec.1 (hvalid τ hτ).choose_spec.2) hpsi)
        _ = Mt G T k τ * K₁ * qf G s x v a b c := by ring
    have hqf0 : 0 ≤ qf G s x v a b c := qf_nonneg G s x v a b c
    have hconst : 0 ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁ :=
      mul_nonneg (mul_nonneg hCd0 (by linarith)) (le_trans zero_le_one hK₁)
    have hτ's : τ' - τ ≤ τ' - τ := le_refl _
    calc |Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c|
        = |(Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c
            - Work.Diff.EXT.ATower.valOp (levT G k τ) x v a b c)
            + Work.Diff.EXT.ATower.valOp (levT G k τ) x v a b c| := by rw [sub_add_cancel]
      _ ≤ |Work.Diff.EXT.ATower.valOp (levT G k s) x v a b c
            - Work.Diff.EXT.ATower.valOp (levT G k τ) x v a b c|
          + |Work.Diff.EXT.ATower.valOp (levT G k τ) x v a b c| := abs_add_le _ _
      _ ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁ * qf G s x v a b c
            * (s - τ) + Mt G T k τ * K₁ * qf G s x v a b c := by
          refine add_le_add hmv htau
      _ ≤ K₁ * (Mt G T k τ + (τ' - τ) * (Cd * (1 + Finset.sum (Finset.range k) B
            + Mt G T k τ'))) * qf G s x v a b c := by
          have hsτ : s - τ ≤ τ' - τ := by linarith [hs.2]
          have hA0' : 0 ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁
              * qf G s x v a b c :=
            mul_nonneg (mul_nonneg (mul_nonneg hCd0 (by linarith))
              (le_trans zero_le_one hK₁)) (qf_nonneg G s x v a b c)
          have hCf : Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁
              * qf G s x v a b c * (s - τ)
              ≤ Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁
                * qf G s x v a b c * (τ' - τ) :=
            mul_le_mul_of_nonneg_left hsτ hA0'
          have hgoal : K₁ * (Mt G T k τ + (τ' - τ) * (Cd * (1 + Finset.sum (Finset.range k) B
                + Mt G T k τ'))) * qf G s x v a b c
              = Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ') * K₁
                  * qf G s x v a b c * (τ' - τ) + Mt G T k τ * K₁ * qf G s x v a b c := by
            ring
          rw [hgoal]
          linarith [hCf]
  -- the sup over `s ∈ [T/2,τ']`
  have hsup : Mt G T k τ' ≤ K₁ * (Mt G T k τ + (τ' - τ) * (Cd *
      (1 + Finset.sum (Finset.range k) B + Mt G T k τ'))) := by
    refine Mt_le ⟨psi G k (T / 2), Set.mem_image_of_mem _
      ⟨le_refl _, le_of_lt (lt_of_le_of_lt hτ.1 hτ'.1)⟩⟩ ?_
    intro s hsS
    have h3 : 0 ≤ (τ' - τ) * (Cd * (1 + Finset.sum (Finset.range k) B + Mt G T k τ')) :=
      mul_nonneg (by linarith [hτ'.1]) (mul_nonneg hCd0 (by linarith))
    have hRHS : 0 ≤ K₁ * (Mt G T k τ + (τ' - τ) * (Cd *
        (1 + Finset.sum (Finset.range k) B + Mt G T k τ'))) :=
      mul_nonneg (le_trans zero_le_one hK₁) (by linarith [hM0, h3])
    have h2 : Mt G T k τ ≤ K₁ * (Mt G T k τ + (τ' - τ) * (Cd *
        (1 + Finset.sum (Finset.range k) B + Mt G T k τ'))) := by
      calc Mt G T k τ ≤ Mt G T k τ + (τ' - τ) * (Cd *
            (1 + Finset.sum (Finset.range k) B + Mt G T k τ')) := le_add_of_nonneg_right h3
        _ ≤ K₁ * (Mt G T k τ + (τ' - τ) * (Cd *
            (1 + Finset.sum (Finset.range k) B + Mt G T k τ'))) := by
            rw [mul_comm]
            exact le_mul_of_one_le_left (by linarith [hM0, h3]) hK₁
    rcases lt_or_ge s τ with hsτ | hτs
    · have h1 : psi G k s ≤ Mt G T k τ := psi_le_Mt (hLB τ hτ) ⟨hsS.1, hsτ.le⟩
      exact le_trans h1 h2
    · rcases eq_or_lt_of_le hτs with rfl | hlt
      · have h1 : psi G k τ ≤ Mt G T k τ := psi_le_Mt (hLB τ hτ) ⟨hτ.1, le_refl τ⟩
        exact le_trans h1 h2
      · exact psi_le_of_mem hRHS
          (valBound_iff.mpr fun x v a b c => hkey s ⟨hlt, hsS.2⟩ x v a b c)
  -- solve the linear inequality
  have hc : K₁ * (τ' - τ) * Cd ≤ 1 / 2 := hsmall
  have hfin : Mt G T k τ' * (1 / 2) ≤ K₁ * Mt G T k τ + K₁ * (τ' - τ) * Cd
      * (1 + Finset.sum (Finset.range k) B) := by
    have hexpand : K₁ * (Mt G T k τ + (τ' - τ) * (Cd *
        (1 + Finset.sum (Finset.range k) B + Mt G T k τ')))
        = K₁ * Mt G T k τ + K₁ * (τ' - τ) * Cd * (1 + Finset.sum (Finset.range k) B)
          + K₁ * (τ' - τ) * Cd * Mt G T k τ' := by ring
    rw [hexpand] at hsup
    nlinarith [hsup, hMt0, hc, hK₁, hCd0, hBsum, hτ'.1, hM0]
  nlinarith [hfin]

/-- **The assembly.**  From the parametric reaction bound `hreact`, the slice bound `hslice` at
`T/2` and the comparison of the `G s`- and `G t`-products, the level-`k` tower of `aOf` is uniformly
bounded on `[T/2,T)`. -/
theorem valBound_uniform_of_react
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (k : ℕ) (B : ℕ → ℝ) {K₁ Cd D0 : ℝ}
    (hK₁ : 1 ≤ K₁) (hCd0 : 0 ≤ Cd) (hB : ∀ j, 0 ≤ B j) (hD00 : 0 ≤ D0)
    (hcmp : ∀ (s r : ℝ), s ∈ Set.Ico (T / 2) T → r ∈ Set.Ico (T / 2) T → ∀ (x : M)
      (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
      qf G r x v a b c ≤ K₁ * qf G s x v a b c)
    (hvalid : ∀ s ∈ Set.Ico (T / 2) T, ∃ U : ℝ, 0 ≤ U ∧
      Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U)
    (hreact : ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k (levT G k t) U →
      ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp (levR G k t) x v a b c|
          ≤ Cd * (1 + Finset.sum (Finset.range k) B + U) * qf G t x v a b c)
    (hLB : ∀ τ ∈ Set.Ico (T / 2) T, BddAbove (psi G k '' Set.Icc (T / 2) τ))
    (hslice : Mt G T k (T / 2) ≤ D0) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t k (levT G k t) Cf := by
  classical
  have hBsum : 0 ≤ Finset.sum (Finset.range k) B := Finset.sum_nonneg fun j _ => hB j
  have hK₁pos : 0 ≤ K₁ := le_trans zero_le_one hK₁
  have h1B : 0 ≤ 1 + Finset.sum (Finset.range k) B := by linarith
  have h2K : (0 : ℝ) ≤ 2 * K₁ := by linarith
  -- the step
  set δ : ℝ := 1 / (2 * K₁ * (Cd + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  have hsmallδ : K₁ * δ * Cd ≤ 1 / 2 := by
    have hK₁ne : K₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hK₁)
    have hcd1 : (0 : ℝ) < Cd + 1 := by linarith
    have hden : (0 : ℝ) < 2 * (Cd + 1) := by linarith
    have heq : K₁ * δ * Cd = Cd / (2 * (Cd + 1)) := by
      rw [hδdef]
      field_simp
    rw [heq, div_le_iff₀ hden]
    linarith
  -- the constants of the recursion
  have hcf0 : 0 ≤ 2 * K₁ * δ * Cd * (1 + Finset.sum (Finset.range k) B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK₁pos) hδpos.le) hCd0) h1B
  set f : ℕ → ℝ := fun j => (2 * K₁) ^ j * D0
      + 2 * K₁ * δ * Cd * (1 + Finset.sum (Finset.range k) B)
        * ∑ i ∈ Finset.range j, (2 * K₁) ^ i with hfdef
  have hf0 : f 0 = D0 := by simp [hfdef]
  have hgeom : ∀ j : ℕ, (2 * K₁) ^ j
      = (2 * K₁ - 1) * ∑ i ∈ Finset.range j, (2 * K₁) ^ i + 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ, pow_succ, ih]
        ring
  have hfS : ∀ j, f (j + 1) = 2 * K₁ * f j + 2 * K₁ * δ * Cd
      * (1 + Finset.sum (Finset.range k) B) := by
    intro j
    simp only [hfdef]
    rw [Finset.sum_range_succ, pow_succ, hgeom j]
    ring
  have hff0 : ∀ j, 0 ≤ f j := by
    intro j
    rw [hfdef]
    refine add_nonneg (mul_nonneg (pow_nonneg h2K _) hD00) ?_
    exact mul_nonneg hcf0 (Finset.sum_nonneg fun i _ => pow_nonneg h2K _)
  have hfmono : Monotone f := by
    refine monotone_nat_of_le_succ fun j => ?_
    rw [hfS j]
    have h1 : 0 ≤ (2 * K₁ - 1) * f j := mul_nonneg (by linarith) (hff0 j)
    linarith
  -- the grid induction
  have hgrid : ∀ j : ℕ, T / 2 + (j : ℝ) * δ < T → Mt G T k (T / 2 + (j : ℝ) * δ) ≤ f j := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [hf0]
        simpa using hslice
    | succ j ih =>
        intro hj
        have hcast : T / 2 + ((j : ℝ) + 1) * δ = T / 2 + (↑(j + 1) : ℝ) * δ := by
          push_cast; ring
        have hjR : T / 2 + ((j : ℝ) + 1) * δ < T := by rw [hcast]; exact hj
        have hj' : T / 2 + (j : ℝ) * δ < T := by
          have : T / 2 + (j : ℝ) * δ < T / 2 + ((j : ℝ) + 1) * δ := by linarith [hδpos]
          linarith
        have hjmem : T / 2 + (j : ℝ) * δ ∈ Set.Ico (T / 2) T :=
          ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδpos.le), hj'⟩
        have hdiffj : T / 2 + ((j : ℝ) + 1) * δ - (T / 2 + (j : ℝ) * δ) = δ := by ring
        have hstep := Mt_step (I := I) (M := M) hLC G T hflow k B hK₁ hCd0 hB hcmp hvalid hreact
          hLB hjmem ⟨by linarith [hδpos], hjR⟩ (by rw [hdiffj]; exact hsmallδ)
        rw [hdiffj] at hstep
        have hih := ih hj'
        have h1 : 2 * K₁ * Mt G T k (T / 2 + (j : ℝ) * δ) + 2 * K₁ * δ * Cd
            * (1 + Finset.sum (Finset.range k) B) ≤ 2 * K₁ * f j + 2 * K₁ * δ * Cd
              * (1 + Finset.sum (Finset.range k) B) :=
          add_le_add (mul_le_mul_of_nonneg_left hih h2K) le_rfl
        rw [← hcast, hfS j]
        exact le_trans hstep h1
  -- the final constant
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ (N : ℝ) * δ := by
    obtain ⟨N, hN⟩ := exists_nat_ge (T / δ)
    refine ⟨N, ?_⟩
    rw [div_le_iff₀ hδpos] at hN
    exact hN
  refine ⟨f N, hff0 N, ?_⟩
  · intro t ht
    set i : ℕ := ⌊(t - T / 2) / δ⌋₊ with hidef
    have hile : (i : ℝ) * δ ≤ t - T / 2 := by
      have h1 : ((i : ℕ) : ℝ) ≤ (t - T / 2) / δ := by
        rw [hidef]
        exact Nat.floor_le (div_nonneg (by linarith [ht.1]) hδpos.le)
      have h2 : ((i : ℕ) : ℝ) * δ ≤ ((t - T / 2) / δ) * δ :=
        mul_le_mul_of_nonneg_right h1 hδpos.le
      rwa [div_mul_cancel₀ _ hδpos.ne'] at h2
    have hilt : t - T / 2 < ((i : ℝ) + 1) * δ := by
      have h1 : (t - T / 2) / δ < ((i : ℕ) : ℝ) + 1 := by
        rw [hidef]
        exact Nat.lt_floor_add_one _
      have h2 := mul_lt_mul_of_pos_right h1 hδpos
      rwa [div_mul_cancel₀ _ hδpos.ne'] at h2
    have hsi : T / 2 + (i : ℝ) * δ ≤ t := by linarith
    have hsiT : T / 2 + (i : ℝ) * δ < T := lt_of_le_of_lt hsi ht.2
    have hiN : i < N := by
      have h1 : ((i : ℕ) : ℝ) * δ < (N : ℝ) * δ := by
        have h2 : T ≤ (N : ℝ) * δ := hN
        linarith
      have h3 : ((i : ℕ) : ℝ) < (N : ℝ) := lt_of_mul_lt_mul_right h1 hδpos.le
      exact_mod_cast h3
    have hMi := hgrid i hsiT
    have hfN : f i ≤ f N := hfmono (by omega)
    have hmain : Mt G T k t ≤ f N := by
      rcases eq_or_lt_of_le hsi with heq | hlt
      · rw [← heq]
        exact le_trans hMi hfN
      · have hrec := Mt_step (I := I) (M := M) hLC G T hflow k B hK₁ hCd0 hB hcmp hvalid hreact
          hLB ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδpos.le), hsiT⟩
          ⟨hlt, ht.2⟩ (by
            have hdiff : t - (T / 2 + (i : ℝ) * δ) ≤ δ := by linarith [hilt]
            have h1 : K₁ * (t - (T / 2 + (i : ℝ) * δ)) * Cd ≤ K₁ * δ * Cd :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff hK₁pos) hCd0
            linarith [h1, hsmallδ])
        have h1 : 2 * K₁ * Mt G T k (T / 2 + (i : ℝ) * δ) + 2 * K₁ * δ * Cd
            * (1 + Finset.sum (Finset.range k) B) ≤ 2 * K₁ * f i + 2 * K₁ * δ * Cd
              * (1 + Finset.sum (Finset.range k) B) :=
          add_le_add (mul_le_mul_of_nonneg_left hMi h2K) le_rfl
        have h4 : 2 * K₁ * (t - (T / 2 + (i : ℝ) * δ)) * Cd
            * (1 + Finset.sum (Finset.range k) B)
            ≤ 2 * K₁ * δ * Cd * (1 + Finset.sum (Finset.range k) B) := by
          have hdiff : t - (T / 2 + (i : ℝ) * δ) ≤ δ := by linarith [hilt]
          calc 2 * K₁ * (t - (T / 2 + (i : ℝ) * δ)) * Cd
                * (1 + Finset.sum (Finset.range k) B)
              ≤ (2 * K₁) * δ * Cd * (1 + Finset.sum (Finset.range k) B) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hdiff h2K) hCd0) h1B
            _ = 2 * K₁ * δ * Cd * (1 + Finset.sum (Finset.range k) B) := by ring
        have h5 : 2 * K₁ * f i + 2 * K₁ * δ * Cd * (1 + Finset.sum (Finset.range k) B)
            = f (i + 1) := (hfS i).symm
        have h3 := hrec
        have h6 : f (i + 1) ≤ f N := hfmono (by omega)
        linarith [h1, h3, h4, h5, h6]
    have hpsi : psi G k t ≤ Mt G T k t := psi_le_Mt (hLB t ht) ⟨ht.1, le_refl t⟩
    exact valBound_mono (psi_valBound (hvalid t ht).choose_spec.1 (hvalid t ht).choose_spec.2)
      (le_trans hpsi hmain)

theorem covKAExt_bound_of_react
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (hReact : ∀ (k : ℕ) (B : ℕ → ℝ), (∀ j, 0 ≤ B j) →
      (∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
        Work.Diff.EXT.ATower.ValBound G t j (levT G j t) (B j)) →
      ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
        Work.Diff.EXT.ATower.ValBound G t k (levT G k t) U →
        ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
          |Work.Diff.EXT.ATower.valOp (levR G k t) x v a b c|
            ≤ Cd * (1 + Finset.sum (Finset.range k) B + U) * qf G t x v a b c) :
    ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
      |Work.Diff.EXT.covKAExt G t k (fun i => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
          (Submission.Diff.smoothExt x c) x|
        ≤ Ck * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c) := by
  classical
  -- the comparison of the `G s`- and the `G t`-products
  have hcmp : ∀ (k : ℕ) (s r : ℝ), s ∈ Set.Ico (T / 2) T → r ∈ Set.Ico (T / 2) T →
      ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
      qf G r x v a b c ≤ (Real.sqrt (Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T))) ^ (k + 3)
        * qf G s x v a b c := by
    intro k s r hs hr x v a b c
    have hs0 : s ∈ Set.Ico 0 T := ⟨by linarith [hs.1, hT], hs.2⟩
    have hr0 : r ∈ Set.Ico 0 T := ⟨by linarith [hr.1, hT], hr.2⟩
    have hquad : ∀ u : TangentSpace I x, (G r).inner x u u
        ≤ Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T) * (G s).inner x u u :=
      fun u => smet_quadForm_le_of_hmet (I := I) (M := M) G T C hT hC hmet r s hr0 hs0 x u
    have h := prod_sqrt_le_of_quadForm_le (I := I) (M := M) (G := G s) (G' := G r)
      (Real.exp_nonneg _) k v a b c hquad
    simpa only [qf] using h
  -- the local validity of a level-`k` constant
  have hvalid : ∀ k : ℕ, ∀ s ∈ Set.Ico (T / 2) T, ∃ U : ℝ, 0 ≤ U ∧
      Work.Diff.EXT.ATower.ValBound G s k (levT G k s) U :=
    fun k s hs => covKAExt_bound_local (I := I) (M := M) hLC G T C hT hC hflow hbound hmet k s hs
  have hLB : ∀ k : ℕ, ∀ τ ∈ Set.Ico (T / 2) T,
      BddAbove (psi G k '' Set.Icc (T / 2) τ) := by
    intro k τ hτ
    obtain ⟨W, hW0, hW⟩ :=
      covKAExt_bound_locBdd (I := I) (M := M) hLC G T C hT hC hflow hmet k τ hτ
    refine ⟨W, ?_⟩
    rintro q ⟨s, hs, rfl⟩
    exact psi_le_of_mem hW0 (hW s hs)
  have hK₁ : ∀ k : ℕ, 1 ≤ (Real.sqrt (Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T))) ^ (k + 3) := by
    intro k
    have h1 : (1 : ℝ) ≤ Real.sqrt (Real.exp (4 * ((Module.finrank ℝ E : ℝ) * C) * T)) := by
      rw [← Real.sqrt_one]
      refine Real.sqrt_le_sqrt ?_
      rw [Real.one_le_exp_iff]
      have : 0 ≤ (Module.finrank ℝ E : ℝ) * C :=
        mul_nonneg (Nat.cast_nonneg _) hC
      nlinarith
    exact one_le_pow₀ h1
  -- the induction on `k`
  have hmain : ∀ k : ℕ, ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t k (levT G k t) Cf := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨C0, hC00, hC0⟩ := covKAExt_bound_zero (I := I) (M := M) hLC G T C hT hC hflow
          hbound hmet hShi
        refine ⟨C0, hC00, fun t ht => (valBound_iff.mpr fun x v a b c => ?_)⟩
        have h := hC0 t ht x a b c
        have hv : v = Fin.elim0 := Subsingleton.elim _ _
        subst hv
        simp only [levT, Work.Diff.EXT.ATower.valOp, Work.Diff.EXT.ATower.tower, qf,
          Finset.univ_eq_empty, Finset.prod_empty, one_mul]
        calc |Work.Diff.EXT.aOf G t (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
              (Submission.Diff.smoothExt x c) x|
            ≤ C0 * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) := h
          _ = C0 * (Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c)) := by ring
      · -- the lower levels
        have hEx : ∀ j : ℕ, ∃ Cf : ℝ, 0 ≤ Cf ∧
            (j < k → ∀ t ∈ Set.Ico (T / 2) T, Work.Diff.EXT.ATower.ValBound G t j (levT G j t) Cf) := by
          intro j
          by_cases hj : j < k
          · obtain ⟨Cf, h0, hv⟩ := ih j hj
            exact ⟨Cf, h0, fun _ => hv⟩
          · exact ⟨0, le_refl 0, fun hlt => absurd hlt hj⟩
        choose B hB0 hBv using hEx
        -- the reaction bound
        obtain ⟨Cd, hCd0, hCd⟩ :=
          hReact k B hB0 (fun j hj t ht => hBv j hj t ht)
        have hreact : ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
            Work.Diff.EXT.ATower.ValBound G t k (levT G k t) U →
            ∀ (x : M) (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
              |Work.Diff.EXT.ATower.valOp (levR G k t) x v a b c|
                ≤ Cd * (1 + Finset.sum (Finset.range k) B + U) * qf G t x v a b c :=
          hCd
        -- the slice bound
        obtain ⟨Cs, hCs0, hCs⟩ := covKAExt_bound_sliceT (I := I) (M := M) hLC G T C hT hC hflow
          hbound hmet k
        have hslice : Mt G T k (T / 2) ≤ Cs := by
          refine Mt_le ⟨psi G k (T / 2), Set.mem_image_of_mem _ ⟨le_refl _, le_refl _⟩⟩ ?_
          intro s hs
          have hs' : s = T / 2 := by simpa [Set.Icc_self] using hs
          subst hs'
          exact psi_le_of_mem hCs0 hCs
        exact valBound_uniform_of_react (I := I) (M := M) hLC G T hT hflow k B
          (hK₁ k) hCd0 hB0 hCs0 (fun s r hs hr => hcmp k s r hs hr) (hvalid k) hreact (hLB k)
          hslice
  -- the target
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := hmain k
  refine ⟨Cf, hCf0, fun t ht x v a b c => ?_⟩
  have h := hCf t ht x v a b c
  simpa only [levT, Work.Diff.EXT.ATower.valOp_tower_eq_covKAExt] using h



end Work.Diff.EXT.ConnCov.V2
