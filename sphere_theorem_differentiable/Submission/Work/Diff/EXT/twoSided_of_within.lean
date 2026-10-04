/-
# Two-sided extension at the initial time: the analytic core

This file proves `Work.Diff.EXT.twoSided_of_within` (the `K`-input of area EXT, i.e. of the
continuation theorem `Submission.Diff.Extension`): a family of metrics jointly smooth on `[0,T)`
restricts, for some `ε > 0`, to a family jointly smooth on `(-ε,ε)` and agreeing with it on `[0,ε)`.

## Route

1. **Model space** (`local_ext_of_within`, proved below).  For `H : ℝ × E → Z` smooth on the slab
   `(Ico 0 T) ×ˢ U` (`U` open, `T > 0`) there are `ε > 0`, an open `V ∋ y₀`, `V ⊆ U`, and a smooth
   `K` on `(Ioo (-ε) ε) ×ˢ V` with `K = H` on `Ico 0 ε`.  The proof is the classical Borel + flat
   cut argument:
   * `jet_functions_smooth` (proved) — the pure time jets `y ↦ ∂_t^k H (0,y)` are smooth;
   * `borel_jet_on` (proved) — they are realised by a smooth two-sided `F`;
   * `pureTimeJets_sub_of_slab` + `flatOfMatching_of_pureJets` (proved below) — `H - F` is flat at
     the seam, i.e. *all* its within-jets vanish there.  This is the analytic heart: by
     `sliceJet_iteratedDerivWithin` the vanishing of the pure time jets is the vanishing of all
     one-dimensional within-derivatives of the slices `t ↦ (H-F)(t,y)`; iterating Hadamard's lemma
     (`factor_smul_of_vanishing_slice`) using `iteratedDerivWithin_smul_id_zero` produces, for every
     `N`, a smooth `Ψ_N` with `H - F = z.1^N • Ψ_N` (`IsTowerInf`); and divisibility by every power
     of the time coordinate kills the whole jet at the seam (`jets_zero_of_isTowerInf`, by induction
     on the order using `IsTowerInf_fderivWithin`; the induction is carried out for codomains in a
     universe containing that of the source, the general case being reduced to it by `ULift`);
   * `cut_of_flat_open` (proved) — the Heaviside cut of a function flat at the seam is smooth;
   * `K := F + cut` is the required extension.

2. **Manifold level.**  For a chart centre `x₀`, `chartMat_halfspace` (proved) gives smoothness of
   the chart matrix `chartMat G x₀` on `(Ico 0 T) ×ˢ (extChartAt I x₀).target`; feeding it to
   `local_ext_of_within` and symmetrising gives a smooth two-sided matrix family agreeing with the
   chart matrix on the right; it is made positive definite on the whole slab by
   `posDef_tube_of_continuous_seam` (proved by a colleague), using that the chart matrix of the
   metric `G 0` is positive definite on the chart target (`chartMatFun_zero_posDef`, proved below:
   `sum_chartMatFun_eq_inner` + injectivity of the coordinate frame).
   This is `local_chart_piece`.

3. **Gluing** (`Work.Diff.EXT.twoSided_glue_self`, a self-contained adaptation of the
   colleague's `Work.Diff.EXT.twoSided_glue_local`): the local pieces are glued over the
   compact manifold by a partition of unity into a jointly smooth two-sided family of metrics
   agreeing with `G` on the right.

The only ingredient not proved in this file is step 3; `twoSided_of_within` is assembled from
`local_chart_piece` and `twoSided_glue_self`.
-/

import ChallengeDeps
import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.borel_jet_on
import Submission.Work.Diff.EXT.cut_of_flat_open
import Submission.Work.Diff.EXT.factor_smul_of_vanishing_slice
import Submission.Work.Diff.EXT.jet_functions_smooth
import Submission.Work.Diff.EXT.chartMat_halfspace
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.JetTowerDefs
import Submission.Work.Diff.EXT.flat_of_matching_isOpen
import Submission.Work.Diff.EXT.posDef_tube_of_continuous_seam
import Submission.Work.Diff.EXT.twoSided_glue_self
import Submission.ChartBounds
import Submission.Work.Diff.EXT.sliceJet_iteratedDerivWithin
import Submission.Work.Diff.EXT.iteratedDerivWithin_smul_id_zero
import Submission.Work.Diff.EXT.IsTowerInf_fderivWithin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Making a jointly smooth one-sided family of metrics two-sided at the initial time

`Work.Diff.EXT.twoSided_of_within`: a family `G : ℝ → SMet I M` which is jointly smooth on the
half-interval `[0,T) × M` (`T > 0`) restricts, for a small `ε > 0`, to a family `K` which is
jointly smooth on the *whole* interval `(-ε, ε)` and agrees with `G` on `[0, ε)`.

## Route

1. **Model space** (`local_ext_of_within` below).  If `H : ℝ × E → Z` is `C^∞` on
   `(Ico 0 T) ×ˢ U` (`U` open in the finite-dimensional space `E`, `T > 0`), then some two-sided
   neighbourhood `(-ε,ε) × V` of `(0,y₀)` carries a `C^∞` function `K` with `K = H` on
   `(Ico 0 ε) × V`.  Proof:
   * the one-sided time-jets `a k y = ∂_t^k H(0,y)` of `H` are `C^∞` in `y`
     (`jet_functions_smooth`);
   * `borel_jet_on` realises the sequence `(a k)` by a `C^∞` function `F` with
     `iteratedDeriv k (F (·,y)) 0 = a k y`;
   * `flat_of_matching_open` then gives that all within-jets of `H - F` vanish along `{0} × V`
     (the jets are transferred from the slab over the ball on which they were defined to the
     smaller slab over `V` using `iteratedFDerivWithin_subset`, both slabs having
     `UniqueDiffOn` since they are products of a convex set with a ball);
   * `cut_of_flat_open` gives that the Heaviside cut of `H - F` is `C^∞`, so
     `K := F + (if 0 < t then H - F else 0)` is a `C^∞` two-sided extension of `H`.

2. **Manifold level** (still to be done).  For each chart centre `x₀`, the chart matrix
   `chartMat G x₀` is `C^∞` on `(Ico 0 T) ×ˢ (extChartAt I x₀).target` (`chartMat_halfspace`);
   applying step 1 componentwise gives a two-sided smooth family of matrices near
   `(extChartAt I x₀) x₀`.  Reading such a family in the coordinate frame
   (`Submission.Geodesic.frameVector`) produces a two-sided smooth symmetric 2-tensor field on a
   neighbourhood of `(0,x₀)` agreeing with `G` on the right; these neighbourhoods are positive
   definite for small `|t|` by continuity from `t = 0`.  Finitely many of them cover the compact
   `M`; with a smooth partition of unity `χ i`, set
   `K t := Σ i χ i • (χ i • chartMetric_i t + (1 - χ i) • (G 0))`.  The coefficients are
   nonnegative and sum to one, so each `K t` is positive definite, and on `[0, ε)` all the
   `chartMetric_i` agree with `G t`, so `K t = G t`.  The `SMet` structure is then built from the
   smooth symmetric positive definite section (the `isVonNBounded` field follows from positive
   definiteness on the finite-dimensional fibres).
-/

open Set Metric
open scoped ContDiff Topology

universe u v

namespace Work.Diff.EXT

variable
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-! ## From the vanishing of the one-sided time jets to flatness at the seam -/

/-- **The tower.**  If all one-dimensional within-derivatives of the slices `t ↦ δ (t,y)` vanish
at `0` (for `y` in `U`), then `δ` is divisible on the slab by every power `z ↦ z.1 ^ N` of the
time coordinate, with a quotient that again has vanishing slice derivatives at the seam.

This is Hadamard's lemma (`factor_smul_of_vanishing_slice`) iterated: at each step the quotient
vanishes on the seam (`iteratedDerivWithin_zero`), and its slice derivatives vanish by the
one-dimensional Leibniz rule in the form `iteratedDerivWithin_smul_id_zero`. -/
theorem tower_slice_zero {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (δ : ℝ × E → Z)
    (hδ : ContDiffOn ℝ (⊤ : ℕ∞) δ ((Set.Ico 0 T) ×ˢ U))
    (h0 : ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedDerivWithin j (fun t : ℝ => δ (t, y)) (Set.Ico 0 T) 0 = 0) :
    ∀ N : ℕ, ∃ Ψ : ℝ × E → Z,
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ ((Set.Ico 0 T) ×ˢ U) ∧
      (∀ z ∈ (Set.Ico 0 T) ×ˢ U, δ z = z.1 ^ N • Ψ z) ∧
      (∀ (j : ℕ) (y : E), y ∈ U →
        iteratedDerivWithin j (fun t : ℝ => Ψ (t, y)) (Set.Ico 0 T) 0 = 0) := by
  intro N
  induction N with
  | zero => exact ⟨δ, hδ, fun z _ => by simp, h0⟩
  | succ N ih =>
    obtain ⟨Ψ, hΨsm, hΨeq, hΨvan⟩ := ih
    have hΨ0 : ∀ y ∈ U, Ψ (0, y) = 0 := by
      intro y hy
      have h := hΨvan 0 y hy
      rwa [iteratedDerivWithin_zero] at h
    obtain ⟨Ψ', hΨ'sm, hΨ'eq⟩ := factor_smul_of_vanishing_slice (Z := Z) hT hU Ψ hΨsm hΨ0
    refine ⟨Ψ', hΨ'sm, ?_, ?_⟩
    · intro z hz
      rw [hΨeq z hz, hΨ'eq z hz, smul_smul, pow_succ]
    · intro j y hy
      have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => Ψ' (t, y)) (Set.Ico 0 T) :=
        hΨ'sm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => ⟨ht, hy⟩)
      refine iteratedDerivWithin_smul_id_zero (Z := Z) hT (fun t : ℝ => Ψ' (t, y)) hslice ?_ j
      intro k
      have hEqOn : Set.EqOn (fun t : ℝ => t • Ψ' (t, y)) (fun t : ℝ => Ψ (t, y))
          (Set.Ico 0 T) := fun t ht => (hΨ'eq (t, y) ⟨ht, hy⟩).symm
      have hmem : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hT⟩
      have hval : iteratedDerivWithin (k + 1) (fun t : ℝ => t • Ψ' (t, y)) (Set.Ico 0 T) 0
          = iteratedDerivWithin (k + 1) (fun t : ℝ => Ψ (t, y)) (Set.Ico 0 T) 0 :=
        iteratedDerivWithin_congr (n := k + 1) hEqOn hmem
      rw [hval]
      exact hΨvan (k + 1) y hy

/-- The tower property of `tower_slice_zero`. -/
theorem isTowerInf_of_slice_zero {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    (δ : ℝ × E → Z) (hδ : ContDiffOn ℝ (⊤ : ℕ∞) δ ((Set.Ico 0 T) ×ˢ U))
    (h0 : ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedDerivWithin j (fun t : ℝ => δ (t, y)) (Set.Ico 0 T) 0 = 0) :
    IsTowerInf ((Set.Ico 0 T) ×ˢ U) δ := by
  intro N
  obtain ⟨Ψ, hsm, heq, _⟩ := tower_slice_zero hT hU δ hδ h0 N
  exact ⟨Ψ, hsm, heq⟩

/-- **Divisibility by all powers of the time coordinate kills the whole jet at the seam.**

Induction on the order.  The `(j+1)`-st within-derivative is the `j`-th within-derivative of
`fderivWithin G s` (`iteratedFDerivWithin_succ_apply_right`), and divisibility is preserved by
`fderivWithin` (`IsTowerInf_fderivWithin`).  The codomain changes along the induction (from `Z` to
`ℝ × E →L[ℝ] Z`, and henceforth to spaces of multilinear maps in the *same* universe as
`ℝ × E →L[ℝ] Z`), so the statement is proved for codomains in a universe containing the universe of
the source; `jets_zero_of_isTowerInf` reduces the general case to this one by `ULift`. -/
private theorem jets_zero_aux {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    {W : Type (max u v)} [NormedAddCommGroup W] [NormedSpace ℝ W] :
    ∀ (j : ℕ) (G : ℝ × E → W), IsTowerInf ((Set.Ico 0 T) ×ˢ U) G → ∀ y : E, y ∈ U →
      iteratedFDerivWithin ℝ j G ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0 := by
  have hs : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ∀ y : E, y ∈ U → ((0 : ℝ), y) ∈ (Set.Ico 0 T) ×ˢ U :=
    fun y hy => ⟨⟨le_refl 0, hT⟩, hy⟩
  have key : ∀ j : ℕ,
      (∀ {W : Type (max u v)} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (G : ℝ × E → W), IsTowerInf ((Set.Ico 0 T) ×ˢ U) G → ∀ y : E, y ∈ U →
          iteratedFDerivWithin ℝ j G ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0) := by
    intro j
    induction j with
    | zero =>
      intro W _ _ G hG y hy
      rw [iteratedFDerivWithin_zero_eq_comp]
      obtain ⟨Ψ, _, heq⟩ := hG 1
      have hz : G ((0 : ℝ), y) = 0 := by
        rw [heq ((0 : ℝ), y) (hx y hy)]; simp
      rw [Function.comp_apply, hz]
      apply ContinuousMultilinearMap.ext
      intro m
      simp
    | succ j ih =>
      intro W _ _ G hG y hy
      have hD : IsTowerInf ((Set.Ico 0 T) ×ˢ U)
          (fun z => fderivWithin ℝ G ((Set.Ico 0 T) ×ˢ U) z) := IsTowerInf_fderivWithin hs hG
      have hprev := ih (W := ℝ × E →L[ℝ] W)
        (fun z => fderivWithin ℝ G ((Set.Ico 0 T) ×ˢ U) z) hD y hy
      apply ContinuousMultilinearMap.ext
      intro m
      rw [iteratedFDerivWithin_succ_apply_right hs (hx y hy)]
      rw [hprev]
      simp
  intro j G hG y hy
  exact key j G hG y hy

/-- **Divisibility by all powers of the time coordinate kills the whole jet at the seam.**  The
general-universe form of `jets_zero_aux`, obtained by lifting the target to a universe containing
the universe of the source (where the derivative recursion stays). -/
theorem jets_zero_of_isTowerInf {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    {G : ℝ × E → Z} (hG : IsTowerInf ((Set.Ico 0 T) ×ˢ U) G) :
    ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ j G ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0 := by
  have hs : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ∀ y : E, y ∈ U → ((0 : ℝ), y) ∈ (Set.Ico 0 T) ×ˢ U :=
    fun y hy => ⟨⟨le_refl 0, hT⟩, hy⟩
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) G ((Set.Ico 0 T) ×ˢ U) := by
    obtain ⟨Ψ, hΨ, heq⟩ := hG 0
    exact hΨ.congr (fun z hz => by rw [heq z hz]; simp)
  intro j
  match j with
  | 0 =>
    intro y hy
    rw [iteratedFDerivWithin_zero_eq_comp]
    obtain ⟨Ψ, _, heq⟩ := hG 1
    have hz : G ((0 : ℝ), y) = 0 := by
      rw [heq ((0 : ℝ), y) (hx y hy)]; simp
    rw [Function.comp_apply, hz]
    apply ContinuousMultilinearMap.ext
    intro m
    simp
  | k + 1 =>
    intro y hy
    let up : Z →L[ℝ] ULift.{max u v, v} Z :=
      (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := Z)).symm.toContinuousLinearMap
    let dn : ULift.{max u v, v} Z →L[ℝ] Z :=
      (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := Z)).toContinuousLinearMap
    have hGup : IsTowerInf ((Set.Ico 0 T) ×ˢ U) (fun z => up (G z)) := by
      intro N
      obtain ⟨Ψ, hΨ, heq⟩ := hG N
      refine ⟨fun z => up (Ψ z), ?_, ?_⟩
      · exact (up.contDiff.contDiffOn (s := Set.univ)).comp hΨ (fun z _ => Set.mem_univ _)
      · intro z hz
        show up (G z) = z.1 ^ N • up (Ψ z)
        rw [heq z hz, map_smul]
    have hsmup : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => up (G z)) ((Set.Ico 0 T) ×ˢ U) := by
      obtain ⟨Ψ, hΨ, heq⟩ := hGup 0
      exact hΨ.congr (fun z hz => by simpa using heq z hz)
    have haux := jets_zero_aux hT hU (k + 1) (fun z => up (G z)) hGup y hy
    have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_left
      (s := (Set.Ico 0 T) ×ˢ U) (x := ((0 : ℝ), y)) (f := fun z => up (G z)) dn
      (hsmup.contDiffWithinAt (hx y hy)) hs (hx y hy) (i := k + 1) (by simp)
    have hzero : iteratedFDerivWithin ℝ (k + 1) (fun z => dn (up (G z)))
        ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0 := by
      rw [show (fun z => dn (up (G z))) = ⇑dn ∘ (fun z => up (G z)) from rfl]
      rw [hcomp, haux]
      ext m
      simp
    have hfun : (fun z => dn (up (G z))) = G := by
      funext z
      rfl
    rwa [hfun] at hzero

/-- **The pure time jets of `H - F` vanish on the seam** (variant of `pureTimeJets_sub` where `F`
is only assumed smooth on the slab and at the seam, instead of everywhere). -/
theorem pureTimeJets_sub_of_slab {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    (H F : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F ((Set.Ico 0 T) ×ˢ U))
    (hF2 : ∀ y ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) F ((0 : ℝ), y))
    (hmatch : ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) (0, y) (fun _ => (1, 0)) =
        iteratedDeriv k (fun t : ℝ => F (t, y)) 0) :
    ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k (fun p => H p - F p) ((Set.Ico 0 T) ×ˢ U) (0, y)
        (fun _ => ((1 : ℝ), (0 : E))) = 0 := by
  intro k y hy
  have hs : UniqueDiffOn ℝ (Set.Ico 0 T ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ((0 : ℝ), y) ∈ Set.Ico 0 T ×ˢ U := ⟨⟨le_refl 0, hT⟩, hy⟩
  have hle : ((k : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
  rw [iteratedFDerivWithin_sub hs hH hF hx k]
  rw [ContinuousMultilinearMap.sub_apply]
  rw [hmatch k y hy]
  have hFcw : iteratedFDerivWithin ℝ k F (Set.Ico 0 T ×ˢ U) (0, y)
      = iteratedFDeriv ℝ k F (0, y) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs ((hF2 y hy).of_le hle) hx
  rw [hFcw]
  rw [iteratedFDeriv_prod_line F (k := k) (y := y) ((hF2 y hy).of_le hle)]
  exact sub_self _

/-- **Flatness of `H - F` at the seam from the matching of the pure time jets** (the `IsOpen U`
form of `flat_of_matching_isOpen`, with `F` assumed smooth on the slab and at the seam). -/
theorem flatOfMatching_of_pureJets {T : ℝ} (hT : 0 < T) {U : Set E}
    (hU : IsOpen U) (H F : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F ((Set.Ico 0 T) ×ˢ U))
    (hF2 : ∀ y ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) F ((0 : ℝ), y))
    (hmatch : ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) (0, y) (fun _ => (1, 0)) =
        iteratedDeriv k (fun t : ℝ => F (t, y)) 0) :
    ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ j (fun p => H p - F p) ((Set.Ico 0 T) ×ˢ U) (0, y) = 0 := by
  have hδ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => H p - F p) ((Set.Ico 0 T) ×ˢ U) :=
    hH.sub hF
  have hpure := pureTimeJets_sub_of_slab hT hU H F hH hF hF2 hmatch
  have hslice : ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedDerivWithin j (fun t : ℝ => (H (t, y) - F (t, y))) (Set.Ico 0 T) 0 = 0 := by
    intro j y hy
    rw [← sliceJet_iteratedDerivWithin hT hU (fun p : ℝ × E => H p - F p) hδ j hy]
    exact hpure j y hy
  exact jets_zero_of_isTowerInf hT hU (isTowerInf_of_slice_zero hT hU _ hδ hslice)


/-- **Model-space two-sided extension of a function smooth on a closed half-interval.**
`H` is assumed `C^∞` on `(Ico 0 T) ×ˢ U`; the conclusion returns a two-sided neighbourhood
`(-ε,ε) ×ˢ V` of `(0,y₀)` and a `C^∞` function `K` on it which equals `H` on the right. -/
theorem local_ext_of_within
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (H : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U)) {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ ε > 0, ∃ V : Set E, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧
      ∃ K : ℝ × E → Z, ContDiffOn ℝ (⊤ : ℕ∞) K ((Set.Ioo (-ε) ε) ×ˢ V) ∧
        ∀ t ∈ Set.Ico 0 ε, ∀ y ∈ V, K (t, y) = H (t, y) := by
  classical
  -- a ball around `y₀` inside `U`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  have hHb : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ Metric.ball y₀ r) :=
    hH.mono (fun p hp => ⟨hp.1, hball hp.2⟩)
  -- Borel's theorem: realise the one-sided time jets by a smooth two-sided function
  obtain ⟨ε₁, hε₁, W₁, hW₁o, hy₀W₁, hW₁b, F, hFsm, hFjets⟩ :=
    borel_jet_on (U := Metric.ball y₀ r) Metric.isOpen_ball
      (fun k y => iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ Metric.ball y₀ r) ((0 : ℝ), y)
        (fun _ => ((1 : ℝ), (0 : E))))
      (fun k => jet_functions_smooth hT Metric.isOpen_ball H hHb k)
      (Metric.mem_ball_self hr)
  -- shrink to a ball inside `W₁`
  obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.mp hW₁o y₀ hy₀W₁
  set V : Set E := Metric.ball y₀ ρ with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball
  have hy₀V : y₀ ∈ V := Metric.mem_ball_self hρ
  have hVU : V ⊆ U := fun y hy => hball (hW₁b (hρball hy))
  -- the two time radii
  set ε' : ℝ := min T ε₁ with hε'def
  have hε'pos : 0 < ε' := lt_min hT hε₁
  have hε'leT : ε' ≤ T := min_le_left _ _
  have hε'leε₁ : ε' ≤ ε₁ := min_le_right _ _
  -- the big slab (where the time jets live) and the small slab
  set s : Set (ℝ × E) := (Set.Ico 0 T) ×ˢ Metric.ball y₀ r with hsdef
  set s' : Set (ℝ × E) := (Set.Ico 0 ε') ×ˢ V with hs'def
  have hs : UniqueDiffOn ℝ s := (uniqueDiffOn_Ico 0 T).prod Metric.isOpen_ball.uniqueDiffOn
  have hs' : UniqueDiffOn ℝ s' := (uniqueDiffOn_Ico 0 ε').prod hVo.uniqueDiffOn
  have hbig : ContDiffOn ℝ (⊤ : ℕ∞) H s := hHb
  have hsub' : s' ⊆ s := by
    rw [hs'def, hsdef]
    intro p hp
    exact ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 hε'leT⟩, hW₁b (hρball hp.2)⟩
  have htransfer : ∀ (k : ℕ) (y : E), y ∈ V →
      iteratedFDerivWithin ℝ k H s' ((0 : ℝ), y) = iteratedFDerivWithin ℝ k H s ((0 : ℝ), y) := by
    intro k y hy
    have hle : ((k : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
    exact iteratedFDerivWithin_subset hsub' hs' hs (hbig.of_le hle) ⟨⟨le_refl 0, hε'pos⟩, hy⟩
  -- the matching hypothesis on the smaller slab
  have hmatch : ∀ (k : ℕ) (y : E), y ∈ V →
      iteratedFDerivWithin ℝ k H s' ((0 : ℝ), y) (fun _ => ((1 : ℝ), (0 : E)))
        = iteratedDeriv k (fun t : ℝ => F (t, y)) 0 := by
    intro k y hy
    rw [htransfer k y hy]
    exact (hFjets k y (hρball hy)).symm
  -- `F` is smooth on the smaller slab
  have hFslab : ContDiffOn ℝ (⊤ : ℕ∞) F s' :=
    hFsm.mono (fun p hp => ⟨⟨by linarith [hp.1.1, hε'leε₁],
      lt_of_lt_of_le hp.1.2 hε'leε₁⟩, hρball hp.2⟩)
  -- and smooth at the seam points
  have hFseam : ∀ y ∈ V, ContDiffAt ℝ (⊤ : ℕ∞) F ((0 : ℝ), y) := by
    intro y hy
    exact hFsm.contDiffAt ((isOpen_Ioo.prod hW₁o).mem_nhds
      ⟨⟨by linarith [hε₁], hε₁⟩, hρball hy⟩)
  -- flatness of `H - F` on the smaller slab
  have hflat : ∀ (j : ℕ) (y : E), y ∈ V →
      iteratedFDerivWithin ℝ j (fun p : ℝ × E => H p - F p) s' ((0 : ℝ), y) = 0 :=
    flatOfMatching_of_pureJets hε'pos hVo H F (hbig.mono hsub') hFslab hFseam hmatch
  -- the Heaviside cut is smooth
  have hcut : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => if 0 < p.1 then H p - F p else 0)
      ((Set.Ioo (-ε') ε') ×ˢ V) := by
    rw [contDiffOn_infty]
    intro m
    have hle : ((m : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
    exact cut_of_flat_open (E := E) hε'pos hVo (fun p : ℝ × E => H p - F p) m
      ((hbig.mono hsub').of_le hle |>.sub (hFslab.of_le hle))
      (fun y hy j _ => hflat j y hy)
  -- the extension
  refine ⟨ε', hε'pos, V, hVo, hy₀V, hVU,
    (fun p : ℝ × E => F p + (if 0 < p.1 then H p - F p else 0)), ?_, ?_⟩
  · have h1 : ContDiffOn ℝ (⊤ : ℕ∞) F ((Set.Ioo (-ε') ε') ×ˢ V) :=
      hFsm.mono (fun p hp => ⟨⟨by linarith [hp.1.1, hε'leε₁],
        lt_of_lt_of_le hp.1.2 hε'leε₁⟩, hρball hp.2⟩)
    exact h1.add hcut
  · intro t ht y hy
    obtain ⟨ht0, _htε⟩ := ht
    by_cases h : 0 < t
    · show F (t, y) + (if 0 < t then H (t, y) - F (t, y) else 0) = H (t, y)
      rw [if_pos h, ← add_sub_assoc, add_comm (F (t, y)) (H (t, y)), add_sub_cancel_right]
    · have ht' : t = 0 := le_antisymm (not_lt.mp h) ht0
      subst ht'
      show F (0, y) + (if 0 < (0 : ℝ) then H (0, y) - F (0, y) else 0) = H (0, y)
      rw [if_neg (lt_irrefl 0), add_zero]
      have h0 := hmatch 0 y hy
      rw [iteratedFDerivWithin_zero_apply] at h0
      rw [iteratedDeriv_zero] at h0
      exact h0.symm

end Work.Diff.EXT

section Main

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- Bilinearity of a continuous bilinear form, in the shape needed for the chart matrix. -/
private lemma sum_sum_mul_mul_inner' {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {n : ℕ} (f : T →L[ℝ] T →L[ℝ] ℝ) (σ : Fin n → T) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * f (σ i) (σ j)) = f (∑ i, v i • σ i) (∑ i, v i • σ i) := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The chart matrix of a smooth metric is positive definite on the chart target.**
The chart matrix is the matrix of `g` in the coordinate frame of the chart, and the coordinate
frame is a basis of the tangent space at every point of the target
(`Submission.ChartBounds.frameVector_eq_zero_iff`), so the quadratic form is the squared norm of a
non-zero tangent vector (`Work.Diff.EXT.sum_chartMatFun_eq_inner`). -/
theorem chartMatFun_zero_posDef (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) {v : Fin (Module.finrank ℝ E) → ℝ} (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j := by
  -- the Riemannian bundle instance of `g`, giving the fibre norms
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  -- the combination of frame vectors is non-zero
  have hWne : (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
      ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i)) ≠ 0 := by
    intro hzero
    have h1 : Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
        (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 := by
      rw [Submission.Geodesic.frameVector_sum Finset.univ x₀ ((extChartAt I x₀).symm y) v
        (Work.Diff.EXT.bB (E := E))]
      exact hzero
    have h2 : (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 :=
      (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) hp _).mp h1
    have h3 : ∀ i, v i = 0 :=
      (Fintype.linearIndependent_iffₛ.mp
        (Work.Diff.EXT.bB (E := E)).linearIndependent) v 0 (by simpa using h2)
    exact hv (funext h3)
  have hkey : (∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j)
      = g.inner ((extChartAt I x₀).symm y)
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i)) := by
    simpa only [Work.Diff.EXT.chartMatFun] using
      (sum_sum_mul_mul_inner' (f := g.inner ((extChartAt I x₀).symm y))
        (σ := fun i => Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) i)) v)
  rw [hkey]
  exact g.pos ((extChartAt I x₀).symm y) _ hWne

/-- **The local piece of the two-sided extension.**  For every chart centre `x₀` there are `δ > 0`,
an open `U ∋ (extChartAt I x₀) x₀` and a smooth matrix family `V` on `(Ioo (-δ) δ) ×ˢ U` which
agrees with the chart matrix of `G` on the right, is symmetric everywhere and positive definite on
the whole two-sided slab.  This is `Work.Diff.EXT.local_ext_of_within` applied to the chart matrix
(`Work.Diff.EXT.chartMat_halfspace`), symmetrised, and shrunk using the positive definiteness of the
metric at time `0` (`chartMatFun_zero_posDef`) and `Work.Diff.EXT.posDef_tube_of_continuous_seam`. -/
theorem local_chart_piece {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T)) (x₀ : M) :
    ∃ δ > 0, ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
      ∃ V : ℝ × E → Work.Diff.EXT.MatE (E := E),
        ContDiffOn ℝ (⊤ : ℕ∞) V ((Set.Ioo (-δ) δ) ×ˢ U) ∧
        (∀ t ∈ Set.Ico 0 δ, ∀ y ∈ U, V (t, y) = Work.Diff.EXT.chartMat G x₀ t y) ∧
        (∀ t ∈ Set.Ioo (-δ) δ, ∀ y ∈ U,
          (∀ i j, V (t, y) i j = V (t, y) j i) ∧
          ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
            0 < ∑ i, ∑ j, v i * v j * V (t, y) i j) := by
  classical
  have hchart := Work.Diff.EXT.chartMat_halfspace (I := I) (M := M) hG x₀
  have hy₀ : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    PartialEquiv.map_source _ (by rw [extChartAt_source]; exact mem_chart_source H x₀)
  obtain ⟨ε₁, hε₁, V₁, hV₁o, hy₀V₁, hV₁sub, K, hKsm, hKeq⟩ :=
    Work.Diff.EXT.local_ext_of_within (Z := Work.Diff.EXT.MatE (E := E)) hT
      (isOpen_extChartAt_target (I := I) x₀)
      (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) hchart hy₀
  -- symmetrise the extension
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ × E → Work.Diff.EXT.MatE (E := E),
      W = fun p i j => (K p i j + K p j i) / 2 := ⟨_, rfl⟩
  have hWsm : ContDiffOn ℝ (⊤ : ℕ∞) W ((Set.Ioo (-ε₁) ε₁) ×ˢ V₁) := by
    rw [hWdef]
    refine contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j => ?_))
    exact (((contDiffOn_pi.mp ((contDiffOn_pi.mp hKsm) i)) j).add
      ((contDiffOn_pi.mp ((contDiffOn_pi.mp hKsm) j)) i)).div_const 2
  have hWeq : ∀ t ∈ Set.Ico 0 ε₁, ∀ y ∈ V₁, W (t, y) = Work.Diff.EXT.chartMat G x₀ t y := by
    intro t ht y hy
    have h1 : K (t, y) = Work.Diff.EXT.chartMat G x₀ t y := hKeq t ht y hy
    funext i j
    rw [hWdef]
    show (K (t, y) i j + K (t, y) j i) / 2 = Work.Diff.EXT.chartMat G x₀ t y i j
    rw [h1,
      show Work.Diff.EXT.chartMat G x₀ t y j i = Work.Diff.EXT.chartMat G x₀ t y i j from
        (G t).symm _ _ _]
    ring
  have hWc : ContinuousOn W ((Set.Ioo (-ε₁) ε₁) ×ˢ V₁) := hWsm.continuousOn
  have hW0 : ∀ y ∈ V₁, ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
      0 < ∑ i, ∑ j, v i * v j * W (0, y) i j := by
    intro y hy v hv
    rw [hWeq 0 ⟨le_refl 0, hε₁⟩ y hy]
    exact chartMatFun_zero_posDef (G 0) x₀ (hV₁sub hy) hv
  obtain ⟨a', ha'pos, U', hU'o, hy₀U', hU'sub, htube⟩ :=
    Work.Diff.EXT.posDef_tube_of_continuous_seam (E := E) hε₁ hV₁o hy₀V₁ hWc hW0
  refine ⟨min a' ε₁, lt_min ha'pos hε₁, U', hU'o, hy₀U', W, ?_, ?_, ?_⟩
  · exact hWsm.mono (fun p hp => ⟨⟨lt_of_le_of_lt (neg_le_neg (min_le_right a' ε₁)) hp.1.1,
      lt_of_lt_of_le hp.1.2 (min_le_right _ _)⟩, hU'sub hp.2⟩)
  · intro t ht y hy
    exact hWeq t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ y (hU'sub hy)
  · intro t ht y hy
    refine ⟨?_, ?_⟩
    · intro i j
      rw [hWdef]
      show (K (t, y) i j + K (t, y) j i) / 2 = (K (t, y) j i + K (t, y) i j) / 2
      ring
    · intro v hv
      exact htube t ⟨lt_of_le_of_lt (neg_le_neg (min_le_left a' ε₁)) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ y hy v hv

/-- **Two-sided extension of a jointly smooth one-sided family of metrics** (the `K`-input of the
continuation theorem): a family jointly smooth on `[0,T)` restricts, for small `ε > 0`, to a
family jointly smooth on the whole interval `(-ε,ε)` and agreeing with it on `[0,ε)`.  The local
pieces are supplied by `local_chart_piece` and glued by `Work.Diff.EXT.twoSided_glue_self`. -/
theorem twoSided_of_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (h : Submission.Diff.JointSmooth G (Set.Ico 0 T)) :
    ∃ ε > 0, ∃ K : ℝ → Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth K (Set.Ioo (-ε) ε) ∧ ∀ t ∈ Set.Ico 0 ε, K t = G t :=
  Work.Diff.EXT.twoSided_glue_self (I := I) (M := M) G T hT h
    (fun x₀ => local_chart_piece (I := I) (M := M) hT h x₀)

end Work.Diff.EXT

end Main
