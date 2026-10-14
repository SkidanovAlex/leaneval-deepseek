import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The level-six `L₁₂`-bundle

The middle stage of the proof, separated from the two level-six `Qang` inputs so that the
recursion (which only uses the `z`-derivative of the angular moments) can be checked
independently of the Fubini/Cauchy–Schwarz chain producing them. -/

/-- **The open-quadrant `L₁₂`-bundle at level six.**  For a source `g` which is `C^∞` on the
open quadrant (`Work.FTS.EllipticEst.SmoothOpen g`) and lies in the weighted space `ℋ⁶`
(`Work.Spaces.HkMem α 6 g`), with `Work.Elliptic.L12 g 0 = 0`, and given

* the `z`-differentiation of the angular moments, `∂_z (Qang g j) z = Qang g (j+1) z / z` for
  `j ≤ 4` (`QangDiff6`),
* the weighted `L²`-finiteness of the zero-th moment, `∫ (Qang g 0)² w² < ∞` (from `QangSq6`),

the three facts about `L₁₂` needed by the consumer:

* the index-raising recursion `D_z^{k+1} L₁₂(g) = -Qang g k` for `k ≤ 5`;
* `z ↦ L₁₂(g)(z)² w(z)²` is integrable on `Iz = [0,∞)`;
* the weighted Hardy estimate `∫ L₁₂(g)² w² ≤ 107 ∫ (Qang g 0)² w²`. -/
theorem l12L6_bundle {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g)
    (h0 : Work.Elliptic.L12 g 0 = 0)
    (hqder : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w)
        (Work.Elliptic.Qang g (j + 1) z / z) z)
    (hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    (∀ k : ℕ, k ≤ 5 → ∀ z : ℝ, 0 < z →
        Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
          = - Work.Elliptic.Qang g k z) ∧
      MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  -- the `ℋ⁴`-membership, used only to feed the (unused) hypothesis of `L12k0Q`
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    HkMem_of_le_of_smoothOpen α (by norm_num) hO hmem
  -- ## the `L₁₂`-density is integrable on `(0,∞)` and `L₁₂` has derivative `-L12dens`
  have hFstarDiv : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk α 6 g hO hmem
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun (hFstarDiv.const_mul 3)
      (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div g r).symm) measurableSet_Ioi
  have h12deriv := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 6 g hO hmem
    (by norm_num : 2 ≤ 6)).2
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    refine (h12deriv z hz).congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  have hcontd : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    have hFcont := (Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 6 g hO hmem
      (by norm_num : 1 ≤ 6)).continuousOn
    have h : ContinuousOn (fun z => 3 * (Work.Elliptic.Fstar g z / z)) (Set.Ioi 0) :=
      continuousOn_const.mul (hFcont.div continuousOn_id (fun z hz => ne_of_gt hz))
    exact h.congr (fun z _ => Work.Elliptic.L12dens_eq_three_Fstar_div g z)
  -- ## the value formula's consequences: decay at `∞` and continuity on `[0,1]`
  obtain ⟨-, htend, hcont⟩ := Work.Elliptic.L12_values g hint h0
  -- ## the index-raising recursion
  have hgen : ∀ k : ℕ, k ≤ 5 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
    intro k
    induction k with
    | zero =>
        intro _ z hz
        have hd : deriv (fun z => Work.Elliptic.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
          (hderiv z hz).deriv
        change z * deriv (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g 0 z
        rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
          mul_div_cancel₀ _ (ne_of_gt hz)]
    | succ n ih =>
        intro hn z hz
        have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)
            =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (by omega) z' hz'
        have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - Work.Elliptic.Qang g (n + 1) z
        rw [hdv, mul_neg, neg_inj, (hqder n (by omega) z hz).deriv,
          mul_div_cancel₀ _ (ne_of_gt hz)]
  -- ## the two weighted Hardy inequalities
  obtain ⟨hInt, hBound⟩ :=
    Work.FTS.H2.L12k0Q α g hmem4 hint hderiv hcontd hcont htend h0 hQint
  exact ⟨hgen, hInt, hBound⟩

/-! ## The assembly -/

/-- **The level-six `L12H` clause from the two level-six angular-moment inputs.**  This is the
whole argument except for the (delegated) level-six open-quadrant facts
`∂_z (Qang g j) z = Qang g (j+1) z / z` (`j ≤ 4`) and
`∫_z (Qang g i)² w² ≤ (∫_θ K²)·HkSq α 6 g` (`i ≤ 5`), which are supplied by `QangDiff6` and
`QangSq6`. -/
theorem N6_L12H_of
    (hD : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 6 g → ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        HasDerivAt (fun w => Work.Elliptic.Qang g j w)
          (Work.Elliptic.Qang g (j + 1) z / z) z)
    (hS : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 6 g → ∀ i : ℕ, i ≤ 5 →
        MeasureTheory.IntegrableOn
            (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
          (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
            ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g) :
    ∃ Xi Cpow : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ ∀ α : ℝ, 0 < α →
      ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 6 g →
      Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.StrongPersist.Xn6 α (fun z θ => Work.Construction.L12 g z)
        ≤ Xi * α ^ (-Cpow) * Work.FTS.StrongPersist.Xn6 α g := by
  -- the two universal constants `∫_θ K²` and `∫_θ sin(2θ)^{-η}`
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (113 * AK * Cθ) + 1, 0, ?_, le_refl 0, ?_⟩
  · have h := Real.sqrt_nonneg (113 * AK * Cθ)
    linarith
  intro α hαpos g hg h0
  obtain ⟨hsm, hmem⟩ := hg
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  -- the two level-six angular-moment inputs
  have hQsq := hS α g hsm hmem
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    l12L6_bundle hsm hmem h0e (hD α g hsm hmem) (hQsq 0 (by norm_num)).1
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 g z with hudef
  -- ## the a.e. transfer `D_z^i (L₁₂ g) = -Qang g (i-1)` on `Iz`, `1 ≤ i ≤ 6`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang g (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi hi6
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 5 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang g (i - 1) z := by
      have h := hgen (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every weighted slot
  have hInt : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi6
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact (hQsq (i - 1) (by omega)).1.congr (htrans i h hi6)
  have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the bounds of the individual slots
  have hBnd0' : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (AK * Work.Spaces.HkSq α 6 g) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    exact le_trans hb (mul_le_mul_of_nonneg_left (hQsq 0 (by norm_num)).2 (by norm_num))
  have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 6 g := by
    intro i hi hi6
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htrans i hi hi6)]
    exact (hQsq (i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 113 * (AK * Work.Spaces.HkSq α 6 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 7) hsum_int,
      Finset.sum_range_succ']
    have h6 : (∑ i ∈ Finset.range 6, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range 6, AK * Work.Spaces.HkSq α 6 g :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_range] at hi
        exact hBndI (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h6
    refine le_trans (add_le_add h6 hBnd0') (le_of_eq ?_)
    ring
  -- ## the energy
  have hHkSq : Work.Spaces.HkSq α 6 (fun z θ => u z)
      = (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 6 (fun z θ => u z)
      ≤ (113 * AK * Cθ) * Work.Spaces.HkSq α 6 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.StrongPersist.Xn6 α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.StrongPersist.Xn6 α (fun z θ => u z)
      ≤ Real.sqrt (113 * AK * Cθ) * Work.FTS.StrongPersist.Xn6 α g := by
    have h113 : 0 ≤ 113 * AK * Cθ := by nlinarith
    calc Work.FTS.StrongPersist.Xn6 α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((113 * AK * Cθ) * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (113 * AK * Cθ) * Work.FTS.StrongPersist.Xn6 α g := by
          rw [Real.sqrt_mul h113]
          rfl
  -- ## membership in `ℋ⁶`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 6 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 7) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun
          (f := fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 7,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## back to `Work.Construction.L12`
  have hfun : (fun z (_ : ℝ) => Work.Construction.L12 g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) z
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

theorem N6_L12H : ∃ Xi Cpow : ℝ, 0 < Xi ∧ 0 ≤ Cpow ∧ ∀ α : ℝ, 0 < α →
    ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 6 g →
    Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 g z) ∧
    Work.FTS.StrongPersist.Xn6 α (fun z θ => Work.Construction.L12 g z)
      ≤ Xi * α ^ (-Cpow) * Work.FTS.StrongPersist.Xn6 α g :=
  N6_L12H_of
    (fun α g hO hmem => (QangDiff6 (α := α) (g := g) hO hmem).1)
    (fun α g hO hmem => QangSq6 (α := α) (g := g) hO hmem)

end Work.FTS.StrongPersist
