import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen
import Submission.Work.FTS.OpenPkg.wmul_field
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.T4Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The "hard" summand of the `D_θ`-transport slot pairing with a `D`-sup coefficient.**

This is `Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen` with the coefficient hypothesis
weakened from `HkMem α 4 f` to `WDMem 4 f`, and the constant `C/√(γ-1)·HkNorm α 4 f` replaced by
`C·WDp 4 f`.  Only the pointwise bounds `|f| ≤ WDp 4 f` and `|D_θf| ≤ WDp 4 f`
(`Work.FTS.OpenPkg.WDMem_of_WDp_le ... le_rfl 0 0` resp. `0 1`) are used in the proof of that
sibling, so the IBP core `Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound` and the slot
integrability `Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen` apply verbatim; take
`C := 3 / 2 + B / 2` from `IbpSliceBound`. -/
theorem T4HardSlot : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (q : ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    ∀ (a b : ℕ), a + b ≤ 4 →
      (a = 0 → q = 0 ∨ q = Work.Spaces.eta) →
      (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
    ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        ≤ C * Work.FTS.VocabO.WDp 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound
  refine ⟨3 / 2 + B / 2, by linarith, ?_⟩
  intro α f g q hα hα1 hfsm hfmem hgsm hgmem hgdec a b hab hq0 hqa z hz
  set Kf : ℝ := Work.FTS.VocabO.WDp 4 f with hKf
  have hKf0 : 0 ≤ Kf := by
    rw [hKf]
    exact Work.FTS.OpenPkg.WDp_nonneg 4 f
  -- the only two facts about `q` used below
  have hqabs : |1 - q| ≤ 1 := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rcases hq0 ha0 with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num [Work.Spaces.eta]
    · rcases hqa hapos with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num [Work.Spaces.eta]
      · rw [h]
        rw [Work.Spaces.gam]
        have h2 : (1 : ℝ) - (1 + α / 10) = -(α / 10) := by ring
        rw [h2, abs_neg, abs_of_nonneg (by linarith)]
        linarith
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate slice `z = 0`: the radial weight vanishes, so both sides are `0`
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    have h0 : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f 0 θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a g) 0 θ * Work.Spaces.mixed b a g 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ
      rw [hw0]
      ring
    rw [h0, MeasureTheory.integral_zero, abs_zero, hw0]
    simp
  · -- the genuine slice `z > 0`: strip the (constant) radial factor `w(z)²`, reduce to the
    -- angular slices `F`, `V` and apply the integration-by-parts bound
    set F : ℝ → ℝ := fun θ => f z θ with hF
    set V : ℝ → ℝ := fun θ => Work.Spaces.mixed b a g z θ with hV
    have hF1 : ContDiffOn ℝ 1 F (Set.Ioo 0 (π / 2)) := by
      rw [hF]
      exact (hfsm.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
    have hV1 : ContDiffOn ℝ 1 V (Set.Ioo 0 (π / 2)) := by
      rw [hV]
      exact ((hgsm.mixed b a).curry_θ hzpos).of_le
        (by simp [Work.Stability.smoothOrder])
    have hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf := by
      intro θ hθ
      have h := Work.FTS.OpenPkg.WDMem_of_WDp_le hfmem le_rfl 0 0 (by norm_num)
        z θ hzpos hθ.1 hθ.2
      simpa only [hF, hKf, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
        Work.Spaces.DzIter_zero] using h
    have hFd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv F θ| ≤ Kf := by
      intro θ hθ
      have h := Work.FTS.OpenPkg.WDMem_of_WDp_le hfmem le_rfl 0 1 (by norm_num)
        z θ hzpos hθ.1 hθ.2
      simpa only [hF, hKf, Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero, Work.Spaces.Dth,
        Work.Spaces.pth] using h
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
      have h := Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen α g a b q hα hgsm
        hgmem hab hq0 hqa hzpos
      simpa only [hV] using h
    have hslice := hB q Kf F V hKf0 hqabs hF1 hV1 hFb hFd hint
    have hcongr : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        = fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ) := by
      funext θ
      simp only [hF, hV, Work.Spaces.Dth, Work.Spaces.pth]
      ring
    calc |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        = (Work.Spaces.w z) ^ 2 * |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ| := by
          rw [hcongr, MeasureTheory.integral_const_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      _ ≤ (Work.Spaces.w z) ^ 2 * ((3 / 2 + B / 2) * Kf
            * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ = (3 / 2 + B / 2) * Work.FTS.VocabO.WDp 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          rw [hKf]; ring
      _ = (3 / 2 + B / 2) * Work.FTS.VocabO.WDp 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          simp only [hV]

end Work.FTS.StrongEps.E4R3.N4C.T4Honest
