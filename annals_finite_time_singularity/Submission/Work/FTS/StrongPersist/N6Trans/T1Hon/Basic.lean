import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotIntegrableGen
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.HardSlotLemGen
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotWeightHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary facts -/

/-- Almost every point of `Iz = [0,∞)` is positive. -/
theorem ae_Iz_pos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [MeasureTheory.ae_iff]
  have hset : {z : ℝ | ¬ (0 < z)} = Set.Iic (0 : ℝ) := by
    ext z; simp only [Set.mem_ofPred_eq, not_lt, Set.mem_Iic]
  rw [hset, MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (0 : ℝ) ∩ Work.Spaces.Iz = {0} := by
    ext x
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici,
      Set.mem_singleton_iff]
    constructor
    · intro h; exact le_antisymm h.1 h.2
    · intro h; simp [h]
  rw [h, MeasureTheory.measure_singleton]

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
  Work.FTS.StrongPersist.N6Trans.HardSlotAux.ae_restrict_Iθ_of_forall_mem_Ioo
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun _ hθ => hθ)

/-- `w²σ^{-q}` is nonnegative on the closed angular interval. -/
theorem weight_nonneg_of_Iθ (q : ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
    (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)

/-- **The weight `w²σ^{-q}` of an admissible leaf is dominated by the slot weight `slotW α a`**
on the open quadrant. -/
theorem weight_le_slotW {α q : ℝ} (hα : 0 < α) {a : ℕ}
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      ≤ Work.FTS.TransportS.slotW α a z θ := by
  have hσ0 : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_Qd hθ
  have hgam0 : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero]
    beta_reduce
    rw [Work.FTS.H2.Whz_sq z θ hσ0.le]
    rcases hq0 rfl with hq | hq
    · subst hq
      simpa only [neg_zero, Real.rpow_zero, mul_one] using
        mul_le_mul_of_nonneg_left
          (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
          (sq_nonneg (Work.Spaces.w z))
    · subst hq
      exact le_rfl
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos' α ha1]
    beta_reduce
    rw [Work.FTS.H2.Wm_sq α hα z θ hσ0.le]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rcases hqa ha1 with hq | hq | hq
    · subst hq
      rw [neg_zero, Real.rpow_zero]
      exact Work.FTS.TransportS.one_le_rpow_neg hgam0 hθ
    · subst hq
      exact Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le
        (le_trans (le_of_lt Work.Spaces.eta_lt_one) (le_of_lt (Work.Spaces.one_lt_gam hα))) hθ
    · subst hq
      exact le_rfl

/-- A split identity: the (double) sum over `range (a+1) × range (b+1)` is its `(0,0)` term plus
the sum with the `(0,0)` term deleted. -/
theorem sum_split_zero {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : ℕ → ℕ → M) :
    (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), F a1 b1)
      = F 0 0 + ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1) := by
  have h0a : (0 : ℕ) ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
  have h0b : (0 : ℕ) ∈ Finset.range (b + 1) := Finset.mem_range.mpr (by omega)
  have key : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0)) = F 0 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single 0]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro b1 hb1 hne; rw [if_neg (fun h => hne h.2)]
      · intro h; exact absurd h0b h
    · intro a1 ha1 hne
      refine Finset.sum_eq_zero fun b1 _ => ?_
      rw [if_neg (fun h => hne h.1)]
    · intro h; exact absurd h0a h
  have hpt : ∀ a1 b1, F a1 b1
      = (if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0)
        + (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1) := by
    intro a1 b1; by_cases h : a1 = 0 ∧ b1 = 0 <;> simp [h]
  calc (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), F a1 b1)
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          ((if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0)
            + (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1)) :=
        Finset.sum_congr rfl fun a1 _ =>
          Finset.sum_congr rfl fun b1 _ => (hpt a1 b1)
    _ = (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then F a1 b1 else 0))
          + (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1)) := by
        simp only [Finset.sum_add_distrib]
    _ = F 0 0 + ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then 0 else F a1 b1) := by rw [key]

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
