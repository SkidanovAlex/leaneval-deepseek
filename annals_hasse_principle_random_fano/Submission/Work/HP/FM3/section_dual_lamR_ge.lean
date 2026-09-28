import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# The dual of the section `L ∩ v^⊥` is not much smaller

Let `v` be a dual vector of `L` of norm at most `(3/2)λ₁(dualLat L)` and let `w ∈ L` satisfy
`⟨v,w⟩ = 1`.  Then every nonzero element of the dual of `L ∩ v^⊥` has norm at least
`(√7/4)·λ₁(dualLat L)`.  This is the key transference step of the induction.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem section_dual_lamR_ge (L : Submodule ℤ (ι → ℝ)) (v w : ι → ℝ)
    (hv : v ∈ dualLat L) (hv0 : v ≠ 0) (hw : w ∈ L) (hwv : dotR v w = 1)
    (hbound : rNorm v ≤ (3 / 2) * lamR (dualLat L) 1) :
    ∀ u ∈ dualLat (secLat v L), u ≠ 0 →
      (Real.sqrt 7 / 4) * lamR (dualLat L) 1 ≤ rNorm u := by
  intro u hu hu0
  have hvnorm_ne : rNorm v ≠ 0 := fun h => hv0 (rNorm_eq_zero_iff.mp h)
  -- `u ⟂ v`
  have huv : dotR v u = 0 := by
    refine Submodule.span_induction (p := fun y _ => dotR v y = 0) (fun y hy => hy.2) ?_ ?_ ?_ hu.1
    · simp
    · intro a b _ _ ha hb; rw [dotR_add_right, ha, hb, add_zero]
    · intro c a _ ha; rw [dotR_smul_right, ha, mul_zero]
  -- the integer `m` and the displacement `s = m - ⟨u,w⟩`
  set m : ℤ := ⌊dotR u w + 1 / 2⌋ with hmdef
  set s : ℝ := (m : ℝ) - dotR u w with hsdef
  have hs_bound : |s| ≤ 1 / 2 := by
    have h1 : (m : ℝ) ≤ dotR u w + 1 / 2 := by rw [hmdef]; exact Int.floor_le _
    have h2 : dotR u w + 1 / 2 < (m : ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one _
    rw [hsdef, abs_le]
    constructor <;> linarith
  -- the corrected vector lies in `dualLat L`
  have hstar : u + s • v ∈ dualLat L := by
    refine ⟨Submodule.add_mem _ (Submodule.span_mono (fun y hy => hy.1) hu.1)
      (Submodule.smul_mem _ _ hv.1), fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := hv.2 z hz
    have hz0 : z - k • w ∈ secLat v L := by
      refine ⟨Submodule.sub_mem _ hz (Submodule.smul_mem _ _ hw), ?_⟩
      show dotR v (z - k • w) = 0
      rw [← Int.cast_smul_eq_zsmul ℝ k w, dotR_sub_right, dotR_smul_right, hwv, mul_one]
      rw [show dotR v z = (k : ℝ) from hk, sub_self]
    obtain ⟨j, hj⟩ := hu.2 (z - k • w) hz0
    have hj' : dotR u (z - k • w) = (j : ℝ) := hj
    have hval : dotR (u + s • v) z = (j : ℝ) + (k : ℝ) * (m : ℝ) := by
      have h1 : dotR u z = (j : ℝ) + (k : ℝ) * dotR u w := by
        have hsplit : dotR u z = dotR u (z - k • w) + dotR u (k • w) := by
          rw [← dotR_add_right, sub_add_cancel]
        rw [hsplit, hj']
        congr 1
        rw [← Int.cast_smul_eq_zsmul ℝ k w, dotR_smul_right]
      have h2 : dotR v z = (k : ℝ) := by
        have hsplit : dotR v z = dotR v (z - k • w) + dotR v (k • w) := by
          rw [← dotR_add_right, sub_add_cancel]
        rw [hsplit, hz0.2, zero_add, ← Int.cast_smul_eq_zsmul ℝ k w, dotR_smul_right, hwv,
          mul_one]
      rw [dotR_add_left, dotR_smul_left, h1, h2, hsdef]
      ring
    exact ⟨j + k * m, by
      change dotR (u + s • v) z = ((j + k * m : ℤ) : ℝ)
      rw [hval]; push_cast; ring⟩
  have hstar_ne : u + s • v ≠ 0 := by
    intro h
    have h1 : dotR v (u + s • v) = 0 := by rw [h, dotR_zero_right]
    rw [dotR_add_right, dotR_smul_right, huv, zero_add, ← rNorm_sq] at h1
    have hsv : (rNorm v) ^ 2 ≠ 0 := pow_ne_zero 2 hvnorm_ne
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hsv
    rw [hs0, zero_smul, add_zero] at h
    exact hu0 h
  have hle : lamR (dualLat L) 1 ≤ rNorm (u + s • v) := lamR_le_rNorm _ hstar hstar_ne
  have hlam_nn : 0 ≤ lamR (dualLat L) 1 := lamR_nonneg _ _
  -- Pythagoras
  have hsq : rNorm (u + s • v) ^ 2 = rNorm u ^ 2 + s ^ 2 * rNorm v ^ 2 := by
    have hoth : dotR u (s • v) = 0 := by
      rw [dotR_smul_right, dotR_comm u v, huv, mul_zero]
    rw [rNorm_add_sq_of_orthogonal hoth, rNorm_smul, mul_pow, sq_abs]
  -- the numerical estimate
  have hsq2 : (7 / 16) * (lamR (dualLat L) 1) ^ 2 ≤ rNorm u ^ 2 := by
    have hle2 : (lamR (dualLat L) 1) ^ 2 ≤ rNorm (u + s • v) ^ 2 :=
      pow_le_pow_left₀ hlam_nn hle 2
    have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [hs_bound, abs_nonneg s, sq_abs s]
    have hv2 : (rNorm v) ^ 2 ≤ (9 / 4) * (lamR (dualLat L) 1) ^ 2 := by
      have h := pow_le_pow_left₀ (rNorm_nonneg v) hbound 2
      nlinarith [h]
    rw [hsq] at hle2
    nlinarith [hle2, hs2, hv2, sq_nonneg s, sq_nonneg (rNorm v)]
  have hA : ((Real.sqrt 7 / 4) * lamR (dualLat L) 1) ^ 2 ≤ (rNorm u) ^ 2 := by
    have h7 : (Real.sqrt 7 / 4) ^ 2 = (7 : ℝ) / 16 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]; norm_num
    rw [mul_pow, h7]
    linarith [hsq2]
  have := Real.sqrt_le_sqrt hA
  rwa [Real.sqrt_sq (mul_nonneg (by positivity) hlam_nn), Real.sqrt_sq (rNorm_nonneg u)] at this

end Work.HP.FM3
