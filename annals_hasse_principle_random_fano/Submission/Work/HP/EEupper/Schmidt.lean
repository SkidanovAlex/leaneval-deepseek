import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.gon
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.Sig2.Recursion

/-!
# Schmidt's bound for lattice points in a ball

`Work.HP.Sig2Rec.recursion_count` gives Schmidt's bound in coefficient space; transporting it to
sublattices of `ℤ^ι` along a `ℤ`-basis yields

`#(L ∩ B(T)) ≤ K · ∏_{i < rk L} (T/λ_{i+1}(L) + 1)`,

and its two corollaries used in the rank-two lattice count (`ballCountRank2Mine`,
`ballCountRankGe2Mine`).  This replaces `Work.HP.FM.schmidt_bound`, whose proof still passes
through the three stubs of that directory.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.EEupper

open Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Schmidt's bound** for lattice points of a sublattice of `ℤ^ι` in a Euclidean ball. -/
theorem schmidtBoundMine :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := by
  classical
  refine ⟨Sig2Rec.Kcb (Fintype.card ι), Sig2Rec.Kcb_pos _, ?_⟩
  intro L T hT
  haveI : Module.Finite ℤ L := inferInstance
  let b : Module.Basis (Fin (rk L)) ℤ L := Module.finBasis ℤ L
  have hv : LinearIndependent ℤ (vb (L := L) b) :=
    b.linearIndependent.map' (Submodule.subtype L)
      (LinearMap.ker_eq_bot.mpr Subtype.coe_injective)
  have hΦ : Function.Injective (phiOf (vb (L := L) b)) := phiOf_injective _ hv
  have hbound := Sig2Rec.recursion_count (rk L) (phiOf (vb (L := L) b)) hΦ T hT
  have hbc : (ballCount L T : ℝ) = (latCount (phiOf (vb (L := L) b)) T : ℝ) := by
    rw [ballCount_eq_latCount b T]
  rw [hbc]
  have hLprod : ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)
      = ∏ i ∈ Finset.range (rk L), (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [lam_eq_latMin b (i + 1)]
  rw [hLprod]
  calc (latCount (phiOf (vb (L := L) b)) T : ℝ)
      ≤ Sig2Rec.Kcb (rk L) * ∏ i ∈ Finset.range (rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := hbound
    _ ≤ Sig2Rec.Kcb (Fintype.card ι) * ∏ i ∈ Finset.range (rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := by
        refine mul_le_mul_of_nonneg_right (Sig2Rec.Kcb_mono (rk_le_card L)) ?_
        exact Finset.prod_nonneg (fun i hi => by
          have hi' : i < rk L := Finset.mem_range.mp hi
          have : 0 < latMin (phiOf (vb (L := L) b)) (i + 1) :=
            gon_latMin_pos _ hΦ (by omega) (by omega)
          exact add_nonneg (div_nonneg (by linarith) this.le) zero_le_one)

/-- Elementary power identity used to clear the window denominators. -/
lemma two_mul_div_pow_mulMine {a b T : ℝ} {r : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : 1 ≤ r) :
    (2 * (T / b)) ^ (r - 1) * (2 * (T / a)) = 2 ^ r * T ^ r / (a * b ^ (r - 1)) := by
  have h : r - 1 + 1 = r := by omega
  rw [show (2 : ℝ) ^ r = 2 ^ (r - 1) * 2 from by rw [← pow_succ, h],
      show T ^ r = T ^ (r - 1) * T from by rw [← pow_succ, h],
      mul_pow, div_pow]
  field_simp

/-- For a lattice of rank `2`, Schmidt's bound reads
`#(L ∩ B(T)) ≤ K (T²/(λ₁λ₂) + T/λ₁ + 1)`. -/
theorem ballCountRank2Mine :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), rk L = 2 → 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1) := by
  obtain ⟨Kc, hKc, hKc'⟩ := schmidtBoundMine (ι := ι)
  refine ⟨2 * Kc, by positivity, ?_⟩
  intro L T h2 hT
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hmono : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) (by omega)
  have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
  have h2' : 0 < lam L 2 := lam_pos L (by norm_num) (by omega)
  have hss := hKc' L T hT
  have hprod : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
      = (T / lam L 1 + 1) * (T / lam L 2 + 1) := by
    rw [h2, Finset.prod_range_succ, Finset.prod_range_succ]
    simp
  rw [hprod] at hss
  have hdiv : T / lam L 2 ≤ T / lam L 1 := div_le_div_of_nonneg_left hT0 h1 hmono
  have hA : 0 ≤ T ^ 2 / (lam L 1 * lam L 2) := by positivity
  have hexp : (T / lam L 1 + 1) * (T / lam L 2 + 1)
      = T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + T / lam L 2 + 1 := by
    field_simp
    ring
  have hmain : (T / lam L 1 + 1) * (T / lam L 2 + 1)
      ≤ 2 * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1) := by
    rw [hexp]; linarith
  calc (ballCount L T : ℝ) ≤ Kc * ((T / lam L 1 + 1) * (T / lam L 2 + 1)) := hss
    _ ≤ Kc * (2 * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1)) :=
        mul_le_mul_of_nonneg_left hmain hKc.le
    _ = 2 * Kc * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1) := by ring

/-- For a lattice of rank `≥ 2` and `T ≥ λ₂`, Schmidt's bound gives
`#(L ∩ B(T)) ≤ K T^{rk L}/(λ₁ λ₂^{rk L - 1})`. -/
theorem ballCountRankGe2Mine :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T → 2 ≤ rk L → lam L 2 ≤ T →
      (ballCount L T : ℝ) ≤ K * T ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
  obtain ⟨Kc, hKc, hKc'⟩ := schmidtBoundMine (ι := ι)
  refine ⟨Kc * 2 ^ (Fintype.card ι), by positivity, ?_⟩
  intro L T hT hrk hlam2
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
  have h2' : 0 < lam L 2 := lam_pos L (by norm_num) hrk
  have hmono : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) hrk
  have hss := hKc' L T hT
  have hpb : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
      ≤ 2 ^ (rk L) * T ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
    have hsplit : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
        = (∏ i ∈ Finset.range (rk L - 1), (T / lam L (i + 1 + 1) + 1))
          * (T / lam L 1 + 1) := by
      have h := Finset.prod_range_succ' (fun i => T / lam L (i + 1) + 1) (rk L - 1)
      rw [show rk L - 1 + 1 = rk L from by omega] at h
      exact h
    have hstep : (∏ i ∈ Finset.range (rk L - 1), (T / lam L (i + 1 + 1) + 1))
        ≤ (∏ _i ∈ Finset.range (rk L - 1), (T / lam L 2 + 1)) := by
      refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
      · have hi' : i + 1 + 1 ≤ rk L := by
          have := Finset.mem_range.mp hi; omega
        have hpos : 0 < lam L (i + 1 + 1) := lam_pos L (by omega) hi'
        have : 0 ≤ T / lam L (i + 1 + 1) := div_nonneg hT0 hpos.le
        linarith
      · have hi' : i + 1 + 1 ≤ rk L := by
          have := Finset.mem_range.mp hi; omega
        have hle : lam L 2 ≤ lam L (i + 1 + 1) := lam_mono L (by omega) hi'
        have : T / lam L (i + 1 + 1) ≤ T / lam L 2 :=
          div_le_div_of_nonneg_left hT0 h2' hle
        linarith
    have hconst : (∏ _i ∈ Finset.range (rk L - 1), (T / lam L 2 + 1))
        = (T / lam L 2 + 1) ^ (rk L - 1) := by
      rw [Finset.prod_const, Finset.card_range]
    have hfin : (T / lam L 2 + 1) ≤ 2 * (T / lam L 2) := by
      have hge : 1 ≤ T / lam L 2 := (one_le_div h2').mpr hlam2
      linarith
    have hf0 : (T / lam L 1 + 1) ≤ 2 * (T / lam L 1) := by
      have hge : 1 ≤ T / lam L 1 := (one_le_div h1).mpr (le_trans hmono hlam2)
      linarith
    rw [hsplit]
    have hstep3 : (∏ i ∈ Finset.range (rk L - 1), (T / lam L (i + 1 + 1) + 1))
          * (T / lam L 1 + 1)
        ≤ (T / lam L 2 + 1) ^ (rk L - 1) * (T / lam L 1 + 1) := by
      rw [← hconst]
      exact mul_le_mul_of_nonneg_right hstep (by positivity)
    refine hstep3.trans ?_
    have hstep4 : (T / lam L 2 + 1) ^ (rk L - 1) * (T / lam L 1 + 1)
        ≤ (2 * (T / lam L 2)) ^ (rk L - 1) * (2 * (T / lam L 1)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hfin (rk L - 1)) hf0
        (by positivity) (by positivity)
    refine hstep4.trans (le_of_eq ?_)
    exact two_mul_div_pow_mulMine (ne_of_gt h1) (ne_of_gt h2') (by omega)
  have hpow : (2 : ℝ) ^ (rk L) ≤ 2 ^ (Fintype.card ι) :=
    pow_le_pow_right₀ (by norm_num) (rk_le_card L)
  have hDpos : 0 < lam L 1 * lam L 2 ^ (rk L - 1) := by positivity
  have hTr : 0 ≤ T ^ rk L := pow_nonneg hT0 _
  calc (ballCount L T : ℝ) ≤ Kc * (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)) := hss
    _ ≤ Kc * (2 ^ (rk L) * T ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1))) :=
        mul_le_mul_of_nonneg_left hpb hKc.le
    _ = Kc * 2 ^ (rk L) * (T ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) := by ring
    _ ≤ Kc * 2 ^ (Fintype.card ι) * (T ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpow hKc.le
    _ = Kc * 2 ^ (Fintype.card ι) * T ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by ring

end Work.HP.EEupper
