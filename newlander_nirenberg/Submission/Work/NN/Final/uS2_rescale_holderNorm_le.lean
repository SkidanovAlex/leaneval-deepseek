import Mathlib
import Submission.Work.NN.Final.uS2_holderNorm_uniform
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Final.uS2_contDiff
import Submission.Work.NN.Final.twoRec
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Final
open Work.CR.Flat Work.CR.Flat.Cauchy Work.CR.Flat.Polydisc

variable {n : ℕ}

/-- The `C^{k,α}` norm of any function on the empty set is zero. -/
lemma holderNorm_empty_set (k : ℕ) (α : ℝ) (f : (Fin n → ℂ) → ℂ) :
    holderNorm k α f (∅ : Set (Fin n → ℂ)) = 0 := by
  simp [holderNorm, iterDerivNorm, holderSeminorm]

/-- For positive radii `a`, the diagonal map `z ↦ (i ↦ a i * z i)` pulls the polydisc of
multi-radii `r` back to the polydisc of multi-radii `i ↦ r i / a i`. -/
lemma diagLin_preimage_polydisc {a r : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    diagLin a ⁻¹' polydisc 0 r = polydisc 0 (fun i => r i / a i) := by
  ext w
  rw [Set.mem_preimage, mem_polydisc, mem_polydisc]
  constructor
  · intro h i
    have h1 : ‖(a i : ℂ) * w i‖ < r i := by
      simpa only [Pi.zero_apply, sub_zero, diagLin_apply] using h i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha i)] at h1
    rw [lt_div_iff₀ (ha i)]
    simpa [mul_comm] using h1
  · intro h i
    have h1 : ‖w i‖ < r i / a i := by
      simpa only [Pi.zero_apply, sub_zero] using h i
    rw [lt_div_iff₀ (ha i)] at h1
    have h2 : a i * ‖w i‖ < r i := by simpa [mul_comm] using h1
    simpa only [Pi.zero_apply, sub_zero, diagLin_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (ha i)] using h2

theorem uS2_rescale_holderNorm_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    {σ : Fin n → ℝ} (hσ : ∀ i, σ i ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiff ℝ k (ζ i l)) → ∀ j : Fin n,
        Work.CR.Flat.holderNorm k α
            (fun z => (((σ j)⁻¹ : ℝ) : ℂ) *
              Work.NN.Final.uS2
                (fun a b w => (σ a : ℂ) * (σ b : ℂ) * ζ a b (fun i => (σ i : ℂ) * w i))
                j (fun i => (((σ i)⁻¹ : ℝ) : ℂ) * z i))
            (Work.CR.Flat.polydisc 0 (fun i => (3 / 4 : ℝ) * σ i))
          ≤ ENNReal.ofReal C *
              ∑ i : Fin n, ∑ l : Fin n,
                Work.CR.Flat.holderNorm k α (ζ i l) (Work.CR.Flat.polydisc 0 σ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun ζ hζ j => Fin.elim0 j⟩
  by_cases hpos : ∀ i, 0 < σ i
  · -- ===== all radii positive =====
    obtain ⟨CU, hCUpos, hCU⟩ := uS2_holderNorm_uniform (n := n) hα0 hα1
    obtain ⟨cΦ, hcΦpos, hcΦ⟩ :=
      holderNorm_comp_linear (n := n) k hα0 (diagLin σ) (isOpen_polydisc 0 σ)
    obtain ⟨cΨ, hcΨpos, hcΨ⟩ :=
      holderNorm_comp_linear (n := n) k hα0 (diagLin (fun i => (σ i)⁻¹))
        (isOpen_solveSet (n := n))
    set invMax : ℝ := (∑ j : Fin n, ‖(((σ j)⁻¹ : ℝ) : ℂ)‖) + 1 with hinvMax
    set siMax : ℝ := (∑ i : Fin n, ∑ l : Fin n, ‖(σ i : ℂ) * (σ l : ℂ)‖) + 1 with hsiMax
    set C : ℝ := invMax * cΨ * (CU k) * siMax * cΦ with hCdef
    have hCpos : 0 < C := by
      rw [hCdef, hinvMax, hsiMax]
      have h3 : (0 : ℝ) < CU k := hCUpos k
      positivity
    have hinvMaxpos : 0 < invMax := by rw [hinvMax]; positivity
    have hsiMaxpos : 0 < siMax := by rw [hsiMax]; positivity
    refine ⟨C, hCpos, fun ζ hζ j => ?_⟩
    have hinvle : ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ ≤ invMax := by
      rw [hinvMax]
      refine le_trans (Finset.single_le_sum
        (f := fun i : Fin n => ‖(((σ i)⁻¹ : ℝ) : ℂ)‖)
        (fun i _ => norm_nonneg _) (Finset.mem_univ j)) ?_
      exact le_add_of_nonneg_right (by norm_num)
    have hsile : ∀ i l : Fin n, ‖(σ i : ℂ) * (σ l : ℂ)‖ ≤ siMax := by
      intro i l
      rw [hsiMax]
      refine le_trans (Finset.single_le_sum
        (f := fun l' : Fin n => ‖(σ i : ℂ) * (σ l' : ℂ)‖)
        (fun l' _ => norm_nonneg _) (Finset.mem_univ l)) ?_
      refine le_trans (Finset.single_le_sum
        (f := fun i' : Fin n => ∑ l' : Fin n, ‖(σ i' : ℂ) * (σ l' : ℂ)‖)
        (fun i' _ => Finset.sum_nonneg (fun l' _ => norm_nonneg _))
        (Finset.mem_univ i)) ?_
      exact le_add_of_nonneg_right (by norm_num)
    set S : ℝ≥0∞ := ∑ i : Fin n, ∑ l : Fin n, holderNorm k α (ζ i l) (polydisc 0 σ) with hSdef
    set eta : Fin n → Fin n → (Fin n → ℂ) → ℂ :=
      fun a b w => (σ a : ℂ) * (σ b : ℂ) * ζ a b (fun i => (σ i : ℂ) * w i) with hetadef
    have hη : ∀ a b, ContDiff ℝ (k : ℕ∞) (eta a b) := by
      intro a b
      have hc : ContDiff ℝ (k : ℕ∞) (fun _ : Fin n → ℂ => (σ a : ℂ) * (σ b : ℂ)) :=
        contDiff_const
      exact hc.mul ((hζ a b).comp (diagLin σ).contDiff)
    have hu : ContDiff ℝ (k : ℕ∞) (uS2 eta j) := uS2_contDiff k hη j
    have hset1 : (diagLin (fun i => (σ i)⁻¹)) ⁻¹' solveSet
        = polydisc 0 (fun i => (3 / 4 : ℝ) * σ i) := by
      rw [solveSet_eq_polydisc, show eqRad = (3 / 4 : ℝ) from by norm_num [eqRad],
        diagLin_preimage_polydisc (a := fun i => (σ i)⁻¹) (r := fun _ => (3 / 4 : ℝ))
          (fun i => inv_pos.mpr (hpos i))]
      congr 1
      funext i
      show (3 / 4 : ℝ) / (σ i)⁻¹ = (3 / 4 : ℝ) * σ i
      rw [div_inv_eq_mul]
    have hset2 : (diagLin σ) ⁻¹' polydisc 0 σ = polydisc 0 (fun _ : Fin n => (1 : ℝ)) := by
      rw [diagLin_preimage_polydisc (a := σ) (r := σ) hpos]
      congr 1
      funext i
      exact div_self (hσ i)
    have hGcont : ContDiffOn ℝ (k : ℕ∞)
        (fun z : Fin n → ℂ => uS2 eta j (diagLin (fun i => (σ i)⁻¹) z))
        (polydisc 0 (fun i => (3 / 4 : ℝ) * σ i)) :=
      (hu.comp (diagLin (fun i => (σ i)⁻¹)).contDiff).contDiffOn
    have hΩ : UniqueDiffOn ℝ (polydisc 0 (fun i => (3 / 4 : ℝ) * σ i)) :=
      (isOpen_polydisc 0 (fun i => (3 / 4 : ℝ) * σ i)).uniqueDiffOn
    have hLHS : (fun z : Fin n → ℂ => (((σ j)⁻¹ : ℝ) : ℂ)
          * uS2 eta j (fun i => (((σ i)⁻¹ : ℝ) : ℂ) * z i))
        = ((((σ j)⁻¹ : ℝ) : ℂ)) •
            (fun z => uS2 eta j (diagLin (fun i => (σ i)⁻¹) z)) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
    have hterm : ∀ i l : Fin n,
        holderNorm k α (eta i l) (polydisc 0 (fun _ : Fin n => (1 : ℝ)))
          ≤ ENNReal.ofReal (‖(σ i : ℂ) * (σ l : ℂ)‖ * cΦ)
              * holderNorm k α (ζ i l) (polydisc 0 σ) := by
      intro i l
      have hfun : eta i l = ((σ i : ℂ) * (σ l : ℂ)) • (fun w => ζ i l (diagLin σ w)) := by
        funext w
        simp only [hetadef, Pi.smul_apply, smul_eq_mul, diagLin_apply]
      have hcont : ContDiffOn ℝ (k : ℕ∞) (fun w : Fin n → ℂ => ζ i l (diagLin σ w))
          (polydisc 0 (fun _ : Fin n => (1 : ℝ))) :=
        ((hζ i l).comp (diagLin σ).contDiff).contDiffOn
      have huniq : UniqueDiffOn ℝ (polydisc 0 (fun _ : Fin n => (1 : ℝ))) :=
        (isOpen_polydisc 0 (fun _ => (1 : ℝ))).uniqueDiffOn
      have hcomp := hcΦ (ζ i l) (hζ i l).contDiffOn
      rw [hset2] at hcomp
      calc holderNorm k α (eta i l) (polydisc 0 (fun _ : Fin n => (1 : ℝ)))
          = ENNReal.ofReal ‖(σ i : ℂ) * (σ l : ℂ)‖ *
              holderNorm k α (fun w : Fin n → ℂ => ζ i l (diagLin σ w))
                (polydisc 0 (fun _ : Fin n => (1 : ℝ))) := by
            rw [hfun, Work.CR.Flat.Holder.holderNorm_smul _ hcont huniq]
        _ ≤ ENNReal.ofReal ‖(σ i : ℂ) * (σ l : ℂ)‖ *
              (ENNReal.ofReal cΦ * holderNorm k α (ζ i l) (polydisc 0 σ)) :=
            mul_le_mul_right hcomp _
        _ = ENNReal.ofReal (‖(σ i : ℂ) * (σ l : ℂ)‖ * cΦ)
              * holderNorm k α (ζ i l) (polydisc 0 σ) := by
            rw [← mul_assoc, ENNReal.ofReal_mul (norm_nonneg _)]
    have hsum : (∑ i : Fin n, ∑ l : Fin n,
          holderNorm k α (eta i l) (polydisc 0 (fun _ : Fin n => (1 : ℝ))))
        ≤ ENNReal.ofReal siMax * (ENNReal.ofReal cΦ * S) := by
      calc (∑ i : Fin n, ∑ l : Fin n,
            holderNorm k α (eta i l) (polydisc 0 (fun _ : Fin n => (1 : ℝ))))
          ≤ ∑ i : Fin n, ∑ l : Fin n, ENNReal.ofReal siMax *
              (ENNReal.ofReal cΦ * holderNorm k α (ζ i l) (polydisc 0 σ)) := by
            refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun l _ => ?_))
            refine le_trans (hterm i l) ?_
            rw [ENNReal.ofReal_mul (norm_nonneg _)]
            exact le_trans
              (mul_le_mul_left
                (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hsile i l)) _) _)
              (le_of_eq (mul_assoc _ _ _))
        _ = ENNReal.ofReal siMax * (ENNReal.ofReal cΦ * S) := by
            rw [hSdef]
            simp only [Finset.mul_sum]
    have stepB : holderNorm k α (fun z : Fin n → ℂ => uS2 eta j (diagLin (fun i => (σ i)⁻¹) z))
          (polydisc 0 (fun i => (3 / 4 : ℝ) * σ i))
        ≤ ENNReal.ofReal cΨ * holderNorm k α (uS2 eta j) solveSet := by
      rw [← hset1]
      exact hcΨ (uS2 eta j) hu.contDiffOn
    have stepC : holderNorm k α (uS2 eta j) solveSet
        ≤ ENNReal.ofReal (CU k) * (∑ i : Fin n, ∑ l : Fin n,
            holderNorm k α (eta i l) (polydisc 0 (fun _ : Fin n => (1 : ℝ)))) := hCU k eta hη j
    have hConstLe : ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * cΨ * (CU k) * siMax * cΦ ≤ C := by
      rw [hCdef]
      have h1 : ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * cΨ ≤ invMax * cΨ :=
        mul_le_mul_of_nonneg_right hinvle (le_of_lt hcΨpos)
      have h2 : ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * cΨ * (CU k) ≤ invMax * cΨ * (CU k) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt (hCUpos k))
      have h3 : ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * cΨ * (CU k) * siMax
          ≤ invMax * cΨ * (CU k) * siMax :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hsiMaxpos)
      exact mul_le_mul_of_nonneg_right h3 (le_of_lt hcΦpos)
    have hofC : ENNReal.ofReal (‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * cΨ * (CU k) * siMax * cΦ)
        = ENNReal.ofReal ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * ENNReal.ofReal cΨ
          * ENNReal.ofReal (CU k) * ENNReal.ofReal siMax * ENNReal.ofReal cΦ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
            (le_of_lt hcΨpos)) (le_of_lt (hCUpos k))) (le_of_lt hsiMaxpos)),
        ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt hcΨpos))
            (le_of_lt (hCUpos k))),
        ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (le_of_lt hcΨpos)),
        ENNReal.ofReal_mul (norm_nonneg _)]
    calc holderNorm k α (fun z => (((σ j)⁻¹ : ℝ) : ℂ)
            * uS2 eta j (fun i => (((σ i)⁻¹ : ℝ) : ℂ) * z i))
          (polydisc 0 (fun i => (3 / 4 : ℝ) * σ i))
        = ENNReal.ofReal ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ *
            holderNorm k α (fun z : Fin n → ℂ => uS2 eta j (diagLin (fun i => (σ i)⁻¹) z))
              (polydisc 0 (fun i => (3 / 4 : ℝ) * σ i)) := by
            rw [hLHS, Work.CR.Flat.Holder.holderNorm_smul _ hGcont hΩ]
      _ ≤ ENNReal.ofReal ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ *
            (ENNReal.ofReal cΨ * holderNorm k α (uS2 eta j) solveSet) :=
            mul_le_mul_right stepB _
      _ ≤ ENNReal.ofReal ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ *
            (ENNReal.ofReal cΨ * (ENNReal.ofReal (CU k) *
              (∑ i : Fin n, ∑ l : Fin n,
                holderNorm k α (eta i l) (polydisc 0 (fun _ : Fin n => (1 : ℝ)))))) :=
            mul_le_mul_right (mul_le_mul_right stepC _) _
      _ ≤ ENNReal.ofReal ‖(((σ j)⁻¹ : ℝ) : ℂ)‖ *
            (ENNReal.ofReal cΨ * (ENNReal.ofReal (CU k) *
              (ENNReal.ofReal siMax * (ENNReal.ofReal cΦ * S)))) :=
            mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hsum _) _) _
      _ = ENNReal.ofReal (‖(((σ j)⁻¹ : ℝ) : ℂ)‖ * cΨ * (CU k) * siMax * cΦ) * S := by
            rw [hofC]
            ring
      _ ≤ ENNReal.ofReal C * S :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hConstLe) S
  · -- ===== some radius is negative: the target polydisc is empty =====
    obtain ⟨i0, hi0⟩ := not_forall.mp hpos
    have hi0' : σ i0 < 0 := lt_of_le_of_ne (not_lt.mp hi0) (hσ i0)
    refine ⟨1, one_pos, fun ζ hζ j => ?_⟩
    have hempty : polydisc 0 (fun i => (3 / 4 : ℝ) * σ i) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨z, hz⟩
      have h0 : ‖z i0‖ < (3 / 4 : ℝ) * σ i0 := by
        have := hz i0
        simpa only [Pi.zero_apply, sub_zero] using this
      nlinarith [norm_nonneg (z i0), hi0', h0]
    rw [hempty, holderNorm_empty_set]
    exact zero_le

end Work.NN.Final
