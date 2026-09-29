import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_3
import Submission.Work.TMC16Core.Basic.green_bound_notA
import Submission.Work.TMC16Core.Basic.dirMat_det

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-- **AJ §9: uniformity of a family of phases forces regularity.**  If `k+1` phases coming
from the sites of a finite set `J` are `ε₁`-uniform (AJ (9.8)), then -- by AJ Lemma 9.3
(`lemma_9_3`, non-generation of uniform families) -- at least one of the corresponding
phases lies *outside* `A_{k,L-ε}`, so the corresponding site `j₀` is a "non-`A`" site.
Such a site contains `y` in its window `[j₀,j₀+k-1]` at distance `≥ k/40` from both ends
(`hgeo`), and the exponentially large continuant at `j₀` gives, via Cramer's rule
(`green_bound_notA`), decay of the boundary Green's-function entries at rate
`L-40ε-39ε₁`. -/
theorem regular_of_uniform {α lam : ℝ} {E : ℂ} {θ L ε ε₁ : ℝ} {k : ℕ} {y : ℤ}
    {J : Finset ℤ} {S : Set ℤ} {Q : Polynomial ℂ}
    (hcard : J.card = k + 1)
    (hk : 4 * ((k : ℝ) + 1) * Real.exp (L - ε) < Real.exp ((k : ℝ) * (ε - ε₁)))
    (hε : ε₁ < ε) (hpos : 0 < L - 40 * ε - 39 * ε₁) (hk40 : 40 ≤ k)
    (hQ : ∀ x : ℝ, Q.eval ((Real.cos (2 * Real.pi * x) : ℝ) : ℂ) =
        Work.TMC16Core.pd α lam (x - (((k : ℝ) - 1) / 2) * α) E (k + 1))
    (hdeg : Q.natDegree ≤ k)
    (huni : Work.TMC16Core.Uniform ε₁
        (fun j : {j : ℤ // j ∈ J} => θ + (((j : ℤ) : ℝ) + (((k : ℝ) - 1) / 2)) * α))
    (hA : ∀ j ∈ J, j ∈ S → θ + (((j : ℝ) + (((k : ℝ) - 1) / 2)) * α) ∈
        Work.TMC16Core.AkSet α lam E k (L - ε))
    (hgeo : ∀ j ∈ J, j ∉ S → (j : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (j : ℝ) + (k : ℝ) - 1 ∧
        (k : ℝ) ≤ 40 * ((y : ℝ) - (j : ℝ)) ∧
        (k : ℝ) ≤ 40 * ((j : ℝ) + (k : ℝ) - 1 - (y : ℝ)))
    (hlarge : ∃ θ₀ : ℝ, Real.exp ((k : ℝ) * L) / 4 ≤
        ‖Work.TMC16Core.pd α lam (θ₀ - (((k : ℝ) - 1) / 2) * α) E (k + 1)‖)
    (hbd : ∀ n : ℕ, n ≤ k → ∀ ζ : ℝ,
        ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁))) :
    Work.TMC16Core.IsRegular α lam θ E (L - 40 * ε - 39 * ε₁) k y := by
  classical
  obtain ⟨θ₀, hθ₀⟩ := hlarge
  have hbd_k := hbd k le_rfl (θ₀ - (((k : ℝ) - 1) / 2) * α)
  have hkε₁ : -(Real.log 4) ≤ (k : ℝ) * ε₁ := by
    have h1 : Real.exp ((k : ℝ) * L - Real.log 4) ≤ Real.exp ((k : ℝ) * (L + ε₁)) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact le_trans hθ₀ hbd_k
    have := Real.exp_le_exp.mp h1
    linarith
  have hr_upper : L - ε < (k : ℝ) * (ε - ε₁) - Real.log (4 * ((k : ℝ) + 1)) := by
    have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 4 * ((k : ℝ) + 1) * Real.exp (L - ε)) hk
    rw [Real.log_mul (by positivity : (4 : ℝ) * ((k : ℝ) + 1) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp] at hlog
    linarith
  have hr_lower : 39 * (ε + ε₁) < L - ε := by
    have : L - ε = (L - 40 * ε - 39 * ε₁) + 39 * (ε + ε₁) := by ring
    linarith [hpos]
  have h39s : 39 * (ε + ε₁) < (k : ℝ) * (ε - ε₁) - Real.log (4 * ((k : ℝ) + 1)) :=
    lt_trans hr_lower hr_upper
  have hstep : ((k : ℝ) - 39) * (ε + ε₁) > 2 * (k : ℝ) * ε₁ + Real.log (4 * ((k : ℝ) + 1)) := by
    linarith [h39s]
  have hkR40 : (40 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk40
  have hlog4pos : Real.log 4 < Real.log ((k : ℝ) + 1) := by
    apply Real.log_lt_log (by norm_num)
    linarith
  have hlogid : Real.log (4 * ((k : ℝ) + 1)) - 2 * Real.log 4
      = Real.log ((k : ℝ) + 1) - Real.log 4 := by
    rw [Real.log_mul (by norm_num) (by positivity : ((k : ℝ) + 1) ≠ 0)]
    ring
  have hstep2 : 0 < ((k : ℝ) - 39) * (ε + ε₁) := by
    have h : Real.log ((k : ℝ) + 1) - Real.log 4
        ≤ 2 * (k : ℝ) * ε₁ + Real.log (4 * ((k : ℝ) + 1)) := by
      linarith [hkε₁, hlogid]
    linarith [hstep, h, hlog4pos]
  have hk39pos : 0 < (k : ℝ) - 39 := by linarith
  have hs_pos : 0 < ε + ε₁ := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hstep2, hk39pos, hcon]
  have hr_pos : 0 < L - ε := by
    have : L - ε = (L - 40 * ε - 39 * ε₁) + 39 * (ε + ε₁) := by ring
    linarith [hpos, hs_pos]
  have hcard' : Fintype.card {j : ℤ // j ∈ J} = k + 1 := by
    rw [Fintype.card_coe, hcard]
  have hExists : ∃ j : ℤ, j ∈ J ∧
      θ + (((j : ℤ) : ℝ) + (((k : ℝ) - 1) / 2)) * α ∉ AkSet α lam E k (L - ε) := by
    by_contra hc
    push_neg at hc
    exact (lemma_9_3 (ι := {j : ℤ // j ∈ J}) hQ hdeg hcard'
      (fun j => hc j.1 j.2) θ₀ hθ₀ hε hk) huni
  obtain ⟨j₀, hj₀J, hj₀not⟩ := hExists
  have hj₀S : j₀ ∉ S := fun hS => hj₀not (hA j₀ hj₀J hS)
  obtain ⟨hjy, hyk, hd1, hd2⟩ := hgeo j₀ hj₀J hj₀S
  have hjyZ : j₀ ≤ y := by exact_mod_cast hjy
  have hykZ : y ≤ j₀ + (k : ℤ) - 1 := by
    have h : (y : ℝ) ≤ ((j₀ + (k : ℤ) - 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hd1Z : (k : ℤ) ≤ 40 * (y - j₀) := by
    have h : ((k : ℤ) : ℝ) ≤ ((40 * (y - j₀) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hd2Z : (k : ℤ) ≤ 40 * (j₀ + (k : ℤ) - 1 - y) := by
    have h : ((k : ℤ) : ℝ) ≤ ((40 * (j₀ + (k : ℤ) - 1 - y) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hnotA : Real.exp (((k : ℝ) + 1) * (L - ε)) <
      ‖pd α lam (θ + (j₀ : ℝ) * α) E (k + 1)‖ := by
    have h := hj₀not
    simp only [AkSet, Set.mem_ofPred_eq] at h
    have h' := not_le.mp h
    have harg : θ + (((j₀ : ℤ) : ℝ) + (((k : ℝ) - 1) / 2)) * α - (((k : ℝ) - 1) / 2) * α
        = θ + (j₀ : ℝ) * α := by ring
    rwa [harg] at h'
  have hdet : (dirMat α lam (θ + (j₀ : ℝ) * α) E k).det ≠ 0 := by
    rw [dirMat_det]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) ?_
    intro h0
    rw [h0, norm_zero] at hnotA
    exact absurd hnotA (not_lt.mpr (le_of_lt (Real.exp_pos _)))
  have hgb := green_bound_notA (α := α) (lam := lam) (E := E) (θ := θ) (r := L - ε)
    (L := L) (ε₁ := ε₁) (k := k) (x₁ := j₀) (x₂ := j₀ + (k : ℤ) - 1) (y := y)
    hbd rfl hjyZ hykZ hnotA
  set a : ℤ := y - j₀ with ha
  set b : ℤ := j₀ + (k : ℤ) - 1 - y with hb
  have ha_nonneg : 0 ≤ a := by rw [ha]; omega
  have hb_nonneg : 0 ≤ b := by rw [hb]; omega
  have h40aR : (k : ℝ) ≤ 40 * (a : ℝ) := by
    have h := hd1Z; rw [ha] at h; exact_mod_cast h
  have h40bR : (k : ℝ) ≤ 40 * (b : ℝ) := by
    have h := hd2Z; rw [hb] at h; exact_mod_cast h
  have hkR : (k : ℝ) = (a : ℝ) + (b : ℝ) + 1 := by
    have h : a + b = (k : ℤ) - 1 := by rw [ha, hb]; ring
    have hc := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at hc; linarith
  refine ⟨j₀, j₀ + (k : ℤ) - 1, rfl, hjyZ, hykZ, hd1Z, hd2Z, hdet, ?_, ?_⟩
  · refine lt_of_lt_of_le hgb.1 (Real.exp_le_exp.mpr ?_)
    rw [show (((j₀ + (k : ℤ) - 1) - y : ℤ) : ℝ) = (b : ℝ) from by rw [← hb],
      show ((y - j₀ : ℤ) : ℝ) = (a : ℝ) from by rw [← ha],
      abs_of_nonneg (by exact_mod_cast ha_nonneg)]
    have hb39a : (b : ℝ) - 39 * (a : ℝ) ≤ -1 := by
      have h1 : (b : ℝ) ≤ (k : ℝ) - 1 - (a : ℝ) := by linarith [hkR]
      linarith [h40aR]
    have key : (L + ε₁) * (b : ℝ) - (((k : ℝ) + 1) * (L - ε)) + (L - 40 * ε - 39 * ε₁) * (a : ℝ)
        = (ε + ε₁) * ((b : ℝ) - 39 * (a : ℝ)) - 2 * (L - ε) := by
      rw [hkR]; ring
    have hneg : (ε + ε₁) * ((b : ℝ) - 39 * (a : ℝ)) - 2 * (L - ε) < 0 := by
      have h1 : (ε + ε₁) * ((b : ℝ) - 39 * (a : ℝ)) ≤ (ε + ε₁) * (-1) :=
        mul_le_mul_of_nonneg_left hb39a (le_of_lt hs_pos)
      linarith [hr_pos]
    linarith [key, hneg]
  · refine lt_of_lt_of_le hgb.2 (Real.exp_le_exp.mpr ?_)
    rw [show ((y - j₀ : ℤ) : ℝ) = (a : ℝ) from by rw [← ha],
      show ((y - (j₀ + (k : ℤ) - 1) : ℤ) : ℝ) = -(b : ℝ) from by
        rw [show (y - (j₀ + (k : ℤ) - 1) : ℤ) = -b from by rw [hb]; ring]
        push_cast; ring,
      abs_neg, abs_of_nonneg (by exact_mod_cast hb_nonneg)]
    have ha39b : (a : ℝ) - 39 * (b : ℝ) ≤ -1 := by
      have h1 : (a : ℝ) ≤ (k : ℝ) - 1 - (b : ℝ) := by linarith [hkR]
      linarith [h40bR]
    have key : (L + ε₁) * (a : ℝ) - (((k : ℝ) + 1) * (L - ε)) + (L - 40 * ε - 39 * ε₁) * (b : ℝ)
        = (ε + ε₁) * ((a : ℝ) - 39 * (b : ℝ)) - 2 * (L - ε) := by
      rw [hkR]; ring
    have hneg : (ε + ε₁) * ((a : ℝ) - 39 * (b : ℝ)) - 2 * (L - ε) < 0 := by
      have h1 : (ε + ε₁) * ((a : ℝ) - 39 * (b : ℝ)) ≤ (ε + ε₁) * (-1) :=
        mul_le_mul_of_nonneg_left ha39b (le_of_lt hs_pos)
      linarith [hr_pos]
    linarith [key, hneg]

end Work.TMC16Core.Basic
