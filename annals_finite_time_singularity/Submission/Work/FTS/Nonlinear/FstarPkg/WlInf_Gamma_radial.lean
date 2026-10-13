import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

-- Intended full name: `Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial`
-- (declare it inside `namespace Work.FTS.Nonlinear.FstarPkg`).  This is the `Γ ⊗ H` version
-- of `Work.Spaces.Gamma_WlInf` (which is the special case `H = hKer`, `D = 1`); the proof
-- pattern is the same: `pzIter_decomp` / `DthIter_decomp` factor the iterated derivatives,
-- `Gam_bounds` gives `|Γ| ≤ 1`, `dthU_Gam_le` gives `|D_θ^j Γ| ≤ α (tBound (j-1) 0) Γ`,
-- `Gam_mul_weight_le` gives `α Γ sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1`, and `hB` bounds the
-- radial `(z+1)^k H^{(k)}`.

/-- Boundedness of a function on the domain (`Work.Spaces.SupFinite`) from a pointwise
bound on the domain; the analogue of `Work.Spaces.HkAux.supFinite_of_pointwise`. -/
lemma supFinite_of_pointwise_bound {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |g z θ| ≤ C) :
    Work.Spaces.SupFinite g :=
  ⟨C, by rintro y ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ⟩

theorem WlInf_Gamma_radial {l : ℕ} {H : ℝ → ℝ} {B : ℕ → ℝ} {D α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : ∀ k, k ≤ l → ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] H z| ≤ B k) :
    Work.Spaces.WlInfMem α l (fun z θ => D * (Work.Spaces.Gam α θ * H z)) ∧
      Work.Spaces.WlInf α l (fun z θ => D * (Work.Spaces.Gam α θ * H z))
        ≤ |D| * ((∑ k ∈ Finset.range (l + 1), B k)
            + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
                (if 1 ≤ j ∧ k + j ≤ l then B k * Work.Spaces.tBound (j - 1) 0 else 0)) := by
  classical
  -- Reassociate the amplitude `D` onto the angular factor.
  have hf : (fun z θ => D * (Work.Spaces.Gam α θ * H z))
      = fun z θ => (D * Work.Spaces.Gam α θ) * H z := by
    funext z θ; ring
  -- Separation of variables for the angular derivatives.
  have hDthF : ∀ j : ℕ, Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)
      = fun z θ => dthU^[j] (fun t => D * Work.Spaces.Gam α t) θ * H z := by
    intro j
    funext z θ
    exact Work.Spaces.DthIter_decomp j (fun t => D * Work.Spaces.Gam α t) H z θ
  have hdthD : ∀ j : ℕ, dthU^[j] (fun t => D * Work.Spaces.Gam α t)
      = fun t => D * dthU^[j] (fun t => Work.Spaces.Gam α t) t := by
    intro j
    exact Work.Spaces.dthU_iter_const_mul j D (fun t => Work.Spaces.Gam α t)
  have hBnn : ∀ k, k ≤ l → 0 ≤ B k := by
    intro k hk
    exact le_trans (abs_nonneg _) (hB k hk 0 (le_refl 0))
  -- The two pointwise estimates.
  have hpt1 : ∀ k, k ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ|
        ≤ |D| * B k := by
    intro k hk z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun θ => D * Work.Spaces.Gam α θ) H z θ]
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    have hDz := hB k hk z hz
    rw [show (z + 1) ^ k * ((D * Work.Spaces.Gam α θ) * deriv^[k] H z)
          = (D * Work.Spaces.Gam α θ) * ((z + 1) ^ k * deriv^[k] H z) by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hGam.1]
    calc |D| * Work.Spaces.Gam α θ * |(z + 1) ^ k * deriv^[k] H z|
        ≤ |D| * 1 * B k := by
          refine mul_le_mul ?_ hDz (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hGam.2 (abs_nonneg D)
      _ = |D| * B k := by ring
  have hpt2 : ∀ j, 1 ≤ j → ∀ k, k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ |D| * B k * Work.Spaces.tBound (j - 1) 0 := by
    intro j hj1 k hkj z hz θ hθ
    have hkl : k ≤ l := by omega
    rw [hDthF j]
    rw [Work.Spaces.pzIter_decomp k (fun θ => dthU^[j] (fun t => D * Work.Spaces.Gam α t) θ) H]
    rw [hdthD j]
    have hsin : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc (by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hw : 0 ≤ Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin _) (le_of_lt hden)
    rw [show (z + 1) ^ k * (D * dthU^[j] (fun t => Work.Spaces.Gam α t) θ * deriv^[k] H z)
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
        = (D * dthU^[j] (fun t => Work.Spaces.Gam α t) θ) * ((z + 1) ^ k * deriv^[k] H z)
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    have hDz := hB k hkl z hz
    have hTBnn := Work.Spaces.tBound_nonneg (j - 1) 0
    have hDnn : 0 ≤ |D| := abs_nonneg D
    have hBknn : 0 ≤ B k := hBnn k hkl
    have hdth_le := Work.Spaces.dthU_Gam_le j hj1 α hα hα1 θ hθ
    calc |D * dthU^[j] (fun t => Work.Spaces.Gam α t) θ| * |(z + 1) ^ k * deriv^[k] H z|
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (|D| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ)) * B k
          * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
          apply mul_le_mul_of_nonneg_right _ hw
          refine mul_le_mul ?_ hDz (abs_nonneg _) ?_
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hdth_le hDnn
          · exact mul_nonneg hDnn (mul_nonneg (mul_nonneg (le_of_lt hα) hTBnn) hGam.1)
      _ = |D| * B k * Work.Spaces.tBound (j - 1) 0
          * (α * Work.Spaces.Gam α θ
            * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      _ ≤ |D| * B k * Work.Spaces.tBound (j - 1) 0 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hDnn hBknn) hTBnn)
          rw [← mul_div_assoc]
          exact Work.Spaces.Gam_mul_weight_le α θ hα hθ
      _ = |D| * B k * Work.Spaces.tBound (j - 1) 0 := by ring
  constructor
  · -- Membership in `𝒲^{l,∞}`.
    rw [Work.Spaces.WlInfMem, hf]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact supFinite_of_pointwise_bound (fun z hz θ hθ => hpt1 k hk z hz θ hθ)
    · intro j hj k hk hj1 hjk
      exact supFinite_of_pointwise_bound (fun z hz θ hθ => hpt2 j hj1 k hjk z hz θ hθ)
  · -- The norm bound.
    rw [Work.Spaces.WlInf, hf]
    have hterm1 : ∀ k ∈ Finset.range (l + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ)
          ≤ |D| * B k := by
      intro k hk
      exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
        hpt1 k (by simpa using Finset.mem_range.mp hk) z hz θ hθ)
    have hterm2 : ∀ j ∈ Finset.range (l + 1), ∀ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k
                (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
            * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0) := by
      intro j hj k hk
      split_ifs with hcond
      · exact le_trans (Work.Spaces.supAbs_le (fun z hz θ hθ =>
          hpt2 j hcond.1 k hcond.2 z hz θ hθ)) (le_of_eq (by ring))
      · exact le_refl 0
    have hsum1 : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ))
        ≤ ∑ k ∈ Finset.range (l + 1), |D| * B k := Finset.sum_le_sum hterm1
    have hsum2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
              * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0))
        ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hterm2 j hj k hk))
    have hsum2eq : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0))
        = |D| * (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then B k * Work.Spaces.tBound (j - 1) 0 else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      by_cases h : 1 ≤ j ∧ k + j ≤ l <;> simp [h]
    have hsum1eq : (∑ k ∈ Finset.range (l + 1), |D| * B k)
        = |D| * (∑ k ∈ Finset.range (l + 1), B k) :=
      (Finset.mul_sum (s := Finset.range (l + 1)) (f := B) (a := |D|)).symm
    calc (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * Work.Spaces.Gam α θ) * H z) z θ))
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then
                Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                  * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter j (fun z θ => (D * Work.Spaces.Gam α θ) * H z)) z θ
                  * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
                else 0)
        ≤ (∑ k ∈ Finset.range (l + 1), |D| * B k)
          + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Work.Spaces.tBound (j - 1) 0) else 0)) :=
          add_le_add hsum1 hsum2
      _ = |D| * ((∑ k ∈ Finset.range (l + 1), B k)
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then B k * Work.Spaces.tBound (j - 1) 0 else 0)) := by
          rw [hsum1eq, hsum2eq, mul_add]

end Work.FTS.Nonlinear.FstarPkg
