import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- Elementary product bound used for the mixed angular-radial terms: if `|dA| * ww ≤ Kc`
with `ww ≥ 0`, and `|X| ≤ Bk`, then `|D * (dA * ww) * X| ≤ |D| * (Bk * Kc)`. -/
private lemma abs_four_le {D dA ww X Kc Bk : ℝ} (hw : 0 ≤ ww) (hKc : 0 ≤ Kc)
    (h1 : |dA| * ww ≤ Kc) (h2 : |X| ≤ Bk) :
    |D * (dA * ww) * X| ≤ |D| * (Bk * Kc) := by
  calc |D * (dA * ww) * X| = |D * (dA * ww)| * |X| := abs_mul _ _
    _ = (|D| * |dA * ww|) * |X| := by rw [abs_mul D (dA * ww)]
    _ = (|D| * (|dA| * ww)) * |X| := by rw [abs_mul dA ww, abs_of_nonneg hw]
    _ ≤ (|D| * Kc) * Bk := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg D)) h2 (abs_nonneg X) ?_
        exact mul_nonneg (abs_nonneg D) hKc
    _ = |D| * (Bk * Kc) := by ring

theorem WlInfAngRadial {l : ℕ} {A : ℝ → ℝ} {Hc : ℝ → ℝ} {B : ℕ → ℝ} {D α KA Kc : ℝ}
    (hα : 0 < α)
    (hA : ∀ θ ∈ Work.Spaces.Iθ, |A θ| ≤ KA)
    (hK : ∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[j]) A θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ Kc)
    (hB : ∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 ≤ z → |(z + 1) ^ k * deriv^[k] Hc z| ≤ B k) :
    Work.Spaces.WlInfMem α l (fun z θ => D * (A θ * Hc z)) ∧
      Work.Spaces.WlInf α l (fun z θ => D * (A θ * Hc z)) ≤
        |D| * ((∑ k ∈ Finset.range (l + 1), KA * B k)
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then B k * Kc else 0)) := by
  classical
  have hf : (fun z θ => D * (A θ * Hc z)) = fun z θ => (D * A θ) * Hc z := by
    funext z θ; ring
  have hDthF : ∀ j : ℕ, Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)
      = fun z θ => Work.Spaces.dthU^[j] (fun t => D * A t) θ * Hc z := by
    intro j
    funext z θ
    exact Work.Spaces.DthIter_decomp j (fun t => D * A t) Hc z θ
  have hdthD : ∀ j : ℕ, Work.Spaces.dthU^[j] (fun t => D * A t)
      = fun t => D * Work.Spaces.dthU^[j] A t := by
    intro j
    exact Work.Spaces.dthU_iter_const_mul j D A
  have hBnn : ∀ k, k ≤ l → 0 ≤ B k := by
    intro k hk
    exact le_trans (abs_nonneg _) (hB k hk 0 (le_refl 0))
  have hKa : 0 ≤ KA := by
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := by
      refine ⟨le_refl 0, ?_⟩
      linarith [Real.pi_pos]
    exact le_trans (abs_nonneg _) (hA 0 h0)
  -- The two pointwise estimates.
  have hpt1 : ∀ k, k ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ|
        ≤ |D| * (KA * B k) := by
    intro k hk z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun θ => D * A θ) Hc z θ]
    rw [show (z + 1) ^ k * ((D * A θ) * deriv^[k] Hc z)
          = (D * A θ) * ((z + 1) ^ k * deriv^[k] Hc z) by ring]
    have hAB : |D * A θ| ≤ |D| * KA := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA θ hθ) (abs_nonneg D)
    have hDz := hB k hk z hz
    calc |(D * A θ) * ((z + 1) ^ k * deriv^[k] Hc z)|
        = |D * A θ| * |(z + 1) ^ k * deriv^[k] Hc z| := abs_mul _ _
      _ ≤ (|D| * KA) * B k :=
          mul_le_mul hAB hDz (abs_nonneg _) (mul_nonneg (abs_nonneg D) hKa)
      _ = |D| * (KA * B k) := by ring
  have hpt2 : ∀ j, 1 ≤ j → ∀ k, k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ |D| * (B k * Kc) := by
    intro j hj1 k hkj z hz θ hθ
    have hkl : k ≤ l := by omega
    have hjl : j ≤ l := by omega
    rw [hDthF j]
    rw [Work.Spaces.pzIter_decomp k
      (fun θ => Work.Spaces.dthU^[j] (fun t => D * A t) θ) Hc]
    rw [hdthD j]
    dsimp only
    rw [mul_div_assoc]
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc (by
        constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin _) (le_of_lt hden)
    have hKc : 0 ≤ Kc := by
      have h1l : 1 ≤ l := le_trans hj1 hjl
      have h0mem : (0 : ℝ) ∈ Work.Spaces.Iθ := by
        refine ⟨le_refl 0, ?_⟩
        linarith [Real.pi_pos]
      have h := hK 1 le_rfl h1l 0 h0mem
      have hzero : |(Work.Spaces.dthU^[1]) A 0|
          * ((Real.sin (2 * (0 : ℝ))) ^ (-(α / 5))
              / (α + Real.sin (2 * (0 : ℝ)))) = 0 := by
        have hne : -(α / 5) ≠ 0 := by
          intro hc
          have : α = 0 := by linarith
          linarith
        have hs : Real.sin (2 * (0 : ℝ)) = 0 := by simp
        rw [hs, Real.zero_rpow hne, zero_div, mul_zero]
      rw [hzero] at h
      exact h
    have hEq : (z + 1) ^ k * ((D * Work.Spaces.dthU^[j] A θ) * deriv^[k] Hc z)
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = D * (Work.Spaces.dthU^[j] A θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          * ((z + 1) ^ k * deriv^[k] Hc z) := by ring
    rw [hEq]
    exact abs_four_le hw hKc (hK j hj1 hjl θ hθ) (hB k hkl z hz)
  constructor
  · rw [Work.Spaces.WlInfMem, hf]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound
        (fun z hz θ hθ => hpt1 k hk z hz θ hθ)
    · intro j hj k hk hj1 hjk
      exact Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound
        (fun z hz θ hθ => hpt2 j hj1 k hjk z hz θ hθ)
  · rw [Work.Spaces.WlInf, hf]
    have hterm1 : ∀ k ∈ Finset.range (l + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ)
          ≤ |D| * (KA * B k) := by
      intro k hk
      exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
        hpt1 k (by simpa using Finset.mem_range.mp hk) z hz θ hθ)
    have hterm2 : ∀ j ∈ Finset.range (l + 1), ∀ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k
                (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
            * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0) := by
      intro j hj k hk
      split_ifs with hcond
      · exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
          hpt2 j hcond.1 k hcond.2 z hz θ hθ)
      · exact le_refl 0
    have hsum1 : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ))
        ≤ ∑ k ∈ Finset.range (l + 1), |D| * (KA * B k) := Finset.sum_le_sum hterm1
    have hsum2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
              * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0))
        ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hterm2 j hj k hk))
    have hsum2eq : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0))
        = |D| * (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then B k * Kc else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      by_cases h : 1 ≤ j ∧ k + j ≤ l <;> simp [h]
    have hsum1eq : (∑ k ∈ Finset.range (l + 1), |D| * (KA * B k))
        = |D| * (∑ k ∈ Finset.range (l + 1), KA * B k) :=
      (Finset.mul_sum (s := Finset.range (l + 1)) (f := fun k => KA * B k)
        (a := |D|)).symm
    calc (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (fun z θ => (D * A θ) * Hc z) z θ))
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then
                Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                  * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter j (fun z θ => (D * A θ) * Hc z)) z θ
                  * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
                else 0)
        ≤ (∑ k ∈ Finset.range (l + 1), |D| * (KA * B k))
          + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then |D| * (B k * Kc) else 0)) :=
          add_le_add hsum1 hsum2
      _ = |D| * ((∑ k ∈ Finset.range (l + 1), KA * B k)
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then B k * Kc else 0)) := by
          rw [hsum1eq, hsum2eq, mul_add]

end Work.FTS.StrongPersist.H6Pair6Aux
