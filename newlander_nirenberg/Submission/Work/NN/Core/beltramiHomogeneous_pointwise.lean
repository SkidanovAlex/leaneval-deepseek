import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.beltrami_theta_setup

namespace Work.NN.Core

open scoped NNReal ENNReal

/-- Cauchy–Schwarz / Chebyshev bound: if `0 ≤ f i ≤ δ` on a finite set `s`, then
`(∑ i, f i * g i)^2 ≤ card s * δ^2 * ∑ i, (g i)^2`. -/
lemma sq_sum_mul_le {ι : Type*} (s : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (f g : ι → ℝ) (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfδ : ∀ i ∈ s, f i ≤ δ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (s.card : ℝ) * δ ^ 2 * ∑ i ∈ s, g i ^ 2 := by
  have h1 : (∑ i ∈ s, f i * g i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i * g i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ i ∈ s, (f i * g i) ^ 2 ≤ δ ^ 2 * ∑ i ∈ s, g i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hfi : (f i) ^ 2 ≤ δ ^ 2 := by nlinarith [hf0 i hi, hfδ i hi]
    calc (f i * g i) ^ 2 = (f i) ^ 2 * (g i) ^ 2 := by ring
      _ ≤ δ ^ 2 * (g i) ^ 2 := mul_le_mul_of_nonneg_right hfi (sq_nonneg _)
  calc (∑ i ∈ s, f i * g i) ^ 2
      ≤ (s.card : ℝ) * ∑ i ∈ s, (f i * g i) ^ 2 := h1
    _ ≤ (s.card : ℝ) * (δ ^ 2 * ∑ i ∈ s, g i ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = (s.card : ℝ) * δ ^ 2 * ∑ i ∈ s, g i ^ 2 := by ring

/-- Pointwise algebraic bound for a homogeneous Beltrami solution.

If `β` is a family of coefficients with `C^{0,α}`-norm bounded by `δ` and `W` solves
the linear Beltrami-type equation
`W_i = Γ⁻¹ (∑_j β_{ij} ∂_j (\bmPotential W)) - ∑_j \bar β_{ij} W_j` pointwise,
then the `ℓ²`-norm of `W` at each point `z` is controlled by the `ℓ²`-norms of the
gradient of the (complex) potential and of `W` itself, with the sharp constant
`2 n^2` coming from `(a+b)^2 ≤ 2a^2+2b^2` and Cauchy–Schwarz in `n` terms. -/
theorem beltramiHomogeneous_pointwise {n : ℕ} (hn : 0 < n) {α δ : ℝ} (hδ0 : 0 ≤ δ)
    {β : Fin n → Fin n → Work.NN.Core.Cn n → ℂ}
    (hβnorm : ∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ ≤ ENNReal.ofReal δ)
    {W : Fin n → Work.NN.Core.Cn n → ℂ}
    (heq : ∀ i z, W i z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          (∑ j, β i j z * Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z)
        - (∑ j, (starRingEnd ℂ (β i j z)) * W j z)) :
    ∀ z, (∑ i, ‖W i z‖ ^ 2)
      ≤ 2 * (n : ℝ) ^ 2 * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ ^ 2 * δ ^ 2
          * (∑ j, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2)
        + 2 * (n : ℝ) ^ 2 * δ ^ 2 * (∑ j, ‖W j z‖ ^ 2) := by
  intro z
  have _ : 0 < n := hn
  -- Pointwise bound on the coefficients, coming from the `C^{0,α}` bound on `β`.
  have hβ : ∀ i j, ‖β i j z‖ ≤ δ := by
    intro i j
    have h1 : ENNReal.ofReal ‖β i j z‖ ≤ ENNReal.ofReal δ := by
      have h := Work.CR.Flat.le_iterDerivNorm 0 (β i j) Set.univ (Set.mem_univ z)
      rw [norm_iteratedFDerivWithin_zero] at h
      exact h.trans ((Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (β i j) Set.univ
        le_rfl).trans (hβnorm i j))
    exact (ENNReal.ofReal_le_ofReal_iff hδ0).mp h1
  set G : ℝ := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ with hGdef
  set S : ℝ := ∑ j : Fin n, ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ^ 2
    with hSdef
  set T : ℝ := ∑ j : Fin n, ‖W j z‖ ^ 2 with hTdef
  -- Per-coordinate estimate.
  have key : ∀ i : Fin n, ‖W i z‖ ^ 2 ≤
      2 * G ^ 2 * ((n : ℝ) * δ ^ 2 * S) + 2 * ((n : ℝ) * δ ^ 2 * T) := by
    intro i
    set B : ℝ := ∑ j : Fin n,
      ‖β i j z‖ * ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ with hBdef
    set C : ℝ := ∑ j : Fin n, ‖β i j z‖ * ‖W j z‖ with hCdef
    have hP : ‖∑ j : Fin n,
        β i j z * Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖ ≤ B := by
      rw [hBdef]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq (norm_mul _ _))
    have hQ : ‖∑ j : Fin n, (starRingEnd ℂ (β i j z)) * W j z‖ ≤ C := by
      rw [hCdef]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, Complex.norm_conj]
    have hB2 : B ^ 2 ≤ (n : ℝ) * δ ^ 2 * S := by
      rw [hBdef, hSdef]
      have h := sq_sum_mul_le (Finset.univ : Finset (Fin n)) hδ0 (fun j => ‖β i j z‖)
        (fun j => ‖Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential W) z‖)
        (fun j _ => norm_nonneg _) (fun j _ => hβ i j)
      simpa [Finset.card_univ, Fintype.card_fin] using h
    have hC2 : C ^ 2 ≤ (n : ℝ) * δ ^ 2 * T := by
      rw [hCdef, hTdef]
      have h := sq_sum_mul_le (Finset.univ : Finset (Fin n)) hδ0 (fun j => ‖β i j z‖)
        (fun j => ‖W j z‖) (fun j _ => norm_nonneg _) (fun j _ => hβ i j)
      simpa [Finset.card_univ, Fintype.card_fin] using h
    have hw : ‖W i z‖ ≤ G * B + C := by
      have h := heq i z
      rw [h]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, hGdef]
      exact add_le_add (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) hQ
    calc ‖W i z‖ ^ 2 ≤ (G * B + C) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ ≤ 2 * (G * B) ^ 2 + 2 * C ^ 2 := by nlinarith [sq_nonneg (G * B - C)]
      _ = 2 * G ^ 2 * B ^ 2 + 2 * C ^ 2 := by ring
      _ ≤ 2 * G ^ 2 * ((n : ℝ) * δ ^ 2 * S) + 2 * ((n : ℝ) * δ ^ 2 * T) :=
          add_le_add (mul_le_mul_of_nonneg_left hB2 (by positivity))
                     (mul_le_mul_of_nonneg_left hC2 (by norm_num))
  have hsum : ∑ i : Fin n, ‖W i z‖ ^ 2 ≤
      ∑ i : Fin n, (2 * G ^ 2 * ((n : ℝ) * δ ^ 2 * S) + 2 * ((n : ℝ) * δ ^ 2 * T)) :=
    Finset.sum_le_sum fun i _ => key i
  have hconst : ∑ i : Fin n,
      (2 * G ^ 2 * ((n : ℝ) * δ ^ 2 * S) + 2 * ((n : ℝ) * δ ^ 2 * T))
      = 2 * (n : ℝ) ^ 2 * G ^ 2 * δ ^ 2 * S + 2 * (n : ℝ) ^ 2 * δ ^ 2 * T := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exact hsum.trans (le_of_eq hconst)

end Work.NN.Core
