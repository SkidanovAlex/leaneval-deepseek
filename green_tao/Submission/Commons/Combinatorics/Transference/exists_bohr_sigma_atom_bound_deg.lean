import Mathlib
import Submission.Commons.Combinatorics.Transference.exists_levelJoin_polys_deg
import Submission.Commons.Combinatorics.Transference.cube_corr_half_bound
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max_bound
import Submission.Commons.Combinatorics.Transference.cube_lfc_half

namespace Commons.Combinatorics.Transference

theorem exists_bohr_sigma_atom_bound_deg {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d)
    (F : Fin K → ZMod p → ℝ) {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ C * (ν x + 1))
    (hcorr : ∀ (A : Finset (Fin d → Bool)), 2 ≤ A.card → ∀ h : Fin d → ZMod p,
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
          ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ, 1 ≤ q →
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ Cm q)
    {εm : ℝ} (hεm0 : 0 ≤ εm) (hεm1 : εm ≤ 1)
    (hmean : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εm)
    {εp : ℝ} (hεp : 0 ≤ εp)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ εp)
    {M : ℝ} (hM : 0 ≤ M)
    (hMbound : ∀ (j : Fin K) (x : ZMod p), |davg d (fun y => F j y / (2 * C)) x| ≤ M)
    {ε η η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hη' : 0 < η')
    (α : Fin K → ℝ) (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε)
    (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (fun z => F j z / (2 * C)) y - α j) / ε - n| ≤ η) → y ∈ T j) :
    ∃ (E : ℝ) (D : ℕ) (E₀ : ℝ), 0 ≤ E ∧ 0 ≤ E₀ ∧
      E₀ ≤ E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D *
        ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0)))) ∧
      (∀ x : ZMod p,
        |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
            (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
                = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)),
            (ν y - 1)|
          ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
              + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
            + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by
  classical
  -- Step 1: the correlation condition for the halved measure `(ν+1)/2`, together with the
  -- explicit bound on the new moment constants `Cm'`.
  obtain ⟨Cm', hCm'nn, hCm'bound, τ', hτ', hmom', hcorr'⟩ :=
    cube_corr_half_bound (p := p) (d := d) hd ν hν hεm0 hεm1 hmean hτ hmom hcorr
  -- Step 2: the cube linear forms condition for the halved measure.
  have hLFC' := cube_lfc_half (p := p) (d := d) ν hεp hLFC
  -- Step 3: the degree-bounded Weierstrass data for the divided generators `F j / (2C)`.
  obtain ⟨E, D, hE, φ, hφc, hφ0, hφ1, hφapprox, hpoly⟩ :=
    exists_levelJoin_polys_deg (p := p) (d := d) (K := K) (fun j z => F j z / (2 * C)) ν
      hε hη hη1 hν hη' hM α hα0 hαε T hT hMbound
  -- Step 4: pick, for every `x`, a polynomial with coefficient mass `≤ E` and degree `≤ D`
  -- approximating the product of the profiles.
  choose P hP using hpoly
  -- Step 5: the effective moment constant at degree `D`.
  have hBnn : (0 : ℝ) ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hSnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0) := by
    apply Finset.sum_nonneg
    intro j _
    by_cases h : j = 0
    · simp [h]
    · simp only [h, if_false]; exact le_max_right _ _
  set CmB : ℝ := (6 : ℝ) ^ D
      * ∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0) with hCmB
  have hCmBnn : 0 ≤ CmB := by
    rw [hCmB]
    exact mul_nonneg (pow_nonneg (by norm_num) D) hSnn
  have hCmBbound : ∀ q : ℕ, q ≤ D → Cm' q ≤ CmB := by
    intro q hq
    have h1 := hCm'bound q
    have h2 : (6 : ℝ) ^ q ≤ (6 : ℝ) ^ D := pow_le_pow_right₀ (by norm_num) hq
    have hSq : (0 : ℝ) ≤ ∑ j ∈ Finset.range (q + 1), (if j = 0 then 1 else max (Cm j) 0) := by
      apply Finset.sum_nonneg
      intro j _
      by_cases h : j = 0
      · simp [h]
      · simp only [h, if_false]; exact le_max_right _ _
    have h3 : ∑ j ∈ Finset.range (q + 1), (if j = 0 then 1 else max (Cm j) 0)
        ≤ ∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_subset_range.mpr (by omega)
      · intro j _ _
        by_cases h : j = 0
        · simp [h]
        · simp only [h, if_false]; exact le_max_right _ _
    calc Cm' q
        ≤ (6 : ℝ) ^ q * ∑ j ∈ Finset.range (q + 1), (if j = 0 then 1 else max (Cm j) 0) := h1
      _ ≤ (6 : ℝ) ^ D * ∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0) :=
          mul_le_mul h2 h3 hSq (pow_nonneg (by norm_num) D)
      _ = CmB := by rw [hCmB]
  -- Step 6: assemble.  The energy level is `E₀ = E·(1 + (2^d·2^d)^D·CmB)`.
  refine ⟨E, D, E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB), hE, ?_, ?_, ?_⟩
  · exact mul_nonneg hE (by
      have h := mul_nonneg (pow_nonneg hBnn D) hCmBnn
      linarith)
  · exact le_of_eq (by rw [hCmB])
  · exact bohr_sigma_atom_gen_poly_max_bound (p := p) (d := d) (K := K) hd F hν hC hF
      hτ' hCm'nn hmom' hcorr' hεp hLFC' hM hMbound hε hη hη1 hη' α T hT φ hφc hφ0 hφ1
      hφapprox P (fun x => (hP x).1) hE (fun x => (hP x).2.1) (fun x => (hP x).2.2) hCmBnn hCmBbound

end Commons.Combinatorics.Transference
