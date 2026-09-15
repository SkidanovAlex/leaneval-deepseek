import Mathlib
import Submission.Commons.Combinatorics.Transference.exists_levelJoin_polys_K0_E
import Submission.Commons.Combinatorics.Transference.cube_corr_half_bound
import Submission.Commons.Combinatorics.Transference.cube_lfc_half
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max_bound

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Proposition 6.6, Weierstrass/polynomial form with prescribed coefficient
mass and degree.**  This is the assembly lemma underlying `exists_bohr_sigma_atom_bound_deg_pow`,
but the caller supplies, through the hypothesis `hpoly`, the approximating polynomials of the
product `∏ j, levelJoinPsi η ((t j - c j)/ε)` together with *prescribed* coefficient mass `E`
and total degree `D`.  The conclusion is the pointwise bound for the atoms of the join of the
level-set σ-algebras, with `CmB = 6^D · ∑_{j ≤ D} max(Cm j) 0` as the moment constant. -/
theorem bohr_sigma_atom_bound_of_weierstrass {p : ℕ} [Fact p.Prime] {d K K₀ : ℕ} (hd : 1 ≤ d)
    (hKK₀ : K ≤ K₀)
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
      (∃ n : ℤ, |(davg d (fun z => F j z / (2 * C)) y - α j) / ε - n| ≤ η) → y ∈ T j)
    {E : ℝ} (hE : 0 ≤ E) {D : ℕ}
    (hpoly : ∀ (K' : ℕ) (hK' : K' ≤ K₀) (c : Fin K' → ℝ), (∀ j, |c j| ≤ M + ε) →
      ∃ P : MvPolynomial (Fin K') ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K' => Set.Icc (-M) M),
          |∏ j, Commons.Combinatorics.Transference.levelJoinPsi η ((t j - c j) / ε)
            - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D) :
    ∀ x : ZMod p,
      |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
              = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)),
          (ν y - 1)|
        ≤ (Fintype.card (ZMod p) : ℝ)
            * (Unorm d (fun y => ν y - 1)
                * (E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D *
                    ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1),
                      (if j = 0 then 1 else max (Cm j) 0)))))
              + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
          + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by
  classical
  -- Step 1: correlation condition for the halved measure `(ν+1)/2`, with moment constants `Cm'`.
  obtain ⟨Cm', hCm'nn, hCm'bound, τ', hτ', hmom', hcorr'⟩ :=
    cube_corr_half_bound (p := p) (d := d) hd ν hν hεm0 hεm1 hmean hτ hmom hcorr
  -- Step 2: cube linear forms condition for the halved measure.
  have hLFC' := cube_lfc_half (p := p) (d := d) ν hεp hLFC
  -- Step 3: Weierstrass data for the divided generators, with prescribed mass `E` and degree `D`.
  obtain ⟨φ, hφc, hφ0, hφ1, hφapprox, hpolyK⟩ :=
    exists_levelJoin_polys_K0_E (p := p) (d := d) (K₀ := K₀) (K := K) hKK₀
      (fun j z => F j z / (2 * C)) ν hε hη hη1 hν hη' hM α hα0 hαε T hT hMbound hE hpoly
  -- Step 4: for every `x`, pick the approximating polynomial with mass `≤ E` and degree `≤ D`.
  choose P hP using hpolyK
  -- Step 5: the effective moment constant in degrees `≤ D`.
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
      _ ≤ (6 : ℝ) ^ D
            * ∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (Cm j) 0) :=
          mul_le_mul h2 h3 hSq (pow_nonneg (by norm_num) D)
      _ = CmB := by rw [hCmB]
  -- Step 6: assemble via the abstract polynomial bound.
  exact bohr_sigma_atom_gen_poly_max_bound (p := p) (d := d) (K := K) hd F hν hC hF
    hτ' hCm'nn hmom' hcorr' hεp hLFC' hM hMbound hε hη hη1 hη' α T hT φ hφc hφ0 hφ1
    hφapprox P (fun x => (hP x).1) (E := E) hE (fun x => (hP x).2.1)
    (D := D) (fun x => (hP x).2.2) hCmBnn hCmBbound

end Commons.Combinatorics.Transference
