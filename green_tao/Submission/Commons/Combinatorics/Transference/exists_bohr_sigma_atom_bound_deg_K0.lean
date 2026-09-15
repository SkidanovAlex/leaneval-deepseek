import Mathlib
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0
import Submission.Commons.Combinatorics.Transference.cube_corr_half_bound
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max_bound
import Submission.Commons.Combinatorics.Transference.exists_bohr_sigma_atom_bound_deg

namespace Commons.Combinatorics.Transference

theorem exists_bohr_sigma_atom_bound_deg_K0 {p : ℕ} [Fact p.Prime] {d K₀ K : ℕ} (hd : 1 ≤ d)
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
  exact exists_bohr_sigma_atom_bound_deg (p := p) (d := d) (K := K) hd F hν hτ hC hF hcorr
    hmom hεm0 hεm1 hmean hεp hLFC hM hMbound hε hη hη1 hη' α hα0 hαε T hT

end Commons.Combinatorics.Transference
