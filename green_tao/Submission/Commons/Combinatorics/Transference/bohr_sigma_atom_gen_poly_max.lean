import Mathlib
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_poly_max
import Submission.Commons.Combinatorics.Transference.Unorm_smul_of_nonneg

namespace Commons.Combinatorics.Transference

/-- Green–Tao Proposition 6.6 for generators satisfying only the scaled bound
`|F_j| ≤ C(ν+1)`, with an EXPLICIT error constant `E₀` and in the `max` form (not summed over
the points `x`).  This is `Commons.Combinatorics.Transference.bohr_sigma_atom_gen` with the
`bohr-sigma` estimate supplied by `bohr_sigma_atom_poly_max` (applied to the halved measure
`(ν+1)/2`, which is why the hypotheses on `τ'`, `Cm'`, `hcorr'`, `hLFC'`, `hφapprox` refer to
`(ν+1)/2`).  The conclusion is the bound with the given `E₀` in place of the existential `E`
of `bohr_sigma_atom_gen`; the boundary coefficient is `3K` as there. -/
theorem bohr_sigma_atom_gen_poly_max {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d)
    (F : Fin K → ZMod p → ℝ) {ν : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x)
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ C * (ν x + 1))
    {τ' : ZMod p → ℝ} (hτ' : ∀ x, 0 ≤ τ' x) {Cm' : ℕ → ℝ}
    (hmom' : ∀ q : ℕ, ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ' x) ^ q ≤ Cm' q)
    (hcorr' : ∀ h : Fin d → ZMod p,
      ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ((ν (y + ∑ i, (if ω i then h i else 0)) + 1) / 2)
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ' ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {εp : ℝ} (hεp : 0 ≤ εp)
    (hLFC' : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ((ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) + 1) / 2) - 1|
        ≤ εp)
    {M : ℝ} (hM : 0 ≤ M)
    (hMbound : ∀ (j : Fin K) (x : ZMod p), |davg d (fun y => F j y / (2 * C)) x| ≤ M)
    {ε η η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hη' : 0 < η')
    (α : Fin K → ℝ) (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (fun z => F j z / (2 * C)) y - α j) / ε - n| ≤ η) → y ∈ T j)
    (φ : Fin K → ZMod p → ℝ → ℝ)
    (hφc : ∀ (j : Fin K) (x : ZMod p), Continuous (φ j x))
    (hφ0 : ∀ (j : Fin K) (x : ZMod p) (t : ℝ), 0 ≤ φ j x t)
    (hφ1 : ∀ (j : Fin K) (x : ZMod p) (t : ℝ), φ j x t ≤ 1)
    (hφapprox : ∀ (j : Fin K) (x : ZMod p),
      ∑ y : ZMod p, ((ν y + 1) / 2 + 1) * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
              = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)
          then (1 : ℝ) else 0) - φ j x (davg d (fun z => F j z / (2 * C)) y)|
        ≤ ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
    (P : ZMod p → MvPolynomial (Fin K) ℝ) {E₀ : ℝ}
    (hPapprox : ∀ (x : ZMod p), ∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
      |∏ j : Fin K, φ j x (t j) - MvPolynomial.eval t (P x)| ≤ η')
    (hE₀ : ∀ x : ZMod p, (∑ m ∈ (P x).support, (|(P x).coeff m| *
              (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
                Cm' (m.sum (fun _ n => n))))) ≤ E₀) :
    ∀ x : ZMod p,
      |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
              = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)),
          (ν y - 1)|
        ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
            + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
          + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by
  classical
  have hCpos : 0 < C := by linarith
  -- positivity of the halved measure and the scaled generator bound
  have hν' : ∀ x : ZMod p, 0 ≤ (ν x + 1) / 2 := fun x => by have := hν x; linarith
  have hF' : ∀ (j : Fin K) (x : ZMod p), |F j x / (2 * C)| ≤ (ν x + 1) / 2 := by
    intro j x
    have h2C : (0 : ℝ) < 2 * C := by linarith
    rw [abs_div, abs_of_pos h2C]
    have hstep : |F j x| / (2 * C) ≤ C * (ν x + 1) / (2 * C) :=
      div_le_div_of_nonneg_right (hF j x) h2C.le
    have heq : C * (ν x + 1) / (2 * C) = (ν x + 1) / 2 := by
      rw [show (2 : ℝ) * C = C * 2 by ring]
      exact mul_div_mul_left (ν x + 1) 2 (ne_of_gt hCpos)
    linarith
  -- the halved measure is the halfway measure `(ν+1)/2`
  have hb := bohr_sigma_atom_poly_max (p := p) (d := d) (K := K) hd
    (fun j z => F j z / (2 * C)) hν' hτ' hF' hcorr' hmom' hM hMbound hε hη hη1 hη'
    α T hT φ hφc hφ0 hφ1 hφapprox P hPapprox hE₀
  -- conversion identities between `ν` and `ν' = (ν+1)/2`
  have hU : Unorm d (fun y => ν y - 1) = 2 * Unorm d (fun y => (ν y + 1) / 2 - 1) := by
    have h : (fun y : ZMod p => ν y - 1) = fun y => (2 : ℝ) * ((ν y + 1) / 2 - 1) := by
      funext y; ring
    rw [h, Unorm_smul_of_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)]
  have hS : (∑ y : ZMod p, |ν y - 1|)
      = 2 * ∑ y : ZMod p, |(ν y + 1) / 2 - 1| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _
    rw [show ν y - 1 = 2 * ((ν y + 1) / 2 - 1) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hT2 : 2 * (∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
      ≤ 3 * (∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by
    have h1 : ∀ j : Fin K,
        2 * (∑ y ∈ T j, ((ν y + 1) / 2 + 1)) ≤ 3 * (∑ y ∈ T j, (ν y + 1)) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum; intro y _
      have := hν y; linarith
    calc 2 * (∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
        = ∑ j : Fin K, 2 * (∑ y ∈ T j, ((ν y + 1) / 2 + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin K, 3 * (∑ y ∈ T j, (ν y + 1)) := Finset.sum_le_sum (fun j _ => h1 j)
      _ = 3 * (∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by rw [Finset.mul_sum]
  intro x
  set A : Finset (ZMod p) := Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
      (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
          = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)) with hA
  have hx := hb x
  simp only [← hA] at hx
  have hL : |∑ y ∈ A, (ν y - 1)| = 2 * |∑ y ∈ A, ((ν y + 1) / 2 - 1)| := by
    have hh : (∑ y ∈ A, (ν y - 1)) = 2 * (∑ y ∈ A, ((ν y + 1) / 2 - 1)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    rw [hh, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hlast : 2 * (K : ℝ) * (∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1))
      ≤ ((3 * K : ℕ) : ℝ) * (∑ j : Fin K, ∑ y ∈ T j, (ν y + 1)) := by
    have hco : ((3 * K : ℕ) : ℝ) = 3 * (K : ℝ) := by push_cast; ring
    rw [hco]
    have hmul := mul_le_mul_of_nonneg_left hT2 hKnn
    nlinarith [hmul]
  calc |∑ y ∈ A, (ν y - 1)|
      = 2 * |∑ y ∈ A, ((ν y + 1) / 2 - 1)| := hL
    _ ≤ 2 * ((Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => (ν y + 1) / 2 - 1) * E₀
          + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, |(ν y + 1) / 2 - 1|))
        + (K : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1)) := by linarith [hx]
    _ = (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
          + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, |ν y - 1|))
        + 2 * (K : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, ((ν y + 1) / 2 + 1) := by
        rw [hU, hS]; ring
    _ ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
          + η' * ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, |ν y - 1|))
        + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by linarith [hlast]

end Commons.Combinatorics.Transference
