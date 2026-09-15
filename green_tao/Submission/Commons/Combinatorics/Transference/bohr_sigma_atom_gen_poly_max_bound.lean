import Mathlib
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max

namespace Commons.Combinatorics.Transference

/-- Green–Tao Proposition 6.6 for generators satisfying only the scaled bound
`|F_j| ≤ C(ν+1)`, in the `max` form, with the polynomial coefficient mass split into
a total-mass bound `E` and a degree bound `D` (with the moment bounds `Cm'` bounded by
`CmB` in degrees `≤ D`).  This is
`Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max` applied with the
pointwise energy `E₀ := E * (1 + (2^d·2^d)^D * CmB)`. -/
theorem bohr_sigma_atom_gen_poly_max_bound {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d)
    (F : Fin K → ZMod p → ℝ) {ν : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x)
    {C : ℝ} (hC : 1 ≤ C) (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ C * (ν x + 1))
    {τ' : ZMod p → ℝ} (hτ' : ∀ x, 0 ≤ τ' x) {Cm' : ℕ → ℝ}
    (hCm'0 : ∀ q : ℕ, 0 ≤ Cm' q)
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
    (P : ZMod p → MvPolynomial (Fin K) ℝ)
    (hPapprox : ∀ (x : ZMod p), ∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
      |∏ j : Fin K, φ j x (t j) - MvPolynomial.eval t (P x)| ≤ η')
    {E : ℝ} (hE : 0 ≤ E)
    (hmass : ∀ x : ZMod p, (∑ m ∈ (P x).support, |(P x).coeff m|) ≤ E)
    {D : ℕ} (hdeg : ∀ x : ZMod p, (P x).totalDegree ≤ D)
    {CmB : ℝ} (hCmB : 0 ≤ CmB) (hCmB' : ∀ q : ℕ, q ≤ D → Cm' q ≤ CmB) :
    ∀ x : ZMod p,
      |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
              = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)),
          (ν y - 1)|
        ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1)
            * (E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB))
            + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
          + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by
  classical
  -- The base `B = 2^d · 2^d` of the exponential weight; `B ≥ 1`.
  have hB1 : (1 : ℝ) ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) := by
    have h2d : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    have hnat : (1 : ℕ) ≤ 2 ^ d * 2 ^ d :=
      calc (1 : ℕ) ≤ 2 * 2 := by norm_num
        _ ≤ 2 ^ d * 2 ^ d := Nat.mul_le_mul h2d h2d
    exact_mod_cast hnat
  have hBnn : (0 : ℝ) ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) := le_trans zero_le_one hB1
  -- The target energy level `E₀ = E * (1 + B^D * CmB)` is nonnegative.
  have hLnn : (0 : ℝ) ≤ 1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB := by
    have : (0 : ℝ) ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB :=
      mul_nonneg (pow_nonneg hBnn D) hCmB
    linarith
  -- Pointwise energy bound: mass `E` times the maximal weight in degrees `≤ D`.
  have hE₀ : ∀ x : ZMod p, (∑ m ∈ (P x).support, (|(P x).coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
              Cm' (m.sum (fun _ n => n)))))
        ≤ E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB) := by
    intro x
    calc ∑ m ∈ (P x).support, (|(P x).coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
              Cm' (m.sum (fun _ n => n))))
        ≤ ∑ m ∈ (P x).support, |(P x).coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB) := by
          apply Finset.sum_le_sum
          intro m hm
          have hdegm : m.sum (fun _ n => n) ≤ D :=
            le_trans (MvPolynomial.le_totalDegree hm) (hdeg x)
          have h1 : (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n))
              ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D := pow_le_pow_right₀ hB1 hdegm
          have h2 : Cm' (m.sum (fun _ n => n)) ≤ CmB := hCmB' _ hdegm
          have h3 : (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
                Cm' (m.sum (fun _ n => n))
              ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB :=
            mul_le_mul h1 h2 (hCm'0 _) (pow_nonneg hBnn D)
          exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = (∑ m ∈ (P x).support, |(P x).coeff m|) *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB) := by
          rw [Finset.sum_mul]
      _ ≤ E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB) :=
          mul_le_mul_of_nonneg_right (hmass x) hLnn
  exact bohr_sigma_atom_gen_poly_max (p := p) (d := d) (K := K) hd F hν hC hF hτ'
    hmom' hcorr' hεp hLFC' hM hMbound hε hη hη1 hη' α T hT φ hφc hφ0 hφ1 hφapprox
    P (E₀ := E * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ D * CmB)) hPapprox hE₀

end Commons.Combinatorics.Transference
