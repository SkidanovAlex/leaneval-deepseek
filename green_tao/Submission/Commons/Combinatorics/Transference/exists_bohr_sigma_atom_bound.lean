import Mathlib
import Submission.Commons.Combinatorics.Transference.exists_levelJoin_polys
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_gen_poly_max
import Submission.Commons.Combinatorics.Transference.cube_corr_half
import Submission.Commons.Combinatorics.Transference.cube_lfc_half

namespace Commons.Combinatorics.Transference

/-- **Green–Tao Proposition 6.6 (the `bohr-sigma` estimate) for the `|F_j| ≤ C(ν+1)`
generators, with a prime-independent error constant.**

This is the one-stop §7 estimate: from the correlation condition and the cube linear forms
condition for `ν` (in the forms produced by `KPseudorandom`, i.e. the finset-form correlation
with moments `Cm`, the mean bound `|𝔼ν − 1| ≤ εm`, and the cube LFC with error `εp`) and the
geometric data (`|F_j| ≤ C(ν+1)`, `|davg d (F_j/(2C))| ≤ M`, shifts `α j`, boundary sets `T j`),
there is an explicit constant `E₀ ≥ 0` such that every atom of the join of the level-set
σ-algebras satisfies the atom-mass bound with `E₀`.

Proof: `cube_corr_half` + `cube_lfc_half` give the corresponding conditions for the halved
measure `(ν+1)/2`; `exists_levelJoin_polys` gives the Weierstrass data (profiles `φ` and
polynomials with coefficient mass `≤ E₀`) for the generators `F_j/(2C)`; and
`bohr_sigma_atom_gen_poly_max` assembles the atom bound. -/
theorem exists_bohr_sigma_atom_bound {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d)
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
    ∃ E₀ : ℝ, 0 ≤ E₀ ∧ ∀ x : ZMod p,
      |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (fun z => F j z / (2 * C)) y - α j) / ε⌋
              = ⌊(davg d (fun z => F j z / (2 * C)) x - α j) / ε⌋)),
          (ν y - 1)|
        ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
            + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
          + ((3 * K : ℕ) : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by
  classical
  -- Step 1: transfer the correlation condition to the halved measure `(ν+1)/2`.
  obtain ⟨Cm', hCm'nn, τ', hτ', hmom', hcorr'⟩ :=
    cube_corr_half (p := p) (d := d) hd ν hν hεm0 hεm1 hmean hτ hmom hcorr
  -- Step 2: transfer the cube linear forms condition to the halved measure.
  have hLFC' := cube_lfc_half (p := p) (d := d) ν hεp hLFC
  -- Step 3: the Weierstrass data for the divided generators `F j / (2C)`.
  obtain ⟨E, _hE, φ, hφc, hφ0, hφ1, hφapprox, hpoly⟩ :=
    exists_levelJoin_polys (p := p) (d := d) (K := K) (fun j z => F j z / (2 * C)) ν
      hε hη hη1 hν hη' hM α hα0 hαε T hT hMbound
  -- Step 4: pick, for every `x`, a polynomial approximating the product of profiles,
  -- with coefficient mass bounded by `E`; the constant `E₀` is the sum over `x` of the
  -- corresponding moment-weighted coefficient mass (finite, since `ZMod p` is finite).
  obtain ⟨P, hPapprox, _hmass⟩ :
      ∃ P : ZMod p → MvPolynomial (Fin K) ℝ,
        (∀ (x : ZMod p), ∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
          |∏ j : Fin K, φ j x (t j) - MvPolynomial.eval t (P x)| ≤ η') ∧
        (∀ x : ZMod p, (∑ m ∈ (P x).support, |(P x).coeff m|) ≤ E) := by
    choose P hP using hpoly
    exact ⟨P, fun x => (hP x).1, fun x => (hP x).2⟩
  set E₀ : ℝ := ∑ x : ZMod p, ∑ m ∈ (P x).support, (|(P x).coeff m| *
      (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
        Cm' (m.sum (fun _ n => n)))) with hE₀def
  have hterm : ∀ (x : ZMod p) (m : Fin K →₀ ℕ), m ∈ (P x).support →
      0 ≤ |(P x).coeff m| * (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
        Cm' (m.sum (fun _ n => n))) := by
    intro x m _
    refine mul_nonneg (abs_nonneg _) ?_
    have h1 : (0 : ℝ) ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) :=
      pow_nonneg (Nat.cast_nonneg _) _
    have h2 : 0 ≤ Cm' (m.sum (fun _ n => n)) := hCm'nn _
    nlinarith
  refine ⟨E₀, ?_, ?_⟩
  · rw [hE₀def]
    exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun m hm => hterm x m hm))
  · -- Step 5: assemble with the one-stop estimate.
    have hE₀ : ∀ x : ZMod p, (∑ m ∈ (P x).support, (|(P x).coeff m| *
          (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
            Cm' (m.sum (fun _ n => n))))) ≤ E₀ := by
      intro x
      rw [hE₀def]
      exact Finset.single_le_sum (fun y _ => Finset.sum_nonneg (fun m hm => hterm y m hm))
        (Finset.mem_univ x)
    exact bohr_sigma_atom_gen_poly_max (p := p) (d := d) (K := K) hd F hν hC hF
      hτ' hmom' hcorr' hεp hLFC' hM hMbound hε hη hη1 hη' α T hT φ hφc hφ0 hφ1 hφapprox P hPapprox hE₀


end Commons.Combinatorics.Transference
