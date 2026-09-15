import Mathlib
import Submission.Commons.Combinatorics.Transference.bohr_sigma_atom_poly
import Submission.Commons.Combinatorics.Transference.weier_family_poly
import Submission.Commons.Combinatorics.Transference.sum_atom_le_of_approx_at
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

namespace Commons.Combinatorics.Transference

/-- Green–Tao Proposition 6.6 with a prime-independent error constant `E₀`, in the `max` form:
this is `Commons.Combinatorics.Transference.bohr_sigma_atom_poly` with the hypothesis on the
polynomial coefficient mass weakened from `∑_{x ∈ ZMod p} weight (P x) ≤ E₀` (which is
automatically `≥ p · min weight`, hence unbounded in the prime `p`) to the pointwise bound
`∀ x, weight (P x) ≤ E₀`.  The proof is the proof of `bohr_sigma_atom_poly` with the derivation
of `Ex x ≤ E₀` from the sum replaced by the hypothesis `hE₀`. -/
theorem bohr_sigma_atom_poly_max {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d)
    (F : Fin K → ZMod p → ℝ) {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x)
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q ≤ Cm q)
    {M : ℝ} (hM : 0 ≤ M) (hMbound : ∀ (j : Fin K) (x : ZMod p), |davg d (F j) x| ≤ M)
    {ε η η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hη' : 0 < η')
    (α : Fin K → ℝ) (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (F j) y - α j) / ε - n| ≤ η) → y ∈ T j)
    (φ : Fin K → ZMod p → ℝ → ℝ)
    (hφc : ∀ (j : Fin K) (x : ZMod p), Continuous (φ j x))
    (hφ0 : ∀ (j : Fin K) (x : ZMod p) (t : ℝ), 0 ≤ φ j x t)
    (hφ1 : ∀ (j : Fin K) (x : ZMod p) (t : ℝ), φ j x t ≤ 1)
    (hφapprox : ∀ (j : Fin K) (x : ZMod p),
      ∑ y : ZMod p, (ν y + 1) * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)
          then (1 : ℝ) else 0) - φ j x (davg d (F j) y)| ≤ ∑ y ∈ T j, (ν y + 1))
    (P : ZMod p → MvPolynomial (Fin K) ℝ) {E₀ : ℝ}
    (hPapprox : ∀ (x : ZMod p), ∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
      |∏ j : Fin K, φ j x (t j) - MvPolynomial.eval t (P x)| ≤ η')
    (hE₀ : ∀ x : ZMod p, (∑ m ∈ (P x).support, (|(P x).coeff m| *
              (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
                Cm (m.sum (fun _ n => n))))) ≤ E₀) :
    ∀ x : ZMod p,
      |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)),
          (ν y - 1)|
        ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
            + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
          + (K : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by
  classical
  -- The coefficient-mass "energy" of the polynomial `P x`.
  set Ex : ZMod p → ℝ := fun z => ∑ m ∈ (P z).support, (|(P z).coeff m| *
      (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
        Cm (m.sum (fun _ n => n)))) with hEx
  have hGcpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : ZMod p)⟩)
  intro x
  -- `Ex x ≤ E₀` is exactly the pointwise hypothesis `hE₀`.
  have hExle : Ex x ≤ E₀ := by
    rw [hEx]
    exact hE₀ x
  -- The boundary-layer budget `η₀`.
  set η₀ : ℝ := ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) with hη₀
  have hη₀nn : 0 ≤ η₀ := by
    rw [hη₀]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => by linarith [hν y]))
  -- The `(ν+1)`-weighted approximation is charged to the boundary layer.
  have happrox : ∀ j : Fin K,
      ∑ y : ZMod p, (ν y + 1) * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)
          then (1 : ℝ) else 0) - φ j x (davg d (F j) y)| ≤ η₀ := by
    intro j
    calc ∑ y : ZMod p, (ν y + 1) * |(if y ∈ Finset.univ.filter
            (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)
            then (1 : ℝ) else 0) - φ j x (davg d (F j) y)|
        ≤ ∑ y ∈ T j, (ν y + 1) := hφapprox j x
      _ ≤ η₀ := by
          rw [hη₀]
          refine Finset.single_le_sum (f := fun i : Fin K => ∑ y ∈ T i, (ν y + 1))
            (a := j) ?_ (Finset.mem_univ j)
          intro i _
          exact Finset.sum_nonneg (fun y _ => by linarith [hν y])
  -- The atom estimate `sum_atom_le_of_approx_at`.
  have hmain : |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
        (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)),
        (ν y - 1)|
      ≤ |∑ y : ZMod p, (ν y - 1) * ∏ j : Fin K, φ j x (davg d (F j) y)| + (K : ℝ) * η₀ := by
    have h := sum_atom_le_of_approx_at
      (P := fun j z => Finset.univ.filter
        (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) z - α j) / ε⌋))
      (Ψ := fun j y => φ j x (davg d (F j) y))
      (ν := ν) (η := η₀)
      (δ := |∑ y : ZMod p, (ν y - 1) * ∏ j : Fin K, φ j x (davg d (F j) y)|)
      hη₀nn (abs_nonneg _) hν (fun j y => hφ0 j x (davg d (F j) y))
      (fun j y => hφ1 j x (davg d (F j) y)) x happrox (le_refl _)
    simpa using h
  -- The Weierstrass bound for the specific polynomial `P x`.
  have hW := weier_poly_bound (p := p) (d := d) (K := K) hd hM hν hτ hcorr hmom
    (P x) (Φ := fun t : Fin K → ℝ => ∏ j : Fin K, φ j x (t j)) (η' := η') (le_of_lt hη')
    (hPapprox x) (fun y => ν y - 1) F hF hMbound
  set S : ℝ := ∑ y : ZMod p, (ν y - 1) * ∏ j : Fin K, φ j x (davg d (F j) y) with hS
  have hW' : ((Fintype.card (ZMod p) : ℝ))⁻¹ * |S|
      ≤ Unorm d (fun y => ν y - 1) * Ex x
        + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|) := by
    rw [hS]
    have h := hW
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hGcpos.le)] at h
    have hExx : (∑ m ∈ (P x).support, (|(P x).coeff m| *
        (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
          Cm (m.sum (fun _ n => n))))) = Ex x := by rw [hEx]
    rw [hExx] at h
    exact h
  -- Replace `Ex x` by `E₀` (monotonicity, `Unorm ≥ 0`).
  have hW'' : ((Fintype.card (ZMod p) : ℝ))⁻¹ * |S|
      ≤ Unorm d (fun y => ν y - 1) * E₀
        + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|) := by
    have hUn := Unorm_nonneg d hd (fun y => ν y - 1)
    have := mul_le_mul_of_nonneg_left hExle hUn
    linarith [hW']
  -- Convert the normalised bound into the un-normalised one.
  have hGB : |S| ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
        + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|)) := by
    calc |S| = (Fintype.card (ZMod p) : ℝ)
          * (((Fintype.card (ZMod p) : ℝ))⁻¹ * |S|) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hGcpos), one_mul]
      _ ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
            + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|)) :=
          mul_le_mul_of_nonneg_left hW'' hGcpos.le
  rw [hS] at hmain
  calc |∑ y ∈ Finset.univ.filter (fun y => ∀ j : Fin K, y ∈ Finset.univ.filter
        (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)),
        (ν y - 1)|
      ≤ |S| + (K : ℝ) * η₀ := hmain
    _ ≤ (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
          + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
        + (K : ℝ) * η₀ := by linarith [hGB]
    _ = (Fintype.card (ZMod p) : ℝ) * (Unorm d (fun y => ν y - 1) * E₀
          + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, |ν y - 1|))
        + (K : ℝ) * ∑ j : Fin K, ∑ y ∈ T j, (ν y + 1) := by rw [hη₀]

end Commons.Combinatorics.Transference
