import Mathlib
import Submission.Commons.Combinatorics.Transference.weier_poly_bound
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Proposition 6.5 / Proposition 6.6, polynomial family version.**

For a finite family `(P i)_{i ∈ s}` of polynomials on the cube, uniformly approximated by
`(Φ i)_{i ∈ s}` up to `η'`, the pairing of `f` against `Φ i ∘ 𝒟F` is bounded by
`Unorm d f` times the sum over the whole family of the coefficient mass constants, plus the
approximation error term.  This is the "family" form of `weier_poly_bound`, obtained by
applying `weier_poly_bound` term by term and dominating the single term for `i` by the full
sum over `s` (all summands are nonnegative since `Cm ≥ 0`). -/
theorem weier_family_poly {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M)
    {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    {Cm : ℕ → ℝ} (hmom : ∀ q : ℕ, (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q ≤ Cm q)
    {ι : Type*} (s : Finset ι) (Φ : ι → (Fin K → ℝ) → ℝ) (P : ι → MvPolynomial (Fin K) ℝ)
    {η' : ℝ} (hη' : 0 ≤ η')
    (happrox : ∀ i ∈ s, ∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
      |Φ i t - MvPolynomial.eval t (P i)| ≤ η') :
    ∀ (f : ZMod p → ℝ) (F : Fin K → ZMod p → ℝ),
      (∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x) →
      (∀ (j : Fin K) (x : ZMod p), |davg d (F j) x| ≤ M) →
      ∀ i ∈ s,
      |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x * Φ i (fun j : Fin K => davg d (F j) x)|
        ≤ Unorm d f * (∑ i ∈ s, ∑ m ∈ (P i).support, (|(P i).coeff m| *
              (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
                Cm (m.sum (fun _ n => n)))))
          + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := by
  intro f F hF hFd i hi
  -- `Cm q` is nonnegative, because it dominates a nonnegative average of powers of `τ ≥ 0`.
  have hCm : ∀ q : ℕ, 0 ≤ Cm q := by
    intro q
    have h1 : 0 ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ q :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun y _ => pow_nonneg (hτ y) q)
    exact le_trans h1 (hmom q)
  -- Each coefficient mass summand is nonnegative.
  have hterm : ∀ (i' : ι) (m : Fin K →₀ ℕ),
      0 ≤ |(P i').coeff m| *
        (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
          Cm (m.sum (fun _ n => n))) := by
    intro i' m
    refine mul_nonneg (abs_nonneg _) ?_
    have hp : (0 : ℝ) ≤ (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) :=
      pow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_nonneg hp (hCm (m.sum (fun _ n => n)))
    linarith
  have hUn : 0 ≤ Unorm d f := Unorm_nonneg d hd f
  have hbound :=
    weier_poly_bound (p := p) (d := d) (K := K) hd hM hν hτ hcorr hmom (P i) hη'
      (happrox i hi) f F hF hFd
  -- Dominating the single `i`-term by the sum over the whole family `s`.
  have hsum_le :
      (∑ m ∈ (P i).support, (|(P i).coeff m| *
          (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
            Cm (m.sum (fun _ n => n)))))
        ≤ ∑ i' ∈ s, ∑ m ∈ (P i').support, (|(P i').coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
              Cm (m.sum (fun _ n => n)))) :=
    Finset.single_le_sum
      (s := s) (a := i)
      (f := fun i' => ∑ m ∈ (P i').support, (|(P i').coeff m| *
        (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
          Cm (m.sum (fun _ n => n)))))
      (fun i' _ => Finset.sum_nonneg fun m _ => hterm i' m) hi
  calc |((Fintype.card (ZMod p) : ℝ))⁻¹ *
          ∑ x : ZMod p, f x * Φ i (fun j : Fin K => davg d (F j) x)|
      ≤ Unorm d f * (∑ m ∈ (P i).support, (|(P i).coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
              Cm (m.sum (fun _ n => n)))))
          + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) := hbound
    _ ≤ Unorm d f * (∑ i' ∈ s, ∑ m ∈ (P i').support, (|(P i').coeff m| *
            (1 + (((2 ^ d * 2 ^ d : ℕ)) : ℝ) ^ (m.sum (fun _ n => n)) *
              Cm (m.sum (fun _ n => n)))))
          + η' * (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, |f x|) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum_le hUn) le_rfl

end Commons.Combinatorics.Transference
