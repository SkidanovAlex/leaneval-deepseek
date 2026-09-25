import Mathlib
import Submission.Work.LT.relT_defs

/-!
# Pythagoras for the `ℓ²`-norm of a finite sum of pairwise orthogonal complex functions

For `l2sq h = ∑ x, Complex.normSq (h x)` (the square of the `ℓ²`-norm of a complex-valued
function on a finite type, see `Submission/Work/LT/relT_defs.lean` and `relT_l2.lean`) and
`ip a b = ∑ x, star (a x) * b x` (the Hermitian pairing), the Pythagorean identity

`l2sq (∑_{z ∈ B} φ z) = ∑_{z ∈ B} l2sq (φ z)`

holds whenever the `φ z`, `z ∈ B`, are pairwise orthogonal: `ip (φ z) (φ z') = 0` for
`z ≠ z'` in `B`.

The proof expands the double sum

`∑_x (∑_{z ∈ B} φ z x) * star (∑_{z' ∈ B} φ z' x)
   = ∑_x ∑_{z ∈ B} ∑_{z' ∈ B} φ z x * star (φ z' x)
   = ∑_{z ∈ B} ∑_{z' ∈ B} ∑_x φ z x * star (φ z' x)`,

takes real parts (`Complex.mul_conj` identifies `Complex.normSq` with the real part of
`w * star w`), and then observes that the inner sum over `z'` collapses to the single term
`z' = z` because

`∑_x φ z x * star (φ z' x) = star (ip (φ z) (φ z')) = 0` for `z ≠ z'`,
while `∑_x φ z x * star (φ z x) = ↑(l2sq (φ z))`.

This is the general form of the second conjunct of `relT_fourier` (the sub-sum Plancherel
identity for the `U`-Fourier decomposition of the column lemma `sl3_relT_column`).
-/

namespace Work.LT

/-- `Complex.normSq` as the real part of `w * star w`. -/
lemma l2sq_sum_orthogonal_normSq_eq_re (w : ℂ) : Complex.normSq w = (w * star w).re := by
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- The conjugate of the Hermitian pairing `ip a b = ∑ x, star (a x) * b x` is the swapped
pairing `∑ x, a x * star (b x)`. -/
lemma l2sq_sum_orthogonal_star_ip {X : Type*} [Fintype X] (a b : X → ℂ) :
    star (ip a b) = ∑ x, a x * star (b x) := by
  rw [ip, star_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [star_mul, star_star, mul_comm]

/-- The diagonal pairing `∑ x, a x * star (a x)` is the coercion of `l2sq a`. -/
lemma l2sq_sum_orthogonal_self {X : Type*} [Fintype X] (a : X → ℂ) :
    (∑ x, a x * star (a x)) = (l2sq a : ℂ) := by
  rw [l2sq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => Complex.mul_conj (a x)

/-- A sum over `B` in which only the term `z` is nonzero equals that term. -/
lemma l2sq_sum_orthogonal_sum_eq_of_forall_ne_zero {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] {B : Finset ι} {g : ι → M} {z : ι} (hz : z ∈ B)
    (h0 : ∀ z' ∈ B, z ≠ z' → g z' = 0) : ∑ z' ∈ B, g z' = g z :=
  Finset.sum_eq_single_of_mem z hz (fun b hb hne => h0 b hb (Ne.symm hne))

/-- The complex form of the Pythagorean identity: for a family `φ` of pairwise orthogonal
functions on `B`, the double sum `∑_x (∑_{z ∈ B} φ z x) * star (∑_{z' ∈ B} φ z' x)` (whose real
part is `l2sq (∑_{z ∈ B} φ z)`) equals `∑_{z ∈ B} ↑(l2sq (φ z))`. -/
lemma l2sq_sum_orthogonal_aux {X : Type*} [Fintype X] {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (φ : ι → X → ℂ)
    (h : ∀ z ∈ B, ∀ z' ∈ B, z ≠ z' → ip (φ z) (φ z') = 0) :
    (∑ x, (∑ z ∈ B, φ z x) * star (∑ z' ∈ B, φ z' x))
      = ∑ z ∈ B, (l2sq (φ z) : ℂ) := by
  -- expand the product of the two sums
  have e1 : (∑ x, (∑ z ∈ B, φ z x) * star (∑ z' ∈ B, φ z' x))
      = ∑ x, ∑ z ∈ B, ∑ z' ∈ B, φ z x * star (φ z' x) := by
    exact Finset.sum_congr rfl fun x _ => by rw [star_sum, Finset.sum_mul_sum]
  -- move the outer sum over `x` inside
  rw [e1]
  have e2 : (∑ x, ∑ z ∈ B, ∑ z' ∈ B, φ z x * star (φ z' x))
      = ∑ z ∈ B, ∑ z' ∈ B, ∑ x, φ z x * star (φ z' x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
  rw [e2]
  -- the inner sum over `z'` collapses to `z' = z` by orthogonality
  have e3 : (∑ z ∈ B, ∑ z' ∈ B, ∑ x, φ z x * star (φ z' x))
      = ∑ z ∈ B, ∑ x, φ z x * star (φ z x) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    refine l2sq_sum_orthogonal_sum_eq_of_forall_ne_zero hz ?_
    intro z' hz' hne
    rw [← l2sq_sum_orthogonal_star_ip, h z hz z' hz' hne, star_zero]
  rw [e3]
  -- the diagonal terms are the squared norms
  exact Finset.sum_congr rfl fun z _ => l2sq_sum_orthogonal_self (φ z)

theorem l2sq_sum_orthogonal :
    ∀ {X : Type*} [Fintype X] {ι : Type*} [DecidableEq ι] (B : Finset ι) (φ : ι → X → ℂ),
      (∀ z ∈ B, ∀ z' ∈ B, z ≠ z' → ip (φ z) (φ z') = 0) →
      l2sq (fun x => ∑ z ∈ B, φ z x) = ∑ z ∈ B, l2sq (φ z) := by
  intro X _ ι _ B φ h
  calc l2sq (fun x => ∑ z ∈ B, φ z x)
      = ∑ x, Complex.normSq (∑ z ∈ B, φ z x) := rfl
    _ = (∑ x, (∑ z ∈ B, φ z x) * star (∑ z' ∈ B, φ z' x)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun x _ =>
          l2sq_sum_orthogonal_normSq_eq_re (∑ z ∈ B, φ z x)
    _ = (∑ z ∈ B, (l2sq (φ z) : ℂ)).re := by
        rw [l2sq_sum_orthogonal_aux B φ h]
    _ = ∑ z ∈ B, l2sq (φ z) := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun z _ => Complex.ofReal_re _

end Work.LT
