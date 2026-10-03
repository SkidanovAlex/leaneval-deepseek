/-
# `Submission.Work.FIArea3.JointCount.pieces` — the Gaussian-divisor piece vocabulary

For a positive integer `d` the set `{z : ℤ[i] | d ∣ |z|²}` is a finite union of *principal ideals*
of `ℤ[i]`: for a Gaussian divisor `u` of `d` the piece

  `gaussPiece d u = {z | u ∣ z ∧ (d/u) ∣ star z}`

is the ideal `u ℤ[i] ∩ star((d/u)) ℤ[i] = gaussPieceGen d u · ℤ[i]`, where
`gaussPieceGen d u = EuclideanDomain.lcm u (star (d/u))` (membership is divisibility by the
generator, `mem_gaussPiece_iff`).

Splitting `d = u · (d/u)` along such a `u` and using `z * star z = |z|²` gives the cover

  `{z | d ∣ |z|²} = ⋃_{w maximal} w · ℤ[i]`

over the *maximal* piece generators (`GaussPieceMax`); the maximal pieces are the ones of minimal
index, they number `∏_{p ≡ 1 (4)} (k_p + 1) ≤ τ(d)`, and each has index
`∏_{p ≡ 1 (4)} p^{k_p} · ∏_{p ≡ 3 (4)} p^{k_p + (k_p mod 2)} · 2^{k_2} ≥ d`.

The joint condition `e ∣ Δ(z₁, ·)` cuts a piece `w ℤ[i]` down to the lattice
`w · {y | e ∣ Im(star z₁ · w · y)}`, of index `gnorm w · e / gcd(e, star z₁ · w)`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The generator of the piece `gaussPiece d u`: the Gaussian lcm of `u` and `star (d/u)`.
It is defined through the Euclidean algorithm (`EuclideanDomain.lcm`), so that
`EuclideanDomain.lcm_dvd_iff` gives the ideal membership `gaussPiece d u = {z | gen ∣ z}`. -/
def gaussPieceGen (d : ℕ) (u : GaussianInt) : GaussianInt :=
  EuclideanDomain.lcm u (star ((d : GaussianInt) / u))

/-- The `u`-th piece of the Gaussian-divisor decomposition of `{z | d ∣ |z|²}`. -/
def gaussPiece (d : ℕ) (u : GaussianInt) : Set GaussianInt :=
  {z : GaussianInt | u ∣ z ∧ ((d : GaussianInt) / u) ∣ star z}

/-- The generator of a piece `gaussPiece d u` for some Gaussian divisor `u` of `d`. -/
def IsPieceGen (d : ℕ) (w : GaussianInt) : Prop :=
  ∃ u : GaussianInt, u ∣ (d : GaussianInt) ∧ w = gaussPieceGen d u

/-- A *maximal* piece generator: a piece generator `w` such that every piece generator dividing
`w` is an associate of `w` (equivalently, the piece `w ℤ[i]` is maximal under inclusion among the
pieces `gaussPiece d u`).  These are exactly the pieces of minimal index, and every point of
`{z | d ∣ |z|²}` lies in one of them (see the delegated `maximal_piece_cover`). -/
def GaussPieceMax (d : ℕ) (w : GaussianInt) : Prop :=
  IsPieceGen d w ∧ ∀ v : GaussianInt, IsPieceGen d v → v ∣ w → w ∣ v

/-- Conjugation exchanges the two divisibility conditions of the piece. -/
lemma star_dvd_iff_dvd_star (a z : GaussianInt) : star a ∣ z ↔ a ∣ star z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨star w, by simp [star_mul, mul_comm]⟩
  · rintro ⟨w, hw⟩
    refine ⟨star w, ?_⟩
    have : z = star (star z) := by simp
    rw [this, hw]
    simp [star_mul, mul_comm]

/-- Membership in the piece is divisibility by the generator. -/
lemma mem_gaussPiece_iff {d : ℕ} {u z : GaussianInt} :
    z ∈ gaussPiece d u ↔ gaussPieceGen d u ∣ z := by
  rw [gaussPiece, gaussPieceGen, EuclideanDomain.lcm_dvd_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (star_dvd_iff_dvd_star _ _).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (star_dvd_iff_dvd_star _ _).mp h2⟩

/-- The lattice `{y : ℤ[i] | e ∣ A·y.im + B·y.re}` (the solution lattice of a linear congruence
mod `e`).  It contains `e ℤ[i]`, hence has finite index, and its index is
`e / gcd(e, |A|, |B|)` (delegated: `index_yLat`). -/
def yLat (A B : ℤ) (e : ℕ) : AddSubgroup GaussianInt where
  carrier := {y : GaussianInt | (e : ℤ) ∣ A * y.im + B * y.re}
  zero_mem' := by simp
  add_mem' := by
    intro y y' hy hy'
    simp only [Set.mem_ofPred_eq] at hy hy' ⊢
    have h : A * (y + y').im + B * (y + y').re
        = (A * y.im + B * y.re) + (A * y'.im + B * y'.re) := by simp; ring
    rw [h]; exact dvd_add hy hy'
  neg_mem' := by
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    have h : A * (-y).im + B * (-y).re = -(A * y.im + B * y.re) := by simp; ring
    rw [h]; exact dvd_neg.mpr hy

/-- The lattice of the piece `w ℤ[i]` cut by the joint condition `e ∣ Δ(z₁, ·)`:
`z` lies in it iff `w ∣ z` and `(star z₁ * z).im = Δ(z₁,z)` is divisible by `e`. -/
def jointPieceLat (z₁ w : GaussianInt) (e : ℕ) : AddSubgroup GaussianInt :=
  (yLat (star z₁ * w).im (star z₁ * w).re e).map (AddMonoidHom.mulRight w)

/-- Membership in `jointPieceLat` unwound: `z` lies in it iff `z = y * w` for some `y`
satisfying the congruence `e ∣ (star z₁ * w).im * y.im + (star z₁ * w).re * y.re`. -/
lemma mem_jointPieceLat_iff (z₁ w z : GaussianInt) (e : ℕ) :
    z ∈ jointPieceLat z₁ w e ↔
      ∃ y : GaussianInt, y * w = z ∧
        (e : ℤ) ∣ (star z₁ * w).im * y.im + (star z₁ * w).re * y.re := by
  rw [jointPieceLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    exact ⟨y, hyz, by simpa [yLat] using hy⟩
  · rintro ⟨y, hyz, hy⟩
    exact ⟨y, by simpa [yLat] using hy, hyz⟩

end

end Work.FIArea3.JointCount
