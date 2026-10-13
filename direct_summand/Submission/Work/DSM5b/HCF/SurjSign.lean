import Mathlib
import Submission.Work.DSM5b.HCF.Surj

namespace Work.DSM5b.HCF

universe u

open Classical Finset

/-- The increasing enumeration of `S₀`, as an order isomorphism `Fin (q+1) ≃o ↥S₀`
(`hq : q + 1 = S₀.card`).  This is the reference used to define signs. -/
noncomputable def refEquiv {n : ℕ} (S₀ : Finset (Fin n)) (q : ℕ) (hq : q + 1 = S₀.card) :
    Fin (q + 1) ≃ ↥S₀ :=
  (S₀.orderIsoOfFin hq.symm : Fin (q + 1) ≃o ↥S₀)

theorem mem_of_range {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ} (τ : SurjIdx S₀ q)
    (i : Fin (q + 1)) : τ.1 i ∈ S₀ :=
  Finset.mem_of_subset (le_of_eq τ.2) (Finset.mem_image_of_mem τ.1 (Finset.mem_univ i))

/-- The corestriction to `S₀` of a tuple `τ : Fin (q+1) → Fin n` with range `S₀`, as a
bijection when `q+1 = S₀.card`. -/
noncomputable def posEquiv {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ} (τ : SurjIdx S₀ q)
    (hq : q + 1 = S₀.card) : Fin (q + 1) ≃ ↥S₀ :=
  Equiv.ofBijective
    (fun i => (⟨τ.1 i, mem_of_range τ i⟩ : ↥S₀))
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
      intro y
      have hy : y.1 ∈ Work.DSM5b.tupRng τ.1 := by rw [τ.2]; exact y.2
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
      exact ⟨i, Subtype.ext hi⟩, by
      simp [Fintype.card_coe, hq]⟩)

@[simp] theorem posEquiv_apply {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ} (τ : SurjIdx S₀ q)
    (hq : q + 1 = S₀.card) (i : Fin (q + 1)) : ((posEquiv τ hq i : ↥S₀) : Fin n) = τ.1 i := by
  rw [posEquiv, Equiv.ofBijective_apply]

/-- The permutation of `Fin (q+1)` carried by the top tuple `τ` relative to the reference
enumeration. -/
noncomputable def permOf {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ} (τ : SurjIdx S₀ q)
    (hq : q + 1 = S₀.card) : Equiv.Perm (Fin (q + 1)) :=
  (posEquiv τ hq).trans (refEquiv S₀ q hq).symm

/-- The sign of the top tuple `τ`. -/
noncomputable def signOf {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ} (τ : SurjIdx S₀ q)
    (hq : q + 1 = S₀.card) : ℤˣ :=
  Equiv.Perm.sign (permOf τ hq)

/-- The sign of `τ`, as an element of `R`. -/
noncomputable def signOfR {R : Type u} [CommRing R] {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ}
    (τ : SurjIdx S₀ q) (hq : q + 1 = S₀.card) : R :=
  ((signOf τ hq : ℤˣ) : ℤ)

/-- The reference tuple `incTupleE` has permutation `1` and sign `1`. -/
theorem permOf_incTupleE {n : ℕ} (S₀ : Finset (Fin n)) (q : ℕ) (hq : q + 1 = S₀.card) :
    permOf (Work.DSM5b.incTupleE S₀ q hq) hq = 1 := by
  rw [permOf]
  have hpos : posEquiv (Work.DSM5b.incTupleE S₀ q hq) hq = refEquiv S₀ q hq := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rw [posEquiv_apply]
    rfl
  rw [hpos, Equiv.self_trans_symm]
  rfl

@[simp] theorem signOf_incTupleE {n : ℕ} (S₀ : Finset (Fin n)) (q : ℕ) (hq : q + 1 = S₀.card) :
    signOf (Work.DSM5b.incTupleE S₀ q hq) hq = 1 := by
  rw [signOf, permOf_incTupleE, Equiv.Perm.sign_one]

@[simp] theorem signOfR_incTupleE {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n))
    (q : ℕ) (hq : q + 1 = S₀.card) :
    signOfR (R := R) (Work.DSM5b.incTupleE S₀ q hq) hq = 1 := by
  rw [signOfR, signOf_incTupleE]
  simp

end Work.DSM5b.HCF
