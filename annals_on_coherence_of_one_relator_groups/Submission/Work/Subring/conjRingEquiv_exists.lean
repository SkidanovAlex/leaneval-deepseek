import Mathlib

namespace Work.Subring

theorem conjRingEquiv_exists {U : Type*} [Ring U] (D : Subring U) (u : Uˣ)
    (h : ∀ x ∈ (D : Set U), (↑u : U) * x * ((u⁻¹ : Uˣ) : U) ∈ (D : Set U))
    (h' : ∀ x ∈ (D : Set U), ((u⁻¹ : Uˣ) : U) * x * (↑u : U) ∈ (D : Set U)) :
    ∃ e : ↥D ≃+* ↥D,
      (∀ x : ↥D, ((e x : ↥D) : U) = (↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U)) ∧
      (∀ x : ↥D, (((e.symm x : ↥D)) : U) = ((u⁻¹ : Uˣ) : U) * (x : U) * (↑u : U)) := by
  -- The conjugation map x ↦ u x u⁻¹ restricted to D, as a ring homomorphism.
  let f : ↥D →+* ↥D :=
    { toFun := fun x => ⟨(↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U), h x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (↑u : U) * ((x : U) * (y : U)) * ((u⁻¹ : Uˣ) : U) =
          ((↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U)) * ((↑u : U) * (y : U) * ((u⁻¹ : Uˣ) : U))
        rw [show ((↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U)) *
              ((↑u : U) * (y : U) * ((u⁻¹ : Uˣ) : U)) =
            (↑u : U) * (x : U) * (((u⁻¹ : Uˣ) : U) * (↑u : U)) * (y : U) *
              ((u⁻¹ : Uˣ) : U) by noncomm_ring]
        rw [Units.inv_mul, mul_one]
        noncomm_ring
      map_add' := by
        intro x y
        apply Subtype.ext
        show (↑u : U) * ((x : U) + (y : U)) * ((u⁻¹ : Uˣ) : U) =
          ((↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U)) +
            ((↑u : U) * (y : U) * ((u⁻¹ : Uˣ) : U))
        noncomm_ring }
  -- Multiply by u⁻¹ on the left and by u on the right to invert conjugation.
  have hrec : ∀ z : U,
      ((u⁻¹ : Uˣ) : U) * ((↑u : U) * z * ((u⁻¹ : Uˣ) : U)) * (↑u : U) = z := by
    intro z
    rw [show ((u⁻¹ : Uˣ) : U) * ((↑u : U) * z * ((u⁻¹ : Uˣ) : U)) * (↑u : U) =
        (((u⁻¹ : Uˣ) : U) * (↑u : U)) * z * (((u⁻¹ : Uˣ) : U) * (↑u : U)) by
          noncomm_ring]
    rw [Units.inv_mul, one_mul, mul_one]
  have hrec' : ∀ z : U,
      (↑u : U) * (((u⁻¹ : Uˣ) : U) * z * (↑u : U)) * ((u⁻¹ : Uˣ) : U) = z := by
    intro z
    rw [show (↑u : U) * (((u⁻¹ : Uˣ) : U) * z * (↑u : U)) * ((u⁻¹ : Uˣ) : U) =
        ((↑u : U) * ((u⁻¹ : Uˣ) : U)) * z * ((↑u : U) * ((u⁻¹ : Uˣ) : U)) by
          noncomm_ring]
    rw [Units.mul_inv, one_mul, mul_one]
  have hkey : ∀ z x : U, (↑u : U) * z * ((u⁻¹ : Uˣ) : U) = x →
      z = ((u⁻¹ : Uˣ) : U) * x * (↑u : U) := by
    intro z x hzx
    calc z = ((u⁻¹ : Uˣ) : U) * ((↑u : U) * z * ((u⁻¹ : Uˣ) : U)) * (↑u : U) :=
          (hrec z).symm
      _ = ((u⁻¹ : Uˣ) : U) * x * (↑u : U) := by rw [hzx]
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply Subtype.ext
      have hxy' : (↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U) =
          (↑u : U) * (y : U) * ((u⁻¹ : Uˣ) : U) := by
        have hh := congrArg (fun w : ↥D => (w : U)) hxy
        simpa [f] using hh
      calc (x : U) =
            ((u⁻¹ : Uˣ) : U) * ((↑u : U) * (x : U) * ((u⁻¹ : Uˣ) : U)) * (↑u : U) :=
              (hrec (x : U)).symm
        _ = ((u⁻¹ : Uˣ) : U) * ((↑u : U) * (y : U) * ((u⁻¹ : Uˣ) : U)) * (↑u : U) := by
              rw [hxy']
        _ = (y : U) := hrec (y : U)
    · intro y
      refine ⟨⟨((u⁻¹ : Uˣ) : U) * (y : U) * (↑u : U), h' y y.2⟩, ?_⟩
      apply Subtype.ext
      show (↑u : U) * (((u⁻¹ : Uˣ) : U) * (y : U) * (↑u : U)) * ((u⁻¹ : Uˣ) : U) = (y : U)
      exact hrec' (y : U)
  let e : ↥D ≃+* ↥D := RingEquiv.ofBijective f hf
  have happly : ∀ y : ↥D,
      ((e y : ↥D) : U) = (↑u : U) * (y : U) * ((u⁻¹ : Uˣ) : U) := by
    intro y
    rfl
  refine ⟨e, happly, ?_⟩
  intro x
  have h4 : (↑u : U) * ((e.symm x : ↥D) : U) * ((u⁻¹ : Uˣ) : U) = (x : U) := by
    rw [← happly (e.symm x)]
    exact congrArg (fun w : ↥D => (w : U)) (RingEquiv.apply_symm_apply e x)
  exact hkey ((e.symm x : ↥D) : U) (x : U) h4

end Work.Subring
