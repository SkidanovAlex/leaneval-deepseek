import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_le
import Submission.Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff
import Submission.Work.ORHughesFree.Instances
import Submission.Work.StarRegular.relativeInverseMap
import Submission.Work.StarRegular.map_starSubringClosure_subset

namespace Work.StarRegular

open Work.ORHughesFree

/-- Conjugation by a unit of a ring, `x ↦ u * x * u⁻¹`, as a ring endomorphism. -/
def conjHom {U : Type*} [Ring U] (u : Uˣ) : U →+* U where
  toFun := fun x => (↑u : U) * x * (↑(u⁻¹) : U)
  map_one' := by simp
  map_mul' := by
    intro a b
    simp only [mul_assoc]
    rw [← mul_assoc (↑(u⁻¹) : U) (↑u : U) (b * ↑(u⁻¹) : U), Units.inv_mul, one_mul]
  map_zero' := by simp
  map_add' := by intro a b; rw [mul_add, add_mul]

theorem conjHom_apply {U : Type*} [Ring U] (u : Uˣ) (x : U) :
    conjHom u x = (↑u : U) * x * (↑(u⁻¹) : U) := rfl

/-- Conjugation by a unitary `u` (`star u = u⁻¹`) commutes with `star`. -/
theorem conjHom_star {U : Type*} [Ring U] [StarRing U] (u : Uˣ)
    (hu : star (↑u : U) = ((u⁻¹ : Uˣ) : U)) (a : U) :
    conjHom u (star a) = star (conjHom u a) := by
  have h1 : star ((↑(u⁻¹ : Uˣ) : U)) = (↑u : U) := by rw [← hu, star_star]
  rw [conjHom_apply, conjHom_apply, star_mul, star_mul, h1, hu, mul_assoc]

/-- Conjugation by a unitary maps every stage of the approximating chain into itself. -/
theorem starRegularChain_conj_mem {U : Type*} [Ring U] [StarRing U] (R : StarSubring U) (u : Uˣ)
    (hu : star (↑u : U) = ((u⁻¹ : Uˣ) : U))
    (h : ∀ x ∈ (R : Set U), (↑u : U) * x * (↑(u⁻¹) : U) ∈ (R : Set U)) :
    ∀ n, ∀ x ∈ (starRegularChain R n : Set U),
      conjHom u x ∈ (starRegularChain R n : Set U) := by
  intro n
  induction n with
  | zero => intro x hx; rw [conjHom_apply]; exact h x hx
  | succ n ih =>
    have hgen : ∀ x ∈ ((starRegularChain R n : Set U) ∪
        relativeInverses (starRegularChain R n : Set U)),
        conjHom u x ∈ (starSubringClosure ((starRegularChain R n : Set U) ∪
          relativeInverses (starRegularChain R n : Set U)) : Set U) := by
      rintro x (hx | hx)
      · exact subset_starSubringClosure _ (Or.inl (ih x hx))
      · rcases hx with ⟨a, ha, hay⟩
        exact subset_starSubringClosure _ (Or.inr ⟨conjHom u a, ih a ha,
          relativeInverseMap hay (conjHom u) (conjHom_star u hu)⟩)
    intro x hx
    exact map_starSubringClosure_subset (conjHom u) (conjHom_star u hu) hgen x hx

theorem starRegularClosure_conj {U : Type*} [Ring U] [StarRing U]
    [Work.ORHughesFree.IsStarRegular U]
    (R : Work.ORHughesFree.StarSubring U) (u : Uˣ)
    (hu : star (↑u : U) = ((u⁻¹ : Uˣ) : U))
    (h : ∀ x ∈ (R : Set U), (↑u : U) * x * (↑(u⁻¹) : U) ∈ (R : Set U))
    (h' : ∀ x ∈ (R : Set U), (↑(u⁻¹) : U) * x * (↑u : U) ∈ (R : Set U)) :
    (∀ x ∈ (Work.ORHughesFree.starRegularClosure R : Set U),
        (↑u : U) * x * (↑(u⁻¹) : U) ∈ (Work.ORHughesFree.starRegularClosure R : Set U)) ∧
      (∀ x ∈ (Work.ORHughesFree.starRegularClosure R : Set U),
        (↑(u⁻¹) : U) * x * (↑u : U) ∈ (Work.ORHughesFree.starRegularClosure R : Set U)) := by
  have h1 : star ((↑(u⁻¹ : Uˣ) : U)) = (↑u : U) := by rw [← hu, star_star]
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ :=
      (Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff R x).mp hx
    refine (Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff R _).mpr ⟨n, ?_⟩
    have key := starRegularChain_conj_mem R u hu h n x hn
    rwa [conjHom_apply] at key
  · intro x hx
    obtain ⟨n, hn⟩ :=
      (Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff R x).mp hx
    refine (Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff R _).mpr ⟨n, ?_⟩
    have key := starRegularChain_conj_mem R (u⁻¹)
      (by rw [inv_inv]; exact h1) (by intro y hy; rw [inv_inv]; exact h' y hy) n x hn
    rwa [conjHom_apply, inv_inv] at key

end Work.StarRegular
