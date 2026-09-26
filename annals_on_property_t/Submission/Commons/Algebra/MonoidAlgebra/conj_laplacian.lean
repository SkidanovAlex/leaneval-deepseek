import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators
open scoped Classical

set_option autoImplicit false

namespace Commons.Algebra.MonoidAlgebra

/-- The Laplacian element of the group algebra `ℝG` of a group `G` for a finite
set `S ⊆ G`: the element `|S| - ∑_{s ∈ S} s`. This is the generic form of the
Laplacian used in the study of property (T) (equation (1) of Kaluba–Kielak–Nowak). -/
noncomputable def Laplacian {G : Type*} [Group G] (S : Finset G) : MonoidAlgebra ℝ G :=
  Nat.card S - ∑ s ∈ S, MonoidAlgebra.of ℝ G s

/-- Conjugating a monoid-algebra element `x` by `of γ` on the left and `of γ⁻¹`
on the right is the image of `x` under the ring endomorphism induced by
conjugation by `γ`. -/
lemma of_conj_mul_of {G : Type*} [Group G] (x : MonoidAlgebra ℝ G) (γ : G) :
    MonoidAlgebra.of ℝ G γ * x * MonoidAlgebra.of ℝ G γ⁻¹
      = MonoidAlgebra.mapDomainRingHom ℝ (MulAut.conj γ) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy, map_add]
  | single m r =>
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply,
          MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
      change MonoidAlgebra.single (γ * m * γ⁻¹) (1 * r * 1)
        = MonoidAlgebra.single (γ * m * γ⁻¹) r
      simp

/-- Conjugating the Laplacian of a finite set `S` by a group element `γ` gives the
Laplacian of the conjugated set `γ S γ⁻¹`; in particular, if `γ` normalises `S`, the
Laplacian is `γ`-invariant. -/
theorem conj_laplacian {G : Type*} [Group G] (S : Finset G) (γ : G) :
    MonoidAlgebra.of ℝ G γ * Laplacian S * MonoidAlgebra.of ℝ G γ⁻¹
      = Laplacian (S.image (fun s => γ * s * γ⁻¹)) := by
  rw [of_conj_mul_of (Laplacian S) γ]
  have hinj : Function.Injective (fun s : G => γ * s * γ⁻¹) := by
    intro a b h
    have h' := congrArg (fun t : G => γ⁻¹ * t * γ) h
    simpa [mul_assoc] using h'
  have hcard : Nat.card (S.image (fun s : G => γ * s * γ⁻¹)) = Nat.card S := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_coe]
    exact Finset.card_image_of_injective S hinj
  have hsum : (∑ t ∈ S.image (fun s : G => γ * s * γ⁻¹), MonoidAlgebra.of ℝ G t)
      = ∑ s ∈ S, MonoidAlgebra.of ℝ G (γ * s * γ⁻¹) :=
    Finset.sum_image (fun a _ b _ hab => hinj hab)
  have hof : ∀ s : G,
      MonoidAlgebra.mapDomainRingHom ℝ (MulAut.conj γ) (MonoidAlgebra.of ℝ G s)
        = MonoidAlgebra.of ℝ G (γ * s * γ⁻¹) := by
    intro s
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, MonoidAlgebra.of_apply]
    change MonoidAlgebra.single (γ * s * γ⁻¹) 1 = MonoidAlgebra.single (γ * s * γ⁻¹) 1
    rfl
  unfold Laplacian
  rw [map_sub, map_sum]
  rw [map_natCast]
  simp only [hof]
  rw [hcard, ← hsum]

end Commons.Algebra.MonoidAlgebra