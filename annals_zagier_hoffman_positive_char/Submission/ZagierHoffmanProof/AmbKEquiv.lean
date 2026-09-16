import Submission.ZagierHoffmanProof.ACMplDatum

/-!
# The isomorphism `K = F_q(θ) ≅ RatFunc F`

The analytic chapter produces its conclusions inside the ambient field `L = Ambient F`, namely as
membership in the subfield `ambK F = F_q(θ)`.  The statements of the challenge, on the other hand,
live over `K = RatFunc F` and `K_∞ = RatFunc.CompletionAtInfty F`.  This file provides the missing
bridge:

  ★★★ `ambKEquiv : RatFunc F ≃+* ↥(ambK F)`,   `ambKEquiv X = ambTheta F`,  `ambKEquiv c = ambCoeff F c`,

i.e. `ambK F` is `F_q(θ)` *as a copy of the rational function field* (`θ` being transcendental over
`F` by `ambTheta_transcendental`).  It is the ring-theoretic half of the transfer
`ambK F → RatFunc F → CompletionAtInfty F` needed to state the challenge's theorems in terms of
`𝒵 F w`, `𝒯 F w`.

## Main results

* `ambKPolyHom` — `F[X] →+* ↥(ambK F)`, `X ↦ θ`;
* `ambKHom` — the induced field homomorphism `RatFunc F →+* ↥(ambK F)`;
* ★★★ `ambKEquiv`.
-/

set_option autoImplicit false
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The map `F[X] →+* ↥(ambK F)`, `X ↦ θ`, `c ↦ c`. -/
noncomputable def ambKPolyHom : Polynomial F →+* ↥(ambK F) :=
  Polynomial.eval₂RingHom
    { toFun := fun c => ⟨ambCoeff F c, ambCoeff_mem_ambK F c⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
    ⟨ambTheta F, ambTheta_mem_ambK F⟩

lemma ambKPolyHom_apply (p : Polynomial F) :
    (ambKPolyHom F p : Ambient F) = p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
  have h : (ambK F).subtype.comp (ambKPolyHom F)
      = Polynomial.eval₂RingHom (algebraMap F (Ambient F)) (ambTheta F) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply]
      rw [ambKPolyHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · simp only [RingHom.comp_apply]
      rw [ambKPolyHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  exact RingHom.congr_fun h p

lemma ambKPolyHom_injective : Function.Injective (ambKPolyHom F) := by
  intro p q hpq
  have h : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F)
      = q.eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
    have h1 := congrArg (fun x : ↥(ambK F) => (x : Ambient F)) hpq
    simpa [ambKPolyHom_apply] using h1
  have h2 : (p - q).eval₂ (algebraMap F (Ambient F)) (ambTheta F) = 0 := by
    rw [Polynomial.eval₂_sub, h, sub_self]
  exact sub_eq_zero.mp (ambTheta_transcendental F (p - q) h2)

/-- The field homomorphism `RatFunc F →+* ↥(ambK F)` induced by `X ↦ θ`. -/
noncomputable def ambKHom : RatFunc F →+* ↥(ambK F) :=
  IsFractionRing.lift (ambKPolyHom_injective F)

lemma ambKHom_algebraMap (p : Polynomial F) :
    ambKHom F (algebraMap (Polynomial F) (RatFunc F) p) = ambKPolyHom F p :=
  IsFractionRing.lift_algebraMap (ambKPolyHom_injective F) p

lemma ambKHom_C (c : F) :
    ambKHom F (algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c))
      = ⟨ambCoeff F c, ambCoeff_mem_ambK F c⟩ := by
  rw [ambKHom_algebraMap, ambKPolyHom, Polynomial.coe_eval₂RingHom]
  simp

lemma ambKHom_X : (ambKHom F RatFunc.X : Ambient F) = ambTheta F := by
  have h : ambKHom F RatFunc.X = ambKPolyHom F Polynomial.X := by
    rw [show RatFunc.X = algebraMap (Polynomial F) (RatFunc F) Polynomial.X from rfl,
      ambKHom_algebraMap]
  rw [h, ambKPolyHom_apply]
  simp only [Polynomial.eval₂_X]

/-- **Every element of `ambK F = F_q(θ)` is a rational function in `θ`**: the map `RatFunc F →
↥(ambK F)` is surjective. -/
theorem ambKHom_surjective : Function.Surjective (ambKHom F) := by
  intro x
  have key : ∀ y (hy : y ∈ ambK F), ∃ z : RatFunc F, (ambKHom F z : Ambient F) = y := by
    intro y hy
    refine Subfield.closure_induction
      (p := fun y _ => ∃ z : RatFunc F, (ambKHom F z : Ambient F) = y)
      ?_ ?_ ?_ ?_ ?_ ?_ hy
    · rintro w (⟨c, rfl⟩ | rfl)
      · refine ⟨algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c), ?_⟩
        rw [ambKHom_C]
      · exact ⟨RatFunc.X, ambKHom_X F⟩
    · refine ⟨1, ?_⟩
      rw [map_one]
      push_cast
      rfl
    · rintro a b _ _ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
      refine ⟨z₁ + z₂, ?_⟩
      rw [map_add]
      push_cast
      rw [hz₁, hz₂]
    · rintro a _ ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [map_neg]
      push_cast
      rw [hz]
    · rintro a _ ⟨z, hz⟩
      by_cases hz0 : z = 0
      · subst hz0
        refine ⟨0, ?_⟩
        have ha : a = 0 := by rw [← hz, map_zero]; rfl
        rw [ha, map_zero, inv_zero]
        rfl
      · refine ⟨z⁻¹, ?_⟩
        rw [map_inv₀]
        push_cast
        rw [hz]
    · rintro a b _ _ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
      refine ⟨z₁ * z₂, ?_⟩
      rw [map_mul]
      push_cast
      rw [hz₁, hz₂]
  obtain ⟨z, hz⟩ := key (x : Ambient F) x.2
  exact ⟨z, Subtype.ext hz⟩

/-- **`ambK F = F_q(θ)` is a copy of the rational function field**: `RatFunc F ≃+* ↥(ambK F)`
with `X ↦ θ`. -/
noncomputable def ambKEquiv : RatFunc F ≃+* ↥(ambK F) :=
  RingEquiv.ofBijective (ambKHom F)
    ⟨RingHom.injective (ambKHom F), ambKHom_surjective F⟩

@[simp] lemma ambKEquiv_apply (x : RatFunc F) : ambKEquiv F x = ambKHom F x := rfl

lemma ambKEquiv_X : (ambKEquiv F RatFunc.X : Ambient F) = ambTheta F := by
  rw [ambKEquiv_apply]
  exact ambKHom_X F

end ZagierHoffmanPositiveChar
