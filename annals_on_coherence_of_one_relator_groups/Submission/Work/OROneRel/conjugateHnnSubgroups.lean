import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

theorem conjugateHnnSubgroups {H G : Type u} [Group H] [Group G] (θ : H →* G) (t : G)
    (hθ : Function.Injective θ) :
    ∃ (A B : Subgroup H) (φ : A ≃* B),
      (∀ a : H, a ∈ A ↔ t⁻¹ * θ a * t ∈ θ.range) ∧
      (∀ a : A, θ (((φ a : B) : H)) = t⁻¹ * θ ((a : H)) * t) := by
  classical
  -- The monoid endomorphism `ψ : H →* G`, `ψ a = t⁻¹ * θ a * t`.
  let ψ : H →* G :=
    { toFun := fun a => t⁻¹ * θ a * t
      map_one' := by simp
      map_mul' := fun a b => by
        show t⁻¹ * θ (a * b) * t = (t⁻¹ * θ a * t) * (t⁻¹ * θ b * t)
        rw [map_mul]; group }
  -- The preimage of `θ.range` under `ψ`; this is the claimed `A`.
  let A : Subgroup H := Subgroup.comap ψ θ.range
  -- The partial inverse of `θ`, defined on `A`.
  let g : A →* H :=
    { toFun := fun a => Function.invFun θ (ψ (a : H))
      map_one' := by
        apply hθ
        rw [Function.invFun_eq (f := θ) (b := ψ ((1 : A) : H)) ⟨1, by simp [ψ]⟩]
        simp [ψ]
      map_mul' := fun a b => by
        apply hθ
        rw [map_mul]
        rw [Function.invFun_eq (f := θ) (b := ψ ((a * b : A) : H))
              (MonoidHom.mem_range.mp (Subgroup.mem_comap.mp (a * b).2)),
            Function.invFun_eq (f := θ) (b := ψ (a : H))
              (MonoidHom.mem_range.mp (Subgroup.mem_comap.mp a.2)),
            Function.invFun_eq (f := θ) (b := ψ (b : H))
              (MonoidHom.mem_range.mp (Subgroup.mem_comap.mp b.2))]
        rw [Subgroup.coe_mul, map_mul] }
  -- Key property: on `A`, the partial inverse `g` inverts `θ` against `ψ`.
  have hg : ∀ x : A, θ (g x) = ψ (x : H) := fun x =>
    Function.invFun_eq (MonoidHom.mem_range.mp (Subgroup.mem_comap.mp x.2))
  have hinj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hθ
    have h1 : ψ (a : H) = ψ (b : H) := by rw [← hg a, ← hg b, hab]
    have h2 : t⁻¹ * θ (a : H) * t = t⁻¹ * θ (b : H) * t := h1
    have h3 := congrArg (fun z => t * z * t⁻¹) h2
    simpa [mul_assoc] using h3
  have hbij : Function.Bijective ⇑g.rangeRestrict :=
    ⟨fun x y h => hinj (Subtype.ext_iff.mp h), g.rangeRestrict_surjective⟩
  -- `B` is the range of `g`, and `φ` the isomorphism `A ≃* B`.
  let φ : A ≃* g.range := MulEquiv.ofBijective g.rangeRestrict hbij
  refine ⟨A, g.range, φ, ?_, ?_⟩
  · intro a
    rw [Subgroup.mem_comap]
    rfl
  · intro a
    have h1 : ((φ a : g.range) : H) = g a := by
      have hφ : φ a = g.rangeRestrict a :=
        MulEquiv.ofBijective_apply g.rangeRestrict hbij a
      rw [hφ]
      rfl
    rw [h1, hg a]
    rfl

end Work.OROneRel
