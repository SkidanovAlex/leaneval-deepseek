import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite Opposite

/-- In `LightProfinite`, a finite effective epimorphic family is jointly surjective on points.

Proof: the family is effective epimorphic iff `Sigma.desc π : ∐ Y ⟶ U` is an epimorphism
(`effectiveEpi_desc_iff_effectiveEpiFamily`, using `FinitaryPreExtensive LightProfinite`), and in
`LightProfinite` epimorphisms are surjective (`LightProfinite.effectiveEpi_iff_surjective`).  The
remaining step is to replace the abstract coproduct `∐ Y` by the explicit finite coproduct
`CompHausLike.finiteCoproduct Y = ↧(Σ a, Y a)`, along the canonical isomorphism `e`. -/
theorem lightProfinite_jointly_surjective_of_effectiveEpiFamily {α : Type} [Finite α]
    {U : LightProfinite.{0}} (Y : α → LightProfinite.{0}) (π : (a : α) → Y a ⟶ U)
    (hπ : EffectiveEpiFamily Y π) :
    ∀ u : ↥U, ∃ a : α, ∃ c : ↥(Y a), π a c = u := by
  intro u
  have hEff : EffectiveEpi (Sigma.desc π) :=
    (effectiveEpi_desc_iff_effectiveEpiFamily Y π).mpr hπ
  obtain ⟨x, hx⟩ := (LightProfinite.effectiveEpi_iff_surjective (Sigma.desc π)).mp hEff u
  let e : (∐ Y) ≅ CompHausLike.finiteCoproduct Y :=
    (colimit.isColimit (Discrete.functor Y)).coconePointUniqueUpToIso
      (CompHausLike.finiteCoproduct.isColimit Y)
  obtain ⟨a, c, hc⟩ := CompHausLike.finiteCoproduct.ι_jointly_surjective Y (e.hom x)
  refine ⟨a, c, ?_⟩
  -- `Sigma.desc π` factors through the explicit coproduct via `e`.
  have hcomp : e.hom ≫ CompHausLike.finiteCoproduct.desc Y π = Sigma.desc π := by
    apply colimit.hom_ext
    intro j
    obtain ⟨b⟩ := j
    simp [e]
  have h := hx
  rw [← hcomp] at h
  rw [ConcreteCategory.comp_apply] at h
  rw [hc] at h
  rw [CompHausLike.finiteCoproduct.ι_desc_apply] at h
  exact h

theorem cover_of_toSheafify_preimage
    (P : CategoryTheory.Functor (Opposite (LightProfinite.{0})) (ModuleCat.{0} ℤ))
    (U : LightProfinite.{0})
    (y : ↥((CategoryTheory.sheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P).obj
        (Opposite.op U))) :
    ∃ (m : ℕ) (C : Fin m → LightProfinite.{0}) (ι : ∀ i, C i ⟶ U),
      (∀ u : ↥U, ∃ i, ∃ c : ↥(C i), ι i c = u) ∧
      ∀ i, ∃ t : ↥(P.obj (Opposite.op (C i))),
        (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P).app
            (Opposite.op (C i)) t
          = (CategoryTheory.sheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P).map
              (ι i).op y := by
  -- The sieve of those `ι : C ⟶ U` along which `y` is locally in the image of `toSheafify` is
  -- covering, because `toSheafify` is locally surjective.
  have hmem : Presheaf.imageSieve
      (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P) y ∈
      (coherentTopology LightProfinite.{0}) U :=
    Presheaf.imageSieve_mem (CategoryTheory.coherentTopology LightProfinite.{0})
      (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P) y
  -- A covering sieve of the coherent topology contains a finite effective epimorphic family.
  obtain ⟨α, hfin, Y, π, hπ, hmem'⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily
      (S := Presheaf.imageSieve
        (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P) y)).mp
      hmem
  -- Each member of the family comes with a preimage of the restriction of `y`.
  have hpoint : ∀ a : α, ∃ t : ↥(P.obj (Opposite.op (Y a))),
      (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P).app
          (Opposite.op (Y a)) t
        = (CategoryTheory.sheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P).map
            (π a).op y := fun a =>
    ⟨Presheaf.localPreimage
        (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P)
        y (π a) (hmem' a),
      Presheaf.app_localPreimage
        (CategoryTheory.toSheafify (CategoryTheory.coherentTopology LightProfinite.{0}) P)
        y (π a) (hmem' a)⟩
  -- Reindex the finite type `α` by `Fin m`.
  obtain ⟨m, ⟨σ : α ≃ Fin m⟩⟩ := @Finite.exists_equiv_fin α hfin
  refine ⟨m, fun i => Y (σ.symm i), fun i => π (σ.symm i), ?_, fun i => hpoint (σ.symm i)⟩
  intro u
  obtain ⟨a, c, hc⟩ := lightProfinite_jointly_surjective_of_effectiveEpiFamily Y π hπ u
  refine ⟨σ a, ?_⟩
  show ∃ c' : ↥(Y (σ.symm (σ a))), π (σ.symm (σ a)) c' = u
  rw [Equiv.symm_apply_apply]
  exact ⟨c, hc⟩

end Work.ANALYTIC
