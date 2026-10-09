import Mathlib
import Submission.Work.SSGRoute.LocalKummerAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

set_option linter.unusedVariables false

/-- **The level-change coefficient maps for the Kummer data.**  For a tower `k ⊆ K ⊆ L` of number
fields (`L/k` finite Galois), places `w' ∣ w`, the restriction `g` of decomposition groups and the
canonical local units map `ι : K_wˣ → L_{w'}ˣ`, there are morphisms of `D_{w'}`-representations
* `iP : (K_wˣ)^p → (L_{w'}ˣ)^p`, induced by `ι`, commuting with both the inclusion into the units and
  the `p`-th power map, and
* `iQ : K_wˣ ⧸ (K_wˣ)^p → L_{w'}ˣ ⧸ (L_{w'}ˣ)^p`, likewise, commuting with the quotient maps and
  given on the class of `a` by the class of `ι a`.

Definitions (`localPthSub`, `localPthRep`, `localPthIncl`, `localPthMap`, `localKummerQuot`,
`localKummerQuotMap`) live in `Submission.Work.SSGRoute.LocalKummerAux`.  Hints: elements of
`↥(localPthRep k K w p)` are elements of the subtype `↥(localPthSub k K w p)` and should be handled
with the `show ↥(localPthSub k K w p) from x` idiom (see
`kummer_level_defs.pthMapX_surjective` and `localKummerSES1_shortExact`); the quotient map can be
built from `Submodule.mapQ` (lemmas `Submodule.mapQ_mkQ`, `Submodule.mapQ_apply`); beware of the
`ULift.module` / `Rep.hV2` instance diamonds — the workspace pattern is `letI := X.hV2` (cf.
`local_duality_ext.localUnits_hom_ext`), and `set_option backward.isDefEq.respectTransparency false`
is used elsewhere for these. -/
theorem exists_localKummerLevelMaps (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] (p : ℕ) (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (g : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (ι : Rep.res g (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w') :
    (∃ iP : Rep.res g (localPthRep k K w p) ⟶ localPthRep k L w' p,
        Rep.resMap g (localPthIncl k K w p) ≫ ι = iP ≫ localPthIncl k L w' p ∧
        Rep.resMap g (localPthMap k K w p) ≫ iP = ι ≫ localPthMap k L w' p) ∧
      (∃ iQ : Rep.res g (localKummerQuot k K w p) ⟶ localKummerQuot k L w' p,
        Rep.resMap g (localKummerQuotMap k K w p) ≫ iQ = ι ≫ localKummerQuotMap k L w' p ∧
        ∀ a : localUnitsK (k := k) w,
          iQ.hom (Submodule.mkQ (localPthSub k K w p) a)
            = Submodule.mkQ (localPthSub k L w' p) (ι.hom a)) := by
  classical
  -- `ι` carries `p`-th powers to `p`-th powers.
  have hmemP : ∀ x : localUnitsK (k := k) w,
      x ∈ localPthSub k K w p → ι.hom x ∈ localPthSub k L w' p := by
    intro x hx
    obtain ⟨u, rfl⟩ := (mem_localPthSub_iff k K w p x).mp hx
    exact (mem_localPthSub_iff k L w' p _).mpr
      ⟨ι.hom u, (map_nsmul ι.hom.toLinearMap p u).symm⟩
  -- ## The level map `iP` on the `p`-th power submodules
  have hP : ∃ iP : Rep.res g (localPthRep k K w p) ⟶ localPthRep k L w' p,
      Rep.resMap g (localPthIncl k K w p) ≫ ι = iP ≫ localPthIncl k L w' p ∧
      Rep.resMap g (localPthMap k K w p) ≫ iP = ι ≫ localPthMap k L w' p := by
    let F : ↥(localPthSub k K w p) →ₗ[Coeff] ↥(localPthSub k L w' p) :=
      { toFun := fun x => ⟨ι.hom (x : localUnitsK (k := k) w), hmemP _ x.2⟩
        map_add' := fun x y => Subtype.ext (by
          show ι.hom (((x : ↥(localPthSub k K w p)) : localUnitsK (k := k) w)
              + ((y : ↥(localPthSub k K w p)) : localUnitsK (k := k) w))
            = ι.hom (x : localUnitsK (k := k) w) + ι.hom (y : localUnitsK (k := k) w)
          rw [map_add])
        map_smul' := fun c x => Subtype.ext (by
          show ι.hom (c • (x : localUnitsK (k := k) w))
            = c • ι.hom (x : localUnitsK (k := k) w)
          rw [map_smul]) }
    let iP : Rep.res g (localPthRep k K w p) ⟶ localPthRep k L w' p :=
      Rep.ofHom { toLinearMap := F
                  isIntertwining' := fun γ => by
                    apply LinearMap.ext
                    intro x
                    apply Subtype.ext
                    show ι.hom ((localUnitsK (k := k) w).ρ (g γ) (Subtype.val x))
                      = (localUnitsK (k := k) w').ρ γ (ι.hom (Subtype.val x))
                    exact Representation.IntertwiningMap.isIntertwining _ _
                      ι.hom γ (Subtype.val x) }
    have hiP : ∀ x : ↥(localPthRep k K w p), iP.hom x = F x := fun x => rfl
    have hiP' : ∀ x : ↥(localPthRep k K w p),
        Subtype.val (iP.hom x) = ι.hom (Subtype.val x) := fun x => rfl
    refine ⟨iP, ?_, ?_⟩
    · apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      show ι.hom ((Rep.resMap g (localPthIncl k K w p)).hom x)
        = (localPthIncl k L w' p).hom (iP.hom x)
      rw [Rep.resMap_hom_apply]
      rw [show (localPthIncl k K w p).hom x = Subtype.val x
            from localPthIncl_apply k K w p x]
      rw [show (localPthIncl k L w' p).hom (iP.hom x) = Subtype.val (iP.hom x)
            from localPthIncl_apply k L w' p (iP.hom x)]
      exact (hiP' x).symm
    · apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      show iP.hom ((Rep.resMap g (localPthMap k K w p)).hom a)
        = (localPthMap k L w' p).hom (ι.hom a)
      rw [Rep.resMap_hom_apply, hiP]
      rw [show (localPthMap k K w p).hom a
            = ⟨(p:ℕ) • a, LinearMap.mem_range_self _ a⟩ from localPthMap_apply k K w p a]
      rw [show (localPthMap k L w' p).hom (ι.hom a)
            = ⟨(p:ℕ) • (ι.hom a), LinearMap.mem_range_self _ (ι.hom a)⟩
            from localPthMap_apply k L w' p (ι.hom a)]
      apply Subtype.ext
      show ι.hom ((p:ℕ) • a) = (p:ℕ) • ι.hom a
      exact map_nsmul ι.hom.toLinearMap p a
  -- ## The level map `iQ` on the Kummer quotients
  have hQ : ∃ iQ : Rep.res g (localKummerQuot k K w p) ⟶ localKummerQuot k L w' p,
      Rep.resMap g (localKummerQuotMap k K w p) ≫ iQ = ι ≫ localKummerQuotMap k L w' p ∧
      ∀ a : localUnitsK (k := k) w,
        iQ.hom (Submodule.mkQ (localPthSub k K w p) a)
          = Submodule.mkQ (localPthSub k L w' p) (ι.hom a) := by
    have hker : localPthSub k K w p ≤ (localPthSub k L w' p).comap ι.hom.toLinearMap :=
      fun x hx => hmemP x hx
    let Q : ↥(localUnitsK (k := k) w) ⧸ localPthSub k K w p →ₗ[Coeff]
        ↥(localUnitsK (k := k) w') ⧸ localPthSub k L w' p :=
      Submodule.mapQ (localPthSub k K w p) (localPthSub k L w' p) ι.hom.toLinearMap hker
    have hQapply : ∀ a : ↥(localUnitsK (k := k) w),
        Q ((localPthSub k K w p).mkQ a) = (localPthSub k L w' p).mkQ (ι.hom a) := by
      intro a
      show (Submodule.mapQ (localPthSub k K w p) (localPthSub k L w' p) ι.hom.toLinearMap hker
          (Submodule.Quotient.mk a)) = Submodule.Quotient.mk (ι.hom a)
      exact Submodule.mapQ_apply _ _ _ a
    have hQint : ∀ (γ : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w'))
        (x : ↥(localUnitsK (k := k) w) ⧸ localPthSub k K w p),
        Q (((localKummerQuot k K w p).ρ (g γ)) x)
          = ((localKummerQuot k L w' p).ρ γ) (Q x) := by
      intro γ x
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (localPthSub k K w p) x
      show Q ((g γ) • ((localPthSub k K w p).mkQ a)) = γ • (Q ((localPthSub k K w p).mkQ a))
      rw [hQapply, localKummerQuot_smul_mk k L w' p γ (ι.hom a),
        localKummerQuot_smul_mk k K w p (g γ) a, hQapply]
      exact congrArg (Submodule.mkQ (localPthSub k L w' p))
        (Representation.IntertwiningMap.isIntertwining _ _ ι.hom γ a)
    let iQ : Rep.res g (localKummerQuot k K w p) ⟶ localKummerQuot k L w' p :=
      Rep.ofHom { toLinearMap := Q
                  isIntertwining' := fun γ => by
                    apply LinearMap.ext
                    intro x
                    exact hQint γ x }
    have hiQ : ∀ x, iQ.hom x = Q x := fun x => rfl
    refine ⟨iQ, ?_, ?_⟩
    · apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      show iQ.hom ((Rep.resMap g (localKummerQuotMap k K w p)).hom a)
        = (localKummerQuotMap k L w' p).hom (ι.hom a)
      rw [Rep.resMap_hom_apply, hiQ]
      rw [show (localKummerQuotMap k K w p).hom a = (localPthSub k K w p).mkQ a from rfl]
      rw [hQapply]
      rfl
    · intro a
      show Q ((localPthSub k K w p).mkQ a) = (localPthSub k L w' p).mkQ (ι.hom a)
      exact hQapply a
  exact ⟨hP, hQ⟩

end Work.SSGRoute
