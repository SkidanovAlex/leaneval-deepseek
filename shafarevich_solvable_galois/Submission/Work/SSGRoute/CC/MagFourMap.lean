import Submission.Work.SSGRoute.CC.MagFourDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the truncated Magnus layers under a re-labelling of the generators

This is a self-contained copy of `Submission/Work/SSGRoute/magLT_mapDomain.lean` (which lives in a
different, incompatible import chain) together with the two consequences needed by the `(4,4)`
graded step: the mod-`2` degree-`4` and degree-`2` components `mag4`, `mag2` of
`Submission/Work/SSGRoute/magFourDefs.lean` commute with the algebra map `sigA X σ` induced by an
involution `σ` of the letters.
-/

open scoped commutatorElement

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

namespace magFourNat

variable {X : Type}

lemma fil_map_le {X : Type*} (σ : X ≃ X) (N : ℕ) :
    (Work.SSGRoute.prop5.fil X N).map
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))) ≤
      Work.SSGRoute.prop5.fil X N := by
  rw [Work.SSGRoute.prop5.fil, Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  refine Ideal.subset_span ⟨FreeMonoid.map σ w, ?_, rfl⟩
  simp only [FreeMonoid.length, FreeMonoid.toList_map, List.length_map]
  exact hw

/-- The endomorphism of the truncated free associative algebra `FreeAssoc X ⧸ fil X N`
induced by a bijection `σ` of the generators. -/
noncomputable def qmap {X : Type*} (σ : X ≃ X) (N : ℕ) :
    (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) →+*
      (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) :=
  Ideal.Quotient.lift (Work.SSGRoute.prop5.fil X N)
    ((Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N)).comp
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))))
    (fun a ha => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (fil_map_le σ N (Ideal.mem_map_of_mem
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))) ha)))

/-- `qmap` computes on representatives. -/
lemma qmap_mk {X : Type*} (σ : X ≃ X) (N : ℕ) (y : Work.SSGRoute.prop5.FreeAssoc X) :
    qmap σ N (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N) y)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N)
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) y) := by
  rw [qmap, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- `qmap` sends the Magnus image of a generator `of x` to the Magnus image of `of (σ x)`. -/
lemma qmap_magnus_of {X : Type*} (σ : X ≃ X) (N : ℕ) (x : X) :
    qmap σ N
        ((magnus X N (FreeGroup.of x) :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)
      = ((magnus X N (FreeGroup.of (σ x)) :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) := by
  rw [magnus_of X N x, magnus_of X N (σ x), map_add, map_one, qmap_mk,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, FreeMonoid.map_of]

/-- Naturality of the Magnus map: re-labelling the generators commutes with the Magnus
embedding (modulo the length filtration). -/
lemma magnus_mapDomain {X : Type*} (σ : X ≃ X) (N : ℕ) (z : FreeGroup X) :
    Units.map (qmap σ N) (magnus X N z) = magnus X N (FreeGroup.freeGroupCongr σ z) := by
  have hhom : (Units.map (qmap σ N)).comp (magnus X N)
      = (magnus X N).comp (FreeGroup.freeGroupCongr σ).toMonoidHom := by
    apply (FreeGroup.lift).symm.injective
    ext x
    simp only [FreeGroup.lift_symm_apply, MonoidHom.comp_apply, Function.comp_apply]
    rw [show (FreeGroup.freeGroupCongr σ).toMonoidHom (FreeGroup.of x)
          = FreeGroup.freeGroupCongr σ (FreeGroup.of x) from rfl]
    rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of, Units.coe_map]
    change qmap σ N ((magnus X N (FreeGroup.of x) :
        (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)
      = ((magnus X N (FreeGroup.of (σ x)) :
          (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)
    exact qmap_magnus_of σ N x
  exact DFunLike.congr_fun hhom z

theorem magLT_mapDomain {X : Type*} (σ : X ≃ X) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup X)
    (a : Work.SSGRoute.prop5.FreeAssoc X)
    (ha : Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)) a = Work.SSGRoute.prop5.magLT X j z) :
    Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1))
        (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a)
      = Work.SSGRoute.prop5.magLT X j (FreeGroup.freeGroupCongr σ z) := by
  have hmk : qmap σ (j + 1) (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)) a)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1))
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a) :=
    qmap_mk σ (j + 1) a
  rw [← hmk, ha]
  have key := magnus_mapDomain σ (j + 1) z
  have hcoe : qmap σ (j + 1)
        ((magnus X (j + 1) z :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))
      = ((Units.map (qmap σ (j + 1)) (magnus X (j + 1) z) :
            (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
          Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) := by
    rw [Units.coe_map]
    rfl
  rw [Work.SSGRoute.prop5.magLT, Work.SSGRoute.prop5.magLT, map_sub, map_one, hcoe, key]
/-! ## Consequences for the mod-`2` layers `mag4` and `mag2` -/

/-- `FreeMonoid.map` preserves word length. -/
theorem freeMonoid_length_map {X Y : Type} (f : X → Y) (w : FreeMonoid X) :
    (FreeMonoid.map f w).length = w.length := by
  simp only [FreeMonoid.length, FreeMonoid.toList_map, List.length_map]

/-- `degPart j` commutes with the re-labelling of the generators. -/
theorem degPart_mapDomain (σ : X ≃ X) (j : ℕ) (b : FreeAssoc X) :
    degPart (X := X) j (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) b)
      = MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))
          (degPart (X := X) j b) := by
  refine MonoidAlgebra.induction_linear (motive := fun b =>
    degPart (X := X) j (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) b)
      = MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X))
          (degPart (X := X) j b)) b ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro m r
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      degPart_single, degPart_single, freeMonoid_length_map]
    by_cases h : m.length = j
    · rw [if_pos h, if_pos h, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single]
    · rw [if_neg h, if_neg h, map_zero]

/-- Reduction mod `2` commutes with the re-labelling of the generators. -/
theorem red2_mapDomain (σ : X ≃ X) (b : FreeAssoc X) :
    red2 X (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) b)
      = MonoidAlgebra.mapDomainRingHom (ZMod 2) (FreeMonoid.map (σ : X → X)) (red2 X b) := by
  have h := MonoidAlgebra.mapRingHom_comp_mapDomainRingHom (Int.castRingHom (ZMod 2))
    (FreeMonoid.map (σ : X → X))
  exact DFunLike.congr_fun h b

end magFourNat

/-- **`mag4` is natural under a re-labelling `σ` of the letters.** -/
theorem mag4_congr (X : Type) (σ : X ≃ X) (z : FreeGroup X) :
    mag4 X (FreeGroup.freeGroupCongr σ z) = sigA X (σ : X → X) (mag4 X z) := by
  set a : FreeAssoc X := Quotient.out (magLead 5 z) with ha
  have hha : Ideal.Quotient.mk (fil X 5) a = magLead 5 z := Ideal.Quotient.mk_out _
  have hmap : Ideal.Quotient.mk (fil X 5)
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a)
      = magLead 5 (FreeGroup.freeGroupCongr σ z) :=
    magFourNat.magLT_mapDomain σ 4 (by norm_num) z a hha
  have h2 : mag4 X (FreeGroup.freeGroupCongr σ z)
      = red2 X (degPart (X := X) 4
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a)) :=
    mag4_eq_of_mk hmap
  have h3 : mag4 X z = red2 X (degPart (X := X) 4 a) := mag4_eq_of_mk hha
  rw [h2, magFourNat.degPart_mapDomain, magFourNat.red2_mapDomain, ← h3]

/-- **`mag2` is natural under a re-labelling `σ` of the letters.** -/
theorem mag2_congr (X : Type) (σ : X ≃ X) (z : FreeGroup X) :
    mag2 X (FreeGroup.freeGroupCongr σ z) = sigA X (σ : X → X) (mag2 X z) := by
  set a : FreeAssoc X := Quotient.out (magLead 5 z) with ha
  have hha : Ideal.Quotient.mk (fil X 5) a = magLead 5 z := Ideal.Quotient.mk_out _
  have hmap : Ideal.Quotient.mk (fil X 5)
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a)
      = magLead 5 (FreeGroup.freeGroupCongr σ z) :=
    magFourNat.magLT_mapDomain σ 4 (by norm_num) z a hha
  have h2 : mag2 X (FreeGroup.freeGroupCongr σ z)
      = red2 X (degPart (X := X) 2
          (MonoidAlgebra.mapDomainRingHom ℤ (FreeMonoid.map (σ : X → X)) a)) :=
    mag2_eq_of_mk hmap
  have h3 : mag2 X z = red2 X (degPart (X := X) 2 a) := mag2_eq_of_mk hha
  rw [h2, magFourNat.degPart_mapDomain, magFourNat.red2_mapDomain, ← h3]

end Work.SSGRoute.CC
