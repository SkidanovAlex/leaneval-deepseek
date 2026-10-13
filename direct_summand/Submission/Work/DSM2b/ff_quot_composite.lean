import Mathlib

set_option linter.style.haveILetI false

namespace Work.DSM2b

universe u

open TensorProduct

/-- Base change of faithful flatness to a quotient by a principal ideal:
if `B` is faithfully flat over `A` then `B ⧸ πB` is faithfully flat over `A ⧸ (π)`. -/
theorem ff_base_quot_canon {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (π : A)
    [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat (A ⧸ Ideal.span {π}) (B ⧸ (Ideal.span {π}).map (algebraMap A B)) := by
  have hbc : Module.FaithfullyFlat (A ⧸ Ideal.span {π}) ((A ⧸ Ideal.span {π}) ⊗[A] B) :=
    inferInstance
  have eA : ((A ⧸ Ideal.span {π}) ⊗[A] B) ≃ₗ[A]
      (B ⧸ (Ideal.span {π}).map (algebraMap A B)) :=
    (TensorProduct.quotTensorEquivQuotSMul B (Ideal.span {π})).trans
      ((Submodule.quotEquivOfEq _ _
        (Ideal.smul_top_eq_map (Ideal.span {π}))).trans
        (Submodule.Quotient.restrictScalarsEquiv A ((Ideal.span {π}).map (algebraMap A B))))
  have eR : ((A ⧸ Ideal.span {π}) ⊗[A] B) ≃ₗ[A ⧸ Ideal.span {π}]
      (B ⧸ (Ideal.span {π}).map (algebraMap A B)) :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective eA
  exact Module.FaithfullyFlat.of_linearEquiv _ _ eR.symm

/-- Faithful flatness is compatible with forming quotients by a principal ideal, for a tower of
rings `A → B₁ → B₂`: if `B₁` is faithfully flat over `A` and `B₂ ⧸ πB₂` is faithfully flat over
`B₁ ⧸ πB₁`, then `B₂ ⧸ πB₂` is faithfully flat over `A ⧸ πA`. -/
theorem ff_quot_composite {A B₁ B₂ : Type u} [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra B₁ B₂] [Algebra A B₂] [IsScalarTower A B₁ B₂] (π : A)
    [Module.FaithfullyFlat A B₁]
    (h : Module.FaithfullyFlat (B₁ ⧸ Ideal.span {(algebraMap A B₁ π)})
      (B₂ ⧸ (Ideal.span {(algebraMap A B₁ π)}).map (algebraMap B₁ B₂))) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {π}) (B₂ ⧸ (Ideal.span {π}).map (algebraMap A B₂)) := by
  -- the `A ⧸ (π)`-algebra structure on `B₁ ⧸ (algebraMap A B₁ π)`
  letI algRS : Algebra (A ⧸ Ideal.span {π}) (B₁ ⧸ Ideal.span {algebraMap A B₁ π}) :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := Ideal.span {π})
      (P := Ideal.span {algebraMap A B₁ π}) (fun x hx => by
        rw [Ideal.mem_comap]
        rw [Ideal.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        rw [map_mul]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))
  -- faithful flatness of `B₁ ⧸ πB₁` over `A ⧸ (π)`
  have h₁ : Module.FaithfullyFlat (A ⧸ Ideal.span {π}) (B₁ ⧸ Ideal.span {algebraMap A B₁ π}) := by
    have hbase := ff_base_quot_canon (A := A) (B := B₁) π
    letI := hbase
    have hJb : Ideal.span {algebraMap A B₁ π} = (Ideal.span {π}).map (algebraMap A B₁) := by
      rw [Ideal.map_span, Set.image_singleton]
    have hf : ∀ x, (Ideal.quotEquivOfEq hJb)
          (algebraMap (A ⧸ Ideal.span {π}) (B₁ ⧸ Ideal.span {algebraMap A B₁ π}) x)
        = algebraMap (A ⧸ Ideal.span {π}) (B₁ ⧸ (Ideal.span {π}).map (algebraMap A B₁)) x := by
      intro x
      refine Quotient.inductionOn x (fun a => ?_)
      have hL : algebraMap (A ⧸ Ideal.span {π}) (B₁ ⧸ Ideal.span {algebraMap A B₁ π})
          (⟦a⟧ : A ⧸ Ideal.span {π})
          = Ideal.Quotient.mk (Ideal.span {algebraMap A B₁ π}) (algebraMap A B₁ a) := rfl
      have hR : algebraMap (A ⧸ Ideal.span {π}) (B₁ ⧸ (Ideal.span {π}).map (algebraMap A B₁))
          (⟦a⟧ : A ⧸ Ideal.span {π})
          = Ideal.Quotient.mk ((Ideal.span {π}).map (algebraMap A B₁)) (algebraMap A B₁ a) := rfl
      rw [hL, hR, Ideal.quotEquivOfEq_mk]
    have heq : (B₁ ⧸ Ideal.span {algebraMap A B₁ π}) ≃ₗ[A ⧸ Ideal.span {π}]
        (B₁ ⧸ (Ideal.span {π}).map (algebraMap A B₁)) :=
      (AlgEquiv.ofRingEquiv (R := A ⧸ Ideal.span {π}) (f := Ideal.quotEquivOfEq hJb) hf).toLinearEquiv
    exact Module.FaithfullyFlat.of_linearEquiv _ _ heq
  -- the `A ⧸ (π)`-algebra structure on `B₂ ⧸ (algebraMap A B₁ π)B₂`
  letI algRM : Algebra (A ⧸ Ideal.span {π})
      (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := Ideal.span {π})
      (P := (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) (fun x hx => by
        rw [Ideal.mem_comap]
        rw [Ideal.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        rw [map_mul, IsScalarTower.algebraMap_apply A B₁ B₂]
        exact Ideal.mul_mem_right _ _
          (Ideal.mem_map_of_mem (algebraMap B₁ B₂) (Ideal.subset_span (Set.mem_singleton _))))
  -- the resulting scalar tower
  letI towerRSM : IsScalarTower (A ⧸ Ideal.span {π})
      (B₁ ⧸ Ideal.span {algebraMap A B₁ π})
      (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      refine Quotient.inductionOn x (fun a => ?_)
      have hL : algebraMap (A ⧸ Ideal.span {π})
            (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
            (⟦a⟧ : A ⧸ Ideal.span {π})
          = Ideal.Quotient.mk ((Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
              (algebraMap A B₂ a) := rfl
      have hM : algebraMap (A ⧸ Ideal.span {π}) (B₁ ⧸ Ideal.span {algebraMap A B₁ π})
            (⟦a⟧ : A ⧸ Ideal.span {π})
          = Ideal.Quotient.mk (Ideal.span {algebraMap A B₁ π}) (algebraMap A B₁ a) := rfl
      have hR : algebraMap (B₁ ⧸ Ideal.span {algebraMap A B₁ π})
            (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
            (Ideal.Quotient.mk (Ideal.span {algebraMap A B₁ π}) (algebraMap A B₁ a))
          = Ideal.Quotient.mk ((Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
              (algebraMap B₁ B₂ (algebraMap A B₁ a)) := rfl
      rw [hL, hM, hR, IsScalarTower.algebraMap_apply A B₁ B₂])
  letI h₁i : Module.FaithfullyFlat (A ⧸ Ideal.span {π})
      (B₁ ⧸ Ideal.span {algebraMap A B₁ π}) := h₁
  letI hi : Module.FaithfullyFlat (B₁ ⧸ Ideal.span {algebraMap A B₁ π})
      (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) := h
  have hc : Module.FaithfullyFlat (A ⧸ Ideal.span {π})
      (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) :=
    Module.FaithfullyFlat.trans (A ⧸ Ideal.span {π}) (B₁ ⧸ Ideal.span {algebraMap A B₁ π})
      (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
  letI hci : Module.FaithfullyFlat (A ⧸ Ideal.span {π})
      (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) := hc
  -- identification of the two ideals in `B₂`
  have hJ : (Ideal.span {π}).map (algebraMap A B₂) =
      (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply A B₁ B₂]
  have hf2 : ∀ x, (Ideal.quotEquivOfEq hJ)
        (algebraMap (A ⧸ Ideal.span {π}) (B₂ ⧸ (Ideal.span {π}).map (algebraMap A B₂)) x)
      = algebraMap (A ⧸ Ideal.span {π})
          (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂)) x := by
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    have hL : algebraMap (A ⧸ Ideal.span {π}) (B₂ ⧸ (Ideal.span {π}).map (algebraMap A B₂))
        (⟦a⟧ : A ⧸ Ideal.span {π})
        = Ideal.Quotient.mk ((Ideal.span {π}).map (algebraMap A B₂)) (algebraMap A B₂ a) := rfl
    have hR : algebraMap (A ⧸ Ideal.span {π})
          (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
          (⟦a⟧ : A ⧸ Ideal.span {π})
        = Ideal.Quotient.mk ((Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
            (algebraMap A B₂ a) := rfl
    rw [hL, hR, Ideal.quotEquivOfEq_mk]
  exact Module.FaithfullyFlat.of_linearEquiv (A ⧸ Ideal.span {π})
    (B₂ ⧸ (Ideal.span {algebraMap A B₁ π}).map (algebraMap B₁ B₂))
    (AlgEquiv.ofRingEquiv (R := A ⧸ Ideal.span {π}) (f := Ideal.quotEquivOfEq hJ) hf2).toLinearEquiv

end Work.DSM2b
