import Mathlib
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.Whitney.tcmModelMul_point_signed_full
import Submission.Work.Whitney.tcmRelCup_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.KeyLocal

/-!
# The model product formula in the `stdModelGen` vocabulary

`Work.ThomBordism.stdModelGen n` is the determinate generator of `H^n(ℝⁿ, ℝⁿ∖0)`
(`Submission/Work/ThomBordism/coorientationRef.lean`), namely the image of the explicit model class
`Work.Thom.Mpun n PUnit` under the identification `ℝⁿ ≅ PUnit × ℝⁿ`.

The main theorem of this file is the *cross-product rule* for these generators, in the form in which
the `KeyLocal` chapter needs it: for *arbitrary* continuous maps `a : X → ℝ⁸` and `b : X → ℝ^k`, the
canonical relative–relative cup (`Work.Whitney.tcmRelCup`) of the pullbacks of `stdModelGen 8` and
`stdModelGen k` along `a` and `b` is the pullback of `stdModelGen (8+k)` along the Whitney-sum map
`x ↦ tcmSumLin 8 k (a x, b x)`.

The proof pulls the *one-point-base* (hence subsingleton-base) model product formula
`Work.Whitney.tcmModelMul_point_signed_full PUnit 8 k`

  `tcmRelCup (pr₁^* Mpun 8) (pr₂^* Mpun k) = (-1)^{8k} • tcmF^* (Mpun (8+k))`

back along the canonical map `X → PUnit × (ℝ⁸ × ℝ^k)`, `x ↦ (·, (a x, b x))`:

* the pullback of `pr₁^* Mpun 8` is `a^*(stdModelGen 8)` (because `stdModelGen` *is* the pullback of
  `Mpun` along `Rⁿ → PUnit × Rⁿ`, and `pr₁ ∘ toModel = psiUnit 8 ∘ a`);
* likewise for the second factor with `pr₂`;
* the pullback of `tcmF^* Mpun (8+k)` is `(tcmSumLin 8 k ∘ (a,b))^*(stdModelGen (8+k))`
  (because `tcmF ∘ toModel = psiUnit (8+k) ∘ tcmSumLin`);
* the Koszul sign is `(-1)^{8k} = 1`.

Everything else is the naturality of `Work.Whitney.tcmRelCup` under a map of pairs
(`Work.Whitney.tcmRelCup_natural`) and functoriality of `Work.Thom.relCohMap`.
-/

/-- The inclusion `ℝⁿ → PUnit × ℝⁿ`, `v ↦ (unit, v)`.  This is exactly the map whose pullback of the
model class `Work.Thom.Mpun n PUnit` is `Work.ThomBordism.stdModelGen n`. -/
def psiUnit (n : ℕ) : C(EuclideanSpace ℝ (Fin n), PUnit × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun v => (PUnit.unit, v), continuous_const.prodMk continuous_id⟩

/-- **`stdModelGen` is the pullback of the model class along `psiUnit`**: this is the definition of
`Work.ThomBordism.stdModelGen`, with the canonical map `ℝⁿ → PUnit × ℝⁿ` named `psiUnit`. -/
lemma stdModelGen_eq_pullback (k : ℕ) :
    Work.ThomBordism.stdModelGen k
      = (Work.Thom.relCohMap (psiUnit k) ({0}ᶜ) (Work.Thom.Punct PUnit k)
          (fun v hv => hv) ℤ k).hom (Work.Thom.Mpun k PUnit) := by
  unfold Work.ThomBordism.stdModelGen psiUnit
  rfl

/-- The map `x ↦ (unit, (a x, b x))` from the base `X` into the model total space
`PUnit × (ℝ⁸ × ℝ^k)` of the one-point-base product formula. -/
def toModelMap {X : Type} [TopologicalSpace X] {k : ℕ}
    (a : C(X, EuclideanSpace ℝ (Fin 8))) (b : C(X, EuclideanSpace ℝ (Fin k))) :
    C(X, PUnit × (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin k))) :=
  ⟨fun x => (PUnit.unit, (a x, b x)), continuous_const.prodMk (a.continuous.prodMk b.continuous)⟩

/-- The Whitney-sum map `x ↦ tcmSumLin 8 k (a x, b x)`. -/
noncomputable def tcmSumMap {X : Type} [TopologicalSpace X] {k : ℕ}
    (a : C(X, EuclideanSpace ℝ (Fin 8))) (b : C(X, EuclideanSpace ℝ (Fin k))) :
    C(X, EuclideanSpace ℝ (Fin (8 + k))) :=
  ⟨fun x => Work.Whitney.tcmSumLin 8 k (a x, b x),
    (Work.Whitney.tcmSumLin 8 k).continuous.comp (a.continuous.prodMk b.continuous)⟩

lemma tcmPr1_comp_toModelMap {X : Type} [TopologicalSpace X] (k : ℕ)
    (a : C(X, EuclideanSpace ℝ (Fin 8))) (b : C(X, EuclideanSpace ℝ (Fin k))) :
    (Work.Whitney.tcmPr1 PUnit 8 k).comp (toModelMap a b) = (psiUnit 8).comp a := by
  apply ContinuousMap.ext; intro x; rfl

lemma tcmPr2_comp_toModelMap {X : Type} [TopologicalSpace X] (k : ℕ)
    (a : C(X, EuclideanSpace ℝ (Fin 8))) (b : C(X, EuclideanSpace ℝ (Fin k))) :
    (Work.Whitney.tcmPr2 PUnit 8 k).comp (toModelMap a b) = (psiUnit k).comp b := by
  apply ContinuousMap.ext; intro x; rfl

lemma tcmF_comp_toModelMap {X : Type} [TopologicalSpace X] (k : ℕ)
    (a : C(X, EuclideanSpace ℝ (Fin 8))) (b : C(X, EuclideanSpace ℝ (Fin k))) :
    (Work.Whitney.tcmF PUnit 8 k).comp (toModelMap a b)
      = (psiUnit (8 + k)).comp (tcmSumMap a b) := by
  apply ContinuousMap.ext; intro x; rfl

theorem tcmRelCup_stdModelGen {X : Type} [TopologicalSpace X] {k : ℕ}
    (a : C(X, EuclideanSpace ℝ (Fin 8))) (b : C(X, EuclideanSpace ℝ (Fin k))) :
    Work.Whitney.tcmRelCup ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        (isOpen_compl_singleton.preimage a.continuous)
        (isOpen_compl_singleton.preimage b.continuous) 8 k
      ((Work.Thom.relCohMap a ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))) (fun x hx => hx) ℤ 8).hom
        (Work.ThomBordism.stdModelGen 8))
      ((Work.Thom.relCohMap b ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) (fun x hx => hx) ℤ k).hom
        (Work.ThomBordism.stdModelGen k))
    = (Work.Thom.relCohMap
        (⟨fun x => Work.Whitney.tcmSumLin 8 k (a x, b x),
          (Work.Whitney.tcmSumLin 8 k).continuous.comp (a.continuous.prodMk b.continuous)⟩ :
            C(X, EuclideanSpace ℝ (Fin (8 + k))))
        ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8)))
          ∪ (fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (8 + k))))
        (fun x hx => by
          intro h0
          rcases hx with hx | hx
          · exact hx (congrArg Prod.fst ((Work.Whitney.tcmSumLin 8 k).injective
              (h0.trans (map_zero (Work.Whitney.tcmSumLin 8 k)).symm)))
          · exact hx (congrArg Prod.snd ((Work.Whitney.tcmSumLin 8 k).injective
              (h0.trans (map_zero (Work.Whitney.tcmSumLin 8 k)).symm)))) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) := by
  -- the membership condition for the Whitney-sum map
  have hG : ∀ x ∈ ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        ∪ (fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))),
      Work.Whitney.tcmSumLin 8 k (a x, b x) ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (8 + k)))) := by
    intro x hx
    rw [Set.mem_union] at hx
    intro h0
    rcases hx with hx | hx
    · exact hx (congrArg Prod.fst ((Work.Whitney.tcmSumLin 8 k).injective
        (h0.trans (map_zero (Work.Whitney.tcmSumLin 8 k)).symm)))
    · exact hx (congrArg Prod.snd ((Work.Whitney.tcmSumLin 8 k).injective
        (h0.trans (map_zero (Work.Whitney.tcmSumLin 8 k)).symm)))
  -- rewrite the goal in the `tcmSumMap` vocabulary
  show Work.Whitney.tcmRelCup ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        (isOpen_compl_singleton.preimage a.continuous)
        (isOpen_compl_singleton.preimage b.continuous) 8 k
      ((Work.Thom.relCohMap a ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))) (fun x hx => hx) ℤ 8).hom
        (Work.ThomBordism.stdModelGen 8))
      ((Work.Thom.relCohMap b ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) (fun x hx => hx) ℤ k).hom
        (Work.ThomBordism.stdModelGen k))
    = (Work.Thom.relCohMap (tcmSumMap a b)
        (((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ∪ ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (8 + k)))) hG ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))
  -- the two pulled-back model classes of the one-point-base product formula
  set X1 := (Work.Thom.relCohMap (Work.Whitney.tcmPr1 PUnit 8 k) (Work.Whitney.tcmA PUnit 8 k)
        (Work.Thom.Punct PUnit 8) (fun x hx => hx) ℤ 8).hom (Work.Thom.Mpun 8 PUnit) with hX1
  set X2 := (Work.Thom.relCohMap (Work.Whitney.tcmPr2 PUnit 8 k) (Work.Whitney.tcmC PUnit 8 k)
        (Work.Thom.Punct PUnit k) (fun x hx => hx) ℤ k).hom (Work.Thom.Mpun k PUnit) with hX2
  -- the first factor is the pullback of `X1` along `toModelMap`
  have hLa : (Work.Thom.relCohMap a ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))) (fun x hx => hx) ℤ 8).hom
      (Work.ThomBordism.stdModelGen 8)
      = (Work.Thom.relCohMap (toModelMap a b)
          ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          (Work.Whitney.tcmA PUnit 8 k) (fun x hx => hx) ℤ 8).hom X1 := by
    rw [stdModelGen_eq_pullback 8]
    rw [Work.Thom.relCohMap_compA_apply ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))) (Work.Thom.Punct PUnit 8) a (psiUnit 8)
        (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) ℤ 8 (Work.Thom.Mpun 8 PUnit)]
    rw [Work.Thom.relCohMap_congrA ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        (Work.Thom.Punct PUnit 8) (tcmPr1_comp_toModelMap k a b).symm (fun x hx => hx)
        (fun x hx => hx) ℤ 8]
    rw [← Work.Thom.relCohMap_compA_apply ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
        (Work.Whitney.tcmA PUnit 8 k) (Work.Thom.Punct PUnit 8) (toModelMap a b)
        (Work.Whitney.tcmPr1 PUnit 8 k) (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) ℤ 8
        (Work.Thom.Mpun 8 PUnit)]
  -- the second factor is the pullback of `X2` along `toModelMap`
  have hLb : (Work.Thom.relCohMap b ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) (fun x hx => hx) ℤ k).hom
      (Work.ThomBordism.stdModelGen k)
      = (Work.Thom.relCohMap (toModelMap a b)
          ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
          (Work.Whitney.tcmC PUnit 8 k) (fun x hx => hx) ℤ k).hom X2 := by
    rw [stdModelGen_eq_pullback k]
    rw [Work.Thom.relCohMap_compA_apply ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) (Work.Thom.Punct PUnit k) b (psiUnit k)
        (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) ℤ k (Work.Thom.Mpun k PUnit)]
    rw [Work.Thom.relCohMap_congrA ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        (Work.Thom.Punct PUnit k) (tcmPr2_comp_toModelMap k a b).symm (fun x hx => hx)
        (fun x hx => hx) ℤ k]
    rw [← Work.Thom.relCohMap_compA_apply ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
        (Work.Whitney.tcmC PUnit 8 k) (Work.Thom.Punct PUnit k) (toModelMap a b)
        (Work.Whitney.tcmPr2 PUnit 8 k) (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) ℤ k
        (Work.Thom.Mpun k PUnit)]
  -- the sum side is the pullback of the model class of the sum along `toModelMap`
  have hRhs : (Work.Thom.relCohMap (tcmSumMap a b)
        (((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ∪ ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (8 + k)))) hG ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))
      = (Work.Thom.relCohMap (toModelMap a b)
          (((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
            ∪ ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))))
          (Work.Whitney.tcmA PUnit 8 k ∪ Work.Whitney.tcmC PUnit 8 k)
          (fun x hx => hx) ℤ (8 + k)).hom
        ((Work.Thom.relCohMap (Work.Whitney.tcmF PUnit 8 k)
          (Work.Whitney.tcmA PUnit 8 k ∪ Work.Whitney.tcmC PUnit 8 k)
          (Work.Thom.Punct PUnit (8 + k))
          (Work.Whitney.tcmF_mem PUnit 8 k) ℤ (8 + k)).hom (Work.Thom.Mpun (8 + k) PUnit)) := by
    rw [stdModelGen_eq_pullback (8 + k)]
    rw [Work.Thom.relCohMap_compA_apply
        (((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ∪ ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (8 + k)))) (Work.Thom.Punct PUnit (8 + k))
        (tcmSumMap a b) (psiUnit (8 + k))
        hG (fun x hx => hx) (fun x hx => hG x hx) ℤ (8 + k)
        (Work.Thom.Mpun (8 + k) PUnit)]
    rw [Work.Thom.relCohMap_congrA
        (((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ∪ ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))))
        (Work.Thom.Punct PUnit (8 + k)) (tcmF_comp_toModelMap k a b).symm (fun x hx => hG x hx)
        (fun x hx => hG x hx) ℤ (8 + k)]
    rw [← Work.Thom.relCohMap_compA_apply
        (((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
          ∪ ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))))
        (Work.Whitney.tcmA PUnit 8 k ∪ Work.Whitney.tcmC PUnit 8 k)
        (Work.Thom.Punct PUnit (8 + k))
        (toModelMap a b) (Work.Whitney.tcmF PUnit 8 k) (fun x hx => hx)
        (Work.Whitney.tcmF_mem PUnit 8 k) (fun x hx => hG x hx) ℤ (8 + k)
        (Work.Thom.Mpun (8 + k) PUnit)]
  -- naturality of the canonical relative–relative cup along `toModelMap`
  have hnat := Work.Whitney.tcmRelCup_natural ℤ (toModelMap a b) (Work.Whitney.tcmA PUnit 8 k)
      (Work.Whitney.tcmC PUnit 8 k)
      ((fun x => a x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 8))))
      ((fun x => b x) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
      (Work.Whitney.isOpen_tcmA PUnit 8 k) (Work.Whitney.isOpen_tcmC PUnit 8 k)
      (isOpen_compl_singleton.preimage a.continuous) (isOpen_compl_singleton.preimage b.continuous)
      (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) 8 k X1 X2
  -- the Koszul sign of the model formula vanishes for the ranks `8` and `k`
  have hEven : (-1 : ℤ) ^ (8 * k) = 1 :=
    Even.neg_one_pow ⟨4 * k, by ring⟩
  rw [hLa, hLb, ← hnat,
    Work.Whitney.tcmModelMul_point_signed_full PUnit 8 k, map_zsmul, hRhs, hEven, one_smul]

end Work.ThomBordism.KeyLocal
