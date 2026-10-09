/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Naturality and `G`-equivariance of `θ`

* `valFn_smul` : the value map is `G`-equivariant;
* `thetaLin_smul` : `θ` is `G`-equivariant;
* `valFn_map` (in `valFn_map.lean`) : naturality of the value map in the rank;
* `thetaLin_natural` : naturality of `θ` in the rank along surjective operator homomorphisms.
-/

import Mathlib
import Submission.Work.SSGRoute.prop5.Theta
import Submission.Work.SSGRoute.prop5.valFn_map
import Submission.Work.SSGRoute.prop5.lowerCentralSeries_le_closure_commWord
import Submission.Work.Shrinking.TensorPower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement TensorProduct

set_option maxHeartbeats 1600000

namespace Work.SSGRoute.prop5

open Work.CohomologicalShrinking

noncomputable section

universe u

/-! ## The action on `F(d)/F(d)²` and on the graded pieces -/

/-- The class map `F(d) → F(d)/F(d)²` is `G`-equivariant. -/
lemma qmk_smul (p : ℕ) (G : Type*) [Group G] (d : ℕ) (g : G)
    (z : Work.Shrinking.freeOperatorGroup G d) :
    g • qmk p G d z = qmk p G d (g • z) := by
  unfold qmk
  change Additive.ofMul
      (g • (QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
        (⟨z, Subgroup.mem_top z⟩ : Ptop p G d) :
          Work.Shrinking.pCentralQuotient p (Work.Shrinking.freeOperatorGroup G d) 0)) = _
  rw [Work.CohomologicalShrinking.pCentral_smul_mk]
  rw [show (Work.Shrinking.subAut (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0) g
        (Work.Shrinking.map_pCentralSeries_eq p
          (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) 0)
        (⟨z, Subgroup.mem_top z⟩ : Ptop p G d) : Ptop p G d)
      = (⟨g • z, Subgroup.mem_top _⟩ : Ptop p G d) from Subtype.ext
        (Work.Shrinking.subAut_coe _ _ _ _)]

/-- The induced map on `F/F²` sends the class of `z` to the class of `ψ z`. -/
lemma quotMapLin_qmk (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) (z : Work.Shrinking.freeOperatorGroup G m) :
    Work.CohomologicalShrinking.quotMapLin p G ψ hψ (qmk p G m z) = qmk p G n (ψ z) := by
  show Additive.ofMul (Work.CohomologicalShrinking.quotMapLin p G ψ hψ
      (Additive.ofMul (QuotientGroup.mk' _ (Work.CohomologicalShrinking.toTop p G m z)))) = _
  rw [Work.CohomologicalShrinking.quotMapLin_mk]
  rfl

/-- The action of `G` on the graded piece, evaluated on the class of an element. -/
lemma refined_smul_mk (p : ℕ) (G : Type*) [Group G] (i j d : ℕ) (g : G)
    (y : Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j) :
    (g • (QuotientGroup.mk'
        ((Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
            (Work.CohomologicalShrinking.tauSucc i j).1
            (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf
          (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j)) y)
        : Work.CohomologicalShrinking.refinedQuotient p (Work.Shrinking.freeOperatorGroup G d) i j) =
      QuotientGroup.mk'
        ((Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
            (Work.CohomologicalShrinking.tauSucc i j).1
            (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf
          (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j))
        (Work.Shrinking.subAut
          (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j) g
          (Work.CohomologicalShrinking.map_refinedTerm_eq p
            (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) i j) y) := by
  change Work.Shrinking.quotAut
      (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j)
      (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
        (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2) g
      (Work.CohomologicalShrinking.map_refinedTerm_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) i j)
      (Work.CohomologicalShrinking.map_refinedTerm_eq p
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g)
        (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2)
      (QuotientGroup.mk' _ y) = _
  rw [Work.Shrinking.quotAut_mk]

/-! ## Equivariance of `valFn` and of `θ` -/

/-- The value map `valFn` is `G`-equivariant. -/
theorem valFn_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (g : G)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) :
    valFn p G i j d hj hji (fun k => g • x k) = g • valFn p G i j d hj hji x := by
  have hcomm : commWord j (fun k => g • x k)
      = MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g
          (commWord j x) := by
    have h := map_commWord
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g).toMonoidHom j x
    simpa using h.symm
  have hmem : ∀ (c : Work.Shrinking.freeOperatorGroup G d),
      c ∈ Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j →
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) c
        ∈ Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j := by
    intro c hc
    rw [← Work.CohomologicalShrinking.map_refinedTerm_eq p
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g) i j]
    exact Subgroup.mem_map_of_mem _ hc
  have key : ∀ (c : Work.Shrinking.freeOperatorGroup G d)
      (hc : c ∈ Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j),
      (g • (QuotientGroup.mk'
          ((Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
              (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf
            (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j))
          ⟨c, hc⟩ :
            Work.CohomologicalShrinking.refinedQuotient p
              (Work.Shrinking.freeOperatorGroup G d) i j))
        = QuotientGroup.mk' _ ⟨MulDistribMulAction.toMulAut G
            (Work.Shrinking.freeOperatorGroup G d) g c, hmem c hc⟩ := by
    intro c hc
    rw [refined_smul_mk]
    congr 1
  rw [valFn_eq, valFn_eq]
  unfold valFnOf
  change Additive.ofMul (QuotientGroup.mk' _ ⟨commWord j (fun k => g • x k) ^ p ^ (i - j), _⟩)
      = Additive.ofMul (g • (QuotientGroup.mk' _
          ⟨commWord j x ^ p ^ (i - j), _⟩ :
            Work.CohomologicalShrinking.refinedQuotient p
              (Work.Shrinking.freeOperatorGroup G d) i j))
  rw [key]
  exact congrArg Additive.ofMul (congrArg
    (QuotientGroup.mk'
      ((Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
          (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf
        (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j)))
    (Subtype.ext (by
      show (commWord j (fun k => g • x k)) ^ p ^ (i - j)
          = MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G d) g
              (commWord j x ^ p ^ (i - j))
      rw [hcomm, map_pow])))

/-- The multilinear map itself is `G`-equivariant on tuples. -/
lemma thetaFun_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (g : G) (f : Fin j → squareQuotient p G d) :
    thetaFun p G i j d hj hji (fun k => g • f k) = g • thetaFun p G i j d hj hji f := by
  rw [thetaFun_eq, thetaFun_eq]
  refine (valFn_congr p G i j d hj hji (fun k => ?_)).trans
    (valFn_smul p G i j d hj hji g (repTuple p G d j f))
  show qmk p G d (repOf p G d (g • f k)) = qmk p G d (g • repOf p G d (f k))
  rw [repOf_spec, ← qmk_smul p G d g (repOf p G d (f k)), repOf_spec]

/-- `θ` is `G`-equivariant. -/
theorem thetaLin_smul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (g : G)
    (Y : ⨂[ZMod p]^j (squareQuotient p G d)) :
    thetaLin p G i j d hj hji (g • Y) = g • thetaLin p G i j d hj hji Y := by
  rw [Work.Shrinking.smul_tensorPower_eq_map]
  show PiTensorProduct.lift (thetaMul p G i j d hj hji)
        (PiTensorProduct.map (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g) Y)
      = Work.Shrinking.actLinear (p := p) g
          (PiTensorProduct.lift (thetaMul p G i j d hj hji) Y)
  have h1 : PiTensorProduct.lift (thetaMul p G i j d hj hji)
        (PiTensorProduct.map (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g) Y)
      = PiTensorProduct.lift ((thetaMul p G i j d hj hji).compLinearMap
          (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g)) Y := by
    have h := LinearMap.congr_fun (PiTensorProduct.lift_comp_map
      (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g) (thetaMul p G i j d hj hji)) Y
    rwa [LinearMap.comp_apply] at h
  have key : PiTensorProduct.lift ((thetaMul p G i j d hj hji).compLinearMap
        (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g))
      = (Work.Shrinking.actLinear (p := p) g).comp
          (PiTensorProduct.lift (thetaMul p G i j d hj hji)) := by
    symm
    refine PiTensorProduct.lift.unique ?_
    intro f
    rw [LinearMap.comp_apply, PiTensorProduct.lift.tprod]
    show Work.Shrinking.actLinear (p := p) g (thetaFun p G i j d hj hji f)
        = (thetaMul p G i j d hj hji).compLinearMap
            (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g) f
    rw [Work.Shrinking.actLinear_apply]
    rw [show (thetaMul p G i j d hj hji).compLinearMap
          (fun _ : Fin j => Work.Shrinking.actLinear (p := p) g) f
        = thetaFun p G i j d hj hji (fun k => g • f k) from rfl]
    exact (thetaFun_smul p G i j d hj hji g f).symm
  rw [h1, key, LinearMap.comp_apply]

/-! ## Naturality of `θ` in the rank -/

/-- `θ` is natural along a surjective homomorphism of operator groups. -/
theorem thetaLin_natural (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j : ℕ) (hj : 1 ≤ j)
    (hji : j ≤ i) {m n : ℕ}
    (ψ : Work.Shrinking.freeOperatorGroup G m →* Work.Shrinking.freeOperatorGroup G n)
    (hψ : Function.Surjective ψ) :
    (thetaLin p G i j n hj hji).comp
        (PiTensorProduct.map (fun _ : Fin j => Work.CohomologicalShrinking.quotMapLin p G ψ hψ))
      = (Work.CohomologicalShrinking.gradedMapLin p ψ hψ i j).comp
          (thetaLin p G i j m hj hji) := by
  rw [thetaLin, thetaLin, PiTensorProduct.lift_comp_map]
  symm
  refine PiTensorProduct.lift.unique ?_
  intro f
  rw [LinearMap.comp_apply, PiTensorProduct.lift.tprod]
  show (Work.CohomologicalShrinking.gradedMapLin p ψ hψ i j)
        (thetaFun p G i j m hj hji f)
      = thetaFun p G i j n hj hji
          (fun k => Work.CohomologicalShrinking.quotMapLin p G ψ hψ (f k))
  rw [thetaFun_eq, valFn_map p G ψ hψ i j hj hji (repTuple p G m j f), thetaFun_eq]
  refine (valFn_congr p G i j n hj hji (fun k => ?_)).symm
  show qmk p G n (repOf p G n (Work.CohomologicalShrinking.quotMapLin p G ψ hψ (f k)))
      = qmk p G n (ψ (repTuple p G m j f k))
  rw [repOf_spec, ← quotMapLin_qmk p G ψ hψ (repTuple p G m j f k)]
  congr 1
  show f k = qmk p G m (repOf p G m (f k))
  rw [repOf_spec]

end

end Work.SSGRoute.prop5
