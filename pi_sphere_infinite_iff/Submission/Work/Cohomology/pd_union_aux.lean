import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.MVSequence

/-!
# Support plumbing for the gluing of the `Good` predicate

This file collects the elementary "support" lemmas used by the crux square of Hatcher's
Lemma 3.36, in the situation where a chain of an ambient space `M` is known to lie in the singular
chains of an open subspace `W ⊆ M`.

For `S ⊆ W ⊆ M`:

* `pdTr W S = {x : W | (x : M) ∈ S}` is the trace of `S` on `W`;
* `pdTrMap h : TopCat.of S ⟶ TopCat.of (pdTr W S)` is the canonical map (a homeomorphism);
* `inclChainsSub_eq_pdTrMap` shows that the chain inclusion `C_*(S) → C_*(W)` factors through the
  chains of the trace, so that `inclChainsSub` lands in the range of `inclChains` of the trace.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-- The trace on `W` of a subset `S ⊆ M`. -/
def pdTr (W S : Set M) : Set W := {x | (x : M) ∈ S}

@[simp] theorem pdTr_mem_iff (W S : Set M) (x : W) : x ∈ pdTr W S ↔ (x : M) ∈ S := Iff.rfl

/-- Monotonicity of the trace. -/
theorem pdTr_mono {W S T : Set M} (h : S ⊆ T) : pdTr W S ⊆ pdTr W T :=
  fun x hx => h hx

/-- The canonical map `S ⟶ W ∩ S` for `S ⊆ W` (a homeomorphism). -/
def pdTrMap {W S : Set M} (h : S ⊆ W) : TopCat.of S ⟶ TopCat.of (pdTr W S) :=
  TopCat.ofHom ⟨fun x => ⟨⟨(x : M), h x.2⟩, x.2⟩, by
    refine Continuous.subtype_mk (p := fun y : ↥W => (y : M) ∈ S)
      (f := fun x : ↥S => (⟨(x : M), h x.2⟩ : ↥W)) ?_ (fun x => x.2)
    exact Continuous.subtype_mk (p := fun y : ↥M => y ∈ W) (f := fun x : ↥S => (x : ↥M))
      (continuous_subtype_val (X := ↥M) (p := fun y : ↥M => y ∈ S)) (fun x => h x.2)⟩

/-- The canonical map is the identity on underlying points. -/
@[simp] theorem pdTrMap_coe {W S : Set M} (h : S ⊆ W) (x : ↥S) :
    ((pdTrMap h x : ↥(pdTr W S)) : ↥W) = ⟨(x : M), h x.2⟩ := rfl

/-- The canonical map followed by the inclusion into `W` is the inclusion of `S` into `W`. -/
theorem pdTrMap_comp {W S : Set M} (h : S ⊆ W) :
    pdTrMap h ≫ subtypeIncl (TopCat.of W) (pdTr W S) = pdIncl W S h := by
  ext x; rfl

/-- **The inclusion of chains `C_*(S) → C_*(W)` factors through the chains of the trace
`W ∩ S`.** -/
theorem inclChainsSub_eq_pdTrMap {W S : Set M} (h : S ⊆ W) :
    inclChainsSub M S W h
      = chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
        ≫ inclChains (TopCat.of W) (pdTr W S) := by
  rw [inclChainsSub, inclChains, chainMap_compPD]
  rw [pdTrMap_comp h]
  rfl

/-- **A chain of `S` included in `W` is a chain supported in the trace `W ∩ S`.** -/
theorem inclChainsSub_mem_range {W S : Set M} (h : S ⊆ W) (n : ℕ)
    (ξ : (singularChains ℤ (TopCat.of S)).X n) :
    (inclChainsSub M S W h).f n ξ
      ∈ LinearMap.range ((inclChains (TopCat.of W) (pdTr W S)).f n).hom := by
  refine ⟨((chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)).f n).hom ξ, ?_⟩
  have h2 := congrArg (fun (g : singularChains ℤ (TopCat.of S) ⟶ singularChains ℤ (TopCat.of W)) =>
    (g.f n).hom ξ) (inclChainsSub_eq_pdTrMap (M := M) h)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h2.symm

/-- The morphism of `TopCat` induced by a homeomorphism of topological spaces. -/
def pdHomeoHom {X Y : TopCat} (e : X ≃ₜ Y) : X ⟶ Y :=
  TopCat.ofHom { toFun := e.toFun, continuous_toFun := e.continuous_toFun }

/-- For `S T : Set M`, the canonical homeomorphism between the trace of `S` on `T` and the
intersection `S ∩ T`. -/
def pdInterHomeo (S T : Set M) : TopCat.of (pdTr T S) ≃ₜ TopCat.of (S ∩ T : Set M) where
  toFun x := ⟨((x : ↥T) : M), ⟨x.2, (x : ↥T).2⟩⟩
  invFun y := ⟨⟨(y : M), y.2.2⟩, y.2.1⟩
  left_inv x := by rfl
  right_inv y := by rfl
  continuous_toFun :=
    Continuous.subtype_mk (p := fun y : ↥M => y ∈ S ∧ y ∈ T)
      (f := fun x : ↥(pdTr T S) => ((x : ↥T) : M))
      (Continuous.subtype_val (p := fun y : ↥M => y ∈ T)
        (f := fun x : ↥(pdTr T S) => (x : ↥T))
        (continuous_subtype_val (X := ↥T) (p := fun y : ↥T => (y : M) ∈ S)))
      (fun x => ⟨x.2, (x : ↥T).2⟩)
  continuous_invFun :=
    Continuous.subtype_mk (p := fun y : ↥T => (y : M) ∈ S)
      (f := fun y : ↥(S ∩ T) => (⟨(y : M), y.2.2⟩ : ↥T))
      (Continuous.subtype_mk (p := fun y : ↥M => y ∈ T) (f := fun y : ↥(S ∩ T) => (y : M))
        (continuous_subtype_val (X := ↥M) (p := fun y : ↥M => y ∈ S ∧ y ∈ T))
        (fun y => y.2.2))
      (fun y => y.2.1)

/-- The canonical homeomorphism commutes with the inclusions of the two sides. -/
theorem pdInterHomeo_comp (S T : Set M) :
    pdHomeoHom (pdInterHomeo S T) ≫ subtypeIncl M (S ∩ T)
      = subtypeIncl (TopCat.of T) (pdTr T S) ≫ subtypeIncl M T := by
  ext x; rfl

/-- The chain-level form of `pdInterHomeo_comp`. -/
theorem pdInterHomeo_chain_comp (S T : Set M) :
    chainMap ℤ (TopCat.of (pdTr T S)) (TopCat.of (S ∩ T : Set M)) (pdHomeoHom (pdInterHomeo S T))
        ≫ inclChains M (S ∩ T)
      = inclChains (TopCat.of T) (pdTr T S) ≫ inclChains M T := by
  rw [inclChains, inclChains, inclChains, chainMap_compPD]
  rw [pdInterHomeo_comp S T, ← chainMap_compPD]

/-- The canonical map `W ∩ S ⟶ S` for `S ⊆ W`, inverse to `pdTrMap`. -/
def pdTrInv {W S : Set M} (h : S ⊆ W) : TopCat.of (pdTr W S) ⟶ TopCat.of S :=
  TopCat.ofHom ⟨fun y => ⟨((y : ↥W) : M), y.2⟩, by
    refine Continuous.subtype_mk (p := fun z : ↥M => z ∈ S)
      (f := fun y : ↥(pdTr W S) => ((y : ↥W) : M)) ?_ (fun y => y.2)
    exact Continuous.subtype_val (p := fun z : ↥M => z ∈ W)
      (f := fun y : ↥(pdTr W S) => (y : ↥W))
      (continuous_subtype_val (X := ↥W) (p := fun z : ↥W => (z : M) ∈ S))⟩

/-- The canonical map `S ⟶ W ∩ S` followed by its inverse is the identity. -/
theorem pdTrInv_comp_pdTrMap {W S : Set M} (h : S ⊆ W) :
    pdTrInv h ≫ pdTrMap h = 𝟙 (TopCat.of (pdTr W S)) := by
  ext x; rfl

/-- The chains of the trace are the chains of a subset of `W` in the range of `inclChainsSub`. -/
theorem inclChains_eq_pdTrInv {W S : Set M} (h : S ⊆ W) :
    inclChains (TopCat.of W) (pdTr W S)
      = chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
        ≫ inclChainsSub M S W h := by
  have h1 : chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
      ≫ chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
      = 𝟙 (singularChains ℤ (TopCat.of (pdTr W S))) := by
    rw [chainMap_compPD, pdTrInv_comp_pdTrMap h, chainMap_id']
  have h2 : inclChainsSub M S W h
      = chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
        ≫ inclChains (TopCat.of W) (pdTr W S) := inclChainsSub_eq_pdTrMap h
  calc inclChains (TopCat.of W) (pdTr W S)
      = 𝟙 _ ≫ inclChains (TopCat.of W) (pdTr W S) := (Category.id_comp _).symm
    _ = (chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
          ≫ chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h))
        ≫ inclChains (TopCat.of W) (pdTr W S) := by rw [h1]
    _ = chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
        ≫ (chainMap ℤ (TopCat.of S) (TopCat.of (pdTr W S)) (pdTrMap h)
          ≫ inclChains (TopCat.of W) (pdTr W S)) := Category.assoc _ _ _
    _ = chainMap ℤ (TopCat.of (pdTr W S)) (TopCat.of S) (pdTrInv h)
        ≫ inclChainsSub M S W h := by rw [h2]

/-- `pdIncl` agrees with `inclChainsSub`. -/
theorem pdIncl_eq_inclChainsSub {W S : Set M} (h : S ⊆ W) :
    chainMap ℤ (TopCat.of S) (TopCat.of W) (pdIncl W S h) = inclChainsSub M S W h := by
  rfl


end

end Work.Cohomology
