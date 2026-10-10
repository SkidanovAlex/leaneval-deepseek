import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.FiberValue
import Submission.NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_algEquiv_completion_eq_finrank
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_decompositionSubgroup_ofInfinite_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne's Proposition 2.7 at an archimedean place

For a finite Galois extension `L / K` of number fields, an infinite place `v` of `K` and an
infinite place `w` of `L` above it, the *fibre* `∏_{w' | v} L_{w'}ˣ` of the idèles of `L` at `v`
has Herbrand quotient equal to the order of the decomposition group of `w`:

  `h(∏_{w' | v} L_{w'}ˣ) = #D_w`.

This is the archimedean half of Milne, *Class Field Theory*, Proposition 2.7 (the nonarchimedean
half is `NK.GlobalCFTdeep.herbrandEq_fiberIdeles_ofFinite`).  The argument follows the same
route as in the finite case:

* Shapiro's lemma for the fibre (`NK.GlobalCFTdeep.herbrandEq_fiberIdeles_iff`) reduces the
  statement to the local computation `h(D_w, L_wˣ) = #D_w`;
* the decomposition group `D_w` is the local Galois group `Gal(L_w/K_v)`
  (`decompositionSubgroupMulEquivLocalGalois`), and the local units representation
  `localUnitsRep (ofInfinite w)` is the restriction of the natural representation of the local
  Galois group on `L_wˣ` along that isomorphism (`localUnitsRep_eq_res_ofInfinite`);
* the local extension `L_w/K_v` is one of `ℝ/ℝ`, `ℂ/ℂ` (trivial, of degree `1`) or `ℂ/ℝ`
  (of degree `2`), so the norm index computation
  `[K_vˣ : N_{L_w/K_v} L_wˣ] = [L_w : K_v]`
  (`index_normGroup_completion_eq_finrank`) applies, and
  `NK.GlobalCFTdeep.Herbrand.herbrandEq_units_of_normIndex` gives the local Herbrand quotient.

The one genuinely archimedean input is the identification of the decomposition group with the
local Galois group: the local action of a stabiliser of `w` on `L_w` is a continuous ring
automorphism, hence fixes the dense image of `K_v` (here of `K`), so it defines a `K_v`-algebra
automorphism; the map `δ ↦ localAction δ` is multiplicative by
`NK.GlobalCFTdeep.localAction_mul_eq_trans`, injective by density, and bijective because both
sides have cardinality the local degree `[L_w : K_v]`
(`natCard_algEquiv_completion_eq_finrank`, `natCard_decompositionSubgroup_ofInfinite_eq_finrank`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped NumberField NumberField.LiesOver RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep

/-! ### The local action at an archimedean place fixes the base completion -/

/-- **The local action of a stabiliser of an archimedean place fixes the image of `K_v`.**  For
`σ ∈ Gal(L/K)` with `σ • w = w`, the induced automorphism of `L_w` is continuous and fixes the
image of `L`; hence it fixes the image of `K_v` as well, both sides being continuous functions
agreeing on the dense image of `K` in `v.Completion`. -/
lemma localAction_completionMap_fixed {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v]
    (σ : L ≃ₐ[K] L) (hσ : σ • Place.ofInfinite w = Place.ofInfinite w) (a : v.Completion) :
    NK.GlobalCFT.Inclusion.Place.localAction σ (Place.ofInfinite w) hσ
        (NumberField.LiesOver.completionMap (v := v) (w := w) a)
      = NumberField.LiesOver.completionMap (v := v) (w := w) a := by
  have hdense : DenseRange (algebraMap K v.Completion) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField (Place.ofInfinite v)
  have hcont : Continuous (fun x : v.Completion =>
      NK.GlobalCFT.Inclusion.Place.localAction σ (Place.ofInfinite w) hσ
        (NumberField.LiesOver.completionMap (v := v) (w := w) x)) :=
    (NK.GlobalCFT.Inclusion.Place.continuous_localAction σ (Place.ofInfinite w) hσ).comp
      (NumberField.LiesOver.continuous_completionMap (v := v) (w := w))
  have hfun : (fun x : v.Completion =>
      NK.GlobalCFT.Inclusion.Place.localAction σ (Place.ofInfinite w) hσ
        (NumberField.LiesOver.completionMap (v := v) (w := w) x))
      = (fun x : v.Completion => NumberField.LiesOver.completionMap (v := v) (w := w) x) := by
    refine DenseRange.equalizer hdense hcont
      (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)) ?_
    funext k
    show NK.GlobalCFT.Inclusion.Place.localAction σ (Place.ofInfinite w) hσ
        (NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k))
      = NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k)
    rw [NK.GlobalCFT.Inclusion.completionMap_algebraMap (K := K) (L := L) (v := v) (w := w) k,
      localAction_algebraMap_eq σ (Place.ofInfinite w) hσ]
    exact congrArg (algebraMap L (w.Completion)) (AlgEquiv.commutes σ k)
  exact congrFun hfun a

/-! ### The decomposition group is the local Galois group -/

/-- The canonical homomorphism `D_w →* Gal(L_w/K_v)` at an archimedean place: the local action of
a stabiliser of `w`. -/
noncomputable def decompositionSubgroupHomLocalGalois {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v] :
    decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w) →*
      (w.Completion ≃ₐ[v.Completion] w.Completion) where
  toFun δ := AlgEquiv.ofRingEquiv (f := NK.GlobalCFT.Inclusion.Place.localAction (δ : L ≃ₐ[K] L)
      (Place.ofInfinite w) δ.2)
    (localAction_completionMap_fixed (v := v) (w := w) δ.1 δ.2)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    show NK.GlobalCFT.Inclusion.Place.localAction (1 : L ≃ₐ[K] L) (Place.ofInfinite w)
      (1 : decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w)).2 x = x
    rw [localAction_one_eq_refl]
    rfl
  map_mul' := by
    intro δ ε
    apply AlgEquiv.ext
    intro x
    show NK.GlobalCFT.Inclusion.Place.localAction (δ * ε : L ≃ₐ[K] L) (Place.ofInfinite w)
        (δ * ε).2 x
      = NK.GlobalCFT.Inclusion.Place.localAction (δ : L ≃ₐ[K] L) (Place.ofInfinite w) δ.2
          (NK.GlobalCFT.Inclusion.Place.localAction (ε : L ≃ₐ[K] L) (Place.ofInfinite w) ε.2 x)
    rw [localAction_mul_eq_trans (δ : L ≃ₐ[K] L) (ε : L ≃ₐ[K] L) (Place.ofInfinite w) δ.2 ε.2
      (δ * ε).2]
    rfl

/-- The value of `decompositionSubgroupHomLocalGalois` is the local action. -/
lemma decompositionSubgroupHomLocalGalois_apply {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v]
    (δ : decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w)) (x : w.Completion) :
    decompositionSubgroupHomLocalGalois (K := K) (L := L) (v := v) (w := w) δ x
      = NK.GlobalCFT.Inclusion.Place.localAction (δ : L ≃ₐ[K] L) (Place.ofInfinite w) δ.2 x :=
  rfl

/-- The homomorphism `D_w →* Gal(L_w/K_v)` at an archimedean place is injective: an element of the
decomposition group acting trivially on the completion acts trivially on the dense image of `L`,
hence is the identity. -/
lemma decompositionSubgroupHomLocalGalois_injective {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v] :
    Function.Injective (decompositionSubgroupHomLocalGalois (K := K) (L := L) (v := v) (w := w)) := by
  intro δ ε h
  have h1 : ∀ x : L, (δ : L ≃ₐ[K] L) x = (ε : L ≃ₐ[K] L) x := by
    intro x
    have h2 : decompositionSubgroupHomLocalGalois (K := K) (L := L) (v := v) (w := w) δ
          (algebraMap L (w.Completion) x)
        = decompositionSubgroupHomLocalGalois (K := K) (L := L) (v := v) (w := w) ε
          (algebraMap L (w.Completion) x) :=
      congrArg (fun f : w.Completion ≃ₐ[v.Completion] w.Completion =>
        f (algebraMap L (w.Completion) x)) h
    rw [decompositionSubgroupHomLocalGalois_apply, decompositionSubgroupHomLocalGalois_apply,
      localAction_algebraMap_eq, localAction_algebraMap_eq] at h2
    exact NK.GlobalCFT.Inclusion.injective_algebraMap_ofInfinite w h2
  exact Subtype.ext (AlgEquiv.ext h1)

/-- **The decomposition group of an archimedean place is its local Galois group.**  The local
action of the stabiliser of `w` is an isomorphism `D_w ≃* Gal(L_w/K_v)`; it is injective by
density and both sides have cardinality the local degree `[L_w : K_v]`. -/
noncomputable def decompositionSubgroupMulEquivLocalGalois {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K) (w : InfinitePlace L) (hw : w.LiesOver v)
    [Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w))] :
    decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w) ≃*
      (w.Completion ≃ₐ[v.Completion] w.Completion) := by
  haveI := hw
  haveI hfin : FiniteDimensional v.Completion w.Completion :=
    NK.GlobalCFT.Inclusion.finite_completionMap (K := K) (L := L) (v := v) (w := w)
  haveI : Fintype (w.Completion ≃ₐ[v.Completion] w.Completion) :=
    AlgEquiv.fintype v.Completion w.Completion
  have hG := natCard_algEquiv_completion_eq_finrank (K := K) (L := L) v w
  have hD := natCard_decompositionSubgroup_ofInfinite_eq_finrank (K := K) (L := L) v w
  refine MulEquiv.ofBijective (decompositionSubgroupHomLocalGalois (K := K) (L := L) (v := v) (w := w))
    (Function.Injective.bijective_of_nat_card_le
      (decompositionSubgroupHomLocalGalois_injective (K := K) (L := L) (v := v) (w := w)) ?_)
  rw [hG, hD]

/-! ### The local units representation is the restriction of the local Galois representation -/

/-- **The local units representation of the decomposition group is the restriction of the local
Galois representation along `D_w ≃* Gal(L_w/K_v)`.** -/
lemma localUnitsRep_eq_res_ofInfinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K) (w : InfinitePlace L) (hw : w.LiesOver v)
    [Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w))] :
    localUnitsRep (K := K) (L := L) (Place.ofInfinite w) =
      Rep.res (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw).toMonoidHom
        (Rep.ofMulDistribMulAction (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ) := by
  haveI := hw
  letI : MulDistribMulAction (decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w))
      ((w.Completion)ˣ) := decompositionUnitsAction (K := K) (L := L) (Place.ofInfinite w)
  rw [localUnitsRep]
  refine congrArg Rep.of ?_
  apply MonoidHom.ext
  intro σ
  apply LinearMap.ext
  intro a
  have hsmul : (decompositionUnitsAction (K := K) (L := L) (Place.ofInfinite w)).smul σ
        (Additive.toMul a)
      = (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw σ)
        • (Additive.toMul a) := by
    rw [decompositionUnitsAction_smul, AlgEquiv.smul_units_def]
    have key : NK.GlobalCFT.Inclusion.Place.localAction (σ : L ≃ₐ[K] L)
        (Place.ofInfinite w) σ.2
        = (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw σ).toRingEquiv := by
      apply RingEquiv.ext
      intro x
      show NK.GlobalCFT.Inclusion.Place.localAction (σ : L ≃ₐ[K] L) (Place.ofInfinite w) σ.2 x
        = decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw σ x
      rw [show decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw σ
          = decompositionSubgroupHomLocalGalois (K := K) (L := L) (v := v) (w := w) σ from rfl]
      rw [decompositionSubgroupHomLocalGalois_apply]
    rw [show (↑(decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw σ) :
        w.Completion →* w.Completion)
        = ((decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw σ).toRingEquiv).toMonoidHom
        from rfl]
    rw [← key]
  exact congrArg Additive.ofMul hsmul

/-! ### The local Herbrand computation at an archimedean place -/

/-- **Milne's Proposition 2.7 at an archimedean place, local form**: the Herbrand quotient of the
local units `L_wˣ` with the action of the decomposition group `D_w` is the order of `D_w`. -/
theorem herbrandEq_localUnitsRep_ofInfinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K) (w : InfinitePlace L) (hw : w.LiesOver v)
    [Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w))] :
    HerbrandEq (localUnitsRep (K := K) (L := L) (Place.ofInfinite w))
      (Nat.card (decompositionSubgroup (K := K) (L := L) (Place.ofInfinite w))) := by
  haveI := hw
  -- The local extension is finite dimensional and Galois (of degree `1` or `2`).
  haveI : FiniteDimensional v.Completion w.Completion :=
    NK.GlobalCFT.Inclusion.finite_completionMap (K := K) (L := L) (v := v) (w := w)
  haveI : IsGalois v.Completion w.Completion :=
    IsGalois.of_card_aut_eq_finrank _ _
      (natCard_algEquiv_completion_eq_finrank (K := K) (L := L) v w)
  letI : Fintype (w.Completion ≃ₐ[v.Completion] w.Completion) :=
    AlgEquiv.fintype v.Completion w.Completion
  -- The norm index is the local degree (`ℝ/ℝ`, `ℂ/ℂ` trivial, `ℂ/ℝ` of degree `2`).
  have hindex : (MonoidHom.range
        (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion))).index
      = Module.finrank v.Completion w.Completion := by
    rw [← NK.LocalReciprocity.normGroup_eq_range]
    exact index_normGroup_completion_eq_finrank (K := K) (L := L) v w
  have hGal := herbrandEq_units_of_normIndex (F := v.Completion) (E := w.Completion) hindex
  have hcard := natCard_decompositionSubgroup_ofInfinite_eq_finrank (K := K) (L := L) v w
  -- Transfer along the isomorphism `D_w ≃* Gal(L_w/K_v)`.
  have h0 := natCard_tateCohomology_zero_of_mulEquiv_res
    (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw)
    (Representation.ofMulDistribMulAction (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ)
  have h1 := natCard_tateCohomology_one_of_mulEquiv_res
    (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw)
    (Representation.ofMulDistribMulAction (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ)
  rw [HerbrandEq] at hGal ⊢
  rw [localUnitsRep_eq_res_ofInfinite (K := K) (L := L) v w hw, hcard]
  rw [show hZero (Rep.res (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw).toMonoidHom
        (Rep.ofMulDistribMulAction (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ))
      = hZero (Rep.of ((Representation.ofMulDistribMulAction
          (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ).comp
          (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw).toMonoidHom))
      from rfl]
  rw [show hOne (Rep.res (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw).toMonoidHom
        (Rep.ofMulDistribMulAction (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ))
      = hOne (Rep.of ((Representation.ofMulDistribMulAction
          (w.Completion ≃ₐ[v.Completion] w.Completion) (w.Completion)ˣ).comp
          (decompositionSubgroupMulEquivLocalGalois (K := K) (L := L) v w hw).toMonoidHom))
      from rfl]
  simp only [hZero_def, hOne_def] at hGal ⊢
  rw [h0, h1]
  exact hGal

/-! ### The fibre

Shapiro's lemma for the fibre (`NK.GlobalCFTdeep.herbrandEq_fiberIdeles_iff`) turns the local
computation into the statement for the fibre `∏_{w' | v} L_{w'}ˣ` itself. -/

/-- **Milne, *CFT*, Proposition 2.7 at an archimedean place**: for a finite Galois extension
`L / K` of number fields, an infinite place `v` of `K` and an infinite place `w` of `L` above it,
the Herbrand quotient of the fibre `∏_{w' | v} L_{w'}ˣ` is the order of the decomposition group
of `w` (equivalently, the local degree `[L_w : K_v]`). -/
theorem herbrandEq_fiberIdeles_ofInfinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    (hw : w.LiesOver v)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofInfinite w))] :
    NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) (NK.GlobalCFT.Place.ofInfinite v))
      (Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w))) :=
  (herbrandEq_fiberIdeles_iff (K := K) (L := L) (Place.ofInfinite v) (Place.ofInfinite w)
    (Place.liesOver_ofInfinite hw) _).mpr
    (herbrandEq_localUnitsRep_ofInfinite (K := K) (L := L) v w hw)

end NK.GlobalCFTdeep.Herbrand
