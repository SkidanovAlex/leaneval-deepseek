import Mathlib
import Submission.Work.ThomBordism.Grassmann.PlaneCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The oriented Grassmannian is an *open* quotient, and continuity of rotation families

The quotient map `V_k(ℝ^{k+m}) → G̃r_k(ℝ^{k+m})` is the quotient by the action of `SO(k)` by
homeomorphisms, hence an **open** quotient map.  This has two consequences used throughout the
trivialisation of the incidence space:

* a map `G × Y → Z` out of a product with the Grassmannian is continuous as soon as its composite
  with `(mk × id)` is (`continuous_lift_prod_left_of_isOpenQuotientMap`) — the standard
  product-of-a-quotient criterion, which for a *general* quotient map needs `Y` locally compact, but
  for an *open* quotient map needs nothing (the proof goes through `IsOpenQuotientMap.map_nhds_eq`);
* hence `planeAct`- and `rotE`-families are continuous without any local compactness hypothesis
  (`continuous_planeAct_family'`, `continuous_rotE_comp'`), which is what makes them applicable with
  index types such as the open half `upSet` of the incidence space.
-/

open scoped Topology
open Filter

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The `SO(k)`-action on frames -/

/-- The action of a matrix in `SO(k)` on frames is continuous. -/
theorem continuous_soAct (A : SOk k) : Continuous fun f : Stiefel k m => A.act f := by
  show Continuous fun f : Stiefel k m =>
    (⟨soActFun A.1 f.1, orthonormal_soActFun A.2.1 f.2⟩ : Stiefel k m)
  refine Continuous.subtype_mk (f := fun f : Stiefel k m => soActFun A.1 f.1) ?_ _
  refine continuous_pi fun i => ?_
  have hterm : ∀ j : Fin k, Continuous fun g : Stiefel k m =>
      (A.1 j i : ℝ) • (g.1 j : Amb (k+m)) :=
    fun j => (continuous_const : Continuous fun _ : Stiefel k m => (A.1 j i : ℝ)).smul
      ((continuous_apply j).comp continuous_subtype_val)
  have hsum := continuous_finsetSum
    (f := fun j (g : Stiefel k m) => (A.1 j i : ℝ) • (g.1 j : Amb (k+m)))
    (Finset.univ : Finset (Fin k)) (fun j _ => hterm j)
  simpa only [soActFun] using hsum

/-- `Aᵀ * A = 1` for `A ∈ SO(k)` (the companion of `SOk.transpose_mul_self`). -/
theorem SOk.transpose_mul_self' (A : SOk k) : A.transpose * A = 1 := by
  have h := SOk.transpose_mul_self A.transpose
  rwa [show A.transpose.transpose = A from Subtype.ext (Matrix.transpose_transpose A.1)] at h

/-- `A.act (A.transpose.act f) = f`. -/
theorem SOk.act_self_transpose_act (A : SOk k) (f : Stiefel k m) :
    A.act (A.transpose.act f) = f := by
  rw [← SOk.act_mul (A := A.transpose) (B := A) (f := f), SOk.transpose_mul_self' A, SOk.act_one]

/-- **The `SO(k)`-action on frames is an open map** (it is a homeomorphism). -/
theorem isOpenMap_soAct (A : SOk k) : IsOpenMap fun f : Stiefel k m => A.act f := by
  intro U hU
  have h : (fun f : Stiefel k m => A.act f) '' U
      = (fun f : Stiefel k m => A.transpose.act f) ⁻¹' U := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      show A.transpose.act (A.act f) ∈ U
      rw [SOk.act_transpose_act]
      exact hf
    · intro hg
      exact ⟨A.transpose.act g, hg, SOk.act_self_transpose_act A g⟩
  rw [h]
  exact (continuous_soAct A.transpose).isOpen_preimage U hU

/-! ## The quotient map is an open quotient map -/

/-- **The quotient map to the oriented Grassmannian is open** (the action is by homeomorphisms). -/
theorem isOpenMap_quot_mk_grassmann :
    IsOpenMap (Quot.mk (grassmannSetoid k m).r : Stiefel k m → Quot (grassmannSetoid k m).r) := by
  intro U hU
  rw [isOpen_coinduced]
  have hpre : (Quot.mk (grassmannSetoid k m).r ⁻¹' (Quot.mk (grassmannSetoid k m).r '' U))
      = ⋃ A : SOk k, (fun f : Stiefel k m => A.act f) ⁻¹' U := by
    ext f
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨g, hgU, hgf⟩
      have hrel : (grassmannSetoid k m).r g f := Quotient.eq.mp hgf
      obtain ⟨A, hA⟩ := hrel
      refine ⟨A.transpose, ?_⟩
      show A.transpose.act f ∈ U
      rw [hA, SOk.act_transpose_act]
      exact hgU
    · rintro ⟨A, hA⟩
      exact ⟨A.act f, hA, (Quot.sound (show (grassmannSetoid k m).r f (A.act f) from ⟨A, rfl⟩)).symm⟩
  rw [hpre]
  exact isOpen_iUnion fun A => (continuous_soAct A).isOpen_preimage U hU

/-- **The quotient map to the oriented Grassmannian is an open quotient map.** -/
theorem isOpenQuotientMap_quot_mk_grassmann :
    IsOpenQuotientMap (Quot.mk (grassmannSetoid k m).r : Stiefel k m → Quot (grassmannSetoid k m).r) :=
  ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_quot_mk_grassmann⟩

/-! ## Lifting continuous maps out of a product with a quotient -/

/-- **The product criterion for an *open* quotient map**: if `f : X₀ → X` is an open quotient map
and the composite of `g : X × Y → Z` with `(f × id)` is continuous, then so is `g`.  No local
compactness of `Y` is needed, because `f` is open (`IsOpenQuotientMap.map_nhds_eq`). -/
theorem continuous_lift_prod_left_of_isOpenQuotientMap {X₀ X Y Z : Type*} [TopologicalSpace X₀]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X₀ → X}
    (hf : IsOpenQuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g :=
  (hf.prodMap IsOpenQuotientMap.id).continuous_comp_iff.mp (by
    change Continuous (fun p : X₀ × Y => g (f p.1, p.2))
    exact hg)

/-! ## Continuity of `planeAct`- and `rotE`-families, revisited -/

/-- **The plane action is continuous, jointly in the linear isometry (through its values) and the
plane** — with no local compactness hypothesis on the index type. -/
theorem continuous_planeAct_family' {ι : Type} [TopologicalSpace ι]
    (R : ι → Amb (k+m) →ₗᵢ[ℝ] Amb (k+m))
    (hR : Continuous fun q : ι × Amb (k+m) => R q.1 q.2) :
    Continuous fun q : Quot (grassmannSetoid k m).r × ι => planeAct (R q.2) q.1 := by
  refine continuous_lift_prod_left_of_isOpenQuotientMap
    (f := fun f : Stiefel k m => (Quot.mk (grassmannSetoid k m).r f)) 
    isOpenQuotientMap_quot_mk_grassmann ?_
  have hcont : Continuous fun p : Stiefel k m × ι =>
      Quot.mk (grassmannSetoid k m).r (⟨fun j => R p.2 (p.1.1 j), ⟨fun j => by
        rw [LinearIsometry.norm_map]; exact p.1.2.1 j, fun i j hij => by
        show inner ℝ (R p.2 (p.1.1 i)) (R p.2 (p.1.1 j)) = 0
        rw [LinearIsometry.inner_map_map, p.1.2.2 hij]⟩⟩ : Stiefel k m) := by
    refine continuous_quot_mk.comp (Continuous.subtype_mk ?_ _)
    refine continuous_pi fun j => ?_
    have hm : Continuous fun a : Stiefel k m × ι => (a.2, (a.1.1 : Fin k → Amb (k+m)) j) :=
      continuous_snd.prodMk
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst))
    exact hR.comp hm
  exact hcont.congr (fun p => (planeAct_mk (R p.2) p.1).symm)

/-- **`rotE` is continuous, in a continuous family of linear isometries acting on a continuous
family of points** — with no local compactness hypothesis on the index type. -/
theorem continuous_rotE_comp' {ι : Type} [TopologicalSpace ι]
    (R : ι → Amb (k+m) →ₗᵢ[ℝ] Amb (k+m))
    (hR : Continuous fun q : ι × Amb (k+m) => R q.1 q.2)
    (x : ι → ↥(incZero k m)) (hx : Continuous x) :
    Continuous fun i => rotE (R i) (x i) := by
  have hproj : Continuous fun i : ι => (x i).1.1 :=
    (VectorBundleCore.continuous_proj (tautologicalBundle k m)).comp
      (continuous_subtype_val.comp hx)
  have hvec : Continuous fun i : ι => evalVec (x i).1 :=
    continuous_evalVec.comp (continuous_subtype_val.comp hx)
  have hP : Continuous fun i : ι => planeAct (R i) (x i).1.1 :=
    (continuous_planeAct_family' (k := k) (m := m) R hR).comp (hproj.prodMk continuous_id)
  have hw : Continuous fun i : ι => R i (evalVec (x i).1) :=
    hR.comp (continuous_id.prodMk hvec)
  have hmem : ∀ i, R i (evalVec (x i).1) ≠ 0 ∧
      memPlane (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1)) := by
    intro i
    refine ⟨?_, planeAct_memPlane (R i) (evalVec_memPlane (x i).1)⟩
    intro h0
    have h1 : evalVec (x i).1 = 0 := by
      have h2 : ‖R i (evalVec (x i).1)‖ = ‖evalVec (x i).1‖ := LinearIsometry.norm_map (R i) _
      rw [h0, norm_zero] at h2
      exact norm_eq_zero.mp h2.symm
    exact evalVec_ne_zero_of_mem_zeroComplement (x i).1 (x i).2 h1
  have hmain : Continuous fun i : ι => mkTotal (planeAct (R i) (x i).1.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1))) :=
    continuousOn_toE_underlying.comp_continuous (hP.prodMk hw) hmem
  have hmem' : ∀ i, mkTotal (planeAct (R i) (x i).1.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1))) ∈ incZero k m := by
    intro i
    rw [Work.Thom.mem_zeroComplement]
    show toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1)) ≠ 0
    exact toECoordAt_ne_zero _ _ ((tautologicalBundle k m).mem_baseSet_at _) _
      (hmem i).1 (hmem i).2
  show Continuous fun i : ι => (⟨mkTotal (planeAct (R i) (x i).1.1)
      (toECoordAt ((tautologicalBundle k m).indexAt (planeAct (R i) (x i).1.1))
        (planeAct (R i) (x i).1.1) (R i (evalVec (x i).1))), hmem' i⟩ : ↥(incZero k m))
  exact Continuous.subtype_mk hmain hmem'

end

end Work.ThomBordism.Grassmann
