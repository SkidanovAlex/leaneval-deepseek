import Mathlib
import Submission.Work.Serre.E2dTools
import Submission.Work.Cohomology.relChainsHomeomorphCompat

/-!
# The middle slice of the pullback is the pullback over the slice

The E2(d) induction reduces the pair `(I^{n+1}, ∂I^{n+1})` of the cube to the *middle slice*
`sliceZ n = {last = 1/2}`, which is a cube of one dimension lower via
`sliceIncl n : Iⁿ → I^{n+1}`, `u ↦ Fin.snoc u (1/2)`.

This file records the (elementary, but essential) *pair* homeomorphism that this reduction rests on:
the preimage in the pullback `τ^*E` of the middle slice is the pullback of `p` along
`τ ∘ sliceIncl`, and under this homeomorphism the relative part
`sliceZ n ∩ ∂I^{n+1}` corresponds to `∂Iⁿ`.  Consequently the relative homology groups agree:

* `Work.Serre.sliceRetrFun` — the retraction `I^{n+1} → Iⁿ` forgetting the last coordinate;
* `Work.Serre.slicePreHomeo` — the homeomorphism of pairs;
* `Work.Serre.slice_pullback_iso` — the induced isomorphism of relative homology groups.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The retraction of the cube `I^{n+1}` onto its first `n` coordinates. -/
def sliceRetrFun (n : ℕ) : Work.Stems.Cubical.IC (n+1) → Work.Stems.Cubical.IC n :=
  fun u i => u (Fin.castSucc i)

theorem continuous_sliceRetrFun (n : ℕ) : Continuous (sliceRetrFun n) := by
  apply continuous_pi
  intro i
  exact continuous_apply (Fin.castSucc i)

/-- The retraction is a section of the slice inclusion. -/
theorem sliceRetrFun_sliceIncl (n : ℕ) (v : Work.Stems.Cubical.IC n) :
    sliceRetrFun n (sliceIncl n v) = v := by
  funext i
  simp [sliceRetrFun]

/-- On the middle slice, the slice inclusion is a section of the retraction. -/
theorem sliceIncl_sliceRetrFun (n : ℕ) {u : Work.Stems.Cubical.IC (n+1)}
    (hu : u ∈ sliceZ n) : sliceIncl n (sliceRetrFun n u) = u := by
  have hlast : u (Fin.last n) = half := (sliceZ_mem_iff n u).mp hu
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [hlast]
  · intro j
    simp [sliceRetrFun]

/-- A point of the middle slice lies on the boundary of `I^{n+1}` exactly when its first `n`
coordinates lie on the boundary of `Iⁿ` (the last coordinate is `1/2`, hence interior). -/
theorem sliceRetrFun_mem_cubeBdryS (n : ℕ) {u : Work.Stems.Cubical.IC (n+1)}
    (hu : u ∈ sliceZ n) : sliceRetrFun n u ∈ cubeBdryS n ↔ u ∈ cubeBdryS (n+1) := by
  have hlast : u (Fin.last n) = half := (sliceZ_mem_iff n u).mp hu
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Fin.castSucc i, hi⟩
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.lastCases ?_ ?_ i
    · intro hi
      exfalso
      rcases hi with h | h
      · have h0 : (u (Fin.last n) : ℝ) = 0 := by rw [h]; rfl
        have hcoord : (u (Fin.last n) : ℝ) = 1/2 := by rw [hlast]; rfl
        linarith
      · have h1 : (u (Fin.last n) : ℝ) = 1 := by rw [h]; rfl
        have hcoord : (u (Fin.last n) : ℝ) = 1/2 := by rw [hlast]; rfl
        linarith
    · intro j hj
      exact ⟨j, hj⟩

/-- The retraction of the middle slice `{last = 1/2}` of `I^{n+1}` onto `Iⁿ`. -/
def sliceRetrCM (n : ℕ) : C(↥(sliceZ n), Work.Stems.Cubical.IC n) where
  toFun u := sliceRetrFun n u.1
  continuous_toFun := (continuous_sliceRetrFun n).comp continuous_subtype_val

/-- The slice inclusion, as a map into the middle slice. -/
def sliceInclCM (n : ℕ) : C(Work.Stems.Cubical.IC n, ↥(sliceZ n)) where
  toFun v := ⟨sliceIncl n v, by
    show lastCoord (sliceIncl n v) = 1/2
    exact lastCoord_sliceIncl n v⟩
  continuous_toFun := Continuous.subtype_mk (sliceIncl n).continuous _

/-- **The preimage of the middle slice in the pullback is the pullback over the slice.**

Explicitly, a point of `↥(pbPre p τ (sliceZ n))` has cube coordinate `u` with last coordinate `1/2`,
hence is `sliceIncl n v` for the unique `v = sliceRetrFun n u`; sending `x` to
`(x.1.1, sliceRetrFun n x.1.1.2)` and back is a homeomorphism. -/
def slicePreHomeo (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    ↥(pbPre p τ (sliceZ n)) ≃ₜ Work.StemsB.Pullback p (τ.comp (sliceIncl n)) where
  toFun x := ⟨(x.1.1.1, sliceRetrFun n x.1.1.2), by
    have h2 : sliceIncl n (sliceRetrFun n x.1.1.2) = x.1.1.2 :=
      sliceIncl_sliceRetrFun n (x.2 : x.1.1.2 ∈ sliceZ n)
    rw [ContinuousMap.comp_apply, h2]
    exact x.1.2⟩
  invFun y := ⟨⟨(y.1.1, sliceIncl n y.1.2), y.2⟩, by
    show lastCoord (sliceIncl n y.1.2) = 1/2
    exact lastCoord_sliceIncl n y.1.2⟩
  left_inv x := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · rfl
    · exact sliceIncl_sliceRetrFun n (x.2 : x.1.1.2 ∈ sliceZ n)
  right_inv y := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · rfl
    · exact sliceRetrFun_sliceIncl n y.1.2
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ ?_
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
    · exact (continuous_sliceRetrFun n).comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ ?_
    refine Continuous.subtype_mk ?_ ?_
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · exact (sliceIncl n).continuous.comp (continuous_snd.comp continuous_subtype_val)

/-- The homeomorphism `slicePreHomeo` on underlying points: the cube coordinate becomes the
retraction of the cube coordinate. -/
@[simp]
theorem slicePreHomeo_apply_fst (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B))
    (x : ↥(pbPre p τ (sliceZ n))) : (slicePreHomeo n p τ x).1.1 = x.1.1.1 := rfl

@[simp]
theorem slicePreHomeo_apply_snd (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B))
    (x : ↥(pbPre p τ (sliceZ n))) :
    (slicePreHomeo n p τ x).1.2 = sliceRetrFun n x.1.1.2 := rfl

/-- The relative part of the slice pair corresponds to the boundary of the lower-dimensional cube
under `slicePreHomeo`. -/
theorem slicePreHomeo_mem (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B))
    (x : ↥(pbPre p τ (sliceZ n))) :
    x ∈ pbSub p τ (sliceZ n) (sliceZ n ∩ cubeBdryS (n+1)) ↔
      slicePreHomeo n p τ x ∈ pbPre p (τ.comp (sliceIncl n)) (cubeBdryS n) := by
  have hx : x.1.1.2 ∈ sliceZ n := x.2
  have h1 : x ∈ pbSub p τ (sliceZ n) (sliceZ n ∩ cubeBdryS (n+1)) ↔
      x.1.1.2 ∈ cubeBdryS (n+1) := by
    show (x.1.1.2 ∈ sliceZ n ∧ x.1.1.2 ∈ cubeBdryS (n+1)) ↔ x.1.1.2 ∈ cubeBdryS (n+1)
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have h2 : slicePreHomeo n p τ x ∈ pbPre p (τ.comp (sliceIncl n)) (cubeBdryS n) ↔
      sliceRetrFun n x.1.1.2 ∈ cubeBdryS n := by
    show sliceRetrFun n x.1.1.2 ∈ cubeBdryS n ↔ sliceRetrFun n x.1.1.2 ∈ cubeBdryS n
    exact Iff.rfl
  rw [h1, h2]
  exact (sliceRetrFun_mem_cubeBdryS n hx).symm

/-- **The relative homology of the pullback over the middle slice is the relative homology of the
pullback over the boundary of the lower cube.**  This is the passage from the middle slab to the
slice in the E2(d) induction: the two pairs are canonically homeomorphic. -/
theorem slice_pullback_iso (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(Work.Serre.pbPre p τ (Work.Serre.sliceZ n)))
        (Work.Serre.pbSub p τ (Work.Serre.sliceZ n)
          (Work.Serre.sliceZ n ∩ Work.Serre.cubeBdryS (n+1)))).homology m) ≅
      ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p (τ.comp (Work.Serre.sliceIncl n))))
        (Work.Serre.pbPre p (τ.comp (Work.Serre.sliceIncl n)) (Work.Serre.cubeBdryS n))).homology m)) :=
  Work.Cohomology.relChainsHomeomorphCompat
    ↥(pbPre p τ (sliceZ n)) (Work.StemsB.Pullback p (τ.comp (sliceIncl n)))
    (pbSub p τ (sliceZ n) (sliceZ n ∩ cubeBdryS (n+1)))
    (pbPre p (τ.comp (sliceIncl n)) (cubeBdryS n))
    (slicePreHomeo n p τ) (slicePreHomeo_mem n p τ) m

end

end Work.Serre
