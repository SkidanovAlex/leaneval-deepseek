import Mathlib
import Submission.Work.Serre.E2dTools
import Submission.Work.Cohomology.relChainsMapOf_isIso

set_option maxHeartbeats 8000000

/-!
# Auxiliary material for `Work.Serre.middleSlab_to_slice`

The pair `(slabM n, slabM n ∩ ∂I^{n+1})` and the pair `(sliceZ n, sliceZ n ∩ ∂I^{n+1})` are two
"cylindrical" pairs of the cube `I^{n+1}`: `slabM n = {1/4 < x_last < 3/4}` retracts onto the
middle slice `sliceZ n = {x_last = 1/2}` by pushing the last coordinate to `1/2`, and the
retraction preserves the boundary part of the cube.  This file builds the explicit retractions
(`pushSlicePt`) and deduces the compression properties of the two base pairs, which via
`Work.Serre.isZero_relChains_preimage_of_base_compress` give the vanishing of the relative
homology of the corresponding pairs of pullbacks.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The last-coordinate retraction of the cube onto the middle slice -/

/-- The last coordinate of the retraction `pushSlicePt`: the convex combination of the last
coordinate of `u` with the midpoint `1/2`. -/
def pushSliceLast (n : ℕ) (z : Work.Stems.Cubical.IC (n+1) × unitInterval) : unitInterval :=
  ⟨(1 - (z.2 : ℝ)) * ((z.1 (Fin.last n) : unitInterval) : ℝ) + (z.2 : ℝ) * (1/2), by
    have hu := (z.1 (Fin.last n)).2
    have ht := z.2.2
    refine ⟨?_, ?_⟩ <;> nlinarith [hu.1, hu.2, ht.1, ht.2]⟩

/-- **The retraction of the cube onto the middle slice** `{last = 1/2}`: only the last coordinate
moves, linearly from its value to `1/2`. -/
def pushSlicePt (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) (t : unitInterval) :
    Work.Stems.Cubical.IC (n+1) :=
  Fin.snoc (Fin.init u) (pushSliceLast n (u, t))

@[simp] theorem pushSlicePt_castSucc (n : ℕ) (u : Work.Stems.Cubical.IC (n+1))
    (t : unitInterval) (j : Fin n) :
    pushSlicePt n u t (Fin.castSucc j) = u (Fin.castSucc j) := by
  simp only [pushSlicePt, Fin.snoc_castSucc]; rfl

@[simp] theorem pushSlicePt_last (n : ℕ) (u : Work.Stems.Cubical.IC (n+1))
    (t : unitInterval) :
    (pushSlicePt n u t (Fin.last n) : unitInterval) = pushSliceLast n (u, t) := by
  simp only [pushSlicePt, Fin.snoc_last]

@[simp] theorem pushSliceLast_coe (n : ℕ) (u : Work.Stems.Cubical.IC (n+1))
    (t : unitInterval) :
    ((pushSliceLast n (u,t) : unitInterval) : ℝ)
      = (1 - (t : ℝ)) * lastCoord u + (t : ℝ) * (1/2) := rfl

@[simp] theorem lastCoord_pushSlicePt (n : ℕ) (u : Work.Stems.Cubical.IC (n+1))
    (t : unitInterval) :
    lastCoord (pushSlicePt n u t) = (1 - (t : ℝ)) * lastCoord u + (t : ℝ) * (1/2) := by
  rw [lastCoord, pushSlicePt_last, pushSliceLast_coe]

theorem pushSlicePt_zero (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    pushSlicePt n u 0 = u := by
  have h : (pushSliceLast n (u,0) : unitInterval) = u (Fin.last n) := by
    refine Subtype.ext ?_
    rw [pushSliceLast_coe]; simp [lastCoord]
  conv_rhs => rw [← Fin.snoc_init_self u]
  rw [pushSlicePt]; congr 1

theorem pushSlicePt_of_last (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) (t : unitInterval)
    (hu : lastCoord u = 1/2) : pushSlicePt n u t = u := by
  have h : (pushSliceLast n (u,t) : unitInterval) = u (Fin.last n) := by
    refine Subtype.ext ?_
    rw [pushSliceLast_coe, ← hu, lastCoord]; ring
  conv_rhs => rw [← Fin.snoc_init_self u]
  rw [pushSlicePt]; congr 1

theorem pushSlicePt_congr_last {n : ℕ} {u v : Work.Stems.Cubical.IC (n+1)}
    (h : ∀ j : Fin n, u (Fin.castSucc j) = v (Fin.castSucc j))
    (hlast : (u (Fin.last n) : unitInterval) = v (Fin.last n)) : u = v := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact h j
  · exact hlast

theorem pushSlicePt_one_mem_sliceZ (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) :
    pushSlicePt n u 1 ∈ sliceZ n := by
  show lastCoord (pushSlicePt n u 1) = 1/2
  simp only [lastCoord, pushSlicePt_last, pushSliceLast_coe]; norm_num

theorem continuous_pushSliceLast (n : ℕ) :
    Continuous fun z : Work.Stems.Cubical.IC (n+1) × unitInterval => pushSliceLast n z := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun z : Work.Stems.Cubical.IC (n+1) × unitInterval =>
      ((z.1 (Fin.last n) : unitInterval) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_fst)
  have h2 : Continuous fun z : Work.Stems.Cubical.IC (n+1) × unitInterval => (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub h2).mul h1).add (h2.mul continuous_const)

theorem continuous_pushSlicePt (n : ℕ) :
    Continuous fun z : Work.Stems.Cubical.IC (n+1) × unitInterval => pushSlicePt n z.1 z.2 := by
  have hinit : Continuous fun z : Work.Stems.Cubical.IC (n+1) × unitInterval => Fin.init z.1 :=
    continuous_pi fun j => (continuous_apply (Fin.castSucc j)).comp continuous_fst
  exact (continuous_snocSlab n).comp (hinit.prodMk (continuous_pushSliceLast n))

/-! ## The retraction preserves the slab and its boundary part -/

theorem pushSlicePt_mem_slabM (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) (t : unitInterval)
    (hu : u ∈ slabM n) : pushSlicePt n u t ∈ slabM n := by
  refine ⟨?_, ?_⟩ <;> rw [lastCoord_pushSlicePt] <;> nlinarith [hu.1, hu.2, t.2.1, t.2.2]

theorem pushSlicePt_mem_cubeBdry (n : ℕ) (u : Work.Stems.Cubical.IC (n+1)) (t : unitInterval)
    (hu : u ∈ cubeBdryS (n+1)) (hslab : u ∈ slabM n) :
    pushSlicePt n u t ∈ cubeBdryS (n+1) := by
  obtain ⟨i, hi⟩ := hu
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ⟨Fin.castSucc j, by rw [pushSlicePt_castSucc]; exact hi⟩
  · exfalso
    have h1 : lastCoord u = 0 ∨ lastCoord u = 1 := by
      rcases hi with h | h
      · left; rw [lastCoord, h]; rfl
      · right; rw [lastCoord, h]; rfl
    rcases h1 with h | h <;> linarith [hslab.1, hslab.2]

/-! ## The two compression properties -/

/-- The retraction of the middle slab onto the middle slice, as a self-map of `↥(slabM n)`. -/
def slabMHom (n : ℕ) : C(↥(slabM n) × unitInterval, ↥(slabM n)) where
  toFun z := ⟨pushSlicePt n z.1.1 z.2, pushSlicePt_mem_slabM n z.1.1 z.2 z.1.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_pushSlicePt n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) _

/-- **The pair `(slabM n, sliceZ n)` has the compression property.** -/
theorem compressRel_slabM (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(slabM n)
      {x : ↥(slabM n) | (x : Work.Stems.Cubical.IC (n+1)) ∈ sliceZ n} d := by
  intro d
  refine Work.Serre.compressRel_of_deformation (slabMHom n) ?_ ?_ ?_ d
  · intro y; exact Subtype.ext (pushSlicePt_zero n y.1)
  · intro y; exact pushSlicePt_one_mem_sliceZ n y.1
  · intro y hy t; exact Subtype.ext (pushSlicePt_of_last n y.1 t hy)

/-- The retraction of the boundary part of the middle slab onto the boundary part of the middle
slice, as a self-map of `↥(slabM n ∩ ∂I^{n+1})`. -/
def slabBdHom (n : ℕ) :
    C(↥(slabM n ∩ cubeBdryS (n+1)) × unitInterval, ↥(slabM n ∩ cubeBdryS (n+1))) where
  toFun z := ⟨pushSlicePt n z.1.1 z.2,
    ⟨pushSlicePt_mem_slabM n z.1.1 z.2 z.1.2.1,
     pushSlicePt_mem_cubeBdry n z.1.1 z.2 z.1.2.2 z.1.2.1⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_pushSlicePt n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) _

/-- **The pair `(slabM n ∩ ∂I^{n+1}, sliceZ n ∩ ∂I^{n+1})` has the compression property.** -/
theorem compressRel_slabBd (n : ℕ) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(slabM n ∩ cubeBdryS (n+1))
      {x : ↥(slabM n ∩ cubeBdryS (n+1)) |
        (x : Work.Stems.Cubical.IC (n+1)) ∈ sliceZ n ∩ cubeBdryS (n+1)} d := by
  intro d
  refine Work.Serre.compressRel_of_deformation (slabBdHom n) ?_ ?_ ?_ d
  · intro y; exact Subtype.ext (pushSlicePt_zero n y.1)
  · intro y
    exact ⟨pushSlicePt_one_mem_sliceZ n y.1,
      pushSlicePt_mem_cubeBdry n y.1 1 y.2.2 y.2.1⟩
  · intro y hy t; exact Subtype.ext (pushSlicePt_of_last n y.1 t hy.1)

/-- The boundary part of the middle slice sits inside the boundary part of the middle slab. -/
theorem sliceZ_inter_bdry_subset_slabM_inter_bdry (n : ℕ) :
    sliceZ n ∩ cubeBdryS (n+1) ⊆ slabM n ∩ cubeBdryS (n+1) :=
  fun _x hx => ⟨sliceZ_subset_slabM n hx.1, hx.2⟩


end

end Work.Serre

namespace Work.Serre

noncomputable section

/-! ## Elementary homeomorphisms of subtypes -/

/-- The inclusion of `S` in `T`, as a homeomorphism onto its image
`{x : ↥T | (x : α) ∈ S}`. -/
def inclSubtypeHomeo {α : Type*} [TopologicalSpace α] {S T : Set α} (h : S ⊆ T) :
    ↥S ≃ₜ ↥{x : ↥T | (x : α) ∈ S} where
  toFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun x => h x.2)) (fun x => x.2)
  continuous_invFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

/-- Exchanging the two defining predicates of a doubly nested subtype. -/
def subtypeSwapHomeo {α : Type*} [TopologicalSpace α] (S T : Set α) :
    ↥{x : ↥S | (x : α) ∈ T} ≃ₜ ↥{y : ↥T | (y : α) ∈ S} where
  toFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  invFun b := ⟨⟨b.1.1, b.2⟩, b.1.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext (Subtype.ext rfl)
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
        (fun a => a.2)) (fun a => a.1.2)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
        (fun b => b.2)) (fun b => b.1.2)

/-- Vanishing of relative homology is transported along a homeomorphism of pairs. -/
theorem isZero_relChains_of_homeomorph {X Y : TopCat} (e : ↑X ≃ₜ ↑Y) {A : Set ↑X} {B : Set ↑Y}
    (h : ∀ x, x ∈ A ↔ e x ∈ B)
    (hB : ∀ m, IsZero ((Work.Cohomology.relChains Y B).homology m)) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains X A).homology m) := by
  obtain ⟨iso⟩ := Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph e A B h m
  exact IsZero.of_iso (hB m) iso

end

end Work.Serre

namespace Work.Serre

noncomputable section

/-! ## The sets of the pullback used by the comparison -/

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The pullback over the middle slab. -/
abbrev pbSL (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set (Work.StemsB.Pullback p τ) := pbPre p τ (slabM n)

/-- The pullback over the middle slice. -/
abbrev pbSZ (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set (Work.StemsB.Pullback p τ) := pbPre p τ (sliceZ n)

/-- The pullback over the boundary part of the middle slab. -/
abbrev pbAL (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set (Work.StemsB.Pullback p τ) := pbPre p τ (slabM n ∩ cubeBdryS (n+1))

/-- The pullback over the boundary part of the middle slice. -/
abbrev pbAZ (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set (Work.StemsB.Pullback p τ) := pbPre p τ (sliceZ n ∩ cubeBdryS (n+1))

/-- The slice inside the slab, as a subset of the slab pullback. -/
abbrev pbF (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set ↥(pbSL n p τ) := pbSub p τ (slabM n) (sliceZ n)

/-- The boundary part of the slab pullback. -/
abbrev pbA1 (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set ↥(pbSL n p τ) := pbSub p τ (slabM n) (slabM n ∩ cubeBdryS (n+1))

/-- The boundary part of the slice pullback. -/
abbrev pbB2 (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set ↥(pbSZ n p τ) := pbSub p τ (sliceZ n) (sliceZ n ∩ cubeBdryS (n+1))

/-- The boundary part of the slice, inside the boundary part of the slab pullback. -/
abbrev pbZ2 (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set ↥(pbAL n p τ) := {z | (z : Work.StemsB.Pullback p τ) ∈ pbAZ n p τ}

/-- The boundary part of the slice, inside the slice pullback, viewed as a subset of the slice
inside the slab. -/
abbrev pbA' (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set ↥(pbF n p τ) := {a | (a : ↥(pbSL n p τ)) ∈ pbA1 n p τ}

/-- The slice inside the slab, viewed inside the boundary part of the slab pullback. -/
abbrev pbG (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    Set ↥(pbA1 n p τ) := {b | (b : ↥(pbSL n p τ)) ∈ pbF n p τ}

open scoped Topology in
/-- The slice pullback sits inside the slab pullback. -/
theorem pbSZ_subset_pbSL (n : ℕ) (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) : pbSZ n p τ ⊆ pbSL n p τ :=
  fun x hx => sliceZ_subset_slabM n hx

open scoped Topology in
/-- The boundary part of the slice pullback sits inside the boundary part of the slab pullback. -/
theorem pbAZ_subset_pbAL (n : ℕ) (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) : pbAZ n p τ ⊆ pbAL n p τ :=
  fun x hx => ⟨sliceZ_subset_slabM n hx.1, hx.2⟩

open scoped Topology in
/-- The boundary part of the slab pullback sits inside the slab pullback. -/
theorem pbAL_subset_pbSL (n : ℕ) (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) : pbAL n p τ ⊆ pbSL n p τ :=
  fun x hx => hx.1

/-! ## The two vanishings -/

/-- **The pair `(slab pullback, slice pullback)` has vanishing relative homology.** -/
theorem isZero_relChains_pbF (n : ℕ) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbSL n p τ)) (pbF n p τ)).homology m) := by
  have h := Work.Serre.isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ)
    (fun i => Work.StemsB.hasHLP_pullback p τ (hp i)) (sliceZ n) (slabM n)
    (sliceZ_subset_slabM n) (fun d => compressRel_slabM n d) m
  exact h

/-- **The pair of boundary pullbacks has vanishing relative homology.** -/
theorem isZero_relChains_pbZ2 (n : ℕ) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbAL n p τ)) (pbZ2 n p τ)).homology m) := by
  have h := Work.Serre.isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ)
    (fun i => Work.StemsB.hasHLP_pullback p τ (hp i))
    (sliceZ n ∩ cubeBdryS (n+1)) (slabM n ∩ cubeBdryS (n+1))
    (sliceZ_inter_bdry_subset_slabM_inter_bdry n) (fun d => compressRel_slabBd n d) m
  exact h

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The boundary part of the slice pullback, included in the boundary part of the slab pullback
as a homeomorphism onto its image. -/
def inclA1 (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    ↥(pbA1 n p τ) ≃ₜ ↥(pbAL n p τ) where
  toFun b := ⟨b.1.1, b.2⟩
  invFun z := ⟨⟨z.1, (pbAL_subset_pbSL n p τ) z.2⟩, z.2⟩
  left_inv b := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun b => b.2)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun z => (pbAL_subset_pbSL n p τ) z.2))
      (fun z => z.2)

/-- The slice pullback, included in the slab pullback as a homeomorphism onto its image. -/
def inclSZ (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    ↥(pbSZ n p τ) ≃ₜ ↥(pbF n p τ) where
  toFun z := ⟨⟨z.1, (pbSZ_subset_pbSL n p τ) z.2⟩, z.2⟩
  invFun a := ⟨a.1.1, a.2⟩
  left_inv z := Subtype.ext rfl
  right_inv a := Subtype.ext (Subtype.ext rfl)
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun z => (pbSZ_subset_pbSL n p τ) z.2))
      (fun z => z.2)
  continuous_invFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.2)

/-- The exchange of the two defining predicates of the doubly nested subtypes `pbA'` and `pbG`. -/
def swapA (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    ↥(pbA' n p τ) ≃ₜ ↥(pbG n p τ) where
  toFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  invFun b := ⟨⟨b.1.1, b.2⟩, b.1.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext (Subtype.ext rfl)
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
        (fun a => a.2)) (fun a => a.1.2)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
        (fun b => b.2)) (fun b => b.1.2)

/-- The boundary part of the slice, inside the boundary part of the slab pullback, has vanishing
relative homology. -/
theorem isZero_relChains_pbG (n : ℕ) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbA1 n p τ)) (pbG n p τ)).homology m) :=
  isZero_relChains_of_homeomorph (X := TopCat.of ↥(pbA1 n p τ)) (Y := TopCat.of ↥(pbAL n p τ))
    (A := pbG n p τ) (B := pbZ2 n p τ) (inclA1 n p τ)
    (fun b => ⟨fun hb => ⟨hb, b.2.2⟩, fun hb => hb.1⟩)
    (isZero_relChains_pbZ2 n p hp τ) m

/-- The map of pairs from `(slice pullback, boundary part)` to `(slab pullback, boundary part)`,
as the composite of the swap homeomorphism with the inclusion of the boundary part of the slab
pullback. -/
def gMap (n : ℕ) (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC (n+1), B)) :
    TopCat.of ↥(pbA' n p τ) ⟶ TopCat.of ↥(pbA1 n p τ) :=
  Work.StemsB.sphHomeoHom (swapA n p τ)
    ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(pbA1 n p τ)) (pbG n p τ)

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The comparison map on the boundary parts is a homology isomorphism.** -/
theorem isIso_chainMap_gMap (n : ℕ) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥(pbA' n p τ)) (TopCat.of ↥(pbA1 n p τ))
        (gMap n p τ)) k) := by
  haveI h1c : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of ↥(pbA' n p τ))
      (TopCat.of ↥(pbG n p τ)) (Work.StemsB.sphHomeoHom (swapA n p τ))) :=
    Work.StemsB.isIso_chainMap_sphHomeoHom (X := TopCat.of ↥(pbA' n p τ))
      (Y := TopCat.of ↥(pbG n p τ)) (swapA n p τ)
  haveI h1 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pbA' n p τ)) (TopCat.of ↥(pbG n p τ))
      (Work.StemsB.sphHomeoHom (swapA n p τ))) k) :=
    Functor.map_isIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k)
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥(pbA' n p τ)) (TopCat.of ↥(pbG n p τ))
        (Work.StemsB.sphHomeoHom (swapA n p τ)))
  haveI h2 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pbG n p τ)) (TopCat.of ↥(pbA1 n p τ))
      (Work.Cohomology.subtypeIncl (TopCat.of ↥(pbA1 n p τ)) (pbG n p τ))) k) :=
    Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains
      (Y := TopCat.of ↥(pbA1 n p τ)) (pbG n p τ) (isZero_relChains_pbG n p hp τ) k
  have hfac : Work.Cohomology.chainMap ℤ (TopCat.of ↥(pbA' n p τ)) (TopCat.of ↥(pbA1 n p τ))
        (gMap n p τ)
      = Work.Cohomology.chainMap ℤ (TopCat.of ↥(pbA' n p τ)) (TopCat.of ↥(pbG n p τ))
          (Work.StemsB.sphHomeoHom (swapA n p τ))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(pbG n p τ)) (TopCat.of ↥(pbA1 n p τ))
          (Work.Cohomology.subtypeIncl (TopCat.of ↥(pbA1 n p τ)) (pbG n p τ)) := by
    rw [gMap]
    exact (Work.StemsB.chainMap_comp _ _).symm
  rw [hfac, HomologicalComplex.homologyMap_comp]
  exact inferInstance

/-- **The comparison isomorphism** between the relative homology of the pair over the middle slab
and that of the pair over the middle slice. -/
theorem pbSL_SZ_iso (n : ℕ) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(pbSL n p τ)) (pbA1 n p τ)).homology m) ≅
      ((Work.Cohomology.relChains (TopCat.of ↥(pbSZ n p τ)) (pbB2 n p τ)).homology m)) := by
  have hw : Work.Cohomology.subtypeIncl (TopCat.of ↥(pbF n p τ)) (pbA' n p τ)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(pbSL n p τ)) (pbF n p τ)
      = gMap n p τ ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(pbSL n p τ)) (pbA1 n p τ) := by
    apply TopCat.ext
    intro a
    rfl
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pbF n p τ)) (TopCat.of ↥(pbSL n p τ))
      (Work.Cohomology.subtypeIncl (TopCat.of ↥(pbSL n p τ)) (pbF n p τ))) k) := fun k =>
    Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains
      (Y := TopCat.of ↥(pbSL n p τ)) (pbF n p τ) (isZero_relChains_pbF n p hp τ) k
  have hg : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(pbA' n p τ)) (TopCat.of ↥(pbA1 n p τ)) (gMap n p τ)) k) := fun k =>
    isIso_chainMap_gMap n p hp τ k
  set R := Work.Cohomology.relChainsMapOf (X := TopCat.of ↥(pbF n p τ))
    (Y := TopCat.of ↥(pbSL n p τ)) (pbA' n p τ) (pbA1 n p τ)
    (Work.Cohomology.subtypeIncl (TopCat.of ↥(pbSL n p τ)) (pbF n p τ)) (gMap n p τ) hw
    with hRdef
  haveI h5 : IsIso (HomologicalComplex.homologyMap R m) :=
    Work.Cohomology.relChainsMapOf_isIso (X := TopCat.of ↥(pbF n p τ))
      (Y := TopCat.of ↥(pbSL n p τ)) (pbA' n p τ) (pbA1 n p τ)
      (Work.Cohomology.subtypeIncl (TopCat.of ↥(pbSL n p τ)) (pbF n p τ)) (gMap n p τ) hw m hf hg
  have hcond : ∀ z : ↥(pbSZ n p τ), z ∈ pbB2 n p τ ↔ inclSZ n p τ z ∈ pbA' n p τ := by
    intro z
    have hz : Work.StemsB.pullbackSnd p τ z.1 ∈ sliceZ n := z.2
    exact ⟨fun h => ⟨sliceZ_subset_slabM n h.1, h.2⟩, fun h => ⟨hz, h.2⟩⟩
  obtain ⟨q⟩ := Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
    (X := TopCat.of ↥(pbSZ n p τ)) (Y := TopCat.of ↥(pbF n p τ))
    (inclSZ n p τ) (pbB2 n p τ) (pbA' n p τ) hcond m
  exact ⟨(asIso (HomologicalComplex.homologyMap R m)).symm ≪≫ q.symm⟩

end

end Work.Serre
