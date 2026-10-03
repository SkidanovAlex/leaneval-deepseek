import Mathlib
import Submission.Work.OROneRel.presentedGroup_union_amalgam

/-!
# The `N = 1` normal form of the line amalgam

This file isolates the **single-amalgam-step** content that the iteration used for the line of band
domains (`π₁ (⋃_{|k| ≤ N} D_k)`) needs, standing on the already proved finite Seifert--van Kampen
`Work.OROneRel.presentedGroup_union_amalgam` and on Mathlib's amalgamated-product normal form
(`Monoid.PushoutI.Reduced`, `of_injective`, `base_injective`, `inf_of_range_eq_base_range`).

For a union `Γ = A ∪ B` of two `2`-complexes with edge sets `E₁`, `E₂` covering `E`, relator sets
`S₁`, `S₂` and `S₀` (of the intersection) mapping into both, the comparison map

  `ugOut : π₁(A) ∗_{π₁(A ∩ B)} π₁(B) →* π₁(Γ)`

of `presentedGroup_union_amalgam` is an **isomorphism**, and the two facts that make the *iteration*
work are recorded here:

* `Work.OROneRel.unionAmalgam_range_inf` — **the two vertex groups intersect exactly in the edge
  group**, `π₁(A) ⊓ π₁(B) = π₁(A ∩ B)` inside `π₁(Γ)`.  This is the `N = 1` form of
  `Monoid.PushoutI.inf_of_range_eq_base_range` transported along `ugOut`, and is what lets one glue
  a further domain onto `π₁(P_N)` along the *same* gate.
* `Work.OROneRel.unionAmalgam_reduced_ne_one` — **the normal form**: an element of the union
  represented by an alternating reduced word in the two vertex groups, which is not the empty word,
  is non-trivial (Mathlib's `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`, i.e. Britton for
  amalgams).  Iterated along the line this is exactly the "Britton normal form for `(H, τ)`".

Both statements are alphabet-general: they mention only `E`, `E₁`, `E₂`, `S₀`, `S₁`, `S₂`, so they
can be instantiated for the band domains `D_k = winE c k (k + pq)` (with `S₀ = ∅`: the gates carry
no `2`-cell) without importing the window machinery.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {E : Type u}
variable (E₁ E₂ : Set E)
variable (S₁ : Set (FreeGroup ↥E₁)) (S₂ : Set (FreeGroup ↥E₂)) (S₀ : Set (FreeGroup ↥(E₁ ∩ E₂)))
variable (h₁ : FreeGroup.map (inc₁ E₁ E₂) '' S₀ ⊆ S₁)
variable (h₂ : FreeGroup.map (inc₂ E₁ E₂) '' S₀ ⊆ S₂)

/-- **The comparison map of the union is injective** (it is an isomorphism by
`presentedGroup_union_amalgam`, with inverse `ugIn`). -/
theorem ugOut_injective (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    Function.Injective (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) := by
  intro x y hxy
  have hx : ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ x) = x :=
    DFunLike.congr_fun (ugIn_comp_ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) x
  have hy : ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ y) = y :=
    DFunLike.congr_fun (ugIn_comp_ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) y
  rw [← hx, ← hy, hxy]

/-- The composite of `ugOut` with the first vertex inclusion is the map induced by `E₁ ↪ E`. -/
theorem ugOut_comp_of_false :
    (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂).comp
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false) =
      presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂) := by
  ext g
  simp only [MonoidHom.comp_apply]
  exact ugOut_of_false E₁ E₂ S₁ S₂ S₀ h₁ h₂ g

/-- The composite of `ugOut` with the second vertex inclusion is the map induced by `E₂ ↪ E`. -/
theorem ugOut_comp_of_true :
    (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂).comp
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true) =
      presentedMap (incVal E₂) (ugSubset₂ E₁ E₂ S₁ S₂) := by
  ext g
  simp only [MonoidHom.comp_apply]
  exact ugOut_of_true E₁ E₂ S₁ S₂ S₀ h₁ h₂ g

/-- The two ways of reading a generator of the intersection (`E₁` first, then `E₂`) agree, i.e. the
composition of the `presentedMap` into the first vertex with the first amalgamating map is the map
induced by `E₁ ∩ E₂ ↪ E`. -/
theorem presentedMap_comp_gate :
    (presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂)).comp
        (presentedMap (inc₁ E₁ E₂) h₁) =
      presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁) := by
  refine presentedGroup_hom_ext fun y => ?_
  simp only [MonoidHom.comp_apply, presentedMap_of]
  rfl

/-- The composite of `ugOut` with the base inclusion is the map induced by `E₁ ∩ E₂ ↪ E`. -/
theorem ugOut_comp_base :
    (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂).comp
        (Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)) =
      presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁) := by
  have h1 : Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) =
      (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false).comp
        (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂ false) :=
    (Monoid.PushoutI.of_comp_eq_base (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false).symm
  rw [h1, ← MonoidHom.comp_assoc, ugOut_comp_of_false E₁ E₂ S₁ S₂ S₀ h₁ h₂]
  exact presentedMap_comp_gate E₁ E₂ S₁ S₂ S₀ h₁

/-- **The two vertex groups of the union intersect exactly in the edge group.**

This is the `N = 1` form of `Monoid.PushoutI.inf_of_range_eq_base_range`, transported along the
isomorphism `ugOut` of `presentedGroup_union_amalgam`.  It is the datum that lets one glue a further
domain onto `π₁(A ∪ B)` along the *same* gate. -/
theorem unionAmalgam_range_inf (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂)
    (hφ : ∀ i, Function.Injective (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂ i)) :
    (presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂)).range ⊓
        (presentedMap (incVal E₂) (ugSubset₂ E₁ E₂ S₁ S₂)).range =
      (presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁)).range := by
  have hinj : Function.Injective (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) :=
    ugOut_injective E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE
  have hfalse :
      (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false).range.map
          (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) =
        (presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂)).range := by
    rw [MonoidHom.map_range]
    exact congrArg MonoidHom.range (ugOut_comp_of_false E₁ E₂ S₁ S₂ S₀ h₁ h₂)
  have htrue :
      (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true).range.map
          (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) =
        (presentedMap (incVal E₂) (ugSubset₂ E₁ E₂ S₁ S₂)).range := by
    rw [MonoidHom.map_range]
    exact congrArg MonoidHom.range (ugOut_comp_of_true E₁ E₂ S₁ S₂ S₀ h₁ h₂)
  have hbase :
      (Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)).range.map
          (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) =
        (presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁)).range := by
    rw [MonoidHom.map_range]
    exact congrArg MonoidHom.range (ugOut_comp_base E₁ E₂ S₁ S₂ S₀ h₁ h₂)
  have hkey : (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false).range ⊓
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true).range =
      (Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)).range :=
    Monoid.PushoutI.inf_of_range_eq_base_range (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) hφ
      (i := false) (j := true) (by decide)
  have hmap := congrArg (fun H : Subgroup (Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)) =>
      H.map (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂)) hkey
  rw [Subgroup.map_inf _ _ _ hinj] at hmap
  rw [hfalse, htrue, hbase] at hmap
  exact hmap

/-- **The normal form of the `N = 1` amalgam** (Britton for amalgams, in the `π₁(Γ)` world).

An element of the amalgam `π₁(Γ)`, represented through `ugOut` by an *alternating reduced* word of
the two vertex groups which is not the empty word, is non-trivial.  This is
`Monoid.PushoutI.Reduced.eq_empty_of_mem_range` (a reduced non-empty word is not in the base group)
transported along `ugOut`, using that `1` lies in the base group. -/
theorem unionAmalgam_reduced_ne_one (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂)
    (hφ : ∀ i, Function.Injective (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂ i))
    (w : Monoid.CoprodI.Word (UGFam E₁ E₂ S₁ S₂))
    (hw : Monoid.PushoutI.Reduced (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) w)
    (hne : w.toList ≠ []) :
    ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ (Monoid.PushoutI.ofCoprodI w.prod) ≠ 1 := by
  intro h
  have hone : Monoid.PushoutI.ofCoprodI w.prod = 1 :=
    ugOut_injective E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (by rw [h, map_one])
  have hmem : Monoid.PushoutI.ofCoprodI w.prod ∈
      (Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)).range := by
    rw [hone]
    exact Subgroup.one_mem _
  have hempty : w = Monoid.CoprodI.Word.empty :=
    Monoid.PushoutI.Reduced.eq_empty_of_mem_range
      (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) hφ hw hmem
  exact hne (by rw [hempty]; rfl)

end Work.OROneRel
