import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.epi_singularCohomologyMap_zero
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.UnitSphere
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.mkToVkRangeHomeomorph
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Milnor.cohomology_Mk_minus_two
import Submission.Work.Cohomology.isZeroRelCohomologyZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cohomology of the pair `(Vk(-2), Mk(-2))`

`Submission.Milnor.Vk k` is the total space of the open disc bundle of Milnor's rank-`4` real
vector bundle `ξ` over `S⁴`, and `Work.Milnor.mkToVkFun k : Mk k → Vk k` includes the unit sphere
bundle.  This file computes the **relative** cohomology of the pair

  `Hⁿ(Vk(-2), Mk(-2); ℤ)`,

the groups of the Thom class: they are `ℤ` in degrees `4` and `8` and vanish otherwise.

## The argument

Let `X = Vk(-2)`, `A = mkToVkFun (-2) '' Mk(-2)`.  The total space is homotopy equivalent to `S⁴`
(the disc bundle retracts to its zero section, `Work.Milnor.cohomology_Vk`) and the sphere bundle
`A` is homeomorphic to `Mk(-2)`, hence by `Work.Milnor.mk_minus_two_homeo` homotopy equivalent to
`S⁷` (`Work.Milnor.cohomology_Mk_minus_two`).  So

* `Hᵐ(X) = 0` for `m ∉ {0,4}`, `H⁰(X) = H⁴(X) = ℤ`;
* `Hᵐ(A) = 0` for `m ∉ {0,7}`, `H⁰(A) = H⁷(A) = ℤ`.

The long exact sequence of the pair (`Work.Cohomology.pair_exact₁/₂/₃`)

  `⋯ → Hᵐ(X,A) → Hᵐ(X) → Hᵐ(A) → Hᵐ⁺¹(X,A) → ⋯`

then gives the result:

* `H⁰(X,A) = 0`: `H⁰(X,A)` is the kernel of the pullback `H⁰(X) → H⁰(A)`, and a degree-`0`
  cocycle of a path-connected space vanishing on the non-empty set `A` is zero
  (`Work.Cohomology.isZeroRelCohomologyZero` directly computes this group).
* `H¹(X,A) = 0`: the pullback `H⁰(X) → H⁰(A)` is surjective because `A` is path connected
  (`Work.Cohomology.epi_singularCohomologyMap_zero`), so the connecting map `H⁰(A) → H¹(X,A)`
  is an epimorphism; its image is killed by `H¹(X) = 0`.
* `H⁴(X,A) ≅ ℤ` and `H⁸(X,A) ≅ ℤ`: the two outer terms of `H⁴(X,A) → H⁴(X) → H⁴(A)` and of
  `H⁷(A) → H⁸(X,A) → H⁸(X)` vanish, so the relevant map of the sequence is an isomorphism.
* all other degrees: the group is squeezed between two vanishing terms of the sequence.
-/

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Limits

set_option linter.style.haveILetI false

noncomputable section

/-- The total space `Vk (-2)` of Milnor's disc bundle, as a topological space. -/
abbrev vkPairX : TopCat := TopCat.of (Submission.Milnor.Vk (-2))

/-- The unit sphere bundle `Mk (-2) ⊆ Vk (-2)`, as a subset. -/
abbrev vkPairA : Set (Submission.Milnor.Vk (-2)) := Set.range (Work.Milnor.mkToVkFun (-2))

/-! ## Small general helpers -/

/-- A homeomorphism transports path connectedness. -/
lemma pathConnectedSpace_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) [PathConnectedSpace β] : PathConnectedSpace α := by
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set β) := pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (e.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective e.symm.surjective] at h2

/-- Exactness of a short complex of `ℤ`-modules, read on the underlying linear maps. -/
lemma exact_range_eq_ker {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact) :
    (ModuleCat.Hom.hom S.f).range = (ModuleCat.Hom.hom S.g).ker :=
  ShortComplex.Exact.moduleCat_range_eq_ker h

/-- The middle term of a short exact sequence with vanishing outer terms vanishes. -/
lemma isZero_of_exact_of_isZero_of_isZero {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact)
    (h1 : IsZero S.X₁) (h3 : IsZero S.X₃) : IsZero S.X₂ := by
  have hf0 : ModuleCat.Hom.hom S.f = 0 := by rw [h1.eq_of_src S.f 0, ModuleCat.hom_zero]
  have hg0 : ModuleCat.Hom.hom S.g = 0 := by rw [h3.eq_of_tgt S.g 0, ModuleCat.hom_zero]
  have hrk := ShortComplex.Exact.moduleCat_range_eq_ker h
  rw [hf0, hg0, LinearMap.range_zero, LinearMap.ker_zero] at hrk
  haveI : Subsingleton ↥S.X₂ := ⟨fun a b => by
    have ha : a = 0 := (Submodule.mem_bot ℤ).mp (by rw [hrk]; exact Submodule.mem_top)
    have hb : b = 0 := (Submodule.mem_bot ℤ).mp (by rw [hrk]; exact Submodule.mem_top)
    rw [ha, hb]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The second arrow of a short exact sequence with vanishing source is a monomorphism. -/
lemma mono_of_exact_of_isZero_src {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact)
    (h1 : IsZero S.X₁) : Mono S.g :=
  (ShortComplex.exact_iff_mono S (h1.eq_of_src S.f 0)).mp h

/-- The first arrow of a short exact sequence with vanishing target is an epimorphism. -/
lemma epi_of_exact_of_isZero_tgt {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact)
    (h3 : IsZero S.X₃) : Epi S.f :=
  (ShortComplex.exact_iff_epi S (h3.eq_of_tgt S.g 0)).mp h

/-! ## The computation -/

private theorem cohomologyPairVk_aux (n : ℕ) :
    Nonempty (relCohomology ℤ vkPairX vkPairA n ≅
      ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 8 then 1 else 0)) → ℤ)) := by
  -- `Mk (-2)` is path connected (it is homeomorphic to `S⁷`)
  haveI hpcSph : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) :=
    Work.Milnor.pathConnectedSpace_sphere8
  haveI hpcMk : PathConnectedSpace (Submission.Milnor.Mk (-2)) :=
    pathConnectedSpace_of_homeomorph Work.Milnor.mk_minus_two_homeo.some
  -- the unit sphere bundle is homeomorphic to `Mk (-2)`
  obtain ⟨hmk⟩ := Work.Milnor.mkToVkRangeHomeomorph (-2)
  haveI hpcA : PathConnectedSpace ↥vkPairA := pathConnectedSpace_of_homeomorph hmk.symm
  have hneA : vkPairA.Nonempty := by
    haveI : Nonempty (Submission.Milnor.Mk (-2)) := PathConnectedSpace.nonempty
    exact Set.range_nonempty (Work.Milnor.mkToVkFun (-2))
  -- the cohomology of `Vk (-2)` (homotopy equivalent to `S⁴`)
  have hB : ∀ m : ℕ, m ≠ 0 → m ≠ 4 → IsZero (singularCohomology ℤ m vkPairX) := by
    intro m hm0 hm4
    obtain ⟨e⟩ := Work.Milnor.cohomology_Vk (-2) m
    have hfin : (if m = 0 then 1 else 0) + (if m = 4 then 1 else 0) = 0 := by
      rw [if_neg hm0, if_neg hm4, add_zero]
    have hz : IsZero (ModuleCat.of ℤ
        (Fin ((if m = 0 then 1 else 0) + (if m = 4 then 1 else 0)) → ℤ)) := by
      rw [hfin, ModuleCat.isZero_iff_subsingleton]
      infer_instance
    exact IsZero.of_iso hz e
  -- the cohomology of the unit sphere bundle (homeomorphic to `Mk (-2) ≃ S⁷`)
  have hA : ∀ m : ℕ, Nonempty (singularCohomology ℤ m (TopCat.of vkPairA) ≅
      ModuleCat.of ℤ (Fin ((if m = 0 then 1 else 0) + (if m = 7 then 1 else 0)) → ℤ)) := by
    intro m
    obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv hmk.symm.toHomotopyEquiv m
    exact ⟨e ≪≫ (Work.Milnor.cohomology_Mk_minus_two m).some⟩
  have hC : ∀ m : ℕ, m ≠ 0 → m ≠ 7 →
      IsZero (singularCohomology ℤ m (TopCat.of vkPairA)) := by
    intro m hm0 hm7
    obtain ⟨e⟩ := hA m
    have hfin : (if m = 0 then 1 else 0) + (if m = 7 then 1 else 0) = 0 := by
      rw [if_neg hm0, if_neg hm7, add_zero]
    have hz : IsZero (ModuleCat.of ℤ
        (Fin ((if m = 0 then 1 else 0) + (if m = 7 then 1 else 0)) → ℤ)) := by
      rw [hfin, ModuleCat.isZero_iff_subsingleton]
      infer_instance
    exact IsZero.of_iso hz e
  -- the vanishing finite-arrow module
  have hzFin : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    infer_instance
  rcases eq_or_ne n 0 with rfl | hn0
  · -- degree `0`
    have hidx : (if (0 : ℕ) = 4 then 1 else 0) + (if (0 : ℕ) = 8 then 1 else 0) = 0 := by
      norm_num
    rw [hidx]
    haveI : PathConnectedSpace vkPairX := Work.Milnor.pathConnectedSpace_Vk (-2)
    exact ⟨IsZero.iso (isZeroRelCohomologyZero vkPairX vkPairA hneA) hzFin⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · -- degree `1`
    have hidx : (if (1 : ℕ) = 4 then 1 else 0) + (if (1 : ℕ) = 8 then 1 else 0) = 0 := by
      norm_num
    rw [hidx]
    haveI hEpi : Epi (HomologicalComplex.homologyMap (restr ℤ vkPairX vkPairA) 0) :=
      epi_singularCohomologyMap_zero (subtypeIncl vkPairX vkPairA)
    have hδepi : Epi (pairδ ℤ vkPairX vkPairA 0) :=
      epi_of_exact_of_isZero_tgt (pair_exact₁ ℤ vkPairX vkPairA 0)
        (hB 1 (by norm_num) (by norm_num))
    have hkerδ : (ModuleCat.Hom.hom (pairδ ℤ vkPairX vkPairA 0)).ker = ⊤ := by
      rw [← exact_range_eq_ker (pair_exact₃ ℤ vkPairX vkPairA 0)]
      exact LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp hEpi)
    have hδ0 : (ModuleCat.Hom.hom (pairδ ℤ vkPairX vkPairA 0)) = 0 :=
      LinearMap.ker_eq_top.mp hkerδ
    have hsurjδ : Function.Surjective (ModuleCat.Hom.hom (pairδ ℤ vkPairX vkPairA 0)) :=
      (ModuleCat.epi_iff_surjective _).mp hδepi
    have hz1 : IsZero (relCohomology ℤ vkPairX vkPairA 1) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, hx⟩ := hsurjδ a
      obtain ⟨y, hy⟩ := hsurjδ b
      rw [← hx, ← hy, hδ0]
      simp
    exact ⟨IsZero.iso hz1 hzFin⟩
  rcases eq_or_ne n 4 with rfl | hn4
  · -- degree `4`
    have hidx : (if (4 : ℕ) = 4 then 1 else 0) + (if (4 : ℕ) = 8 then 1 else 0) = 1 := by
      norm_num
    rw [hidx]
    haveI : Mono (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) :=
      mono_of_exact_of_isZero_src (pair_exact₁ ℤ vkPairX vkPairA 3)
        (hC 3 (by norm_num) (by norm_num))
    haveI : Epi (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) :=
      epi_of_exact_of_isZero_tgt (pair_exact₂ ℤ vkPairX vkPairA 4)
        (hC 4 (by norm_num) (by norm_num))
    haveI : IsIso (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) :=
      isIso_of_mono_of_epi _
    obtain ⟨eB⟩ := Work.Milnor.cohomology_Vk (-2) 4
    have hidxB : (if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0) = 1 := by
      norm_num
    rw [hidxB] at eB
    exact ⟨asIso (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) ≪≫ eB⟩
  rcases eq_or_ne n 8 with rfl | hn8
  · -- degree `8`
    have hidx : (if (8 : ℕ) = 4 then 1 else 0) + (if (8 : ℕ) = 8 then 1 else 0) = 1 := by
      norm_num
    rw [hidx]
    haveI : Mono (pairδ ℤ vkPairX vkPairA 7) :=
      mono_of_exact_of_isZero_src (pair_exact₃ ℤ vkPairX vkPairA 7)
        (hB 7 (by norm_num) (by norm_num))
    haveI : Epi (pairδ ℤ vkPairX vkPairA 7) :=
      epi_of_exact_of_isZero_tgt (pair_exact₁ ℤ vkPairX vkPairA 7)
        (hB 8 (by norm_num) (by norm_num))
    haveI : IsIso (pairδ ℤ vkPairX vkPairA 7) := isIso_of_mono_of_epi _
    obtain ⟨eC⟩ := hA 7
    have hidxC : (if (7 : ℕ) = 0 then 1 else 0) + (if (7 : ℕ) = 7 then 1 else 0) = 1 := by
      norm_num
    rw [hidxC] at eC
    exact ⟨(asIso (pairδ ℤ vkPairX vkPairA 7)).symm ≪≫ eC⟩
  · -- all remaining degrees `n ≥ 2`, `n ≠ 4, 8`
    have hn2 : 2 ≤ n := by omega
    have hidx : (if n = 4 then 1 else 0) + (if n = 8 then 1 else 0) = 0 := by
      rw [if_neg hn4, if_neg hn8, add_zero]
    rw [hidx]
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hzC : IsZero (singularCohomology ℤ (n - 1) (TopCat.of vkPairA)) :=
      hC (n - 1) (by omega) (by omega)
    have hzB : IsZero (singularCohomology ℤ (n - 1 + 1) vkPairX) :=
      hB (n - 1 + 1) (by omega) (by omega)
    have hzA : IsZero (relCohomology ℤ vkPairX vkPairA n) := by
      have h : IsZero (relCohomology ℤ vkPairX vkPairA (n - 1 + 1)) :=
        isZero_of_exact_of_isZero_of_isZero (pair_exact₁ ℤ vkPairX vkPairA (n - 1)) hzC hzB
      rwa [hsub] at h
    exact ⟨IsZero.iso hzA hzFin⟩

theorem cohomologyPairVk (n : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
        (Set.range (Work.Milnor.mkToVkFun (-2))) n ≅
      ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 8 then 1 else 0)) → ℤ)) :=
  cohomologyPairVk_aux n

end

end Work.Cohomology
