import Mathlib
import Submission.Work.ThomBordism.iUnion.coneAux
import Submission.Work.ThomBordism.psiClassHyp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# The degree-`0` case of `coneCyclicPosIUnion`

If the cone of the cochain-level Thom map is cyclic at degree `0` (`ConeCyclicZero`) over the union
of every subfamily of a chain `C` of open pieces, and the local Thom map is bijective over every
member of `C`, then the cone is cyclic at degree `0` over the union of any subfamily `D₀ ⊆ C`.

The proof is the Zorn argument on partial solutions (the graph of a compatible family of primitives
`q W : ConeC Z n W 0` of the fixed cone-`1`-cycle `p`): the chain step is pointwise, the glued
primitive over the region of a maximal solution is `ConeAux.coneGlueMembersC`, and the maximality
step adjoins a new member `W ∈ D₀` by correcting `qW` by the `ExtraD`-image of a lift of the
primitive of the obstruction, which is supplied by `hzero` over the current region.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism.iUnion

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The degree-`0` case**, in the form in which the degree induction consumes it: over the union
`⋃₀ D₀` of *any* subfamily, with an *arbitrary* proof of the inclusion `⋃₀ D₀ ⊆ ⋃₀ C`. -/
theorem coneCyclicPos_zero (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W)
    (hchainC : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' ∨ W' ⊆ W)
    (τ : Work.Thom.PieceCoh Z (⋃₀ C) n)
    (h : ∀ W (hW : W ∈ C), ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' W) (Set.preimage_mono (Set.subset_sUnion_of_mem hW)) n).hom τ) k))
    (hzero : ∀ (D : Set (Set B)) (hD : D ⊆ C),
        Work.ThomBordism.ConeCyclicZero Z n (⋃₀ C) τ (⋃₀ D) (Set.sUnion_mono hD))
    (D₀ : Set (Set B)) (hD₀ : D₀ ⊆ C) (hinc₀ : ⋃₀ D₀ ⊆ ⋃₀ C) :
    Work.ThomBordism.ConeCyclicPos Z n (⋃₀ C) τ (⋃₀ D₀) hinc₀ 0 := by

  classical
  intro p hp
  -- ## The partial solutions
  let S : Set (Set (Sigma fun W : Set B => ConeC Z n W 0)) := {G |
    (∀ (W : Set B) (q q' : ConeC Z n W 0),
        Sigma.mk W q ∈ G → Sigma.mk W q' ∈ G → q = q') ∧
    (∀ (W : Set B) (q : ConeC Z n W 0), Sigma.mk W q ∈ G → W ∈ D₀) ∧
    (∀ (W : Set B) (q : ConeC Z n W 0) (hW : W ∈ D₀), Sigma.mk W q ∈ G →
      coneD Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) 0 q
        = coneRes Z n (Set.subset_sUnion_of_mem hW) (0 + 1) p) ∧
    (∀ (W : Set B) (q : ConeC Z n W 0) (W' : Set B) (q' : ConeC Z n W' 0),
        Sigma.mk W q ∈ G → Sigma.mk W' q' ∈ G → ∀ (hle : W ⊆ W'),
      coneRes Z n hle 0 q' = q)}
  have hSempty : (∅ : Set (Sigma fun W : Set B => ConeC Z n W 0)) ∈ S := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  -- ## The chain step of Zorn
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro W q q' ⟨G, hGc, hG⟩ ⟨G', hG'c, hG'⟩
      rcases eq_or_ne G G' with rfl | hne
      · exact (hc hGc).1 W q q' hG hG'
      · rcases hcc hGc hG'c hne with hle | hle
        · exact (hc hG'c).1 W q q' (hle hG) hG'
        · exact (hc hGc).1 W q q' hG (hle hG')
    · rintro W q ⟨G, hGc, hG⟩
      exact (hc hGc).2.1 W q hG
    · rintro W q hW ⟨G, hGc, hG⟩
      exact (hc hGc).2.2.1 W q hW hG
    · rintro W q W' q' ⟨G, hGc, hG⟩ ⟨G', hG'c, hG'⟩ hle'
      rcases eq_or_ne G G' with rfl | hne
      · exact (hc hGc).2.2.2 W q W' q' hG hG' hle'
      · rcases hcc hGc hG'c hne with hsub | hsub
        · exact (hc hG'c).2.2.2 W q W' q' (hsub hG) hG' hle'
        · exact (hc hGc).2.2.2 W q W' q' hG (hsub hG') hle'
  obtain ⟨G₀, hG₀mem, hG₀max⟩ := zorn_subset S hchain
  obtain ⟨hG₀fun, hG₀dom, hG₀prim, hG₀comp⟩ := hG₀mem
  let dom : Set (Set B) := {W | ∃ q : ConeC Z n W 0, Sigma.mk W q ∈ G₀}
  have hvalm : ∀ (W : Set B) (hW : W ∈ dom), ∃ q : ConeC Z n W 0, Sigma.mk W q ∈ G₀ := by
    intro W hW
    exact hW
  have hval : ∀ (W : Set B) (hW : W ∈ dom),
      Sigma.mk W (Classical.choose (hvalm W hW)) ∈ G₀ :=
    fun W hW => Classical.choose_spec (hvalm W hW)
  have hdomD₀ : dom ⊆ D₀ := fun W hW => hG₀dom W _ (hval W hW)
  have hdomchain : ∀ W ∈ dom, ∀ W' ∈ dom, W ⊆ W' ∨ W' ⊆ W :=
    fun W hW W' hW' => hchainC W (hD₀ (hdomD₀ hW)) W' (hD₀ (hdomD₀ hW'))
  -- ## Maximality: every member of `D₀` lies in the region covered by `dom`
  have hcov : ∀ W ∈ D₀, W ⊆ ⋃₀ dom := by
    intro W hW
    by_contra hcon
    obtain ⟨z, hzW, hzdom⟩ := Set.not_subset.mp hcon
    have hWnotdom : W ∉ dom := fun hWd => hzdom (Set.subset_sUnion_of_mem hWd hzW)
    -- every member of `dom` is contained in `W`
    have hle : ∀ W' ∈ dom, W' ⊆ W := by
      intro W' hW'
      rcases hchainC W' (hD₀ (hdomD₀ hW')) W (hD₀ hW) with h | h
      · exact h
      · exact absurd ((h.trans (Set.subset_sUnion_of_mem hW')) hzW) hzdom
    have hAW : ⋃₀ dom ⊆ W := Set.sUnion_subset_iff.mpr hle
    -- the glued primitive over the current region
    obtain ⟨q₀, hq₀res, hq₀eq⟩ := ConeAux.coneGlueMembersC Z n 0 C hC τ D₀ hD₀
      hdomD₀ hdomchain p (fun W : ↥dom => Classical.choose (hvalm W.1 W.2))
      (fun W W' hle' => hG₀comp W.1 _ W'.1 _ (hval W.1 W.2) (hval W'.1 W'.2) hle')
      (fun W => hG₀prim W.1 _ (hdomD₀ W.2) (hval W.1 W.2))
    -- a primitive of `p` over `W`
    have hcyc : ConeCycle Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) (0 + 1)
        (coneRes Z n (Set.subset_sUnion_of_mem hW) (0 + 1) p) := by
      show coneD Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) (0 + 1)
        (coneRes Z n (Set.subset_sUnion_of_mem hW) (0 + 1) p) = 0
      rw [← coneRes_coneD Z n (⋃₀ C) τ (Set.subset_sUnion_of_mem hW)
            (Set.subset_sUnion_of_mem (hD₀ hW)) hinc₀ (0 + 1) p,
          hp, coneRes_zero]
    obtain ⟨qW, hqWeq⟩ := coneCyclicPos_of_localThomMap Z n hn (⋃₀ C) τ W
      (Set.subset_sUnion_of_mem (hD₀ hW))
      (psiClassHyp Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)))
      (h W (hD₀ hW)) 0 (coneRes Z n (Set.subset_sUnion_of_mem hW) (0 + 1) p) hcyc
    -- the obstruction is a cone-`(m+1)`-cycle over the current region
    have hccyc : coneD Z n (⋃₀ C) τ (⋃₀ dom) (Set.sUnion_mono (hdomD₀.trans hD₀)) 0
        (coneRes Z n hAW 0 qW - q₀) = 0 := by
      rw [ConeAux.coneD_sub, hq₀eq,
        ← coneRes_coneD Z n (⋃₀ C) τ hAW (Set.sUnion_mono (hdomD₀.trans hD₀))
          (Set.subset_sUnion_of_mem (hD₀ hW)) 0 qW,
        hqWeq, coneRes_comp Z n hAW (Set.subset_sUnion_of_mem hW) (0 + 1) p]
      rw [show hAW.trans (Set.subset_sUnion_of_mem hW) = Set.sUnion_mono hdomD₀ from
        Subsingleton.elim _ _, sub_self]
    -- the correction
    obtain ⟨r, hr⟩ := hzero dom (hdomD₀.trans hD₀) (coneRes Z n hAW 0 qW - q₀) hccyc
    obtain ⟨r', hr'⟩ := extraRes_surjective Z n hAW r
    -- ## The extended partial solution
    have hG'mem : (insert (Sigma.mk W (qW - extraD Z n (⋃₀ C) τ W
        (Set.subset_sUnion_of_mem (hD₀ hW)) r')) G₀) ∈ S := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- functionality
        rintro W₁ q₁ q₂ h₁ h₂
        rcases h₁ with h₁ | h₁
        · rcases h₂ with h₂ | h₂
          · rw [Sigma.mk.injEq] at h₁ h₂
            obtain ⟨hW₁, hq₁⟩ := h₁
            obtain ⟨hW₂, hq₂⟩ := h₂
            cases hW₂
            cases hW₁
            rw [eq_of_heq hq₁, eq_of_heq hq₂]
          · rw [Sigma.mk.injEq] at h₁
            obtain ⟨hW₁, -⟩ := h₁
            subst W₁
            exact absurd ⟨q₂, h₂⟩ hWnotdom
        · rcases h₂ with h₂ | h₂
          · rw [Sigma.mk.injEq] at h₂
            obtain ⟨hW₂, -⟩ := h₂
            subst hW₂
            exact absurd ⟨q₁, h₁⟩ hWnotdom
          · exact hG₀fun W₁ q₁ q₂ h₁ h₂
      · -- the domain lies in `D₀`
        rintro W₁ q h
        rcases h with h | h
        · rw [Sigma.mk.injEq] at h
          exact h.1 ▸ hW
        · exact hG₀dom W₁ q h
      · -- each value is a primitive
        rintro W₁ q hW₁ h
        rcases h with h | h
        · rw [Sigma.mk.injEq] at h
          obtain ⟨hW₁', hq⟩ := h
          subst W₁
          rw [eq_of_heq hq, ConeAux.coneD_sub,
            coneD_zero_extraD Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) r', sub_zero]
          exact hqWeq
        · exact hG₀prim W₁ q hW₁ h
      · -- compatibility
        rintro W₁ q₁ W₂ q₂ h₁ h₂ hle'
        rcases h₁ with h₁ | h₁
        · -- the new element is the smaller one
          rcases h₂ with h₂ | h₂
          · rw [Sigma.mk.injEq] at h₁ h₂
            obtain ⟨hW₁, hq₁⟩ := h₁
            obtain ⟨hW₂, hq₂⟩ := h₂
            cases hW₂
            cases hW₁
            rw [eq_of_heq hq₁, eq_of_heq hq₂]
            exact coneRes_self Z n _ 0 _
          · rw [Sigma.mk.injEq] at h₁
            obtain ⟨hW₁, -⟩ := h₁
            subst W₁
            exact absurd ((hle'.trans (Set.subset_sUnion_of_mem (⟨q₂, h₂⟩ : W₂ ∈ dom))) hzW)
              hzdom
        · rcases h₂ with h₂ | h₂
          · -- an old element contained in the new one: the correction
            rw [Sigma.mk.injEq] at h₂
            obtain ⟨hW₂, hq₂⟩ := h₂
            subst W₂
            rw [eq_of_heq hq₂]
            have hdom₁ : W₁ ∈ dom := ⟨q₁, h₁⟩
            have h₁' : W₁ ⊆ ⋃₀ dom := Set.subset_sUnion_of_mem hdom₁
            have hch : Classical.choose hdom₁ = q₁ :=
              hG₀fun W₁ (Classical.choose (hvalm W₁ hdom₁)) q₁ (hval W₁ hdom₁) h₁
            -- the restriction of the lifted correction
            have hcomp₁ : extraRes Z n hle' r' = extraRes Z n h₁' r := by
              rw [show hle' = h₁'.trans hAW from Subsingleton.elim _ _]
              rw [← extraRes_comp Z n h₁' hAW r', hr']
            have h2 : coneRes Z n hle' 0
                (extraD Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) r')
              = coneRes Z n hle' 0 qW - q₁ := by
              rw [coneRes_extraD Z n (⋃₀ C) τ hle'
                (Set.subset_sUnion_of_mem (hD₀ (hdomD₀ hdom₁)))
                (Set.subset_sUnion_of_mem (hD₀ hW)) r']
              rw [hcomp₁]
              rw [← coneRes_extraD Z n (⋃₀ C) τ h₁'
                (Set.subset_sUnion_of_mem (hD₀ (hdomD₀ hdom₁))) (Set.sUnion_mono (hdomD₀.trans hD₀))
                r]
              rw [hr, coneRes_sub, coneRes_comp Z n h₁' hAW 0 qW]
              rw [show h₁'.trans hAW = hle' from Subsingleton.elim _ _]
              rw [hq₀res ⟨W₁, hdom₁⟩, hch]
            rw [coneRes_sub, h2, sub_sub_cancel]
          · exact hG₀comp W₁ q₁ W₂ q₂ h₁ h₂ hle'
    -- ## Contradiction with maximality
    have hsub := hG₀max hG'mem (Set.subset_insert _ _)
    exact hWnotdom ⟨qW - extraD Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) r',
      hsub (Set.mem_insert _ _)⟩
  -- ## The endgame: the maximal solution covers `⋃₀ D₀`
  have hregion : (⋃₀ dom) = ⋃₀ D₀ :=
    Set.Subset.antisymm (Set.sUnion_mono hdomD₀) (Set.sUnion_subset_iff.mpr hcov)
  obtain ⟨Q, -, hQeq⟩ := ConeAux.coneGlueMembersC Z n 0 C hC τ D₀ hD₀ hdomD₀ hdomchain p
    (fun W : ↥dom => Classical.choose (hvalm W.1 W.2))
    (fun W W' hle' => hG₀comp W.1 _ W'.1 _ (hval W.1 W.2) (hval W'.1 W'.2) hle')
    (fun W => hG₀prim W.1 _ (hdomD₀ W.2) (hval W.1 W.2))
  refine ⟨coneRes Z n (le_of_eq hregion.symm) 0 Q, ?_⟩
  rw [← coneRes_coneD Z n (⋃₀ C) τ (le_of_eq hregion.symm) hinc₀
    (Set.sUnion_mono (hdomD₀.trans hD₀)) 0 Q]
  rw [hQeq, coneRes_comp Z n (le_of_eq hregion.symm) (Set.sUnion_mono hdomD₀) (0 + 1) p]
  exact coneRes_self Z n _ (0 + 1) p

end

end Work.ThomBordism.iUnion
