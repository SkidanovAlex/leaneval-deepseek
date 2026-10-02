import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.psiClassHyp
import Submission.Work.ThomBordism.iUnion.extra
import Submission.Work.ThomBordism.iUnion.extraKerLift
import Submission.Work.ThomBordism.iUnion.extraGlueMembers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# Cyclicity of the cone at degree `0` over the union of a chain of pieces

The degree-`0` half of the patching step of `Work.ThomBordism.localThom_iUnion_of_fibreGenerator`:
if `σ` restricts to a local Thom class over every member `W` of a chain `C` of open sets, then the
cone of the cochain-level Thom map is cyclic at degree `0` (i.e. every cone-`0`-cycle has a primitive
in the `Extra` term) over the union of the members of any subfamily `D₀ ⊆ C`.

The proof is a Zorn argument on the *partial solutions*: a partial solution is the graph of a
compatible family of `Extra`-primitives of the fixed cycle `p` over the members of a subfamily of
`D₀`, i.e. a subset `G ⊆ Σ W : Set B, ExtraC Z n W` such that
* `G` is the graph of a function (`W` determines the value),
* the sets in the domain lie in `D₀`,
* each value is a primitive of `p` over its set,
* the values are compatible with the restrictions (`extraRes`).

The chain step of Zorn is *pointwise* (the union of a chain of partial solutions is again one), so no
gluing is needed; gluing is used only twice: to compute the primitive over the union of the domain of
a *maximal* solution, and to produce the final primitive over `⋃₀ D₀`.

The maximality step uses the correction supplied by `Work.ThomBordism.iUnion.extraKerLift`: a new
member `W ∈ D₀` whose piece is not yet covered can be adjoined because the obstruction
`q_W|_{⋃₀ dom} - q₀` (where `q₀` is the glued primitive over the current domain) lies in the kernel
of `extraD`, and `extraKerLift` lifts it to a *cycle* over `W` which is subtracted from `q_W`,
keeping `extraD q_W = p|_W` while arranging compatibility.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism.iUnion

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Cyclicity of the cone at degree `0` over the union of a subfamily of a chain.** -/
theorem coneCyclicZeroIUnion (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W)
    (hchainC : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' ∨ W' ⊆ W)
    (τ : Work.Thom.PieceCoh Z (⋃₀ C) n)
    (h : ∀ W (hW : W ∈ C), ∀ k, Function.Bijective (Work.Thom.localThomMap Z n W
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' W) (Set.preimage_mono (Set.subset_sUnion_of_mem hW)) n).hom τ) k))
    (h0inj : ∀ (D : Set (Set B)) (hD : D ⊆ C),
      Function.Injective (Work.Thom.localThomMap Z n (⋃₀ D)
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃₀ C)) (Z.proj ⁻¹' (⋃₀ D)) (Set.preimage_mono (Set.sUnion_mono hD)) n).hom τ) 0))
    (hlow : ∀ S : Set B, Subsingleton (Work.Thom.PieceCoh Z S (n - 1)))
    (D₀ : Set (Set B)) (hD₀ : D₀ ⊆ C) :
    Work.ThomBordism.ConeCyclicZero Z n (⋃₀ C) τ (⋃₀ D₀) (Set.sUnion_mono hD₀) := by
  classical
  intro p hp
  -- the set of partial solutions
  let S : Set (Set (Sigma fun W : Set B => Work.ThomBordism.ExtraC Z n W)) := {G |
    (∀ (W : Set B) (q q' : Work.ThomBordism.ExtraC Z n W),
        Sigma.mk W q ∈ G → Sigma.mk W q' ∈ G → q = q') ∧
    (∀ (W : Set B) (q : Work.ThomBordism.ExtraC Z n W), Sigma.mk W q ∈ G → W ∈ D₀) ∧
    (∀ (W : Set B) (q : Work.ThomBordism.ExtraC Z n W) (hW : W ∈ D₀), Sigma.mk W q ∈ G →
      Work.ThomBordism.extraD Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)) q
        = Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem hW) 0 p) ∧
    (∀ (W : Set B) (q : Work.ThomBordism.ExtraC Z n W) (W' : Set B)
        (q' : Work.ThomBordism.ExtraC Z n W'), Sigma.mk W q ∈ G → Sigma.mk W' q' ∈ G →
      ∀ (hle : W ⊆ W'), Work.ThomBordism.extraRes Z n hle q' = q)}
  have hSempty : (∅ : Set (Sigma fun W : Set B => Work.ThomBordism.ExtraC Z n W)) ∈ S := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  -- the chain step
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- functionality
      rintro W q q' ⟨G, hGc, hG⟩ ⟨G', hG'c, hG'⟩
      rcases eq_or_ne G G' with rfl | hne
      · exact (hc hGc).1 W q q' hG hG'
      · rcases hcc hGc hG'c hne with hle | hle
        · exact (hc hG'c).1 W q q' (hle hG) hG'
        · exact (hc hGc).1 W q q' hG (hle hG')
    · -- the domain lies in `D₀`
      rintro W q ⟨G, hGc, hG⟩
      exact (hc hGc).2.1 W q hG
    · -- each value is a primitive
      rintro W q hW ⟨G, hGc, hG⟩
      exact (hc hGc).2.2.1 W q hW hG
    · -- compatibility
      rintro W q W' q' ⟨G, hGc, hG⟩ ⟨G', hG'c, hG'⟩ hle
      rcases eq_or_ne G G' with rfl | hne
      · exact (hc hGc).2.2.2 W q W' q' hG hG' hle
      · rcases hcc hGc hG'c hne with hsub | hsub
        · exact (hc hG'c).2.2.2 W q W' q' (hsub hG) hG' hle
        · exact (hc hGc).2.2.2 W q W' q' hG (hsub hG') hle
  obtain ⟨G₀, hG₀mem, hG₀max⟩ := zorn_subset S hchain
  obtain ⟨hG₀fun, hG₀dom, hG₀prim, hG₀comp⟩ := hG₀mem
  -- the domain of the maximal solution, and its values
  let dom : Set (Set B) := {W | ∃ q : Work.ThomBordism.ExtraC Z n W,
    Sigma.mk W q ∈ G₀}
  have hval : ∀ (W : Set B) (hW : W ∈ dom),
      Sigma.mk W (Classical.choose hW) ∈ G₀ := fun W hW => Classical.choose_spec hW
  have hdomD₀ : dom ⊆ D₀ := fun W hW => hG₀dom W _ (hval W hW)
  have hdomC : dom ⊆ C := fun W hW => hD₀ (hdomD₀ hW)
  have hdomchain : ∀ W ∈ dom, ∀ W' ∈ dom, W ⊆ W' ∨ W' ⊆ W :=
    fun W hW W' hW' => hchainC W (hdomC hW) W' (hdomC hW')
  -- **maximality**: every member of `D₀` lies in the piece covered by `dom`
  have hcov : ∀ W ∈ D₀, W ⊆ ⋃₀ dom := by
    intro W hW
    by_contra hcon
    obtain ⟨z, hzW, hzdom⟩ := Set.not_subset.mp hcon
    have hWnotdom : W ∉ dom := fun hWd => hzdom (Set.subset_sUnion_of_mem hWd hzW)
    -- every member of `dom` is contained in `W`
    have hle : ∀ W' ∈ dom, W' ⊆ W := by
      intro W' hW'
      rcases hchainC W' (hdomC hW') W (hD₀ hW) with h | h
      · exact h
      · exact absurd ((h.trans (Set.subset_sUnion_of_mem hW')) hzW) hzdom
    have hAW : ⋃₀ dom ⊆ W := Set.sUnion_subset_iff.mpr hle
    -- the glued primitive over the current region
    obtain ⟨q₀, hq₀res, hq₀eq⟩ := extraGlueMembers Z n C hC τ D₀ hD₀ hdomD₀ hdomchain p
      (fun W : ↥dom => Classical.choose W.2)
      (fun W W' hle' => hG₀comp W.1 _ W'.1 _ (hval W.1 W.2) (hval W'.1 W'.2) hle')
      (fun W => hG₀prim W.1 _ (hdomD₀ W.2) (hval W.1 W.2))
    -- a primitive over `W`
    have hcyc : Work.ThomBordism.ConeCycle Z n (⋃₀ C) τ W
        (Set.subset_sUnion_of_mem (hD₀ hW)) 0
        (Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem hW) 0 p) := by
      show Work.ThomBordism.coneD Z n (⋃₀ C) τ W
        (Set.subset_sUnion_of_mem (hD₀ hW)) 0
        (Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem hW) 0 p) = 0
      have hcc := Work.ThomBordism.coneRes_coneD Z n (⋃₀ C) τ
        (Set.subset_sUnion_of_mem hW) (Set.subset_sUnion_of_mem (hD₀ hW))
        (Set.sUnion_mono hD₀) 0 p
      rw [← hcc, hp, Work.ThomBordism.coneRes_zero]
    have hqW := coneCyclicZero_of_localThomMap Z n hn (⋃₀ C) τ W
      (Set.subset_sUnion_of_mem (hD₀ hW))
      (psiClassHyp Z n (⋃₀ C) τ W (Set.subset_sUnion_of_mem (hD₀ hW)))
      (h W (hD₀ hW)) _ hcyc
    obtain ⟨qW, hqWeq⟩ := hqW
    -- the obstruction lies in the kernel of `extraD`
    have he : Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ dom) (Set.sUnion_mono hdomC)
        (Work.ThomBordism.extraRes Z n hAW qW - q₀) = 0 := by
      have h1 : Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ dom) (Set.sUnion_mono hdomC)
          (Work.ThomBordism.extraRes Z n hAW qW)
          = Work.ThomBordism.coneRes Z n (Set.sUnion_mono hdomD₀) 0 p := by
        rw [show Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ dom) (Set.sUnion_mono hdomC)
              (Work.ThomBordism.extraRes Z n hAW qW)
            = Work.ThomBordism.coneRes Z n hAW 0
                (Work.ThomBordism.extraD Z n (⋃₀ C) τ W
                  (Set.subset_sUnion_of_mem (hD₀ hW)) qW) from
          (coneRes_extraD Z n (⋃₀ C) τ hAW (Set.sUnion_mono hdomC)
            (Set.subset_sUnion_of_mem (hD₀ hW)) qW).symm]
        rw [hqWeq, ← Work.ThomBordism.coneRes_comp Z n hAW (Set.subset_sUnion_of_mem hW) 0 p]
      rw [Work.ThomBordism.extraD_sub, h1, hq₀eq, sub_self]
    -- the correction
    obtain ⟨r, hr1, hr2⟩ := extraKerLift Z n hn (⋃₀ C) τ hAW (Set.sUnion_mono hdomC)
      (Set.subset_sUnion_of_mem (hD₀ hW)) (h0inj dom hdomC) (hlow (⋃₀ dom))
      (Work.ThomBordism.extraRes Z n hAW qW - q₀) he
    -- the extended partial solution
    have hG'mem : (insert (Sigma.mk W (qW - r)) G₀) ∈ S := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- functionality
        rintro W₁ q₁ q₂ h₁ h₂
        rcases h₁ with h₁ | h₁
        · -- `⟨W₁,q₁⟩` is the new element
          rcases h₂ with h₂ | h₂
          · rw [Sigma.mk.injEq] at h₁ h₂
            obtain ⟨hW₁, hq₁⟩ := h₁
            obtain ⟨hW₂, hq₂⟩ := h₂
            cases hW₂
            cases hW₁
            rw [eq_of_heq hq₁, eq_of_heq hq₂]
          · rw [Sigma.mk.injEq] at h₁
            obtain ⟨hW₁, -⟩ := h₁
            subst hW₁
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
          subst hW₁'
          rw [eq_of_heq hq, Work.ThomBordism.extraD_sub, hr1, sub_zero]
          exact hqWeq
        · exact hG₀prim W₁ q hW₁ h
      · -- compatibility
        rintro W₁ q₁ W₂ q₂ h₁ h₂ hle'
        rcases h₁ with h₁ | h₁
        · -- `⟨W₁,q₁⟩` is the new element
          rcases h₂ with h₂ | h₂
          · rw [Sigma.mk.injEq] at h₁ h₂
            obtain ⟨hW₁, hq₁⟩ := h₁
            obtain ⟨hW₂, hq₂⟩ := h₂
            cases hW₂
            cases hW₁
            rw [eq_of_heq hq₁, eq_of_heq hq₂]
            exact Work.ThomBordism.extraRes_self Z n _ _
          · rw [Sigma.mk.injEq] at h₁
            obtain ⟨hW₁, -⟩ := h₁
            subst hW₁
            exact absurd ((hle'.trans (Set.subset_sUnion_of_mem (⟨q₂, h₂⟩ : W₂ ∈ dom))) hzW) hzdom
        · rcases h₂ with h₂ | h₂
          · -- an old element contained in the new one: the correction
            rw [Sigma.mk.injEq] at h₂
            obtain ⟨hW₂, hq₂⟩ := h₂
            subst hW₂
            rw [eq_of_heq hq₂]
            have hdom₁ : W₁ ∈ dom := ⟨q₁, h₁⟩
            have h₁' : W₁ ⊆ ⋃₀ dom := Set.subset_sUnion_of_mem hdom₁
            have hch : Classical.choose hdom₁ = q₁ :=
              hG₀fun W₁ (Classical.choose hdom₁) q₁ (hval W₁ hdom₁) h₁
            have hcomp₁ : Work.ThomBordism.extraRes Z n hle' r
                = Work.ThomBordism.extraRes Z n h₁' (Work.ThomBordism.extraRes Z n hAW r) := by
              have hh := Work.ThomBordism.extraRes_comp Z n h₁' hAW r
              rw [Work.ThomBordism.extraRes_proof_irrel Z n ((h₁').trans hAW) hle'] at hh
              exact hh.symm
            have h2 : Work.ThomBordism.extraRes Z n h₁' (Work.ThomBordism.extraRes Z n hAW r)
                = Work.ThomBordism.extraRes Z n hle' qW - q₁ := by
              calc Work.ThomBordism.extraRes Z n h₁' (Work.ThomBordism.extraRes Z n hAW r)
                  = Work.ThomBordism.extraRes Z n h₁'
                      (Work.ThomBordism.extraRes Z n hAW qW - q₀) := by rw [hr2]
                _ = Work.ThomBordism.extraRes Z n h₁' (Work.ThomBordism.extraRes Z n hAW qW)
                      - Work.ThomBordism.extraRes Z n h₁' q₀ :=
                    Work.ThomBordism.extraRes_sub Z n _ _ _
                _ = Work.ThomBordism.extraRes Z n hle' qW
                      - Work.ThomBordism.extraRes Z n h₁' q₀ := by
                    have hh := Work.ThomBordism.extraRes_comp Z n h₁' hAW qW
                    rw [Work.ThomBordism.extraRes_proof_irrel Z n ((h₁').trans hAW) hle'] at hh
                    rw [← hh]
                _ = Work.ThomBordism.extraRes Z n hle' qW - q₁ := by
                    rw [hq₀res ⟨W₁, hdom₁⟩, hch]
            rw [Work.ThomBordism.extraRes_sub, hcomp₁, h2, sub_sub_cancel]
          · exact hG₀comp W₁ q₁ W₂ q₂ h₁ h₂ hle'
    -- contradiction with maximality
    have hle' : G₀ ⊆ insert (Sigma.mk W (qW - r)) G₀ := Set.subset_insert _ _
    have hsub := hG₀max hG'mem hle'
    exact hWnotdom ⟨qW - r, hsub (Set.mem_insert _ _)⟩
  -- the region of the maximal solution is the whole of `⋃₀ D₀`
  have hregion : (⋃₀ dom) = ⋃₀ D₀ :=
    Set.Subset.antisymm (Set.sUnion_mono hdomD₀) (Set.sUnion_subset_iff.mpr hcov)
  obtain ⟨Q, -, hQeq⟩ := extraGlueMembers Z n C hC τ D₀ hD₀ hdomD₀ hdomchain p
    (fun W : ↥dom => Classical.choose W.2)
    (fun W W' hle' => hG₀comp W.1 _ W'.1 _ (hval W.1 W.2) (hval W'.1 W'.2) hle')
    (fun W => hG₀prim W.1 _ (hdomD₀ W.2) (hval W.1 W.2))
  refine ⟨Work.ThomBordism.extraRes Z n (le_of_eq hregion.symm) Q, ?_⟩
  rw [show Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ D₀) (Set.sUnion_mono hD₀)
        (Work.ThomBordism.extraRes Z n (le_of_eq hregion.symm) Q)
      = Work.ThomBordism.coneRes Z n (le_of_eq hregion.symm) 0
          (Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ dom) (Set.sUnion_mono hdomC) Q) from
    (coneRes_extraD Z n (⋃₀ C) τ (le_of_eq hregion.symm) (Set.sUnion_mono hD₀)
      (Set.sUnion_mono hdomC) Q).symm]
  rw [hQeq, Work.ThomBordism.coneRes_comp Z n (le_of_eq hregion.symm)
    (Set.sUnion_mono hdomD₀) 0 p]
  exact coneRes_self Z n _ 0 p

end

end Work.ThomBordism.iUnion
