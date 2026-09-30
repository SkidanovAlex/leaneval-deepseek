import Mathlib
import Submission.Work.Fold.GlueDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Fold

open Set Function

/-- The positive orthant `{x | 0 ≤ x i}` (`i < c`) is closed in `E4`. -/
lemma isClosed_posOrthant (c : ℕ) : IsClosed (posOrthant c) := by
  have h : posOrthant c = ⋂ (i : Fin 4), ⋂ (_ : i.1 < c), {y : E4 | 0 ≤ y i} := by
    ext x
    simp only [mem_iInter, Set.mem_ofPred_eq]
    exact mem_posOrthant_iff
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i)

namespace FoldGlue

variable {Y : Type*} [TopologicalSpace Y] {c : ℕ}

/-- **A piece of the target is closed in the target.**  If `x` is a point of the target and a limit
of points of the `r`-th chart image, then `x` already lies in that image.

Indeed, if `reflVec r x` were outside `S = ψ₊ '' U₊` but inside the positive orthant, then
`foldMap x = foldMap (reflVec r x) = reflVec r x` would force `reflVec r x ∈ S`; hence
`reflVec r x ∉ posOrthant`, and then `reflVec r ⁻¹' (posOrthant)ᶜ` is an open neighbourhood of `x`
meeting `ψ r '' U r` nowhere. -/
lemma mem_image_of_mem_closure (D : FoldGlue Y c) (hc : c ≤ 4) {x : E4}
    (hx : x ∈ D.target hc) (r : Sign c) (hcl : x ∈ closure (D.ψ r '' D.U r)) :
    x ∈ D.ψ r '' D.U r := by
  by_contra hcon
  have hxt : x ∈ D.ψ (signOf c hc x) '' D.U (signOf c hc x) := D.mem_image_signOf hc hx
  have hfold : foldMap c hc x ∈ D.S := by
    have h := hx
    rwa [target, mem_preimage] at h
  -- `reflVec r x` does not lie in `S`, hence not in the positive orthant
  have hv : reflVec r x ∉ D.S := fun hS =>
    hcon (by rw [D.himage r, image_reflVec_eq_preimage, mem_preimage]; exact hS)
  have hpos : reflVec r x ∉ posOrthant c := fun hpos => hv (by
    rw [← foldMap_eq_self_of_mem_posOrthant hc hpos, foldMap_reflVec]
    exact hfold)
  -- open neighbourhood of `x` disjoint from the image
  have hO : IsOpen (reflVec r ⁻¹' (posOrthant c)ᶜ) :=
    (isClosed_posOrthant c).isOpen_compl.preimage (continuous_reflVec r)
  have hxO : x ∈ reflVec r ⁻¹' (posOrthant c)ᶜ := by
    rw [mem_preimage, mem_compl_iff]
    exact hpos
  have hsub : D.ψ r '' D.U r ⊆ (reflVec r ⁻¹' (posOrthant c)ᶜ)ᶜ := by
    rw [D.himage r]
    rintro y ⟨s, hs, rfl⟩
    simp only [mem_compl_iff, mem_preimage, reflVec_involutive, not_not]
    exact D.S_subset hs
  have hxcompl : x ∈ (reflVec r ⁻¹' (posOrthant c)ᶜ)ᶜ :=
    closure_minimal hsub hO.isClosed_compl hcl
  rw [mem_compl_iff] at hxcompl
  exact hxcompl hxO

/-- **The pieces are closed in the target.**  For every sign pattern `r`, the part of the target
lying in the closure of the `r`-th chart image lies in the image itself. -/
theorem closure_image_inter_target_subset (D : FoldGlue Y c) (hc : c ≤ 4) (r : Sign c) :
    closure (D.ψ r '' D.U r) ∩ D.target hc ⊆ D.ψ r '' D.U r :=
  fun _ hx => mem_image_of_mem_closure D hc hx.2 r hx.1

end FoldGlue

/-- **The inverse of the fold chart is continuous on its target.**

Let `x` be a point of the target, `y = invFun x` the corresponding point of the source and `N` an
open neighbourhood of `y`.  The pieces of the target are closed in the target
(`FoldGlue.mem_image_of_mem_closure`), so the set of target points whose canonical preimage lies
outside `N` is closed in the target away from `x`: if `x` were a limit of such points
`xₙ = ψ r yₙ` with `yₙ ∈ U r ∖ N`, then `x ∈ ψ r '' U r` and `inv r` is continuous at `x` on
`ψ r '' U r` with `inv r x = y ∈ N`, forcing `yₙ = inv r xₙ ∈ N` for `xₙ` close to `x`.  Hence a
neighbourhood of `x` is mapped into `N`. -/
theorem invFun_continuousOn {Y : Type*} [TopologicalSpace Y] {c : ℕ} (D : FoldGlue Y c)
    (hc : c ≤ 4) : ContinuousOn (D.invFun hc) (D.target hc) := by
  classical
  rw [continuousOn_iff]
  intro x hx N hN hxN
  -- no piece accumulates at `x` on points whose canonical preimage lies outside `N`
  have hcl : ∀ r : Sign c, x ∉ closure (D.ψ r '' (D.U r \ N)) := by
    intro r hmem
    have hmem' : x ∈ closure (D.ψ r '' D.U r) :=
      closure_mono (Set.image_mono Set.diff_subset) hmem
    obtain ⟨y, hyU, hyx⟩ := FoldGlue.mem_image_of_mem_closure D hc hx r hmem'
    -- `y` is the canonical preimage of `x`
    have hycanon : D.invFun hc x = y := by
      change D.inv (signOf c hc x) x = y
      exact D.hcross (signOf c hc x) r (D.inv_mem _ (D.mem_image_signOf hc hx)) hyU
        (by rw [D.inv_apply _ (D.mem_image_signOf hc hx), hyx])
    have hyN : y ∈ N := hycanon ▸ hxN
    have hinv : D.inv r x = y :=
      D.hcross r r (D.inv_mem r ⟨y, hyU, hyx⟩) hyU (by rw [D.inv_apply r ⟨y, hyU, hyx⟩, hyx])
    -- continuity of `inv r` at `x` inside `ψ r '' U r`
    obtain ⟨A, hAopen, hxA, hAsub⟩ :=
      (continuousOn_iff.mp (D.inv_cont r)) x ⟨y, hyU, hyx⟩ N hN (by rw [hinv]; exact hyN)
    -- `A` is disjoint from the piece restricted to `U r ∖ N`
    have hsub : D.ψ r '' (D.U r \ N) ⊆ Aᶜ := by
      rintro z ⟨yr, ⟨hyrU, hyrN⟩, rfl⟩
      rw [mem_compl_iff]
      intro hzA
      have h1 : D.inv r (D.ψ r yr) ∈ N := hAsub ⟨hzA, ⟨yr, hyrU, rfl⟩⟩
      have h2 : D.inv r (D.ψ r yr) = yr :=
        D.hcross r r (D.inv_mem r ⟨yr, hyrU, rfl⟩) hyrU (by rw [D.inv_apply r ⟨yr, hyrU, rfl⟩])
      rw [h2] at h1
      exact hyrN h1
    have hxcompl : x ∈ Aᶜ := closure_minimal hsub hAopen.isClosed_compl hmem
    rw [mem_compl_iff] at hxcompl
    exact hxcompl hxA
  refine ⟨⋂ r : Sign c, (closure (D.ψ r '' (D.U r \ N)))ᶜ, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun r => isClosed_closure.isOpen_compl
  · rw [mem_iInter]
    intro r
    rw [mem_compl_iff]
    exact hcl r
  · rintro x' ⟨hx'W, hx't⟩
    rw [mem_preimage]
    by_contra hcon
    have ht : D.invFun hc x' ∈ D.U (signOf c hc x') \ N :=
      ⟨D.inv_mem _ (D.mem_image_signOf hc hx't), hcon⟩
    have hψ : D.ψ (signOf c hc x') (D.invFun hc x') = x' := by
      change D.ψ (signOf c hc x') (D.inv (signOf c hc x') x') = x'
      exact D.inv_apply _ (D.mem_image_signOf hc hx't)
    have hmem : x' ∈ closure (D.ψ (signOf c hc x') '' (D.U (signOf c hc x') \ N)) :=
      subset_closure ⟨D.invFun hc x', ht, hψ⟩
    have hnot : x' ∉ closure (D.ψ (signOf c hc x') '' (D.U (signOf c hc x') \ N)) := by
      have h1 := mem_iInter.mp hx'W (signOf c hc x')
      rwa [mem_compl_iff] at h1
    exact hnot hmem

end Work.Fold
