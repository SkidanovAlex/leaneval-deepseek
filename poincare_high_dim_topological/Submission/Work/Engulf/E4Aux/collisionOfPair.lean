import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Defs2

/-!
# `E4b`, the collision case: two shelled or collision faces meet only on the floor

The second half of the bad-set lemma `E4b` of Newman's Lemma 7 Case 1 (the first is
`Work.Engulf.E4Aux.xCaseOfXcov`; the statement is the same as `Work.Engulf.E4alt.collisionOfPair`,
proved here in the `E4Aux` namespace).

Setting: `σ = ND.ord[i]` is a shelled simplex with its affine witness `A_τ` (so
`ND.g₁ = ψ ∘ A_τ` on `simp σ`, `A_τ` injective there), `λ ∈ ND.Γ₁.faces` a *core* face lying in the
already-engulfed set `K ∪ Q^i`, `A_λ` its witness, and `D` the exceptional set of the
general-position bound of the pair `(σ, λ)` (`NormData.pair`):

    A_τ '' simp σ ∩ A_λ '' simp λ ⊆ A_τ '' simp (σ ∩ λ)
      ∪ (A_τ '' simp (σ ∩ Fzv) ∩ A_λ '' simp (λ ∩ Fzv)) ∪ D.

Conclusion: a common chart point `A_τ x = A_λ y` of the two simplices either comes from a domain
point of `σ` that is already engulfed (`x ∈ simp σ ∩ (floorOf τ₀ τ₁ ∪ Q^i)`) or lies in `D`.

The case analysis is Newman's (12.6) with the lead's contract §1.3:
* the first term forces `x ∈ simp λ ⊆ K ∪ Q^i` by injectivity of `A_τ`; combined with
  `L7Hyp.meetK` (`K ∩ simp Δ = floorOf`) this puts `x` on the floor;
* the second term is frozen/frozen: `ND.Fzv_hull` puts both frozen hulls in `L`, `ND.g₁frz` turns
  `g₁` into `f` there, and `L7Hyp.clean` forces `x = y`, which returns us to the first case;
* the third term is `D`.
-/

open Set Metric PL

namespace Work.Engulf.E4Aux

universe u

theorem collisionOfPair {n p q N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    {i : ℕ} (hi : i < ND.ord.length)
    (hτcore : f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    {lam : Finset (PL.E N)} (hlam : lam ∈ ND.Γ₁.faces)
    (hlam_core : f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    (hlam_eng : PL.simp lam ⊆ K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
        ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w))
    (A_τ A_lam : PL.E N →ᵃ[ℝ] PL.E n)
    (hτwit : ∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A_τ x))
    (hlam_wit : ∀ x ∈ PL.simp lam, ND.g₁ x = ψ.toFun (A_lam x))
    (hτinj : Set.InjOn A_τ (PL.simp (ND.ord[i])))
    (D : Set (PL.E n))
    (hDmem : A_τ '' PL.simp (ND.ord[i]) ∩ A_lam '' PL.simp lam ⊆
      A_τ '' PL.simp (ND.ord[i] ∩ lam) ∪
        (A_τ '' PL.simp (ND.ord[i] ∩ ND.Fzv) ∩ A_lam '' PL.simp (lam ∩ ND.Fzv)) ∪ D)
    {x : PL.E N} (hx : x ∈ PL.simp (ND.ord[i])) {y : PL.E N} (hy : y ∈ PL.simp lam)
    (heq : A_τ x = A_lam y) :
    x ∈ PL.simp (ND.ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
        ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
          ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) ∨ A_τ x ∈ D := by
  classical
  have hmem : ND.ord[i] ∈ ND.ord := List.getElem_mem hi
  have hτΔ : PL.simp (ND.ord[i]) ⊆ PL.simp (τ₀ ∪ τ₁) := ND.ord_sub _ hmem
  -- the `q`-skeleton of the previous members lies in the join simplex
  have hQΔ : (⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) ⊆ PL.simp (τ₀ ∪ τ₁) := by
    intro z hz
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hz
    obtain ⟨j, hj, hj', w, hw, hz⟩ := hz
    exact ND.ord_sub _ (List.getElem_mem hj')
      (simp_mono (Finset.erase_subset _ _) hz)
  -- a point of `simp σ ∩ (K ∪ Q^i)` is in the already engulfed set `floorOf ∪ Q^i`
  have key : ∀ z ∈ PL.simp (ND.ord[i]),
      z ∈ K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
        ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w) →
      z ∈ PL.simp (ND.ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
        ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
          ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) := by
    intro z hz hzKQ
    refine ⟨hz, ?_⟩
    rcases hzKQ with hzK | hzQ
    · exact Or.inl (by
        have hzΔ : z ∈ PL.simp (τ₀ ∪ τ₁) := hτΔ hz
        have hz' : z ∈ K ∩ PL.simp (τ₀ ∪ τ₁) := ⟨hzK, hzΔ⟩
        rwa [H7.meetK] at hz')
    · exact Or.inr hzQ
  -- the point of the pair bound
  have hmem_pair : A_τ x ∈ A_τ '' PL.simp (ND.ord[i]) ∩ A_lam '' PL.simp lam :=
    ⟨⟨x, hx, rfl⟩, ⟨y, hy, heq.symm⟩⟩
  rcases hDmem hmem_pair with (h1 | h2) | hD
  · -- first term: `x` and `y` are the same domain point inside `σ ∩ λ`
    obtain ⟨x', hx', hx'eq⟩ := h1
    have hx'τ : x' ∈ PL.simp (ND.ord[i]) := simp_mono Finset.inter_subset_left hx'
    have hxx : x = x' := hτinj hx hx'τ hx'eq.symm
    have hxlam : x ∈ PL.simp lam := hxx ▸ simp_mono Finset.inter_subset_right hx'
    exact Or.inl (key x hx (hlam_eng hxlam))
  · -- second term: frozen/frozen, excluded by `clean`
    obtain ⟨⟨x', hx', hx'eq⟩, ⟨y', hy', hy'eq⟩⟩ := h2
    have hx'τ : x' ∈ PL.simp (ND.ord[i]) := simp_mono Finset.inter_subset_left hx'
    have hxx : x = x' := hτinj hx hx'τ hx'eq.symm
    have hx'L : x' ∈ L := ND.Fzv_hull _ (ND.ord_mem _ hmem) hτcore hx'
    have hxL : x ∈ L := hxx ▸ hx'L
    have hy'lam : y' ∈ PL.simp lam := simp_mono Finset.inter_subset_left hy'
    have hy'L : y' ∈ L := ND.Fzv_hull _ hlam hlam_core hy'
    have hfx : f x = ψ.toFun (A_τ x) := by rw [← ND.g₁frz hxL, hτwit x hx]
    have hfy : f y' = ψ.toFun (A_lam y') := by rw [← ND.g₁frz hy'L, hlam_wit y' hy'lam]
    have hmid : A_τ x = A_lam y' := heq.trans (heq.symm.trans hy'eq.symm)
    have hfeq : f x = f y' := by rw [hfx, hfy, hmid]
    have hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁) := hτΔ hx
    have hy'K : y' ∈ K ∪ PL.simp (τ₀ ∪ τ₁) :=
      (hlam_eng hy'lam).imp id (fun hh => hQΔ hh)
    have hxy : x = y' := H7.clean x ⟨hxΔ, hxL⟩ y' ⟨hy'K, hy'L⟩ hfeq
    have hxlam : x ∈ PL.simp lam := hxy ▸ hy'lam
    exact Or.inl (key x hx (hlam_eng hxlam))
  · exact Or.inr hD

end Work.Engulf.E4Aux
