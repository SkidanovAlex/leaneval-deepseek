/-
# The four side conditions of the Tietze elimination (`abstract_tietze`)

This file proves, for the Tietze data `D : TietzeData P` of `SubstSupport.lean`, the four
hypotheses required by `abstract_tietze` for the pair of homomorphisms

* `ι = delEraseVG D.K x : F(DelV D.K)_x →* F(Γ)_x` (the erasure of paths), and
* `σ = D.pathSubst.vertexHom x : F(Γ)_x →* F(DelV D.K)_x` (the substitution),

with `N = P.relatorNormalClosure x` and `N' = (P.deleteSub D.K (· ≠ D.i₀)).relatorNormalClosure x`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.L4.SubstSupport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {P : Presentation V} (D : TietzeData P)

/-! ## (a) `σ ∘ ι = id` -/

theorem pathSubst_vertexHom_eraseVG (x : V) (a : VertexGroup (V := DelV D.K) x) :
    D.pathSubst.vertexHom x (delEraseVG D.K x a) = a := by
  obtain ⟨p, hp⟩ := a
  refine Subtype.ext ?_
  simp only [PathSubst.vertexHom_apply, delEraseVG_apply]
  rw [D.pathSubst_mapPath_erasePath p, red_eq_self hp]

/-! ## (c) `ι(N') ⊆ N` -/

theorem eraseVG_mem_relatorNormalClosure (x : V) (a : VertexGroup (V := DelV D.K) x)
    (ha : a ∈ (P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x) :
    delEraseVG D.K x a ∈ P.relatorNormalClosure x := by
  have hle : (P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x ≤
      (P.relatorNormalClosure x).comap (delEraseVG D.K x) := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro y ⟨i, δ, hδ, rfl⟩
    refine Subgroup.subset_normalClosure ⟨i.1, DelV.erasePath D.K x δ,
      DelV.isReduced_erasePath D.K hδ, ?_⟩
    apply Subtype.ext
    show DelV.erasePath D.K x
        (pmul δ (pmul ((P.deleteSub D.K (fun i => i ≠ D.i₀)).path i) δ.reverse)) =
      pmul (DelV.erasePath D.K x δ) (pmul (P.path i.1) (DelV.erasePath D.K x δ).reverse)
    rw [DelV.erasePath_pmul, DelV.erasePath_pmul, DelV.erasePath_reverse,
      show DelV.erasePath D.K ((P.deleteSub D.K (fun i => i ≠ D.i₀)).base i)
          ((P.deleteSub D.K (fun i => i ≠ D.i₀)).path i) = P.path i.1 from
        DelV.erasePath_liftPath D.K (P.path i.1) i.2.2]
  exact hle ha

/-! ## (b) `σ(N) ⊆ N'` -/

/-- The substitution intertwines with conjugation by a path. -/
theorem vertexHom_conjPathHom (x : V) {a : V} (δ : Quiver.Path x a) (w : VertexGroup a) :
    D.pathSubst.vertexHom x (conjPathHom δ w)
      = conjPathHom (red (D.pathSubst.mapPath δ)) (D.pathSubst.vertexHom a w) := by
  apply Subtype.ext
  simp only [PathSubst.vertexHom_apply, conjPathHom_apply]
  rw [PathSubst.mapPath_pmul, PathSubst.mapPath_pmul, PathSubst.mapPath_reverse, red_reverse]

theorem pathSubst_vertexHom_relatorNormalClosure
    (hkeep : ∀ i, i ≠ D.i₀ → ∀ e ∈ (P.path i).arrowList, D.K.pred e) (x : V) :
    (P.relatorNormalClosure x).map (D.pathSubst.vertexHom x) ≤
      (P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x := by
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  refine Subgroup.normalClosure_le_normal ?_
  rintro y ⟨i, δ, hδ, rfl⟩
  change D.pathSubst.vertexHom x (⟨pmul δ (pmul (P.path i) δ.reverse), pmul_isReduced _ _⟩ :
      VertexGroup x) ∈ (P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x
  have hy : (⟨pmul δ (pmul (P.path i) δ.reverse), pmul_isReduced _ _⟩ : VertexGroup x)
      = conjPathHom δ (⟨P.path i, P.reduced i⟩ : VertexGroup (P.base i)) := by
    apply Subtype.ext
    rw [conjPathHom_apply, pmul_assoc]
  rw [hy, vertexHom_conjPathHom D x δ ⟨P.path i, P.reduced i⟩]
  by_cases hi : i = D.i₀
  · subst hi
    have hone : D.pathSubst.vertexHom (P.base D.i₀) ⟨P.path D.i₀, P.reduced D.i₀⟩ = 1 := by
      apply Subtype.ext
      simp only [PathSubst.vertexHom_apply, VertexGroup.coe_one]
      exact D.red_pathSubst_path_i₀
    rw [hone, map_one]
    exact Subgroup.one_mem _
  · have hk : ∀ e ∈ (P.path i).arrowList, D.K.pred e := hkeep i hi
    have hL : D.pathSubst.vertexHom (P.base i) ⟨P.path i, P.reduced i⟩
        = (⟨DelV.liftPath D.K (P.base i) (P.path i) hk,
            (DelV.isReduced_liftPath D.K (P.path i) hk).mpr (P.reduced i)⟩
          : VertexGroup (V := DelV D.K) (P.base i)) := by
      apply Subtype.ext
      simp only [PathSubst.vertexHom_apply]
      rw [D.pathSubst_mapPath_liftPath (P.path i) hk,
        red_eq_self ((DelV.isReduced_liftPath D.K (P.path i) hk).mpr (P.reduced i))]
    rw [hL]
    refine Subgroup.subset_normalClosure
      ⟨⟨i, hi, hk⟩, red (D.pathSubst.mapPath δ), isReduced_red _, ?_⟩
    apply Subtype.ext
    show pmul (pmul (red (D.pathSubst.mapPath δ))
          (DelV.liftPath D.K (P.base i) (P.path i) hk)) (red (D.pathSubst.mapPath δ)).reverse
      = pmul (red (D.pathSubst.mapPath δ))
          (pmul ((P.deleteSub D.K (fun i => i ≠ D.i₀)).path ⟨i, hi, hk⟩)
            (red (D.pathSubst.mapPath δ)).reverse)
    rw [pmul_assoc]
    rfl

/-! ## Assembly via `abstract_tietze` -/

theorem deleteSubInclVG_bijective_of_tietzeData
    (hkeep : ∀ i, i ≠ D.i₀ → ∀ e ∈ (P.path i).arrowList, D.K.pred e) (x : V)
    (hcong : ∀ b : VertexGroup x,
      delEraseVG D.K x (D.pathSubst.vertexHom x b) * b⁻¹ ∈ P.relatorNormalClosure x) :
    Function.Bijective (P.deleteSubInclVG D.K (fun i => i ≠ D.i₀) x) := by
  have hσι : ∀ a : VertexGroup (V := DelV D.K) x,
      D.pathSubst.vertexHom x (delEraseVG D.K x a) = a :=
    fun a => pathSubst_vertexHom_eraseVG D x a
  have hσN : ∀ b ∈ P.relatorNormalClosure x,
      D.pathSubst.vertexHom x b ∈
        (P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x := by
    intro b hb
    exact Subgroup.mem_comap.mp
      ((Subgroup.map_le_iff_le_comap.mp (pathSubst_vertexHom_relatorNormalClosure D hkeep x)) hb)
  have hιN' : ∀ a ∈ (P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x,
      delEraseVG D.K x a ∈ P.relatorNormalClosure x :=
    fun a ha => eraseVG_mem_relatorNormalClosure D x a ha
  have hΦ : ∀ a : VertexGroup (V := DelV D.K) x,
      P.deleteSubInclVG D.K (fun i => i ≠ D.i₀) x (QuotientGroup.mk a) =
        QuotientGroup.mk (delEraseVG D.K x a) := by
    intro a
    show QuotientGroup.lift ((P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x)
      ((P.toVertexGroup x).comp (delEraseVG D.K x)) _ (QuotientGroup.mk a) = _
    rw [QuotientGroup.lift_mk']
    exact P.toVertexGroup_apply x (delEraseVG D.K x a)
  exact abstract_tietze (delEraseVG D.K x) (D.pathSubst.vertexHom x) (P.relatorNormalClosure x)
    ((P.deleteSub D.K (fun i => i ≠ D.i₀)).relatorNormalClosure x) hσι hσN hιN' hcong
    (P.deleteSubInclVG D.K (fun i => i ≠ D.i₀) x) hΦ

end Work.ORLocInd.Howie
