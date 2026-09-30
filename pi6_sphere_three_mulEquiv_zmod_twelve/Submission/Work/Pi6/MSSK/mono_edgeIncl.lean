import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-!
# `mono_edgeIncl`

`edgeIncl p σ : T_{lastEdge ≫ σ} ⟶ T_σ` is the inclusion of the part of `T_σ = Δ[t+1] ×_{Sing B} Sing E`
lying over the last edge `{t, t+1}` of `Δ[t+1]`, induced by `lastEdge t : Δ[1] ⟶ Δ[t+1]`.  We show
that it is a monomorphism of simplicial sets.

The argument is purely categorical, exactly as for `mono_fibreInc`.  Write `a = lastEdge t`,
`σ : Δ[t+1] ⟶ Sing B`, `f = Sing p : Sing E ⟶ Sing B`, `π₁ = pullback.fst σ f`,
`ρ₁ = pullback.fst (a ≫ σ) f`, `ρ₂ = pullback.snd (a ≫ σ) f`.  Then

* `edgeIncl p σ ≫ π₁ = ρ₁ ≫ a` and `edgeIncl p σ ≫ π₂ = ρ₂` (its two projections),
* `a = lastEdge t` is a mono: it is `SSet.stdSimplex.map (lastEdgeHom t)`, and `lastEdgeHom t` is
  injective (hence a mono of `SimplexCategory`), while `SSet.stdSimplex` sends monos to monos.

Hence if `g ≫ edgeIncl = h ≫ edgeIncl` then `g ≫ ρ₂ = h ≫ ρ₂` (project onto the second factor) and
`g ≫ ρ₁ ≫ a = h ≫ ρ₁ ≫ a`, whence `g ≫ ρ₁ = h ≫ ρ₁` by mono-ness of `a`; two maps into the
pullback `T_{lastEdge ≫ σ}` agreeing on both projections are equal.
-/

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

noncomputable section

/-- The functor `SSet.stdSimplex : SimplexCategory ⥤ SSet` (the Yoneda embedding) sends
monomorphisms to monomorphisms. -/
lemma mono_stdSimplex_map {n m : SimplexCategory} (f : n ⟶ m) [Mono f] :
    Mono (SSet.stdSimplex.map f) := by
  refine (NatTrans.mono_iff_mono_app _).mpr fun X => ?_
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  -- On simplices, `stdSimplex.map f` is postcomposition with `f`.
  have key : ∀ a : (SSet.stdSimplex.obj n).obj X,
      SSet.stdSimplex.objEquiv (((SSet.stdSimplex.map f).app X) a)
        = SSet.stdSimplex.objEquiv a ≫ f := by
    intro a
    have h := SSet.stdSimplex.objEquiv_symm_comp (n := n) (n' := m) (m := X)
      (SSet.stdSimplex.objEquiv a) f
    rw [SSet.stdSimplex.objEquiv.symm_apply_apply] at h
    rw [← h]
    exact SSet.stdSimplex.objEquiv.apply_symm_apply _
  have h2 := congrArg SSet.stdSimplex.objEquiv hab
  rw [key a, key b] at h2
  exact SSet.stdSimplex.objEquiv.injective ((cancel_mono f).mp h2)

/-- `lastEdgeHom t` sends `i` to `t + i`, so it is injective. -/
lemma lastEdgeHom_toOrderHom_val (t : ℕ) (i : Fin 2) :
    ((lastEdgeHom t).toOrderHom i).val = t + i.val := rfl

/-- The monotone map `lastEdgeHom t` is a monomorphism of `SimplexCategory`. -/
lemma mono_lastEdgeHom (t : ℕ) : Mono (lastEdgeHom t) := by
  rw [SimplexCategory.mono_iff_injective]
  intro i j h
  have h1 := congrArg (fun x => x.val) h
  rw [lastEdgeHom_toOrderHom_val, lastEdgeHom_toOrderHom_val] at h1
  exact Fin.ext (Nat.add_left_cancel h1)

/-- The last edge `Δ[1] ⟶ Δ[t+1]` is a monomorphism of simplicial sets. -/
lemma mono_lastEdge (t : ℕ) : Mono (lastEdge t) := by
  rw [lastEdge]
  exact @mono_stdSimplex_map _ _ (lastEdgeHom t) (mono_lastEdgeHom t)

theorem mono_edgeIncl {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    CategoryTheory.Mono (Work.Pi6.MSSK.edgeIncl p σ) := by
  have hk : Mono (lastEdge t) := mono_lastEdge t
  refine ⟨fun {Z} g h H => ?_⟩
  -- the two projections of `edgeIncl`
  have h1 : (edgeIncl p σ) ≫ pullback.fst σ (Work.SSSR.sSingP p)
      = pullback.fst (lastEdge t ≫ σ) (Work.SSSR.sSingP p) ≫ lastEdge t := by
    rw [edgeIncl, pullback.lift_fst]
  have h2 : (edgeIncl p σ) ≫ pullback.snd σ (Work.SSSR.sSingP p)
      = pullback.snd (lastEdge t ≫ σ) (Work.SSSR.sSingP p) := by
    rw [edgeIncl, pullback.lift_snd]
  apply pullback.hom_ext
  · -- first projection: cancel `lastEdge t`
    apply hk.right_cancellation
    simpa only [Category.assoc, h1] using
      congrArg (fun u => u ≫ pullback.fst σ (Work.SSSR.sSingP p)) H
  · -- second projection: direct
    simpa only [Category.assoc, h2] using
      congrArg (fun u => u ≫ pullback.snd σ (Work.SSSR.sSingP p)) H

end

end Work.Pi6.MSSK
