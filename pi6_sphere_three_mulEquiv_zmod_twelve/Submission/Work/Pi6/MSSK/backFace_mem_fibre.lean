import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-!
# The back face of a top-front simplex lies in the fibre over the last vertex

For a simplex `σ : Δ[s] ⟶ Sing B` and a simplex `w` of `T_σ = Δ[s] ×_{Sing B} Sing E` of
dimension `s + K` whose projection to `Δ[s]` is **top-front** (its underlying monotone map fixes
the first `s+1` vertices), the back `K`-face of `w` lies over the last vertex `v_s ∈ Δ[s]`: it is
the image under the inclusion `fibreInc p σ : T_{σ(v_s)} ⟶ T_σ` of the fibre over the last vertex.

The proof is a small computation with the standard simplex `Δ[s]`:

* the monotone map underlying a top-front `α : Δ[s]_{s+K}` sends every vertex `j ≥ s` to the last
  vertex (`isTopFront_tail`), so composing with the back inclusion `backIncl s K` gives the
  constant map at the last vertex;
* conversely `lastV s` applied to any `K`-simplex of `Δ[0]` is that same constant map.

Hence the back face of `w` and the pair `(z, ∂_K(Sing E)-component)` define the same element of
`T_σ`, which yields the required lift in the fibre.
-/

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The underlying monotone map of the back face of a top-front simplex of `Δ[s]` is the constant
map at the last vertex.  In other words, for top-front `α` the composition
`backIncl s K ≫ (α : ⦋s+K⦌ ⟶ ⦋s⦌)` is the constant map at `Fin.last s`. -/
lemma bfmf_backIncl_comp_objEquiv_eq_const {s K : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).obj (op ⦋s+K⦌))
    (hα : IsTopFront α) :
    Work.Cohomology.backIncl s K ≫ SSet.stdSimplex.objEquiv α
      = SimplexCategory.const (SimplexCategory.mk K) (SimplexCategory.mk s) (Fin.last s) := by
  -- every vertex `j ≥ s` of `⦋s+K⦌` is sent to the last vertex of `⦋s⦌`
  have key : ∀ (j' : Fin (s+K+1)), s ≤ j'.val →
      ((SSet.stdSimplex.objEquiv α).toOrderHom j').val = s := by
    intro j' hj
    have h := isTopFront_tail hα (Nat.le_add_right s K) j' hj
    rw [h]; rfl
  have hback : ∀ j : Fin (K+1), ((Work.Cohomology.backIncl s K).toOrderHom j).val = s + j.val := by
    intro j
    simp only [Work.Cohomology.backIncl, SimplexCategory.Hom.toOrderHom_mk]
    rfl
  have hconst : ∀ j : Fin (K+1),
      ((SimplexCategory.const (SimplexCategory.mk K) (SimplexCategory.mk s)
        (Fin.last s)).toOrderHom j).val = s := by
    intro j
    simp [SimplexCategory.const, SimplexCategory.Hom.toOrderHom_mk]
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  refine Fin.ext ?_
  rw [SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  rw [hconst j]
  exact key ((Work.Cohomology.backIncl s K).toOrderHom j)
    (by rw [hback j]; exact Nat.le_add_right s j.val)

/-- The back face of a top-front simplex of `Δ[s]` is the constant simplex at the last vertex. -/
lemma bfmf_backFace_eq_objEquiv_symm_const {s K : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).obj (op ⦋s+K⦌))
    (hα : IsTopFront α) :
    Work.Cohomology.backFace (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s K α
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.const (SimplexCategory.mk K)
          (SimplexCategory.mk s) (Fin.last s)) := by
  rw [Work.Cohomology.backFace,
    show α = SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv α) from
      (Equiv.symm_apply_apply _ _).symm,
    SSet.stdSimplex.map_objEquiv_symm]
  exact congrArg SSet.stdSimplex.objEquiv.symm (bfmf_backIncl_comp_objEquiv_eq_const α hα)

/-- The last vertex inclusion `lastV s`, applied to any `K`-simplex of `Δ[0]`, is the constant
simplex at the last vertex of `Δ[s]`. -/
lemma bfmf_lastV_app_eq_objEquiv_symm_const {s K : ℕ}
    (z : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).obj (op ⦋K⦌)) :
    (lastV s).app (op ⦋K⦌) z
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.const (SimplexCategory.mk K)
          (SimplexCategory.mk s) (Fin.last s)) := by
  have hζ : SSet.yonedaEquiv (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv z)) = z := by
    rw [SSet.yonedaEquiv_map, Equiv.symm_apply_apply]
  have hcomp : SSet.stdSimplex.map (SSet.stdSimplex.objEquiv z) ≫ lastV s
      = SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk K)
          (SimplexCategory.mk s) (Fin.last s)) := by
    rw [lastV, ← Functor.map_comp]
    congr 1
  rw [← hζ, ← SSet.yonedaEquiv_comp, hcomp, SSet.yonedaEquiv_map]

/-- For a top-front `α`, applying `lastV s` to a `K`-simplex of `Δ[0]` gives the back face of
`α`. -/
lemma bfmf_lastV_app_eq_backFace {s K : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).obj (op ⦋s+K⦌))
    (hα : IsTopFront α)
    (z : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}).obj (op ⦋K⦌)) :
    (lastV s).app (op ⦋K⦌) z
      = Work.Cohomology.backFace (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s K α := by
  rw [bfmf_lastV_app_eq_objEquiv_symm_const z, bfmf_backFace_eq_objEquiv_symm_const α hα]

theorem backFace_mem_fibre {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {s K : ℕ} (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s + K⦌)
    (hα : Work.Pi6.MSSK.IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w)) :
    ∃ v : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (Work.Pi6.MSSK.lastV s ≫ σ)) _⦋K⦌,
      (Work.Pi6.MSSK.fibreInc p σ).app (op ⦋K⦌) v
        = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w := by
  classical
  -- the two components of `w`
  set α := (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w with hαdef
  set e := (pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w with hedef
  -- the `K`-simplex of `Δ[0]` (equivalently, the constant map `⦋K⦌ ⟶ ⦋0⦌`) and the two legs of
  -- the lift we are going to construct
  set ζ : ⦋K⦌ ⟶ ⦋0⦌ := SimplexCategory.const (SimplexCategory.mk K) (SimplexCategory.mk 0) 0
    with hζdef
  set A := SSet.stdSimplex.map ζ with hAdef
  set Bv := SSet.yonedaEquiv.symm ((Work.SSSR.sSing E).map (Work.Cohomology.backIncl s K).op e)
    with hBdef
  have htop : Work.Pi6.MSSK.IsTopFront α := hα
  -- the compatibility of the two components of the lifted simplex
  have hcond : σ.app (op ⦋s+K⦌) α = (Work.SSSR.sSingP p).app (op ⦋s+K⦌) e := by
    rw [hαdef, hedef]
    have h := congrArg (fun (g : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶
        Work.SSSR.sSing B) => g.app (op ⦋s+K⦌) w) pullback.condition
    rw [NatTrans.comp_app, NatTrans.comp_app] at h
    exact h
  -- the first leg of the lift: `A ≫ lastV s` is the element of `T_σ` supported at the back face
  -- of `α`
  have hA_last : A ≫ Work.Pi6.MSSK.lastV s
      = SSet.yonedaEquiv.symm (Work.Cohomology.backFace
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s K α) := by
    rw [hAdef, Work.Pi6.MSSK.lastV, ← Functor.map_comp]
    rw [show ζ ≫ SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk s) (Fin.last s)
        = SimplexCategory.const (SimplexCategory.mk K) (SimplexCategory.mk s) (Fin.last s) from by
      rw [hζdef]; rfl]
    rw [bfmf_backFace_eq_objEquiv_symm_const α htop,
      ← SSet.yonedaEquiv_map (f := SimplexCategory.const (SimplexCategory.mk K)
        (SimplexCategory.mk s) (Fin.last s)),
      Equiv.symm_apply_apply]
  -- the compatibility of the two legs, i.e. that `(A, Bv)` is a cone on the pullback cospan
  have hcompat : A ≫ (Work.Pi6.MSSK.lastV s ≫ σ) = Bv ≫ Work.SSSR.sSingP p := by
    apply SSet.yonedaEquiv.injective
    have hL : SSet.yonedaEquiv (A ≫ (Work.Pi6.MSSK.lastV s ≫ σ))
        = σ.app (op ⦋K⦌) (Work.Cohomology.backFace
            (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s K α) := by
      rw [SSet.yonedaEquiv_comp, hAdef, SSet.yonedaEquiv_map, NatTrans.comp_app]
      exact congrArg (σ.app (op ⦋K⦌))
        (bfmf_lastV_app_eq_backFace α htop (SSet.stdSimplex.objEquiv.symm ζ))
    have hR : SSet.yonedaEquiv (Bv ≫ Work.SSSR.sSingP p)
        = σ.app (op ⦋K⦌) (Work.Cohomology.backFace
            (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s K α) := by
      rw [SSet.yonedaEquiv_comp, hBdef, Equiv.apply_symm_apply]
      rw [NatTrans.naturality_apply (Work.SSSR.sSingP p) (Work.Cohomology.backIncl s K).op e,
        ← hcond]
      rw [← NatTrans.naturality_apply σ (Work.Cohomology.backIncl s K).op α]
      rfl
    rw [hL, hR]
  -- the back face of `w`, as a morphism `Δ[K] ⟶ T_σ`
  set W : (SSet.stdSimplex.obj (SimplexCategory.mk K) : SSet.{0}) ⟶
      pullback σ (Work.SSSR.sSingP p) :=
    SSet.yonedaEquiv.symm (Work.Cohomology.backFace
      (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w) with hWdef
  have hWspec : SSet.yonedaEquiv W
      = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w := by
    rw [hWdef, Equiv.apply_symm_apply]
  -- the lift `V` of the cone `(A, Bv)`, and the computation of its two projections
  have hVfib : pullback.lift A Bv hcompat ≫ Work.Pi6.MSSK.fibreInc p σ = W := by
    have hVfst : pullback.lift A Bv hcompat
        ≫ pullback.fst (Work.Pi6.MSSK.lastV s ≫ σ) (Work.SSSR.sSingP p) = A := by
      rw [pullback.lift_fst]
    apply pullback.hom_ext
    · simp only [Category.assoc, Work.Pi6.MSSK.fibreInc, pullback.lift_fst]
      simp only [← Category.assoc, hVfst]
      rw [hWdef, SSet.yonedaEquiv_symm_comp, Work.Pi6.MSSK.fst_backFace, ← hαdef]
      exact hA_last
    · simp only [Category.assoc, Work.Pi6.MSSK.fibreInc, pullback.lift_snd]
      rw [hWdef, SSet.yonedaEquiv_symm_comp, Work.Pi6.MSSK.snd_backFace, ← hedef, hBdef]
  have key : SSet.yonedaEquiv (pullback.lift A Bv hcompat ≫ Work.Pi6.MSSK.fibreInc p σ)
      = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w := by
    rw [hVfib]
    exact hWspec
  exact ⟨SSet.yonedaEquiv (pullback.lift A Bv hcompat),
    (SSet.yonedaEquiv_comp (pullback.lift A Bv hcompat)
      (Work.Pi6.MSSK.fibreInc p σ)).symm.trans key⟩

end

end Work.Pi6.MSSK
