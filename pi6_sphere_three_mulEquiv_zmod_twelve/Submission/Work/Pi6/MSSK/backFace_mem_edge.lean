import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.CapThetaBasic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.Pi6.MSSK

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

-- `pullAlong` is definitionally the pullback of `sSingP p`; making it unfold at the `implicit`
-- transparency level lets rewriting see through the two spellings of the same simplicial set.
attribute [local implicit_reducible] Work.SSSR.pullAlong


/-!
# The back face of an edge-cond simplex lies over the last edge

Helper lemmas for `Work.Pi6.MSSK.backFace_mem_edge`.
-/

/-- The retraction `⦋t+1⦌ ⟶ ⦋1⦌` of the last edge inclusion `lastEdgeHom t`: it collapses the
first `t+1` vertices `0, …, t` of `⦋t+1⦌` to `0` and sends `t+1` to `1`. -/
def rhoEdge (t : ℕ) : ⦋t+1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom
    ({ toFun := fun j : Fin (t+2) => if j.val ≤ t then (0 : Fin 2) else 1
       monotone' := by
        intro a b hab
        simp only [Fin.le_def] at hab
        by_cases ha : a.val ≤ t
        · by_cases hb : b.val ≤ t
          · simp [ha, hb]
          · simp [ha, hb]
        · have hb : ¬ b.val ≤ t := by omega
          simp [ha, hb] } : Fin (t+2) →o Fin 2)

lemma rhoEdge_apply (t : ℕ) (j : Fin (t+2)) :
    (rhoEdge t).toOrderHom j = (if j.val ≤ t then (0 : Fin 2) else 1) := by
  simp only [rhoEdge, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  rfl

lemma lastEdgeHom_val (t : ℕ) (i : Fin 2) :
    ((Work.Pi6.MSSK.lastEdgeHom t).toOrderHom i).val = t + i.val := by
  simp only [Work.Pi6.MSSK.lastEdgeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  rfl

/-- The last face inclusion `δ (Fin.last (t+1)) : [t] ⟶ [t+1]` is the inclusion of the first
`t+1` vertices, in value form. -/
lemma delta_last_toOrderHom (t : ℕ) (j : Fin (t+1)) :
    (SimplexCategory.δ (n := t) (Fin.last (t+1))).toOrderHom j = j.castSucc := by
  rw [show (SimplexCategory.δ (n := t) (Fin.last (t+1))).toOrderHom
      = ⇑(ConcreteCategory.hom (SimplexCategory.δ (n := t) (Fin.last (t+1)))) from rfl]
  rw [SimplexCategory.coe_δ]
  exact Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)

lemma frontIncl_last_val (t K : ℕ) :
    (((Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))).toOrderHom
      (Fin.last t)) : Fin (t + (K+1) + 1)).val = t := by
  simp only [Work.Cohomology.frontIncl, SimplexCategory.Hom.toOrderHom_mk]
  rfl

lemma backIncl_val (t K : ℕ) (j : Fin (K+2)) :
    (((Work.Cohomology.backIncl t (K+1)).toOrderHom j) : Fin (t + (K+1) + 1)).val = t + j.val := by
  simp only [Work.Cohomology.backIncl, SimplexCategory.Hom.toOrderHom_mk]
  rfl

/-- If the front `t`-face of a simplex `α` of `Δ[t+1]` is the last face inclusion (i.e. the
underlying monotone map fixes `0, …, t`), then every vertex `k` whose index is at least that of
the vertex `t` of `Δ[t+1]` is mapped to a vertex `≥ t`. -/
lemma objEquiv_ge_t {t K : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) _⦋t + (K+1)⦌)
    (hα : Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))
        ≫ SSet.stdSimplex.objEquiv α = SimplexCategory.δ (n := t) (Fin.last (t+1)))
    (k : Fin (t + (K+1) + 1))
    (hk : ((Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))).toOrderHom
        (Fin.last t)) ≤ k) :
    t ≤ ((SSet.stdSimplex.objEquiv α).toOrderHom k).val := by
  have hfix : ((SSet.stdSimplex.objEquiv α).toOrderHom
      ((Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))).toOrderHom
        (Fin.last t))).val = t := by
    have h := congrArg (fun (g : ⦋t⦌ ⟶ ⦋t+1⦌) => (g.toOrderHom (Fin.last t)).val) hα
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at h
    rw [delta_last_toOrderHom t (Fin.last t)] at h
    simpa [Fin.val_castSucc, Fin.val_last] using h
  have hmono : ((SSet.stdSimplex.objEquiv α).toOrderHom
      ((Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))).toOrderHom
        (Fin.last t))) ≤ ((SSet.stdSimplex.objEquiv α).toOrderHom k) :=
    ((SSet.stdSimplex.objEquiv α).toOrderHom).monotone hk
  simp only [Fin.le_def] at hmono
  omega

/-- **The back inclusion of an edge-cond simplex factors through the last edge.**  If the front
`t`-face of `α` is the last face inclusion, then the composite
`backIncl t (K+1) ≫ (α's monotone map)` factors through the last edge inclusion `lastEdgeHom t`,
with factoring map `rhoEdge t`. -/
lemma gammaEdge_factor_alpha {t K : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) _⦋t + (K+1)⦌)
    (hα : Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))
        ≫ SSet.stdSimplex.objEquiv α = SimplexCategory.δ (n := t) (Fin.last (t+1))) :
    ((Work.Cohomology.backIncl t (K+1) ≫ SSet.stdSimplex.objEquiv α) ≫ rhoEdge t)
        ≫ Work.Pi6.MSSK.lastEdgeHom t
      = Work.Cohomology.backIncl t (K+1) ≫ SSet.stdSimplex.objEquiv α := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  rw [SimplexCategory.comp_toOrderHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.comp_toOrderHom]
  simp only [OrderHom.comp_coe, Function.comp_apply]
  rw [lastEdgeHom_val, rhoEdge_apply]
  have hle : ((SSet.stdSimplex.objEquiv α).toOrderHom
      ((Work.Cohomology.backIncl t (K+1)).toOrderHom j)).val ≤ t + 1 := by
    have hlt : ((SSet.stdSimplex.objEquiv α).toOrderHom
        ((Work.Cohomology.backIncl t (K+1)).toOrderHom j)).val < t + 1 + 1 :=
      ((SSet.stdSimplex.objEquiv α).toOrderHom
        ((Work.Cohomology.backIncl t (K+1)).toOrderHom j)).isLt
    omega
  have hge : t ≤ ((SSet.stdSimplex.objEquiv α).toOrderHom
      ((Work.Cohomology.backIncl t (K+1)).toOrderHom j)).val :=
    objEquiv_ge_t α hα _ (by rw [Fin.le_def, frontIncl_last_val t K, backIncl_val t K j]; omega)
  have h : ((SSet.stdSimplex.objEquiv α).toOrderHom
      ((Work.Cohomology.backIncl t (K+1)).toOrderHom j)).val = t
      ∨ ((SSet.stdSimplex.objEquiv α).toOrderHom
      ((Work.Cohomology.backIncl t (K+1)).toOrderHom j)).val = t + 1 := by omega
  obtain h | h := h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The projection of the back face, with the index shape `t + (K+1)` of the edge-cond setting. -/
lemma fst_backFace_edge {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {t K : ℕ}
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌) :
    (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋K+1⦌)
        (Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w)
      = Work.Cohomology.backFace (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
          t (K+1) ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t + (K+1)⦌) w) :=
  NatTrans.naturality_apply (pullback.fst σ (Work.SSSR.sSingP p))
    (Work.Cohomology.backIncl t (K+1)).op w

/-- The `Sing E`-component of the back face, with the index shape `t + (K+1)`. -/
lemma snd_backFace_edge {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {t K : ℕ}
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌) :
    (pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋K+1⦌)
        (Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w)
      = (Work.SSSR.sSing E).map (Work.Cohomology.backIncl t (K+1)).op
          ((pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋t + (K+1)⦌) w) :=
  NatTrans.naturality_apply (pullback.snd σ (Work.SSSR.sSingP p))
    (Work.Cohomology.backIncl t (K+1)).op w

/-- **The back face of a simplex whose front `t`-face is the last face lies over the last edge.**
Let `T_σ = Δ[t+1] ×_{Sing B} Sing E` (`Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ`) and let `w` be a
simplex of `T_σ` of dimension `t + (K+1)` whose projection `α := proj p σ w` to `Δ[t+1]` has front
`t`-face equal to the last face inclusion, i.e. whose underlying monotone map fixes `0,…,t`.
Then the back `K`-face of `w` (`backFace (T_σ) t (K+1) w`, a `(K+1)`-simplex of `T_σ`) lies in the
image of `edgeIncl p σ : T_{lastEdge t ≫ σ} ⟶ T_σ`, the inclusion of the part of `T_σ` over the last
edge `{t, t+1}` of `Δ[t+1]`.

PROOF RECIPE (the whole proof is a near-copy of the proved sibling lemma
`Work.Pi6.MSSK.backFace_mem_fibre` in `Submission/Work/Pi6/MSSK/backFace_mem_fibre.lean`, which is
the same statement for `fibreInc`/`IsTopFront`; read it first).

Write `α := proj p σ w`, `e := comp p σ w` (so `σ α = sSingP p e` by `pullback.condition`).

1. **Combinatorics of the monotone map.** Define
   `rhoEdge (t : ℕ) : ⦋t+1⦌ ⟶ ⦋1⦌` by `toOrderHom j = if j.val ≤ t then 0 else 1` (monotone).
   Show `rhoEdge t ≫ lastEdgeHom t = 𝟙 ⦋1⦌`.
   From `hα` (`α(i) = i` for `i ≤ t`, in `toOrderHom`/`Fin` form) and monotonicity of
   `SSet.stdSimplex.objEquiv α`, show for every `j : Fin (K+2)` that
   `(objEquiv α).toOrderHom ⟨t + j, _⟩` has value `t` or `t+1`; hence
   `(objEquiv α) ∘ backIncl t (K+1) = γ ≫ lastEdgeHom t` where
   `γ := (backIncl t (K+1) ≫ objEquiv α) ≫ rhoEdge t : ⦋K+1⦌ ⟶ ⦋1⦌`
   (prove by `SimplexCategory.Hom.ext`/`OrderHom.ext`/`Fin.ext` + `omega`).
   (Use `Work.Cohomology.backIncl`, `Work.Pi6.MSSK.lastEdgeHom`, `SimplexCategory.comp_toOrderHom`.)
   In particular `SSet.stdSimplex.map γ ≫ lastEdge t`
   `= SSet.stdSimplex.map (backIncl t (K+1) ≫ objEquiv α)` (Functor.map_comp + `lastEdge`).
   [For the last-face analogue of the top-front bookkeeping see
   `Work.Pi6.MSSK.isTopFront_val`/`isTopFront_tail` in `CapThetaBasic.lean`.]

2. **The two legs of the lift.** Set
   `A := SSet.stdSimplex.map γ : Δ[K+1] ⟶ Δ[1]`,
   `Bv := SSet.yonedaEquiv.symm ((Work.SSSR.sSing E).map (Work.Cohomology.backIncl t (K+1)).op e)`,
   `W := SSet.yonedaEquiv.symm (Work.Cohomology.backFace (pullAlong (sSingP p) σ) t (K+1) w)`.
   Using `SSet.yonedaEquiv_symm_comp`, `SSet.yonedaEquiv_comp`, `SSet.yonedaEquiv_map`,
   `SSet.stdSimplex.map_objEquiv_symm`, `Work.Pi6.MSSK.fst_backFace`, `Work.Pi6.MSSK.snd_backFace`
   and `SSet.yonedaEquiv.injective`, identify `W ≫ pullback.fst σ (sSingP p)` with
   `SSet.yonedaEquiv.symm (Work.Cohomology.backFace (SSet.stdSimplex.obj (SimplexCategory.mk (t+1))) t (K+1) α)`,
   and prove that this equals `A ≫ lastEdge t` (via step 1 + `SSet.stdSimplex.map_objEquiv_symm` /
   `SSet.yonedaEquiv_map`), while `W ≫ pullback.snd σ (sSingP p) = Bv`.
3. **Compatibility and the lift.** From `W`'s compatibility (`pullback.condition`) and
   `harmless naturality` (`NatTrans.naturality_apply`) deduce
   `A ≫ (lastEdge t ≫ σ) = Bv ≫ sSingP p`, set
   `v := SSet.yonedaEquiv (pullback.lift A Bv hcompat)`; using
   `Work.Pi6.MSSK.edgeIncl = pullback.lift (pullback.fst (lastEdge t ≫ σ) _ ≫ lastEdge t)
   (pullback.snd _ _) _`, `pullback.lift_fst`, `pullback.lift_snd`, `pullback.hom_ext`,
   `SSet.yonedaEquiv_symm_comp`, `SSet.yonedaEquiv_comp` (exactly as in the last lines of
   `backFace_mem_fibre`), conclude.

Note the target file must import `Mathlib`,
`Submission.Work.Pi6.MSSK.LastEdge` and `Submission.Work.Pi6.MSSK.CapThetaBasic` only (both are
already proved); the statement must not be changed, and no extra hypotheses may be added. -/
theorem backFace_mem_edge {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B)
    {t K : ℕ} (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).obj
        (Opposite.op (SimplexCategory.mk (t + (K+1)))))
    (hα : CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1)))
        (SSet.stdSimplex.objEquiv (Work.Pi6.MSSK.proj p σ w))
      = SimplexCategory.δ (n := t) (Fin.last (t+1))) :
    ∃ v : (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)).obj
        (Opposite.op (SimplexCategory.mk (K+1))),
      (Work.Pi6.MSSK.edgeIncl p σ).app (Opposite.op (SimplexCategory.mk (K+1))) v
        = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w := by
  classical
  set α := Work.Pi6.MSSK.proj p σ w with hαdef
  set e := Work.Pi6.MSSK.comp p σ w with hedef
  -- the unfolded (application) forms of the two components
  have hαdef' : α = (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t + (K+1)⦌) w := hαdef
  have hedef' : e = (pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋t + (K+1)⦌) w := hedef
  -- the two components of `w` are compatible
  have hcond : σ.app (op ⦋t + (K+1)⦌) α = (Work.SSSR.sSingP p).app (op ⦋t + (K+1)⦌) e := by
    rw [hαdef, hedef]
    have h := congrArg (fun (g : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶
        Work.SSSR.sSing B) => g.app (op ⦋t + (K+1)⦌) w) pullback.condition
    rw [NatTrans.comp_app, NatTrans.comp_app] at h
    exact h
  -- **Step 1.** the projection of the back face factors through the last edge
  have hcomb : ((Work.Cohomology.backIncl t (K+1) ≫ SSet.stdSimplex.objEquiv α) ≫ rhoEdge t)
      ≫ Work.Pi6.MSSK.lastEdgeHom t
      = Work.Cohomology.backIncl t (K+1) ≫ SSet.stdSimplex.objEquiv α :=
    gammaEdge_factor_alpha α hα
  -- **Step 2.** the first leg of the lift: the `Δ[1]`-simplex of the edge piece
  set A : (SSet.stdSimplex.obj (SimplexCategory.mk (K+1)) : SSet.{0}) ⟶
      SSet.stdSimplex.obj (SimplexCategory.mk 1) :=
    SSet.stdSimplex.map ((Work.Cohomology.backIncl t (K+1) ≫ SSet.stdSimplex.objEquiv α)
      ≫ rhoEdge t) with hAdef
  have hA_last : A ≫ Work.Pi6.MSSK.lastEdge t
      = SSet.yonedaEquiv.symm (Work.Cohomology.backFace
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) t (K+1) α) := by
    rw [hAdef, Work.Pi6.MSSK.lastEdge, ← Functor.map_comp, hcomb]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_map, Equiv.apply_symm_apply, Work.Cohomology.backFace,
      SSet.stdSimplex.map_apply, Quiver.Hom.unop_op]
  -- **Step 3.** the second leg of the lift: the `Sing E`-simplex of the back face
  set Bv : (SSet.stdSimplex.obj (SimplexCategory.mk (K+1)) : SSet.{0}) ⟶ Work.SSSR.sSing E :=
    SSet.yonedaEquiv.symm ((Work.SSSR.sSing E).map (Work.Cohomology.backIncl t (K+1)).op e)
    with hBdef
  have hLstep : (Work.Pi6.MSSK.lastEdge t).app (op ⦋K+1⦌) (SSet.yonedaEquiv A)
      = Work.Cohomology.backFace
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) t (K+1) α := by
    rw [← SSet.yonedaEquiv_comp, hA_last, Equiv.apply_symm_apply]
  have hL : SSet.yonedaEquiv (A ≫ (Work.Pi6.MSSK.lastEdge t ≫ σ))
      = σ.app (op ⦋K+1⦌) (Work.Cohomology.backFace
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) t (K+1) α) := by
    rw [SSet.yonedaEquiv_comp, NatTrans.comp_app]
    exact congrArg (σ.app (op ⦋K+1⦌)) hLstep
  have hR : SSet.yonedaEquiv (Bv ≫ Work.SSSR.sSingP p)
      = σ.app (op ⦋K+1⦌) (Work.Cohomology.backFace
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) t (K+1) α) := by
    rw [SSet.yonedaEquiv_comp, hBdef, Equiv.apply_symm_apply,
      NatTrans.naturality_apply (Work.SSSR.sSingP p) (Work.Cohomology.backIncl t (K+1)).op e,
      ← hcond]
    rw [← NatTrans.naturality_apply σ (Work.Cohomology.backIncl t (K+1)).op α]
    rfl
  -- the two legs form a cone over the pullback cospan
  have hcompat : A ≫ (Work.Pi6.MSSK.lastEdge t ≫ σ) = Bv ≫ Work.SSSR.sSingP p := by
    apply SSet.yonedaEquiv.injective
    rw [hL, hR]
  -- the back face of `w`, as a morphism `Δ[K+1] ⟶ T_σ`
  set W : (SSet.stdSimplex.obj (SimplexCategory.mk (K+1)) : SSet.{0}) ⟶
      pullback σ (Work.SSSR.sSingP p) :=
    SSet.yonedaEquiv.symm (Work.Cohomology.backFace
      (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w) with hWdef
  have hWspec : SSet.yonedaEquiv W
      = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w := by
    rw [hWdef, Equiv.apply_symm_apply]
  -- **Step 4.** the lift and the identification of its image under `edgeIncl` with `W`
  have hVfst : pullback.lift A Bv hcompat
      ≫ pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p) = A := by
    rw [pullback.lift_fst]
  have hVfib : pullback.lift A Bv hcompat ≫ Work.Pi6.MSSK.edgeIncl p σ = W := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Work.Pi6.MSSK.edgeIncl, pullback.lift_fst]
      simp only [← Category.assoc, hVfst]
      rw [hWdef, SSet.yonedaEquiv_symm_comp, fst_backFace_edge, ← hαdef']
      exact hA_last
    · simp only [Category.assoc, Work.Pi6.MSSK.edgeIncl, pullback.lift_snd]
      rw [hWdef, SSet.yonedaEquiv_symm_comp, snd_backFace_edge, ← hedef', hBdef]
  have key : SSet.yonedaEquiv (pullback.lift A Bv hcompat ≫ Work.Pi6.MSSK.edgeIncl p σ)
      = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w := by
    rw [hVfib]
    exact hWspec
  exact ⟨SSet.yonedaEquiv (pullback.lift A Bv hcompat),
    (SSet.yonedaEquiv_comp (pullback.lift A Bv hcompat)
      (Work.Pi6.MSSK.edgeIncl p σ)).symm.trans key⟩

end

end Work.Pi6.MSSK
