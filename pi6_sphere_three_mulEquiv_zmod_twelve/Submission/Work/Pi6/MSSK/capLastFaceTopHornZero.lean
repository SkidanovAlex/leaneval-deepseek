import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# The cap product with the last-face top cochain vanishes on the horn

Let `t K : ℕ`, `p : C(E, B)`, `σ : Δ[t+1] ⟶ Sing B` and `T_σ = Δ[t+1] ×_{Sing B} Sing E`
(`Work.SSSR.pullAlong (sSingP p) σ`).  The cochain `lastFaceTop R p σ` is the `t`-cochain on
`T_σ` which is `1` on the simplices over the top simplex of the *last* face of `Δ[t+1]`
(equivalently: whose projection to `Δ[t+1]` fixes the first `t+1` vertices) and `0` elsewhere
(`Work.Pi6.MSSK.lastFaceVal`).

The **horn** `Λ = Work.SSSR.pieceHorn (sSingP p) σ ⊆ T_σ` is the part of `T_σ` lying over the
union of the faces `d_i Δ[t+1]`, `i ≤ t`, of `Δ[t+1]`.  A simplex of `T_σ` over the horn has a
projection `α : [N] ⟶ [t+1]` whose image misses some vertex `i ≤ t`; but `lastFaceTop` is `1`
on a simplex only if `α` fixes `0, …, t`, and then in particular `α i = i`, contradiction.
Hence capping `lastFaceTop` with a chain of the horn gives `0`:

`capLastFaceTopHornZero`.  This is the "vanishing on the boundary/horn" input of the
cap–transport computation (see `Submission/Work/Pi6/MSSK/cap_theta_bdry_zero.lean` for the
`thetaTop`/`∂T_σ` analogue).
-/

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The last face inclusion `δ (Fin.last (t+1)) : [t] ⟶ [t+1]` is the inclusion of the first
`t+1` vertices, in value form. -/
private lemma delta_last_toOrderHom (t : ℕ) (j : Fin (t+1)) :
    (SimplexCategory.δ (n := t) (Fin.last (t+1))).toOrderHom j = j.castSucc := by
  rw [show (SimplexCategory.δ (n := t) (Fin.last (t+1))).toOrderHom
      = ⇑(ConcreteCategory.hom (SimplexCategory.δ (n := t) (Fin.last (t+1)))) from rfl]
  rw [SimplexCategory.coe_δ]
  exact Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)

/-- Membership in the horn `Work.SSSR.hornSimp s = ⋃_{i<s} d_i Δ[s]`: an `s`-simplex of `Δ[s]`
lies in the horn iff some vertex `i : Fin s` is missed by its underlying monotone map. -/
private lemma mem_hornSimp_iff {s d : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋d⦌) :
    α ∈ (Work.SSSR.hornSimp s).obj (op ⦋d⦌) ↔ ∃ i : Fin s, ∀ k : Fin (d+1), α k ≠ i.castSucc := by
  rw [Work.SSSR.hornSimp, Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun k => ?_⟩
    have h := (SSet.stdSimplex.mem_face_iff (S := ({i.castSucc} : Finset (Fin (s+1)))ᶜ) α).mp hi k
    simpa using h
  · rintro ⟨i, hi⟩
    exact ⟨i, (SSet.stdSimplex.mem_face_iff (S := ({i.castSucc} : Finset (Fin (s+1)))ᶜ) α).mpr
      (fun k => by simpa using hi k)⟩

/-- The projection of the front `n`-face of a simplex of `T_σ` is the front `n`-face of its
projection (`fst_frontFace` with the source dimension of `σ` kept general). -/
private lemma fst_frontFace' {s n N : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : n ≤ N) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋n⦌)
        (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) n N h w)
      = Work.Cohomology.frontFace (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) n N h
          ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w) :=
  NatTrans.naturality_apply (pullback.fst σ (Work.SSSR.sSingP p)) (Work.Cohomology.frontIncl n N h).op w

/-- **The combinatorial heart.**  If a simplex `α : Δ[t+1] _⦋N⦌` lies over the horn, then its
underlying monotone map does not fix the first `t+1` vertices, i.e. the front `t`-face of `α` is
not the top simplex of the last face of `Δ[t+1]`. -/
private lemma not_frontIncl_comp_objEquiv_eq_delta_last {t N : ℕ} (h : t ≤ N)
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) _⦋N⦌)
    (hmem : α ∈ (Work.SSSR.hornSimp (t+1)).obj (op ⦋N⦌)) :
    ¬ (Work.Cohomology.frontIncl t N h ≫ SSet.stdSimplex.objEquiv α
        = SimplexCategory.δ (n := t) (Fin.last (t+1))) := by
  obtain ⟨i, hi⟩ := (mem_hornSimp_iff α).mp hmem
  intro hf
  have h2 := congrArg (fun (g : ⦋t⦌ ⟶ ⦋t+1⦌) => g.toOrderHom i) hf
  rw [SimplexCategory.comp_toOrderHom] at h2
  simp only [OrderHom.comp_coe, Function.comp_apply] at h2
  rw [delta_last_toOrderHom] at h2
  exact hi ((Work.Cohomology.frontIncl t N h).toOrderHom i) h2

/-- `lastFaceVal` of the front `t`-face of a simplex `w` of `T_σ` is the indicator of the
condition that the front `t`-face of the projection of `w` is the top simplex of the last face of
`Δ[t+1]`. -/
private lemma lastFaceVal_frontFace_eq {t K : ℕ} (R : Type) [CommRing R] [Nontrivial R]
    (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t+K⦌) :
    lastFaceVal R p σ (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t+K)
        (Nat.le_add_right t K) w)
      = (if Work.Cohomology.frontIncl t (t+K) (Nat.le_add_right t K)
            ≫ SSet.stdSimplex.objEquiv ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+K⦌) w)
          = SimplexCategory.δ (n := t) (Fin.last (t+1)) then (1:R) else 0) := by
  have hmap : SSet.stdSimplex.objEquiv (Work.Cohomology.frontFace
        (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) t (t+K) (Nat.le_add_right t K)
        ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+K⦌) w))
      = Work.Cohomology.frontIncl t (t+K) (Nat.le_add_right t K)
          ≫ SSet.stdSimplex.objEquiv ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+K⦌) w) := by
    rw [Work.Cohomology.frontFace, SSet.stdSimplex.map_apply, Quiver.Hom.unop_op,
      Equiv.apply_symm_apply]
  have hiff : ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌)
        (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t+K)
          (Nat.le_add_right t K) w)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (n := t) (Fin.last (t+1))))
      ↔ (Work.Cohomology.frontIncl t (t+K) (Nat.le_add_right t K)
            ≫ SSet.stdSimplex.objEquiv ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+K⦌) w)
          = SimplexCategory.δ (n := t) (Fin.last (t+1))) := by
    rw [fst_frontFace' p σ (Nat.le_add_right t K) w, Equiv.eq_symm_apply, hmap]
  rw [lastFaceVal]
  exact if_congr hiff rfl rfl

/-- **The cap product with `lastFaceTop` vanishes on the horn.**  A chain of the horn subcomplex
`Λ ⊆ T_σ` is a sum of simplices lying over the horn, and on each such simplex the cap product with
`lastFaceTop` is `0` (the front `t`-face of a simplex over the horn is never over the top simplex
of the last face). -/
theorem capLastFaceTopHornZero (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {t K : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (y : (Work.SSSR.sCC R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).X (t + K)) :
    Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.lastFaceTop R p σ) K
        ((Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f (t + K) y) = 0 := by
  -- On the generators of the horn subcomplex the cap product with `lastFaceTop` vanishes.
  have key : ∀ (w : (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ : SSet.{0}) _⦋t+K⦌),
      (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w.1
        ≫ Work.Cohomology.capHom R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.lastFaceTop R p σ) K = 0 := by
    intro w
    -- `w` lies over the horn of `Δ[t+1]`
    have hmem : ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+K⦌) w.1)
        ∈ (Work.SSSR.hornSimp (t+1)).obj (op ⦋t+K⦌) := by
      have h2 := w.2
      change (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+K⦌) w.1
        ∈ (Work.SSSR.hornSimp (t+1)).obj (op ⦋t+K⦌) at h2
      exact h2
    rw [Work.Cohomology.ιChainComplex_capHom, Work.Pi6.MSSK.genEval_lastFaceTop]
    rw [lastFaceVal_frontFace_eq R p σ w.1,
      ite_eq_right (not_frontIncl_comp_objEquiv_eq_delta_last (Nat.le_add_right t K) _ hmem)]
    simp
  -- Hence the chain-level composite `sCCMap ι ≫ capHom lastFaceTop` is zero.
  have hcomp : (Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f (t+K)
      ≫ Work.Cohomology.capHom R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.lastFaceTop R p σ) K = 0 := by
    apply SSet.chainComplex_hom_ext
    intro w
    -- the generator of the subcomplex maps to the generator of the ambient complex
    have hnat : (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ : SSet.{0}).ιChainComplex
          (R := ModuleCat.of R R) w
        ≫ (Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f (t+K)
        = (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w.1 := by
      rw [show (Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f (t+K)
          = (SSet.chainComplexMap (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι
              (ModuleCat.of R R)).f (t+K) from rfl]
      rw [SSet.ι_chainComplexMap_f]
      rfl
    rw [← Category.assoc, hnat, key w]
    simp
  -- Evaluate the chain-level identity at `y`.
  have h2 := congrArg (fun (g : (Work.SSSR.sCC R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).X (t+K) ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X K) =>
        ModuleCat.Hom.hom g y) hcomp
  simpa [Work.Cohomology.cap, ModuleCat.hom_comp] using h2

end

end Work.Pi6.MSSK
