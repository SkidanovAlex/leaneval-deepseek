import Mathlib
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field_at
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.EXT.ric_bound_of_curvBound
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.ChartCurv
open Work.Diff.GE

namespace Work.Diff.EXT

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The coordinate of a vector read off the inverse Gram matrix

The pointwise Ricci tensor is the trace of the endomorphism `w ↦ R(w,u)v`, so it is computed by
reading the coordinates of the curvature vectors `rmVec (lcof g) x (bb m) u v` in the basis
`Module.finBasis ℝ E`.  The coordinate of a vector in a basis is recovered from its pairings with
the basis through the inverse of the Gram matrix; that is the elementary linear-algebra input of
the proof. -/

/-- **Coordinates from pairings, entry by entry.**  If `ip` is an additive, homogeneous, symmetric,
positive definite pairing on a vector space `V` with basis `b`, then the `m`-th coordinate of `w`
in the basis `b` is `∑ l, (Γ⁻¹) m l * ip w (b l)`, where `Γ i j = ip (b i) (b j)`. -/
lemma coord_eq_sum_invGram_mul_pairing
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin n) ℝ V) (ip : V → V → ℝ)
    (hadd : ∀ x y z, ip (x + y) z = ip x z + ip y z)
    (hsmul : ∀ (c : ℝ) x z, ip (c • x) z = c * ip x z)
    (hsymm : ∀ x y, ip x y = ip y x)
    (hpos : ∀ x, x ≠ 0 → 0 < ip x x)
    (w : V) (m : Fin n) :
    b.coord m w = ∑ l, (Matrix.of (fun i j => ip (b i) (b j)))⁻¹ m l * ip w (b l) := by
  have h := eq_sum_basis_of_pairing_gram b ip hadd hsmul hsymm hpos w
  have hc : b.equivFun w = Matrix.mulVec (Matrix.of (fun i j => ip (b i) (b j)))⁻¹
      (fun l => ip w (b l)) := by
    conv_lhs => rw [h]
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, hc, Matrix.mulVec_apply, dotProduct]
  exact Finset.sum_congr rfl (fun l _ => by rw [Matrix.row_apply, mul_comm])

/-- **The Ricci tensor as a contraction of the inverse Gram matrix with the curvature pairings.**
In the canonical basis of the model space,
`ricAt (lcOf g) x u v = ∑ m l, (Γ⁻¹) m l * 𝓡m(bb m, u, v; bb l)` where `Γ` is the Gram matrix of
the canonical basis for `g.inner x`.

(Note the argument order of `rmP`: `rmP g x a b c d = `⟪R(a,b)d, c⟫`, so the contraction of the
`l`-th index is with the third argument of the displayed `rmP`.) -/
theorem ricAt_eq_sum_gramInv_rmP {g : SMet I M} (x : M) (u v : TangentSpace I x) :
    ricAt (lcOf g) x u v
      = ∑ m, ∑ l, (Matrix.of (fun i j => g.inner x (Module.finBasis ℝ E i : TangentSpace I x)
            (Module.finBasis ℝ E j)))⁻¹ m l *
          rmP g x (Module.finBasis ℝ E m) u (Module.finBasis ℝ E l) v := by
  rw [ricAt]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine coord_eq_sum_invGram_mul_pairing (V := TangentSpace I x)
    (Module.finBasis ℝ E : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (fun a b => g.inner x a b) ?_ ?_ ?_ ?_
    (rmVec (lcOf g) x ((Module.finBasis ℝ E m : E) : TangentSpace I x) u v) m
  · intro a b c
    rw [map_add]
    rfl
  · intro c a b
    rw [map_smul]
    rfl
  · intro a b
    exact g.symm x a b
  · intro a ha
    exact g.pos x a ha

/-- A finite sum of functions continuous at a point is continuous at that point. -/
lemma continuousAt_finSum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {t₀ : ℝ}
    (h : ∀ i ∈ s, ContinuousAt (f i) t₀) :
    ContinuousAt (fun t : ℝ => ∑ i ∈ s, f i t) t₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert a s ha ih =>
      have ha' : ContinuousAt (f a) t₀ := h a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, ContinuousAt (f i) t₀ := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hgoal : (fun t : ℝ => ∑ i ∈ insert a s, f i t)
          = fun t : ℝ => f a t + ∑ i ∈ s, f i t := by
        funext t
        rw [Finset.sum_insert ha]
      rw [hgoal]
      exact ha'.add (ih hs')

/-- **Continuity of the Ricci tensor along a jointly smooth family of metrics.**  If
`t ↦ G t` is a jointly smooth family of metrics on an open time interval `J` (in the sense that the
section `(t,x) ↦ (G t).inner x` is `C^∞` on `J × M`), then for fixed `x`, `u`, `v` the function
`t ↦ ricAt (lcOf (G t)) x u v` — the pointwise Ricci tensor of the Levi-Civita connection of
`G t` — is continuous at every `t₀ ∈ J`.  (Proof: in a chart, `ricAt` is a smooth function of the
second spatial derivatives of the metric components, which are themselves continuous in `t`.) -/
theorem ricAt_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (x : M) (u v : TangentSpace I x) :
    ContinuousAt (fun t : ℝ => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x u v) t₀ := by
  -- an arbitrary smooth metric of the family, to provide the auxiliary instances
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun y : M ↦ TangentSpace I y) := inferInstance
  -- the Levi-Civita connection of each member of the family is smooth
  have hLC : LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  -- the trace identity: `ricAt` is the inverse-Gram contraction of the curvature pairings
  have key : (fun t : ℝ => ricAt (lcOf (G t)) x u v)
      = fun t : ℝ => ∑ m, ∑ l,
          (Matrix.of (fun i j => (G t).inner x (Module.finBasis ℝ E i : TangentSpace I x)
            (Module.finBasis ℝ E j)))⁻¹ m l *
          rmP (G t) x (Module.finBasis ℝ E m) u (Module.finBasis ℝ E l) v := by
    funext t
    exact ricAt_eq_sum_gramInv_rmP (g := G t) x u v
  rw [key]
  -- the Gram matrix of the family is the one of the coordinate frame at the point `x`
  have hGram : ∀ t : ℝ, Matrix.of (fun i j => (G t).inner x
        (Module.finBasis ℝ E i : TangentSpace I x) (Module.finBasis ℝ E j))
      = GramM (I := I) G x t x := by
    intro t
    ext i j
    simp only [Matrix.of_apply, GramM, mComp, cFrame_apply, cBasis]
    rw [Submission.Gauss.frameVector_self x (Module.finBasis ℝ E i),
      Submission.Gauss.frameVector_self x (Module.finBasis ℝ E j)]
  -- the path `t ↦ (t, x)` into the product
  have hcx : ContinuousAt (fun t : ℝ => (t, x)) t₀ := by fun_prop
  -- the inverse Gram matrix is continuous in time
  have hGramC : ∀ m l : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ => (Matrix.of (fun i j => (G t).inner x
        (Module.finBasis ℝ E i : TangentSpace I x) (Module.finBasis ℝ E j)))⁻¹ m l) t₀ := by
    intro m l
    have h3 : ContinuousAt (fun t : ℝ => GramInv (I := I) G x t x m l) t₀ := by
      have h := (gramInv_jointSmooth (I := I) (M := M) hJ hG ht₀ x m l).continuousAt
      refine (h.comp (x := t₀) (f := fun t : ℝ => (t, x)) hcx).congr ?_
      filter_upwards with t
      simp only [Function.comp_apply]
    have hft : (fun t : ℝ => (Matrix.of (fun i j => (G t).inner x
          (Module.finBasis ℝ E i : TangentSpace I x) (Module.finBasis ℝ E j)))⁻¹ m l)
        = fun t : ℝ => GramInv (I := I) G x t x m l := by
      funext t
      rw [hGram t, GramInv]
    rw [hft]
    exact h3
  -- the curvature pairings are continuous in time
  have hRmP : ∀ m l : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ => rmP (G t) x (Module.finBasis ℝ E m) u
        (Module.finBasis ℝ E l) v) t₀ := by
    intro m l
    have h : ContinuousAt (fun p : ℝ × M => rmP (G p.1) p.2
        (smoothExt x ((Module.finBasis ℝ E m : E) : TangentSpace I x) p.2)
        (smoothExt x u p.2) (smoothExt x ((Module.finBasis ℝ E l : E) : TangentSpace I x) p.2)
        (smoothExt x v p.2)) (t₀, x) :=
      (rmP_jointSmoothNoCompact (I := I) (M := M) hLC hJ hG ht₀ x
        (A := smoothExt x ((Module.finBasis ℝ E m : E) : TangentSpace I x))
        (B := smoothExt x u)
        (C := smoothExt x ((Module.finBasis ℝ E l : E) : TangentSpace I x))
        (D := smoothExt x v)
        (smoothExt_cmdiff x _) (smoothExt_cmdiff x u) (smoothExt_cmdiff x _)
        (smoothExt_cmdiff x v)).continuousAt
    refine (h.comp (x := t₀) (f := fun t : ℝ => (t, x)) hcx).congr ?_
    filter_upwards with t
    simp only [Function.comp_apply, smoothExt_apply]
  -- assemble the finite double sum
  exact continuousAt_finSum _ (fun m _ => continuousAt_finSum _ (fun l _ =>
    (hGramC m l).mul (hRmP m l)))

end

end Work.Diff.EXT
