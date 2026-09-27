import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.k0_basic
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.K0map.map_comp
import Submission.Work.KT.K0map.map_id

/-!
# `Work.KT.HopfK.augPair_K0_independent`

The augmentation `augPair (Eu m) y : Kpair (Eu m) →ₐ[ℂ] ℂ` is evaluation at the point `y` of the
closed unit ball of `Eu m = ℝ^{2m}`, restricted to the functions on the ball that are constant on
the boundary sphere.  Its image under `K₀` — an additive map `K₀ (Kpair (Eu m)) →+ K₀ ℂ` — is
**independent of the point `y`**.

The mathematical content is that `K₀` is a homotopy invariant of `ℂ`-algebra homomorphisms: if
`γ : [0,1] → Ball (Eu m)` is a continuous path then for every idempotent matrix `p` over
`Kpair (Eu m)` the path `t ↦ p.2.map (augPair (Eu m) (γ t))` is a continuous path of *idempotent*
complex matrices, so its two ends have the same `K₀(ℂ)`-class
(`Work.KT.Fund.cls_eq_of_path`, the `R = ⊤` case of `Work.KT.homotopy_inv`).  Since the ball is
convex, any two of its points are joined by such a path — the straight line segment.

Both `y` and `y'` are arbitrary points of the ball (in particular they may lie on the boundary, or
in the interior); no hypothesis on them is needed.
-/

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

/-! ## Extensionality of additive maps out of `K₀` on the classes `cls p` -/

/-- An additive homomorphism out of `K₀` is determined by its values on the classes `cls p` of
matrices. -/
lemma k0_hom_ext_cls {A B : Type} [Ring A] [Ring B] {F G : K0 A →+ K0 B}
    (h : ∀ p : Mat A, F (cls p) = G (cls p)) : F = G := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | H x =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p => exact h p
  | neg p ih =>
    simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢
    rw [ih]
  | add p q ihp ihq =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ihp ihq ⊢
    rw [ihp, ihq]

/-! ## The straight line segment in the unit ball -/

/-- The straight line from `y` to `y'` in the closed unit ball of `Eu m`, as a continuous path.

The ball is convex (`convex_closedBall`), so `(1 - t) • y + t • y'` stays inside it. -/
def ballPath (m : ℕ) (y y' : Ball (Eu m)) : C(unitInterval, Ball (Eu m)) where
  toFun t := ⟨(1 - (t : ℝ)) • (y : Eu m) + (t : ℝ) • (y' : Eu m), by
    apply convex_closedBall (0 : Eu m) 1 y.2 y'.2
    · linarith [t.2.2]
    · exact t.2.1
    · ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)

@[simp] lemma ballPath_zero (m : ℕ) (y y' : Ball (Eu m)) : ballPath m y y' 0 = y := by
  apply Subtype.ext
  simp [ballPath]

@[simp] lemma ballPath_one (m : ℕ) (y y' : Ball (Eu m)) : ballPath m y y' 1 = y' := by
  apply Subtype.ext
  simp [ballPath]

/-! ## Evaluation along a path -/

/-- The image under `K₀` of the augmentation `augPair (Eu m) y` is unchanged when `y` is moved
along a continuous path in the ball. -/
lemma augPair_mapA_eq_of_path (m : ℕ) (y y' : Ball (Eu m)) (γ : C(unitInterval, Ball (Eu m)))
    (h0 : γ 0 = y) (h1 : γ 1 = y') :
    K0.mapA (augPair (Eu m) y) = K0.mapA (augPair (Eu m) y') := by
  refine k0_hom_ext_cls fun p => ?_
  by_cases hp : p.IsIdem
  · -- the class of a fixed idempotent matrix is carried along a path of idempotent matrices
    let Γ : unitInterval → Matrix (Fin p.1) (Fin p.1) ℂ :=
      fun t => p.2.map (augPair (Eu m) (γ t))
    have hΓcont : Continuous Γ := by
      apply continuous_matrix
      intro i j
      have hfun : (fun t : unitInterval => Γ t i j)
          = fun t => ((p.2 i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) (γ t) := by
        funext t
        simp only [Γ, Matrix.map_apply]
        rfl
      rw [hfun]
      exact ((p.2 i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)).continuous.comp γ.continuous
    have hΓidem : ∀ t, Γ t * Γ t = Γ t := by
      intro t
      simp only [Γ]
      rw [← Matrix.map_mul, hp]
    have hpath := Work.KT.Fund.cls_eq_of_path ℂ Γ hΓcont hΓidem
    have hΓ0 : (⟨p.1, Γ 0⟩ : Mat ℂ) = p.map (augPair (Eu m) y) := by
      show (⟨p.1, Γ 0⟩ : Mat ℂ) = ⟨p.1, p.2.map (augPair (Eu m) y)⟩
      simp only [Γ, h0]
    have hΓ1 : (⟨p.1, Γ 1⟩ : Mat ℂ) = p.map (augPair (Eu m) y') := by
      show (⟨p.1, Γ 1⟩ : Mat ℂ) = ⟨p.1, p.2.map (augPair (Eu m) y')⟩
      simp only [Γ, h1]
    simp only [K0.mapA, K0map.map_cls, mapCls, if_pos hp]
    rw [show Work.KT.Mat.map (augPair (Eu m) y).toRingHom p = (⟨p.1, Γ 0⟩ : Mat ℂ)
          from hΓ0.symm,
      show Work.KT.Mat.map (augPair (Eu m) y').toRingHom p = (⟨p.1, Γ 1⟩ : Mat ℂ)
          from hΓ1.symm]
    exact hpath
  · -- a non-idempotent generator contributes nothing on either side
    simp only [K0.mapA, K0map.map_cls, mapCls, if_neg hp]

/-! ## The theorem -/

/-- **The augmentation on `K₀` is independent of the chosen point of the ball.** -/
theorem augPair_K0_independent (m : ℕ) (y y' : Ball (Eu m)) :
    K0.mapA (augPair (Eu m) y) = K0.mapA (augPair (Eu m) y') :=
  augPair_mapA_eq_of_path m y y' (ballPath m y y') (ballPath_zero m y y')
    (ballPath_one m y y')

end

end Work.KT.HopfK
