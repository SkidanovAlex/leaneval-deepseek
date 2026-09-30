import Mathlib
import Submission.Work.SSS.serreE1Snd
import Submission.Work.SSS.grFMap
import Submission.Work.SSS.serreSubcomplexToN

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-- Evaluation of an arbitrary simplex `σ : Δ[P] ⟶ Y` on a simplex `a` of `Δ[P]`, in terms of
the `P`-simplex `SSet.yonedaEquiv σ` that `σ` is attached to. -/
lemma sigma_app_apply_eq_yoneda {Y : SSet.{0}} {P n : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (a : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) _⦋n⦌) :
    σ.app (op ⦋n⦌) a = Y.map (SSet.stdSimplex.objEquiv a).op (SSet.yonedaEquiv σ) := by
  conv_lhs => rw [← Equiv.symm_apply_apply
    (SSet.yonedaEquiv (X := Y) (n := SimplexCategory.mk P)) σ]
  exact (SSet.stdSimplex.map_objEquiv_op_apply (X := Y) (SSet.yonedaEquiv σ) (m := op ⦋n⦌) a).symm

/-- A face of a simplex `b : Y _⦋P⦌` has nondegenerate part of dimension at most that of `b`. -/
lemma toN_dim_le_map_of_simplex {Y : SSet.{0}} {P n : ℕ} (b : Y _⦋P⦌) (v : ⦋n⦌ ⟶ ⦋P⦌) :
    (SSet.S.mk (Y.map v.op b)).toN.dim ≤ (SSet.S.mk b).toN.dim := by
  have hle : (SSet.S.mk (Y.map v.op b)).subcomplex ≤ (SSet.S.mk b).subcomplex :=
    SSet.S.subcomplex_map_le _ _ v rfl
  have h1 : (SSet.S.mk (Y.map v.op b)).toN ≤ (SSet.S.mk b).toN := by
    rw [SSet.N.le_iff, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    exact hle
  exact SSet.N.dim_le_of_le h1

/-- The nondegenerate part of the `X`-component of a simplex of `T_σ = Δ[P] ×_Y X` has dimension
at most that of the nondegenerate part of the base simplex `SSet.yonedaEquiv σ`. -/
lemma snd_toN_dim_le {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (w : (pullAlong f σ).obj (op ⦋n⦌)) :
    (SSet.S.mk (f.app (op ⦋n⦌) ((pullback.snd σ f).app (op ⦋n⦌) w))).toN.dim ≤
      (SSet.S.mk (SSet.yonedaEquiv σ)).toN.dim := by
  have hcond : σ.app (op ⦋n⦌) ((pullback.fst σ f).app (op ⦋n⦌) w) =
      f.app (op ⦋n⦌) ((pullback.snd σ f).app (op ⦋n⦌) w) :=
    congr($(pullback.condition (f := σ) (g := f)).app (op ⦋n⦌) w)
  rw [← hcond, sigma_app_apply_eq_yoneda]
  exact toN_dim_le_map_of_simplex (SSet.yonedaEquiv σ)
    (SSet.stdSimplex.objEquiv ((pullback.fst σ f).app (op ⦋n⦌) w))

/-- The nondegenerate part of a degenerate `P`-simplex has dimension `< P`. -/
lemma toN_dim_lt_of_not_nonDegenerate {Y : SSet.{0}} {P : ℕ} (b : Y _⦋P⦌)
    (hb : b ∉ Y.nonDegenerate P) : (SSet.S.mk b).toN.dim < P := by
  have hdeg : b ∈ Y.degenerate P := by
    rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]; exact hb
  rw [SSet.mem_degenerate_iff] at hdeg
  obtain ⟨m, hm, g, _hg, y, hy⟩ := hdeg
  have h1 : (SSet.S.mk b).toN.dim ≤ (SSet.S.mk y).toN.dim := by
    rw [← hy]
    exact toN_dim_le_map_of_simplex y g
  have h3 : (SSet.S.mk y).toN.dim ≤ m := SSet.S.dim_toN_le (SSet.S.mk y)
  omega

/-- **Range bounds for the second projection of a pullback.**  For a morphism `f : X ⟶ Y` of
simplicial sets and a simplex `σ : Δ[P] ⟶ Y`:

* the image of `pullback.snd σ f : T_σ ⟶ X` always lies in `R_{P+1} = f ⁻¹' (sk (P+1))`;
* if `σ` is *degenerate* (its nondegenerate part has dimension `< P`), the image lies in
  `R_P = f ⁻¹' (sk P)`.

The first bound is the general form of `Work.SSS.T_range_le`; the second is what makes the
degenerate face terms of the boundary of a lifted σ-cycle vanish in the graded piece
`grF = R_{s+2}/R_{s+1}`. -/
theorem sndToSerre_range {X Y : SSet.{0}} (f : X ⟶ Y) :
    (∀ {P : ℕ} (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y),
        SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.StemsB.serreSubcomplex f (P+1))
    ∧
    (∀ {P : ℕ} (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y),
        SSet.yonedaEquiv σ ∉ Y.nonDegenerate P →
        SSet.Subcomplex.range (pullback.snd σ f) ≤ Work.StemsB.serreSubcomplex f P) := by
  constructor
  · intro P σ
    rw [Subfunctor.le_def]
    intro n w hw
    rw [Subfunctor.range_obj] at hw
    obtain ⟨w₀, rfl⟩ := hw
    rw [Work.SSS.serreSubcomplexToN]
    have h := snd_toN_dim_le f σ w₀
    have h2 : (SSet.S.mk (SSet.yonedaEquiv σ)).toN.dim ≤ P :=
      SSet.S.dim_toN_le (SSet.S.mk (SSet.yonedaEquiv σ))
    exact Nat.lt_of_le_of_lt h (Nat.lt_succ_of_le h2)
  · intro P σ hσ
    rw [Subfunctor.le_def]
    intro n w hw
    rw [Subfunctor.range_obj] at hw
    obtain ⟨w₀, rfl⟩ := hw
    rw [Work.SSS.serreSubcomplexToN]
    have h := snd_toN_dim_le f σ w₀
    have h2 : (SSet.S.mk (SSet.yonedaEquiv σ)).toN.dim < P :=
      toN_dim_lt_of_not_nonDegenerate (SSet.yonedaEquiv σ) hσ
    exact Nat.lt_of_le_of_lt h h2

end

end Work.SSS
