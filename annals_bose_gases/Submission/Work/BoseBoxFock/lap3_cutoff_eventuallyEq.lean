import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.lap3_decay_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lap3_cutoff_eventuallyEq`

The cutoff families `θ R` of `cutFam_exists` (see `CutoffHyp`) are the identity on `closedBall 0 R`
and vanish outside `closedBall 0 (2R)`.  Consequently, for a *fixed* `x` and smooth `g`, the
truncated function `y ↦ θ R y · g y` agrees with `g` on a whole neighbourhood of `x` as soon as
`R > ‖x‖`; since `Δ³ = lap3` is a differential operator it only sees the germ at `x`, so

`∀ᶠ R in atTop, lap3 (fun y => (θ R y : ℂ) * g y) x = lap3 g x`.

The germ statement is isolated as `lap3_congr_of_eventuallyEq`: `dIter` (hence `lap3`) is
invariant under `EventuallyEq` at the point, proved by induction on the list of directions using
`Filter.EventuallyEq.fderiv`.

No smoothness of `g` is needed for the conclusion (the hypothesis `hg` is kept in the statement to
fix the intended use): `lap3` is a sum of iterated `fderiv`s, which are defined unconditionally and
are local at their base point.
-/

noncomputable section

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. `dIter` and `lap3` depend only on the germ at the point -/

/-- The iterated directional derivative depends only on the germ: if `f =ᶠ[𝓝 x] g` then
`dIter f L =ᶠ[𝓝 x] dIter g L` for every list of directions `L`. -/
lemma dIter_eventuallyEq {f g : E3 → ℂ} {x : E3} (h : f =ᶠ[nhds x] g) (L : List E3) :
    dIter f L =ᶠ[nhds x] dIter g L := by
  induction L with
  | nil => simpa using h
  | cons v L ih =>
    have hf : fderiv ℝ (dIter f L) =ᶠ[nhds x] fderiv ℝ (dIter g L) := ih.fderiv (𝕜 := ℝ)
    filter_upwards [hf] with y hy
    simp only [dIter_cons]
    rw [hy]

/-- `Δ³ = lap3` depends only on the germ at the point. -/
lemma lap3_congr_of_eventuallyEq {f g : E3 → ℂ} {x : E3} (h : f =ᶠ[nhds x] g) :
    lap3 f x = lap3 g x := by
  show (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, dIter f (lap3List a b c) x)
    = (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, dIter g (lap3List a b c) x)
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => ?_)))
  exact (dIter_eventuallyEq h (lap3List a b c)).eq_of_nhds

/-! ## 2. The truncation is eventually the identity near a fixed point -/

theorem lap3_cutoff_eventuallyEq {θ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hθ : Work.BoseBoxFock.CutoffHyp θ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ∀ᶠ R in Filter.atTop,
      Work.BoseBoxFock.lap3 (fun y => ((θ R y : ℝ) : ℂ) * g y) x = Work.BoseBoxFock.lap3 g x := by
  have _hg := hg
  -- take `R` beyond `‖x‖`
  have hgt : ∀ᶠ R in Filter.atTop, ‖x‖ < R :=
    Filter.eventually_atTop.mpr ⟨‖x‖ + 1, fun R hR => lt_of_lt_of_le (lt_add_one ‖x‖) hR⟩
  filter_upwards [hgt] with R hR
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg x) hR
  -- `θ R = 1` on the open ball of radius `R`, a neighbourhood of `x`
  have hnb : ∀ᶠ y in nhds x, ‖y‖ < R :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hR
  have heq : (fun y : E3 => ((θ R y : ℝ) : ℂ) * g y) =ᶠ[nhds x] g := by
    filter_upwards [hnb] with y hy
    rw [hθ.eq_one R hpos y hy.le]
    simp
  exact lap3_congr_of_eventuallyEq heq

end Work.BoseBoxFock

end
