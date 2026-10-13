import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS_EllLimOK.HkSq_le_of_JConv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JConvAux.ae_tendsto_HkIntegrand_slice` — the integrand converges

The `ℋ^k`-integrand `HkIntegrand α k f z θ` is a finite sum of squares of terms
`slot · weight(z,θ)`, where `slot` runs over the mixed derivatives `D_z^j D_θ^i f` with
`j + i ≤ k` (and `mixed i 0 = DzIter i` supplies the first sum).  Hence, at a fixed `(z,θ)`,
convergence of the slots gives convergence of the integrand.  Off the open quadrant the weights
degenerate (`w 0 = 0`, so both sums vanish at `z = 0`; `sin(2θ) = 0` kills the denominators and
every mixed slot with `i ≥ 1`, which is why no positivity of `α` is needed), so the statement
holds at *every* point of `Iz × Iθ`, in particular a.e.

The elementary ingredients (`tendsto_HkIntegrand_of_tendsto_mixed` and the two degeneracy lemmas
`HkIntegrand_fst_zero`, `HkIntegrand_eq_zero_of_sin_eq_zero`) are the helpers of
`FTS_EllLimOK.HkSq_le_of_JConv`, whose proof uses this statement in turn.
-/
open scoped Real Topology
open MeasureTheory Filter

namespace Work.FTS_EllLimOK.JConvAux

theorem ae_tendsto_HkIntegrand_slice {α : ℝ} {k : ℕ} {Ψn : ℕ → ℝ → ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hconv : ∀ j i : ℕ, j + i ≤ k → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Ψn n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Ψ z θ)))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop
        (nhds (Work.Spaces.HkIntegrand α k Ψ z θ)) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [MeasureTheory.ae_restrict_iff' hIθ]
  refine Filter.Eventually.of_forall fun θ hθ => ?_
  by_cases hz0 : z = 0
  · subst hz0
    have h1 : ∀ n, Work.Spaces.HkIntegrand α k (Ψn n) 0 θ = 0 :=
      fun n => HkIntegrand_fst_zero α k (Ψn n) θ
    have h2 : Work.Spaces.HkIntegrand α k Ψ 0 θ = 0 := HkIntegrand_fst_zero α k Ψ θ
    rw [show (fun n => Work.Spaces.HkIntegrand α k (Ψn n) 0 θ) = fun _ => (0 : ℝ) from
      funext h1, h2]
    exact tendsto_const_nhds
  · by_cases hsin : Real.sin (2 * θ) = 0
    · have h1 : ∀ n, Work.Spaces.HkIntegrand α k (Ψn n) z θ = 0 :=
        fun n => HkIntegrand_eq_zero_of_sin_eq_zero α k (Ψn n) z θ hsin
      have h2 : Work.Spaces.HkIntegrand α k Ψ z θ = 0 :=
        HkIntegrand_eq_zero_of_sin_eq_zero α k Ψ z θ hsin
      rw [show (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) = fun _ => (0 : ℝ) from
        funext h1, h2]
      exact tendsto_const_nhds
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hθ0 : 0 < θ := by
        rcases lt_or_eq_of_le hθ.1 with h' | h'
        · exact h'
        · exact absurd (by rw [← h']; simp) hsin
      have hθpi : θ < π / 2 := by
        rcases lt_or_eq_of_le hθ.2 with h' | h'
        · exact h'
        · exact absurd (by rw [h', show 2 * (π / 2) = π by ring]; exact Real.sin_pi) hsin
      exact tendsto_HkIntegrand_of_tendsto_mixed (α := α) (k := k) (fn := Ψn) (f := Ψ)
        (p := (z, θ)) (fun j i hji => hconv j i hji z θ (by
          rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
          exact ⟨hzpos, hθ0, hθpi⟩))

end Work.FTS_EllLimOK.JConvAux
