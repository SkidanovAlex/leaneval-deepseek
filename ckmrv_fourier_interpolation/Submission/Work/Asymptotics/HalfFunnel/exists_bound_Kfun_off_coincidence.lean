/-
# The CKMRV kernel is bounded away from the coincidence divisor

`K^{(d)}(τ,z)` is meromorphic with simple poles exactly on `{j τ = j z}`; at a simple pole it
blows up, so on a compact set `S × T` the only obstruction to a uniform bound is a coincidence
`j τ = j z` (those points are covered separately by
`Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence`).  This file proves the
off-coincidence companion: if `j` separates `S` from `T` then `Kfun` is uniformly bounded on
`S × T`.

The proof uses the master identity `Kfun ℓ d τ z * (j τ - j z) = AfunFun ℓ d τ z`
(`Work.Asymptotics.Kfun_mul_slope_eq_AfunFun`), i.e. off the divisor
`Kfun = AfunFun / (j τ - j z)`, together with the continuity of `AfunFun` in both variables.
-/
import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence

open UpperHalfPlane

namespace Work.Asymptotics.HalfFunnel

open Work.Kernels

noncomputable section

/-- **The kernel is bounded on a compact set disjoint from the coincidence divisor.**  If
`j τ ≠ j z` for all `(τ,z) ∈ S × T` with `S`, `T` compact, then `‖K^{(d)}(τ,z)‖` is bounded on
`S × T` (by `max (sup) 1`, to keep the constant positive). -/
theorem exists_bound_Kfun_off_coincidence (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {S T : Set ℍ} (hS : IsCompact S) (hT : IsCompact T)
    (hsep : ∀ (τ : ℍ), τ ∈ S → ∀ (z : ℍ), z ∈ T →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℍ), τ ∈ S → ∀ (z : ℍ), z ∈ T →
      ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ C := by
  have hjcont : Continuous (fun p : ℍ × ℍ =>
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun p.2) :=
    (Work.Asymptotics.MiddleRange.continuous_jInvariantFun.comp continuous_fst).sub
      (Work.Asymptotics.MiddleRange.continuous_jInvariantFun.comp continuous_snd)
  have hne : ∀ p : ℍ × ℍ, p ∈ S ×ˢ T →
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun p.2 ≠ 0 := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact sub_ne_zero.mpr (hsep p.1 hp.1 p.2 hp.2)
  have hinv : ContinuousOn (fun p : ℍ × ℍ =>
      (Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun p.2)⁻¹) (S ×ˢ T) :=
    hjcont.continuousOn.inv₀ hne
  have hF : ContinuousOn (fun p : ℍ × ℍ =>
      AfunFun ℓ d p.1 p.2 * (Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun p.2)⁻¹)
      (S ×ˢ T) :=
    ((continuous_AfunFun ℓ d).continuousOn).mul hinv
  obtain ⟨C, hC⟩ := (hS.prod hT).exists_bound_of_continuousOn hF
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ hτ z hz => ?_⟩
  have hne' : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := hsep τ hτ z hz
  have hid := Kfun_mul_slope_eq_AfunFun ℓ d hd τ z hne'
  have hval : Work.Kernels.Kfun ℓ d τ z =
      AfunFun ℓ d τ z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (sub_ne_zero.mpr hne')]
    exact hid
  rw [hval]
  exact le_trans (hC (τ, z) ⟨hτ, hz⟩) (le_max_left _ _)

end

end Work.Asymptotics.HalfFunnel
