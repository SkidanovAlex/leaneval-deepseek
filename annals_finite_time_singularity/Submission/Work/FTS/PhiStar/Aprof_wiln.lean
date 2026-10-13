/-
# `Work.FTS.PhiStar.Aprof_wiln` — the flat radial profile `Aprof` is `O(α)` in `𝒲^{4,∞}`

The function `Aprof α = GzProfile α − ThetaProfile` is the radial factor of the flat
presentation `Φ̃_* = Aprof α(z)·sin 2θ + α φ ψ + R` of `Φ_*` (`Defs.lean`).

The point of the estimate is the *cancellation* `Gstar α (F_*) = −Θ/sin 2θ` on `z ≥ 0`
(`L12(F_*) = 2α/(1+z)`), which identifies

`Aprof α = −Gbar α (F_*)`   on `{z > 0}`,

so the whole content is the already-proved `O(α)` bound for `Ḡ` (`Gbar_wiln`).  Since
`Aprof` is *radial*, every angular slot of `WlInf` vanishes (`DthIter_radial`), and the
norm collapses to the sum of the five radial sup norms (`WlInf_radial`).

The only subtlety is the endpoint `z = 0`, where the `deriv`-iterates of `Aprof` are
junk as soon as `Aprof` stops being differentiable: the left of `0` has nothing to do
with `−Dk (5/α) 0`.  This is handled exactly as in `Gbar_wiln`: `Aprof α 0 = 0` and
`Aprof α = −Dk (5/α) 0` on `(0,∞)`, so `deriv_iter_value` applied to `−(Aprof α)`
shows that each iterate at `0` is either `0` or `−Dk (5/α) k 0`, and both are
`≤ 3456/N ≤ 3456 α` by `Dk_bound`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Negation and the `deriv`-iterates -/

/-- Negation commutes with the `deriv`-iterates. -/
theorem deriv_iter_neg (f : ℝ → ℝ) (k : ℕ) :
    (deriv^[k]) (fun z => -f z) = fun z => -((deriv^[k]) f z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    rw [Function.iterate_succ_apply', ih, deriv.fun_neg', Function.iterate_succ_apply']

/-! ## The value of `Aprof` at `0` -/

/-- `Aprof α 0 = 0`: at `z = 0` one has `Gstar α (F_*) 0 = −1/2` (because `L₁₂(F_*) 0 = 2α`),
`Ḡ 0 = 0` and `Θ/sin 2θ = 1/2`. -/
theorem Aprof_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : Aprof α 0 = 0 := by
  have hL0 : Work.Construction.L12 (Work.Construction.Fstar α) 0 = 2 * α := by
    simpa using L12_profile_eq (α := α) hα hα1 (le_refl (0 : ℝ))
  have hL0' : Work.Elliptic.L12 (Work.Construction.Fstar α) 0 = 2 * α := hL0
  have hGS0 : Work.Elliptic.Gstar α (Work.Construction.Fstar α) 0 = -(1 / 2) := by
    rw [Work.Elliptic.Gstar, hL0']
    field_simp
    norm_num
  have hGB0 : Work.Elliptic.Gbar α (Work.Construction.Fstar α) 0 = 0 := by
    rw [Work.Elliptic.Gbar, Real.zero_rpow (by
      intro h
      have hpos : (0 : ℝ) < 5 / α := div_pos (by norm_num) hα
      have h5 : (5 : ℝ) / α = 0 := by linarith
      rw [h5] at hpos
      norm_num at hpos)]
    simp
  simp only [Aprof, GzProfile, Work.Elliptic.Gsing]
  rw [hGS0, hGB0, ThetaProfile]
  norm_num

/-! ## The identification `Aprof α = −Gbar α (F_*)` on `z > 0` -/

/-- On `z ≥ 0` the singular term `G_*` is `−Θ/sin 2θ = −1/(2(1+z))`, so `Aprof α` —
which is `−(G_* + Ḡ) − Θ/sin 2θ` — equals `−Ḡ = −Dk (5/α) 0`. -/
theorem Aprof_eqOn_negDk {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    EqOn (Aprof α) (fun z => -Work.FTS.H2.PhiStarE.Dk (5 / α) 0 z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  have hL : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    L12_profile_eq hα hα1 hz0
  have hL' : Work.Elliptic.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := hL
  have hGS : Work.Elliptic.Gstar α (Work.Construction.Fstar α) z = -ThetaProfile z := by
    rw [Work.Elliptic.Gstar, hL', ThetaProfile]
    have h1z : (1 + z) ≠ 0 := by linarith
    field_simp
    ring
  have hGB : Work.Elliptic.Gbar α (Work.Construction.Fstar α) z
      = Work.FTS.H2.PhiStarE.Dk (5 / α) 0 z := by
    have h := Work.FTS.H2.PhiStarE.Gbar_eq_of_nonneg α hα hα1 hz0
    rw [h]
    simp only [Work.FTS.H2.PhiStarE.Dk_zero, Work.FTS.H2.PhiStarE.Pi_def]
  simp only [Aprof, GzProfile, Work.Elliptic.Gsing]
  rw [hGS, hGB]
  ring

/-! ## The weighted pointwise bound -/

/-- The weighted pointwise bound for the `deriv`-iterates of `Aprof`, `k ≤ 4`,
`0 ≤ z ≤ ∞`: `|(z+1)^k ∂_z^k Aprof α| ≤ 3456 α`. -/
theorem Aprof_iter_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ k ≤ 4, ∀ z ∈ Work.Spaces.Iz,
      |(z + 1) ^ k * (deriv^[k]) (Aprof α) z| ≤ 3456 * α := by
  have hNpos : (0 : ℝ) < 5 / α := div_pos (by norm_num) hα
  have hN0 : (0 : ℝ) ≤ 5 / α := le_of_lt hNpos
  have hN5 : (5 : ℝ) ≤ 5 / α := by
    rw [le_div_iff₀ hα]; linarith
  have harith : 3456 / (5 / α) ≤ 3456 * α := by
    have h5 : α * (5 / α) = 5 := by field_simp
    rw [div_le_iff₀ (div_pos (by norm_num) hα),
      show (3456 : ℝ) * α * (5 / α) = 3456 * (α * (5 / α)) from by ring, h5]
    linarith
  have hAprof_eq := Aprof_eqOn_negDk hα hα1
  have hAprof0 := Aprof_zero hα hα1
  have hF : EqOn (fun z => -Aprof α z) (Work.FTS.H2.PhiStarE.Dk (5 / α) 0) (Set.Ioi 0) := by
    intro w hw
    show -Aprof α w = _
    rw [hAprof_eq hw, neg_neg]
  have hF0 : (fun z => -Aprof α z) 0 = 0 := by
    show -Aprof α 0 = 0
    rw [hAprof0, neg_zero]
  intro k hk z hz
  have hzle : (0 : ℝ) ≤ z := hz
  rw [show z + 1 = 1 + z from by ring]
  rcases eq_or_lt_of_le hzle with hz0 | hz0
  · subst hz0
    rcases Work.FTS.H2.PhiStarE.deriv_iter_value (5 / α) hN0 (fun z => -Aprof α z) hF hF0 k hk
      with h | h
    · have hz' : (deriv^[k]) (Aprof α) 0 = 0 := by
        rw [deriv_iter_neg] at h
        linarith
      rw [hz']
      simp only [mul_zero, abs_zero]
      positivity
    · have hz' : (deriv^[k]) (Aprof α) 0 = -(Work.FTS.H2.PhiStarE.Dk (5 / α) k 0) := by
        rw [deriv_iter_neg] at h
        linarith
      rw [hz', mul_neg, abs_neg]
      exact (Work.FTS.H2.PhiStarE.Dk_bound (5 / α) hN5 k hk (le_refl (0 : ℝ))).trans harith
  · have h2 := Work.FTS.H2.PhiStarE.EqOn_iter_Dk (5 / α) hN0 (fun z => -Aprof α z) hF k hk hz0
    have hz' : (deriv^[k]) (Aprof α) z = -(Work.FTS.H2.PhiStarE.Dk (5 / α) k z) := by
      rw [deriv_iter_neg] at h2
      linarith
    rw [hz', mul_neg, abs_neg]
    exact (Work.FTS.H2.PhiStarE.Dk_bound (5 / α) hN5 k hk hz).trans harith

/-! ## The `𝒲^{4,∞}` estimate -/

theorem Aprof_wiln {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (fun z θ => Aprof α z) ∧
    Work.Spaces.WlInf α 4 (fun z θ => Aprof α z) ≤ 20000 * α := by
  have hbound := Aprof_iter_bound hα hα1
  refine ⟨?_, ?_⟩
  · refine ⟨fun k hk => ?_, fun j hj k hk hj1 hkj => ?_⟩
    · refine ⟨3456 * α, fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      show |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => Aprof α z) z θ| ≤ 3456 * α
      rw [Work.FTS.H2.PhiStarE.pzIter_radial]
      exact hbound k hk z hz
    · refine ⟨0, fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => Aprof α z))
          = fun _ _ => (0 : ℝ) := by
        rw [Work.FTS.H2.PhiStarE.DthIter_radial (Aprof α) j hj1,
          Work.FTS.H2.PhiStarE.pzIter_zero_fun]
      simp only [h1, mul_zero, zero_mul, zero_div, abs_zero]
      exact le_refl 0
  · rw [Work.FTS.H2.PhiStarE.WlInf_radial]
    calc ∑ k ∈ Finset.range 5, Work.Spaces.supAbs
            (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => Aprof α z) z θ)
        ≤ ∑ k ∈ Finset.range 5, (3456 * α) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk4 : k ≤ 4 := by
            rw [Finset.mem_range] at hk; omega
          refine csSup_le ⟨|(0 + 1) ^ k * Work.Spaces.pzIter k
              (fun z θ => Aprof α z) 0 0|,
              0, by simp [Work.Spaces.Iz], 0, ?_, rfl⟩ fun y hy => ?_
          · simp only [Work.Spaces.Iθ, Set.mem_Icc]
            exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
          · obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
            show |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => Aprof α z) z θ| ≤ 3456 * α
            rw [Work.FTS.H2.PhiStarE.pzIter_radial]
            exact hbound k hk4 z hz
      _ = 5 * (3456 * α) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
      _ ≤ 20000 * α := by nlinarith [hα]

end Work.FTS.PhiStar
