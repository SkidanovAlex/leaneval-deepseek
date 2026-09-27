import Mathlib
import Submission.Work.EKLC8Core.Vol

open MeasureTheory

namespace Work.EKLC8Core

/-- Scaling transfer for `BadAt`, without any hypothesis on the sign of `ρ`: if `ν₁` is
`InXrho`-bad (`ν₁[−ρ,ρ] < ½ ν₁[−1,1]`) and the two measures are related by the normalised
radial scaling `hscale`, then `ν₀` is `BadAt ρ S`.

The proof is the elementary comparison
`ν₀[−ρS,ρS] = ν₁[−ρ,ρ] · ν₀[−S,S] < ½ · ν₀[−S,S]`,
where the equality is `hscale` at `σ = ρ` together with `ν₁[−1,1] = 1`, and the strict
inequality uses `ν₀[−S,S] > 0` (which follows from `ν₀[−1,1] = 1` and `S ≥ 1`).  No
hypothesis on the sign of `ρ` is needed: `ρ` only enters through the interval endpoints,
and negative or zero `ρ` are handled by the same multiplication. -/
theorem step7_transfer_nopos {ν₀ ν₁ : MeasureTheory.Measure ℝ} {ρ S : ℝ} (hS : 1 ≤ S)
    (hnorm₀ : ν₀.real (Set.Icc (-1) 1) = 1) (hnorm₁ : ν₁.real (Set.Icc (-1) 1) = 1)
    (hfin : ν₀ (Set.Icc (-S) S) ≠ ⊤)
    (hscale : ∀ σ : ℝ, ν₁.real (Set.Icc (-σ) σ) * ν₀.real (Set.Icc (-S) S)
        = ν₀.real (Set.Icc (-(σ * S)) (σ * S)) * ν₁.real (Set.Icc (-1) 1))
    (hbad : Work.EKLC8Core.BadAt ν₁ ρ 1) : Work.EKLC8Core.BadAt ν₀ ρ S := by
  -- `ν₀ [-S,S] > 0`: it dominates `ν₀ [-1,1] = 1` because `S ≥ 1`.
  have hpos : 0 < ν₀.real (Set.Icc (-S) S) := by
    have hsub : Set.Icc (-1) 1 ⊆ Set.Icc (-S) S := by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2]
    have h := measureReal_mono hsub hfin
    rw [hnorm₀] at h
    linarith
  -- `hscale` at `σ = ρ`, using `ν₁[-1,1] = 1`.
  have hs := hscale ρ
  rw [hnorm₁, mul_one] at hs
  -- `BadAt ν₁ ρ 1` gives `ν₁[-ρ,ρ] < 1/2`.
  have hb : ν₁.real (Set.Icc (-ρ) ρ) < 1 / 2 := by
    simpa [BadAt, hnorm₁] using hbad
  rw [BadAt]
  rw [← hs]
  exact mul_lt_mul_of_pos_right hb hpos

end Work.EKLC8Core
