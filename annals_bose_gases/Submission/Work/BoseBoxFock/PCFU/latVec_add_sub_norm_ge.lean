import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.LatVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.latVec_add_sub_norm_ge`

**The separation lemma of the `Ksfr`-image bound.**  Let `α β : ℝ³` with `|α m| ≤ 1/2` for every
coordinate `m` (i.e. `α` lies in the cube of side `1`) and `‖β‖ ≤ 1/2 - δ`.  Then for every
*nonzero* integer vector `d : Fin 3 → ℤ`,

    δ ≤ ‖latVec d + α - β‖ .

**Why.**  Since `d ≠ 0` some coordinate satisfies `|d m| ≥ 1`, whence
`|(latVec d + α) m| = |d m + α m| ≥ 1 - 1/2 = 1/2` and therefore `‖latVec d + α‖ ≥ 1/2`
(the Euclidean norm dominates every coordinate, `PiLp.norm_apply_le`).  The triangle inequality
gives `‖latVec d + α - β‖ ≥ ‖latVec d + α‖ - ‖β‖ ≥ 1/2 - (1/2 - δ) = δ`.

This is the geometric input of `Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le`: with
`α = ℓ⁻¹ • u` for `u ∈ acube ℓ` and `β = ℓ⁻¹ • b`, the hypothesis on `β` is exactly the
nonvanishing of the scaled bump `chiScale ℓ b` (whose flatness at the boundary is quantified by
`δ = 1/2 - ‖ℓ⁻¹ • b‖`).  Consequently the `d ≠ 0` images `ℓ • latVec d + (u - b)` are all at
distance at least `ℓ δ` from the origin.
-/

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock.PCFU

theorem latVec_add_sub_norm_ge {δ : ℝ} {α β : E3}
    (hα : ∀ m : Fin 3, |α m| ≤ 1 / 2) (hβ : ‖β‖ ≤ 1 / 2 - δ) :
    ∀ d : Fin 3 → ℤ, d ≠ 0 → δ ≤ ‖Work.BoseBoxFock.latVec d + α - β‖ := by
  intro d hd
  obtain ⟨m, hm⟩ : ∃ m, d m ≠ 0 := Function.ne_iff.mp hd
  have h1 : (1 : ℝ) ≤ |((d m : ℤ) : ℝ)| := by
    have h : (1 : ℤ) ≤ |d m| := Int.one_le_abs hm
    exact_mod_cast h
  -- a coordinate of `latVec d + α` has modulus at least `1/2`
  have hcoord : (1 / 2 : ℝ) ≤ |(Work.BoseBoxFock.latVec d + α) m| := by
    have hsplit : (Work.BoseBoxFock.latVec d + α) m = ((d m : ℤ) : ℝ) + α m := by
      simp [Work.BoseBoxFock.latVec]
    rw [hsplit]
    have h2 : |α m| ≤ 1 / 2 := hα m
    have h3 : |((d m : ℤ) : ℝ)| - |α m| ≤ |((d m : ℤ) : ℝ) + α m| := by
      have h4 : (((d m : ℤ) : ℝ) + α m) + (-α m) = ((d m : ℤ) : ℝ) := by ring
      have h5 : |((d m : ℤ) : ℝ)| ≤ |((d m : ℤ) : ℝ) + α m| + |α m| := by
        calc |((d m : ℤ) : ℝ)| = |(((d m : ℤ) : ℝ) + α m) + (-α m)| := by rw [h4]
          _ ≤ |((d m : ℤ) : ℝ) + α m| + |(-α m)| := abs_add_le _ _
          _ = |((d m : ℤ) : ℝ) + α m| + |α m| := by rw [abs_neg]
      linarith
    linarith
  -- the Euclidean norm dominates each coordinate
  have h3 : (1 / 2 : ℝ) ≤ ‖Work.BoseBoxFock.latVec d + α‖ := by
    refine le_trans hcoord ?_
    have h4 := PiLp.norm_apply_le (Work.BoseBoxFock.latVec d + α) m
    rwa [Real.norm_eq_abs] at h4
  -- reverse triangle inequality
  have h5 : ‖Work.BoseBoxFock.latVec d + α‖ - ‖β‖ ≤ ‖Work.BoseBoxFock.latVec d + α - β‖ := by
    have h6 : ‖Work.BoseBoxFock.latVec d + α‖
        ≤ ‖Work.BoseBoxFock.latVec d + α - β‖ + ‖β‖ := by
      have h7 := norm_add_le (Work.BoseBoxFock.latVec d + α - β) β
      have h8 : (Work.BoseBoxFock.latVec d + α - β) + β = Work.BoseBoxFock.latVec d + α := by
        abel
      rwa [h8] at h7
    linarith
  linarith

end Work.BoseBoxFock.PCFU
