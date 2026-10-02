import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.rayPt_g
import Submission.Work.GATE2.T5_window
import Submission.Work.ELNest.bAng_nest_arc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

open LeanEval.ComplexAnalysis (Tantibar)

/-- The shift bound: `32 (bAng' (n+1) - α₂) < α₁ - bAng n`. -/
private lemma window_shift_bound (n : ℕ) :
    32 * (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2)
      < Work.EL.alpha1 - Work.ELNest.bAng n := by
  have hα2 : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl
  have hα1 : Work.EL.alpha1 = Work.ELNest.alpha1 := rfl
  rw [hα1, hα2]
  have hnum : (Work.ELNest.beta0' - Work.ELNest.alpha2) / 32
      < Work.ELNest.alpha1 - Work.ELNest.beta0 := by
    norm_num [Work.ELNest.beta0', Work.ELNest.alpha2, Work.ELNest.alpha1, Work.ELNest.beta0]
  have hp : (0:ℝ) < (1024:ℝ)^n := by positivity
  have e : 32 * (Work.ELNest.alpha2
      + (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024:ℝ)^(n+1) - Work.ELNest.alpha2)
      = ((Work.ELNest.beta0' - Work.ELNest.alpha2) / 32) / (1024:ℝ)^n := by
    rw [pow_succ]
    field_simp
    ring
  have e2 : Work.ELNest.alpha1
      - (Work.ELNest.alpha1 - (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024:ℝ)^n)
      = (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024:ℝ)^n := by ring
  rw [Work.ELNest.bAng', Work.ELNest.bAng, e, e2]
  exact div_lt_div_of_pos_right hnum hp

/-- **The `α₁`-window angle of a deep nest point, up to the half-integer shift.**

Let `z = fl.Ψ x` be a point of the `Ψ`-plane off `K c` lying in the near sides of the `α`-pair
`nest.P0` and of the level-`n+1` pair `nest.Q (n+1)`.  Then either `z` itself is a ray point of an
angle in the `α₁`-window `(bAng n, α₁)`, or its half-integer shift `fl.Ψ (x + 1/2) = g z` is.

The first case is the `α₁`-branch of `Work.GATE.Nest.ray_angle_of_near_sides`
(`ϑ ∈ [bAng (n+1), α₁] ∪ [α₂, bAng' (n+1)]`); in the second the angle `ϑ` lies in the
`α₂`-window `(α₂, bAng' (n+1)]`, and the antiholomorphic square root
`g = (T_c)^[5]` (`ParabolicFlower.Ψ_anti`) carries it to `T^[5] ϑ = α₁ - 32 (ϑ - α₂)`
(`Work.GATE2.T5_window`), which lies in `(bAng n, α₁)` because
`32 (bAng' (n+1) - α₂) = 32·417/(1024^{n+1}·1047552) < 45/(1024^n·1047552) = α₁ - bAng n`. -/
theorem exists_alpha1_angle_or_shift {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (n : ℕ) {x : ℝ}
    (hxK : fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c)
    (hxP : fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (hxQ : fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear (nest.Q (n + 1))) :
    (∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
        ∃ t : ℝ, 1 < t ∧ fl.Ψ ((x : ℝ) : ℂ) = Work.EL.rayPt d.hN θ t) ∨
      (∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
        ∃ t : ℝ, 1 < t ∧ fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) = Work.EL.rayPt d.hN θ t) := by
  have hα1 : Work.EL.alpha1 = Work.ELNest.alpha1 := rfl
  have hα2 : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl
  have hβ₁ : Work.ELNest.bAng (n + 1) < Work.EL.alpha1 := by
    rw [hα1]; exact (Work.ELNest.bAng_range (n + 1)).1.2
  have h₂β' : Work.EL.alpha2 < Work.ELNest.bAng' (n + 1) := by
    rw [hα2]; exact (Work.ELNest.bAng_range (n + 1)).2.1
  have h₁₂ : Work.EL.alpha1 < Work.EL.alpha2 := by
    rw [hα1, hα2]; exact Work.ELNest.alpha1_lt_alpha2
  obtain ⟨ϑ, hϑparam, hϑcase⟩ :=
    Work.GATE.Nest.ray_angle_of_near_sides (hN := d.hN) (P0 := nest.P0) (Q := nest.Q (n + 1))
      (β := Work.ELNest.bAng (n + 1)) (β' := Work.ELNest.bAng' (n + 1))
      nest.P0_spec.1 nest.P0_spec.2.1 (hQa (n + 1)) (hQb (n + 1))
      (Work.ELNest.bAng_pos (n + 1)) hβ₁ h₁₂ h₂β' (Work.ELNest.bAng'_lt_one (n + 1))
      nest.sides_P0 (nest.sides_Q (n + 1))
      (fun w hw => Work.GATE.Nest.mem_paramRay_of_notMem_K d.hN hw)
      hxK hxP hxQ
  -- the ray representation of the point
  have hϑparam' := hϑparam
  obtain ⟨hzK', t, ht, hΦ⟩ := hϑparam
  have hzt : fl.Ψ ((x : ℝ) : ℂ) = Work.EL.rayPt d.hN ϑ t :=
    Work.Top.NakaneData.injOn_Phi d.hN hzK' (Work.Top.NakaneData.rayPt_notMem d.hN ht)
      (by rw [Work.Top.NakaneData.Phi_rayPt d.hN ht]; exact hΦ)
  -- the point is off the α-pair curve, so `ϑ` is neither root angle
  have hznotcurve : fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.pairCurve nest.P0 := by
    have h : fl.Ψ ((x : ℝ) : ℂ) ∈ (Work.EL.pairCurve nest.P0)ᶜ := by
      rw [← nest.sides_P0.union_eq]; exact Or.inr hxP
    exact h
  have hϑ_ne_α1 : ϑ ≠ Work.EL.alpha1 := by
    intro h
    apply hznotcurve
    refine (Work.EL.mem_pairCurve_iff nest.P0 _).mpr (Or.inl ?_)
    rw [nest.P0_spec.1, ← h]; exact hϑparam'
  have hϑ_ne_α2 : ϑ ≠ Work.EL.alpha2 := by
    intro h
    apply hznotcurve
    refine (Work.EL.mem_pairCurve_iff nest.P0 _).mpr (Or.inr (Or.inr ?_))
    rw [nest.P0_spec.2.1, ← h]; exact hϑparam'
  rcases hϑcase with ⟨hlo1, hhi1⟩ | ⟨hlo2, hhi2⟩
  · -- the `α₁`-branch: `ϑ` itself works
    exact Or.inl ⟨ϑ, ⟨lt_of_lt_of_le (Work.ELNest.bAng_mono n) hlo1,
      lt_of_le_of_ne hhi1 hϑ_ne_α1⟩, t, ht, hzt⟩
  · -- the `α₂`-branch: the half shift lands in the `α₁`-window
    have hϑ_gt : Work.EL.alpha2 < ϑ := lt_of_le_of_ne hlo2 (Ne.symm hϑ_ne_α2)
    have hϑ_le : ϑ ≤ Work.ELNest.beta0' :=
      le_trans hhi2 (Work.ELNest.bAng'_le_beta0' (n + 1))
    have hT5 : (Work.EL.T^[5]) ϑ = Work.EL.alpha1 - 32 * (ϑ - Work.EL.alpha2) :=
      Work.GATE2.T5_window hϑ_gt hϑ_le
    have hwin : (Work.EL.T^[5]) ϑ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1 := by
      rw [hT5]
      refine ⟨?_, ?_⟩
      · have hb := window_shift_bound n
        have hmono : 32 * (ϑ - Work.EL.alpha2)
            ≤ 32 * (Work.ELNest.bAng' (n + 1) - Work.EL.alpha2) :=
          mul_le_mul_of_nonneg_left (by linarith [hhi2]) (by norm_num)
        linarith
      · linarith
    refine Or.inr ⟨(Work.EL.T^[5]) ϑ, hwin, t ^ (32 : ℕ), one_lt_pow₀ ht (by norm_num), ?_⟩
    have hanti : fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) =
        (Tantibar c)^[5] (fl.Ψ ((x : ℝ) : ℂ)) := by
      have h := fl.Ψ_anti ((x : ℝ) : ℂ)
      have hstar : star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by simp
      rw [hstar] at h
      have h1 : ((x + 1 / 2 : ℝ) : ℂ) = ((x : ℝ) : ℂ) + 1 / 2 := by push_cast; ring
      rw [h1]; simpa using h
    rw [hanti, hzt, Work.GATE2.rayPt_g d ht]

end Work.GATE2
