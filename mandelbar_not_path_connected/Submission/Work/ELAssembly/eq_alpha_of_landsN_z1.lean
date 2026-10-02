import Mathlib
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- Landing at `z₁` for the dynamical Böttcher data of the root-parabolic parameter is
`1`-periodic in the angle: the ray of angle `θ` is the ray of angle `θ + k` (`k : ℤ`),
because `rayPt` depends on the angle only modulo `ℤ`
(`Submission/Work/ELTop/rayPt_add_int.lean`). -/
theorem landsN_z1_add_int_iff {c : ℂ} (d : Work.EL.RootParabolic c) (θ : ℝ) (m : ℤ) :
    Work.EL.LandsN d.hN (θ + (m : ℝ)) d.z₁ ↔ Work.EL.LandsN d.hN θ d.z₁ := by
  have hfuneq : (fun t : ℝ => Work.EL.rayPt d.hN (θ + (m : ℝ)) t)
      = fun t : ℝ => Work.EL.rayPt d.hN θ t :=
    funext fun t => Work.ELTop.rayPt_add_int d.hN θ t m
  rw [Work.EL.LandsN, Work.EL.LandsN, hfuneq]

/-- **Normalisation of an angle landing at `z₁`.**  If `hzero` says that, among the angles in
`[0, 1)`, exactly `alpha1` and `alpha2` land at the parabolic point `z₁`, then *every* angle
whose ray lands at `z₁` is congruent to `alpha1` or `alpha2` modulo `1`: reduce `θ` to its
fractional part, which lies in `[0, 1)` and has the same ray, and read off `hzero`. -/
theorem eq_alpha_of_landsN_z1 {c : ℂ} (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2))
    {θ : ℝ} (h : Work.EL.LandsN d.hN θ d.z₁) :
    ∃ m : ℤ, θ = Work.EL.alpha1 + m ∨ θ = Work.EL.alpha2 + m := by
  set m : ℤ := ⌊θ⌋ with hm
  have hθ : θ = Int.fract θ + (m : ℝ) := by
    rw [hm]
    exact (Int.fract_add_floor θ).symm
  have hfrac : Work.EL.LandsN d.hN (Int.fract θ) d.z₁ :=
    (landsN_z1_add_int_iff d (Int.fract θ) m).mp (by rw [← hθ]; exact h)
  have hmem : Int.fract θ ∈ Set.Ico 0 1 := ⟨Int.fract_nonneg θ, Int.fract_lt_one θ⟩
  rcases (hzero (Int.fract θ) hmem).mp hfrac with ha | ha
  · exact ⟨m, Or.inl (by rw [hθ, ha])⟩
  · exact ⟨m, Or.inr (by rw [hθ, ha])⟩

end Work.ELAssembly
