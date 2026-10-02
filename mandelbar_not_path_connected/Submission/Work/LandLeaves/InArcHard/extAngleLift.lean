/-
# The external angle is continuous at an interior ray point, with a lift

`Work.LandLeaves.InArcHard.extAngle_close_at_gen_lift`: at an interior point `rayPt hN e t₀`
(`t₀ > 1`) of the dynamic ray of *any* angle `e : ℝ`, a nearby point `z ∉ K c` has an external
angle which, for a suitable integer lift `m`, is close to `e`:

`∃ m : ℤ, |extAngle (dynPhi c φ) z + m - e| < η`.

The existing `Work.LandLeaves.extAngle_close_at_gen` (and its ancestors) require `e ∈ (0,1)`,
because `extAngle` takes its values in `[0,1)`; the lift removes that restriction, which is what
allows the local "side transfer" statements at ray points to be applied without normalising the
angle of the ray into `(0,1)` (in particular at a ray of *integer* angle, where no such
normalisation exists).

The proof is the one of `Work.Top.extAngle_close_of_Phi_close`: write `w = Φ z / rayPoint e t₀`;
then `‖w - 1‖` is small, `|arg w|` is small, and `arg (Φ z) - arg w - 2π e ∈ 2πℤ`; reducing
modulo `1` gives `extAngle (Φ z) = fract (e + arg w / (2π))`, whence the lift
`m = ⌊e + arg w / (2π)⌋`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.Top.extAngle_close_of_Phi_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.LandLeaves.InArcHard

/-- The Böttcher coordinate of the dynamical plane is continuous off the filled Julia set. -/
theorem continuousOn_dynPhi_of_dynB {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) :
    ContinuousOn (Work.EL.dynPhi c φ) (Work.EL.K c)ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Set.domRestrict (Work.EL.K c)ᶜ (Work.EL.dynPhi c φ)
      = fun z => ((hN.e z : Work.Top.exteriorDisc) : ℂ) := by
    funext z
    exact hN.he z
  rw [h]
  exact continuous_subtype_val.comp hN.e.continuous

/-- **Local continuity of the external angle at a ray point, with a lift.**  For every angle
`e : ℝ` and every `η > 0` there is `δ > 0` such that every `z` within `δ` of the level-`t₀`
point of the ray of angle `e` (`t₀ > 1`) is off the filled Julia set and has an external angle
which, up to an integral lift, is within `η` of `e`. -/
theorem extAngle_close_at_gen_lift {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {e η : ℝ} (hη : 0 < η) {t₀ : ℝ} (ht₀ : 1 < t₀) :
    ∃ δ > 0, ∀ z : ℂ, ‖z - Work.EL.rayPt hN e t₀‖ < δ →
      z ∉ Work.EL.K c ∧
      ∃ m : ℤ, |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z + (m : ℝ) - e| < η := by
  have hRpos : 0 < t₀ := lt_trans zero_lt_one ht₀
  set ε : ℝ := η / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεη : ε < η := by rw [hεdef]; linarith
  -- `arg` is continuous at `1`, where it vanishes
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ w : ℂ, ‖w - 1‖ < δ₁ → |Complex.arg w| < 2 * Real.pi * ε := by
    have h2πε : (0 : ℝ) < 2 * Real.pi * ε :=
      mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hεpos
    have hmem : Complex.arg (1 : ℂ) ∈ Set.Ioo (-(2 * Real.pi * ε)) (2 * Real.pi * ε) := by
      simp only [Complex.arg_one]
      exact ⟨by linarith, h2πε⟩
    have h1slit : (1 : ℂ) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_one, Complex.ofReal_mem_slitPlane]
      norm_num
    have hev : ∀ᶠ w in 𝓝 (1 : ℂ), |Complex.arg w| < 2 * Real.pi * ε := by
      have h1 := (Complex.continuousAt_arg h1slit).preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
      filter_upwards [h1] with w hw using abs_lt.mpr hw
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev
    exact ⟨δ₁, hδ₁pos, fun w hw => hδ₁ (by simpa [dist_eq_norm] using hw)⟩
  -- the reference point
  have hpK : Work.EL.rayPt hN e t₀ ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN ht₀
  have hpPhi : Work.EL.dynPhi c φ (Work.EL.rayPt hN e t₀) = Work.Top.NakaneData.rayPoint e t₀ :=
    Work.Top.NakaneData.Phi_rayPt hN ht₀
  have hpnorm : ‖Work.Top.NakaneData.rayPoint e t₀‖ = t₀ := by
    rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos hRpos]
  have hcont : ContinuousAt (Work.EL.dynPhi c φ) (Work.EL.rayPt hN e t₀) :=
    (continuousOn_dynPhi_of_dynB hN).continuousAt
      (hN.isClosed_mb.isOpen_compl.mem_nhds hpK)
  have hminpos : 0 < min (t₀ * δ₁) t₀ := lt_min (by positivity) hRpos
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (min (t₀ * δ₁) t₀) hminpos
  refine ⟨δ, hδpos, fun z hz => ?_⟩
  have hd : dist (Work.EL.dynPhi c φ z) (Work.EL.dynPhi c φ (Work.EL.rayPt hN e t₀))
      < min (t₀ * δ₁) t₀ := hδ (by rwa [dist_eq_norm])
  rw [dist_eq_norm, hpPhi] at hd
  have hzK : z ∉ Work.EL.K c := by
    intro hzK
    have h0 : Work.EL.dynPhi c φ z = 0 := hN.Phi_eq_zero_of_mem z hzK
    rw [h0, zero_sub, norm_neg, hpnorm] at hd
    exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (lt_irrefl t₀)
  refine ⟨hzK, ?_⟩
  have hz_ne : Work.EL.dynPhi c φ z ≠ 0 := hN.Phi_ne_zero hzK
  have hz₀_ne : Work.Top.NakaneData.rayPoint e t₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpnorm
    linarith
  -- the normalised Böttcher coordinate of `z`
  set w : ℂ := Work.EL.dynPhi c φ z / Work.Top.NakaneData.rayPoint e t₀ with hwdef
  have hw1 : w - 1 = (Work.EL.dynPhi c φ z - Work.Top.NakaneData.rayPoint e t₀)
      / Work.Top.NakaneData.rayPoint e t₀ := by
    rw [hwdef, sub_div, div_self hz₀_ne]
  have hwdist : ‖w - 1‖ < δ₁ := by
    rw [hw1, norm_div, hpnorm, div_lt_iff₀ hRpos]
    have := lt_of_lt_of_le hd (min_le_left (t₀ * δ₁) t₀)
    calc ‖(Work.EL.dynPhi c φ z - Work.Top.NakaneData.rayPoint e t₀)‖
        < t₀ * δ₁ := this
      _ = δ₁ * t₀ := by ring
  have hargw : |Complex.arg w| < 2 * Real.pi * ε := hδ₁ w hwdist
  have hargw2 : |Complex.arg w / (2 * Real.pi)| < ε := by
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [abs_div, abs_of_pos h2π, div_lt_iff₀ h2π]
    linarith [hargw]
  -- the congruence of the arguments modulo `2π`
  obtain ⟨n, hn⟩ := Work.Top.NakaneData.exists_int_arg_sub_arg_div
    (z := Work.EL.dynPhi c φ z) (z₀ := Work.Top.NakaneData.rayPoint e t₀)
    hz_ne hz₀_ne (θ := 2 * Real.pi * e) (Work.Top.NakaneData.arg_rayPoint_coe_angle hRpos)
  rw [← hwdef] at hn
  set δ' : ℝ := Complex.arg w / (2 * Real.pi) with hδ'def
  have hδ'abs : |δ'| < ε := by rw [hδ'def]; exact hargw2
  -- the external angle of `z` is `fract (e + δ')`
  have harg_eq : Complex.arg (Work.EL.dynPhi c φ z)
      = 2 * Real.pi * e + 2 * Real.pi * δ' + 2 * Real.pi * (n : ℝ) := by
    have h2 : Complex.arg w = 2 * Real.pi * δ' := by rw [hδ'def]; field_simp
    linarith [hn, h2]
  have hρ : Complex.arg (Work.EL.dynPhi c φ z) / (2 * Real.pi) = e + δ' + (n : ℝ) := by
    rw [harg_eq]
    field_simp
  have hExt : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z = Int.fract (e + δ') := by
    rw [Work.Top.NakaneData.extAngle, toIcoMod_eq_iff]
    refine ⟨⟨Int.fract_nonneg _, ?_⟩, ?_⟩
    · linarith [Int.fract_lt_one (e + δ')]
    refine ⟨n + ⌊e + δ'⌋, ?_⟩
    rw [zsmul_eq_mul, mul_one, hρ]
    have hself : (⌊e + δ'⌋ : ℝ) = e + δ' - Int.fract (e + δ') := by
      have h := Int.self_sub_fract (e + δ'); linarith
    push_cast
    linarith
  refine ⟨⌊e + δ'⌋, ?_⟩
  rw [hExt]
  have hcancel : Int.fract (e + δ') + (⌊e + δ'⌋ : ℝ) - e = δ' := by
    have h := Int.fract_add_floor (e + δ')
    linarith
  rw [hcancel]
  exact lt_of_lt_of_le hδ'abs (le_of_lt hεη)

end Work.LandLeaves.InArcHard
