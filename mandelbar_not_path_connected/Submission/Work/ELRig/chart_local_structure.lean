import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.chart_sphere_crossings

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-- **The local structure of the straightening chart at a far-left point.**  Let `p = γ₁ s₀` with
`Re p < -L.R`, and let `δ > 0` be a level such that the horizontal line through `p` meets the two
lifts only at `p` on `(0, δ)`.  Then there is a radius `r > 0`, `r < δ`, so small that the closed
ball of radius `r` around `p` lies in `{Re < -L.R}` and its `Ψ`-image misses `K c`, such that on
that ball the zero set of the imaginary part of the chart `sideFlipChart c d fl L s₀` is exactly
the piece of the lift `γ₁` inside the ball; moreover the points of that piece are exactly the
`γ₁ s` with `s` in the interval between the two "first exit" parameters `sL < s₀ < sR` from the
circle of radius `r`, and along that piece the imaginary part differs from `Im p` except at `p`. -/
theorem chart_local_structure {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) {δ : ℝ} (hδ : 0 < δ)
    (hsimple : ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    ∃ r > 0, r < δ ∧ r < -((L.γ₁ s₀).re) - L.R ∧
      (∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ r → fl.Ψ w ∉ Work.EL.K c) ∧
      ∃ sL sR : ℝ, sL < s₀ ∧ s₀ < sR ∧
        (∀ s ∈ Set.Ioo sL sR, ‖L.γ₁ s - L.γ₁ s₀‖ < r) ∧
        ‖L.γ₁ sL - L.γ₁ s₀‖ = r ∧ ‖L.γ₁ sR - L.γ₁ s₀‖ = r ∧
        (∀ s ∈ Set.Icc sL sR, L.γ₁ s ≠ L.γ₁ s₀ → (L.γ₁ s).im ≠ (L.γ₁ s₀).im) ∧
        (∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ r →
          ((Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0 ↔
            ∃ s ∈ Set.Icc sL sR, L.γ₁ s = w)) := by
  classical
  -- ## The three local inputs proved in `chart_sphere_crossings`
  -- the zero set of the chart near `p` is exactly the lift
  obtain ⟨εU, hεUpos, hU⟩ :=
    exists_chart_zero_neighbourhood (c := c) (d := d) (fl := fl) (L := L) hre
  -- the two first-exit parameters on each side, for every radius in a range
  obtain ⟨δ', hδ'pos, r_loc, hr_loc_pos, hloc⟩ :=
    local_exit_crossings (c := c) (d := d) (fl := fl) (L := L) hre
  -- the curve cannot come back to a small ball far away in parameter
  obtain ⟨εno, hεno_pos, hno⟩ :=
    exists_no_crossing_radius (γ := L.γ₁) L.cont₁ (rayCylLift_injective L)
      (rayCylLift_norm_growth L) rfl hδ'pos
  -- ## `Ψ` misses `K c` on a neighbourhood of `p`
  have hqK : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]
    exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  obtain ⟨εK, hεKpos, hεK⟩ :
      ∃ ε > 0, ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ε → fl.Ψ w ∉ Work.EL.K c := by
    obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := Metric.isOpen_iff.mp
      (Work.ParamRays.isClosed_filledJulia c).isOpen_compl (fl.Ψ (L.γ₁ s₀)) hqK
    obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := Metric.continuousAt_iff.mp
      fl.Ψ_diff.continuous.continuousAt ρ₁ hρ₁pos
    refine ⟨min ρ₁ ρ₂ / 2, by linarith [lt_min hρ₁pos hρ₂pos], fun w hw => ?_⟩
    have hlt : dist w (L.γ₁ s₀) < ρ₂ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hw (lt_of_lt_of_le (half_lt_self (lt_min hρ₁pos hρ₂pos))
        (min_le_right ρ₁ ρ₂))
    exact hρ₁ (Metric.mem_ball.mpr (hρ₂ hlt))
  -- ## The radius
  have hRpos : 0 < -((L.γ₁ s₀).re) - L.R := by linarith [hre]
  set M : ℝ := min δ (min (-((L.γ₁ s₀).re) - L.R)
    (min εU (min εno (min r_loc εK)))) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hδ (lt_min hRpos (lt_min hεUpos (lt_min hεno_pos (lt_min hr_loc_pos hεKpos))))
  have hMδ : M ≤ δ := by rw [hM]; exact min_le_left _ _
  have hMR : M ≤ -((L.γ₁ s₀).re) - L.R := by
    rw [hM]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hMU : M ≤ εU := by
    rw [hM]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMno : M ≤ εno := by
    rw [hM]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hMloc : M ≤ r_loc := by
    rw [hM]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hMK : M ≤ εK := by
    rw [hM]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  set r : ℝ := M / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrδ : r < δ := by rw [hr]; linarith
  have hrR : r < -((L.γ₁ s₀).re) - L.R := by rw [hr]; linarith
  have hrU : r < εU := by rw [hr]; linarith
  have hrno : r < εno := by rw [hr]; linarith
  have hrloc : r < r_loc := by rw [hr]; linarith
  have hrK : r < εK := by rw [hr]; linarith
  -- ## The two first-exit parameters for this radius
  obtain ⟨⟨sL, ⟨hsLmem, hsLval⟩, hsLuniq⟩, ⟨sR, ⟨hsRmem, hsRval⟩, hsRuniq⟩⟩ :=
    hloc r ⟨hrpos, hrloc⟩
  have hsLs₀ : sL < s₀ := hsLmem.2
  have hs₀sR : s₀ < sR := hsRmem.1
  -- ## The only parameters of the curve on the circle are `sL` and `sR`
  have hsphere : ∀ t : ℝ, ‖L.γ₁ t - L.γ₁ s₀‖ = r → t = sL ∨ t = sR := by
    intro t ht
    have hmem : t ∈ Set.Ioo (s₀ - δ') (s₀ + δ') := hno t (by rw [ht]; exact hrno)
    rcases lt_trichotomy t s₀ with h | h | h
    · exact Or.inl (hsLuniq t ⟨⟨hmem.1, h⟩, ht⟩)
    · exfalso
      rw [h] at ht
      simp only [sub_self, norm_zero] at ht
      linarith
    · exact Or.inr (hsRuniq t ⟨⟨h, hmem.2⟩, ht⟩)
  -- ## The values at the ends of the window are large
  have hgc : Continuous fun u : ℝ => ‖L.γ₁ u - L.γ₁ s₀‖ :=
    (L.cont₁.sub continuous_const).norm
  have hbndR : εno ≤ ‖L.γ₁ (s₀ + δ') - L.γ₁ s₀‖ := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hno (s₀ + δ') hcon).2 (lt_irrefl _)
  have hbndL : εno ≤ ‖L.γ₁ (s₀ - δ') - L.γ₁ s₀‖ := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hno (s₀ - δ') hcon).1 (lt_irrefl _)
  -- ## Parameters of the curve inside the open ball lie strictly between `sL` and `sR`
  have hlimg : ∀ t : ℝ, ‖L.γ₁ t - L.γ₁ s₀‖ < r → t ∈ Set.Ioo sL sR := by
    intro t ht
    have htw : t ∈ Set.Ioo (s₀ - δ') (s₀ + δ') := hno t (lt_trans ht hrno)
    have hgR : r < ‖L.γ₁ (s₀ + δ') - L.γ₁ s₀‖ := lt_of_lt_of_le hrno hbndR
    have hgL : r < ‖L.γ₁ (s₀ - δ') - L.γ₁ s₀‖ := lt_of_lt_of_le hrno hbndL
    have h1 : sL < t := by
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hlt | heq
      · have hmem : r ∈ Set.Icc (‖L.γ₁ t - L.γ₁ s₀‖)
            (‖L.γ₁ (s₀ - δ') - L.γ₁ s₀‖) := ⟨le_of_lt ht, le_of_lt hgL⟩
        obtain ⟨cc, hcmem, hceq⟩ :=
          intermediate_value_Icc' (le_of_lt htw.1) hgc.continuousOn hmem
        change ‖L.γ₁ cc - L.γ₁ s₀‖ = r at hceq
        have hc1 : s₀ - δ' < cc := lt_of_le_of_ne hcmem.1 (fun h => by
          rw [← h] at hceq; linarith [hgL])
        have hc2 : cc < t := lt_of_le_of_ne hcmem.2 (fun h => by
          rw [h] at hceq; linarith)
        rcases hsphere cc hceq with h | h
        · rw [h] at hc2; linarith [hcon]
        · rw [h] at hc2; linarith [hcon, hsLs₀, hs₀sR]
      · rw [heq, hsLval] at ht
        exact absurd ht (lt_irrefl r)
    refine ⟨h1, ?_⟩
    by_contra hcon
    push_neg at hcon
    have hmem : r ∈ Set.Icc (‖L.γ₁ t - L.γ₁ s₀‖)
        (‖L.γ₁ (s₀ + δ') - L.γ₁ s₀‖) := ⟨le_of_lt ht, le_of_lt hgR⟩
    obtain ⟨cc, hcmem, hceq⟩ :=
      intermediate_value_Icc (le_of_lt htw.2) hgc.continuousOn hmem
    change ‖L.γ₁ cc - L.γ₁ s₀‖ = r at hceq
    have hc1 : t < cc := lt_of_le_of_ne hcmem.1 (fun h => by rw [← h] at hceq; linarith)
    have hc2 : cc < s₀ + δ' := lt_of_le_of_ne hcmem.2 (fun h => by
      rw [h] at hceq; linarith)
    rcases hsphere cc hceq with h | h
    · rw [h] at hc1; linarith [h1]
    · rw [h] at hc1; linarith [hcon]
  -- ## ... and the curve stays strictly inside the ball between `sL` and `sR`
  have hIoo : ∀ t : ℝ, t ∈ Set.Ioo sL sR → ‖L.γ₁ t - L.γ₁ s₀‖ < r := by
    intro t ht
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · rcases lt_trichotomy t s₀ with hts | hts | hts
      · have hmem : r ∈ Set.Icc (‖L.γ₁ s₀ - L.γ₁ s₀‖) (‖L.γ₁ t - L.γ₁ s₀‖) :=
          ⟨by simp only [sub_self, norm_zero]; exact hrpos.le, le_of_lt hlt⟩
        obtain ⟨cc, hcmem, hceq⟩ :=
          intermediate_value_Icc' (le_of_lt hts) hgc.continuousOn hmem
        change ‖L.γ₁ cc - L.γ₁ s₀‖ = r at hceq
        have hc1 : t < cc := lt_of_le_of_ne hcmem.1 (fun h => by rw [← h] at hceq; linarith)
        have hc2 : cc < s₀ := lt_of_le_of_ne hcmem.2 (fun h => by
          rw [h] at hceq; simp only [sub_self, norm_zero] at hceq; linarith)
        rcases hsphere cc hceq with h | h
        · rw [h] at hc1; linarith [ht.1]
        · rw [h] at hc2; linarith [hs₀sR]
      · rw [hts] at hlt
        simp only [sub_self, norm_zero] at hlt
        linarith
      · have hmem : r ∈ Set.Icc (‖L.γ₁ s₀ - L.γ₁ s₀‖) (‖L.γ₁ t - L.γ₁ s₀‖) :=
          ⟨by simp only [sub_self, norm_zero]; exact hrpos.le, le_of_lt hlt⟩
        obtain ⟨cc, hcmem, hceq⟩ :=
          intermediate_value_Icc (le_of_lt hts) hgc.continuousOn hmem
        change ‖L.γ₁ cc - L.γ₁ s₀‖ = r at hceq
        have hc1 : s₀ < cc := lt_of_le_of_ne hcmem.1 (fun h => by
          rw [← h] at hceq; simp only [sub_self, norm_zero] at hceq; linarith)
        have hc2 : cc < t := lt_of_le_of_ne hcmem.2 (fun h => by rw [h] at hceq; linarith)
        rcases hsphere cc hceq with h | h
        · rw [h] at hc1; linarith [hsLs₀]
        · rw [h] at hc2; linarith [ht.2]
    · rcases hsphere t heq.symm with h | h
      · exact absurd h (ne_of_gt ht.1)
      · exact absurd h (ne_of_lt ht.2)
  -- ## converse: the curve is inside the ball at the parameters of `[sL,sR]`
  have hIcc : ∀ t : ℝ, t ∈ Set.Icc sL sR → ‖L.γ₁ t - L.γ₁ s₀‖ ≤ r := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact le_of_eq hsLval
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; exact le_of_eq hsRval
    · exact le_of_lt (hIoo t ⟨h, h'⟩)
  -- ## a point of the curve in the closed ball has its parameter in `[sL,sR]`
  have hIcc' : ∀ t : ℝ, ‖L.γ₁ t - L.γ₁ s₀‖ ≤ r → t ∈ Set.Icc sL sR := by
    intro t ht
    rcases lt_or_eq_of_le ht with hlt | heq
    · exact ⟨le_of_lt (hlimg t hlt).1, le_of_lt (hlimg t hlt).2⟩
    · rcases hsphere t heq with h | h
      · rw [h]; exact ⟨le_rfl, le_of_lt (lt_trans hsLs₀ hs₀sR)⟩
      · rw [h]; exact ⟨le_of_lt (lt_trans hsLs₀ hs₀sR), le_rfl⟩
  -- ## Assembly
  refine ⟨r, hrpos, hrδ, hrR, fun w hw => hεK w (le_of_lt (lt_of_le_of_lt hw hrK)),
    sL, sR, hsLs₀, hs₀sR, hIoo, hsLval, hsRval, ?_, ?_⟩
  · -- the imaginary part on the piece differs from `Im p` except at `p`
    intro t ht hne him
    have hle : ‖L.γ₁ t - L.γ₁ s₀‖ ≤ r := hIcc t ht
    set u : ℝ := (L.γ₁ t - L.γ₁ s₀).re with hu
    have hreal : L.γ₁ t - L.γ₁ s₀ = ((u : ℝ) : ℂ) := by
      refine Complex.ext rfl ?_
      rw [Complex.ofReal_im]
      simpa [hu] using sub_eq_zero.mpr him
    have hnorm : |u| = ‖L.γ₁ t - L.γ₁ s₀‖ := by
      have h := congrArg norm hreal
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      exact h.symm
    have hud : |u| < δ := lt_of_le_of_lt (le_of_eq hnorm) (lt_of_le_of_lt hle hrδ)
    have hune : u ≠ 0 := by
      intro h0
      apply hne
      have hzero : L.γ₁ t - L.γ₁ s₀ = 0 := by rw [hreal, h0]; simp
      exact sub_eq_zero.mp hzero
    have hγt : L.γ₁ t = L.γ₁ s₀ + (u : ℂ) := by
      rw [← hreal]; ring
    rcases lt_or_gt_of_ne hune with huneg | hupos
    · have hueq : (u : ℂ) = -((|u| : ℝ) : ℂ) := by
        rw [abs_of_neg huneg]; push_cast; ring
      refine (hsimple |u| ⟨abs_pos.mpr hune, hud⟩).2 (Or.inl ⟨t, ?_⟩)
      rw [hγt, hueq]; ring
    · have hueq : (u : ℂ) = ((|u| : ℝ) : ℂ) := by
        rw [abs_of_pos hupos]
      refine (hsimple u ⟨hupos, lt_of_le_of_lt (le_abs_self u) hud⟩).1 (Or.inl ⟨t, ?_⟩)
      rw [hγt, hueq]
  · -- the zero set of the chart on the closed ball
    intro w hw
    constructor
    · intro him
      have hwU : ‖w - L.γ₁ s₀‖ < εU := lt_of_le_of_lt hw hrU
      obtain ⟨t, ht⟩ := (hU w hwU).mp him
      exact ⟨t, hIcc' t (by rw [ht]; exact hw), ht⟩
    · rintro ⟨t, ht, htw⟩
      rw [← htw, sideFlipChart_eq_ofReal]
      exact Complex.ofReal_im _

end Work.ELRig
