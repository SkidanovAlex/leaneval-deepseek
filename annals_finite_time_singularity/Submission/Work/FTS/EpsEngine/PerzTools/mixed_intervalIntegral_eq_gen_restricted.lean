import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Pointwise

namespace Work.FTS.EpsEngine.PerzTools

/-! ## Restricted-measurability variants of the two inductions

`Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen` assumes the a.e.-strong-measurability
of *every* slot `mixed k l` in the parameter `s`.  Its two internal inductions, however, only
ever evaluate that hypothesis at slots of order `k + l ≤ n` (the angular one at `(0, l)` and
`(0, l+1)`, the radial one at `(k, l)` and `(k+1, l)`).  The two lemmas below record exactly
that: they are the same statements with the measurability hypothesis restricted to the slots
of order `≤ n`, and their proofs are the inductions of
`Submission/Work/FTS/StrongEps/E5G5/DthIter_intervalIntegral_eq_gen.lean` and
`Submission/Work/FTS/StrongEps/E5G5/DzIter_intervalIntegral_eq_gen.lean`, verbatim. -/

/-- **The angular exchange for an arbitrary order `l ≤ n`, with restricted measurability.** -/
theorem DthIter_intervalIntegral_eq_gen_restricted {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    {n l : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (hl : l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction l with
  | zero => intro z θ _; rfl
  | succ l ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hzcl : z ∈ Set.Icc z₁ z₂ := ⟨le_of_lt hzz.1, le_of_lt hzz.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set θlo : ℝ := max θ₁ (θ / 2) with hθlo
    set θhi : ℝ := min θ₂ ((θ + Real.pi / 2) / 2) with hθhi
    have hθlo_lt : θlo < θ := by
      rw [hθlo]; exact max_lt hθθ.1 (by linarith)
    have hθ_lt_θhi : θ < θhi := by
      rw [hθhi]; exact lt_min hθθ.2 (by linarith)
    have hθlo0 : 0 < θlo := lt_of_lt_of_le (by linarith : (0:ℝ) < θ / 2) (le_max_right _ _)
    have hθhi_lt : θhi < Real.pi / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨smin, hsmin_pos, hsmin_le⟩ := Work.FTS.StrongEps.exists_pos_min_sin_two hθlo0 hθhi_lt
    have hmem_box : ∀ y ∈ Set.Ioo θlo θhi,
        (z, y) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro y hy
      exact ⟨hzcl, ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy.1),
        le_of_lt (lt_of_lt_of_le hy.2 (min_le_left _ _))⟩⟩
    have hyQ : ∀ y ∈ Set.Ioo θlo θhi, (z, y) ∈ Work.FTS.EllipticEst.Q0 :=
      fun y hy => hboxQ (hmem_box y hy)
    have hyf : ∀ y ∈ Set.Ioo θlo θhi, 0 < y ∧ y < Real.pi / 2 := by
      intro y hy
      obtain ⟨-, hy1, hy2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hyQ y hy)
      exact ⟨hy1, hy2⟩
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t y => Work.Spaces.DthIter l (H t) z y)
      (G' := fun t y => Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y))
      (bound := fun _ => C / smin) hθlo_lt hθ_lt_θhi ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro y hy
      have := (hmeas 0 l (by omega) z y (hyQ y hy)).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed_zero_left] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas 0 l (by omega) z θ hzQ).mono_measure
          (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed_zero_left] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        have := hbdd t htT 0 l (by omega) (z, θ)
          ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
        simpa only [Work.Spaces.mixed_zero_left] using this
    · have h1 := (hmeas 0 (l + 1) (by omega) z θ hzQ).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const (Real.sin (2 * θ))⁻¹
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hsinpos : 0 < Real.sin (2 * y) :=
        lt_of_lt_of_le hsmin_pos (hsmin_le y (Set.Ioo_subset_Icc_self hy))
      have hb := hbdd t htT 0 (l + 1) (by omega) (z, y) (hmem_box y hy)
      calc |Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y)|
          = |Work.Spaces.mixed 0 (l + 1) (H t) z y| / Real.sin (2 * y) := by
            rw [abs_div, abs_of_pos hsinpos]
        _ ≤ C / Real.sin (2 * y) := div_le_div_of_nonneg_right hb (le_of_lt hsinpos)
        _ ≤ C / smin := div_le_div_of_nonneg_left hC hsmin_pos
            (hsmin_le y (Set.Ioo_subset_Icc_self hy))
    · exact intervalIntegrable_const
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder := Work.FTS.StrongEps.SmoothOpen.hasDerivAt_slice_th
        (Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0
          (hsm t htT) l) hz0 (hyf y hy)
      have hid : Work.Spaces.pth (Work.Spaces.DthIter l (H t)) z y
          = Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y) := by
        simpa only [Work.Spaces.mixed_zero_left] using
          Work.FTS.StrongEps.LocUnif.pth_mixed_div 0 l (hsm t htT) z y (hyQ y hy)
      exact hder.congr_deriv hid
    have hev : (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y)
        =ᶠ[𝓝 θ] (fun y => ∫ s in a..b, Work.Spaces.DthIter l (H s) z y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθθ] with y hy
      exact ih (by omega) z y ⟨hzz, hy⟩
    have hpth : Work.Spaces.pth (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ) := by
      show deriv (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) θ = _
      rw [hev.deriv_eq, hcore.deriv]
    have hsinne : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    calc Work.Spaces.DthIter (l + 1) (fun z θ => ∫ s in a..b, H s z θ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth
            (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ := by
          rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      _ = Real.sin (2 * θ) * (∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ)) := by rw [hpth]
      _ = Real.sin (2 * θ) * ((∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ) / Real.sin (2 * θ)) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ :=
          mul_div_cancel₀ _ hsinne
      _ = ∫ s in a..b, Work.Spaces.DthIter (l + 1) (H s) z θ := rfl

/-- **The radial exchange for an arbitrary order, with restricted measurability.** -/
theorem DzIter_intervalIntegral_eq_gen_restricted {H : ℝ → ℝ → ℝ → ℝ}
    {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (k l : ℕ) (hkl : k + l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DzIter k (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction k with
  | zero => intro z θ _; rfl
  | succ k ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hθcl : θ ∈ Set.Icc θ₁ θ₂ := ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set zlo : ℝ := max z₁ (z / 2) with hzlo
    have hzlo_lt : zlo < z := by
      rw [hzlo]; exact max_lt hzz.1 (by linarith)
    have hmem_box : ∀ x ∈ Set.Ioo zlo z₂,
        (x, θ) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro x hx
      exact ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩, hθcl⟩
    have hxQ : ∀ x ∈ Set.Ioo zlo z₂, (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => hboxQ (hmem_box x hx)
    have hxpos : ∀ x ∈ Set.Ioo zlo z₂, 0 < x := fun x hx =>
      lt_of_lt_of_le (by linarith : (0:ℝ) < z / 2)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1))
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t x => Work.Spaces.DzIter k (Work.Spaces.DthIter l (H t)) x θ)
      (G' := fun t x => Work.Spaces.mixed (k + 1) l (H t) x θ / x)
      (bound := fun _ => C * (2 / z)) hzlo_lt hzz.2 ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro x hx
      have := (hmeas k l (by omega) x θ (hxQ x hx)).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas k l (by omega) z θ hzQ).mono_measure
          (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        exact hbdd t htT k l (by omega) (z, θ) ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    · have h1 := (hmeas (k + 1) l (by omega) z θ hzQ).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hx2 : z / 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
      have hb := hbdd t htT (k + 1) l (by omega) (x, θ) (hmem_box x hx)
      calc |Work.Spaces.mixed (k + 1) l (H t) x θ / x|
          = |Work.Spaces.mixed (k + 1) l (H t) x θ| / x := by
            rw [abs_div, abs_of_pos (hxpos x hx)]
        _ ≤ C / x := div_le_div_of_nonneg_right hb (le_of_lt (hxpos x hx))
        _ ≤ C / (z / 2) := div_le_div_of_nonneg_left hC (by linarith) hx2
        _ = C * (2 / z) := by field_simp
    · exact intervalIntegrable_const
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder : HasDerivAt (fun x' => Work.Spaces.mixed k l (H t) x' θ)
          (Work.Spaces.pz (Work.Spaces.mixed k l (H t)) x θ) x :=
        Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
          (Work.FTS.LocData.contDiffOn_mixed Work.FTS.EllipticEst.isOpen_Q0 (hsm t htT) k l)
          (θ := θ) ⟨hθ0, hθπ2⟩ (hxpos x hx)
      exact hder.congr_deriv
        (Work.FTS.StrongEps.LocUnif.pz_mixed_div k l (hsm t htT) x θ (hxQ x hx))
    have hloc : (fun x => Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ)
        =ᶠ[𝓝 z] (fun x => ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) x θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzz] with x hx
      exact ih (by omega) x θ ⟨hx, hθθ⟩
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z := by
      show deriv (fun x => Work.Spaces.DzIter k
        (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ) z = _
      rw [hloc.deriv_eq, hcore.deriv]
    have hzne : z ≠ 0 := ne_of_gt hz0
    calc Work.Spaces.DzIter (k + 1)
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k
            (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ := by
          rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      _ = z * (∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z) := by rw [hpz]
      _ = z * ((∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ) / z) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ := mul_div_cancel₀ _ hzne
      _ = ∫ s in a..b, Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l (H s)) z θ := rfl

/-- **Exchange of `mixed j i` (`j + i ≤ n`) with the interval integral, with the measurability
hypothesis restricted to the slots of order `≤ n`.**

This is `Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen` with the (otherwise unused)
measurability of the higher slots dropped: the two inductions behind it only ever evaluate
`hmeas` at slots of order `≤ n`. -/
theorem mixed_intervalIntegral_eq_gen_restricted {H : ℝ → ℝ → ℝ → ℝ}
    {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  have hbox_open : IsOpen (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo
  intro z θ hzθ
  have hA := DthIter_intervalIntegral_eq_gen_restricted (H := H) haT hbT hab hC hsm hmeas hbdd
    hboxQ (l := i) (by omega)
  have hB := DzIter_intervalIntegral_eq_gen_restricted (H := H) haT hbT hab hC hsm hmeas hbdd
    hboxQ j i hji z θ hzθ
  have hA' : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)))
      (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ))
      (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := fun p hp => hA p.1 p.2 hp
  have hloc := Work.FTS.StrongEps.DzIter_congr_of_isOpen hbox_open hA' j hzθ
  simp only [Function.uncurry] at hloc
  calc Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ) z θ := hloc
    _ = ∫ s in a..b, Work.Spaces.DzIter j (Work.Spaces.DthIter i (H s)) z θ := hB
    _ = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := rfl

end Work.FTS.EpsEngine.PerzTools
