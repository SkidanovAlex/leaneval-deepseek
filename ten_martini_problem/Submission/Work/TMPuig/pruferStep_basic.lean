import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs
import Submission.Work.TMComp.RotBasics.PS

open Matrix
open Filter
open scoped Matrix Topology

namespace Work.TMPuig

/-! ## Basic properties of the Prüfer lift `Work.TMContract.pruferStep`

The positive-lift identity, the shift by `2`, the cell estimate `|pruferStep a t - t| < 3/2`
and antitonicity in `a` are all specialisations of results proved in
`Submission/Work/TMComp/RotBasics/PS.lean` for the *same* function
(`RotBasics.Defs` opens `Work.TMContract` and does not redefine `pruferStep`).

Continuity in `t` is proved here from scratch: the only discontinuities of
`t ↦ ⌊t + 1/2⌋` lie at `t = n - 1/2`, `n ∈ ℤ`, and exactly there the definition takes the
value `n`, which is also the two-sided limit (`tan (π(t-n)) → ∓∞`, `arctan → ±π/2`). -/

/-- Continuity of `pruferStep a` in `t`, for every fixed `a`. -/
theorem pruferStep_continuous_aux :
    ∀ a : ℝ, Continuous (fun t : ℝ => Work.TMContract.pruferStep a t) := by
  intro a
  rw [continuous_iff_continuousAt]
  intro t₀
  set n : ℤ := ⌊t₀ + 1 / 2⌋ with hn
  have hn' : ⌊t₀ + 1 / 2⌋ = n := hn.symm
  have hslo : -1/2 ≤ t₀ - (n:ℝ) := by
    have h := Int.floor_le (t₀ + 1/2); rw [hn'] at h; linarith
  have hshi : t₀ - (n:ℝ) < 1/2 := by
    have h := Int.lt_floor_add_one (t₀ + 1/2); rw [hn'] at h; linarith
  rcases eq_or_lt_of_le hslo with hsp | hsp
  · -- corner case: `t₀ = n - 1/2`
    have hspec : t₀ - (n:ℝ) = -1/2 := hsp.symm
    have hval : Work.TMContract.pruferStep a t₀ = (n:ℝ) :=
      Work.TMComp.RotBasics.pruferStep_eq_of_floor_special hn' hspec
    rw [continuousAt_iff_punctured_nhds]
    rw [hval, punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, Filter.tendsto_sup]
    constructor
    · -- left limit: cell `n - 1`
      have hmem : Set.Ioo (t₀ - 1/2) t₀ ∈ 𝓝[<] t₀ := Ioo_mem_nhdsLT (by norm_num)
      have hev : (fun t => Work.TMContract.pruferStep a t) =ᶠ[𝓝[<] t₀]
          (fun t => ((n-1 : ℤ):ℝ) + 1/2
            + Real.arctan (Real.tan (Real.pi * (t - ((n-1 : ℤ):ℝ))) - a)/Real.pi) := by
        filter_upwards [hmem] with t ht
        have hfl : ⌊t + 1/2⌋ = n - 1 := by
          rw [Int.floor_eq_iff]
          constructor <;> push_cast <;> linarith [ht.1, ht.2, hspec]
        have hne : t - ((n-1 : ℤ):ℝ) ≠ -1/2 := by
          push_cast; linarith [ht.1, ht.2, hspec]
        rw [Work.TMComp.RotBasics.pruferStep_eq_of_floor hfl hne]
      have h1 : Tendsto (fun t => Real.pi * (t - ((n-1 : ℤ):ℝ))) (𝓝[<] t₀) (𝓝[<] (Real.pi/2)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc : Tendsto (fun t : ℝ => Real.pi * (t - ((n-1 : ℤ):ℝ))) (𝓝 t₀)
              (𝓝 (Real.pi * (t₀ - ((n-1 : ℤ):ℝ)))) :=
            (by fun_prop : ContinuousAt (fun t : ℝ => Real.pi * (t - ((n-1 : ℤ):ℝ))) t₀).tendsto
          have hval2 : Real.pi * (t₀ - ((n-1 : ℤ):ℝ)) = Real.pi/2 := by
            have h2 : t₀ - ((n-1 : ℤ):ℝ) = 1/2 := by push_cast; linarith [hspec]
            rw [h2]; ring
          rw [hval2] at hc
          exact hc.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [Set.mem_Iio] at ht ⊢
          have h2 : t - ((n-1 : ℤ):ℝ) = (t - t₀) + 1/2 := by push_cast; linarith [hspec]
          rw [h2]
          have h3 : Real.pi * ((t - t₀) + 1/2) = Real.pi * (t - t₀) + Real.pi/2 := by ring
          rw [h3]
          have : Real.pi * (t - t₀) < 0 := mul_neg_of_pos_of_neg Real.pi_pos (sub_neg.mpr ht)
          linarith
      have h2 : Tendsto (fun t => Real.tan (Real.pi * (t - ((n-1 : ℤ):ℝ)))) (𝓝[<] t₀) atTop :=
        Real.tendsto_tan_pi_div_two.comp h1
      have h3 : Tendsto (fun t => Real.tan (Real.pi * (t - ((n-1 : ℤ):ℝ))) - a) (𝓝[<] t₀) atTop := by
        have hh := h2.atTop_add (tendsto_const_nhds : Tendsto (fun _ : ℝ => -a) (𝓝[<] t₀) (𝓝 (-a)))
        simpa [sub_eq_add_neg] using hh
      have h4 : Tendsto (fun t => Real.arctan (Real.tan (Real.pi * (t - ((n-1 : ℤ):ℝ))) - a))
          (𝓝[<] t₀) (𝓝 (Real.pi/2)) :=
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h3
      have h5 : Tendsto (fun t => ((n-1 : ℤ):ℝ) + 1/2
            + Real.arctan (Real.tan (Real.pi * (t - ((n-1 : ℤ):ℝ))) - a)/Real.pi)
          (𝓝[<] t₀) (𝓝 (n:ℝ)) := by
        have h6 := h4.div_const Real.pi
        have h7 := h6.const_add (((n-1 : ℤ):ℝ) + 1/2)
        have hvv : (((n-1 : ℤ):ℝ) + 1/2) + (Real.pi/2)/Real.pi = (n:ℝ) := by
          have : ((n-1 : ℤ):ℝ) = (n:ℝ) - 1 := by push_cast; ring
          rw [this]; field_simp; ring
        simpa only [hvv] using h7
      exact h5.congr' hev.symm
    · -- right limit: cell `n`
      have hmem : Set.Ioo t₀ (t₀ + 1/2) ∈ 𝓝[>] t₀ := Ioo_mem_nhdsGT (by norm_num)
      have hev : (fun t => Work.TMContract.pruferStep a t) =ᶠ[𝓝[>] t₀]
          (fun t => (n:ℝ) + 1/2 + Real.arctan (Real.tan (Real.pi * (t - (n:ℝ))) - a)/Real.pi) := by
        filter_upwards [hmem] with t ht
        have hfl : ⌊t + 1/2⌋ = n := by
          rw [Int.floor_eq_iff]
          constructor <;> linarith [ht.1, ht.2, hspec]
        have hne : t - (n:ℝ) ≠ -1/2 := by linarith [ht.1, ht.2, hspec]
        rw [Work.TMComp.RotBasics.pruferStep_eq_of_floor hfl hne]
      have h1 : Tendsto (fun t => Real.pi * (t - (n:ℝ))) (𝓝[>] t₀) (𝓝[>] (-(Real.pi/2))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc : Tendsto (fun t : ℝ => Real.pi * (t - (n:ℝ))) (𝓝 t₀)
              (𝓝 (Real.pi * (t₀ - (n:ℝ)))) :=
            (by fun_prop : ContinuousAt (fun t : ℝ => Real.pi * (t - (n:ℝ))) t₀).tendsto
          have hval2 : Real.pi * (t₀ - (n:ℝ)) = -(Real.pi/2) := by rw [hspec]; ring
          rw [hval2] at hc
          exact hc.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [Set.mem_Ioi] at ht ⊢
          have h2 : t - (n:ℝ) = (t - t₀) - 1/2 := by linarith [hspec]
          rw [h2]
          have h3 : Real.pi * ((t - t₀) - 1/2) = Real.pi * (t - t₀) - Real.pi/2 := by ring
          rw [h3]
          have : (0:ℝ) < Real.pi * (t - t₀) := mul_pos Real.pi_pos (sub_pos.mpr ht)
          linarith
      have h2 : Tendsto (fun t => Real.tan (Real.pi * (t - (n:ℝ)))) (𝓝[>] t₀) atBot :=
        Real.tendsto_tan_neg_pi_div_two.comp h1
      have h3 : Tendsto (fun t => Real.tan (Real.pi * (t - (n:ℝ))) - a) (𝓝[>] t₀) atBot := by
        have hh := h2.atBot_add (tendsto_const_nhds : Tendsto (fun _ : ℝ => -a) (𝓝[>] t₀) (𝓝 (-a)))
        simpa [sub_eq_add_neg] using hh
      have h4 : Tendsto (fun t => Real.arctan (Real.tan (Real.pi * (t - (n:ℝ))) - a))
          (𝓝[>] t₀) (𝓝 (-(Real.pi/2))) :=
        (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp h3
      have h5 : Tendsto (fun t => (n:ℝ) + 1/2
            + Real.arctan (Real.tan (Real.pi * (t - (n:ℝ))) - a)/Real.pi)
          (𝓝[>] t₀) (𝓝 (n:ℝ)) := by
        have h6 := h4.div_const Real.pi
        have h7 := h6.const_add ((n:ℝ) + 1/2)
        have hvv : ((n:ℝ) + 1/2) + (-(Real.pi/2))/Real.pi = (n:ℝ) := by field_simp; ring
        simpa only [hvv] using h7
      exact h5.congr' hev.symm
  · -- interior case: `-1/2 < t₀ - n < 1/2`
    have hs1 : -(1/2) < t₀ - (n:ℝ) := by linarith
    have hcos : Real.cos (Real.pi * (t₀ - (n:ℝ))) ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, hs1, hshi]
    have hφcont : ContinuousAt (fun t : ℝ => (n:ℝ) + 1/2
        + Real.arctan (Real.tan (Real.pi * (t - (n:ℝ))) - a)/Real.pi) t₀ := by
      have hf : ContinuousAt (fun t : ℝ => Real.pi * (t - (n:ℝ))) t₀ := by fun_prop
      have htan : ContinuousAt (fun t : ℝ => Real.tan (Real.pi * (t - (n:ℝ)))) t₀ :=
        (Real.continuousAt_tan.mpr hcos).comp (f := fun t : ℝ => Real.pi * (t - (n:ℝ))) hf
      have hsub : ContinuousAt (fun t : ℝ => Real.tan (Real.pi * (t - (n:ℝ))) - a) t₀ :=
        htan.sub continuousAt_const
      have harctan : ContinuousAt (fun t : ℝ =>
          Real.arctan (Real.tan (Real.pi * (t - (n:ℝ))) - a)) t₀ :=
        Real.continuous_arctan.continuousAt.comp hsub
      exact continuousAt_const.add (harctan.div_const Real.pi)
    have hev : (fun t : ℝ => (n:ℝ) + 1/2
        + Real.arctan (Real.tan (Real.pi * (t - (n:ℝ))) - a)/Real.pi)
        =ᶠ[𝓝 t₀] (fun t => Work.TMContract.pruferStep a t) := by
      have hmem : Set.Ioo ((n:ℝ) - 1/2) ((n:ℝ) + 1/2) ∈ 𝓝 t₀ :=
        isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
      filter_upwards [hmem] with t ht
      have hfl : ⌊t + 1/2⌋ = n := by
        rw [Int.floor_eq_iff]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hne : t - (n:ℝ) ≠ -1/2 := by
        intro hc; linarith [ht.1, hc]
      rw [Work.TMComp.RotBasics.pruferStep_eq_of_floor hfl hne]
    exact hφcont.congr hev

/-- **The positive-lift identity in coordinates.**  For all `a, t` there is `ρ > 0` with
`ρ * (a cos πt - sin πt) = cos (π · pruferStep a t)` and `ρ * cos πt = sin (π · pruferStep a t)`.
This is `pruferStep_smul_eq` (the positive lift of `comp a`) rewritten coordinatewise, with the
reciprocal scalar (the vector is *not* normalised in the statement). -/
theorem pruferStep_posLift_coord (a t : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ρ * (a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t))
        = Real.cos (Real.pi * Work.TMContract.pruferStep a t) ∧
      ρ * Real.cos (Real.pi * t) = Real.sin (Real.pi * Work.TMContract.pruferStep a t) := by
  obtain ⟨ρ, hρ, h⟩ := Work.TMComp.RotBasics.pruferStep_smul_eq a t
  have hX : a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t)
      = ρ * Real.cos (Real.pi * Work.TMContract.pruferStep a t) := by
    have hre := congrArg Complex.re h
    rw [Work.TMComp.RotBasics.smul_comp, Complex.smul_re] at hre
    exact hre
  have hY : Real.cos (Real.pi * t)
      = ρ * Real.sin (Real.pi * Work.TMContract.pruferStep a t) := by
    have him := congrArg Complex.im h
    rw [Work.TMComp.RotBasics.smul_comp, Complex.smul_im] at him
    exact him
  have hne : ρ ≠ 0 := ne_of_gt hρ
  refine ⟨ρ⁻¹, inv_pos.mpr hρ, ?_, ?_⟩
  · rw [hX, inv_mul_cancel_left₀ hne]
  · rw [hY, inv_mul_cancel_left₀ hne]

/-- **Shift by `2`.**  `pruferStep a (t + 2) = pruferStep a t + 2`. -/
theorem pruferStep_add_two (a t : ℝ) :
    Work.TMContract.pruferStep a (t + 2) = Work.TMContract.pruferStep a t + 2 := by
  have h1 : t + 2 = t + 1 + 1 := by ring
  rw [h1, Work.TMComp.RotBasics.pruferStep_add_one,
    Work.TMComp.RotBasics.pruferStep_add_one]
  ring

/-- **The value is within `(-1/2, 3/2)` of `t`.** -/
theorem pruferStep_sub_mem (a t : ℝ) :
    Work.TMContract.pruferStep a t - t ∈ Set.Ioo (-(1 / 2)) (3 / 2) := by
  set n : ℤ := ⌊t + 1 / 2⌋ with hn
  have hn' : ⌊t + 1 / 2⌋ = n := hn.symm
  have hcell := Work.TMComp.RotBasics.pruferStep_cell a t
  rw [hn'] at hcell
  obtain ⟨hupper, hlower⟩ := hcell
  have hfloor_le := Int.floor_le (t + 1 / 2)
  have hfloor_lt := Int.lt_floor_add_one (t + 1 / 2)
  rw [hn'] at hfloor_le hfloor_lt
  have h1 : t - (n : ℝ) < 1 / 2 := by linarith
  have h2 : (n : ℝ) - t ≤ 1 / 2 := by linarith
  constructor
  · linarith
  · linarith

/-- **Antitonicity in the parameter.**  `a ≤ a' → pruferStep a' t ≤ pruferStep a t`. -/
theorem pruferStep_antitone_param (a a' t : ℝ) (h : a ≤ a') :
    Work.TMContract.pruferStep a' t ≤ Work.TMContract.pruferStep a t :=
  Work.TMComp.RotBasics.pruferStep_antitone t h

theorem pruferStep_basic :
    (∀ a t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      ρ * (a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t)) = Real.cos (Real.pi * Work.TMContract.pruferStep a t) ∧
      ρ * Real.cos (Real.pi * t) = Real.sin (Real.pi * Work.TMContract.pruferStep a t)) ∧
    (∀ a t : ℝ, Work.TMContract.pruferStep a (t + 2) = Work.TMContract.pruferStep a t + 2) ∧
    (∀ a t : ℝ, Work.TMContract.pruferStep a t - t ∈ Set.Ioo (-(1/2)) (3/2)) ∧
    (∀ a a' t : ℝ, a ≤ a' → Work.TMContract.pruferStep a' t ≤ Work.TMContract.pruferStep a t) ∧
    (∀ a : ℝ, Continuous (fun t : ℝ => Work.TMContract.pruferStep a t)) := by
  refine ⟨pruferStep_posLift_coord, pruferStep_add_two, pruferStep_sub_mem,
    pruferStep_antitone_param, pruferStep_continuous_aux⟩

end Work.TMPuig
