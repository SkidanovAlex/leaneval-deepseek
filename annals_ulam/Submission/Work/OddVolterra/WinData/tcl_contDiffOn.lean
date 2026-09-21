import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.WinData.source_contDiffOn
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Work.OddExistence.Manifest.thetaM_lipschitz

/-!
# Smoothness of the clamped `Θ` datum of the odd window construction

The clamped `Θ` datum of the window construction is

`Tcl n h s σ z = wChiT s σ z • ΘM n h s σ z`,

the product of the manifest odd kernel `KernelExt.ThetaM` with the cut-off
`wChiT s σ z = wCs s · wCs σ · wCz (z - baseState σ)`.

`ΘM` is smooth only where the Abel radicand is positive, so `Tcl` is not *a priori* smooth on all
of `ℝ × (ℝ × St)`.  It is nevertheless `C^∞` everywhere, and this file proves it:

* the cut-off `wChiT` is `C^∞` everywhere (`contDiff_wChiT`);
* on the open region `winThetaMRegion` — both slopes in `(237/1000, 963/1000)` and the state within
  `51/100` of `baseState σ` — the manifest kernel is `C^∞`
  (`thetaM_contDiffOn_winThetaMRegion`, from
  `Work.OddExistence.Manifest.contDiffOn_KernelExtThetaM_of_pos`: there the chord endpoints have
  modulus at least `18/25 - 51/100 = 21/100 > 1/5` and every slope sum exceeds `474/1000 > 1/10`,
  so `krad` is positive);
* every point of the closed box `[24/100, 96/100]² ×` the closed ball of radius `101/200` around
  `baseState σ` lies in `winThetaMRegion` (the constants are chosen with a margin), and off that
  box one of the three factors of `wChiT` vanishes on a whole neighbourhood of the point.

Hence `Tcl` is smooth everywhere: on `winThetaMRegion` as a product of two smooth functions, and
off the closed box (where `wChiT` vanishes locally) as the zero function.

The role of the constants: `wCs` is the bump with `rIn = 7/20`, `rOut = 7/20 + 1/100`, centre
`3/5`, so `wCs s = 0` for `s ≤ 24/100` or `96/100 ≤ s`, while `wCs s ≠ 0` forces
`s ∈ (24/100, 96/100)`; `wCz` is the bump with `rIn = 1/2`, `rOut = 101/200`, so on the region
`‖z - baseState σ‖ < 51/100` we have `z 0, z 1 ≥ 18/25 - 51/100 > 1/5`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

/-! ## Two elementary bounds -/

/-- On `|s| ≤ 963/1000` the ball profile stays above `18/25`. -/
lemma profileX_ge_18_25 {s : ℝ} (hs : |s| ≤ 963 / 1000) :
    (18 / 25 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (963 / 1000 : ℝ) ^ 2 := by
    have h := abs_le.mp hs
    nlinarith [h.1, h.2]
  have hsq : Real.sqrt (1 + s ^ 2) ≤ 25 / 18 := by
    have hle : 1 + s ^ 2 ≤ (25 / 18 : ℝ) ^ 2 := by nlinarith [hs2]
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((25 / 18 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 25 / 18 := Real.sqrt_sq (by norm_num)
  rw [Commons.Geometry.Ulam.profileX, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  calc 18 / 25 * Real.sqrt (1 + s ^ 2) ≤ 18 / 25 * (25 / 18) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 := by norm_num

/-- The slope cut-off vanishes below `24/100`. -/
lemma wCs_eq_zero_of_le {s : ℝ} (hs : s ≤ 24 / 100) : (wCs : ℝ → ℝ) s = 0 := by
  apply ContDiffBump.zero_of_le_dist (c := (3 / 5 : ℝ))
  rw [Real.dist_eq, wCs_rOut]
  have h : s - 3 / 5 ≤ 0 := by linarith
  rw [abs_of_nonpos h]
  linarith

/-- The slope cut-off vanishes above `96/100`. -/
lemma wCs_eq_zero_of_ge {s : ℝ} (hs : 96 / 100 ≤ s) : (wCs : ℝ → ℝ) s = 0 := by
  apply ContDiffBump.zero_of_le_dist (c := (3 / 5 : ℝ))
  rw [Real.dist_eq, wCs_rOut]
  have h : 0 ≤ s - 3 / 5 := by linarith
  rw [abs_of_nonneg h]
  linarith

/-! ## Smoothness of the cut-off `wChiT` -/

/-- The cut-off `wChiT` vanishes as soon as its first slope factor does. -/
lemma wChiT_eq_zero_of_left {s σ : ℝ} {z : St} (h : (wCs : ℝ → ℝ) s = 0) :
    wChiT s σ z = 0 := by
  simp only [wChiT, h, zero_mul]

/-- The cut-off `wChiT` vanishes as soon as its second slope factor does. -/
lemma wChiT_eq_zero_of_right {s σ : ℝ} {z : St} (h : (wCs : ℝ → ℝ) σ = 0) :
    wChiT s σ z = 0 := by
  simp only [wChiT, h, zero_mul, mul_zero]

/-- The cut-off `wChiT` vanishes as soon as its state factor does. -/
lemma wChiT_eq_zero_of_state {s σ : ℝ} {z : St} (h : (wCz : St → ℝ) (z - baseState σ) = 0) :
    wChiT s σ z = 0 := by
  simp only [wChiT, h, mul_zero]

/-- The cut-off `wChiT` is `C^∞` on the whole space. -/
lemma contDiff_wChiT :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => wChiT q.1 q.2.1 q.2.2) := by
  unfold wChiT
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => (wCs : ℝ → ℝ) q.1) :=
    (ContDiffBump.contDiff wCs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × St) => (wCs : ℝ → ℝ) q.2.1) :=
    (ContDiffBump.contDiff wCs).comp contDiff_snd.fst
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) => (wCz : St → ℝ) (q.2.2 - baseState q.2.1)) :=
    (ContDiffBump.contDiff wCz).comp
      (contDiff_snd.snd.sub (Work.Anchor.contDiff_baseState_eng.comp contDiff_snd.fst))
  exact (h1.mul h2).mul h3

/-- **The cut-off vanishes near every point outside the closed box**
`[24/100, 96/100] × [24/100, 96/100] × closedBall (baseState σ) (101/200)`. -/
lemma eventually_wChiT_eq_zero {q : ℝ × (ℝ × St)}
    (hq : ¬ (24 / 100 ≤ q.1 ∧ q.1 ≤ 96 / 100 ∧ 24 / 100 ≤ q.2.1 ∧ q.2.1 ≤ 96 / 100 ∧
      ‖q.2.2 - baseState q.2.1‖ ≤ 101 / 200)) :
    ∀ᶠ q' in 𝓝 q, wChiT q'.1 q'.2.1 q'.2.2 = 0 := by
  have hnorm : Continuous (fun q : ℝ × (ℝ × St) => ‖q.2.2 - baseState q.2.1‖) := by
    refine Continuous.norm ?_
    exact (continuous_snd.snd).sub ((Work.Anchor.contDiff_baseState_eng.continuous).comp
      continuous_snd.fst)
  have h_or : ∀ᶠ q' in 𝓝 q, q'.1 ≤ 24 / 100 ∨ 96 / 100 ≤ q'.1 ∨ q'.2.1 ≤ 24 / 100 ∨
      96 / 100 ≤ q'.2.1 ∨ 101 / 200 ≤ ‖q'.2.2 - baseState q'.2.1‖ := by
    simp only [not_and_or, not_le] at hq
    rcases hq with h | h | h | h | h
    · filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds h] with q' hq'
      exact Or.inl hq'.le
    · filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds h] with q' hq'
      exact Or.inr (Or.inl hq'.le)
    · filter_upwards [(isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).mem_nhds h]
        with q' hq'
      exact Or.inr (Or.inr (Or.inl hq'.le))
    · filter_upwards [(isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds h]
        with q' hq'
      exact Or.inr (Or.inr (Or.inr (Or.inl hq'.le)))
    · filter_upwards [(isOpen_lt continuous_const hnorm).mem_nhds h] with q' hq'
      exact Or.inr (Or.inr (Or.inr (Or.inr hq'.le)))
  filter_upwards [h_or] with q' hq'
  rcases hq' with h | h | h | h | h
  · exact wChiT_eq_zero_of_left (wCs_eq_zero_of_le (s := q'.1) h)
  · exact wChiT_eq_zero_of_left (wCs_eq_zero_of_ge (s := q'.1) h)
  · exact wChiT_eq_zero_of_right (wCs_eq_zero_of_le (s := q'.2.1) h)
  · exact wChiT_eq_zero_of_right (wCs_eq_zero_of_ge (s := q'.2.1) h)
  · refine wChiT_eq_zero_of_state ?_
    apply ContDiffBump.zero_of_le_dist (c := (0 : St))
    rwa [dist_zero_right]

/-! ## Smoothness of the manifest kernel on the window region -/

/-- The open region of slope/state space on which the window construction needs the manifest kernel
`ΘM`: both slopes in `(237/1000, 963/1000)` and the state within `51/100` of `baseState σ`.  This
region contains the closed box on which the cut-off `wChiT` is allowed to be non-zero. -/
def winThetaMRegion : Set (ℝ × (ℝ × St)) :=
  {q | 237 / 1000 < q.1 ∧ q.1 < 963 / 1000 ∧ 237 / 1000 < q.2.1 ∧ q.2.1 < 963 / 1000 ∧
    ‖q.2.2 - baseState q.2.1‖ < 51 / 100}

lemma isOpen_winThetaMRegion : IsOpen winThetaMRegion := by
  have hd : Continuous (fun q : ℝ × (ℝ × St) => q.2.2 - baseState q.2.1) :=
    (continuous_snd.snd).sub ((Work.Anchor.contDiff_baseState_eng.continuous).comp
      continuous_snd.fst)
  have hnorm : Continuous (fun q : ℝ × (ℝ × St) => ‖q.2.2 - baseState q.2.1‖) := hd.norm
  have h : IsOpen ({q : ℝ × (ℝ × St) | 237 / 1000 < q.1} ∩
      ({q : ℝ × (ℝ × St) | q.1 < 963 / 1000} ∩
      ({q : ℝ × (ℝ × St) | 237 / 1000 < q.2.1} ∩
      ({q : ℝ × (ℝ × St) | q.2.1 < 963 / 1000} ∩
      {q : ℝ × (ℝ × St) | ‖q.2.2 - baseState q.2.1‖ < 51 / 100})))) :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
      ((isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).inter
      (isOpen_lt hnorm continuous_const))))
  convert h using 1
  ext q
  simp only [winThetaMRegion, Set.mem_ofPred_eq, Set.mem_inter_iff]

/-- On `winThetaMRegion` the two chord endpoints have modulus at least `1/5`. -/
lemma winThetaMRegion_abs_state {q : ℝ × (ℝ × St)} (hq : q ∈ winThetaMRegion) :
    1 / 5 ≤ |q.2.2 0| ∧ 1 / 5 ≤ |q.2.2 1| := by
  rw [winThetaMRegion] at hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  have hprof : (18 / 25 : ℝ) ≤ Commons.Geometry.Ulam.profileX q.2.1 := by
    apply profileX_ge_18_25
    rw [abs_le]
    constructor <;> linarith
  have hkey : ∀ i : Fin 4, (i = 0 ∨ i = 1) → 1 / 5 ≤ |q.2.2 i| := by
    intro i hi
    have hii : |q.2.2 i - baseState q.2.1 i| ≤ ‖q.2.2 - baseState q.2.1‖ := by
      have := norm_le_pi_norm (q.2.2 - baseState q.2.1) i
      rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    have hb : baseState q.2.1 i = Commons.Geometry.Ulam.profileX q.2.1 := by
      rcases hi with rfl | rfl <;> simp [Work.OddVolterra.baseState]
    rw [hb] at hii
    have hlow : -(51 / 100) < q.2.2 i - Commons.Geometry.Ulam.profileX q.2.1 := by
      have := (abs_lt.mp (lt_of_le_of_lt hii h5)).1
      linarith
    have hpos : (1 / 5 : ℝ) ≤ q.2.2 i := by linarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact ⟨hkey 0 (Or.inl rfl), hkey 1 (Or.inr rfl)⟩

/-- **The manifest `Θ` kernel is `C^∞` on the window region.** -/
lemma thetaM_contDiffOn_winThetaMRegion (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × St) => KernelExt.ThetaM n h q.1 q.2.1 q.2.2)
      winThetaMRegion := by
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by norm_num)) s
  refine Work.OddExistence.Manifest.contDiffOn_KernelExtThetaM_of_pos n hh
    isOpen_winThetaMRegion ?_ ?_
  · intro q hq
    obtain ⟨hz0, hz1⟩ := winThetaMRegion_abs_state hq
    rw [winThetaMRegion] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    exact ⟨krad_pos_of_add_pos' hsupp hsmall1 (by linarith) (by rwa [abs_neg]),
      krad_pos_of_add_pos' hsupp hsmall1 (by linarith) hz1⟩
  · intro q hq τ hτ
    obtain ⟨hz0, hz1⟩ := winThetaMRegion_abs_state hq
    rw [winThetaMRegion] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    obtain ⟨hτ0, hτ1⟩ := hτ
    have ha : 237 / 1000 < q.1 + τ * (q.2.1 - q.1) := by
      rcases le_total q.1 q.2.1 with hle | hle
      · have := mul_nonneg hτ0 (sub_nonneg.mpr hle)
        linarith
      · have := mul_le_mul_of_nonpos_right hτ1 (sub_nonpos.mpr hle)
        linarith
    exact ⟨krad_pos_of_add_pos' hsupp hsmall1 (by linarith) (by rwa [abs_neg]),
      krad_pos_of_add_pos' hsupp hsmall1 (by linarith) hz1⟩

/-! ## The clamped `Θ` datum -/

theorem tcl_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (ℝ × Work.OddVolterra.St) =>
        Work.OddVolterra.WinData.Tcl n h q.1 q.2.1 q.2.2) Set.univ := by
  have hfun : (fun q : ℝ × (ℝ × St) => Tcl n h q.1 q.2.1 q.2.2) =
      fun q : ℝ × (ℝ × St) =>
        wChiT q.1 q.2.1 q.2.2 • KernelExt.ThetaM n h q.1 q.2.1 q.2.2 := rfl
  rw [hfun, contDiffOn_univ, contDiff_iff_contDiffAt]
  intro q
  by_cases hq : 24 / 100 ≤ q.1 ∧ q.1 ≤ 96 / 100 ∧ 24 / 100 ≤ q.2.1 ∧ q.2.1 ≤ 96 / 100 ∧
      ‖q.2.2 - baseState q.2.1‖ ≤ 101 / 200
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    have hqV : q ∈ winThetaMRegion := by
      rw [winThetaMRegion]
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    have hsm := thetaM_contDiffOn_winThetaMRegion n hh hsupp hsmall
    have hW : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × (ℝ × St) =>
          wChiT q.1 q.2.1 q.2.2 • KernelExt.ThetaM n h q.1 q.2.1 q.2.2)
        winThetaMRegion := contDiff_wChiT.contDiffOn.smul hsm
    exact hW.contDiffAt (isOpen_winThetaMRegion.mem_nhds hqV)
  · refine ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : ℝ × (ℝ × St) => (0 : St)) (contDiffAt_const (c := (0 : St))) ?_
    filter_upwards [eventually_wChiT_eq_zero hq] with q' hq'
    rw [hq', zero_smul]

end

end Work.OddVolterra.WinData
