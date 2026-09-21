import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.WinData.win_lines
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat

/-!
# Smoothness of the clamped state datum `Gcl` of the odd window construction

The clamped state datum of the window construction is

`Gcl n h s z = wChiG s z • diagForm n h s z`,

the product of the explicit diagonal form of the state datum with the cut-off
`wChiG s z = wCs s · wCz (z - baseState s)`.

`diagForm` is smooth only where the Abel radicand is positive, so `Gcl` is not *a priori* smooth
on all of `ℝ × St`.  It is nevertheless `C^∞` everywhere, and this file proves it:

* the cut-off `wChiG` is `C^∞` everywhere (`gcl_contDiff_wChiG`);
* on the open region `gRegion` — the slope in `(237/1000, 963/1000)` and the first two state
  coordinates of modulus `> 1/5` — the manifest state datum `GoddM` (= `Godd` = `diagForm`) is
  `C^∞` (`gcl_contDiffOn_GoddM_region`), because there the Abel radicand `krad h s t s` is
  positive at the two chord endpoints `t = ±z 0`, `z 1` (`krad_pos_of_add_pos`: `σ + a = 2s >
  1/10` and `|t| ≥ 1/5`);
* every point of the closed box `[24/100, 96/100] ×` the closed ball of radius `101/200` around
  `baseState s` lies in `gRegion` (the constants are chosen with a margin: `18/25 - 101/200 >
  1/5`), and off that box the cut-off `wChiG` vanishes on a whole neighbourhood of the point.

Hence `Gcl` is smooth everywhere: on `gRegion` as a product of two smooth functions, and off the
closed box (where `wChiG` vanishes locally) as the zero function.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The box containing the support of the cut-off, and the good region -/

/-- The closed box containing the support of the cut-off `wChiG`: the slope within the support of
the slope bump, the state within the support of the state bump. -/
def gBox : Set (ℝ × St) :=
  {p | 24 / 100 ≤ p.1 ∧ p.1 ≤ 96 / 100 ∧ ‖p.2 - baseState p.1‖ ≤ 101 / 200}

/-- The open region on which the state datum is `C^∞`: the slopes on which the cut-off can be
non-zero, and the two chord endpoints at distance `> 1/5` from the axis. -/
def gRegion : Set (ℝ × St) :=
  {p | 237 / 1000 < p.1 ∧ p.1 < 963 / 1000 ∧ 1 / 5 < |p.2 0| ∧ 1 / 5 < |p.2 1|}

/-! ## Elementary bounds -/

/-- On `|s| ≤ 963/1000` the ball profile stays above `18/25`. -/
lemma gcl_profileX_ge {s : ℝ} (hs : |s| ≤ 963 / 1000) :
    (18 / 25 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (963 / 1000 : ℝ) ^ 2 := by
    have h := abs_le.mp hs
    nlinarith [h.1, h.2]
  have hsq : Real.sqrt (1 + s ^ 2) ≤ 25 / 18 := by
    have hle : 1 + s ^ 2 ≤ (25 / 18 : ℝ) ^ 2 := by nlinarith [hs2]
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((25 / 18 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 25 / 18 := Real.sqrt_sq (by norm_num)
  rw [profileX_unfold, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  calc 18 / 25 * Real.sqrt (1 + s ^ 2) ≤ 18 / 25 * (25 / 18) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 := by norm_num

lemma gcl_isOpen_region : IsOpen gRegion := by
  have hcont0 : Continuous (fun p : ℝ × St => |p.2 0|) := by fun_prop
  have hcont1 : Continuous (fun p : ℝ × St => |p.2 1|) := by fun_prop
  have heq : gRegion = {p : ℝ × St | 237 / 1000 < p.1} ∩
      ({p : ℝ × St | p.1 < 963 / 1000} ∩
      ({p : ℝ × St | 1 / 5 < |p.2 0|} ∩ {p : ℝ × St | 1 / 5 < |p.2 1|})) := by
    ext p
    simp only [gRegion, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [heq]
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const hcont0).inter (isOpen_lt continuous_const hcont1)))

lemma gcl_isClosed_box : IsClosed gBox := by
  have hc : Continuous (fun p : ℝ × St => ‖p.2 - baseState p.1‖) :=
    (continuous_snd.sub Existence.contDiff_baseState_comp.continuous).norm
  have heq : gBox = {p : ℝ × St | 24 / 100 ≤ p.1} ∩
      ({p : ℝ × St | p.1 ≤ 96 / 100} ∩ {p : ℝ × St | ‖p.2 - baseState p.1‖ ≤ 101 / 200}) := by
    ext p
    simp only [gBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [heq]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter (isClosed_le hc continuous_const))

/-! ## The cut-off -/

/-- The cut-off `wChiG` is `C^∞` on the whole space. -/
lemma gcl_contDiff_wChiG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => wChiG p.1 p.2) := by
  have hbase := Existence.contDiff_baseState_comp
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (wCs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff wCs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => (wCz : St → ℝ) (p.2 - baseState p.1)) :=
    (ContDiffBump.contDiff wCz).comp (contDiff_snd.sub hbase)
  simpa only [wChiG] using h1.mul h2

/-- The support of the cut-off `wChiG` is contained in the closed box `gBox`. -/
lemma gcl_support_subset_box :
    Function.support (fun p : ℝ × St => wChiG p.1 p.2) ⊆ gBox := by
  intro p hp
  rw [Function.mem_support] at hp
  have hcs : (wCs : ℝ → ℝ) p.1 ≠ 0 := fun h0 => hp (by rw [wChiG, h0, zero_mul])
  have hcz : (wCz : St → ℝ) (p.2 - baseState p.1) ≠ 0 :=
    fun h0 => hp (by rw [wChiG, h0, mul_zero])
  have hs : p.1 ∈ Metric.ball (3 / 5 : ℝ) wCs.rOut := by
    have h : p.1 ∈ Function.support (wCs : ℝ → ℝ) := Function.mem_support.mpr hcs
    rwa [ContDiffBump.support_eq] at h
  have hz : p.2 - baseState p.1 ∈ Metric.ball (0 : St) wCz.rOut := by
    have h : (p.2 - baseState p.1) ∈ Function.support (wCz : St → ℝ) :=
      Function.mem_support.mpr hcz
    rwa [ContDiffBump.support_eq] at h
  rw [Metric.mem_ball, Real.dist_eq, wCs_rOut] at hs
  rw [Metric.mem_ball, dist_zero_right, wCz_rOut] at hz
  obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
  exact ⟨by linarith, by linarith, le_of_lt hz⟩

/-- The closed box is contained in the good open region.  On it the ball profile is `≥ 18/25`, so
the two chord endpoints are at distance `> 1/5` from the axis. -/
lemma gcl_box_subset_region : gBox ⊆ gRegion := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hprof : (18 / 25 : ℝ) ≤ Commons.Geometry.Ulam.profileX p.1 :=
    gcl_profileX_ge (by rw [abs_le]; constructor <;> linarith)
  have hcoord : ∀ i : Fin 4, |p.2 i - baseState p.1 i| ≤ 101 / 200 := by
    intro i
    have h := norm_le_pi_norm (p.2 - baseState p.1) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h h3
  have key : ∀ i : Fin 4, (i = 0 ∨ i = 1) → 1 / 5 < |p.2 i| := by
    intro i hi
    have h := hcoord i
    have hb : baseState p.1 i = Commons.Geometry.Ulam.profileX p.1 := by
      rcases hi with rfl | rfl <;> simp [Work.OddVolterra.baseState]
    rw [hb] at h
    have hlow : (1 / 5 : ℝ) < p.2 i := by linarith [(abs_le.mp h).1]
    exact lt_of_lt_of_le hlow (le_abs_self _)
  exact ⟨by linarith, by linarith, key 0 (Or.inl rfl), key 1 (Or.inr rfl)⟩

/-! ## Smoothness of the state datum on the good region -/

/-- **The manifest state datum is `C^∞` on `gRegion`.**  There the two chord-endpoint radicands
`krad h s t s` are positive, so `KvecM` is `C^∞`; the diagonal reduction `G2M_diag` exhibits
`GoddM` as that kernel times the constant `∫_0^1 (√(τ(1-τ)))⁻¹`. -/
lemma gcl_contDiffOn_GoddM_region (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => KernelExt.GoddM n h p.1 p.2) gRegion := by
  have hpos0 : ∀ p ∈ gRegion, 0 < Kden h p.1 p.1 (-(p.2 0)) := by
    intro p hp
    obtain ⟨hs1, _, hz0, _⟩ := hp
    rw [Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (Existence.krad_pos_of_add_pos hsupp hsmall
      (a := p.1) (σ := p.1) (t := -(p.2 0)) (by linarith) (by rw [abs_neg]; exact le_of_lt hz0))
  have hpos1 : ∀ p ∈ gRegion, 0 < Kden h p.1 p.1 (p.2 1) := by
    intro p hp
    obtain ⟨hs1, _, _, hz1⟩ := hp
    rw [Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (Existence.krad_pos_of_add_pos hsupp hsmall
      (a := p.1) (σ := p.1) (t := p.2 1) (by linarith) (le_of_lt hz1))
  have hK := Existence.contDiffOn_KvecM_diag n hh hpos0 hpos1
  have hKm : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St =>
      - (((KernelExt.KvecM n h p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) i) *
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹)) gRegion :=
    fun i => (((contDiffOn_pi.mp hK) i).mul contDiffOn_const).neg
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · refine (Existence.contDiffOn_coord (B := gRegion) 0).congr (fun p _ => ?_)
    simp [KernelExt.GoddM]
  · refine (Existence.contDiffOn_coord (B := gRegion) 1).congr (fun p _ => ?_)
    simp [KernelExt.GoddM]
  · refine (hKm 0).congr (fun p _ => ?_)
    simp only [KernelExt.GoddM]
    rw [Existence.G2M_diag n h p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3) 0]
    simp
  · refine (hKm 1).congr (fun p _ => ?_)
    simp only [KernelExt.GoddM]
    rw [Existence.G2M_diag n h p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3) 1]
    simp

/-! ## The target -/

theorem gcl_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Work.OddVolterra.St => Work.OddVolterra.WinData.Gcl n h p.1 p.2) Set.univ := by
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by norm_num)) s
  have hsm := gcl_contDiffOn_GoddM_region n hh hsupp hsmall1
  -- the clamped datum is the cut-off times the manifest state datum
  have hGcl : ∀ p : ℝ × St,
      Gcl n h p.1 p.2 = wChiG p.1 p.2 • KernelExt.GoddM n h p.1 p.2 := by
    intro p
    rw [Gcl, Window.GoddM_eq_Godd n hh p.1 p.2, Godd_eq_diagForm n h p.1 p.2]
  have hgood : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Gcl n h p.1 p.2) gRegion :=
    (gcl_contDiff_wChiG.contDiffOn.smul hsm).congr (fun p _ => hGcl p)
  have hzero : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Gcl n h p.1 p.2) gBoxᶜ := by
    refine (contDiffOn_const (c := (0 : St))).congr (fun p hp => ?_)
    have hmem : p ∉ Function.support (fun p : ℝ × St => wChiG p.1 p.2) :=
      fun hc => hp (gcl_support_subset_box hc)
    rw [hGcl p, Function.notMem_support.mp hmem, zero_smul]
  refine contDiffOn_of_locally_contDiffOn (fun p _ => ?_)
  by_cases hp : p ∈ gRegion
  · exact ⟨gRegion, gcl_isOpen_region, hp, hgood.mono Set.inter_subset_right⟩
  · exact ⟨gBoxᶜ, gcl_isClosed_box.isOpen_compl, fun hc => hp (gcl_box_subset_region hc),
      hzero.mono Set.inter_subset_right⟩

end

end Work.OddVolterra.WinData
