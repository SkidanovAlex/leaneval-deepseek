import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Gates
import Submission.Work.Pert.tools
import Submission.Work.Pert.nearTranslation_F0
import Submission.Work.Pert.Qreg_norm_lower
import Submission.Work.Parab.germ
import Submission.Work.Parab.basin_basic
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.Parab.petal_cone
import Submission.Work.Parab.flower
import Submission.Work.FatouCoord.Petal.petal_mapsTo_tendsto_of_le

/-!
# `Work.Pert.limitCoord_plus_exists`

The limit Fatou coordinate of the unperturbed conjugated germ `F₀ w = τ₀ (f₀ (τ₀ w))`,
`τ₀ w = -1/w`, on the cone `Qreg (some ξ₁) none = {w | Re w + |Im w| > ξ₁}`, identified with
the datum's coordinate `d.Φ ∘ τ₀` on the part of the cone whose `τ₀`-image lies in the
parabolic basin.

The coordinate is the maximal-domain extension of `d.Φ ∘ τ₀`:
`Φ u = d.Φ (τ₀ (F₀^[j] u)) - j` at any level `j` whose `τ₀`-image is in the basin.  The levels
are consistent by `d.Φ_abel`, and a good level exists because every orbit of `F₀` inside the
cone drifts to `+∞` (so the `τ₀`-images march into the tiny cone `-Re z > |Im z|`), while that
tiny cone lies in the parabolic basin — it is contained in the attracting petal of the germ.
-/

namespace Work.Pert

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-! ## The conjugated germ and the cone -/

/-- The germ in the coordinate `w = τ₀ z = -1/z`. -/
def tauConj (f₀ : ℂ → ℂ) : ℂ → ℂ := fun w => MandelDim.tau0 (f₀ (MandelDim.tau0 w))

@[simp] theorem tauConj_apply (w : ℂ) :
    tauConj f₀ w = MandelDim.tau0 (f₀ (MandelDim.tau0 w)) := rfl

/-- The cone `Qreg (some ξ) none` in coordinates. -/
theorem mem_Qreg_cone {ξ : ℝ} {z : ℂ} :
    z ∈ MandelDim.Qreg (some (ξ : ℂ)) none ↔ ξ < z.re + |z.im| := by
  rw [MandelDim.Qreg]
  constructor
  · intro h
    have h1 := h.1 (ξ : ℂ) (by simp)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero] at h1
    linarith
  · intro h
    refine ⟨fun b hb => ?_, fun b hb => by simp at hb⟩
    rw [Option.mem_def, Option.some.injEq] at hb
    subst hb
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero]
    linarith

/-- The cone is open. -/
theorem isOpen_Qreg_cone {ξ : ℝ} : IsOpen (MandelDim.Qreg (some (ξ : ℂ)) none) := by
  have h : MandelDim.Qreg (some (ξ : ℂ)) none = {z : ℂ | ξ < z.re + |z.im|} := by
    ext z; exact mem_Qreg_cone
  rw [h]
  exact isOpen_lt continuous_const (Complex.continuous_re.add Complex.continuous_im.abs)

/-- Monotonicity of the cone in the vertex. -/
theorem Qreg_cone_mono {ξ ξ' : ℝ} (h : ξ ≤ ξ') :
    MandelDim.Qreg (some (ξ' : ℂ)) none ⊆ MandelDim.Qreg (some (ξ : ℂ)) none := by
  intro z hz
  rw [mem_Qreg_cone] at hz ⊢
  linarith

/-! ## The march -/

/-- Coordinate bounds from `‖G w - (w+1)‖ ≤ 1/32`. -/
theorem step_bounds {G : ℂ → ℂ} {w : ℂ} (h : ‖G w - (w + 1)‖ ≤ 1 / 32) :
    |(G w).re - (w.re + 1)| ≤ 1 / 32 ∧ |(G w).im - w.im| ≤ 1 / 32 := by
  constructor
  · have h1 := Complex.abs_re_le_norm (G w - (w + 1))
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re] at h1
    linarith
  · have h1 := Complex.abs_im_le_norm (G w - (w + 1))
    simp only [Complex.sub_im, Complex.add_im, Complex.one_im, add_zero] at h1
    linarith

/-- Iterating `G`: the cone is invariant and the real part drifts to `+∞`. -/
theorem G_iterate_spec {ξ : ℝ} {G : ℂ → ℂ}
    (hstep : ∀ z ∈ MandelDim.Qreg (some (ξ : ℂ)) none, ‖G z - (z + 1)‖ ≤ 1 / 32)
    {w : ℂ} (hw : w ∈ MandelDim.Qreg (some (ξ : ℂ)) none) (j : ℕ) :
    (G^[j] w ∈ MandelDim.Qreg (some (ξ : ℂ)) none) ∧
      (G^[j] w).re ≥ w.re + (j : ℝ) * (31 / 32) ∧
      |(G^[j] w).im| ≤ |w.im| + (j : ℝ) * (1 / 32) := by
  induction j with
  | zero => simp [hw]
  | succ j ih =>
    obtain ⟨hmem, hre, him⟩ := ih
    obtain ⟨hb1, hb2⟩ := step_bounds (hstep _ hmem)
    have hb1' : (G (G^[j] w)).re ≥ (G^[j] w).re + 31 / 32 := by
      have := (abs_le.mp hb1).1; linarith
    have hb2a : |(G (G^[j] w)).im| ≤ |(G^[j] w).im| + 1 / 32 := by
      have h4 : |(G (G^[j] w)).im - (G^[j] w).im| ≤ 1 / 32 := by
        rw [abs_le]; exact ⟨by linarith [(abs_le.mp hb2).1], by linarith [(abs_le.mp hb2).2]⟩
      have h5 := abs_sub_abs_le_abs_sub ((G (G^[j] w)).im) ((G^[j] w).im)
      have h6 := (abs_le.mp h4).2
      linarith
    have hb2b : |(G (G^[j] w)).im| ≥ |(G^[j] w).im| - 1 / 32 := by
      have h4 : |(G (G^[j] w)).im - (G^[j] w).im| ≤ 1 / 32 := by
        rw [abs_le]; exact ⟨by linarith [(abs_le.mp hb2).1], by linarith [(abs_le.mp hb2).2]⟩
      have h5 := abs_sub_abs_le_abs_sub ((G^[j] w).im) ((G (G^[j] w)).im)
      have h6 : |(G^[j] w).im - (G (G^[j] w)).im| ≤ 1 / 32 := by
        rw [abs_sub_comm]; exact h4
      linarith [h5, h6]
    have hmem' : G (G^[j] w) ∈ MandelDim.Qreg (some (ξ : ℂ)) none := by
      rw [mem_Qreg_cone] at hmem ⊢
      linarith
    rw [Function.iterate_succ_apply']
    exact ⟨hmem', by push_cast; linarith, by push_cast; linarith⟩

/-- **Confinement.**  Every `τ₀`-image along the orbit of a point of the cone has modulus
`< 2/ξ`. -/
theorem norm_tau0_iterate_lt {ξ : ℝ} (hξ : 0 < ξ) {G : ℂ → ℂ}
    (hstep : ∀ z ∈ MandelDim.Qreg (some (ξ : ℂ)) none, ‖G z - (z + 1)‖ ≤ 1 / 32)
    {w : ℂ} (hw : w ∈ MandelDim.Qreg (some (ξ : ℂ)) none) (j : ℕ) :
    ‖MandelDim.tau0 ((G^[j]) w)‖ < 2 / ξ := by
  have hmem := (G_iterate_spec hstep hw j).1
  have hgt := NTF0.norm_gt_of_mem_right hmem
  have hpos : 0 < ‖(G^[j]) w‖ := by linarith
  rw [NTF0.norm_tau0]
  have h1 : 1 / ‖(G^[j]) w‖ < 1 / (ξ / 2) := one_div_lt_one_div_of_lt (by linarith) hgt
  have h2 : 1 / (ξ / 2) = 2 / ξ := by field_simp
  linarith [h1, h2.le, h2.ge]

/-! ## `τ₀` interchanges the two dynamics -/

theorem tau0_eq_zero_iff {z : ℂ} : MandelDim.tau0 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    have h2 : (-1 : ℂ) / z = 0 := h
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · norm_num at h2
    · exact hz h2
  · intro h; rw [h]; simp [MandelDim.tau0]

theorem tau0_ne_zero {z : ℂ} (hz : z ≠ 0) : MandelDim.tau0 z ≠ 0 :=
  fun h => hz (tau0_eq_zero_iff.mp h)

theorem tau0_invol' {z : ℂ} (hz : z ≠ 0) : MandelDim.tau0 (MandelDim.tau0 z) = z :=
  NTF0.tau0_invol hz

theorem tau0_injective : Function.Injective MandelDim.tau0 := by
  intro a b hab
  rcases eq_or_ne a 0 with rfl | ha
  · exact (tau0_eq_zero_iff.mp (hab ▸ (tau0_eq_zero_iff.mpr rfl))).symm
  · rcases eq_or_ne b 0 with rfl | hb
    · exact tau0_eq_zero_iff.mp (hab ▸ (tau0_eq_zero_iff.mpr rfl))
    · rw [← tau0_invol' ha, hab, tau0_invol' hb]

/-- The orbit relation, as long as the orbit does not meet `0` and the `τ₀`-images are small
enough that `f₀` has no further zeros there. -/
theorem tau0_iterate_eq {ξ : ℝ} {G : ℂ → ℂ} (hG : ∀ w, G w = tauConj f₀ w)
    (hzero : ∀ z : ℂ, ‖z‖ < 2 / ξ → f₀ z = 0 → z = 0)
    {w : ℂ} (hGne : ∀ j, (G^[j]) w ≠ 0)
    (hbound : ∀ j, ‖MandelDim.tau0 ((G^[j]) w)‖ < 2 / ξ) (j : ℕ) :
    MandelDim.tau0 ((G^[j]) w) = (f₀^[j]) (MandelDim.tau0 w) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hfne : f₀ (MandelDim.tau0 ((G^[j]) w)) ≠ 0 := by
      intro h
      have h1 : MandelDim.tau0 ((G^[j]) w) = 0 := hzero _ (hbound j) h
      have h2 : (G^[j]) w = 0 := tau0_eq_zero_iff.mp h1
      exact hGne j h2
    rw [Function.iterate_succ_apply', hG, tauConj_apply, tau0_invol' hfne, ih,
      Function.iterate_succ_apply']

/-! ## The tiny cone is contained in the parabolic basin -/

/-- The cone condition `-Re z > |Im z|` gives the angular bound `|arg z| ≥ 3π/4`. -/
theorem cone_arg_ge {z : ℂ} (hz : z ≠ 0) (h : -z.re > |z.im|) : 3 * Real.pi / 4 ≤ |z.arg| := by
  have hcos : Real.cos |z.arg| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  have hsinarg : Real.sin |z.arg| = |Real.sin z.arg| := by
    rcases lt_trichotomy (0 : ℝ) z.arg with h0 | h0 | h0
    · rw [abs_of_nonneg h0.le,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0.le (Complex.arg_le_pi z))]
    · rw [← h0]; simp
    · rw [abs_of_neg h0, Real.sin_neg,
        abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h0 (Complex.neg_pi_lt_arg z))]
  have hsin : Real.sin |z.arg| = |z.im| / ‖z‖ := by
    rw [hsinarg, Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg z)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.cos |z.arg| < -Real.sin |z.arg| := by
    rw [hcos, hsin]
    have h2 := div_lt_div_of_pos_right (show z.re < -|z.im| by linarith) hn
    rwa [neg_div] at h2
  have h2 : Real.cos |z.arg| + Real.sin |z.arg| < 0 := by linarith
  have h3 : Real.cos |z.arg| + Real.sin |z.arg| =
      Real.sqrt 2 * Real.sin (|z.arg| + Real.pi / 4) := by
    rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have h4 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← sq, Real.sq_sqrt (by norm_num)]
    nlinarith [h4]
  have h5 : Real.sin (|z.arg| + Real.pi / 4) < 0 := by
    have h6 : Real.sqrt 2 * Real.sin (|z.arg| + Real.pi / 4) < 0 := by rw [← h3]; exact h2
    rcases mul_neg_iff.mp h6 with ⟨-, h7⟩ | ⟨h7, -⟩
    · exact h7
    · exact absurd h7 (not_lt.mpr (Real.sqrt_nonneg 2))
  have h6 : |z.arg| + Real.pi / 4 > Real.pi := by
    by_contra hc
    push_neg at hc
    have h7 : 0 ≤ Real.sin (|z.arg| + Real.pi / 4) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hc
    linarith
  linarith

/-- **The tiny cone lies in the basin**: it is contained in the attracting petal, which is
forward invariant with uniform convergence to `0` and lies in the domain of `f₀`. -/
theorem cone_subset_basin (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z‖ < ρ → -z.re > |z.im| →
      z ∈ MandelDim.ParabolicBasin f₀ D₀ := by
  classical
  obtain ⟨h, a, r, A, A', hb, hball⟩ := Work.Parab.exists_parabolicBounds_of_germ hd
  have hrpos : 0 < r := hb.hr
  obtain ⟨M₁, hM₁⟩ := Work.FatouCoord.Petal.petal_mapsTo_tendsto_of_le hb
  obtain ⟨M', hM'pos, hunif⟩ := Work.Parab.petal_uniform_convergence hb
  set M : ℝ := max (max M₁ M') 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM₁M : M₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM'M : M' ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨ρ, hρpos, hρ⟩ := Work.Parab.petal_cone (r := r) (M := M) (δ := Real.pi / 12)
    hb.hr hMpos (by positivity) (by linarith [Real.pi_pos])
  refine ⟨min ρ r, lt_min hρpos hb.hr, fun z hz hcone => ?_⟩
  have hzr : ‖z‖ < r := lt_of_lt_of_le hz (min_le_right _ _)
  have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz0 : z ≠ 0 := by intro h; rw [h] at hcone; simp at hcone
  have harg : Real.pi / 2 + Real.pi / 12 ≤ |z.arg| := by
    have := cone_arg_ge hz0 hcone
    linarith [Real.pi_pos]
  have hzP : z ∈ Work.FatouCoord.Petal r M := hρ z (norm_pos_iff.mpr hz0) hzρ harg
  have hmapM : MapsTo f₀ (Work.FatouCoord.Petal r M) (Work.FatouCoord.Petal r M) :=
    (hM₁ M hM₁M).1
  refine ⟨Work.FatouCoord.Petal r M, Work.FatouCoord.isOpen_Petal.mem_nhds hzP, ?_, ?_⟩
  · intro n z' hz'
    exact hball (Work.FatouCoord.Petal_subset_ball
      (Work.FatouCoord.mapsTo_iterate_of_mapsTo hmapM n hz'))
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif ε hε
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn w hw =>
      by simpa [dist_eq_norm] using hN n hn w (Work.FatouCoord.Petal_mono le_rfl hM'M hw)⟩

/-! ## Elementary basin facts -/

theorem isOpen_basin (f : ℂ → ℂ) (D : Set ℂ) : IsOpen (MandelDim.ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hmap, hunif⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  exact Filter.mem_of_superset (hVopen.mem_nhds hzV) fun y hy =>
    ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hunif.mono hVU⟩

theorem basin_subset_domain (f : ℂ → ℂ) (D : Set ℂ) :
    MandelDim.ParabolicBasin f D ⊆ D := by
  rintro z ⟨U, hU, hmap, -⟩
  exact hmap 0 (mem_of_mem_nhds hU)

/-- **Forward invariance at a tiny basin point**, from local injectivity of `f₀` near `0`. -/
theorem basin_forward_tiny {ρ : ℝ}
    (hinj : ∀ z ∈ ball 0 ρ, ∀ z' ∈ ball 0 ρ, f₀ z = f₀ z' → z = z')
    (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∀ z ∈ MandelDim.ParabolicBasin f₀ D₀, ‖z‖ < ρ → f₀ z ∈ MandelDim.ParabolicBasin f₀ D₀ := by
  intro z hz hzρ
  have hzD : z ∈ D₀ := basin_subset_domain f₀ D₀ hz
  have hzan : AnalyticAt ℂ f₀ z := hd.2.2.1.analyticAt (hd.1.mem_nhds hzD)
  have hnc : ¬ ∀ᶠ w in 𝓝 z, f₀ w = f₀ z := by
    intro hev
    rw [Filter.eventually_iff] at hev
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hev
    have hρz : 0 < ρ - ‖z‖ := sub_pos.mpr hzρ
    set δ : ℝ := min ε (ρ - ‖z‖) / 2 with hδ
    have hδpos : 0 < δ := half_pos (lt_min hε hρz)
    have hδε : δ < ε := lt_of_le_of_lt (by rw [hδ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) (half_lt_self hε)
    have hδρ : δ < ρ - ‖z‖ := lt_of_le_of_lt (by rw [hδ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) (half_lt_self hρz)
    set w : ℂ := z + (δ : ℂ) with hw
    have hwz : w ≠ z := by
      intro h
      have : (δ : ℂ) = 0 := by
        have h2 : w - z = 0 := by rw [h]; ring
        rw [hw] at h2; simpa using h2
      exact hδpos.ne' (Complex.ofReal_eq_zero.mp this)
    have hwε : w ∈ ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδpos]
      exact hδε
    have hwρ : ‖w‖ < ρ := by
      have h1 : ‖w - z‖ = δ := by
        rw [hw, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
      calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            have := norm_add_le (w - z) z; simpa using this
        _ = δ + ‖z‖ := by rw [h1]
        _ < ρ := by linarith
    exact hwz (hinj w (by simpa [Metric.mem_ball, dist_eq_norm] using hwρ)
      z (by simpa [Metric.mem_ball, dist_eq_norm] using hzρ) (hε' hwε))
  exact Work.Parab.basin_forward hzan hnc hz

/-! ## The merging lemma -/

/-- If two basin points with the same `Φ`-value have all their iterates in the basin, then
their orbits merge (the two points are the same up to the orbit relation). -/
theorem merge_of_Phi_eq (d : MandelDim.ParabData f₀ D₀)
    (h0 : (0 : ℂ) ∉ MandelDim.ParabolicBasin f₀ D₀)
    {z z' : ℂ} (hz : z ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hz' : z' ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hiter : ∀ j, (f₀^[j]) z ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hiter' : ∀ j, (f₀^[j]) z' ∈ MandelDim.ParabolicBasin f₀ D₀)
    (heq : d.Φ z = d.Φ z') :
    ∃ m, (f₀^[m]) z = (f₀^[m]) z' := by
  have hne : ∀ j, (f₀^[j]) z ≠ 0 := fun j h => h0 (h ▸ hiter j)
  have hne' : ∀ j, (f₀^[j]) z' ≠ 0 := fun j h => h0 (h ▸ hiter' j)
  obtain ⟨n, hn⟩ := d.basin_enter z hz hne
  obtain ⟨n', hn'⟩ := d.basin_enter z' hz' hne'
  have hval : ∀ j, d.Φ ((f₀^[j]) z) = d.Φ z + (j : ℂ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', d.Φ_abel _ (hiter j), ih]; push_cast; ring
  have hval' : ∀ j, d.Φ ((f₀^[j]) z') = d.Φ z' + (j : ℂ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', d.Φ_abel _ (hiter' j), ih]; push_cast; ring
  rcases le_or_gt n n' with hle | hlt
  · have hstep : d.Φ ((f₀^[n']) z) = d.Φ ((f₀^[n']) z') := by
      rw [hval n', hval' n', heq]
    have hmem1 : (f₀^[n']) z' ∈ d.Ωp := hn'
    have hmem2 : (f₀^[n']) z ∈ d.Ωp := by
      have : (f₀^[n']) z = (f₀^[n' - n]) ((f₀^[n]) z) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
      rw [this]
      exact d.Ωp_maps.iterate _ hn
    exact ⟨n', d.Φ_inj hmem2 hmem1 hstep⟩
  · have hstep : d.Φ ((f₀^[n]) z) = d.Φ ((f₀^[n]) z') := by
      rw [hval n, hval' n, heq]
    have hmem1 : (f₀^[n]) z ∈ d.Ωp := hn
    have hmem2 : (f₀^[n]) z' ∈ d.Ωp := by
      have : (f₀^[n]) z' = (f₀^[n - n']) ((f₀^[n']) z') := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hlt)]
      rw [this]
      exact d.Ωp_maps.iterate _ hn'
    exact ⟨n, d.Φ_inj hmem1 hmem2 hstep⟩

/-! ## The main theorem -/

theorem limitCoord_plus_exists {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ ξ₁ : ℝ, ξ ≤ ξ₁ →
      ∃ Φ : ℂ → ℂ,
        MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Φ
          (MandelDim.Qreg (some (ξ₁ : ℂ)) none) ∧
        (∀ u ∈ MandelDim.Qreg (some (ξ₁ : ℂ)) none,
          MandelDim.tau0 u ∈ MandelDim.ParabolicBasin f₀ D₀ →
            Φ u = d.Φ (MandelDim.tau0 u)) := by
  classical
  obtain ⟨h, a, r, A, A', hb, hball⟩ := Work.Parab.exists_parabolicBounds_of_germ hd
  have hrpos : 0 < r := hb.hr
  obtain ⟨Ginv, δi, hδipos, -, -, -, -, hGinvL, -⟩ := Work.Parab.exists_local_inverse_ball hd
  have hinj : ∀ z ∈ ball 0 δi, ∀ z' ∈ ball 0 δi, f₀ z = f₀ z' → z = z' := by
    intro z hz z' hz' h
    rw [← hGinvL z hz, h, hGinvL z' hz']
  obtain ⟨ρc, hρcpos, hcone⟩ := cone_subset_basin hd
  have h0 : (0 : ℂ) ∉ MandelDim.ParabolicBasin f₀ D₀ :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hd
  obtain ⟨ξNT, hξNTpos, hNT, -, -, -⟩ := nearTranslation_F0 hd
  set ξ : ℝ := max ξNT (max (max (2 / ρc) (2 / δi)) (max (max (8 / r) 4) 1)) with hξdef
  have hξNT : ξNT ≤ ξ := le_max_left _ _
  have hmid : max (max (2 / ρc) (2 / δi)) (max (max (8 / r) 4) 1) ≤ ξ := le_max_right _ _
  have hA : max (2 / ρc) (2 / δi) ≤
      max (max (2 / ρc) (2 / δi)) (max (max (8 / r) 4) 1) := le_max_left _ _
  have hB : max (max (8 / r) 4) 1 ≤
      max (max (2 / ρc) (2 / δi)) (max (max (8 / r) 4) 1) := le_max_right _ _
  have hC : max (8 / r) 4 ≤ max (max (8 / r) 4) 1 := le_max_left _ _
  have hξρc : 2 / ρc ≤ ξ := le_trans (le_max_left _ _) (le_trans hA hmid)
  have hξδi : 2 / δi ≤ ξ := le_trans (le_max_right _ _) (le_trans hA hmid)
  have hξ4r : 8 / r ≤ ξ := le_trans (le_max_left _ _) (le_trans hC (le_trans hB hmid))
  have hξ4 : (4 : ℝ) ≤ ξ := le_trans (le_max_right _ _) (le_trans hC (le_trans hB hmid))
  have hξ1 : (1 : ℝ) ≤ ξ := le_trans (le_max_right _ _) (le_trans hB hmid)
  have hξpos : 0 < ξ := lt_of_lt_of_le zero_lt_one hξ1
  refine ⟨ξ, hξpos, fun ξ₁ hξ₁ => ?_⟩
  have hξ₁pos : 0 < ξ₁ := lt_of_lt_of_le hξpos hξ₁
  set Q : Set ℂ := MandelDim.Qreg (some (ξ₁ : ℂ)) none with hQ
  have hQopen : IsOpen Q := isOpen_Qreg_cone
  have hsub : Q ⊆ MandelDim.Qreg (some (ξNT : ℂ)) none := fun z hz => Qreg_cone_mono (le_trans hξNT hξ₁) hz
  have hstep : ∀ z ∈ Q, ‖tauConj f₀ z - (z + 1)‖ ≤ 1 / 32 := fun z hz => (hNT.2 z (hsub hz)).1
  have hconf : ∀ w ∈ Q, ∀ j, ‖MandelDim.tau0 ((tauConj f₀)^[j] w)‖ < 2 / ξ₁ :=
    fun w hw j => norm_tau0_iterate_lt hξ₁pos hstep hw j
  have hQiter : ∀ w ∈ Q, ∀ j, (tauConj f₀)^[j] w ∈ Q :=
    fun w hw j => (G_iterate_spec hstep hw j).1
  have hGne : ∀ w ∈ Q, ∀ j, (tauConj f₀)^[j] w ≠ 0 := by
    intro w hw j
    exact norm_pos_iff.mp (by
      have := NTF0.norm_gt_of_mem_right (hQiter w hw j)
      linarith)
  have h2δi_le : 2 / ξ₁ ≤ δi := by
    have h1 : 2 / δi ≤ ξ₁ := le_trans hξδi hξ₁
    rw [div_le_iff₀ hδipos] at h1
    rw [div_le_iff₀ hξ₁pos]
    nlinarith [h1]
  have h2ρc_le : 2 / ξ₁ ≤ ρc := by
    have h1 : 2 / ρc ≤ ξ₁ := le_trans hξρc hξ₁
    rw [div_le_iff₀ hρcpos] at h1
    rw [div_le_iff₀ hξ₁pos]
    nlinarith [h1]
  -- no other zeros near 0
  have hzero : ∀ z : ℂ, ‖z‖ < 2 / ξ₁ → f₀ z = 0 → z = 0 := by
    intro z hz hf
    have hzr2 : 2 / ξ₁ < r / 2 := by
      have h5 : 8 ≤ ξ₁ * r := by
        have h6 : 8 / r ≤ ξ₁ := le_trans hξ4r hξ₁
        rw [div_le_iff₀ hb.hr] at h6
        linarith
      have h6 : 2 / ξ₁ ≤ r / 4 := by
        rw [div_le_iff₀ hξ₁pos]
        nlinarith [h5]
      linarith [h6, hrpos]
    have hzr : z ∈ ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    rcases eq_or_ne z 0 with rfl | hz0
    · rfl
    · exfalso
      have hfz : f₀ z = z * (1 + z * h z) := by rw [hb.f_eq z hzr]; ring
      rw [hfz, mul_eq_zero] at hf
      rcases hf with hf | hf
      · exact hz0 hf
      · have hbnd : ‖z * h z‖ < 1 := by
          rw [norm_mul]
          have h1 := hb.h_bound z hzr
          have h2 : ‖z‖ < 1 / 2 := by
            have h3 : 2 / ξ₁ ≤ 1 / 2 := by
              rw [div_le_iff₀ hξ₁pos]
              linarith [hξ4, hξ₁]
            linarith
          nlinarith [h1, norm_nonneg z, norm_nonneg (h z)]
        have h1 : z * h z = -1 := by linear_combination hf
        rw [h1] at hbnd
        norm_num at hbnd
  -- the orbit relation
  have horbit : ∀ w ∈ Q, ∀ j,
      MandelDim.tau0 ((tauConj f₀)^[j] w) = (f₀^[j]) (MandelDim.tau0 w) :=
    fun w hw j => tau0_iterate_eq (ξ := ξ₁) (fun _ => rfl) hzero (hGne w hw) (hconf w hw) j
  -- every orbit reaches the basin
  have hgoodExists : ∀ u ∈ Q, ∃ j : ℕ,
      MandelDim.tau0 ((tauConj f₀)^[j] u) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
    intro u hu
    obtain ⟨j, hj1, hj2⟩ : ∃ j : ℕ, |u.im| - u.re < (j : ℝ) * (15 / 16) ∧
        1 / ρc - u.re < (j : ℝ) * (31 / 32) := by
      obtain ⟨j, hj⟩ := exists_nat_gt (max ((|u.im| - u.re) * (16 / 15) + 1)
        ((1 / ρc - u.re) * (32 / 31) + 1))
      refine ⟨j, ?_, ?_⟩
      · have := le_max_left ((|u.im| - u.re) * (16 / 15) + 1) ((1 / ρc - u.re) * (32 / 31) + 1)
        nlinarith [hj, this]
      · have := le_max_right ((|u.im| - u.re) * (16 / 15) + 1) ((1 / ρc - u.re) * (32 / 31) + 1)
        nlinarith [hj, this]
    obtain ⟨hmem, hre, him⟩ := G_iterate_spec hstep hu j
    have hre' : ((tauConj f₀)^[j] u).re > |((tauConj f₀)^[j] u).im| := by
      have h1 : |u.im| + (j : ℝ) * (1 / 32) < u.re + (j : ℝ) * (31 / 32) := by
        nlinarith [hj1]
      have h2 : u.re + (j : ℝ) * (31 / 32) ≤ ((tauConj f₀)^[j] u).re := hre
      have h3 : |((tauConj f₀)^[j] u).im| ≤ |u.im| + (j : ℝ) * (1 / 32) := him
      linarith
    have hbig : ((tauConj f₀)^[j] u).re > 1 / ρc := by
      have h2 : 1 / ρc < u.re + (j : ℝ) * (31 / 32) := by nlinarith [hj2]
      linarith
    have hnorm : 1 / ρc < ‖((tauConj f₀)^[j] u)‖ :=
      lt_of_lt_of_le hbig (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
    have hz1 : -(MandelDim.tau0 ((tauConj f₀)^[j] u)).re >
        |(MandelDim.tau0 ((tauConj f₀)^[j] u)).im| := by
      have hw : (0 : ℝ) < ‖((tauConj f₀)^[j] u)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (hGne u hu j)) 2
      rw [Work.Pert.tau0_re, Work.Pert.tau0_im, neg_div, neg_neg, abs_div,
        abs_of_nonneg hw.le]
      exact div_lt_div_of_pos_right hre' hw
    have hz2 : ‖MandelDim.tau0 ((tauConj f₀)^[j] u)‖ < ρc := by
      have hw : (0 : ℝ) < ‖((tauConj f₀)^[j] u)‖ := norm_pos_iff.mpr (hGne u hu j)
      rw [NTF0.norm_tau0, div_lt_iff₀ hw]
      have h := hnorm
      rw [div_lt_iff₀ hρcpos] at h
      nlinarith [h]
    exact ⟨j, hcone _ hz2 hz1⟩
  -- levels
  let J : ℂ → ℕ := fun u => if h : u ∈ Q then Classical.choose (hgoodExists u h) else 0
  have hJ : ∀ u ∈ Q, MandelDim.tau0 ((tauConj f₀)^[J u] u) ∈
      MandelDim.ParabolicBasin f₀ D₀ := by
    intro u hu
    simp only [J, dif_pos hu]
    exact Classical.choose_spec (hgoodExists u hu)
  have hgoodStep : ∀ u ∈ Q, ∀ i : ℕ,
      MandelDim.tau0 ((tauConj f₀)^[i] u) ∈ MandelDim.ParabolicBasin f₀ D₀ →
      MandelDim.tau0 ((tauConj f₀)^[i + 1] u) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
    intro u hu i hi
    have hrel : MandelDim.tau0 ((tauConj f₀)^[i + 1] u) =
        f₀ (MandelDim.tau0 ((tauConj f₀)^[i] u)) := by
      rw [horbit u hu (i + 1), horbit u hu i, Function.iterate_succ_apply']
    rw [hrel]
    exact basin_forward_tiny hinj hd _ hi (lt_of_lt_of_le (hconf u hu i) h2δi_le)
  have htail : ∀ u ∈ Q, ∀ m k : ℕ,
      MandelDim.tau0 ((tauConj f₀)^[m] u) ∈ MandelDim.ParabolicBasin f₀ D₀ → m ≤ k →
      MandelDim.tau0 ((tauConj f₀)^[k] u) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
    intro u hu m k hm hmk
    obtain ⟨dd, rfl⟩ : ∃ dd, k = m + dd := ⟨k - m, by omega⟩
    have hclimb : ∀ dd : ℕ, MandelDim.tau0 ((tauConj f₀)^[m + dd] u) ∈
        MandelDim.ParabolicBasin f₀ D₀ := by
      intro dd
      induction dd with
      | zero => simpa using hm
      | succ dd ih =>
        rw [show m + (dd + 1) = (m + dd) + 1 by omega]
        exact hgoodStep u hu (m + dd) ih
    exact hclimb dd
  -- telescoping
  have hvalStep : ∀ u ∈ Q, ∀ i : ℕ,
      MandelDim.tau0 ((tauConj f₀)^[i] u) ∈ MandelDim.ParabolicBasin f₀ D₀ →
      MandelDim.tau0 ((tauConj f₀)^[i + 1] u) ∈ MandelDim.ParabolicBasin f₀ D₀ →
      d.Φ (MandelDim.tau0 ((tauConj f₀)^[i + 1] u)) - ((i + 1 : ℕ) : ℂ) =
        d.Φ (MandelDim.tau0 ((tauConj f₀)^[i] u)) - (i : ℂ) := by
    intro u hu i hi _
    have hrel : MandelDim.tau0 ((tauConj f₀)^[i + 1] u) =
        f₀ (MandelDim.tau0 ((tauConj f₀)^[i] u)) := by
      rw [horbit u hu (i + 1), horbit u hu i, Function.iterate_succ_apply']
    rw [hrel, d.Φ_abel _ hi]
    push_cast
    ring
  have hval : ∀ u ∈ Q, ∀ i j : ℕ, i ≤ j →
      (∀ k : ℕ, i ≤ k → k ≤ j →
        MandelDim.tau0 ((tauConj f₀)^[k] u) ∈ MandelDim.ParabolicBasin f₀ D₀) →
      d.Φ (MandelDim.tau0 ((tauConj f₀)^[i] u)) - (i : ℂ) =
        d.Φ (MandelDim.tau0 ((tauConj f₀)^[j] u)) - (j : ℂ) := by
    intro u hu i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; ring
    | succ k hik ih =>
      intro hgood
      have h1 := ih (fun k' h1 h2 => hgood k' h1 (by omega))
      have h2 := hvalStep u hu k (hgood k (by omega) (by omega)) (hgood (k + 1) (by omega) le_rfl)
      rw [h1, h2]
  have hval2 : ∀ u ∈ Q, ∀ i j : ℕ,
      MandelDim.tau0 ((tauConj f₀)^[i] u) ∈ MandelDim.ParabolicBasin f₀ D₀ →
      MandelDim.tau0 ((tauConj f₀)^[j] u) ∈ MandelDim.ParabolicBasin f₀ D₀ →
      d.Φ (MandelDim.tau0 ((tauConj f₀)^[i] u)) - (i : ℂ) =
        d.Φ (MandelDim.tau0 ((tauConj f₀)^[j] u)) - (j : ℂ) := by
    intro u hu i j hi hj
    rcases le_or_gt i j with h | h
    · exact hval u hu i j h (fun k h1 _ => htail u hu i k hi h1)
    · exact (hval u hu j i (le_of_lt h) (fun k h1 _ => htail u hu j k hj h1)).symm
  -- the coordinate
  let Phi : ℂ → ℂ := fun u => d.Φ (MandelDim.tau0 ((tauConj f₀)^[J u] u)) - (J u : ℂ)
  have hPhiJ : ∀ u ∈ Q, Phi u =
      d.Φ (MandelDim.tau0 ((tauConj f₀)^[J u] u)) - (J u : ℂ) := fun _ _ => rfl
  have hagree : ∀ u ∈ Q, MandelDim.tau0 u ∈ MandelDim.ParabolicBasin f₀ D₀ →
      Phi u = d.Φ (MandelDim.tau0 u) := by
    intro u hu huB
    have h2 := hval2 u hu (J u) 0 (hJ u hu) huB
    simpa [Phi] using h2
  refine ⟨Phi, ⟨?_, ?_, ?_⟩, hagree⟩
  · -- holomorphy
    intro u₀ hu₀
    set j₀ : ℕ := J u₀ with hj₀
    have hgood₀ : MandelDim.tau0 ((tauConj f₀)^[j₀] u₀) ∈
        MandelDim.ParabolicBasin f₀ D₀ := hJ u₀ hu₀
    have hdiffG : DifferentiableOn ℂ (tauConj f₀) Q := hNT.1.mono hsub
    have hdiff_iter : DifferentiableOn ℂ (fun u => (tauConj f₀)^[j₀] u) Q :=
      (hdiffG.iterate (fun u hu => hQiter u hu 1)) j₀
    have hdiff1 : DifferentiableAt ℂ (fun u => (tauConj f₀)^[j₀] u) u₀ :=
      hdiff_iter.differentiableAt (hQopen.mem_nhds hu₀)
    have hne : (tauConj f₀)^[j₀] u₀ ≠ 0 := hGne u₀ hu₀ j₀
    have hdiff2 : DifferentiableAt ℂ (fun u => MandelDim.tau0 ((tauConj f₀)^[j₀] u)) u₀ :=
      (NTF0.differentiableAt_tau0 hne).comp u₀ hdiff1
    have hdiff3 : DifferentiableAt ℂ d.Φ (MandelDim.tau0 ((tauConj f₀)^[j₀] u₀)) :=
      d.Φ_holo.differentiableAt ((isOpen_basin f₀ D₀).mem_nhds hgood₀)
    have hcand : DifferentiableAt ℂ
        (fun u => d.Φ (MandelDim.tau0 ((tauConj f₀)^[j₀] u)) - (j₀ : ℂ)) u₀ :=
      (hdiff3.comp u₀ hdiff2).sub_const _
    have hev : Phi =ᶠ[𝓝[Q] u₀]
        (fun u => d.Φ (MandelDim.tau0 ((tauConj f₀)^[j₀] u)) - (j₀ : ℂ)) := by
      have hBev : ∀ᶠ u in 𝓝[Q] u₀,
          MandelDim.tau0 ((tauConj f₀)^[j₀] u) ∈ MandelDim.ParabolicBasin f₀ D₀ :=
        (hdiff2.continuousAt.eventually ((isOpen_basin f₀ D₀).mem_nhds hgood₀)).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hBev] with u huQ huB
      exact hval2 u huQ (J u) j₀ (hJ u huQ) huB
    have hpt : (fun u => d.Φ (MandelDim.tau0 ((tauConj f₀)^[j₀] u)) - (j₀ : ℂ)) u₀ = Phi u₀ := by
      show _ = Phi u₀
      rw [show Phi u₀ = d.Φ (MandelDim.tau0 ((tauConj f₀)^[J u₀] u₀)) - (J u₀ : ℂ) from rfl, hj₀]
    exact hcand.differentiableWithinAt.congr_of_eventuallyEq hev hpt
  · -- injectivity
    have hmemδi : ∀ w ∈ Q, MandelDim.tau0 w ∈ ball 0 δi := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le (hconf w hw 0) h2δi_le
    have hGstepInj : ∀ w ∈ Q, ∀ w' ∈ Q, tauConj f₀ w = tauConj f₀ w' → w = w' := by
      intro w hw w' hw' hww'
      have h1 : f₀ (MandelDim.tau0 w) = f₀ (MandelDim.tau0 w') := tau0_injective hww'
      exact tau0_injective (hinj _ (hmemδi w hw) _ (hmemδi w' hw') h1)
    have hwalkback : ∀ u ∈ Q, ∀ u' ∈ Q, ∀ m : ℕ,
        (tauConj f₀)^[m] u = (tauConj f₀)^[m] u' → u = u' := by
      intro u hu u' hu' m
      induction m with
      | zero => intro h; simpa using h
      | succ m ih =>
        intro h
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
        exact ih (hGstepInj _ (hQiter u hu m) _ (hQiter u' hu' m) h)
    have hInjS : Set.InjOn d.Φ
        (MandelDim.tau0 '' Q ∩ MandelDim.ParabolicBasin f₀ D₀) := by
      rintro z ⟨⟨u, hu, rfl⟩, hzB⟩ z' ⟨⟨u', hu', rfl⟩, hzB'⟩ hzeq
      have hiterB : ∀ j, MandelDim.tau0 ((tauConj f₀)^[j] u) ∈
          MandelDim.ParabolicBasin f₀ D₀ := by
        intro j
        induction j with
        | zero => simpa using hzB
        | succ j ih =>
          have hrel : MandelDim.tau0 ((tauConj f₀)^[j + 1] u) =
              f₀ (MandelDim.tau0 ((tauConj f₀)^[j] u)) := by
            rw [horbit u hu (j + 1), horbit u hu j, Function.iterate_succ_apply']
          rw [hrel]
          exact basin_forward_tiny hinj hd _ ih (lt_of_lt_of_le (hconf u hu j) h2δi_le)
      have hiterB' : ∀ j, MandelDim.tau0 ((tauConj f₀)^[j] u') ∈
          MandelDim.ParabolicBasin f₀ D₀ := by
        intro j
        induction j with
        | zero => simpa using hzB'
        | succ j ih =>
          have hrel : MandelDim.tau0 ((tauConj f₀)^[j + 1] u') =
              f₀ (MandelDim.tau0 ((tauConj f₀)^[j] u')) := by
            rw [horbit u' hu' (j + 1), horbit u' hu' j, Function.iterate_succ_apply']
          rw [hrel]
          exact basin_forward_tiny hinj hd _ ih (lt_of_lt_of_le (hconf u' hu' j) h2δi_le)
      have hfiter : ∀ j, (f₀^[j]) (MandelDim.tau0 u) ∈
          MandelDim.ParabolicBasin f₀ D₀ := fun j => by
        rw [← horbit u hu j]; exact hiterB j
      have hfiter' : ∀ j, (f₀^[j]) (MandelDim.tau0 u') ∈
          MandelDim.ParabolicBasin f₀ D₀ := fun j => by
        rw [← horbit u' hu' j]; exact hiterB' j
      obtain ⟨m, hm⟩ := merge_of_Phi_eq d h0 hzB hzB' hfiter hfiter' hzeq
      have hGm : (tauConj f₀)^[m] u = (tauConj f₀)^[m] u' := by
        apply tau0_injective
        rw [horbit u hu m, horbit u' hu' m]
        exact hm
      rw [hwalkback u hu u' hu' m hGm]
    intro u hu u' hu' heq
    set m : ℕ := max (J u) (J u') with hmdef
    have hm1 : J u ≤ m := le_max_left _ _
    have hm2 : J u' ≤ m := le_max_right _ _
    have hgu : MandelDim.tau0 ((tauConj f₀)^[m] u) ∈
        MandelDim.ParabolicBasin f₀ D₀ := htail u hu (J u) m (hJ u hu) hm1
    have hgu' : MandelDim.tau0 ((tauConj f₀)^[m] u') ∈
        MandelDim.ParabolicBasin f₀ D₀ := htail u' hu' (J u') m (hJ u' hu') hm2
    have h1 : Phi u = d.Φ (MandelDim.tau0 ((tauConj f₀)^[m] u)) - (m : ℂ) := by
      rw [hPhiJ u hu]
      exact hval2 u hu (J u) m (hJ u hu) hgu
    have h2 : Phi u' = d.Φ (MandelDim.tau0 ((tauConj f₀)^[m] u')) - (m : ℂ) := by
      rw [hPhiJ u' hu']
      exact hval2 u' hu' (J u') m (hJ u' hu') hgu'
    have hzeq : d.Φ (MandelDim.tau0 ((tauConj f₀)^[m] u)) =
        d.Φ (MandelDim.tau0 ((tauConj f₀)^[m] u')) := by
      have h3 := heq
      rw [h1, h2] at h3
      have h4 : d.Φ (MandelDim.tau0 ((tauConj f₀)^[m] u)) + (-(m : ℂ)) =
          d.Φ (MandelDim.tau0 ((tauConj f₀)^[m] u')) + (-(m : ℂ)) := by
        linear_combination h3
      exact add_right_cancel h4
    have hS : MandelDim.tau0 ((tauConj f₀)^[m] u) ∈
        MandelDim.tau0 '' Q ∩ MandelDim.ParabolicBasin f₀ D₀ :=
      ⟨⟨_, hQiter u hu m, rfl⟩, hgu⟩
    have hS' : MandelDim.tau0 ((tauConj f₀)^[m] u') ∈
        MandelDim.tau0 '' Q ∩ MandelDim.ParabolicBasin f₀ D₀ :=
      ⟨⟨_, hQiter u' hu' m, rfl⟩, hgu'⟩
    have hz := hInjS hS hS' hzeq
    have hGm : (tauConj f₀)^[m] u = (tauConj f₀)^[m] u' := tau0_injective hz
    exact hwalkback u hu u' hu' m hGm
  · -- the Abel equation
    intro u hu _
    have hgood' : MandelDim.tau0 ((tauConj f₀)^[J (tauConj f₀ u) + 1] u) ∈
        MandelDim.ParabolicBasin f₀ D₀ := by
      rw [show (tauConj f₀)^[J (tauConj f₀ u) + 1] u =
          (tauConj f₀)^[J (tauConj f₀ u)] (tauConj f₀ u) from
        Function.iterate_succ_apply ..]
      exact hJ (tauConj f₀ u) (hQiter u hu 1)
    have hkey := hval2 u hu (J u) (J (tauConj f₀ u) + 1) (hJ u hu) hgood'
    have hB : Phi (tauConj f₀ u) =
        (d.Φ (MandelDim.tau0 ((tauConj f₀)^[J (tauConj f₀ u) + 1] u)) -
          ((J (tauConj f₀ u) + 1 : ℕ) : ℂ)) + 1 := by
      rw [hPhiJ (tauConj f₀ u) (hQiter u hu 1),
        show (tauConj f₀)^[J (tauConj f₀ u)] (tauConj f₀ u) =
          (tauConj f₀)^[J (tauConj f₀ u) + 1] u from
        Function.iterate_succ_apply ..]
      push_cast
      ring
    change Phi (tauConj f₀ u) = Phi u + 1
    have hval1 : Phi (tauConj f₀ u) =
        (d.Φ (MandelDim.tau0 ((tauConj f₀)^[J u] u)) - (J u : ℂ)) + 1 := by
      rw [hB]
      exact congrArg (· + 1) hkey.symm
    have hval2' : Phi u = d.Φ (MandelDim.tau0 ((tauConj f₀)^[J u] u)) - (J u : ℂ) :=
      hPhiJ u hu
    rw [hval1, hval2']

end

end Work.Pert
