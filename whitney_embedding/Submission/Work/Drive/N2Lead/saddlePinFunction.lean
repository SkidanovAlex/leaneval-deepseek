import Mathlib
import Submission.Work.Drive.N2.windowDatum

/-!
# The pin function `θ` of the saddle packet

`NOTES_LEAD_saddlePacket.md` §3.3 item 3.  The engine
`Work.Drive.N2Lead.saddleWindow_of_packet_band_off` consumes three rows of the pin function:

* `hθ01 : ∀ x, 0 ≤ θ x ∧ θ x ≤ 1`;
* `hApin` and `hAoff` (the rows relating `θ` to the packet's picture `A`);
* `hfootFrint : frontier points of the region have their foot in `interior (θ ⁻¹' {1})`.

This file provides the function itself and its pointwise rows:

  `θ x = pinBeta m (|Im (Z x)²|) * pinChi (‖Z x‖²)`  on the chart source, `0` off it,

with `pinBeta m w = ST ((2 - |w|) / (2 - m))` (so `pinBeta m w = 1 ↔ |w| ≤ m` for `m < 2`) and
`pinChi σ = 1 - ST ((σ - 4)/5)` (so `pinChi σ = 1 ↔ σ ≤ 4`).  On the anchor level of the saddle
window the norm bound `‖Z x‖² ≤ √(η²+m²) < 4` holds automatically, so there
`θ x = 1 ↔ |Im (Z x)²| ≤ m` — the pin.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

noncomputable section

/-- The pin profile: `1` on `|w| ≤ m` and `0` on `|w| ≥ 2`. -/
def pinBeta (m w : ℝ) : ℝ := Real.smoothTransition ((2 - |w|) / (2 - m))

/-- The norm profile: `1` on `[0,4]` and `0` on `[9,∞)`. -/
def pinChi (σ : ℝ) : ℝ := 1 - Real.smoothTransition ((σ - 4) / 5)

lemma pinBeta_nonneg (m w : ℝ) : 0 ≤ pinBeta m w := Real.smoothTransition.nonneg _

lemma pinBeta_le_one (m w : ℝ) : pinBeta m w ≤ 1 := Real.smoothTransition.le_one _

lemma pinChi_nonneg (σ : ℝ) : 0 ≤ pinChi σ := by
  have h := Real.smoothTransition.le_one ((σ - 4) / 5)
  simp only [pinChi]
  linarith

lemma pinChi_le_one (σ : ℝ) : pinChi σ ≤ 1 := by
  have h := Real.smoothTransition.nonneg ((σ - 4) / 5)
  simp only [pinChi]
  linarith

lemma pinChi_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pinChi := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => (σ - 4) / 5) := by fun_prop
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp h1)

lemma pinBeta_eq_one_iff {m : ℝ} (hm : m < 2) (w : ℝ) : pinBeta m w = 1 ↔ |w| ≤ m := by
  constructor
  · intro h
    by_contra hw
    have hw' : m < |w| := not_le.mp hw
    have hlt : (2 - |w|) / (2 - m) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    have := Real.smoothTransition.lt_one_of_lt_one hlt
    simp only [pinBeta] at h
    linarith
  · intro hw
    have hle : 1 ≤ (2 - |w|) / (2 - m) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    simp only [pinBeta]
    exact Real.smoothTransition.one_of_one_le hle

lemma pinChi_eq_one_iff (σ : ℝ) : pinChi σ = 1 ↔ σ ≤ 4 := by
  constructor
  · intro h
    by_contra hσ
    have hσ' : 4 < σ := not_le.mp hσ
    have hpos : 0 < (σ - 4) / 5 := by linarith
    have := Real.smoothTransition.pos_of_pos hpos
    simp only [pinChi] at h
    linarith
  · intro hσ
    have h0 : (σ - 4) / 5 ≤ 0 := by linarith
    simp only [pinChi, Real.smoothTransition.zero_of_nonpos h0, sub_zero]

section Datum

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The pin function of the saddle packet**: on the marked chart,
`θ x = pinBeta m (|Im (Z x)²|) · pinChi (‖Z x‖²)`, and `0` off the chart source. -/
def pinTheta {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (Z : M → ℂ) (m : ℝ) :
    M → ℝ :=
  fun x => if x ∈ (D.φ D.j).source then pinBeta m (|((Z x) ^ 2).im|) * pinChi (‖Z x‖ ^ 2) else 0

lemma pinTheta_apply_of_mem {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} {x : M} (hx : x ∈ (D.φ D.j).source) :
    pinTheta D Z m x = pinBeta m (|((Z x) ^ 2).im|) * pinChi (‖Z x‖ ^ 2) := if_pos hx

lemma pinTheta_apply_of_notMem {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} {x : M} (hx : x ∉ (D.φ D.j).source) :
    pinTheta D Z m x = 0 := if_neg hx

/-- **The range row `hθ01`.** -/
lemma pinTheta_mem_Icc {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} (x : M) : 0 ≤ pinTheta D Z m x ∧ pinTheta D Z m x ≤ 1 := by
  by_cases hx : x ∈ (D.φ D.j).source
  · rw [pinTheta_apply_of_mem D (Z := Z) (m := m) hx]
    have h1 := pinBeta_nonneg m (|((Z x) ^ 2).im|)
    have h2 := pinBeta_le_one m (|((Z x) ^ 2).im|)
    have h3 := pinChi_nonneg (‖Z x‖ ^ 2)
    have h4 := pinChi_le_one (‖Z x‖ ^ 2)
    refine ⟨mul_nonneg h1 h3, ?_⟩
    have := mul_le_mul h2 h4 h3 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  · rw [pinTheta_apply_of_notMem D (Z := Z) (m := m) hx]
    exact ⟨le_rfl, zero_le_one⟩

/-- **The pin condition**: on the chart source, `θ x = 1` iff `|Im (Z x)²| ≤ m` and
`‖Z x‖² ≤ 4` (for `m < 2`). -/
lemma pinTheta_eq_one_iff {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} (hm : m < 2) {x : M} (hx : x ∈ (D.φ D.j).source) :
    pinTheta D Z m x = 1 ↔ |((Z x) ^ 2).im| ≤ m ∧ ‖Z x‖ ^ 2 ≤ 4 := by
  have hprod := pinTheta_apply_of_mem D (Z := Z) (m := m) hx
  rw [hprod]
  have hb1 := pinBeta_nonneg m (|((Z x) ^ 2).im|)
  have hb2 := pinBeta_le_one m (|((Z x) ^ 2).im|)
  have hc1 := pinChi_nonneg (‖Z x‖ ^ 2)
  have hc2 := pinChi_le_one (‖Z x‖ ^ 2)
  constructor
  · intro h
    have hb : pinBeta m (|((Z x) ^ 2).im|) = 1 := by
      by_contra hne
      have hlt : pinBeta m (|((Z x) ^ 2).im|) < 1 := lt_of_le_of_ne hb2 hne
      have hpos : 0 < pinBeta m (|((Z x) ^ 2).im|) * pinChi (‖Z x‖ ^ 2) := by rw [h]; norm_num
      nlinarith [hc1, hc2]
    have hc : pinChi (‖Z x‖ ^ 2) = 1 := by
      by_contra hne
      have hlt : pinChi (‖Z x‖ ^ 2) < 1 := lt_of_le_of_ne hc2 hne
      have hpos : 0 < pinBeta m (|((Z x) ^ 2).im|) * pinChi (‖Z x‖ ^ 2) := by rw [h]; norm_num
      nlinarith [hb1, hb2]
    have hbm : |((Z x) ^ 2).im| ≤ m := by
      have := (pinBeta_eq_one_iff hm |((Z x) ^ 2).im|).mp hb
      rwa [abs_abs] at this
    exact ⟨hbm, (pinChi_eq_one_iff _).mp hc⟩
  · rintro ⟨h1, h2⟩
    have h1' : |(|((Z x) ^ 2).im|)| ≤ m := by rwa [abs_abs]
    have hchi : pinChi (‖Z x‖ ^ 2) = 1 := (pinChi_eq_one_iff _).mpr h2
    have hbeta : pinBeta m (|((Z x) ^ 2).im|) = 1 := (pinBeta_eq_one_iff hm _).mpr h1'
    rw [hbeta, hchi, mul_one]

/-- The pin function vanishes off the chart source, so its support is inside the chart. -/
lemma pinTheta_eq_zero_of_notMem {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} {x : M} (hx : x ∉ (D.φ D.j).source) :
    pinTheta D Z m x = 0 := pinTheta_apply_of_notMem D (Z := Z) (m := m) hx

lemma tsupport_pinTheta_subset {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} :
    Function.support (pinTheta D Z m) ⊆ (D.φ D.j).source := by
  intro x hx
  by_contra hx'
  exact hx (pinTheta_eq_zero_of_notMem D hx')

/-- **The open set of strict pin points.**  Where `|Im (Z ·)²| < m` and `‖Z ·‖² < 4` strictly, the
pin function equals `1` on a whole neighbourhood. -/
lemma pinTheta_eventuallyEq_one {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {m : ℝ} (hm : m < 2)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    {x : M} (hx : x ∈ (D.φ D.j).source)
    (h1 : |((Z x) ^ 2).im| < m) (h2 : ‖Z x‖ ^ 2 < 4) :
    ∀ᶠ y in 𝓝 x, pinTheta D Z m y = 1 := by
  have hZc : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hx)).continuousAt
  have hsqc : ContinuousAt (fun y : M => (Z y) ^ 2) x := hZc.pow 2
  have himc : ContinuousAt (fun y : M => ((Z y) ^ 2).im) x :=
    Complex.continuous_im.continuousAt.comp hsqc
  have habsc : ContinuousAt (fun y : M => |((Z y) ^ 2).im|) x := himc.abs
  have hnormc : ContinuousAt (fun y : M => ‖Z y‖ ^ 2) x := (continuous_norm.continuousAt.comp hZc).pow 2
  have hsrc : ∀ᶠ y in 𝓝 x, y ∈ (D.φ D.j).source :=
    (D.φ D.j).open_source.mem_nhds hx
  have hlt1 : ∀ᶠ y in 𝓝 x, |((Z y) ^ 2).im| < m :=
    habsc.preimage_mem_nhds (isOpen_Iio.mem_nhds h1)
  have hlt2 : ∀ᶠ y in 𝓝 x, ‖Z y‖ ^ 2 < 4 :=
    hnormc.preimage_mem_nhds (isOpen_Iio.mem_nhds h2)
  filter_upwards [hsrc, hlt1, hlt2] with y hys hy1 hy2
  rw [pinTheta_apply_of_mem D hys]
  have hb : pinBeta m (|((Z y) ^ 2).im|) = 1 := by
    rw [pinBeta_eq_one_iff hm, abs_abs]
    exact le_of_lt hy1
  have hc : pinChi (‖Z y‖ ^ 2) = 1 := by
    rw [pinChi_eq_one_iff]
    exact le_of_lt hy2
  rw [hb, hc, mul_one]

end Datum

end

end Work.Drive.N2Lead
