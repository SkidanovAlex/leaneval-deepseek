import Mathlib
import Submission.Work.Parab.CoordData
import Submission.Work.Parab.Setup
import Submission.Work.Parab.leftCoord.escC
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.psiC_asymptotic
import Submission.Work.Parab.leftCoord.coordError_sector
import Submission.Work.Parab.leftCoordData.orbit_ends_control
import Submission.Work.Parab.leftCoord.exists_levelFacts
import Submission.Work.Parab.basin_basic
import Submission.Work.Parab.Eends.wedge_PsiC_asymptotic
import Submission.Work.Parab.Eends.basin_Phi_eq_PsiC

/-!
# The two ends of the Ecalle coordinate: the limits of `Φ (φ w) - w`

Shishikura's A.3 normalisation: for a parabolic germ with its §4.1 data, the composition
`E = Φ ∘ φ` satisfies `E w - w → 0` at the upper end and tends to a constant at the lower end.

The proof uses two structural facts.

* `E w - w` is invariant under `w ↦ w + 1` (the Abel equations for `φ` and for `Φ`), so the
  statement on the ends `{Im → ±∞}` follows from the statement on the fundamental strip
  `{Re w + ξ₀ ∈ [-1, 0]}`.
* On that strip the point `φ w` is close to `0` and in the correct direction, so that
  `Φ (φ w) = ψ w' - n` with `w' = -1/(φ w)` and `ψ = fatouCoordW f (1 - a)`: this is
  `basin_Phi_eq_PsiC`, and the asymptotic `ψ w' = w' - (1-a) log w' + o(1)` uniformly in `Re w'`
  is `wedge_PsiC_asymptotic`.  Composing with the asymptotic of `φ` itself
  (`CoordData.φ_asymp_ends`) leaves the explicit expression
  `d.bEnd + (1 - d.ag) (log (-w) - log w)` whose two boundary values are the limits.
-/

namespace Work.Parab.Eends

open Complex Set Filter Metric
open scoped Topology

noncomputable section

/-! ## The two ends as filters -/

lemma tendsto_upperEnd_iff {g : ℂ → ℂ} {l : ℂ} :
    Filter.Tendsto g MandelDim.upperEnd (nhds l) ↔
      ∀ ε > 0, ∃ T : ℝ, ∀ w : ℂ, T < w.im → dist (g w) l < ε := by
  rw [MandelDim.upperEnd, Filter.tendsto_def]
  constructor
  · intro h ε hε
    have hmem : g ⁻¹' Metric.ball l ε ∈ Filter.comap Complex.im Filter.atTop :=
      h (Metric.ball l ε) (Metric.ball_mem_nhds l hε)
    rw [Filter.mem_comap] at hmem
    obtain ⟨t, ht, hsub⟩ := hmem
    rw [Filter.mem_atTop_sets] at ht
    obtain ⟨a, ha⟩ := ht
    exact ⟨a, fun w hw => hsub (ha w.im (le_of_lt hw))⟩
  · intro h V hV
    rw [Metric.mem_nhds_iff] at hV
    obtain ⟨ε, hε, hball⟩ := hV
    obtain ⟨T, hT⟩ := h ε hε
    rw [Filter.mem_comap]
    exact ⟨Set.Ioi T, Filter.Ioi_mem_atTop T, fun w hw => hball (hT w hw)⟩

lemma tendsto_lowerEnd_iff {g : ℂ → ℂ} {l : ℂ} :
    Filter.Tendsto g MandelDim.lowerEnd (nhds l) ↔
      ∀ ε > 0, ∃ T : ℝ, ∀ w : ℂ, w.im < T → dist (g w) l < ε := by
  rw [MandelDim.lowerEnd, Filter.tendsto_def]
  constructor
  · intro h ε hε
    have hmem : g ⁻¹' Metric.ball l ε ∈ Filter.comap Complex.im Filter.atBot :=
      h (Metric.ball l ε) (Metric.ball_mem_nhds l hε)
    rw [Filter.mem_comap] at hmem
    obtain ⟨t, ht, hsub⟩ := hmem
    rw [Filter.mem_atBot_sets] at ht
    obtain ⟨a, ha⟩ := ht
    exact ⟨a, fun w hw => hsub (ha w.im (le_of_lt hw))⟩
  · intro h V hV
    rw [Metric.mem_nhds_iff] at hV
    obtain ⟨ε, hε, hball⟩ := hV
    obtain ⟨T, hT⟩ := h ε hε
    rw [Filter.mem_comap]
    exact ⟨Set.Iio T, Filter.Iio_mem_atBot T, fun w hw => hball (hT w hw)⟩

/-! ## Elementary complex logarithm facts -/

lemma log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - (Real.pi : ℂ) * I := by
  have harg : (-u).arg = u.arg - Real.pi := Complex.arg_neg_eq_arg_sub_pi_of_im_pos hu
  have hnorm : ‖-u‖ = ‖u‖ := norm_neg u
  apply Complex.ext
  · simp [Complex.log_re, hnorm]
  · simp [Complex.log_im, harg]

lemma log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + (Real.pi : ℂ) * I := by
  have harg : (-u).arg = u.arg + Real.pi := Complex.arg_neg_eq_arg_add_pi_of_im_neg hu
  have hnorm : ‖-u‖ = ‖u‖ := norm_neg u
  apply Complex.ext
  · simp [Complex.log_re, hnorm]
  · simp [Complex.log_im, harg]

lemma norm_log_le (z : ℂ) : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 : |z.arg| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg z), Complex.arg_le_pi z⟩
  linarith

/-- For `m → ∞`, `2 K (log (2 m) + π + 1) ≤ δ m`. -/
lemma eventually_two_mul_log_le {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ m : ℝ in Filter.atTop, 2 * K * (Real.log (2 * m) + Real.pi + 1) ≤ δ * m := by
  have hc : 0 < δ / (8 * (K + 1)) := div_pos hδ (by linarith)
  have h1 : ∀ᶠ m : ℝ in Filter.atTop,
      ‖Real.log m‖ ≤ (δ / (8 * (K + 1))) * ‖m‖ :=
    (Asymptotics.isLittleO_iff.mp Real.isLittleO_log_id_atTop) (c := δ / (8 * (K + 1))) hc
  have h2 : ∀ᶠ m : ℝ in Filter.atTop, (16 * K * (Real.log 2 + Real.pi + 1)) / δ ≤ m :=
    eventually_ge_atTop _
  have h3 : ∀ᶠ m : ℝ in Filter.atTop, 1 ≤ m := eventually_ge_atTop 1
  filter_upwards [h1, h2, h3] with m hm1 hm2 hm3
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm3
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm3
  rw [Real.norm_eq_abs, abs_of_nonneg hlogm, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hmpos)]
    at hm1
  have h2m : Real.log (2 * m) = Real.log 2 + Real.log m :=
    Real.log_mul (by norm_num) (ne_of_gt hmpos)
  have hbound : 16 * K * (Real.log 2 + Real.pi + 1) ≤ δ * m := by
    rw [div_le_iff₀ hδ] at hm2
    linarith
  have hK1 : 2 * K / (8 * (K + 1)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 8 * (K + 1))]
    linarith
  calc 2 * K * (Real.log (2 * m) + Real.pi + 1)
      = 2 * K * (Real.log 2 + Real.pi + 1) + 2 * K * Real.log m := by rw [h2m]; ring
    _ ≤ (δ * m) / 8 + 2 * K * ((δ / (8 * (K + 1))) * m) := by
        have h4 : 2 * K * (Real.log 2 + Real.pi + 1) ≤ (δ * m) / 8 := by linarith
        have h5 : 2 * K * Real.log m ≤ 2 * K * ((δ / (8 * (K + 1))) * m) :=
          mul_le_mul_of_nonneg_left hm1 (by linarith)
        linarith
    _ ≤ (δ * m) / 8 + (1 / 4) * (δ * m) := by
        have h6 : 2 * K * ((δ / (8 * (K + 1))) * m) = (2 * K / (8 * (K + 1))) * (δ * m) := by
          ring
        have h7 : (2 * K / (8 * (K + 1))) * (δ * m) ≤ (1 / 4) * (δ * m) :=
          mul_le_mul_of_nonneg_right hK1 (by positivity)
        rw [h6]
        linarith
    _ ≤ δ * m := by
        have h8 : 0 < δ * m := mul_pos hδ hmpos
        linarith

/-! ## Periodicity of `w ↦ Φ (φ w) - w` on the ends -/

lemma endF_add_one {f : ℂ → ℂ} {D₀ : Set ℂ} (d : Work.Parab.CoordData f D₀)
    {Φ : ℂ → ℂ} (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    {w : ℂ} (hw : d.η₀ < |w.im|) :
    Φ (d.φ (w + 1)) - (w + 1) = Φ (d.φ w) - w := by
  have him : |(w + 1).im| = |w.im| := by simp
  obtain ⟨hwd, hpb⟩ := d.ends_sub w hw
  obtain ⟨hw1d, -⟩ := d.ends_sub (w + 1) (by rw [him]; exact hw)
  rw [d.φ_abel w hwd hw1d, hΦabel (d.φ w) hpb]
  ring

lemma endF_add_nat {f : ℂ → ℂ} {D₀ : Set ℂ} (d : Work.Parab.CoordData f D₀)
    {Φ : ℂ → ℂ} (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    (n : ℕ) {w : ℂ} (hw : d.η₀ < |w.im|) :
    Φ (d.φ (w + (n : ℂ))) - (w + (n : ℂ)) = Φ (d.φ w) - w := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hwk : d.η₀ < |(w + (k : ℂ)).im| := by simpa using hw
      have h1 : Φ (d.φ ((w + (k : ℂ)) + 1)) - ((w + (k : ℂ)) + 1)
          = Φ (d.φ (w + (k : ℂ))) - (w + (k : ℂ)) := endF_add_one d hΦabel hwk
      have h2 : Φ (d.φ (w + (k : ℂ))) - (w + (k : ℂ)) = Φ (d.φ w) - w := ih
      rw [show w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 by push_cast; ring, h1, h2]

lemma endF_sub_nat {f : ℂ → ℂ} {D₀ : Set ℂ} (d : Work.Parab.CoordData f D₀)
    {Φ : ℂ → ℂ} (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    (n : ℕ) {w : ℂ} (hw : d.η₀ < |w.im|) :
    Φ (d.φ (w - (n : ℂ))) - (w - (n : ℂ)) = Φ (d.φ w) - w := by
  induction n with
  | zero => simp
  | succ k ih =>
      set u : ℂ := w - (k : ℂ) - 1 with hudef
      have hu : d.η₀ < |u.im| := by rw [hudef]; simpa using hw
      have h1 : Φ (d.φ (u + 1)) - (u + 1) = Φ (d.φ u) - u := endF_add_one d hΦabel hu
      have hu1 : u + 1 = w - (k : ℂ) := by rw [hudef]; ring
      rw [hu1] at h1
      have h2 : Φ (d.φ (w - (k : ℂ))) - (w - (k : ℂ)) = Φ (d.φ w) - w := ih
      have hgoal : w - ((k + 1 : ℕ) : ℂ) = u := by rw [hudef]; push_cast; ring
      rw [hgoal]
      exact h1.symm.trans h2

/-- The integer shifts. -/
lemma endF_int {f : ℂ → ℂ} {D₀ : Set ℂ} (d : Work.Parab.CoordData f D₀)
    {Φ : ℂ → ℂ} (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    (k : ℤ) {w : ℂ} (hw : d.η₀ < |w.im|) :
    Φ (d.φ (w + (k : ℂ))) - (w + (k : ℂ)) = Φ (d.φ w) - w := by
  by_cases hk : 0 ≤ k
  · have h1 : (((k.toNat : ℕ) : ℂ)) = (k : ℂ) := by
      have h := Int.toNat_of_nonneg hk
      exact_mod_cast h
    have h := endF_add_nat d hΦabel k.toNat hw
    rwa [h1] at h
  · have hk' : k < 0 := not_le.mp hk
    have h1 : ((((-k).toNat : ℕ) : ℂ)) = (-(k : ℂ)) := by
      have h := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -k)
      exact_mod_cast h
    have h := endF_sub_nat d hΦabel (-k).toNat (w := w) hw
    rw [h1] at h
    simpa using h

/-- `a * (δ / 2) ≤ (a + 1) * δ` for `a, δ ≥ 0`. -/
lemma mul_half_le_succ_mul {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) : a * (δ / 2) ≤ (a + 1) * δ := by
  nlinarith

/-- `(a + 1) * δ ≤ ε / 8` from `δ ≤ ε / (8 (a + 1))`. -/
lemma succ_mul_le_eighth {a δ ε : ℝ} (ha : 0 ≤ a) (hδ : δ ≤ ε / (8 * (a + 1))) :
    (a + 1) * δ ≤ ε / 8 := by
  have h1 : 0 < a + 1 := by linarith
  have h2 : (a + 1) * δ ≤ (a + 1) * (ε / (8 * (a + 1))) :=
    mul_le_mul_of_nonneg_left hδ (le_of_lt h1)
  have h3 : (a + 1) * (ε / (8 * (a + 1))) = ε / 8 := by field_simp
  linarith [h2, h3.le]

/-- The final numeric step, isolated so that `linarith` never sees the large terms. -/
lemma add_le_half {δ D ε : ℝ} (hD : D ≤ ε / 8) (hδ : δ ≤ ε / 8) (hε : 0 < ε) :
    δ + D + ε / 4 ≤ ε / 2 := by linarith

/-- The triangle inequality for three terms. -/
lemma norm_add_add_le (A B C : ℂ) : ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
  calc ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
    _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by linarith [norm_add_le A B]

/-- The final triangle-inequality step of the strip estimate, with the numerical side
conditions separated off so that `linarith` never sees the (large) terms `A`, `B`, `C`. -/
lemma endBound {A B C : ℂ} {δ D ε : ℝ} (hε : 0 < ε) (hA : ‖A‖ ≤ δ) (hB : ‖B‖ ≤ D)
    (hC : ‖C‖ ≤ ε / 4) (hsum : δ + D + ε / 4 ≤ ε / 2) : ‖A + B + C‖ < ε := by
  have h := norm_add_add_le A B C
  linarith

/-! ## The limit on the fundamental strip -/

theorem strip_limit {f : ℂ → ℂ} {D₀ : Set ℂ} (hg : MandelDim.IsParabolicGerm f D₀)
    (d : Work.Parab.CoordData f D₀) {h : ℂ → ℂ} {r A A' M : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h d.ag r A A')
    (hpetal : Work.FatouCoord.Petal r M ⊆ MandelDim.ParabolicBasin f D₀)
    {Φ : ℂ → ℂ}
    (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    (hΦpet : ∀ z ∈ Work.FatouCoord.Petal r M, Φ z = Work.FatouCoord.fatouCoord f (1 - d.ag) z) :
    ∀ ε > 0, ∃ T : ℝ, ∀ u : ℂ, -1 ≤ u.re + d.ξ₀ → u.re + d.ξ₀ ≤ 0 → T < |u.im| →
      ‖Φ (d.φ u) - u - (d.bEnd + (1 - d.ag) * (Complex.log (-u) - Complex.log u))‖ < ε := by
  intro ε hε
  obtain ⟨N₁, -, hNasym⟩ := wedge_PsiC_asymptotic hb
  obtain ⟨N₂, -, -, -, hN₂⟩ := basin_Phi_eq_PsiC hg hb hpetal hΦabel hΦpet
  have hNasym' := hNasym (max N₁ N₂) (le_max_left _ _)
  obtain ⟨T₂, hT₂⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨T₁, hT₁⟩ := hNasym' (ε / 4) hε4
  set δ : ℝ := min 1 (ε / (8 * (‖1 - d.ag‖ + 1))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδle : δ ≤ ε / (8 * (‖1 - d.ag‖ + 1)) := min_le_right _ _
  have hδle1 : δ ≤ 1 := min_le_left _ _
  obtain ⟨R, hR⟩ := d.φ_asymp_ends δ hδpos
  set K₁ : ℝ := ‖1 - d.ag‖ + ‖d.bEnd‖ + 1 with hK₁def
  have hK₁nn : 0 ≤ K₁ := by rw [hK₁def]; positivity
  have hKlog : ∀ᶠ m : ℝ in Filter.atTop, K₁ * (Real.log (2 * m) + Real.pi + 1) ≤ m / 4 := by
    have h := eventually_two_mul_log_le (K := K₁) (δ := (1/2 : ℝ)) hK₁nn (by norm_num)
    filter_upwards [h] with m hm
    linarith
  have hKlog2 : ∀ᶠ m : ℝ in Filter.atTop,
      2 * K₁ * (Real.log (2 * m) + Real.pi + 1) ≤ (δ / 2) * m :=
    eventually_two_mul_log_le (K := K₁) (δ := δ / 2) hK₁nn (by positivity)
  have hbig : ∀ᶠ m : ℝ in Filter.atTop, R < m ∧ 2 * T₁ < m ∧ 2 * T₂ < m ∧ d.η₀ < m ∧
      8 ≤ m ∧ d.ξ₀ + 1 ≤ m ∧ 4 * (d.ξ₀ + 1) < 5 * m := by
    filter_upwards [eventually_gt_atTop R, eventually_gt_atTop (2 * T₁),
      eventually_gt_atTop (2 * T₂), eventually_gt_atTop d.η₀, eventually_ge_atTop (8 : ℝ),
      eventually_ge_atTop (d.ξ₀ + 1), eventually_gt_atTop (4 * (d.ξ₀ + 1) / 5)]
      with m h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, by linarith⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hKlog.and (hKlog2.and hbig))
  refine ⟨max T 0, fun u hlo hhi him => ?_⟩
  have himT : T ≤ |u.im| := le_of_lt (lt_of_le_of_lt (le_max_left _ _) him)
  obtain ⟨hKlog', hKlog2', hRlt, hT₁lt, hT₂lt, hηlt, hm8, hmξ, hmw⟩ := hT _ himT
  set m : ℝ := |u.im| with hmdef
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm8
  have hmm : |u.im| = m := hmdef.symm
  have hu_re_neg : u.re < 0 := by linarith [hhi, d.ξ₀_pos]
  have hu_re_low : -(d.ξ₀ + 1) ≤ u.re := by linarith
  have hnorm_ge : m ≤ ‖u‖ := by rw [← hmm]; exact Complex.abs_im_le_norm u
  have hnorm_le : ‖u‖ ≤ 2 * m := by
    have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    have h2 : |u.re| ≤ d.ξ₀ + 1 := by rw [abs_of_neg hu_re_neg]; linarith
    rw [← hmm]
    linarith
  -- the short-hands
  have hs_def : Real.log (2 * m) + Real.pi + 1 = Real.log (2 * m) + Real.pi + 1 := rfl
  have hs1 : (1 : ℝ) ≤ Real.log (2 * m) + Real.pi + 1 := by
    have h1 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
    linarith [Real.pi_pos]
  -- the point `w' = -1/(φ u)`
  set w' : ℂ := MandelDim.tau0 (d.φ u) with hw'def
  have hw'_asymp : ‖w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd)‖ < δ := by
    rw [hw'def]
    exact hR u (by rw [hmm]; exact hRlt)
  have hlog_bound : ‖Complex.log (-u)‖ ≤ Real.log (2 * m) + Real.pi := by
    have h1 : ‖Complex.log (-u)‖ ≤ |Real.log ‖-u‖| + Real.pi := norm_log_le _
    rw [norm_neg] at h1
    have h2 : 0 < ‖u‖ := lt_of_lt_of_le hmpos hnorm_ge
    have h3 : Real.log ‖u‖ ≤ Real.log (2 * m) := Real.log_le_log h2 hnorm_le
    have h4 : 0 ≤ Real.log ‖u‖ := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h4] at h1
    linarith
  have hsmall : ‖(1 - d.ag) * Complex.log (-u) + d.bEnd‖
      ≤ (‖1 - d.ag‖ + ‖d.bEnd‖) * (Real.log (2 * m) + Real.pi + 1) := by
    have h2 : ‖(1 - d.ag) * Complex.log (-u)‖ ≤ ‖1 - d.ag‖ * (Real.log (2 * m) + Real.pi) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hlog_bound (norm_nonneg _)
    have h6 : ‖d.bEnd‖ ≤ ‖d.bEnd‖ * (Real.log (2 * m) + Real.pi + 1) := by
      nlinarith [norm_nonneg d.bEnd, hs1]
    have h7 : ‖1 - d.ag‖ * (Real.log (2 * m) + Real.pi)
        ≤ ‖1 - d.ag‖ * (Real.log (2 * m) + Real.pi + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h8 := norm_add_le ((1 - d.ag) * Complex.log (-u)) d.bEnd
    linarith
  have hw'_sub : ‖w' - u‖ ≤ K₁ * (Real.log (2 * m) + Real.pi + 1) := by
    have h1 : w' - u = ((1 - d.ag) * Complex.log (-u) + d.bEnd)
        + (w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd)) := by ring
    rw [h1]
    calc ‖((1 - d.ag) * Complex.log (-u) + d.bEnd)
            + (w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd))‖
        ≤ ‖(1 - d.ag) * Complex.log (-u) + d.bEnd‖
            + ‖w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd)‖ := norm_add_le _ _
      _ ≤ (‖1 - d.ag‖ + ‖d.bEnd‖) * (Real.log (2 * m) + Real.pi + 1)
            + (Real.log (2 * m) + Real.pi + 1) := by linarith [hsmall, hδle1, hs1]
      _ = K₁ * (Real.log (2 * m) + Real.pi + 1) := by rw [hK₁def]; ring
  -- `|Im w'|` is at least half of `m`
  have hw'_im : m / 2 ≤ |w'.im| := by
    have h1 : m ≤ |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im|
        + (‖1 - d.ag‖ + ‖d.bEnd‖) * (Real.log (2 * m) + Real.pi + 1) := by
      have h3 : |u.im| ≤ |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im|
          + |((1 - d.ag) * Complex.log (-u) + d.bEnd).im| := by
        have h5 : (u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im
            + (-(((1 - d.ag) * Complex.log (-u) + d.bEnd).im)) = u.im := by
          simp only [Complex.add_im]
          ring
        calc |u.im| = |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im
              + (-(((1 - d.ag) * Complex.log (-u) + d.bEnd).im))| := by rw [h5]
          _ ≤ |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im|
              + |(-(((1 - d.ag) * Complex.log (-u) + d.bEnd).im))| := abs_add_le _ _
          _ = |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im|
              + |((1 - d.ag) * Complex.log (-u) + d.bEnd).im| := by rw [abs_neg]
      have h6 : |((1 - d.ag) * Complex.log (-u) + d.bEnd).im|
          ≤ ‖(1 - d.ag) * Complex.log (-u) + d.bEnd‖ := Complex.abs_im_le_norm _
      have h7 : |u.im| = m := hmm
      linarith [h3, h6, hsmall, h7]
    have h2 : |w'.im - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im| ≤ δ := by
      calc |w'.im - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im|
          = |(w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd)).im| := by simp
        _ ≤ ‖w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd)‖ := Complex.abs_im_le_norm _
        _ ≤ δ := le_of_lt hw'_asymp
    have h8 : |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im| - δ ≤ |w'.im| := by
      have h9 : |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im| - |w'.im|
          ≤ |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im - w'.im| :=
        abs_sub_abs_le_abs_sub _ _
      have h10 : |(u + (1 - d.ag) * Complex.log (-u) + d.bEnd).im - w'.im| ≤ δ := by
        rw [abs_sub_comm]; exact h2
      linarith
    have hC1 : (‖1 - d.ag‖ + ‖d.bEnd‖) * (Real.log (2 * m) + Real.pi + 1)
        ≤ K₁ * (Real.log (2 * m) + Real.pi + 1) := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith [Real.pi_pos])
      rw [hK₁def]; linarith [norm_nonneg (1 - d.ag), norm_nonneg d.bEnd]
    linarith [h1, h8, hC1, hKlog', hδle1, hm8, hmpos]
  -- the wedge condition for `w'`
  have hw'_wedge : -3 * |w'.im| < w'.re := by
    have h1 : u.re - ‖w' - u‖ ≤ w'.re := by
      have h3 : |(w' - u).re| ≤ ‖w' - u‖ := Complex.abs_re_le_norm _
      have h4 : (w' - u).re = w'.re - u.re := by simp
      have h5 : -|(w' - u).re| ≤ (w' - u).re := neg_abs_le _
      linarith [h3, h4, h5]
    have h2 : -(d.ξ₀ + 1) - K₁ * (Real.log (2 * m) + Real.pi + 1) ≤ u.re - ‖w' - u‖ := by
      linarith [hu_re_low, hw'_sub]
    have h3 : K₁ * (Real.log (2 * m) + Real.pi + 1) ≤ m / 4 := hKlog'
    have h4 : m / 2 ≤ |w'.im| := hw'_im
    linarith [h1, h2, h3, h4, hmw]
  -- the identification of `Φ (φ u)` with the closed extension
  have hneq : d.φ u ≠ 0 := by
    intro h0
    have hzero : w' = 0 := by rw [hw'def, h0]; simp [MandelDim.tau0]
    rw [hzero] at hw'_im
    simp only [Complex.zero_im, abs_zero] at hw'_im
    linarith [hmpos]
  have hneg : -1 / w' = d.φ u := by
    rw [hw'def, MandelDim.tau0]
    field_simp
  have hbasin : d.φ u ∈ MandelDim.ParabolicBasin f D₀ :=
    (d.ends_sub u (by rw [hmm]; exact hηlt)).2
  have hident : Φ (d.φ u) = Work.Parab.leftCoord.PsiC (max N₁ N₂) (Work.FatouCoord.wMap f)
      (Work.FatouCoord.fatouCoordW f (1 - d.ag)) w' := by
    have h := hT₂ w' (by linarith [hT₂lt, hw'_im]) hw'_wedge (by rw [hneg]; exact hbasin)
    rwa [hneg] at h
  have hasym : ‖Work.Parab.leftCoord.PsiC (max N₁ N₂) (Work.FatouCoord.wMap f)
      (Work.FatouCoord.fatouCoordW f (1 - d.ag)) w' - (w' - (1 - d.ag) * Complex.log w')‖
        < ε / 4 :=
    hT₁ w' (by linarith [hT₁lt, hw'_im]) hw'_wedge
  -- the logarithmic difference
  have hseg : ∀ z ∈ segment ℝ u w', m / 2 ≤ |z.im| := by
    intro z hz
    have h1 : ‖z - u‖ ≤ ‖w' - u‖ := norm_sub_le_of_mem_segment hz
    have h2 : |z.im - u.im| ≤ ‖z - u‖ := by
      calc |z.im - u.im| = |(z - u).im| := by simp
        _ ≤ ‖z - u‖ := Complex.abs_im_le_norm _
    have h3 : |u.im| - |z.im| ≤ |u.im - z.im| := abs_sub_abs_le_abs_sub _ _
    have h4 : |u.im - z.im| = |z.im - u.im| := abs_sub_comm _ _
    have h5 : |u.im| = m := hmm
    have h6 : ‖w' - u‖ ≤ m / 4 := by linarith [hw'_sub, hKlog']
    linarith
  have hslit : ∀ z ∈ segment ℝ u w', z ∈ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    refine Or.inr (fun h0 => ?_)
    have h1 := hseg z hz
    rw [h0] at h1
    simp only [Complex.zero_im, abs_zero] at h1
    linarith [hmpos]
  have hderiv : ∀ z ∈ segment ℝ u w', ‖deriv Complex.log z‖ ≤ 2 / m := by
    intro z hz
    rw [Complex.deriv_log (hslit z hz), norm_inv]
    have hzm : m / 2 ≤ ‖z‖ := by linarith [hseg z hz, Complex.abs_im_le_norm z]
    have hzpos : 0 < ‖z‖ := by linarith [hzm, hmpos]
    have hm2pos : 0 < m / 2 := by linarith
    calc ‖z‖⁻¹ ≤ (m / 2)⁻¹ := (inv_le_inv₀ hzpos hm2pos).mpr hzm
      _ = 2 / m := by field_simp
  have hlogdiff : ‖Complex.log w' - Complex.log u‖
      ≤ 2 * K₁ * (Real.log (2 * m) + Real.pi + 1) / m := by
    have hMVT : ‖Complex.log w' - Complex.log u‖ ≤ (2 / m) * ‖w' - u‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (Complex.hasDerivAt_log (hslit z hz)).differentiableAt)
        (fun z hz => hderiv z hz)
        (convex_segment u w') (left_mem_segment ℝ u w') (right_mem_segment ℝ u w')
    calc ‖Complex.log w' - Complex.log u‖ ≤ (2 / m) * ‖w' - u‖ := hMVT
      _ ≤ (2 / m) * (K₁ * (Real.log (2 * m) + Real.pi + 1)) :=
          mul_le_mul_of_nonneg_left hw'_sub (by positivity)
      _ = 2 * K₁ * (Real.log (2 * m) + Real.pi + 1) / m := by ring
  -- the final algebra
  have hdecomp : Φ (d.φ u) - u - (d.bEnd + (1 - d.ag) * (Complex.log (-u) - Complex.log u))
      = (w' - (u + (1 - d.ag) * Complex.log (-u) + d.bEnd))
        + ((1 - d.ag) * (Complex.log u - Complex.log w'))
        + (Work.Parab.leftCoord.PsiC (max N₁ N₂) (Work.FatouCoord.wMap f)
            (Work.FatouCoord.fatouCoordW f (1 - d.ag)) w'
              - (w' - (1 - d.ag) * Complex.log w')) := by
    rw [← hident]
    ring
  have hδ' : 2 * K₁ * (Real.log (2 * m) + Real.pi + 1) / m ≤ δ / 2 := by
    have h := hKlog2'
    rw [div_le_iff₀ hmpos]
    linarith
  have hδ8 : δ ≤ ε / 8 := by
    have h4 : δ * (8 * (‖1 - d.ag‖ + 1)) ≤ ε := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * (‖1 - d.ag‖ + 1))] at hδle
      exact hδle
    have h5 : (1 : ℝ) ≤ ‖1 - d.ag‖ + 1 := by linarith [norm_nonneg (1 - d.ag)]
    nlinarith [h4, h5, hδpos]
  rw [hdecomp]
  have hB : ‖(1 - d.ag) * (Complex.log u - Complex.log w')‖ ≤ ‖1 - d.ag‖ * (δ / 2) := by
    rw [norm_mul]
    have h1 : ‖Complex.log u - Complex.log w'‖ ≤ δ / 2 := by
      rw [← norm_sub_rev]
      exact le_trans hlogdiff hδ'
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have h3 : ‖1 - d.ag‖ * (δ / 2) ≤ ε / 8 :=
    le_trans (mul_half_le_succ_mul (norm_nonneg (1 - d.ag)) (le_of_lt hδpos))
      (succ_mul_le_eighth (norm_nonneg (1 - d.ag)) hδle)
  exact endBound (D := ‖1 - d.ag‖ * (δ / 2)) hε (le_of_lt hw'_asymp) hB (le_of_lt hasym)
    (add_le_half h3 hδ8 hε)


/-! ## The main theorem -/

theorem E_ends {f : ℂ → ℂ} {D₀ : Set ℂ} (hg : MandelDim.IsParabolicGerm f D₀)
    (d : Work.Parab.CoordData f D₀)
    {Φ : ℂ → ℂ} {h : ℂ → ℂ} {r A A' M : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h d.ag r A A')
    (hpetal : Work.FatouCoord.Petal r M ⊆ MandelDim.ParabolicBasin f D₀)
    (hΦholo : DifferentiableOn ℂ Φ (MandelDim.ParabolicBasin f D₀))
    (hΦabel : ∀ z ∈ MandelDim.ParabolicBasin f D₀, Φ (f z) = Φ z + 1)
    (hΦpet : ∀ z ∈ Work.FatouCoord.Petal r M, Φ z = Work.FatouCoord.fatouCoord f (1 - d.ag) z) :
    ∃ cl cl' : ℂ,
      Filter.Tendsto (fun w => Φ (d.φ w) - w) MandelDim.upperEnd (nhds cl) ∧
      Filter.Tendsto (fun w => Φ (d.φ w) - w) MandelDim.lowerEnd (nhds cl') := by
  have hstrip := strip_limit hg d hb hpetal hΦabel hΦpet
  refine ⟨d.bEnd - (1 - d.ag) * ((Real.pi : ℂ) * I),
    d.bEnd + (1 - d.ag) * ((Real.pi : ℂ) * I), ?_, ?_⟩
  · rw [tendsto_upperEnd_iff]
    intro ε hε
    obtain ⟨T, hT⟩ := hstrip ε hε
    refine ⟨max T (max d.η₀ 0), fun w hw => ?_⟩
    have hwT : T < w.im := lt_of_le_of_lt (le_max_left _ _) hw
    have hwη : d.η₀ < w.im :=
      lt_of_le_of_lt (le_trans (le_max_left d.η₀ 0) (le_max_right T (max d.η₀ 0))) hw
    have hwpos : 0 < w.im :=
      lt_of_le_of_lt (le_trans (le_max_right d.η₀ 0) (le_max_right T (max d.η₀ 0))) hw
    set k : ℤ := ⌈w.re + d.ξ₀⌉ with hkdef
    set u : ℂ := w - (k : ℂ) with hudef
    have hu_re : u.re = w.re - (k : ℝ) := by rw [hudef]; simp
    have hu_im : u.im = w.im := by rw [hudef]; simp
    have hu_imabs : |u.im| = w.im := by rw [hu_im, abs_of_pos hwpos]
    have hu_lo : (-1 : ℝ) ≤ u.re + d.ξ₀ := by
      have h2 : (-1 : ℝ) < (w.re + d.ξ₀) - (⌈w.re + d.ξ₀⌉ : ℝ) := by
        have := Int.ceil_lt_add_one (w.re + d.ξ₀); linarith
      rw [hu_re, hkdef]
      linarith
    have hu_hi : u.re + d.ξ₀ ≤ 0 := by
      have h1 : (w.re + d.ξ₀) - (⌈w.re + d.ξ₀⌉ : ℝ) ≤ 0 := by
        have := Int.le_ceil (w.re + d.ξ₀); linarith
      rw [hu_re, hkdef]
      linarith
    have huT : T < |u.im| := by rw [hu_imabs]; exact hwT
    have huη : d.η₀ < |u.im| := by rw [hu_imabs]; exact hwη
    have hstrip_u := hT u hu_lo hu_hi huT
    have huimpos : 0 < u.im := by rw [hu_im]; exact hwpos
    have hbranch : Complex.log (-u) - Complex.log u = -((Real.pi : ℂ) * I) := by
      rw [log_neg_of_im_pos huimpos]
      ring
    have hshift : Φ (d.φ w) - w = Φ (d.φ u) - u := by
      have h := endF_int d hΦabel k (w := u) huη
      rwa [show u + (k : ℂ) = w by rw [hudef]; ring] at h
    have hgoal : Φ (d.φ u) - u - (d.bEnd + (1 - d.ag) * (Complex.log (-u) - Complex.log u))
        = Φ (d.φ u) - u - (d.bEnd - (1 - d.ag) * ((Real.pi : ℂ) * I)) := by
      rw [hbranch]; ring
    rw [dist_eq_norm, hshift, ← hgoal]
    exact hstrip_u
  · rw [tendsto_lowerEnd_iff]
    intro ε hε
    obtain ⟨T, hT⟩ := hstrip ε hε
    refine ⟨min (-T) (min (-d.η₀) 0), fun w hw => ?_⟩
    have hwT' : w.im < -T := lt_of_lt_of_le hw (min_le_left _ _)
    have hwneg : w.im < 0 :=
      lt_of_lt_of_le hw (le_trans (min_le_right (-T) (min (-d.η₀) 0)) (min_le_right (-d.η₀) 0))
    have hwηneg : w.im < -d.η₀ :=
      lt_of_lt_of_le hw (le_trans (min_le_right (-T) (min (-d.η₀) 0)) (min_le_left (-d.η₀) 0))
    have hwη : d.η₀ < |w.im| := by rw [abs_of_neg hwneg]; linarith
    set k : ℤ := ⌈w.re + d.ξ₀⌉ with hkdef
    set u : ℂ := w - (k : ℂ) with hudef
    have hu_re : u.re = w.re - (k : ℝ) := by rw [hudef]; simp
    have hu_im : u.im = w.im := by rw [hudef]; simp
    have hu_imabs : |u.im| = |w.im| := by rw [hu_im]
    have hu_lo : (-1 : ℝ) ≤ u.re + d.ξ₀ := by
      have h2 : (-1 : ℝ) < (w.re + d.ξ₀) - (⌈w.re + d.ξ₀⌉ : ℝ) := by
        have := Int.ceil_lt_add_one (w.re + d.ξ₀); linarith
      rw [hu_re, hkdef]
      linarith
    have hu_hi : u.re + d.ξ₀ ≤ 0 := by
      have h1 : (w.re + d.ξ₀) - (⌈w.re + d.ξ₀⌉ : ℝ) ≤ 0 := by
        have := Int.le_ceil (w.re + d.ξ₀); linarith
      rw [hu_re, hkdef]
      linarith
    have huT : T < |u.im| := by rw [hu_imabs, abs_of_neg hwneg]; linarith
    have huη : d.η₀ < |u.im| := by rw [hu_imabs]; exact hwη
    have hstrip_u := hT u hu_lo hu_hi huT
    have huimneg : u.im < 0 := by rw [hu_im]; exact hwneg
    have hbranch : Complex.log (-u) - Complex.log u = (Real.pi : ℂ) * I := by
      rw [log_neg_of_im_neg huimneg]
      ring
    have hshift : Φ (d.φ w) - w = Φ (d.φ u) - u := by
      have h := endF_int d hΦabel k (w := u) huη
      rwa [show u + (k : ℂ) = w by rw [hudef]; ring] at h
    have hgoal : Φ (d.φ u) - u - (d.bEnd + (1 - d.ag) * (Complex.log (-u) - Complex.log u))
        = Φ (d.φ u) - u - (d.bEnd + (1 - d.ag) * ((Real.pi : ℂ) * I)) := by
      rw [hbranch]
    rw [dist_eq_norm, hshift, ← hgoal]
    exact hstrip_u


end

end Work.Parab.Eends
