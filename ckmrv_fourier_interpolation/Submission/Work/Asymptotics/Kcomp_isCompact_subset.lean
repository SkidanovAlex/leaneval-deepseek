/-
# `Kcomp` is a compact subset of `𝒟`

The cusp-`0` half tile `Tregion = {w ∈ 𝒟 : 1/2 ≤ Im (S • w) ≤ 2}`
(`Submission/Work/Asymptotics/seminormK_cusp0_half.lean`) is *not* relatively compact in `𝒟`:
its closure meets `∂𝒟` along the arcs `{|w ∓ 1/2| = 1/2}` and at the two points `±1 + i` of the
bad lines.  Removing the two bad-line neighbourhoods of radius `1/10` and the two arc
neighbourhoods of radius `1/10` leaves `Kcomp`, and this file proves the elementary geometry
recorded in that file: `Kcomp` is compact and contained in `𝒟`.

The only non-elementary input is the estimate `Im w > 1/10` on `Tregion` (`key_estimate`
below), which is what makes `Tregion` — and hence `Kcomp` — bounded away from the real axis.
Writing `w = X + iY`, the conditions `1/2 ≤ Im (S • w) ≤ 2` read

  `X² + Y² ≤ 2Y`   and   `Y ≤ 2 (X² + Y²)`,

while `w ∈ 𝒟` gives `0 < X² - X + Y²` and `0 < X² + X + Y²` (the two arcs).  With
`A = X² + Y²` these say `A ≤ 2Y`, `Y ≤ 2A`, `|X| < A`; from `|X| < A` we get `X² < A²`, i.e.
`Y² > A - A² ≥ A - 4Y²`, so `5Y² > A ≥ Y/2`, whence `Y > 1/10`.
-/
import Mathlib
import Submission.Work.Asymptotics.seminormK_cusp0_defs

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Topology

/-- **The away-from-the-axis estimate.**  For `w = X + iY ∈ Tregion` one has `Y > 1/10`;
this is a statement about real numbers, using `A = X² + Y²`. -/
private lemma key_estimate {X Y : ℝ} (hY : 0 < Y)
    (hI : X ^ 2 + Y ^ 2 ≤ 2 * Y) (hII : Y ≤ 2 * (X ^ 2 + Y ^ 2))
    (hIII : 0 < X ^ 2 - X + Y ^ 2) (hIV : 0 < X ^ 2 + X + Y ^ 2) :
    (1 : ℝ) / 10 < Y := by
  have hApos : 0 < X ^ 2 + Y ^ 2 := by positivity
  have hXlt : X < X ^ 2 + Y ^ 2 := by linarith
  have hXgt : -(X ^ 2 + Y ^ 2) < X := by linarith
  have hX2 : X ^ 2 < (X ^ 2 + Y ^ 2) ^ 2 := by
    have habs : |X| < X ^ 2 + Y ^ 2 := abs_lt.mpr ⟨hXgt, hXlt⟩
    nlinarith [sq_abs X, sq_abs (X ^ 2 + Y ^ 2), abs_nonneg X, abs_nonneg (X ^ 2 + Y ^ 2),
      habs, hApos]
  have hY2 : (X ^ 2 + Y ^ 2) - (X ^ 2 + Y ^ 2) ^ 2 < Y ^ 2 := by nlinarith [hX2]
  have hA2 : (X ^ 2 + Y ^ 2) ^ 2 ≤ 4 * Y ^ 2 := by nlinarith [hI, hY, sq_nonneg X]
  have h5 : (X ^ 2 + Y ^ 2) < 5 * Y ^ 2 := by linarith
  have hhalf : Y / 2 ≤ X ^ 2 + Y ^ 2 := by linarith
  nlinarith [h5, hhalf, hY]

private lemma S_smul_coe' (w : ℍ) : (((ModularGroup.S • w : ℍ)) : ℂ) = -((w : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  simp

private lemma neg_inv_im' (z : ℂ) : (-z⁻¹).im = z.im / ‖z‖ ^ 2 := by
  rw [Complex.neg_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

private lemma S_smul_im' (w : ℍ) : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_im, S_smul_coe', neg_inv_im', UpperHalfPlane.coe_im]

private lemma normSq_eq' (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The two elementary estimates on `Tregion` used below: `Im w > 1/10` (so `Tregion` is
bounded away from the real axis) and `Im w ≤ 2`, together with the disk condition
`Re w² + (Im w - 1)² ≤ 1` coming from `Im (S • w) ≥ 1/2`. -/
private lemma Tregion_est {w : ℍ} (hw : w ∈ Tregion) :
    (1 : ℝ) / 10 < w.im ∧ w.im ≤ 2 ∧ w.re ^ 2 + (w.im - 1) ^ 2 ≤ 1 := by
  rw [mem_Tregion] at hw
  obtain ⟨hwD, hlo, hhi⟩ := hw
  obtain ⟨hre1, hre2, hd1, hd2⟩ := hwD
  have hYpos : 0 < w.im := w.im_pos
  have hn2 := normSq_eq' w
  have hden : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  -- `Im (S • w) ≥ 1/2` is `Re w² + Im w² ≤ 2 Im w`
  have hI : w.re ^ 2 + w.im ^ 2 ≤ 2 * w.im := by
    rw [S_smul_im', hn2, le_div_iff₀ hden] at hlo
    nlinarith [hlo]
  -- `Im (S • w) ≤ 2` is `Im w ≤ 2 (Re w² + Im w²)`
  have hII : w.im ≤ 2 * (w.re ^ 2 + w.im ^ 2) := by
    rw [S_smul_im', hn2, div_le_iff₀ hden] at hhi
    nlinarith [hhi]
  have h3 : ‖(w : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (w.re - 1 / 2) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h4 : ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (w.re + 1 / 2) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num [Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- the two arcs of `∂𝒟`
  have hIII : 0 < w.re ^ 2 - w.re + w.im ^ 2 := by
    have hd1' : (1 / 2 : ℝ) ^ 2 < ‖(w : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      nlinarith [hd1, norm_nonneg ((w : ℂ) - (1 / 2 : ℂ))]
    rw [h3] at hd1'
    nlinarith [hd1']
  have hIV : 0 < w.re ^ 2 + w.re + w.im ^ 2 := by
    have hd2' : (1 / 2 : ℝ) ^ 2 < ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
      nlinarith [hd2, norm_nonneg ((w : ℂ) + (1 / 2 : ℂ))]
    rw [h4] at hd2'
    nlinarith [hd2']
  have hmain := key_estimate hYpos hI hII hIII hIV
  refine ⟨hmain, ?_, ?_⟩
  · nlinarith [hI, sq_nonneg w.re, sq_nonneg (w.im - 1), hYpos]
  · nlinarith [hI, sq_nonneg (w.im - 1)]

/-- The closed Euclidean box in `ℂ` containing `Kcomp`. -/
private def KboxC : Set ℂ :=
  {z | -(1 : ℝ) ≤ z.re} ∩ {z | z.re ≤ 1} ∩ {z | (1 : ℝ) / 10 ≤ z.im} ∩ {z | z.im ≤ 2} ∩
  {z | z.re ^ 2 + (z.im - 1) ^ 2 ≤ 1} ∩
  {z | (1 : ℝ) / 2 + 1 / 10 ≤ ‖z - (1 / 2 : ℂ)‖} ∩
  {z | (1 : ℝ) / 2 + 1 / 10 ≤ ‖z + (1 / 2 : ℂ)‖} ∩
  {z | (1 : ℝ) / 10 ≤ ‖z - ((1 : ℂ) + Complex.I)‖} ∩
  {z | (1 : ℝ) / 10 ≤ ‖z - ((-1 : ℂ) + Complex.I)‖}

private lemma mem_KboxC {z : ℂ} : z ∈ KboxC ↔
    -(1 : ℝ) ≤ z.re ∧ z.re ≤ 1 ∧ (1 : ℝ) / 10 ≤ z.im ∧ z.im ≤ 2 ∧
      z.re ^ 2 + (z.im - 1) ^ 2 ≤ 1 ∧
      (1 : ℝ) / 2 + 1 / 10 ≤ ‖z - (1 / 2 : ℂ)‖ ∧
      (1 : ℝ) / 2 + 1 / 10 ≤ ‖z + (1 / 2 : ℂ)‖ ∧
      (1 : ℝ) / 10 ≤ ‖z - ((1 : ℂ) + Complex.I)‖ ∧
      (1 : ℝ) / 10 ≤ ‖z - ((-1 : ℂ) + Complex.I)‖ := by
  unfold KboxC
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

private lemma isClosed_KboxC : IsClosed KboxC := by
  have h1 : IsClosed {z : ℂ | -(1 : ℝ) ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ 1} := isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | (1 : ℝ) / 10 ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ 2} := isClosed_le Complex.continuous_im continuous_const
  have h5 : IsClosed {z : ℂ | z.re ^ 2 + (z.im - 1) ^ 2 ≤ 1} :=
    isClosed_le ((Complex.continuous_re.pow 2).add
      ((Complex.continuous_im.sub continuous_const).pow 2)) continuous_const
  have h6 : IsClosed {z : ℂ | (1 : ℝ) / 2 + 1 / 10 ≤ ‖z - (1 / 2 : ℂ)‖} :=
    isClosed_le continuous_const (Continuous.norm (continuous_id.sub continuous_const))
  have h7 : IsClosed {z : ℂ | (1 : ℝ) / 2 + 1 / 10 ≤ ‖z + (1 / 2 : ℂ)‖} :=
    isClosed_le continuous_const (Continuous.norm (continuous_id.add continuous_const))
  have h8 : IsClosed {z : ℂ | (1 : ℝ) / 10 ≤ ‖z - ((1 : ℂ) + Complex.I)‖} :=
    isClosed_le continuous_const (Continuous.norm (continuous_id.sub continuous_const))
  have h9 : IsClosed {z : ℂ | (1 : ℝ) / 10 ≤ ‖z - ((-1 : ℂ) + Complex.I)‖} :=
    isClosed_le continuous_const (Continuous.norm (continuous_id.sub continuous_const))
  unfold KboxC
  exact ((((((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7).inter h8).inter h9)

private lemma isCompact_KboxC : IsCompact KboxC := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 3) isClosed_KboxC ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [mem_KboxC] at hz
  obtain ⟨ha, hb, hc, hd, he, -⟩ := hz
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have himabs : |z.im| ≤ 2 := abs_le.mpr ⟨by linarith, hd⟩
  have hreabs : |z.re| ≤ 1 := abs_le.mpr ⟨ha.trans (by norm_num), hb⟩
  have : ‖z‖ ^ 2 ≤ 9 := by
    nlinarith [sq_abs z.im, abs_nonneg z.im, himabs, sq_abs z.re, hreabs, abs_nonneg z.re, hnorm]
  nlinarith [norm_nonneg z]

/-- The corresponding closed subset of `ℍ`. -/
private def Kbox : Set ℍ := (↑) ⁻¹' KboxC

private lemma mem_Kbox {w : ℍ} : w ∈ Kbox ↔
    -(1 : ℝ) ≤ w.re ∧ w.re ≤ 1 ∧ (1 : ℝ) / 10 ≤ w.im ∧ w.im ≤ 2 ∧
      w.re ^ 2 + (w.im - 1) ^ 2 ≤ 1 ∧
      (1 : ℝ) / 2 + 1 / 10 ≤ ‖(w : ℂ) - (1 / 2 : ℂ)‖ ∧
      (1 : ℝ) / 2 + 1 / 10 ≤ ‖(w : ℂ) + (1 / 2 : ℂ)‖ ∧
      (1 : ℝ) / 10 ≤ ‖(w : ℂ) - ((1 : ℂ) + Complex.I)‖ ∧
      (1 : ℝ) / 10 ≤ ‖(w : ℂ) - ((-1 : ℂ) + Complex.I)‖ := by
  rw [Kbox, Set.mem_preimage, mem_KboxC, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]

private lemma isCompact_Kbox : IsCompact Kbox := by
  have hrange : KboxC ⊆ Set.range ((↑) : ℍ → ℂ) := by
    intro z hz
    rw [UpperHalfPlane.range_coe, mem_KboxC] at *
    exact lt_of_lt_of_le (by norm_num) hz.2.2.1
  exact UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' isCompact_KboxC hrange

private lemma isClosed_Kbox : IsClosed Kbox :=
  isClosed_KboxC.preimage UpperHalfPlane.continuous_coe

private lemma Kcomp_subset_Kbox : Kcomp ⊆ Kbox := by
  refine closure_minimal ?_ isClosed_Kbox
  intro w hw
  obtain ⟨hwT, hd1, hd2, hd3, hd4⟩ := hw
  obtain ⟨him1, him2, hdisk⟩ := Tregion_est hwT
  rw [mem_Tregion] at hwT
  obtain ⟨hwD, -, -⟩ := hwT
  rw [mem_Kbox]
  exact ⟨le_of_lt hwD.1, le_of_lt hwD.2.1, le_of_lt him1, him2, hdisk, hd3, hd4, hd1, hd2⟩

/-- `Kbox` avoids the two points `±1 + i` of the bad lines, which is exactly what upgrades the
weak strip bounds `-1 ≤ Re w ≤ 1` to the strict ones required by `𝒟`. -/
private lemma Kbox_subset_DomainD : Kbox ⊆ DomainD := by
  intro w hw
  rw [mem_Kbox] at hw
  obtain ⟨hre1, hre2, him1, him2, hdisk, hd1, hd2, hb1, hb2⟩ := hw
  have hre_gt : -1 < w.re := by
    rcases lt_or_eq_of_le hre1 with h | h
    · exact h
    · exfalso
      have him_eq : w.im = 1 := by nlinarith [hdisk, h, sq_nonneg (w.im - 1)]
      have hzero : (w : ℂ) - ((-1 : ℂ) + Complex.I) = 0 := by
        apply Complex.ext
        · simp [Complex.sub_re, Complex.add_re, UpperHalfPlane.coe_re, h]
        · simp [Complex.sub_im, Complex.add_im, UpperHalfPlane.coe_im, him_eq]
      rw [hzero, norm_zero] at hb2
      linarith
  have hre_lt : w.re < 1 := by
    rcases lt_or_eq_of_le hre2 with h | h
    · exact h
    · exfalso
      have him_eq : w.im = 1 := by nlinarith [hdisk, h, sq_nonneg (w.im - 1)]
      have hzero : (w : ℂ) - ((1 : ℂ) + Complex.I) = 0 := by
        apply Complex.ext
        · simp [Complex.sub_re, Complex.add_re, UpperHalfPlane.coe_re, h]
        · simp [Complex.sub_im, Complex.add_im, UpperHalfPlane.coe_im, him_eq]
      rw [hzero, norm_zero] at hb1
      linarith
  exact ⟨hre_gt, hre_lt, lt_of_lt_of_le (by norm_num) hd1, lt_of_lt_of_le (by norm_num) hd2⟩

theorem Kcomp_isCompact_subset :
    IsCompact (Work.Asymptotics.Kcomp) ∧ (Work.Asymptotics.Kcomp) ⊆ Work.Asymptotics.DomainD := by
  have hsub := Kcomp_subset_Kbox
  refine ⟨IsCompact.of_isClosed_subset isCompact_Kbox isClosed_closure hsub,
    fun w hw => Kbox_subset_DomainD (hsub hw)⟩

end Work.Asymptotics
