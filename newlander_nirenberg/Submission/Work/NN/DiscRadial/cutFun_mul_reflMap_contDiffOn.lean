/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Smoothness of the reflected Seeley term `cutFun b · (w ∘ reflMap b)`

For `b ≥ 2` and `c > 1`, the function

`p ↦ cutFun b p * w (reflMap b p)`

is `C^k` on `U ×ˢ {z | 1 < ‖z‖ ∧ ‖z‖ < c}` whenever `w` is `C^k` on `U ×ˢ ball(0,c)`.

The point is that the cutoff `cutFun b` can only be non-zero on the annulus
`1 < ‖z‖ < 1 + 2/b`, where the radial reflection `discRefl b z` has modulus `< 1`, hence
lands strictly inside `ball(0,c)`.  Points with `‖z‖` larger than `1 + 2/b` (plus a small
margin) lie where `cutFun b` vanishes identically, so the product is there the zero function.
-/
import Mathlib
import Submission.Work.NN.DiscRadial.DiscRadialAux

noncomputable section

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.DiscRadial

open Work.NN.Final

section Aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `cutFun b` is smooth wherever `p.2 ≠ 0`. -/
private lemma contDiffOn_cutFun (b : ℝ) :
    ContDiffOn ℝ ∞ (cutFun b) {p : X × ℂ | p.2 ≠ 0} := by
  intro p hp
  have h2 : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => q.2) {p : X × ℂ | p.2 ≠ 0} p :=
    contDiffWithinAt_id.snd
  have hnorm : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => ‖q.2‖) {p : X × ℂ | p.2 ≠ 0} p :=
    ContDiffWithinAt.norm ℝ h2 hp
  have hlin : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => b * (‖q.2‖ - 1)) {p : X × ℂ | p.2 ≠ 0} p :=
    contDiffWithinAt_const.mul (hnorm.sub contDiffWithinAt_const)
  have hcut : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => seeleyCut (b * (‖q.2‖ - 1)))
      {p : X × ℂ | p.2 ≠ 0} p :=
    (seeleyCut_contDiff.contDiffWithinAt).comp p hlin (mapsTo_univ _ _)
  have hc2 : ContDiffWithinAt ℝ ∞
      (fun q : X × ℂ => ((seeleyCut (b * (‖q.2‖ - 1)) : ℝ) : ℂ)) {p : X × ℂ | p.2 ≠ 0} p :=
    (Complex.ofRealCLM.contDiff.contDiffWithinAt).comp p hcut (mapsTo_univ _ _)
  exact hc2

/-- `reflMap b` is smooth wherever `p.2 ≠ 0`. -/
private lemma contDiffOn_reflMap (b : ℝ) :
    ContDiffOn ℝ ∞ (reflMap b) {p : X × ℂ | p.2 ≠ 0} := by
  intro p hp
  have hfst : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => q.1) {p : X × ℂ | p.2 ≠ 0} p :=
    contDiffWithinAt_id.fst
  have hd : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => discRefl b q.2) {p : X × ℂ | p.2 ≠ 0} p := by
    have hg : ContDiffWithinAt ℝ ∞ (discRefl b) {z : ℂ | z ≠ 0} p.2 :=
      ((contDiffOn_discRefl b).contDiffWithinAt hp).of_le le_top
    have hf : ContDiffWithinAt ℝ ∞ (fun q : X × ℂ => q.2) {p : X × ℂ | p.2 ≠ 0} p :=
      contDiffWithinAt_id.snd
    exact hg.comp p hf (fun q hq => hq)
  exact hfst.prodMk hd

/-- The modulus of the radial reflection stays inside the disc of radius `c` on the annulus
`1 < ‖z‖ < 1 + 2/b + (c-1)/(4b)` (for `b > 0`, `c > 1`). -/
private lemma norm_discRefl_lt {b c : ℝ} (hb : 0 < b) (hc : 1 < c) {z : ℂ}
    (h1 : 1 < ‖z‖) (h2 : ‖z‖ < 1 + 2 / b + (c - 1) / (4 * b)) :
    ‖discRefl b z‖ < c := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at h1; simp only [norm_zero] at h1; linarith
  rw [norm_discRefl b hz0]
  have htpos : 0 < b * (‖z‖ - 1) := mul_pos hb (by linarith)
  have htupper : b * (‖z‖ - 1) < 2 + (c - 1) / 4 := by
    have hstep : ‖z‖ - 1 < 2 / b + (c - 1) / (4 * b) := by linarith
    calc b * (‖z‖ - 1) < b * (2 / b + (c - 1) / (4 * b)) := mul_lt_mul_of_pos_left hstep hb
      _ = 2 + (c - 1) / 4 := by field_simp
  rw [abs_lt]
  constructor <;> linarith

/-- `reflMap b` maps the annulus `1 < ‖z‖ < 1 + 2/b + (c-1)/(4b)` into `ball 0 c`. -/
private lemma mapsTo_reflMap_ball {U : Set X} {b c : ℝ} (hb : 0 < b) (hc : 1 < c) :
    MapsTo (reflMap b)
      (U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 1 + 2 / b + (c - 1) / (4 * b)})
      (U ×ˢ ball (0 : ℂ) c) := by
  intro p hp
  rw [mem_prod] at hp ⊢
  obtain ⟨hpU, hpz1, hpz2⟩ := hp
  refine ⟨hpU, ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_discRefl_lt hb hc hpz1 hpz2

/-- `cutFun b` vanishes on the region `1 + 2/b + (c-1)/(8b) < ‖z‖` (for `b ≥ 2`, `c > 1`). -/
private lemma cutFun_eq_zero_of {b c : ℝ} (hb : 2 ≤ b) (hc : 1 < c) {p : X × ℂ}
    (hp : 1 + 2 / b + (c - 1) / (8 * b) < ‖p.2‖) : cutFun b p = 0 := by
  have hb0 : 0 < b := by linarith
  have ht : 2 < b * (‖p.2‖ - 1) := by
    have h2 : 2 / b + (c - 1) / (8 * b) < ‖p.2‖ - 1 := by linarith
    have h2' : 2 < b * (2 / b + (c - 1) / (8 * b)) := by
      have heq : b * (2 / b + (c - 1) / (8 * b)) = 2 + (c - 1) / 8 := by
        field_simp
      rw [heq]; linarith
    calc 2 < b * (2 / b + (c - 1) / (8 * b)) := h2'
      _ < b * (‖p.2‖ - 1) := mul_lt_mul_of_pos_left h2 hb0
  have hsc : seeleyCut (b * (‖p.2‖ - 1)) = 0 :=
    seeleyCut_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)
  rw [cutFun, hsc]
  simp

end Aux

theorem cutFun_mul_reflMap_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {U : Set X} {c b : ℝ}
    (hb : 2 ≤ b) (hc : 1 < c)
    {w : X × ℂ → ℂ} (hw : ContDiffOn ℝ (k : WithTop ENat) w (U ×ˢ Metric.ball (0 : ℂ) c)) :
    ContDiffOn ℝ (k : WithTop ENat)
      (fun p => Work.NN.DiscRadial.cutFun b p * w (Work.NN.DiscRadial.reflMap b p))
      (U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < c}) := by
  have hb0 : 0 < b := by linarith
  have hk_le : (k : WithTop ENat) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hη'lt : (c - 1) / (8 * b) < (c - 1) / (4 * b) := by
    rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 8 * b) (by linarith : (0:ℝ) < 4 * b)]
    nlinarith
  set S : Set (X × ℂ) := U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < c} with hS
  set SA : Set (X × ℂ) := U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 1 + 2 / b + (c - 1) / (4 * b)} with hSA
  set SB : Set (X × ℂ) := U ×ˢ {z : ℂ | 1 + 2 / b + (c - 1) / (8 * b) < ‖z‖} with hSB
  intro p hp
  rw [hS, mem_prod] at hp
  obtain ⟨hpU, hpz1, hpzc⟩ := hp
  by_cases hcase : ‖p.2‖ < 1 + 2 / b + (c - 1) / (4 * b)
  · have hpSA : p ∈ SA := by
      rw [hSA, mem_prod]
      exact ⟨hpU, hpz1, hcase⟩
    have hmemA : SA ∈ 𝓝[S] p := by
      have hN : {q : X × ℂ | ‖q.2‖ < 1 + 2 / b + (c - 1) / (4 * b)} ∈ 𝓝 p :=
        (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds hcase
      have hmem : S ∩ {q : X × ℂ | ‖q.2‖ < 1 + 2 / b + (c - 1) / (4 * b)} ∈ 𝓝[S] p :=
        Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hN)
      refine Filter.mem_of_superset hmem ?_
      intro q hq
      rw [Set.mem_inter_iff] at hq
      obtain ⟨hqS, hqN⟩ := hq
      rw [hS, mem_prod] at hqS
      rw [hSA, mem_prod]
      exact ⟨hqS.1, hqS.2.1, hqN⟩
    have hcutOn : ContDiffOn ℝ ∞ (cutFun b) SA :=
      (contDiffOn_cutFun b).mono (fun q hq => by
        rw [hSA, mem_prod] at hq
        exact norm_pos_iff.mp (by linarith [hq.2.1]))
    have hcut : ContDiffWithinAt ℝ (k : WithTop ENat) (cutFun b) SA p :=
      (hcutOn.contDiffWithinAt hpSA).of_le hk_le
    have hreflOn : ContDiffOn ℝ ∞ (reflMap b) SA :=
      (contDiffOn_reflMap b).mono (fun q hq => by
        rw [hSA, mem_prod] at hq
        exact norm_pos_iff.mp (by linarith [hq.2.1]))
    have hrefl : ContDiffWithinAt ℝ (k : WithTop ENat) (reflMap b) SA p :=
      (hreflOn.contDiffWithinAt hpSA).of_le hk_le
    have hmap : MapsTo (reflMap b) SA (U ×ˢ ball (0 : ℂ) c) := by
      rw [hSA]; exact mapsTo_reflMap_ball hb0 hc
    have hw' : ContDiffWithinAt ℝ (k : WithTop ENat) w (U ×ˢ ball (0 : ℂ) c) (reflMap b p) :=
      hw.contDiffWithinAt (hmap hpSA)
    have hcomp : ContDiffWithinAt ℝ (k : WithTop ENat) (w ∘ reflMap b) SA p :=
      hw'.comp p hrefl hmap
    have hprod : ContDiffWithinAt ℝ (k : WithTop ENat)
        (fun q => cutFun b q * w (reflMap b q)) SA p := by
      simpa only [Function.comp_apply] using hcut.mul hcomp
    exact hprod.mono_of_mem_nhdsWithin hmemA
  · simp only [not_lt] at hcase
    have hpSB : p ∈ SB := by
      rw [hSB, mem_prod]
      refine ⟨hpU, ?_⟩
      show 1 + 2 / b + (c - 1) / (8 * b) < ‖p.2‖
      linarith [hcase, hη'lt]
    have hmemB : SB ∈ 𝓝[S] p := by
      have hN : {q : X × ℂ | 1 + 2 / b + (c - 1) / (8 * b) < ‖q.2‖} ∈ 𝓝 p :=
        (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
          (show 1 + 2 / b + (c - 1) / (8 * b) < ‖p.2‖ from by linarith [hcase, hη'lt])
      have hmem : S ∩ {q : X × ℂ | 1 + 2 / b + (c - 1) / (8 * b) < ‖q.2‖} ∈ 𝓝[S] p :=
        Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hN)
      refine Filter.mem_of_superset hmem ?_
      intro q hq
      rw [Set.mem_inter_iff] at hq
      obtain ⟨hqS, hqN⟩ := hq
      rw [hS, mem_prod] at hqS
      rw [hSB, mem_prod]
      exact ⟨hqS.1, hqN⟩
    have hzero : ∀ q ∈ SB, (fun p => cutFun b p * w (reflMap b p)) q = 0 := by
      intro q hq
      rw [hSB, mem_prod] at hq
      show cutFun b q * w (reflMap b q) = 0
      rw [cutFun_eq_zero_of hb hc hq.2, zero_mul]
    have hzeroCt : ContDiffWithinAt ℝ (k : WithTop ENat)
        (fun q => cutFun b q * w (reflMap b q)) SB p := by
      have hconst : ContDiffWithinAt ℝ (k : WithTop ENat)
          (fun _ : X × ℂ => (0 : ℂ)) SB p := contDiffWithinAt_const
      exact hconst.congr hzero (hzero p hpSB)
    exact hzeroCt.mono_of_mem_nhdsWithin hmemB

end Work.NN.DiscRadial
