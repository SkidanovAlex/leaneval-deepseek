import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2C.saddleCollarRowWide
import Submission.Work.Drive.N2Lead.landingWide_band

/-!
# The flow identifications of the pin arcs

For the anchor level `a = f p - 3η/2` and the upper level `u⁺ = f p + 3η/2` (in the scaled
coordinate `ηs = (3η/2)/λ²`, `λ = ρ j / 8`), the datum flow carries the collar points of the upper
level to the anchor level by the model map `saddlePsi`, and `Work.Drive.N2Lead.collar_anchor_eq`
identifies the image with the corresponding anchor arc.
-/

set_option maxHeartbeats 1600000

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- `√(ηs + i w)` has positive real part for `ηs > 0`. -/
lemma sqrt_add_re_pos {ηs : ℝ} (hηs : 0 < ηs) (w : ℝ) :
    0 < (Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)).re := by
  apply sqrt_re_pos
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  exact hηs

section Main

variable {f : M → ℝ} {p : M}

/-- **The flow row at a collar point of the upper level, right arc.**  A point of the model chart
whose coordinate is `λ √(ηs + i w)` (the point `arcR w`) is carried by the backward flow of time
`3η` to the anchor arc `arcU w` if `w > 0` and to `arcD w` if `w < 0`. -/
lemma flowDown_arcR (D : Work.Drive.N2.WindowDatum f p) (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (S : SaddleChart D) {η ηs w δ ηb : ℝ} (hη : 0 < η)
    (hηs : ηs = 3 * η / 2 / (D.ρ D.j / 8) ^ 2)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hηs' : ηs < 1 / 10)
    (hηb : ηb = 2 * η / (D.ρ D.j / 8) ^ 2) (hηb_lt : ηb < 1 / 10)
    (hwlo : 2 - 2 * δ ≤ |w|) (hwhi : |w| ≤ 2) (hwne : w ≠ 0)
    {y : M} (hyZ : S.Zc y
        = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))
    (hyf : f y = f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) (hysrc : y ∈ S.φ'.source) :
    D.Φ (-(3 * η), y) = (if 0 < w then S.arcU ηs w else S.arcD ηs w) := by
  have hρ := D.hρ D.j
  have hlam : 0 < D.ρ D.j / 8 := by positivity
  have hlamne : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hlam
  have hηs_pos : 0 < ηs := by rw [hηs]; positivity
  have hηs_le : ηs ≤ 1 := le_of_lt (lt_trans hηs' (by norm_num))
  have hηs_nonneg : 0 ≤ ηs := le_of_lt hηs_pos
  have hηs_le_ηb : ηs ≤ ηb := by
    rw [hηs, hηb]
    have hpos : 0 < (D.ρ D.j / 8) ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    linarith
  have hlam2ηs : (D.ρ D.j / 8) ^ 2 * ηs = 3 * η / 2 := by rw [hηs]; field_simp
  have htime : f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y = -(3 * η) := by
    rw [hyf]; linarith
  -- the scaled collar coordinate
  set Z : M → ℂ := fun y => S.Zc y / (((D.ρ D.j / 8 : ℝ)) : ℂ) with hZdef
  have hZrel : ∀ y : M, S.Zc y = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y := by
    intro y; rw [hZdef]; field_simp
  have hZval : Z y = Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I) := by
    change S.Zc y / (((D.ρ D.j / 8 : ℝ)) : ℂ) = _
    rw [hyZ, mul_div_cancel_left₀ _ hlamne]
  have hZsq : (Z y) ^ 2 = (ηs : ℂ) + (w : ℂ) * Complex.I := by
    rw [hZval]; exact Work.Drive.N2.complex_sqrt_sq _
  have hZre : 0 < (Z y).re := by
    rw [hZval]; exact sqrt_add_re_pos hηs_pos w
  -- the collar condition
  have hcol : Z y ∈ Work.Drive.N2C.saddleCollarWide ηb δ := by
    simp only [Work.Drive.N2C.mem_saddleCollarWide]
    refine ⟨?_, ?_, ?_⟩
    · have hre : (Z y ^ 2).re = ηs := by rw [hZsq]; simp
      rw [hre, abs_of_nonneg hηs_nonneg]; exact hηs_le_ηb
    · have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
      rw [him]; exact hwlo
    · have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
      rw [him]; exact hwhi
  -- the collar row
  obtain ⟨hl1, -, hl3⟩ :=
    Work.Drive.N2C.saddleCollarRowWide D hsgn S.φ' S.Zc Z (D.ρ D.j / 8) rfl S.source_eq
      S.ball_eq S.Zc_eq hZrel S.level_eq S.ODE S.im_inv
      hηs_pos hηs' hδ hδ' hηb_lt hηs_le_ηb hysrc hcol
  -- the model map
  have hZre' : |(Z y ^ 2).re| ≤ ηs := by
    have hre : (Z y ^ 2).re = ηs := by rw [hZsq]; simp
    rw [hre, abs_of_nonneg hηs_nonneg]
  have hZimlo : 2 - 2 * δ ≤ |(Z y ^ 2).im| := by
    have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
    rw [him]; exact hwlo
  have hZimhi : |(Z y ^ 2).im| ≤ 2 := by
    have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
    rw [him]; exact hwhi
  obtain ⟨hpsi1, hpsi2⟩ := Work.Drive.N2.saddlePsi_collar hηs_pos hηs' hδ hδ'
    (z := Z y) hZre' hZimlo hZimhi
  have hu2 : (Work.Drive.N2.saddlePsi ηs δ (Z y)) ^ 2
      = -((ηs : ℝ) : ℂ) + (w : ℂ) * Complex.I := by
    rw [hpsi1]
    have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
    rw [him]
  have hident := collar_anchor_eq hηs_pos hwne (a := ηs) (w := w)
    (u := Work.Drive.N2.saddlePsi ηs δ (Z y)) (z := Z y) hZsq hu2 hpsi2
  rw [if_pos hZre] at hident
  -- the coordinate of the landing point
  have hcoeff : Work.Drive.N2.saddlePsi ηs δ (Z y)
      = (if 0 < w then (1 : ℂ) else -1) * (Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) := by
    rw [hident]; ring
  have hFinal : S.Zc (D.Φ (-(3 * η), y))
      = (if 0 < w then S.Zc (S.arcU ηs w) else S.Zc (S.arcD ηs w)) := by
    have ht : D.Φ (-(3 * η), y) = D.Φ (f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y, y) := by rw [htime]
    rw [ht, hZrel (D.Φ (f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y, y)), hl3, hcoeff]
    by_cases hw : 0 < w
    · rw [if_pos hw, if_pos hw, S.arcU_Zc hηs_nonneg hηs_le hwhi]
      ring
    · rw [if_neg hw, if_neg hw, S.arcD_Zc hηs_nonneg hηs_le hwhi]
      ring
  -- conclude by injectivity
  have hsrc' : D.Φ (-(3 * η), y) ∈ S.φ'.source := by
    have ht : D.Φ (-(3 * η), y) = D.Φ (f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y, y) := by rw [htime]
    rw [ht]; exact hl1
  by_cases hw : 0 < w
  · rw [if_pos hw] at hFinal ⊢
    exact S.injOn_Zc hsrc' (S.arcU_source hηs_nonneg hηs_le hwhi) hFinal
  · rw [if_neg hw] at hFinal ⊢
    exact S.injOn_Zc hsrc' (S.arcD_source hηs_nonneg hηs_le hwhi) hFinal

/-- **The flow row at a collar point of the upper level, left arc.**  A point of the model chart
whose coordinate is `-λ √(ηs + i w)` (the point `arcL w`) is carried by the backward flow of time
`3η` to the anchor arc `arcD w` if `w > 0` and to `arcU w` if `w < 0`. -/
lemma flowDown_arcL (D : Work.Drive.N2.WindowDatum f p) (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (S : SaddleChart D) {η ηs w δ ηb : ℝ} (hη : 0 < η)
    (hηs : ηs = 3 * η / 2 / (D.ρ D.j / 8) ^ 2)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hηs' : ηs < 1 / 10)
    (hηb : ηb = 2 * η / (D.ρ D.j / 8) ^ 2) (hηb_lt : ηb < 1 / 10)
    (hwlo : 2 - 2 * δ ≤ |w|) (hwhi : |w| ≤ 2) (hwne : w ≠ 0)
    {y : M} (hyZ : S.Zc y
        = -(((D.ρ D.j / 8 : ℝ)) : ℂ) * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I))
    (hyf : f y = f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) (hysrc : y ∈ S.φ'.source) :
    D.Φ (-(3 * η), y) = (if 0 < w then S.arcD ηs w else S.arcU ηs w) := by
  have hρ := D.hρ D.j
  have hlam : 0 < D.ρ D.j / 8 := by positivity
  have hlamne : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hlam
  have hηs_pos : 0 < ηs := by rw [hηs]; positivity
  have hηs_le : ηs ≤ 1 := le_of_lt (lt_trans hηs' (by norm_num))
  have hηs_nonneg : 0 ≤ ηs := le_of_lt hηs_pos
  have hηs_le_ηb : ηs ≤ ηb := by
    rw [hηs, hηb]
    have hpos : 0 < (D.ρ D.j / 8) ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    linarith
  have hlam2ηs : (D.ρ D.j / 8) ^ 2 * ηs = 3 * η / 2 := by rw [hηs]; field_simp
  have htime : f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y = -(3 * η) := by
    rw [hyf]; linarith
  set Z : M → ℂ := fun y => S.Zc y / (((D.ρ D.j / 8 : ℝ)) : ℂ) with hZdef
  have hZrel : ∀ y : M, S.Zc y = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y := by
    intro y; rw [hZdef]; field_simp
  have hZval : Z y = -Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I) := by
    change S.Zc y / (((D.ρ D.j / 8 : ℝ)) : ℂ) = _
    rw [hyZ, neg_mul, neg_div, mul_div_cancel_left₀ _ hlamne]
  have hZsq : (Z y) ^ 2 = (ηs : ℂ) + (w : ℂ) * Complex.I := by
    rw [hZval, neg_sq]; exact Work.Drive.N2.complex_sqrt_sq _
  have hZre : (Z y).re < 0 := by
    rw [hZval]; exact neg_lt_zero.mpr (sqrt_add_re_pos hηs_pos w)
  have hcol : Z y ∈ Work.Drive.N2C.saddleCollarWide ηb δ := by
    simp only [Work.Drive.N2C.mem_saddleCollarWide]
    refine ⟨?_, ?_, ?_⟩
    · have hre : (Z y ^ 2).re = ηs := by rw [hZsq]; simp
      rw [hre, abs_of_nonneg hηs_nonneg]; exact hηs_le_ηb
    · have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
      rw [him]; exact hwlo
    · have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
      rw [him]; exact hwhi
  obtain ⟨hl1, -, hl3⟩ :=
    Work.Drive.N2C.saddleCollarRowWide D hsgn S.φ' S.Zc Z (D.ρ D.j / 8) rfl S.source_eq
      S.ball_eq S.Zc_eq hZrel S.level_eq S.ODE S.im_inv
      hηs_pos hηs' hδ hδ' hηb_lt hηs_le_ηb hysrc hcol
  have hZre' : |(Z y ^ 2).re| ≤ ηs := by
    have hre : (Z y ^ 2).re = ηs := by rw [hZsq]; simp
    rw [hre, abs_of_nonneg hηs_nonneg]
  have hZimlo : 2 - 2 * δ ≤ |(Z y ^ 2).im| := by
    have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
    rw [him]; exact hwlo
  have hZimhi : |(Z y ^ 2).im| ≤ 2 := by
    have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
    rw [him]; exact hwhi
  obtain ⟨hpsi1, hpsi2⟩ := Work.Drive.N2.saddlePsi_collar hηs_pos hηs' hδ hδ'
    (z := Z y) hZre' hZimlo hZimhi
  have hu2 : (Work.Drive.N2.saddlePsi ηs δ (Z y)) ^ 2
      = -((ηs : ℝ) : ℂ) + (w : ℂ) * Complex.I := by
    rw [hpsi1]
    have him : (Z y ^ 2).im = w := by rw [hZsq]; simp
    rw [him]
  have hident := collar_anchor_eq hηs_pos hwne (a := ηs) (w := w)
    (u := Work.Drive.N2.saddlePsi ηs δ (Z y)) (z := Z y) hZsq hu2 hpsi2
  rw [if_neg (not_lt.mpr (le_of_lt hZre))] at hident
  have hFinal : S.Zc (D.Φ (-(3 * η), y))
      = (if 0 < w then S.Zc (S.arcD ηs w) else S.Zc (S.arcU ηs w)) := by
    have ht : D.Φ (-(3 * η), y) = D.Φ (f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y, y) := by rw [htime]
    rw [ht, hZrel (D.Φ (f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y, y)), hl3, hident]
    by_cases hw : 0 < w
    · rw [if_pos hw, if_pos hw, S.arcD_Zc hηs_nonneg hηs_le hwhi]
      ring
    · rw [if_neg hw, if_neg hw, S.arcU_Zc hηs_nonneg hηs_le hwhi]
      ring
  have hsrc' : D.Φ (-(3 * η), y) ∈ S.φ'.source := by
    have ht : D.Φ (-(3 * η), y) = D.Φ (f p - ((D.ρ D.j / 8)) ^ 2 * ηs - f y, y) := by rw [htime]
    rw [ht]; exact hl1
  by_cases hw : 0 < w
  · rw [if_pos hw] at hFinal ⊢
    exact S.injOn_Zc hsrc' (S.arcD_source hηs_nonneg hηs_le hwhi) hFinal
  · rw [if_neg hw] at hFinal ⊢
    exact S.injOn_Zc hsrc' (S.arcU_source hηs_nonneg hηs_le hwhi) hFinal

/-- **The four flow identifications of the pin arcs.** -/
theorem flow_arcIds (D : Work.Drive.N2.WindowDatum f p) (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (S : SaddleChart D) {η ηs c₀ δ : ℝ} (hη : 0 < η)
    (hηs : ηs = 3 * η / 2 / (D.ρ D.j / 8) ^ 2)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hηs' : ηs < 1 / 10)
    (hηb' : 2 * η / (D.ρ D.j / 8) ^ 2 < 1 / 10)
    (hc₀lo : 2 - 2 * δ ≤ c₀) (hc₀hi : c₀ ≤ 2) :
    D.Φ (3 * η, S.arcU ηs c₀) = S.arcR ηs c₀ ∧
    D.Φ (3 * η, S.arcU ηs (-c₀)) = S.arcL ηs (-c₀) ∧
    D.Φ (3 * η, S.arcD ηs c₀) = S.arcL ηs c₀ ∧
    D.Φ (3 * η, S.arcD ηs (-c₀)) = S.arcR ηs (-c₀) := by
  have hηs_pos : 0 < ηs := by
    rw [hηs]
    exact div_pos (by linarith) (pow_pos (div_pos (D.hρ D.j) (by norm_num)) 2)
  have hηs_le : ηs ≤ 1 := le_of_lt (lt_trans hηs' (by norm_num))
  have hηs_nonneg : 0 ≤ ηs := le_of_lt hηs_pos
  have hc₀pos : 0 < c₀ := by linarith
  have hc₀ne : c₀ ≠ 0 := ne_of_gt hc₀pos
  have hnegneg : ¬ (0 < -c₀) := by linarith
  have habs : |(-c₀)| = c₀ := by rw [abs_neg, abs_of_pos hc₀pos]
  have habs' : |c₀| = c₀ := abs_of_pos hc₀pos
  -- the four backward rows
  have h1 := flowDown_arcR D hsgn S hη hηs hδ hδ' hηs'
    (ηb := 2 * η / (D.ρ D.j / 8) ^ 2) rfl hηb'
    (by rw [habs']; exact hc₀lo) (by rw [habs']; exact hc₀hi) hc₀ne
    (y := S.arcR ηs c₀) (S.arcR_Zc hηs_nonneg hηs_le (by rw [habs']; exact hc₀hi))
    (S.arcR_level hηs_nonneg hηs_le (by rw [habs']; exact hc₀hi))
    (S.arcR_source hηs_nonneg hηs_le (by rw [habs']; exact hc₀hi))
  rw [if_pos hc₀pos] at h1
  have h2 := flowDown_arcL D hsgn S hη hηs hδ hδ' hηs'
    (ηb := 2 * η / (D.ρ D.j / 8) ^ 2) rfl hηb'
    (by rw [habs']; exact hc₀lo) (by rw [habs']; exact hc₀hi) hc₀ne
    (y := S.arcL ηs c₀) (by rw [S.arcL_Zc hηs_nonneg hηs_le (by rw [habs']; exact hc₀hi)]; ring)
    (S.arcL_level hηs_nonneg hηs_le (by rw [habs']; exact hc₀hi))
    (S.arcL_source hηs_nonneg hηs_le (by rw [habs']; exact hc₀hi))
  rw [if_pos hc₀pos] at h2
  have h3 := flowDown_arcR D hsgn S hη hηs hδ hδ' hηs'
    (ηb := 2 * η / (D.ρ D.j / 8) ^ 2) rfl hηb'
    (by rw [habs]; exact hc₀lo) (by rw [habs]; exact hc₀hi) (by simp [hc₀ne])
    (y := S.arcR ηs (-c₀)) (S.arcR_Zc hηs_nonneg hηs_le (by rw [habs]; exact hc₀hi))
    (S.arcR_level hηs_nonneg hηs_le (by rw [habs]; exact hc₀hi))
    (S.arcR_source hηs_nonneg hηs_le (by rw [habs]; exact hc₀hi))
  rw [if_neg hnegneg] at h3
  have h4 := flowDown_arcL D hsgn S hη hηs hδ hδ' hηs'
    (ηb := 2 * η / (D.ρ D.j / 8) ^ 2) rfl hηb'
    (by rw [habs]; exact hc₀lo) (by rw [habs]; exact hc₀hi) (by simp [hc₀ne])
    (y := S.arcL ηs (-c₀)) (by rw [S.arcL_Zc hηs_nonneg hηs_le (by rw [habs]; exact hc₀hi)]; ring)
    (S.arcL_level hηs_nonneg hηs_le (by rw [habs]; exact hc₀hi))
    (S.arcL_source hηs_nonneg hηs_le (by rw [habs]; exact hc₀hi))
  rw [if_neg hnegneg] at h4
  -- forward in time
  have step : ∀ x : M, D.Φ (3 * η, D.Φ (-(3 * η), x)) = x := by
    intro x
    rw [D.hΦcomp]
    have : 3 * η + -(3 * η) = 0 := by ring
    rw [this, D.hΦ0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1]; exact step _
  · rw [← h4]; exact step _
  · rw [← h2]; exact step _
  · rw [← h3]; exact step _

end Main

end Work.Drive.N2Lead
