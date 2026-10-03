import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.Cont.Defs
import Submission.Work.FatouCH.Cont.SradGeo
import Submission.Work.FatouCH.Cont.ChainBound
import Submission.Work.FatouCH.Cont.DerivApprox
import Submission.Work.FatouCH.Cont.AbelTransfer
import Submission.Work.FatouCH.Cont.InjOfTendsto
import Submission.Work.FatouCH.FC.abelPair
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.Normal.exists_compact_exhaustion
import Submission.Work.Normal.exists_subseq_tendstoLocallyUniformlyOn_of_exhaustion
import Submission.Work.Normal.exists_subseq_tendstoUniformlyOn_of_locallyBounded
import Submission.Work.Fatou.Analysis.isFatouCoordOfLimit

namespace Work.Fatou.Analysis

open Set Metric Filter Complex
open scoped Topology

noncomputable section

/-! ## Elementary properties of the safe radius `srad` -/

/-- The left-cone term `z ↦ ½ (Re (z-a) + |Im (z-a)|)` is `1`-Lipschitz. -/
lemma abs_s1_le (a u v : ℂ) :
    |(1 / 2) * ((u - a).re + |(u - a).im|) - (1 / 2) * ((v - a).re + |(v - a).im|)| ≤ ‖u - v‖ := by
  have h1 : |(u - a).re - (v - a).re| ≤ ‖u - v‖ := by
    have h := Complex.abs_re_le_norm (u - v)
    rw [Complex.sub_re] at h
    simpa [Complex.sub_re] using h
  have h2 : |(u - a).im - (v - a).im| ≤ ‖u - v‖ := by
    have h := Complex.abs_im_le_norm (u - v)
    rw [Complex.sub_im] at h
    simpa [Complex.sub_im] using h
  have h3 : |abs ((u - a).im) - abs ((v - a).im)| ≤ ‖u - v‖ :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans h2
  have heq : (1 / 2) * ((u - a).re + |(u - a).im|) - (1 / 2) * ((v - a).re + |(v - a).im|)
      = (1 / 2) * ((u - a).re - (v - a).re) + (1 / 2) * (|(u - a).im| - |(v - a).im|) := by
    ring
  rw [heq]
  calc |(1 / 2) * ((u - a).re - (v - a).re) + (1 / 2) * (|(u - a).im| - |(v - a).im|)|
      ≤ |(1 / 2) * ((u - a).re - (v - a).re)| + |(1 / 2) * (|(u - a).im| - |(v - a).im|)| :=
        abs_add_le _ _
    _ = (1 / 2) * |(u - a).re - (v - a).re| + (1 / 2) * |abs ((u - a).im) - abs ((v - a).im)| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ (1 / 2) * ‖u - v‖ + (1 / 2) * ‖u - v‖ := by linarith [h1, h3]
    _ = ‖u - v‖ := by ring

/-- The right-cone term `z ↦ ½ (|Im (z-b)| - Re (z-b))` is `1`-Lipschitz. -/
lemma abs_s2_le (b u v : ℂ) :
    |(1 / 2) * (|(u - b).im| - (u - b).re) - (1 / 2) * (|(v - b).im| - (v - b).re)| ≤ ‖u - v‖ := by
  have h1 : |(u - b).re - (v - b).re| ≤ ‖u - v‖ := by
    have h := Complex.abs_re_le_norm (u - v)
    rw [Complex.sub_re] at h
    simpa [Complex.sub_re] using h
  have h2 : |(u - b).im - (v - b).im| ≤ ‖u - v‖ := by
    have h := Complex.abs_im_le_norm (u - v)
    rw [Complex.sub_im] at h
    simpa [Complex.sub_im] using h
  have h3 : |abs ((u - b).im) - abs ((v - b).im)| ≤ ‖u - v‖ :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans h2
  have heq : (1 / 2) * (|(u - b).im| - (u - b).re) - (1 / 2) * (|(v - b).im| - (v - b).re)
      = (1 / 2) * (|(u - b).im| - |(v - b).im|) - (1 / 2) * ((u - b).re - (v - b).re) := by
    ring
  rw [heq]
  calc |(1 / 2) * (|(u - b).im| - |(v - b).im|) - (1 / 2) * ((u - b).re - (v - b).re)|
      ≤ |(1 / 2) * (|(u - b).im| - |(v - b).im|)| + |(1 / 2) * ((u - b).re - (v - b).re)| := by
        rw [sub_eq_add_neg]
        exact le_trans (abs_add_le _ _) (by rw [abs_neg])
    _ = (1 / 2) * |abs ((u - b).im) - abs ((v - b).im)| + (1 / 2) * |(u - b).re - (v - b).re| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ (1 / 2) * ‖u - v‖ + (1 / 2) * ‖u - v‖ := by linarith [h1, h3]
    _ = ‖u - v‖ := by ring

/-- `srad b₁ b₂` is `1`-Lipschitz. -/
lemma srad_lipschitz (b₁ b₂ : Option ℂ) (u v : ℂ) :
    |Work.FatouCH.srad b₁ b₂ u - Work.FatouCH.srad b₁ b₂ v| ≤ ‖u - v‖ := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · rw [show Work.FatouCH.srad (none : Option ℂ) none u = 1 + ‖u‖ from by simp [Work.FatouCH.srad],
          show Work.FatouCH.srad (none : Option ℂ) none v = 1 + ‖v‖ from by simp [Work.FatouCH.srad]]
      have := abs_norm_sub_norm_le u v
      simpa using this
    · rw [show Work.FatouCH.srad (none : Option ℂ) (some b) u
            = (1 / 2) * (|(u - b).im| - (u - b).re) from by simp [Work.FatouCH.srad],
          show Work.FatouCH.srad (none : Option ℂ) (some b) v
            = (1 / 2) * (|(v - b).im| - (v - b).re) from by simp [Work.FatouCH.srad]]
      exact abs_s2_le b u v
  · rcases b₂ with _ | b
    · rw [show Work.FatouCH.srad (some a) (none : Option ℂ) u
            = (1 / 2) * ((u - a).re + |(u - a).im|) from by simp [Work.FatouCH.srad],
          show Work.FatouCH.srad (some a) (none : Option ℂ) v
            = (1 / 2) * ((v - a).re + |(v - a).im|) from by simp [Work.FatouCH.srad]]
      exact abs_s1_le a u v
    · rw [show Work.FatouCH.srad (some a) (some b) u
            = min ((1 / 2) * ((u - a).re + |(u - a).im|))
                ((1 / 2) * (|(u - b).im| - (u - b).re)) from by simp [Work.FatouCH.srad],
          show Work.FatouCH.srad (some a) (some b) v
            = min ((1 / 2) * ((v - a).re + |(v - a).im|))
                ((1 / 2) * (|(v - b).im| - (v - b).re)) from by simp [Work.FatouCH.srad]]
      refine le_trans (abs_min_sub_min_le_max _ _ _ _) ?_
      exact max_le (abs_s1_le a u v) (abs_s2_le b u v)

/-- `srad` is positive exactly on the region. -/
lemma srad_pos_iff {b₁ b₂ : Option ℂ} {z : ℂ} :
    0 < Work.FatouCH.srad b₁ b₂ z ↔ z ∈ MandelDim.Qreg b₁ b₂ := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · rw [show Work.FatouCH.srad (none : Option ℂ) none z = 1 + ‖z‖ from by
            simp [Work.FatouCH.srad],
          show MandelDim.Qreg (none : Option ℂ) none = univ from by
            ext w; simp [MandelDim.Qreg, Option.mem_def]]
      exact ⟨fun _ => trivial, fun _ => by positivity⟩
    · rw [show Work.FatouCH.srad (none : Option ℂ) (some b) z
            = (1 / 2) * (|(z - b).im| - (z - b).re) from by simp [Work.FatouCH.srad],
          show MandelDim.Qreg (none : Option ℂ) (some b) = {w : ℂ | (w - b).re < |(w - b).im|}
            from by ext w; simp [MandelDim.Qreg, Option.mem_def]]
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
  · rcases b₂ with _ | b
    · rw [show Work.FatouCH.srad (some a) (none : Option ℂ) z
            = (1 / 2) * ((z - a).re + |(z - a).im|) from by simp [Work.FatouCH.srad],
          show MandelDim.Qreg (some a) (none : Option ℂ) = {w : ℂ | -|(w - a).im| < (w - a).re}
            from by ext w; simp [MandelDim.Qreg, Option.mem_def]]
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    · rw [show Work.FatouCH.srad (some a) (some b) z
            = min ((1 / 2) * ((z - a).re + |(z - a).im|))
                ((1 / 2) * (|(z - b).im| - (z - b).re)) from by simp [Work.FatouCH.srad],
          show MandelDim.Qreg (some a) (some b) =
              {w : ℂ | -|(w - a).im| < (w - a).re ∧ (w - b).re < |(w - b).im|}
            from by ext w; simp [MandelDim.Qreg, Option.mem_def]]
      simp only [Set.mem_ofPred_eq, lt_min_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩


/-- The safe radius of the spine tends to infinity along the spine: for every `R₁ > 0` and every
lower bound `C` there is `T ≥ C` with `srad (spineRe + T i) ≥ 2 R₁`. -/
lemma spineGrowOfSpine {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) (R₁ : ℝ) (hR₁ : 0 < R₁)
    (C : ℝ) : ∃ T : ℝ, C ≤ T ∧ 2 * R₁ ≤
      Work.FatouCH.srad b₁ b₂ (Work.FatouCH.spineRe b₁ b₂ + T * Complex.I) := by
  rcases b₁ with _ | a
  · rcases b₂ with _ | b
    · refine ⟨max C (2 * R₁), le_max_left _ _, ?_⟩
      simp only [Work.FatouCH.spineRe, Work.FatouCH.srad]
      have hge : (0:ℝ) ≤ max C (2*R₁) := le_trans (by linarith) (le_max_right C (2*R₁))
      rw [Complex.ofReal_zero, zero_add]
      have him : ((((max C (2*R₁) : ℝ)) : ℂ) * Complex.I).im = max C (2*R₁) := by simp
      have h3 := Complex.abs_im_le_norm ((((max C (2*R₁) : ℝ)) : ℂ) * Complex.I)
      rw [him, abs_of_nonneg hge] at h3
      linarith [le_max_right C (2*R₁)]
    · refine ⟨max C b.im + 4 * R₁, le_trans (le_max_left C b.im) (by linarith), ?_⟩
      have hsp : Work.FatouCH.spineRe (none : Option ℂ) (some b) = b.re - 2 := by
        simp [Work.FatouCH.spineRe]
      rw [hsp]
      have him : (↑(b.re - 2) + ↑(max C b.im + 4 * R₁) * Complex.I - b).im
          = max C b.im + 4 * R₁ - b.im := by simp
      have hre : (↑(b.re - 2) + ↑(max C b.im + 4 * R₁) * Complex.I - b).re
          = -2 := by simp
      have hTb : b.im ≤ max C b.im := le_max_right C b.im
      have hnn : (0:ℝ) ≤ max C b.im + 4 * R₁ - b.im := by linarith
      simp only [Work.FatouCH.srad]
      rw [hre, him, abs_of_nonneg hnn]
      linarith
  · rcases b₂ with _ | b
    · refine ⟨max C a.im + 4 * R₁, le_trans (le_max_left C a.im) (by linarith), ?_⟩
      have hsp : Work.FatouCH.spineRe (some a) (none : Option ℂ) = a.re + 2 := by
        simp [Work.FatouCH.spineRe]
      rw [hsp]
      have him : (↑(a.re + 2) + ↑(max C a.im + 4 * R₁) * Complex.I - a).im
          = max C a.im + 4 * R₁ - a.im := by simp
      have hre : (↑(a.re + 2) + ↑(max C a.im + 4 * R₁) * Complex.I - a).re = 2 := by simp
      have hTa : a.im ≤ max C a.im := le_max_right C a.im
      have hnn : (0:ℝ) ≤ max C a.im + 4 * R₁ - a.im := by linarith
      simp only [Work.FatouCH.srad]
      rw [hre, him, abs_of_nonneg hnn]
      linarith
    · have hab : a.re + 4 < b.re := hAdm a (by simp) b (by simp)
      have hsp : Work.FatouCH.spineRe (some a) (some b) = (a.re + b.re)/2 := by
        simp [Work.FatouCH.spineRe]
      refine ⟨max C (max a.im b.im) + 4 * R₁, le_trans (le_max_left C _) (by linarith), ?_⟩
      rw [hsp]
      have hTa : a.im ≤ max C (max a.im b.im) := le_trans (le_max_left a.im b.im) (le_max_right C _)
      have hTb : b.im ≤ max C (max a.im b.im) := le_trans (le_max_right a.im b.im) (le_max_right C _)
      have hnn_a : (0:ℝ) ≤ max C (max a.im b.im) + 4 * R₁ - a.im := by linarith
      have hnn_b : (0:ℝ) ≤ max C (max a.im b.im) + 4 * R₁ - b.im := by linarith
      have hreA : (↑((a.re + b.re)/2) + ↑(max C (max a.im b.im) + 4 * R₁) * Complex.I - a).re
          = (b.re - a.re)/2 := by
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, sub_zero]
        ring
      have himA : (↑((a.re + b.re)/2) + ↑(max C (max a.im b.im) + 4 * R₁) * Complex.I - a).im
          = max C (max a.im b.im) + 4 * R₁ - a.im := by
        simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add]
        ring
      have hreB : (↑((a.re + b.re)/2) + ↑(max C (max a.im b.im) + 4 * R₁) * Complex.I - b).re
          = (a.re - b.re)/2 := by
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, sub_zero]
        ring
      have himB : (↑((a.re + b.re)/2) + ↑(max C (max a.im b.im) + 4 * R₁) * Complex.I - b).im
          = max C (max a.im b.im) + 4 * R₁ - b.im := by
        simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add]
        ring
      simp only [Work.FatouCH.srad]
      rw [hreA, himA, hreB, himB, abs_of_nonneg hnn_a, abs_of_nonneg hnn_b]
      apply le_min <;> linarith

private lemma norm_convex_le {x y : ℂ} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) : ‖(1 - θ) • x + θ • y‖ ≤ R := by
  have h1 : ‖(1 - θ) • x‖ ≤ (1 - θ) * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hθ.2] : (0 : ℝ) ≤ 1 - θ)]
    exact mul_le_mul_of_nonneg_left hx (by linarith [hθ.2])
  have h2 : ‖θ • y‖ ≤ θ * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact mul_le_mul_of_nonneg_left hy hθ.1
  calc ‖(1 - θ) • x + θ • y‖ ≤ ‖(1 - θ) • x‖ + ‖θ • y‖ := norm_add_le _ _
    _ ≤ (1 - θ) * R + θ * R := add_le_add h1 h2
    _ = R := by ring

/-- Norm of a real number seen as a complex number. -/
private lemma norm_coe (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- Norm of `r · i`. -/
private lemma norm_coe_mul_I (r : ℝ) : ‖((r : ℝ) : ℂ) * Complex.I‖ = |r| := by simp

/-- Difference of two points of the vertical line through `m`. -/
private lemma vert_diff (m T a b : ℝ) :
    ((m : ℂ) + ((T - a : ℝ) : ℂ) * Complex.I) - ((m : ℂ) + ((T - b : ℝ) : ℂ) * Complex.I)
      = (((b - a : ℝ)) : ℂ) * Complex.I := by
  push_cast; ring

/-- Difference of two points of the segment from `q` to `z`. -/
private lemma horiz_diff (q z : ℂ) (a b : ℝ) :
    (q + (a : ℂ) * (z - q)) - (q + (b : ℂ) * (z - q)) = ((a - b : ℝ) : ℂ) * (z - q) := by
  push_cast; ring

/-- The point `q + θ (z - q)` is the convex combination of `q` and `z` with weights `1 - θ`, `θ`. -/
private lemma convex_eq (q z : ℂ) (θ : ℝ) :
    q + (θ : ℂ) * (z - q) = (1 - θ) • q + θ • z := by
  simp only [Complex.real_smul]; push_cast; ring

theorem walkOfSpine {b₁ b₂ : Option ℂ} (hAdm : MandelDim.QAdm b₁ b₂) {R₁ : ℝ} (hR₁ : 0 < R₁)
    {K : Set ℂ} (hKc : IsCompact K) (hKQ : K ⊆ MandelDim.Qreg b₁ b₂) :
    ∃ (T : ℝ) (Nmax : ℕ) (B sr : ℝ) (p₀ : ℂ),
      p₀ = Work.FatouCH.spineRe b₁ b₂ + T * Complex.I ∧
      (2 * R₁) ≤ Work.FatouCH.srad b₁ b₂ p₀ ∧ 0 < sr ∧
      (∀ z ∈ K, ∃ (N : ℕ) (p : ℕ → ℂ),
        N ≤ Nmax ∧ p 0 = p₀ ∧ p N = z ∧
        (∀ i ≤ N, ‖p i‖ ≤ B ∧ Work.FatouCH.srad b₁ b₂ (p i) ≤ B ∧
          sr ≤ Work.FatouCH.srad b₁ b₂ (p i)) ∧
        (∀ i < N, ‖p (i + 1) - p i‖ ≤ (1 / 4) * Work.FatouCH.srad b₁ b₂ (p i))) := by
  classical
  obtain ⟨-, -, -, -, hspine, -, -, hseg, -⟩ := Work.FatouCH.Cont.SradGeo hAdm
  obtain ⟨δ, hδpos, hδK⟩ := Work.FatouCH.exists_min_srad_of_isCompact hKc hKQ
  obtain ⟨Rv, hRvpos, hRv⟩ := hKc.isBounded.exists_pos_norm_le
  obtain ⟨T, hTC, hTa⟩ := spineGrowOfSpine hAdm R₁ hR₁ (Rv + 1)
  have hTpos : 0 < T := by linarith
  set m : ℝ := Work.FatouCH.spineRe b₁ b₂ with hm
  let s : ℝ := min 1 δ / 8
  have hspos : 0 < s := by
    have h1 : 0 < min (1 : ℝ) δ := lt_min one_pos hδpos
    simp only [s]; linarith
  have hmin8 : min (1 : ℝ) δ = 8 * s := by simp only [s]; ring
  let Bv : ℝ := |m| + T + 2 * Rv + 1
  have hBvnn : 0 ≤ Bv := by simp only [Bv]; positivity
  obtain ⟨w, hwmem, hwmax⟩ := (isCompact_closedBall (0 : ℂ) Bv).exists_isMaxOn
     (Metric.nonempty_closedBall.mpr hBvnn) (Work.FatouCH.continuous_srad b₁ b₂).continuousOn
  let B : ℝ := max Bv (Work.FatouCH.srad b₁ b₂ w)
  have hBsrad : ∀ y : ℂ, ‖y‖ ≤ Bv → Work.FatouCH.srad b₁ b₂ y ≤ B := by
    intro y hy
    exact le_trans (hwmax (by simpa [Metric.mem_closedBall, dist_eq_norm] using hy))
      (le_max_right _ _)
  have hBnorm : ∀ y : ℂ, ‖y‖ ≤ Bv → ‖y‖ ≤ B := fun y hy => le_trans hy (le_max_left _ _)
  let Nmax : ℕ := ⌈(T + Rv) / s⌉₊ + ⌈(|m| + 2 * Rv) / s⌉₊
  refine ⟨T, Nmax, B, min 1 δ, (m : ℂ) + (T : ℂ) * Complex.I, rfl, hTa,
    lt_min one_pos hδpos, ?_⟩
  intro z hzK
  have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := hKQ hzK
  have hzn : ‖z‖ ≤ Rv := hRv z hzK
  have hzim : |z.im| ≤ Rv := le_trans (Complex.abs_im_le_norm z) hzn
  have hzimm : -Rv ≤ z.im ∧ z.im ≤ Rv := abs_le.mp hzim
  set q : ℂ := m + z.im * Complex.I with hq
  have hqnorm : ‖q‖ ≤ |m| + Rv := by
    rw [hq]
    calc ‖(m : ℂ) + (z.im : ℂ) * Complex.I‖
        ≤ ‖(m : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |m| + |z.im| := by rw [norm_coe, norm_coe_mul_I]
      _ ≤ |m| + Rv := by linarith [hzim]
  set Lv : ℝ := T - z.im with hLv
  have hLvpos : 0 < Lv := by rw [hLv]; linarith [hTC, hzimm.2]
  set Lh : ℝ := ‖z - q‖ with hLh
  have hLhnn : 0 ≤ Lh := by rw [hLh]; positivity
  let Nv : ℕ := ⌈Lv / s⌉₊
  let Nh : ℕ := ⌈Lh / s⌉₊
  let θ : ℕ → ℝ := fun i => ((i - Nv : ℕ) : ℝ) / Nh
  let p : ℕ → ℂ := fun i =>
    if i ≤ Nv then (m : ℂ) + ((T - (i : ℝ) * (Lv / (Nv : ℝ)) : ℝ) : ℂ) * Complex.I
    else q + ((θ i : ℝ) : ℂ) * (z - q)
  have hNvpos : 0 < Nv := by
    have h1 : 0 < Lv / s := div_pos hLvpos hspos
    have h2 : Lv / s ≤ (Nv : ℝ) := by simp only [Nv]; exact Nat.le_ceil _
    exact_mod_cast (lt_of_lt_of_le h1 h2)
  have hNvne : (Nv : ℝ) ≠ 0 := by exact_mod_cast hNvpos.ne'
  have hNhpos : 0 < Lh → 0 < Nh := by
    intro hLhpos
    have h1 : 0 < Lh / s := div_pos hLhpos hspos
    have h2 : Lh / s ≤ (Nh : ℝ) := by simp only [Nh]; exact Nat.le_ceil _
    exact_mod_cast (lt_of_lt_of_le h1 h2)
  have hLvNv : Lv / (Nv : ℝ) ≤ s := by
    have h2 : Lv / s ≤ (Nv : ℝ) := by simp only [Nv]; exact Nat.le_ceil _
    have h3 : Lv ≤ (Nv : ℝ) * s := by
      have h4 := mul_le_mul_of_nonneg_right h2 hspos.le
      rwa [div_mul_cancel₀ Lv hspos.ne'] at h4
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Nv : ℝ))]
    linarith
  have hLhNh : Lh / (Nh : ℝ) ≤ s := by
    rcases eq_or_lt_of_le hLhnn with h0 | hpos
    · rw [← h0]; simp only [zero_div]; exact hspos.le
    · have hNhpos' : (0 : ℝ) < (Nh : ℝ) := by exact_mod_cast (hNhpos hpos)
      have h2 : Lh / s ≤ (Nh : ℝ) := by simp only [Nh]; exact Nat.le_ceil _
      have h3 : Lh ≤ (Nh : ℝ) * s := by
        have h4 := mul_le_mul_of_nonneg_right h2 hspos.le
        rwa [div_mul_cancel₀ Lh hspos.ne'] at h4
      rw [div_le_iff₀ hNhpos']
      linarith
  have hpNv : p Nv = q := by
    simp only [p, if_pos (le_refl Nv)]
    rw [mul_div_cancel₀ Lv hNvne, hLv]
    rw [show T - (T - z.im) = z.im by ring, ← hq]
  have hNle : Nv + Nh ≤ Nmax := by
    have h1 : Nv ≤ ⌈(T + Rv) / s⌉₊ := by
      simp only [Nv]; apply Nat.ceil_mono
      apply div_le_div_of_nonneg_right _ hspos.le
      rw [hLv]; linarith [hzimm.1]
    have h2 : Nh ≤ ⌈(|m| + 2 * Rv) / s⌉₊ := by
      simp only [Nh]; apply Nat.ceil_mono
      apply div_le_div_of_nonneg_right _ hspos.le
      rw [hLh]
      calc ‖z - q‖ ≤ ‖z‖ + ‖q‖ := norm_sub_le z q
        _ ≤ Rv + (|m| + Rv) := add_le_add hzn hqnorm
        _ ≤ |m| + 2 * Rv := by linarith
    simp only [Nmax]; exact add_le_add h1 h2
  have hp0 : p 0 = (m : ℂ) + (T : ℂ) * Complex.I := by
    simp only [p, if_pos (Nat.zero_le Nv)]
    norm_num
  have hθIcc : ∀ i, ¬ i ≤ Nv → i ≤ Nv + Nh → θ i ∈ Icc 0 1 := by
    intro i h1 h2
    have hNh1 : 1 ≤ Nh := by omega
    refine ⟨?_, ?_⟩
    · simp only [θ]; positivity
    · simp only [θ]
      rw [div_le_one (by positivity : (0 : ℝ) < (Nh : ℝ))]
      exact_mod_cast (Nat.sub_le_iff_le_add.mpr (by omega : i ≤ Nh + Nv))
  have hmemseg : ∀ i, ¬ i ≤ Nv → i ≤ Nv + Nh → p i ∈ segment ℝ z q := by
    intro i h1 h2
    obtain ⟨hθ0, hθ1⟩ := hθIcc i h1 h2
    rw [segment_symm, segment_eq_image]
    refine ⟨θ i, ⟨hθ0, hθ1⟩, ?_⟩
    simp only [p, if_neg h1]
    rw [convex_eq]
  have hpN : p (Nv + Nh) = z := by
    rcases eq_or_lt_of_le hLhnn with hL0 | hLpos
    · have hzq : z = q := by
        have h0 : ‖z - q‖ = 0 := by rw [← hLh]; exact hL0.symm
        exact sub_eq_zero.mp (norm_eq_zero.mp h0)
      have hNh0 : Nh = 0 := by
        simp only [Nh]; rw [← hL0]; simp
      have hcast : (Nv + Nh : ℕ) = Nv := by rw [hNh0, Nat.add_zero]
      rw [hcast, hpNv]
      exact hzq.symm
    · have hNh1 : 1 ≤ Nh := Nat.one_le_iff_ne_zero.mpr (hNhpos hLpos).ne'
      have hgt : ¬ (Nv + Nh ≤ Nv) := by omega
      have hsub : (Nv + Nh - Nv : ℕ) = Nh := by omega
      have hθ1 : θ (Nv + Nh) = 1 := by
        simp only [θ]
        rw [hsub]
        push_cast
        exact div_self (by positivity : ((Nh : ℕ) : ℝ) ≠ 0)
      simp only [p, if_neg hgt]
      rw [hθ1]
      push_cast
      ring
  have hnorm : ∀ i, i ≤ Nv + Nh → ‖p i‖ ≤ Bv := by
    intro i hi
    by_cases hiv : i ≤ Nv
    · have hx0 : 0 ≤ (i : ℝ) * (Lv / (Nv : ℝ)) := by positivity
      have hxL : (i : ℝ) * (Lv / (Nv : ℝ)) ≤ Lv := by
        have hile : (i : ℝ) ≤ (Nv : ℝ) := by exact_mod_cast hiv
        calc (i : ℝ) * (Lv / (Nv : ℝ)) ≤ (Nv : ℝ) * (Lv / (Nv : ℝ)) :=
              mul_le_mul_of_nonneg_right hile (by positivity)
          _ = Lv := mul_div_cancel₀ Lv hNvne
      have hxT : |T - (i : ℝ) * (Lv / (Nv : ℝ))| ≤ T := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 : T - Lv = z.im := by rw [hLv]; ring
          linarith [hzimm.1]
        · linarith
      simp only [p, if_pos hiv]
      calc ‖(m : ℂ) + ((T - (i : ℝ) * (Lv / (Nv : ℝ)) : ℝ) : ℂ) * Complex.I‖
          ≤ ‖(m : ℂ)‖ + ‖((T - (i : ℝ) * (Lv / (Nv : ℝ)) : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |m| + |T - (i : ℝ) * (Lv / (Nv : ℝ))| := by rw [norm_coe, norm_coe_mul_I]
        _ ≤ |m| + T := by linarith
        _ ≤ Bv := by simp only [Bv]; linarith
    · obtain ⟨hθ0, hθ1⟩ := hθIcc i hiv hi
      have hqB : ‖q‖ ≤ Bv := by simp only [Bv]; linarith [hqnorm, abs_nonneg m]
      have hzB : ‖z‖ ≤ Bv := by simp only [Bv]; linarith [hzn, abs_nonneg m]
      simp only [p, if_neg hiv]
      rw [convex_eq]
      exact norm_convex_le hqB hzB ⟨hθ0, hθ1⟩
  have hsradlow : ∀ i, i ≤ Nv + Nh → min (1 : ℝ) δ ≤ Work.FatouCH.srad b₁ b₂ (p i) := by
    intro i hi
    by_cases hiv : i ≤ Nv
    · simp only [p, if_pos hiv]
      exact le_trans (min_le_left 1 δ) (hspine (T - (i : ℝ) * (Lv / (Nv : ℝ)))).2
    · exact le_trans (min_le_min le_rfl (hδK z hzK)) (hseg z (p i) hzQ (hmemseg i hiv hi)).1
  have hmemQ : ∀ i, i ≤ Nv + Nh → p i ∈ MandelDim.Qreg b₁ b₂ := by
    intro i hi
    by_cases hiv : i ≤ Nv
    · simp only [p, if_pos hiv]
      exact (hspine (T - (i : ℝ) * (Lv / (Nv : ℝ)))).1
    · exact (hseg z (p i) hzQ (hmemseg i hiv hi)).2
  have hstep : ∀ i, i < Nv + Nh → ‖p (i + 1) - p i‖ ≤ s := by
    intro i hi
    rcases lt_or_ge Nv (i + 1) with h1 | h1
    · have hNh1 : 1 ≤ Nh := by omega
      have hNhpos' : (0 : ℝ) < (Nh : ℝ) := by exact_mod_cast hNh1
      have heq : p (i + 1) - p i = ((1 / (Nh : ℝ) : ℝ) : ℂ) * (z - q) := by
        by_cases h2 : i ≤ Nv
        · have h2e : i = Nv := by omega
          have hθi : θ (Nv + 1) = 1 / (Nh : ℝ) := by
            simp only [θ]
            have hsub : (Nv + 1 - Nv : ℕ) = 1 := by omega
            rw [hsub]; push_cast; ring
          rw [h2e, hpNv]
          simp only [p, if_neg (by omega : ¬ (Nv + 1) ≤ Nv)]
          rw [hθi]
          ring
        · have hθdiff : θ (i + 1) - θ i = 1 / (Nh : ℝ) := by
            simp only [θ]
            have hsub : (i + 1 - Nv : ℕ) = (i - Nv) + 1 := by omega
            rw [hsub]; push_cast; field_simp; ring
          simp only [p, if_neg (by omega : ¬ (i + 1) ≤ Nv), if_neg h2]
          rw [horiz_diff, hθdiff]
      rw [heq]
      have hnn : ‖((1 / (Nh : ℝ) : ℝ) : ℂ) * (z - q)‖ = (1 / (Nh : ℝ)) * Lh := by
        rw [norm_mul, ← hLh, norm_coe, abs_of_nonneg (le_of_lt (one_div_pos.mpr hNhpos'))]
      rw [hnn]
      have hrr : (1 / (Nh : ℝ)) * Lh = Lh / (Nh : ℝ) := by ring
      rw [hrr]
      exact hLhNh
    · have hiv : i ≤ Nv := by omega
      have heq : p (i + 1) - p i = (((-(Lv / (Nv : ℝ))) : ℝ) : ℂ) * Complex.I := by
        simp only [p, if_pos h1, if_pos hiv]
        rw [vert_diff]
        have hsub : (i : ℝ) * (Lv / (Nv : ℝ)) - ((i + 1 : ℕ) : ℝ) * (Lv / (Nv : ℝ))
            = -(Lv / (Nv : ℝ)) := by
          push_cast; ring
        rw [hsub]
      rw [heq]
      rw [norm_coe_mul_I, abs_neg, abs_of_nonneg (by positivity)]
      exact hLvNv
  refine ⟨Nv + Nh, p, hNle, hp0, hpN, ?_, ?_⟩
  · intro i hi
    exact ⟨hBnorm (p i) (hnorm i hi), hBsrad (p i) (hnorm i hi),
      hsradlow i hi⟩
  · intro i hi
    refine le_trans (hstep i hi) ?_
    calc s ≤ (1 / 4) * min (1 : ℝ) δ := by rw [hmin8]; linarith
      _ ≤ (1 / 4) * Work.FatouCH.srad b₁ b₂ (p i) :=
          mul_le_mul_of_nonneg_left (hsradlow i (le_of_lt hi)) (by norm_num)


theorem localBoundOf (hD : MandelDim.FatouDerivEstimate) {b₁ b₂ : ℕ → Option ℂ}
    {c₁ c₂ : Option ℂ} {F : ℕ → ℂ → ℂ} {Φ : ℕ → ℂ → ℂ} {z₀ : ℂ}
    (hAdm : ∀ n, MandelDim.QAdm (b₁ n) (b₂ n)) (hAdm0 : MandelDim.QAdm c₁ c₂)
    (hNT : ∀ n, MandelDim.NearTranslationOn (F n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hΦ : ∀ n, MandelDim.IsFatouCoordOn (F n) (Φ n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hdom : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n))
    (hz₀ : z₀ ∈ MandelDim.Qreg c₁ c₂) (hval : ∃ x : ℂ, ∀ᶠ n in atTop, Φ n z₀ = x)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ MandelDim.Qreg c₁ c₂) :
    ∃ (N : ℕ) (M : ℝ), ∀ n ≥ N, ∀ z ∈ K, ‖Φ n z‖ ≤ M := by
  obtain ⟨R₁, C₂, L, hR₁, hC₂, hL, hDeriv⟩ := Work.FatouCH.Cont.DerivApprox hD
  obtain ⟨C, hCge1, hChain⟩ := Work.FatouCH.Cont.ChainBound
  have hK'c : IsCompact (insert z₀ K) := hKc.insert z₀
  have hK'Q : insert z₀ K ⊆ MandelDim.Qreg c₁ c₂ := by
    intro w hw
    rcases hw with rfl | hw
    · exact hz₀
    · exact hK hw
  obtain ⟨T, Nmax, B, sr, p₀, hp₀eq, hp₀srad, hsrnpos, hwalk⟩ :=
    walkOfSpine hAdm0 hR₁ hK'c hK'Q
  have hp₀norm : ‖p₀‖ ≤ B := by
    obtain ⟨N, p, -, hp0, -, hprops, -⟩ := hwalk z₀ (by simp)
    rw [← hp0]; exact (hprops 0 (Nat.zero_le N)).1
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) hp₀norm
  have hp₀sradle : Work.FatouCH.srad c₁ c₂ p₀ ≤ B := by
    obtain ⟨N, p, -, hp0, -, hprops, -⟩ := hwalk z₀ (by simp)
    rw [← hp0]; exact (hprops 0 (Nat.zero_le N)).2.1
  -- the fixed compact set containing all the walks
  set W : Set ℂ := closedBall (0:ℂ) (3 * B / 2 + 1) ∩ {w : ℂ | sr / 2 ≤ Work.FatouCH.srad c₁ c₂ w}
    with hWdef
  have hWc : IsCompact W := by
    rw [hWdef]
    exact (isCompact_closedBall (0:ℂ) _).inter_right
      (isClosed_le continuous_const (Work.FatouCH.continuous_srad c₁ c₂))
  have hWQ : W ⊆ MandelDim.Qreg c₁ c₂ := by
    intro w hw
    rw [hWdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hw
    exact srad_pos_iff.mp (lt_of_lt_of_le (by linarith) hw.2)
  have hK'W : insert z₀ K ⊆ W := by
    intro w hw
    obtain ⟨N, p, -, hp0, hpN, hprops, -⟩ := hwalk w hw
    have hmem := hprops N le_rfl
    rw [hpN] at hmem
    rw [hWdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_closedBall]
    exact ⟨by rw [dist_zero_right]; linarith [hmem.1, hBnn],
           by linarith [hmem.2.2, hsrnpos]⟩
  -- the small closed ball around `p₀` is a compact subset of the limit region
  have hp₀ballQ : Metric.closedBall p₀ R₁ ⊆ MandelDim.Qreg c₁ c₂ := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    apply srad_pos_iff.mp
    have h1 : |Work.FatouCH.srad c₁ c₂ p₀ - Work.FatouCH.srad c₁ c₂ u| ≤ ‖p₀ - u‖ :=
      srad_lipschitz c₁ c₂ p₀ u
    have h2 := (abs_le.mp h1).2
    rw [norm_sub_rev] at h2
    linarith [hp₀srad, hR₁]
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hdom (Metric.closedBall p₀ R₁) hp₀ballQ (isCompact_closedBall p₀ R₁))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hdom W hWQ hWc)
  obtain ⟨x, hx⟩ := hval
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hx
  refine ⟨max (max N₁ N₀) N₂,
    2 * (L * C ^ (Nmax + 1) * ((Nmax : ℝ) * (B / 4) + B / 2)) + ‖x‖, ?_⟩
  intro n hn z hz
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₀ : N₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hWn : W ⊆ MandelDim.Qreg (b₁ n) (b₂ n) := hN₁ n hn₁
  have hA : ‖deriv (Φ n) p₀‖ ≤ L :=
    (hDeriv (F n) (Φ n) (b₁ n) (b₂ n) p₀ (hAdm n) (hNT n) (hΦ n)
      (fun u hu => hN₀ n hn₀ (ball_subset_closedBall hu))).2
  have hchain : ∀ z' ∈ insert z₀ K,
      ‖Φ n z' - Φ n p₀‖ ≤ L * C ^ (Nmax + 1) * ((Nmax : ℝ) * (B / 4) + B / 2) := by
    intro z' hz'
    obtain ⟨Nz, p, hNzmax, hp0, hpN, hprops, hsteps⟩ := hwalk z' hz'
    have hRpos : ∀ i ≤ Nz, 0 < (1 / 2) * Work.FatouCH.srad c₁ c₂ (p i) := by
      intro i hi; have h := (hprops i hi).2.2; linarith
    have hballΩ : ∀ i ≤ Nz,
        Metric.ball (p i) ((1 / 2) * Work.FatouCH.srad c₁ c₂ (p i)) ⊆
          MandelDim.Qreg (b₁ n) (b₂ n) := by
      intro i hi u hu
      refine hWn ?_
      rw [mem_ball, dist_eq_norm] at hu
      have hsr : sr ≤ Work.FatouCH.srad c₁ c₂ (p i) := (hprops i hi).2.2
      have hnorm : ‖p i‖ ≤ B := (hprops i hi).1
      have hsle : Work.FatouCH.srad c₁ c₂ (p i) ≤ B := (hprops i hi).2.1
      rw [hWdef, Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_closedBall]
      refine ⟨?_, ?_⟩
      · rw [dist_zero_right]
        calc ‖u‖ ≤ ‖u - p i‖ + ‖p i‖ := by
              have h := norm_add_le (u - p i) (p i); rwa [sub_add_cancel] at h
          _ ≤ (1 / 2) * Work.FatouCH.srad c₁ c₂ (p i) + B := add_le_add hu.le hnorm
          _ ≤ 3 * B / 2 + 1 := by linarith
      · have h1 : |Work.FatouCH.srad c₁ c₂ (p i) - Work.FatouCH.srad c₁ c₂ u| ≤ ‖p i - u‖ :=
          srad_lipschitz c₁ c₂ (p i) u
        have h2 := (abs_le.mp h1).2
        rw [norm_sub_rev] at h2
        linarith [hsr]
    have hstep : ∀ i < Nz,
        ‖p (i + 1) - p i‖ ≤ (1 / 2) * ((1 / 2) * Work.FatouCH.srad c₁ c₂ (p i)) := by
      intro i hi; have h := hsteps i hi; linarith
    have hA' : ‖deriv (Φ n) (p 0)‖ ≤ L := by rw [hp0]; exact hA
    obtain ⟨-, hdisp⟩ := hChain (Work.FatouCH.Cont.SradGeo (hAdm n)).1 (hΦ n).1 (hΦ n).2.1
      hRpos hballΩ hstep hA'
    have hmem : z' ∈ closedBall (p Nz) ((1 / 2) * ((1 / 2) * Work.FatouCH.srad c₁ c₂ (p Nz))) := by
      rw [← hpN]
      refine mem_closedBall_self ?_
      have h := (hprops Nz le_rfl).2.2
      linarith
    have h1 := hdisp z' hmem
    rw [hp0] at h1
    have hsum : ∑ i ∈ Finset.range Nz, ‖p (i + 1) - p i‖ ≤ (Nmax : ℝ) * (B / 4) := by
      have h1 : ∑ i ∈ Finset.range Nz, ‖p (i + 1) - p i‖ ≤ ∑ _i ∈ Finset.range Nz, (B / 4) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < Nz := Finset.mem_range.mp hi
        have h2 : Work.FatouCH.srad c₁ c₂ (p i) ≤ B := (hprops i (le_of_lt hi')).2.1
        have h3 := hsteps i hi'
        linarith
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
      refine h1.trans ?_
      have : (Nz : ℝ) ≤ (Nmax : ℝ) := by exact_mod_cast hNzmax
      nlinarith [hBnn]
    have hsradN : (1 / 2) * Work.FatouCH.srad c₁ c₂ (p Nz) ≤ B / 2 := by
      have h2 : Work.FatouCH.srad c₁ c₂ (p Nz) ≤ B := (hprops Nz le_rfl).2.1
      linarith
    have hinner : (∑ i ∈ Finset.range Nz, ‖p (i + 1) - p i‖) +
        (1 / 2) * Work.FatouCH.srad c₁ c₂ (p Nz) ≤ (Nmax : ℝ) * (B / 4) + B / 2 :=
      add_le_add hsum hsradN
    have hinner_nn : 0 ≤ (∑ i ∈ Finset.range Nz, ‖p (i + 1) - p i‖) +
        (1 / 2) * Work.FatouCH.srad c₁ c₂ (p Nz) := by
      have h2 : 0 < (1 / 2) * Work.FatouCH.srad c₁ c₂ (p Nz) := hRpos Nz le_rfl
      have h3 : 0 ≤ ∑ i ∈ Finset.range Nz, ‖p (i + 1) - p i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      linarith
    have hpow : C ^ (Nz + 1) ≤ C ^ (Nmax + 1) :=
      pow_le_pow_right₀ hCge1 (by omega)
    have hLC : L * C ^ (Nz + 1) ≤ L * C ^ (Nmax + 1) :=
      mul_le_mul_of_nonneg_left hpow hL.le
    have hLC_nn : 0 ≤ L * C ^ (Nz + 1) :=
      mul_nonneg hL.le (pow_nonneg (le_trans zero_le_one hCge1) _)
    exact h1.trans (mul_le_mul hLC hinner hinner_nn
      (mul_nonneg hL.le (pow_nonneg (le_trans zero_le_one hCge1) _)))
  have h1 := hchain z (mem_insert_iff.mpr (Or.inr hz))
  have h2 := hchain z₀ (mem_insert_iff.mpr (Or.inl rfl))
  have h3 : Φ n z₀ = x := hN₂ n hn₂
  have h2' : ‖Φ n p₀ - x‖ ≤ L * C ^ (Nmax + 1) * ((Nmax : ℝ) * (B / 4) + B / 2) := by
    rw [← h3]
    simpa [norm_sub_rev] using h2
  calc ‖Φ n z‖ = ‖(Φ n z - Φ n p₀) + (Φ n p₀ - Φ n z₀) + Φ n z₀‖ := by
        rw [show (Φ n z - Φ n p₀) + (Φ n p₀ - Φ n z₀) + Φ n z₀ = Φ n z by ring]
    _ ≤ ‖Φ n z - Φ n p₀‖ + ‖Φ n p₀ - Φ n z₀‖ + ‖Φ n z₀‖ := by
        have h4 := norm_add_le (Φ n z - Φ n p₀) (Φ n p₀ - Φ n z₀)
        have h5 := norm_add_le ((Φ n z - Φ n p₀) + (Φ n p₀ - Φ n z₀)) (Φ n z₀)
        linarith
    _ ≤ L * C ^ (Nmax + 1) * ((Nmax : ℝ) * (B / 4) + B / 2)
          + L * C ^ (Nmax + 1) * ((Nmax : ℝ) * (B / 4) + B / 2) + ‖x‖ := by
        rw [h3]
        linarith [h1, h2']
    _ = 2 * (L * C ^ (Nmax + 1) * ((Nmax : ℝ) * (B / 4) + B / 2)) + ‖x‖ := by ring


/-! ## Extraction of a locally uniformly convergent subsequence -/

/-- Given an open `U ⊆ ℂ` and a compact `K ⊆ U`, there are an open set `V` and a compact set `W`
with `K ⊆ V ⊆ W ⊆ U`. -/
lemma exists_open_compact_between {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ V W : Set ℂ, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ W ⊆ U ∧ IsCompact W := by
  obtain ⟨δ, hδpos, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨Metric.thickening (δ / 2) K, Metric.cthickening (δ / 2) K, Metric.isOpen_thickening,
    Metric.self_subset_thickening (half_pos hδpos) K, Metric.thickening_subset_cthickening _ K,
    (Metric.cthickening_mono (by linarith) K).trans hδU, hK.cthickening⟩

/-- **Montel extraction for moving domains.**  A sequence `Φ n` of functions holomorphic on the
moving regions `Qreg (b₁ n) (b₂ n)`, whose regions eventually swallow every compact subset of
`Qreg c₁ c₂` and which is eventually uniformly bounded on every such compact subset, has a
strictly monotone subsequence converging locally uniformly on `Qreg c₁ c₂`. -/
theorem subseqExtract {b₁ b₂ : ℕ → Option ℂ} {c₁ c₂ : Option ℂ} {Φ : ℕ → ℂ → ℂ}
    (hOpen : IsOpen (MandelDim.Qreg c₁ c₂))
    (hhol : ∀ n, DifferentiableOn ℂ (Φ n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hdom : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n))
    (hLB : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K → ∃ (N : ℕ) (M : ℝ),
      ∀ n ≥ N, ∀ z ∈ K, ‖Φ n z‖ ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Ψ : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun k => Φ (σ k)) Ψ atTop (MandelDim.Qreg c₁ c₂) := by
  classical
  set U : Set ℂ := MandelDim.Qreg c₁ c₂ with hUdef
  obtain ⟨K, hKc, hKU, hcover⟩ := Work.Normal.exists_compact_exhaustion U hOpen
  have hsub : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ n : ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : ℂ → ℂ, TendstoUniformlyOn (fun k => Φ (ψ (σ k))) g atTop (K n) := by
    intro ψ hψ n
    obtain ⟨V, W, hVopen, hKV, hVW, hWU, hWc⟩ :=
      exists_open_compact_between hOpen (hKc n) (hKU n)
    have hevW : ∀ᶠ k in atTop, W ⊆ MandelDim.Qreg (b₁ (ψ k)) (b₂ (ψ k)) :=
      hψ.tendsto_atTop.eventually (hdom W hWU hWc)
    obtain ⟨Nb, hNb⟩ := eventually_atTop.mp hevW
    obtain ⟨Nc, M, hM⟩ := hLB W hWU hWc
    have hidle : ∀ k, k ≤ ψ k := fun k => hψ.id_le k
    let N₀ : ℕ := max Nb Nc
    have hNb₀ : ∀ k, Nb ≤ ψ (k + N₀) := fun k =>
      le_trans (le_max_left Nb Nc) (le_trans (Nat.le_add_left N₀ k) (hidle (k + N₀)))
    have hNc₀ : ∀ k, Nc ≤ ψ (k + N₀) := fun k =>
      le_trans (le_max_right Nb Nc) (le_trans (Nat.le_add_left N₀ k) (hidle (k + N₀)))
    have hN₀le : ∀ k, N₀ ≤ k + N₀ := fun k => Nat.le_add_left N₀ k
    have hNble : ∀ k, Nb ≤ k + N₀ := fun k =>
      le_trans (le_max_left Nb Nc) (hN₀le k)
    let v : ℕ → ℂ → ℂ := fun k => Φ (ψ (k + N₀))
    have hv : ∀ k, DifferentiableOn ℂ (v k) V := fun k =>
      (hhol (ψ (k + N₀))).mono (hVW.trans (hNb (k + N₀) (hNble k)))
    have hb : Work.Normal.IsLocallyBoundedOn (Set.range v) V := by
      intro K' hK'V _
      refine ⟨M, ?_⟩
      rintro f ⟨k, rfl⟩ z hz
      exact hM (ψ (k + N₀)) (hNc₀ k) z (hVW (hK'V hz))
    obtain ⟨σ', hσ', g, hg⟩ :=
      Work.Normal.exists_subseq_tendstoUniformlyOn_of_locallyBounded hVopen (hKc n) hKV v hv hb
    refine ⟨fun k => σ' k + N₀, fun a b hab => Nat.add_lt_add_right (hσ' hab) N₀, g, ?_⟩
    exact hg
  obtain ⟨φ, hφ, g, hg⟩ :=
    Work.Normal.exists_subseq_tendstoLocallyUniformlyOn_of_exhaustion hOpen Φ K hcover hsub
  exact ⟨φ, hφ, g, hg⟩

/-- If every subsequence of `F` has a further subsequence converging to `g` uniformly on `K`,
then `F` itself converges to `g` uniformly on `K`. -/
lemma tendstoUniformlyOn_of_forall_subseq {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : Set ℂ}
    (h : ∀ τ : ℕ → ℕ, StrictMono τ → ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n => F (τ (σ n))) g atTop K) :
    TendstoUniformlyOn F g atTop K := by
  by_contra hbad
  rw [Metric.tendstoUniformlyOn_iff] at hbad
  push_neg at hbad
  obtain ⟨ε, hε, hfreq⟩ := hbad
  have hex : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ x ∈ K, ε ≤ dist (g x) (F n x) :=
    fun N => Filter.frequently_atTop.mp hfreq N
  choose f hf using hex
  let nseq : ℕ → ℕ := fun k => Nat.rec (f 0) (fun _ ih => f (ih + 1)) k
  have hnseq_succ : ∀ k, nseq (k + 1) = f (nseq k + 1) := fun k => rfl
  have hmono : StrictMono nseq := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hnseq_succ k]
    have := (hf (nseq k + 1)).1
    omega
  have hbn : ∀ k, ∃ x ∈ K, ε ≤ dist (g x) (F (nseq k) x) := by
    intro k
    cases k with
    | zero => exact (hf 0).2
    | succ j => rw [hnseq_succ j]; exact (hf (nseq j + 1)).2
  choose xb hxb using hbn
  obtain ⟨σ, hσ, hconv⟩ := h nseq hmono
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv ε hε)
  have h1 := hN N le_rfl (xb (σ N)) (hxb (σ N)).1
  have h2 := (hxb (σ N)).2
  linarith

/-! ## The main theorem -/

/-- **FX11 (Shishikura A.2.1(iii)): continuity of the Fatou coordinate.**

`MandelDim.FatouContinuity` is the interface proposition (see `Submission/Work/Interfaces/Fatou.lean`):
moving domains `Qreg (b₁ n) (b₂ n)` with `Qreg c₁ c₂` as limit, every compact of the limit domain
eventually inside the moving domains, `F n → F₀` uniformly on compacts of the limit domain, and the
normalisation `Φ n z₀ = Φ₀ z₀` eventually, imply `Φ n → Φ₀` uniformly on every compact of the limit
domain.

Proof route (blueprint `Submission/Work/Fatou/fatouU.lean`, section FX11):

1. **Local uniform bounds of `Φ n` on compacts of the limit domain** (`localBoundOf`, built above on
   Shishikura's derivative estimate `FatouDerivEstimate`, the universal Koebe chain bound
   `ChainBound` and the walk along the spine of `Qreg` provided by `walkOfSpine`).
2. **Montel** (`subseqExtract`) gives, after passing to a subsequence, local uniform convergence
   `Φ (σ k) → Ψ` on `Qreg c₁ c₂`.
3. **The limit is a Fatou coordinate** (`isFatouCoordOfLimit`): the Abel equation is transferred,
   `Ψ` is holomorphic and injective by Hurwitz.
4. **Uniqueness** (`hU`): `Ψ = Φ₀ + c` on `Qreg c₁ c₂`, and the normalisation at `z₀` forces
   `c = 0`, so `Ψ = Φ₀`.
5. **Conclusion**: every subsequence of `ℕ` has a further subsequence along which `Φ → Φ₀`
   uniformly on `K`; by the sub-subsequence argument the whole sequence converges uniformly on `K`.

`hE` (`MandelDim.FatouExists`) is not needed by this route; it is kept in the signature for the
caller's assembly. -/
theorem fatouContinuityOf (hE : MandelDim.FatouExists) (hU : MandelDim.FatouUnique)
    (hD : MandelDim.FatouDerivEstimate) : MandelDim.FatouContinuity := by
  intro b₁ b₂ c₁ c₂ F F₀ Φ Φ₀ z₀ hAdm hAdm0 hNT hNT0 hconv hΦ hΦ0 hz₀ hnorm K hKQ hKc
  obtain ⟨hOpen, -, -, -, -, -, -, -, -⟩ := Work.FatouCH.Cont.SradGeo (b₁ := c₁) (b₂ := c₂) hAdm0
  have hdom : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n) :=
    fun K h1 h2 => (hconv K h1 h2).1
  have hF : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K → TendstoUniformlyOn F F₀ atTop K :=
    fun K h1 h2 => (hconv K h1 h2).2
  refine tendstoUniformlyOn_of_forall_subseq (K := K) ?_
  intro τ hτ
  have hτt : Tendsto τ atTop atTop := hτ.tendsto_atTop
  have hdomτ : ∀ K' ⊆ MandelDim.Qreg c₁ c₂, IsCompact K' →
      ∀ᶠ n in atTop, K' ⊆ MandelDim.Qreg (b₁ (τ n)) (b₂ (τ n)) :=
    fun K' h1 h2 => hτt.eventually (hdom K' h1 h2)
  have hFτ : ∀ K' ⊆ MandelDim.Qreg c₁ c₂, IsCompact K' →
      TendstoUniformlyOn (fun n => F (τ n)) F₀ atTop K' :=
    fun K' h1 h2 => Work.Normal.tendstoUniformlyOn_comp_index_tendsto (hF K' h1 h2) hτt
  have hLBτ : ∀ K' ⊆ MandelDim.Qreg c₁ c₂, IsCompact K' → ∃ (N : ℕ) (M : ℝ),
      ∀ n ≥ N, ∀ z ∈ K', ‖Φ (τ n) z‖ ≤ M := by
    intro K' h1 h2
    exact localBoundOf hD (fun n => hAdm (τ n)) hAdm0 (fun n => hNT (τ n))
      (fun n => hΦ (τ n)) hdomτ hz₀ ⟨Φ₀ z₀, hτt.eventually hnorm⟩ h2 h1
  obtain ⟨σ, hσ, Ψ, hΨ⟩ := subseqExtract hOpen (fun n => (hΦ (τ n)).1) hdomτ hLBτ
  set ρ : ℕ → ℕ := fun k => τ (σ k) with hρdef
  have hρ : StrictMono ρ := hτ.comp hσ
  have hdomρ : ∀ K' ⊆ MandelDim.Qreg c₁ c₂, IsCompact K' →
      ∀ᶠ n in atTop, K' ⊆ MandelDim.Qreg (b₁ (ρ n)) (b₂ (ρ n)) :=
    fun K' h1 h2 => hρ.tendsto_atTop.eventually (hdom K' h1 h2)
  have hFρ : ∀ K' ⊆ MandelDim.Qreg c₁ c₂, IsCompact K' →
      TendstoUniformlyOn (fun n => F (ρ n)) F₀ atTop K' :=
    fun K' h1 h2 => Work.Normal.tendstoUniformlyOn_comp_index_tendsto (hF K' h1 h2) hρ.tendsto_atTop
  have hAbel := Work.FatouCH.Cont.AbelTransfer hOpen (fun n => hNT (ρ n)) (fun n => hΦ (ρ n))
    hdomρ hFρ hΨ
  have hFC : MandelDim.IsFatouCoordOn F₀ Ψ (MandelDim.Qreg c₁ c₂) :=
    isFatouCoordOfLimit hAdm0 hNT0 (fun n => hΦ (ρ n)) hdomρ hΨ hAbel
  obtain ⟨c, hc⟩ := hU c₁ c₂ F₀ Φ₀ Ψ hAdm0 hNT0 hΦ0 hFC
  have hz₀eq : Ψ z₀ = Φ₀ z₀ := by
    have h1 : Tendsto (fun k => Φ (ρ k) z₀) atTop (𝓝 (Ψ z₀)) := hΨ.tendsto_at hz₀
    have hev : (fun k => Φ (ρ k) z₀) =ᶠ[atTop] (fun _ => Φ₀ z₀) :=
      hρ.tendsto_atTop.eventually hnorm
    have h2 : Tendsto (fun k => Φ (ρ k) z₀) atTop (𝓝 (Φ₀ z₀)) :=
      tendsto_const_nhds.congr' hev.symm
    exact tendsto_nhds_unique h1 h2
  have hc0 : c = 0 := by
    have h := hc z₀ hz₀
    rw [hz₀eq] at h
    have h2 : Φ₀ z₀ + c = Φ₀ z₀ + 0 := by simpa using h.symm
    exact add_left_cancel h2
  refine ⟨σ, hσ, ?_⟩
  have heq : Set.EqOn Ψ Φ₀ (MandelDim.Qreg c₁ c₂) := by
    intro z hz
    rw [hc z hz, hc0, add_zero]
  have hconv2 : TendstoLocallyUniformlyOn (fun k => Φ (ρ k)) Φ₀ atTop (MandelDim.Qreg c₁ c₂) :=
    hΨ.congr_right heq
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hOpen).mp hconv2 K hKQ hKc

end

end Work.Fatou.Analysis
