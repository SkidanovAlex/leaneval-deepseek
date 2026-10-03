import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.SepDefs

/-!
# Smoothness and compact support of the cut chirp `fcut`

`fcut ε α u = cutPhi u · cutPsi (ε u) · |u|^{iα}`.  Each factor is harmless on its own except
the chirp `|u|^{iα}`, which is only smooth away from `u = 0`; but `cutPhi` vanishes identically
for `|u| ≤ 1/2`, so the product is smooth everywhere.  Concretely we prove `C^∞`-regularity on
the three pieces

* `{u | 0 < u}`, where `|u| = u` and the chirp is `exp (i α log u)`;
* `{u | u < 0}`, where `|u| = -u` and the chirp is `exp (i α log (-u))`;
* `{u | |u| < 1/2}`, where `fcut` vanishes because `cutPhi` does,

which cover `ℝ` (the first two cover `{0}ᶜ`, and `0` lies in the third).  Compact support is
immediate from `cutPsi (ε u) = 0` as soon as `|ε u| ≥ 2`.
-/

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- `fcut ε α` is `C^∞` on the positive half-line. -/
lemma contDiffOn_fcut_Ioi (ε α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fcut ε α) (Set.Ioi 0) := by
  have hphi : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => ((cutPhi v : ℝ) : ℂ)) (Set.Ioi 0) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn contDiff_cutPhi.contDiffOn
  have hpsi : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => ((cutPsi (ε * v) : ℝ) : ℂ)) (Set.Ioi 0) := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => cutPsi (ε * v)) :=
      contDiff_cutPsi.comp (contDiff_const.mul contDiff_id)
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn h2.contDiffOn
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono (by intro x hx; simpa using (Set.mem_Ioi.mp hx).ne')
  have hlogα : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => (α * Real.log v : ℝ)) (Set.Ioi 0) :=
    (hlog.mul contDiffOn_const).congr (fun v _ => by ring)
  have hcast : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => ((α * Real.log v : ℝ) : ℂ)) (Set.Ioi 0) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn hlogα
  have hexp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : ℝ => Complex.exp (((α * Real.log v : ℝ) : ℂ) * Complex.I)) (Set.Ioi 0) := by
    simpa [Function.comp_def] using
      (Complex.contDiff_exp (𝕜 := ℝ) (n := (⊤ : ℕ∞))).comp_contDiffOn (hcast.mul contDiffOn_const)
  refine ((hphi.mul hpsi).mul hexp).congr ?_
  intro v hv
  have hv' : 0 < v := Set.mem_Ioi.mp hv
  simp only [fcut]
  rw [cpow_eq_chirp (ne_of_gt hv'), chirp, abs_of_pos hv']

/-- `fcut ε α` is `C^∞` on the negative half-line. -/
lemma contDiffOn_fcut_Iio (ε α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fcut ε α) (Set.Iio 0) := by
  have hphi : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => ((cutPhi v : ℝ) : ℂ)) (Set.Iio 0) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn contDiff_cutPhi.contDiffOn
  have hpsi : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => ((cutPsi (ε * v) : ℝ) : ℂ)) (Set.Iio 0) := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => cutPsi (ε * v)) :=
      contDiff_cutPsi.comp (contDiff_const.mul contDiff_id)
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn h2.contDiffOn
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => Real.log (-v)) (Set.Iio 0) := by
    have hneg : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => -v) (Set.Iio 0) := contDiffOn_id.neg
    have hmap : Set.MapsTo (fun v : ℝ => -v) (Set.Iio 0) ({0}ᶜ : Set ℝ) := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (by simpa using hx)
    simpa [Function.comp_def] using (Real.contDiffOn_log (n := (⊤ : ℕ∞))).comp hneg hmap
  have hlogα : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => (α * Real.log (-v) : ℝ)) (Set.Iio 0) :=
    (hlog.mul contDiffOn_const).congr (fun v _ => by ring)
  have hcast : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => ((α * Real.log (-v) : ℝ) : ℂ)) (Set.Iio 0) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn hlogα
  have hexp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v : ℝ => Complex.exp (((α * Real.log (-v) : ℝ) : ℂ) * Complex.I)) (Set.Iio 0) := by
    simpa [Function.comp_def] using
      (Complex.contDiff_exp (𝕜 := ℝ) (n := (⊤ : ℕ∞))).comp_contDiffOn (hcast.mul contDiffOn_const)
  refine ((hphi.mul hpsi).mul hexp).congr ?_
  intro v hv
  have hv' : v < 0 := Set.mem_Iio.mp hv
  simp only [fcut]
  rw [cpow_eq_chirp (ne_of_lt hv'), chirp, abs_of_neg hv']

/-- `fcut ε α` vanishes identically for `|u| < 1/2`, where `cutPhi` does. -/
lemma fcut_eq_zero_of_abs_lt_half {ε α u : ℝ} (hu : |u| < 1 / 2) : fcut ε α u = 0 := by
  have hcu : cutPhi u = 0 := cutPhi_eq_zero_of_abs_le (le_of_lt hu)
  simp [fcut, hcu]

/-- `fcut ε α` is `C^∞` on the middle interval `(-1/2, 1/2)`, being identically zero there. -/
lemma contDiffOn_fcut_mid (ε α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fcut ε α) (Set.Ioo (-(1/2)) (1/2)) := by
  refine (contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℂ)) _).congr ?_
  intro u hu
  rw [Set.mem_Ioo] at hu
  exact fcut_eq_zero_of_abs_lt_half (abs_lt.mpr hu)

theorem contDiff_fcut (ε α : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fcut ε α) ∧ HasCompactSupport (fcut ε α) := by
  constructor
  · -- `C^∞`-regularity, by gluing the three open pieces that cover the line.
    have hpos := contDiffOn_fcut_Ioi ε α
    have hneg := contDiffOn_fcut_Iio ε α
    have hmid := contDiffOn_fcut_mid ε α
    have hne : ContDiffOn ℝ (⊤ : ℕ∞) (fcut ε α) ({0}ᶜ : Set ℝ) :=
      (hpos.union_of_isOpen hneg isOpen_Ioi isOpen_Iio).mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi,
          Set.mem_Iio] at hx ⊢
        rcases lt_or_gt_of_ne hx with h | h
        · exact Or.inr h
        · exact Or.inl h)
    refine contDiff_of_contDiffOn_union_of_isOpen hne hmid ?_ isOpen_compl_singleton isOpen_Ioo
    ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases h : x = 0
    · right; simp [Set.mem_Ioo, h]
    · exact Or.inl h
  · -- compact support: `fcut ε α` vanishes off `[-2/ε, 2/ε]`.
    have h2e : 0 < 2 / ε := div_pos (by norm_num) hε
    refine HasCompactSupport.intro' (K := Set.Icc (-(2/ε)) (2/ε)) isCompact_Icc isClosed_Icc ?_
    intro u hu
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    have hu' : 2 / ε < |u| := by
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact h
    have h4 : 4 ≤ (ε * u) ^ 2 := by
      have h1 : 2 < |ε * u| := by
        rw [abs_mul, abs_of_pos hε]
        have key := mul_lt_mul_of_pos_left hu' hε
        have he2 : ε * (2 / ε) = 2 := by field_simp
        linarith
      have h2 : (4 : ℝ) < (ε * u) ^ 2 := by
        nlinarith [h1, sq_abs (ε * u), abs_nonneg (ε * u)]
      linarith
    have hcz : cutPsi (ε * u) = 0 := cutPsi_eq_zero_of_sq_ge h4
    simp [fcut, hcz]

end

end Work.FIArea4.Vflip.Vfd
