import Mathlib
import Submission.Work.Drive.classDatum
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.planeChart_eq_imp_annulus
import Submission.Work.Drive.dirC_eq_iff_collinear
import Submission.Work.Drive.seamEssentiality
import Submission.Work.Drive.exists_contMDiffAt_stripChart_closed
import Submission.Work.Drive.coreLoopCapDisjoint

/-!
# The class injectivity of a plane chart on the annulus

`Work.Drive.IsPlaneChart` pins the chart `Q` on the annulus `1/2 < ‖z‖ ≤ 1` to the strip chart
`stripChart γ hγne 0 (annW z)` (the chord symmetric around `γ (arg z)` with half-opening `annS z`),
and `Work.Drive.planeChart_eq_imp_annulus` proves that the *values* of the chart on the annulus
determine the parameter, up to the antipodal identification of the boundary circle.

The transport lane (`Work.Drive.ncard_cutFibreBox_clampedSweep_eq_one`, and hence the per-block
transport `T6` of the counting route) needs the corresponding statement for the **classes**: the
class of `Q z` determines `z`.  The class is the *projective* class of the capping point, i.e. it
drops the level, and the level of the strip chart is the capping radius of the chord; so a class
collision on the annulus is exactly a pair of **homothetic chords** of `γ` (two chords that are
positive multiples of one another about the origin) — a configuration that is *not* excluded by the
clauses of `IsPlaneChart`.  The hypothesis that rules it out is that no two points of `γ` lie on a
common ray from the origin (`hrad` below), i.e. that `γ` is star-shaped with respect to the origin;
for a curve of winding one about the origin this holds exactly when every radial ray meets the curve
once.

This file proves:

* `Work.Drive.confProjVecOf_proj_eq_iff` and `Work.Drive.classOfConf_eq_iff` — the **dictionary**:
  the class of a configuration point of the capping space determines its normalised midpoint `d`
  and its doubled direction `η`, hence (by `cls_stripChart_zero`) the class of a strip value
  determines `(d, η)`;
* `Work.Drive.stripD_eq_imp_midrel`, `Work.Drive.abs_eq_of_data_rel` — the two algebraic steps that
  turn that into "the two chords are positive multiples of one another";
* `Work.Drive.confProjVecOf_proj_ne_capProjVecOf` — the config-side/cap-side dichotomy (a strip value
  over a non-degenerate chord has `‖c₂‖ < ‖c₁‖`, a cap point has `‖c₁‖ ≤ ‖c₂‖`);
* `Work.Drive.class_injective_of_radial` — the region-restricted class injectivity: for `z` in the
  annulus and any `z'` of the closed disk with `‖z'‖ ≠ 1/2`, equal classes force `z = z'` or the
  boundary antipodal case;
* `Work.Drive.class_injective_diskPlane_of_annulus` — the `hcls` input of
  `Work.Drive.ncard_cutFibreBox_clampedSweep_eq_one` for base points whose disk image lies in the
  annulus.

The interface case `‖z'‖ = 1/2` is *not* covered here; its value is pinned only by continuity
(`Work.Drive.isPlaneChart_seam_mem_stripImage`, `Work.Drive.tendsto_stripChart_seamDiag`) and its
class has `‖d‖ = 1`.  All declarations of this file are `sorry`-free and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Work.Drive
open Submission.Configuration (muOrd)
open Manifold
open scoped Manifold ContDiff
noncomputable section

set_option maxHeartbeats 2000000






lemma c₁_smul_real (t : ℝ) (v : Eucl 3) : c₁ (t • v) = (t : ℂ) * c₁ v := by
  rw [← confProjVecOf_c₁CLM_apply (t • v), ContinuousLinearMap.map_smul,
    confProjVecOf_c₁CLM_apply v, Complex.real_smul]

lemma c₂_smul_real (t : ℝ) (v : Eucl 3) : c₂ (t • v) = (t : ℂ) * c₂ v := by
  rw [← confProjVecOf_c₂CLM_apply (t • v), ContinuousLinearMap.map_smul,
    confProjVecOf_c₂CLM_apply v, Complex.real_smul]

lemma eq_of_c₁_c₂ {v w : Eucl 3} (h1 : c₁ v = c₁ w) (h2 : c₂ v = c₂ w) : v = w := by
  rw [← ofComplex_c₁_c₂ v, ← ofComplex_c₁_c₂ w, h1, h2]

lemma sqrt_factor_pos {d : ℂ} (hd : ‖d‖ ≤ 1) : 0 < Real.sqrt (1 - ‖d‖ ^ 2 / 2) :=
  Real.sqrt_pos.mpr (by nlinarith [norm_nonneg d, sq_nonneg ‖d‖, hd])

lemma sqrt_two_ne_zero_complex : (((Real.sqrt 2 : ℝ)) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))

/-- **The class of a configuration point of the capping space determines the normalised offset and
the doubled direction.**  For unit complex numbers `u`, `u'` and points `d`, `d'` of the closed unit
disk, the projective classes of `confProjVecOf u d` and `confProjVecOf u' d'` in `ℝP³` agree if and
only if `d = d'` and `u ^ 2 = u' ^ 2`. -/
theorem confProjVecOf_proj_eq_iff {u u' d d' : ℂ} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hd : ‖d‖ ≤ 1) (hd' : ‖d'‖ ≤ 1) :
    (Projectivization.mk ℝ (confProjVecOf u d) (confProjVecOf_ne_zero hu hd)
        = Projectivization.mk ℝ (confProjVecOf u' d') (confProjVecOf_ne_zero hu' hd'))
      ↔ d = d' ∧ u ^ 2 = u' ^ 2 := by
  have hv := norm_confProjVecOf hu hd
  have hw := norm_confProjVecOf hu' hd'
  have hsne : ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sqrt_factor_pos hd)
  have hs2 : (((Real.sqrt 2 : ℝ)) : ℂ) ≠ 0 := sqrt_two_ne_zero_complex
  constructor
  · intro h
    rw [Projectivization.mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    rw [Units.smul_def] at ha
    -- `‖a‖ = 1`
    have hnorm : ‖(a : ℝ)‖ = 1 := by
      have h2 := congrArg norm ha
      rw [norm_smul, hw, mul_one, hv] at h2
      simpa using h2
    -- hence `(a : ℂ) ^ 2 = 1`
    have hsq : (a : ℂ) ^ 2 = 1 := by
      have ha2 : (a : ℝ) ^ 2 = 1 := by
        have h2 : ‖(a : ℂ)‖ ^ 2 = 1 := by
          have h3 : ‖(a : ℂ)‖ = 1 := by simpa using hnorm
          rw [h3]; norm_num
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im] at h2
        nlinarith [h2]
      rw [← Complex.ofReal_pow, ha2, Complex.ofReal_one]
    have han : ‖(a : ℂ)‖ = 1 := by simpa using hnorm
    -- the two component equations
    have e1 : (a : ℂ) * (u' * ((Real.sqrt (1 - ‖d'‖ ^ 2 / 2) : ℝ) : ℂ))
        = u * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) := by
      have h' := congrArg c₁ ha
      rw [c₁_smul_real, c₁_confProjVecOf, c₁_confProjVecOf] at h'
      exact h'
    have e2 : (a : ℂ) * (star u' * d' / ((Real.sqrt 2 : ℝ) : ℂ))
        = star u * d / ((Real.sqrt 2 : ℝ) : ℂ) := by
      have h' := congrArg c₂ ha
      rw [c₂_smul_real, c₂_confProjVecOf, c₂_confProjVecOf] at h'
      exact h'
    -- `‖d'‖ = ‖d‖`
    have hdd : ‖d'‖ = ‖d‖ := by
      have h' := congrArg norm e2
      simp only [norm_mul, han, one_mul, norm_div, norm_star, hu', hu] at h'
      have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2n : ‖(((Real.sqrt 2 : ℝ)) : ℂ)‖ = Real.sqrt 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2pos]
      rw [hs2n] at h'
      rw [div_eq_mul_inv, div_eq_mul_inv] at h'
      exact mul_right_cancel₀ (inv_ne_zero (ne_of_gt h2pos)) h'
    -- the square-root factors agree
    have hs : Real.sqrt (1 - ‖d'‖ ^ 2 / 2) = Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
      have h' := congrArg norm e1
      simp only [norm_mul, han, one_mul, hu', hu, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (sqrt_factor_pos hd'), abs_of_pos (sqrt_factor_pos hd)] at h'
      exact h'
    -- `u = a * u'`
    have hsc : ((Real.sqrt (1 - ‖d'‖ ^ 2 / 2) : ℝ) : ℂ)
        = ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) := by rw [hs]
    have hu_eq : u = (a : ℂ) * u' := by
      have h' := e1
      rw [hsc, ← mul_assoc] at h'
      exact (mul_right_cancel₀ hsne h').symm
    refine ⟨?_, ?_⟩
    · -- `d = d'`
      have hstar : star u = (a : ℂ) * star u' := by
        rw [hu_eq, star_mul]
        rw [show star ((a : ℂ)) = (a : ℂ) from Complex.conj_ofReal (a : ℝ)]
        ring
      have ha_ne : (a : ℂ) ≠ 0 := by
        intro h0; rw [h0] at hsq; norm_num at hsq
      have hsu_ne : star u' ≠ 0 := by
        intro h
        rw [star_eq_zero] at h
        rw [h] at hu'
        norm_num at hu'
      have key : (a : ℂ) * star u' * d' = (a : ℂ) * star u' * d := by
        have h'' := e2
        rw [hstar] at h''
        have h5 := congrArg (fun z : ℂ => z * (((Real.sqrt 2 : ℝ)) : ℂ)) h''
        rw [mul_assoc, div_mul_cancel₀ _ hs2, mul_assoc, div_mul_cancel₀ _ hs2] at h5
        simpa [mul_assoc] using h5
      have := mul_left_cancel₀ (mul_ne_zero ha_ne hsu_ne) key
      exact this.symm
    · -- `u ^ 2 = u' ^ 2`
      rw [hu_eq, mul_pow, hsq, one_mul]
  · rintro ⟨rfl, hu2⟩
    have hsign : u' = u ∨ u' = -u := by
      have h0 : (u' - u) * (u' + u) = 0 := by
        have : u' ^ 2 - u ^ 2 = 0 := by rw [hu2]; ring
        linear_combination this
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (by linear_combination h0)
    rcases hsign with h | h
    · subst h
      rw [Projectivization.mk_eq_mk_iff]
      exact ⟨1, by simp⟩
    · subst h
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨-1, ?_⟩
      rw [Units.smul_def, show (((-1 : ℝˣ)) : ℝ) = -1 from rfl, neg_one_smul,
        confProjVecOf_neg_u, neg_neg]


/-- **The class datum is injective**: the class of a configuration point of the capping space
determines its normalised midpoint and its doubled direction. -/
theorem classOfConf_eq_iff {d d' : ℂ} (hd : ‖d‖ ≤ 1) (hd' : ‖d'‖ ≤ 1)
    {η η' : UnitAddCircle} :
    classOfConf d hd η = classOfConf d' hd' η' ↔ d = d' ∧ η = η' := by
  constructor
  · intro h
    rw [classOfConf_eq_mk, classOfConf_eq_mk] at h
    have h' := (confProjVecOf_proj_eq_iff (classRoot_norm η) (classRoot_norm η') hd hd').mp h
    obtain ⟨hd_eq, hsq⟩ := h'
    refine ⟨hd_eq, circleOf_injective ?_⟩
    rw [← classRoot_sq η, ← classRoot_sq η', hsq]
  · rintro ⟨rfl, rfl⟩
    exact (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, by rw [one_smul]⟩



/-- The complex coordinate of a vector of the plane. -/
def cm (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

lemma cm_injective : Function.Injective cm := by
  intro p q h
  have h1 : p.1 = q.1 := by have := congrArg Complex.re h; simpa [cm] using this
  have h2 : p.2 = q.2 := by have := congrArg Complex.im h; simpa [cm] using this
  exact Prod.ext h1 h2

lemma cm_add (p q : ℝ × ℝ) : cm (p + q) = cm p + cm q := by
  apply Complex.ext <;> simp [cm]

lemma cm_sub (p q : ℝ × ℝ) : cm (p - q) = cm p - cm q := by
  apply Complex.ext <;> simp [cm]

lemma cm_smul (a : ℝ) (p : ℝ × ℝ) : cm (a • p) = (a : ℂ) * cm p := by
  apply Complex.ext <;> simp [cm]

lemma cm_div_two (p : ℝ × ℝ) : cm (p / 2) = cm p / 2 := by
  apply Complex.ext <;> simp [cm]

lemma cm_neg (p : ℝ × ℝ) : cm (-p) = - cm p := by
  apply Complex.ext <;> simp [cm]

/-- **The endpoints of the strip chord in the complex coordinates.** -/
lemma strip_cm_endpoint_zero (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    cm (γ (Circle.exp (w 0))) = (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) + stripChord γ w / 2 := by
  apply Complex.ext <;> simp [cm, stripMid, stripChord, chordC] <;> ring

lemma strip_cm_endpoint_one (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    cm (γ (Circle.exp (w 1))) = (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) - stripChord γ w / 2 := by
  apply Complex.ext <;> simp [cm, stripMid, stripChord, chordC] <;> ring

/-- The radius and the data. -/
lemma stripR_sq (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    stripR γ w ^ 2 = Complex.normSq (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ)
      + Complex.normSq (stripChord γ w) := by
  have hA : 0 ≤ stripA γ w := by
    have h1 : (0:ℝ) ≤ (stripMid γ w).1 ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (stripMid γ w).2 ^ 2 := sq_nonneg _
    have h3 : (0:ℝ) ≤ (stripChord γ w).re ^ 2 := sq_nonneg _
    have h4 : (0:ℝ) ≤ (stripChord γ w).im ^ 2 := sq_nonneg _
    rw [stripA, Complex.normSq_apply]
    linarith
  rw [stripR, Real.sq_sqrt hA, stripA, Complex.normSq_apply, Complex.normSq_apply]
  ring

lemma stripD_eq (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    stripD γ w = (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) / ((stripR γ w : ℝ) : ℂ) := by
  rw [stripD]
  congr 1
  apply Complex.ext <;> simp

lemma stripChord_eq_cm (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    stripChord γ w = cm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) := by
  rw [stripChord, chordC]
  apply Complex.ext <;> simp [cm]

/-- The doubled direction of `stripData` is the doubled direction of the chord. -/
lemma stripData_snd_snd (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    (stripData γ w).2.2 = Submission.Collision.dirC
      (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) := rfl

/-- The strip chart depends only on `stripData`. -/
lemma stripChart_eq_of_stripData_eq {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    (v : UnitAddCircle) {w w' : EuclideanSpace ℝ (Fin 2)} (h : stripData γ w = stripData γ w') :
    stripChart γ hγne v w = stripChart γ hγne v w' := by
  rw [stripChart_eq_mk, stripChart_eq_mk, mk_inl_inj]
  refine Subtype.ext ?_
  show ((stripData γ w).1, (stripData γ w).2.1, (stripData γ w).2.2 + v)
      = ((stripData γ w').1, (stripData γ w').2.1, (stripData γ w').2.2 + v)
  rw [h]


/-- **The midpoint relation from the equality of the normalised midpoints**: if the `stripD`-data of two
chords agree, the (complex) midpoints are positive multiples of one another. -/
lemma stripD_eq_imp_midrel {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    {w w' : EuclideanSpace ℝ (Fin 2)} (h : stripD γ w = stripD γ w') :
    (⟨(stripMid γ w').1, (stripMid γ w').2⟩ : ℂ)
      = ((stripR γ w' / stripR γ w : ℝ) : ℂ) * (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) := by
  have hRpos : (0 : ℝ) < stripR γ w := by
    have h1 := stripData_pos hγne w
    rwa [stripData_fst] at h1
  have hR'pos : (0 : ℝ) < stripR γ w' := by
    have h1 := stripData_pos hγne w'
    rwa [stripData_fst] at h1
  have hRne : ((stripR γ w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hRpos
  have hR'ne : ((stripR γ w' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR'pos
  have h1 : (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) / ((stripR γ w : ℝ) : ℂ)
      = (⟨(stripMid γ w').1, (stripMid γ w').2⟩ : ℂ) / ((stripR γ w' : ℝ) : ℂ) := by
    rw [← stripD_eq, ← stripD_eq]
    exact h
  have h2 : (⟨(stripMid γ w').1, (stripMid γ w').2⟩ : ℂ)
      = ((⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) / ((stripR γ w : ℝ) : ℂ))
        * ((stripR γ w' : ℝ) : ℂ) := by
    rw [h1]
    exact (div_mul_cancel₀ _ hR'ne).symm
  rw [h2]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The length/radius algebra: if the midpoints and the chords are positive-and-sign multiples with
matching radii, the scalars have equal absolute values. -/
lemma abs_eq_of_data_rel {M M' D D' : ℂ} {R R' c : ℝ}
    (hR : R ^ 2 = Complex.normSq M + Complex.normSq D)
    (hR' : R' ^ 2 = Complex.normSq M' + Complex.normSq D')
    (hRpos : 0 < R) (hRpos' : 0 < R')
    (hM : M' = ((R' / R : ℝ) : ℂ) * M) (hD : D' = (c : ℂ) * D) (hDne : D ≠ 0) :
    |c| = R' / R := by
  have hDn : Complex.normSq D ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hDne)
  have h1 : Complex.normSq D' = (c ^ 2) * Complex.normSq D := by
    rw [hD, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have h2 : Complex.normSq M' = ((R' / R) ^ 2) * Complex.normSq M := by
    rw [hM, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have h3 : R' ^ 2 = ((R' / R) ^ 2) * R ^ 2 := by
    field_simp
  have hR'2 : R' ^ 2 = ((R' / R) ^ 2) * Complex.normSq M + (c ^ 2) * Complex.normSq D := by
    rw [hR', h2, h1]
  have hR2 : R' ^ 2
      = ((R' / R) ^ 2) * Complex.normSq M + ((R' / R) ^ 2) * Complex.normSq D := by
    rw [h3, hR, mul_add]
  have h5 : (c ^ 2) * Complex.normSq D = ((R' / R) ^ 2) * Complex.normSq D := by
    linarith [hR'2, hR2]
  have h6 : c ^ 2 = (R' / R) ^ 2 := mul_right_cancel₀ hDn h5
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h6 with h | h
  · rw [h, abs_of_pos (div_pos hRpos' hRpos)]
  · rw [h, abs_neg, abs_of_pos (div_pos hRpos' hRpos)]

/-- The chord of the strip parameter of an annulus point is non-degenerate. -/
lemma chord_ne_of_annulus {γ : Circle → ℝ × ℝ} (hγinj : Function.Injective γ)
    {z : ℂ} (hz : 1 / 2 < ‖z‖) (hz1 : ‖z‖ ≤ 1) :
    γ (Circle.exp ((annW z) 0)) ≠ γ (Circle.exp ((annW z) 1)) := by
  intro h
  have he : Circle.exp ((annW z) 0) = Circle.exp ((annW z) 1) := hγinj h
  rw [circle_exp_eq_iff_exists_int] at he
  obtain ⟨n, hn⟩ := he
  have h01 : (annW z) 0 - (annW z) 1 = 2 * annS z := by
    rw [annW_apply_zero, annW_apply_one]; ring
  have hAS : annS z = Real.pi * (n : ℝ) := by linarith [hn, h01]
  have hpos : 0 < annS z := annS_pos hz
  have hle : annS z ≤ Real.pi / 2 := annS_le hz1
  have h1 : (0 : ℝ) < Real.pi * (n : ℝ) := by linarith
  have h2 : Real.pi * (n : ℝ) ≤ Real.pi / 2 := by linarith
  have hn1 : (1 : ℤ) ≤ n := by
    have : (0 : ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hle2 : (n : ℝ) ≤ 1 / 2 := by nlinarith [Real.pi_pos]
  linarith

/-- **The class map of a plane chart is injective on the annulus, modulo the boundary antipodal
identification, provided no two points of `γ` lie on a common ray from the origin** (the hypothesis
`hrad`).  This is the region-restricted class injectivity that the transport's fibre hypotheses
(`Work.Drive.ncard_cutFibreBox_clampedSweep_eq_one`) consume. -/
theorem class_annulus_injective_of_radial {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    (hrad : ∀ (p q : Circle) (lam : ℝ), 0 < lam → γ p = lam • γ q → γ p = γ q)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {z z' : ℂ}
    (hz : 1 / 2 < ‖z‖) (hz1 : ‖z‖ ≤ 1) (hz' : 1 / 2 < ‖z'‖) (hz1' : ‖z'‖ ≤ 1)
    (hcls : (cappingSpaceHomeoProj (Q z)).2 = (cappingSpaceHomeoProj (Q z')).2) :
    z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  have hQz : Q z = stripChart γ hγne 0 (annW z) := hQ.2.1 z hz hz1
  have hQz' : Q z' = stripChart γ hγne 0 (annW z') := hQ.2.1 z' hz' hz1'
  rw [hQz, hQz', cls_stripChart_zero, cls_stripChart_zero] at hcls
  obtain ⟨hd, hη⟩ := (classOfConf_eq_iff (confOf_snd_norm_le_one _)
    (confOf_snd_norm_le_one _)).mp hcls
  set w : EuclideanSpace ℝ (Fin 2) := annW z with hw
  set w' : EuclideanSpace ℝ (Fin 2) := annW z' with hw'
  have hdD : stripD γ w = stripD γ w' := by
    rw [← stripData_snd, ← stripData_snd]
    exact hd
  have hdir : Submission.Collision.dirC (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1)))
      = Submission.Collision.dirC (γ (Circle.exp (w' 0)) - γ (Circle.exp (w' 1))) := by
    rw [← stripData_snd_snd γ w, ← stripData_snd_snd γ w']
    simpa only [stripData] using hη
  -- the chord vectors do not vanish
  have hchordz : γ (Circle.exp (w 0)) ≠ γ (Circle.exp (w 1)) := by
    rw [hw]; exact chord_ne_of_annulus hγinj hz hz1
  have hDne : γ (Circle.exp (w 0)) - γ (Circle.exp (w 1)) ≠ 0 := fun h0 =>
    hchordz (sub_eq_zero.mp h0)
  have hchordz' : γ (Circle.exp (w' 0)) ≠ γ (Circle.exp (w' 1)) := by
    rw [hw']; exact chord_ne_of_annulus hγinj hz' hz1'
  have hDne' : γ (Circle.exp (w' 0)) - γ (Circle.exp (w' 1)) ≠ 0 := fun h0 =>
    hchordz' (sub_eq_zero.mp h0)
  -- the proportionality of the chord vectors
  obtain ⟨c, hcne, hcD⟩ := (dirC_eq_iff_collinear hDne' hDne).mp hdir.symm
  -- the chain data
  have hRpos : 0 < stripR γ w := by
    have h := stripData_pos hγne w
    rwa [stripData_fst] at h
  have hRpos' : 0 < stripR γ w' := by
    have h := stripData_pos hγne w'
    rwa [stripData_fst] at h
  have hDrel : stripChord γ w' = (c : ℂ) * stripChord γ w := by
    rw [stripChord_eq_cm, stripChord_eq_cm, ← cm_smul]
    exact congrArg cm hcD
  have hDneC : stripChord γ w ≠ 0 := by
    rw [stripChord_eq_cm]
    intro h0
    exact hDne (cm_injective (by rw [h0]; rfl))
  have hMrel := stripD_eq_imp_midrel hγne hdD
  have hRsq : stripR γ w ^ 2 = Complex.normSq (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ)
      + Complex.normSq (stripChord γ w) := stripR_sq γ w
  have hR'sq : stripR γ w' ^ 2 = Complex.normSq (⟨(stripMid γ w').1, (stripMid γ w').2⟩ : ℂ)
      + Complex.normSq (stripChord γ w') := stripR_sq γ w'
  have hρ : |c| = stripR γ w' / stripR γ w :=
    abs_eq_of_data_rel hRsq hR'sq hRpos hRpos' hMrel hDrel hDneC
  have hρpos : 0 < stripR γ w' / stripR γ w := div_pos hRpos' hRpos
  have hcsign : c = stripR γ w' / stripR γ w ∨ c = -(stripR γ w' / stripR γ w) := by
    have h2 : c ^ 2 = (stripR γ w' / stripR γ w) ^ 2 := by
      have h3 : |c| = |stripR γ w' / stripR γ w| := by
        rw [hρ, abs_of_pos hρpos]
      rw [← sq_abs c, ← sq_abs (stripR γ w' / stripR γ w), h3]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  -- the endpoint relations
  have hkey : (cm (γ (Circle.exp (w' 0)))
        = ((stripR γ w' / stripR γ w : ℝ) : ℂ) * cm (γ (Circle.exp (w 0)))
      ∧ cm (γ (Circle.exp (w' 1)))
        = ((stripR γ w' / stripR γ w : ℝ) : ℂ) * cm (γ (Circle.exp (w 1))))
      ∨ (cm (γ (Circle.exp (w' 0)))
        = ((stripR γ w' / stripR γ w : ℝ) : ℂ) * cm (γ (Circle.exp (w 1)))
      ∧ cm (γ (Circle.exp (w' 1)))
        = ((stripR γ w' / stripR γ w : ℝ) : ℂ) * cm (γ (Circle.exp (w 0)))) := by
    have hw0 : cm (γ (Circle.exp (w' 0)))
        = (⟨(stripMid γ w').1, (stripMid γ w').2⟩ : ℂ) + stripChord γ w' / 2 :=
      strip_cm_endpoint_zero γ w'
    have hw1 : cm (γ (Circle.exp (w' 1)))
        = (⟨(stripMid γ w').1, (stripMid γ w').2⟩ : ℂ) - stripChord γ w' / 2 :=
      strip_cm_endpoint_one γ w'
    have hz0 : cm (γ (Circle.exp (w 0)))
        = (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) + stripChord γ w / 2 :=
      strip_cm_endpoint_zero γ w
    have hz1 : cm (γ (Circle.exp (w 1)))
        = (⟨(stripMid γ w).1, (stripMid γ w).2⟩ : ℂ) - stripChord γ w / 2 :=
      strip_cm_endpoint_one γ w
    rcases hcsign with hc | hc
    · left
      exact ⟨by rw [hw0, hz0, hMrel, hDrel, hc]; push_cast; ring,
             by rw [hw1, hz1, hMrel, hDrel, hc]; push_cast; ring⟩
    · right
      exact ⟨by rw [hw0, hz1, hMrel, hDrel, hc]; push_cast; ring,
             by rw [hw1, hz0, hMrel, hDrel, hc]; push_cast; ring⟩
  -- the radial hypothesis turns a positive multiple into an equality of points
  have hpt : ∀ (p q : Circle) (lam : ℝ), 0 < lam → cm (γ p) = (lam : ℂ) * cm (γ q) → γ p = γ q := by
    intro p q lam hlam h
    exact hrad p q lam hlam (cm_injective (by rw [cm_smul]; exact h))
  rcases hkey with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hp0 : γ (Circle.exp (w' 0)) = γ (Circle.exp (w 0)) := hpt _ _ _ hρpos h0
    have hp1 : γ (Circle.exp (w' 1)) = γ (Circle.exp (w 1)) := hpt _ _ _ hρpos h1
    have he0 : Circle.exp (w' 0) = Circle.exp (w 0) := hγinj hp0
    have he1 : Circle.exp (w' 1) = Circle.exp (w 1) := hγinj hp1
    have hval : stripChart γ hγne 0 w = stripChart γ hγne 0 w' :=
      (stripChart_congr hγne 0 he0 he1).symm
    exact stripChart_annW_eq_imp hγne hγinj hz hz1 hz' hz1' (by rw [← hw, ← hw']; exact hval)
  · have hp0 : γ (Circle.exp (w' 0)) = γ (Circle.exp (w 1)) := hpt _ _ _ hρpos h0
    have hp1 : γ (Circle.exp (w' 1)) = γ (Circle.exp (w 0)) := hpt _ _ _ hρpos h1
    have he0 : Circle.exp (w' 0) = Circle.exp (w 1) := hγinj hp0
    have he1 : Circle.exp (w' 1) = Circle.exp (w 0) := hγinj hp1
    have hsd : stripData γ w' = stripData γ w := by
      have h1' : stripData γ w' = stripData γ (mk2 (w 1) (w 0)) :=
        stripData_eq_of_exp_eq (by simpa using he0) (by simpa using he1)
      rw [h1', stripData_swap]
    have hval : stripChart γ hγne 0 w = stripChart γ hγne 0 w' :=
      (stripChart_eq_of_stripData_eq hγne 0 hsd).symm
    exact stripChart_annW_eq_imp hγne hγinj hz hz1 hz' hz1' (by rw [← hw, ← hw']; exact hval)


lemma norm_c₁_capProjVecOf {w d : ℂ} (hw : ‖w‖ = 1) :
    ‖c₁ (capProjVecOf w d)‖ = ‖d‖ / Real.sqrt 2 := by
  rw [c₁_capProjVecOf, norm_div, norm_mul, hw]
  simp only [one_mul, mul_one]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

lemma norm_c₂_capProjVecOf {w d : ℂ} (hw : ‖w‖ = 1) :
    ‖c₂ (capProjVecOf w d)‖ = Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
  rw [c₂_capProjVecOf, norm_mul, norm_star, hw]
  simp only [one_mul, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The strict config-side inequality: for a configuration datum with `‖d‖ < 1` the class lift has
`‖c₂‖ < ‖c₁‖`. -/
lemma norm_c₂_lt_c₁_of_lt {u d : ℂ} (hu : ‖u‖ = 1) (hd : ‖d‖ < 1) :
    ‖c₂ (confProjVecOf u d)‖ < ‖c₁ (confProjVecOf u d)‖ := by
  rw [norm_c₂_confProjVecOf hu, norm_c₁_confProjVecOf hu, div_lt_iff₀
    (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
  have hsq : (‖d‖) ^ 2 < (Real.sqrt (1 - ‖d‖ ^ 2 / 2) * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith [norm_nonneg d, sq_nonneg ‖d‖]),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [norm_nonneg d, sq_nonneg ‖d‖]
  have h1 : (0:ℝ) ≤ ‖d‖ := norm_nonneg d
  have h2 : (0:ℝ) ≤ Real.sqrt (1 - ‖d‖ ^ 2 / 2) * Real.sqrt 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have := sq_lt_sq.mp hsq
  rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this

lemma norm_c₁_le_c₂_cap {w d : ℂ} (hw : ‖w‖ = 1) (hd : ‖d‖ ≤ 1) :
    ‖c₁ (capProjVecOf w d)‖ ≤ ‖c₂ (capProjVecOf w d)‖ := by
  rw [norm_c₁_capProjVecOf hw, norm_c₂_capProjVecOf hw, div_le_iff₀
    (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
  have hsq : (‖d‖) ^ 2 ≤ (Real.sqrt (1 - ‖d‖ ^ 2 / 2) * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith [norm_nonneg d, sq_nonneg ‖d‖]),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [norm_nonneg d, sq_nonneg ‖d‖]
  have h1 : (0:ℝ) ≤ ‖d‖ := norm_nonneg d
  have h2 : (0:ℝ) ≤ Real.sqrt (1 - ‖d‖ ^ 2 / 2) * Real.sqrt 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this

/-- **A strictly configuration-side class is not a cap class.** -/
lemma confProjVecOf_proj_ne_capProjVecOf {u w d d' : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hd : ‖d‖ < 1) (hd' : ‖d'‖ ≤ 1) :
    (Projectivization.mk ℝ (confProjVecOf u d) (confProjVecOf_ne_zero hu (le_of_lt hd))
      ≠ Projectivization.mk ℝ (capProjVecOf w d') (capProjVecOf_ne_zero hw hd')) := by
  intro h
  have h1 := norm_c₂_lt_c₁_of_lt hu hd
  have h2 := norm_c₁_le_c₂_cap hw hd'
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  rw [Units.smul_def] at ha
  have hc1 : ‖c₁ (confProjVecOf u d)‖ = ‖(a : ℝ)‖ * ‖c₁ (capProjVecOf w d')‖ := by
    rw [← ha, c₁_smul_real, norm_mul]
    simp
  have hc2 : ‖c₂ (confProjVecOf u d)‖ = ‖(a : ℝ)‖ * ‖c₂ (capProjVecOf w d')‖ := by
    rw [← ha, c₂_smul_real, norm_mul]
    simp
  nlinarith [norm_nonneg (a : ℝ)]


/-- **The region-restricted class injectivity of a plane chart**: for a point of the annulus `1/2 < ‖z‖ ≤ 1`
and *any* point of the closed disk with `‖z'‖ ≠ 1/2`, equality of the classes forces equality of the
parameters (up to the boundary antipodal identification), provided no two points of `γ` lie on a common
ray from the origin.

The case `‖z'‖ < 1/2` (the cap part) is settled by the config-side/cap-side dichotomy: a strip value
over a non-degenerate chord has a representative with `‖d‖ < 1`, i.e. `‖c₂‖ < ‖c₁‖`, while a cap point
has `‖c₁‖ ≤ ‖c₂‖`, and proportionality preserves the inequality. -/
theorem class_injective_of_radial {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    (hrad : ∀ (p q : Circle) (lam : ℝ), 0 < lam → γ p = lam • γ q → γ p = γ q)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {z z' : ℂ}
    (hz : 1 / 2 < ‖z‖) (hz1 : ‖z‖ ≤ 1) (hz1' : ‖z'‖ ≤ 1) (hne : ‖z'‖ ≠ 1 / 2)
    (hcls : (cappingSpaceHomeoProj (Q z)).2 = (cappingSpaceHomeoProj (Q z')).2) :
    z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- the cap part: the classes have different sides
    exfalso
    obtain ⟨c, hc⟩ := hQ.2.2.2 z' hlt
    obtain ⟨p, hp1, hp2⟩ := c
    have hcz := cappingSpaceHomeoProj_capPiece p hp1 hp2 (classRoot_sq p.2.1)
    have hQz : Q z = stripChart γ hγne 0 (annW z) := hQ.2.1 z hz hz1
    have hdlt : ‖(stripData γ (annW z)).2.1‖ < 1 :=
      stripData_snd_norm_lt_one_of_chord_ne (chord_ne_of_annulus hγinj hz hz1)
    have h1 : (cappingSpaceHomeoProj (Q z)).2
        = Projectivization.mk ℝ (confProjVecOf (classRoot ((stripData γ (annW z)).2.2))
            (stripData γ (annW z)).2.1)
            (confProjVecOf_ne_zero (classRoot_norm _) (le_of_lt hdlt)) := by
      rw [hQz, cls_stripChart_zero, classOfConf_eq_mk]
      simp only [stripData]
    have h2 : (cappingSpaceHomeoProj (Q z')).2
        = Projectivization.mk ℝ (capProjVecOf (classRoot p.2.1) p.2.2)
            (capProjVecOf_ne_zero (classRoot_norm _) hp2) := by
      rw [hc, hcz]
    exact (confProjVecOf_proj_ne_capProjVecOf (classRoot_norm _) (classRoot_norm _) hdlt hp2)
      (by rw [← h1, ← h2]; exact hcls)
  · exact class_annulus_injective_of_radial hγinj hrad hQ hz hz1 hgt hz1' hcls

/-- **The `hcls` hypothesis of `Work.Drive.ncard_cutFibreBox_clampedSweep_eq_one`**, for base points
whose disk image lies in the annulus `1/2 < ‖·‖`: the class of the disk presentation of the plane
determines the box parameter, under the star-shapedness of `γ` and with the box points off the
interface circle `‖sqDisk (foldBox y)‖ = 1/2` excluded. -/
theorem class_injective_diskPlane_of_annulus {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    (hrad : ∀ (p q : Circle) (lam : ℝ), 0 < lam → γ p = lam • γ q → γ p = γ q)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {u y : EuclideanSpace ℝ (Fin 2)} (hu : u ∈ Submission.Drive.unitBox 1)
    (hy : y ∈ Submission.Drive.unitBox 1)
    (hann : 1 / 2 < ‖sqDisk (foldBox u)‖) (hint : ‖sqDisk (foldBox u)‖ < 1)
    (hne : ‖sqDisk (foldBox y)‖ ≠ 1 / 2)
    (hcls : (cappingSpaceHomeoProj (diskPlane Q y)).2
      = (cappingSpaceHomeoProj (diskPlane Q u)).2) :
    y = u := by
  have hzu : ‖sqDisk (foldBox u)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox u)
  have hzy : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
  have h := class_injective_of_radial hγinj hrad hQ hann hzu hzy hne hcls.symm
  rcases h with h | ⟨h1, h2, h3⟩
  · have hyu : sqDisk (foldBox y) = sqDisk (foldBox u) := h.symm
    obtain ⟨w, hw, huniq⟩ := sqDisk_foldBox_existsUnique (sqDisk (foldBox u)) (le_of_lt hint)
    have h1' : y = w := huniq y ⟨hy, hyu⟩
    have h2' : u = w := huniq u ⟨hu, rfl⟩
    rw [h1', h2']
  · exact absurd h1 (ne_of_lt hint)


end
end Work.Drive
