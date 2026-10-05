import Mathlib
import Submission.Work.RPCore.Port.PushDisc.conicalFluxMachinery
import Submission.Work.RPCore.Port.PushDisc.coneVolumeInvariance

/-!
# The conical families and the smooth obstruction

The three straight-line conical families joining the identity to the antipodal self-map of the unit
sphere of `E = EuclideanSpace ℝ (Fin d)` through a smooth sphere-valued "avoiding" homotopy, and the
resulting **smooth obstruction**: for odd `d` there is no smooth sphere-valued homotopy which avoids
the antipodal map at time `0` and the identity at time `1`.

The conical signed volume `coneVol` of a self-map is invariant along each of the three families
(`coneVolume_invariant`), and its values at the two ends are `∫ χ > 0` and `(-1)^d ∫ χ < 0` for
`d` odd.
-/

namespace Work.RPCore.Port.PushDisc

open scoped Matrix Topology
open MeasureTheory Filter

variable {d : ℕ}

/-! ## The cone extension of a self-map of the sphere -/

/-- The radial projection to the unit sphere, total at the origin. -/
noncomputable def unitize (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (‖y‖)⁻¹ • y

/-- The cone extension `y ↦ ‖y‖ • f (y/‖y‖)` of a self-map of the unit sphere. -/
noncomputable def coneExt (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ‖y‖ • f (unitize y)

lemma unitize_of_norm_one {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ = 1) : unitize y = y := by
  rw [unitize, hy, inv_one, one_smul]

lemma norm_unitize {y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) : ‖unitize y‖ = 1 := by
  rw [unitize]
  exact norm_smul_inv_norm hy

lemma unitize_zero : unitize (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  simp [unitize]

lemma coneExt_congr {f g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → f x = g x) : coneExt f = coneExt g := by
  funext y
  rcases eq_or_ne y 0 with rfl | hy
  · simp [coneExt]
  · rw [coneExt, coneExt, h _ (norm_unitize hy)]

lemma coneExt_smul (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin d)) : coneExt f (r • y) = r • coneExt f y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [coneExt]
  · have h1 : ‖r • y‖ = r * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
    have h2 : unitize (r • y) = unitize y := by
      rw [unitize, unitize, h1]
      have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      have hr' : r ≠ 0 := ne_of_gt hr
      rw [smul_smul]
      congr 1
      field_simp
    rw [coneExt, coneExt, h1, h2, smul_smul]

lemma norm_coneExt (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → ‖f x‖ = 1)
    (y : EuclideanSpace ℝ (Fin d)) : ‖coneExt f y‖ = ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [coneExt]
  · rw [coneExt, norm_smul, Real.norm_of_nonneg (norm_nonneg y), hf _ (norm_unitize hy), mul_one]

/-! ## The three straight-line families -/

/-- The straight line from the identity to `H (0, ·)`, renormalised. -/
noncomputable def fam1 (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  unitize ((1 - s) • x + s • H (0, x))

/-- The homotopy `H` itself. -/
noncomputable def fam2 (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := H (s, x)

/-- The straight line from `H (1, ·)` to the antipodal map, renormalised. -/
noncomputable def fam3 (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  unitize ((1 - s) • H (1, x) - s • x)

/-- A segment between two unit vectors is nonzero unless its target is the antipode of its source. -/
lemma seg_add_ne_zero {u v : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : v ≠ -u) (s : ℝ) : (1 - s) • u + s • v ≠ 0 := by
  intro hc
  have h1 : (1 - s) • u = -(s • v) := eq_neg_of_add_eq_zero_left hc
  have h2 : |1 - s| = |s| := by
    have h3 := congrArg norm h1
    rw [norm_smul, norm_neg, norm_smul, hu, hv, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs] at h3
    exact h3
  have hs : s = 1 / 2 := by
    rcases abs_eq_abs.mp h2 with h3 | h3
    · linarith
    · linarith
  have hsum : u + v = 0 := by
    have h6 : (1 / 2 : ℝ) • (u + v) = 0 := by
      have hc' := hc
      rw [hs, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hc'
      rw [smul_add]
      exact hc'
    have h7 : (2 : ℝ) • ((1 / 2 : ℝ) • (u + v)) = 0 := by rw [h6, smul_zero]
    rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at h7
    exact h7
  have hv' : v = -u := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hsum
  exact h hv'

/-- A segment between two unit vectors is nonzero unless the two coincide. -/
lemma seg_sub_ne_zero {u v : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : v ≠ u) (s : ℝ) : (1 - s) • v - s • u ≠ 0 := by
  have h2 := seg_add_ne_zero (u := v) (v := -u) hv (by simpa using hu)
    (fun hc => h (neg_inj.mp hc).symm) s
  refine fun hc => h2 ?_
  rw [← hc]
  simp [sub_eq_add_neg, smul_neg]

theorem fam1_norm (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1)
    (h0 : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (0, x) ≠ -x) (s : ℝ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ = 1) : ‖fam1 H s y‖ = 1 := by
  have hne : (1 - s) • y + s • H (0, y) ≠ 0 := seg_add_ne_zero hy (hu 0 y hy) (h0 y hy) s
  rw [fam1, norm_unitize hne]

theorem fam2_norm (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1) (s : ℝ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ = 1) : ‖fam2 H s y‖ = 1 := hu s y hy

theorem fam3_norm (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1)
    (h1 : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (1, x) ≠ x) (s : ℝ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ = 1) : ‖fam3 H s y‖ = 1 := by
  have hne : (1 - s) • H (1, y) - s • y ≠ 0 :=
    seg_sub_ne_zero hy (hu 1 y hy) (h1 y hy) s
  rw [fam3, norm_unitize hne]

/-! ## Smoothness of the conical families -/

/-- The radial projection is smooth off the origin. -/
lemma contDiffOn_unitize_snd :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => unitize p.2) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
  have hnf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ‖p.2‖) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    ContDiffOn.norm ℝ (contDiff_snd.contDiffOn (s := {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0})) (fun p hp => hp)
  have hne0 : ∀ p ∈ {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0}, ‖p.2‖ ≠ 0 := fun p hp => norm_ne_zero_iff.mpr (hp)
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun p : ℝ × EuclideanSpace ℝ (Fin d) => (‖p.2‖)⁻¹) •
        fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.2) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    (hnf.inv hne0).smul contDiff_snd.contDiffOn
  have hcongr : (fun p : ℝ × EuclideanSpace ℝ (Fin d) => unitize p.2)
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (‖p.2‖)⁻¹) •
        fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.2 := rfl
  rw [hcongr]
  exact hsm

theorem contDiffOn_coneExt_fam1 (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1)
    (h0 : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (0, x) ≠ -x) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (fam1 H p.1) p.2) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
  have hnf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ‖p.2‖) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    ContDiffOn.norm ℝ (contDiff_snd.contDiffOn (s := {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0})) (fun p hp => hp)
  have hH0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => H (0, unitize p.2)) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : ℝ × EuclideanSpace ℝ (Fin d) => (0 : ℝ)) := contDiff_const
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ((0 : ℝ), unitize p.2))
        {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
      hc.contDiffOn.prodMk contDiffOn_unitize_snd
    have := hsm.comp_contDiffOn hpair
    simpa only [Function.comp_def] using this
  have hcomb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (1 - p.1) • unitize p.2 + p.1 • H (0, unitize p.2))
      {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    (((contDiff_const.sub contDiff_fst).contDiffOn).smul contDiffOn_unitize_snd).add
      (contDiff_fst.contDiffOn.smul hH0)
  have hne : ∀ p ∈ {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0},
      (1 - p.1) • unitize p.2 + p.1 • H (0, unitize p.2) ≠ 0 := by
    intro p hp
    have h1 : ‖unitize p.2‖ = 1 := norm_unitize hp
    exact seg_add_ne_zero (u := unitize p.2) (v := H (0, unitize p.2)) h1 (hu 0 _ h1) (h0 _ h1) p.1
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
        unitize ((1 - p.1) • unitize p.2 + p.1 • H (0, unitize p.2))) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
    have hne0 : ∀ p ∈ {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0},
        ‖(1 - p.1) • unitize p.2 + p.1 • H (0, unitize p.2)‖ ≠ 0 :=
      fun p hp => norm_ne_zero_iff.mpr (hne p hp)
    exact (((hcomb.norm ℝ hne).inv hne0).smul hcomb)
  exact hnf.smul hU

theorem contDiffOn_coneExt_fam2 (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (fam2 H p.1) p.2) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
  have hnf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ‖p.2‖) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    ContDiffOn.norm ℝ (contDiff_snd.contDiffOn (s := {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0})) (fun p hp => hp)
  have hH : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => H (p.1, unitize p.2)) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
    have := hsm.comp_contDiffOn (contDiff_fst.contDiffOn.prodMk contDiffOn_unitize_snd)
    simpa only [Function.comp_def] using this
  exact hnf.smul hH

theorem contDiffOn_coneExt_fam3 (H : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hu : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖H (t, x)‖ = 1)
    (h1 : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → H (1, x) ≠ x) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (fam3 H p.1) p.2) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
  have hnf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ‖p.2‖) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    ContDiffOn.norm ℝ (contDiff_snd.contDiffOn (s := {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0})) (fun p hp => hp)
  have hH1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => H (1, unitize p.2)) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : ℝ × EuclideanSpace ℝ (Fin d) => (1 : ℝ)) := contDiff_const
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin d) => ((1 : ℝ), unitize p.2))
        {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
      hc.contDiffOn.prodMk contDiffOn_unitize_snd
    have := hsm.comp_contDiffOn hpair
    simpa only [Function.comp_def] using this
  have hcomb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => (1 - p.1) • H (1, unitize p.2) - p.1 • unitize p.2)
      {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} :=
    (((contDiff_const.sub contDiff_fst).contDiffOn).smul hH1).sub
      (contDiff_fst.contDiffOn.smul contDiffOn_unitize_snd)
  have hne : ∀ p ∈ {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0},
      (1 - p.1) • H (1, unitize p.2) - p.1 • unitize p.2 ≠ 0 := by
    intro p hp
    have h2 : ‖unitize p.2‖ = 1 := norm_unitize hp
    exact seg_sub_ne_zero (u := unitize p.2) (v := H (1, unitize p.2)) h2 (hu 1 _ h2) (h1 _ h2) p.1
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
        unitize ((1 - p.1) • H (1, unitize p.2) - p.1 • unitize p.2)) {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0} := by
    have hne0 : ∀ p ∈ {p : ℝ × EuclideanSpace ℝ (Fin d) | p.2 ≠ 0},
        ‖(1 - p.1) • H (1, unitize p.2) - p.1 • unitize p.2‖ ≠ 0 :=
      fun p hp => norm_ne_zero_iff.mpr (hne p hp)
    exact (((hcomb.norm ℝ hne).inv hne0).smul hcomb)
  exact hnf.smul hU

/-! ## The conical signed volume -/

/-- The conical signed volume of a self-map of the sphere: the signed volume of its cone
extension, weighted by the annular cut-off `χ`. -/
noncomputable def coneVol (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, chi y * (jacM (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt f p.2) (0, y)).det

lemma coneVol_congr {f g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → f x = g x) : coneVol f = coneVol g := by
  have h1 : coneExt f = coneExt g := coneExt_congr h
  rw [coneVol, coneVol,
    show (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt f p.2)
        = (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt g p.2) from by
      funext p; rw [h1]]

/-- The `t`-slice of the conical family of `F` at time `a` is the cone extension of `F a`. -/
lemma coneVol_eq_family (F : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    (∫ y, chi y *
        (jacM (fun p : ℝ × EuclideanSpace ℝ (Fin d) => coneExt (F p.1) p.2) (a, y)).det)
      = coneVol (F a) := rfl

end Work.RPCore.Port.PushDisc
