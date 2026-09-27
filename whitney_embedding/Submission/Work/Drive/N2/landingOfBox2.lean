import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.levelBoundsOfJourney
import Submission.Work.Drive.N2.sepClosedModelBall

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-!
# The landing row of the `n = 2` critical-window drawing (box condition)

`Work.Drive.N2.landingOfBox2`: a point `x` of the window band whose *invariant* `Im (Zs x)²` is
bounded below by the entry bound (`x ∉ modelBall (φ j) (ρ j)`, or `c₀ · lam0² ≤ |Im (Zs x)²|` with
`c₀ > 1`) reaches the anchor level `f p - lam0² η` under the model-adapted flow, i.e.

  `f (Φ (f p - lam0² η - f x, x)) = f p - lam0² η`.

The mathematical content is the first-entry argument of `Work.Drive.N2.journeyAvoids_of_chartODE`,
run on the marked saddle chart: as long as the backward journey stays off the small model ball of
the marked chart (of radius `lam0 = ρ j / 8`) and off the *other* charts' model balls, the level law
of the model-adapted flow (`WindowDatum.hlevel`) integrates to `f (Φ (t,x)) = f x + t`, so the
journey lands exactly on the anchor level.  The two obstructions are excluded as follows:

* the other charts' model balls carry values at distance `> 2 ηd > lam0² η` from `f p`
  (`sepClosedModelBall`), while the journey (by `orbit_pair_bound`) never exceeds the band;
* an entry of the journey into the marked small ball is impossible: the `Im (Z ·)²` invariant
  (`WindowDatum.him`) propagates the entry bound along the initial run of the journey inside the
  closed chart region `C j`; if that run reaches time `0` then `x ∈ C j` and the entry bound holds
  at `x`, and if it stops at an *exit* point of the chart region then the exit point (of chart norm
  `≥ ρ j`) has `|Re (Z ·)²| ≥ √(ρ j⁴ - lam0⁴) ≫ lam0²`, while monotonicity of `f` along the journey
  keeps `Re (Z ·)²` below `lam0² η`.
-/

/-! ## Elementary private facts about the complex model coordinate -/

private lemma lob_modelBall_mono {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) {r r' : ℝ} (h : r ≤ r') :
    modelBall φ r ⊆ modelBall φ r' := fun _ hy => ⟨hy.1, lt_of_lt_of_le hy.2 h⟩

private lemma lob_isOpen_modelBall {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (modelBall φ r) := by
  have h := φ.isOpen_inter_preimage (s := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)
    Metric.isOpen_ball
  convert h using 1
  ext y
  simp [modelBall, Metric.mem_ball]

private lemma lob_norm_eq_of_chart {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (Z : M → ℂ) (hZ : ∀ m : M, Z m = (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I) (m : M) :
    ‖Z m‖ = ‖φ m‖ := by
  have hsq : ‖Z m‖ ^ 2 = ‖φ m‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hZ m]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
    ring
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

private lemma lob_im_sq_lt_of_norm_lt {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ < r) :
    |(z ^ 2).im| < r ^ 2 := by
  have h : ‖z ^ 2‖ < r ^ 2 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  exact lt_of_le_of_lt (Complex.abs_im_le_norm _) h

private lemma lob_neg_sq_lt_re_of_norm_lt {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ < r) :
    -(r ^ 2) < (z ^ 2).re := by
  have h : ‖z ^ 2‖ < r ^ 2 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have h2 : -‖z ^ 2‖ ≤ (z ^ 2).re := (abs_le.mp (Complex.abs_re_le_norm _)).1
  linarith

private lemma lob_im_sq_ge_of_norm_ge {z : ℂ} {R η : ℝ} (hR0 : 0 ≤ R) (hη : 0 ≤ η) (hR : R ≤ ‖z‖)
    (hre : |(z ^ 2).re| < η) : R ^ 4 - η ^ 2 ≤ ((z ^ 2).im) ^ 2 := by
  have hnorm : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  have hsq : ‖z ^ 2‖ ^ 2 = (z ^ 2).re ^ 2 + (z ^ 2).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h3 : R ^ 4 ≤ ‖z ^ 2‖ ^ 2 := by
    rw [hnorm]
    have h4 : R ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hR0 hR 2
    calc R ^ 4 = (R ^ 2) ^ 2 := by ring
      _ ≤ (‖z‖ ^ 2) ^ 2 := pow_le_pow_left₀ (pow_nonneg hR0 2) h4 2
  have hre2 : (z ^ 2).re ^ 2 < η ^ 2 := by
    have h : |(z ^ 2).re| < |η| := by rwa [abs_of_nonneg hη]
    have := (sq_lt_sq (a := (z ^ 2).re) (b := η)).mpr h
    simpa using this
  nlinarith [hsq, h3, hre2]

private lemma lob_re_sq_ge_of_norm_ge_of_im_lt {z : ℂ} {R r : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ ‖z‖)
    (him : |(z ^ 2).im| < r ^ 2) : R ^ 4 - r ^ 4 ≤ ((z ^ 2).re) ^ 2 := by
  have hnorm : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  have hsq : ‖z ^ 2‖ ^ 2 = (z ^ 2).re ^ 2 + (z ^ 2).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h3 : R ^ 4 ≤ ‖z ^ 2‖ ^ 2 := by
    rw [hnorm]
    have h4 : R ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hR0 hR 2
    calc R ^ 4 = (R ^ 2) ^ 2 := by ring
      _ ≤ (‖z‖ ^ 2) ^ 2 := pow_le_pow_left₀ (pow_nonneg hR0 2) h4 2
  have him2 : (z ^ 2).im ^ 2 < (r ^ 2) ^ 2 := by
    have h : |(z ^ 2).im| < |r ^ 2| := by rwa [abs_of_nonneg (sq_nonneg r)]
    exact (sq_lt_sq (a := (z ^ 2).im) (b := r ^ 2)).mpr h
  have hr4 : (r ^ 2) ^ 2 = r ^ 4 := by ring
  rw [hr4] at him2
  nlinarith [hsq, h3, him2]

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The other charts' forbidden set -/

/-- The union of the *closures* of the model balls of the charts of the datum other than the marked
one: the forbidden set of the journey argument. -/
def otherBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) : Set M :=
  ⋃ i : {i : Fin D.N // i ≠ D.j}, closure (modelBall (D.φ i.1) (D.ρ i.1 / 8))

/-- The other charts' forbidden set is closed. -/
theorem isClosed_otherBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) :
    IsClosed (otherBalls D) :=
  isClosed_iUnion_of_finite fun _ => isClosed_closure

/-- **The value separation off the other charts' forbidden set.** -/
theorem val_sep_of_mem_otherBalls {f : M → ℝ} {p : M} (D : WindowDatum f p) {lam0 η : ℝ}
    (hlam0 : lam0 = D.ρ D.j / 8) (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {y : M} (hy : y ∈ otherBalls D) : lam0 ^ 2 * η < |f y - f p| := by
  rw [otherBalls] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  have h := sepClosedModelBall D i.2 y hi
  have h' : lam0 ^ 2 * η = (D.ρ D.j / 8) ^ 2 * η := by rw [hlam0]
  linarith [h']

/-- Avoiding the marked small ball and the other charts' forbidden set is avoiding *all* the model
balls of the datum. -/
theorem notMem_modelBall_of_notMem {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) {lam0 : ℝ}
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r) {y : M}
    (hy : y ∉ modelBall φ' lam0) (hKy : y ∉ otherBalls D) :
    ∀ i : Fin D.N, y ∉ modelBall (D.φ i) (D.ρ i / 8) := by
  intro i hi
  by_cases hij : i = D.j
  · subst hij
    refine hy ?_
    rw [hball]
    rwa [hlam0]
  · refine hKy ?_
    rw [otherBalls]
    exact Set.mem_iUnion.mpr ⟨⟨i, hij⟩, subset_closure hi⟩

/-! ## The journey of a box point avoids every model ball -/

set_option maxHeartbeats 1000000 in
/-- **The journey of a box point of the window band avoids every model ball of the datum**, and its
values stay in the (closed) band. -/
theorem journeyAvoidsOfBox {f : M → ℝ} {p : M} (D : WindowDatum f p)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {x : M}
    (hbox : x ∉ modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs x) ^ 2).im|)
    (hband : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    ∀ u ∈ Set.Icc (min 0 (f p - lam0 ^ 2 * η - f x)) (max 0 (f p - lam0 ^ 2 * η - f x)),
      (∀ i : Fin D.N, D.Φ (u, x) ∉ modelBall (D.φ i) (D.ρ i / 8)) ∧
      f (D.Φ (u, x)) ∈ Set.Icc (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η) := by
  -- ### basic notations
  have hlam0pos : 0 < lam0 := by rw [hlam0]; exact div_pos (D.hρ D.j) (by norm_num)
  have hR_eq : D.ρ D.j = 8 * lam0 := by rw [hlam0]; ring
  have hRpos : 0 < D.ρ D.j := D.hρ D.j
  have hηp : 0 < lam0 ^ 2 * η := mul_pos (pow_pos hlam0pos 2) hη
  have hηR : (lam0 ^ 2 * η) ^ 2 + lam0 ^ 4 ≤ (D.ρ D.j) ^ 4 := by
    rw [hR_eq]
    have h1 : (lam0 ^ 2 * η) ^ 2 = lam0 ^ 4 * η ^ 2 := by ring
    have h2 : (8 * lam0) ^ 4 = 4096 * lam0 ^ 4 := by ring
    rw [h1, h2]
    have h3 : η ^ 2 ≤ 1 := by nlinarith [hη, hη']
    have h4 : lam0 ^ 4 * η ^ 2 ≤ lam0 ^ 4 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith [h4, pow_pos hlam0pos 4]
  have hnum : lam0 ^ 2 + 2 * (lam0 ^ 2 * η) < Real.sqrt ((D.ρ D.j) ^ 4 - lam0 ^ 4) := by
    rw [hR_eq]
    have h1 : (8 * lam0) ^ 4 - lam0 ^ 4 = lam0 ^ 4 * 4095 := by ring
    rw [h1]
    have hsq : Real.sqrt (lam0 ^ 4 * 4095) = lam0 ^ 2 * Real.sqrt 4095 := by
      have h4 : lam0 ^ 4 = (lam0 ^ 2) ^ 2 := by ring
      rw [h4, Real.sqrt_mul (sq_nonneg (lam0 ^ 2)), Real.sqrt_sq (sq_nonneg lam0)]
    rw [hsq]
    have h4095 : (1 : ℝ) + 2 * η < Real.sqrt 4095 := by
      have h1 : Real.sqrt ((6 / 5 : ℝ) ^ 2) ≤ Real.sqrt 4095 := Real.sqrt_le_sqrt (by norm_num)
      rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 6 / 5)] at h1
      linarith [hη']
    have h2 : lam0 ^ 2 + 2 * (lam0 ^ 2 * η) = lam0 ^ 2 * (1 + 2 * η) := by ring
    rw [h2]
    exact mul_lt_mul_of_pos_left h4095 (pow_pos hlam0pos 2)
  set T : ℝ := f p - lam0 ^ 2 * η - f x with hTdef
  have hTneg : T < 0 := by rw [hTdef]; linarith [hband.1]
  have hjour : Continuous fun t : ℝ => D.Φ (t, x) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hCsrcJ : D.C D.j ⊆ (D.φ D.j).source := D.hCsub D.j
  have hCsrc' : D.C D.j ⊆ φ'.source := fun y hy => by rw [hsrc]; exact hCsrcJ hy
  have hlam0_le_R : lam0 ≤ D.ρ D.j := by rw [hR_eq]; linarith
  have hCV : modelBall φ' (D.ρ D.j) ⊆ D.C D.j := by
    intro y hy
    rw [hball] at hy
    exact D.hCop D.j hy
  have hKcl : IsClosed (otherBalls D) := isClosed_otherBalls D
  have hKval : ∀ y ∈ otherBalls D, lam0 ^ 2 * η < |f y - f p| :=
    fun y hy => val_sep_of_mem_otherBalls D hlam0 hsep hy
  -- ### monotonicity of the level along the journey
  have hmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → f (D.Φ (t₁, x)) ≤ f (D.Φ (t₂, x)) := by
    intro t₁ t₂ h12
    have h := D.hmono (D.Φ (t₁, x)) (le_refl (0 : ℝ)) (sub_nonneg.mpr h12) (sub_nonneg.mpr h12)
    simp only [D.hΦ0, D.hΦcomp, sub_add_cancel] at h
    exact h
  -- ### the entry inequality at a point of the chart region
  have hH_of : x ∈ D.C D.j → lam0 ^ 2 ≤ |((Zs x) ^ 2).im| := by
    intro hxC
    have hxsrcJ : x ∈ (D.φ D.j).source := hCsrcJ hxC
    have hxsrc' : x ∈ φ'.source := hCsrc' hxC
    rcases hbox with hbox1 | hbox2
    · have hxR : x ∉ modelBall φ' (D.ρ D.j) := by rw [hball]; exact hbox1
      have hRle : D.ρ D.j ≤ ‖Zs x‖ := by
        rw [lob_norm_eq_of_chart φ' Zs hZs x]
        by_contra hlt
        push_neg at hlt
        exact hxR ⟨hxsrc', hlt⟩
      have hre : |((Zs x) ^ 2).re| < lam0 ^ 2 * η := by
        have h1 : ((Zs x) ^ 2).re = f x - f p := by
          have h2 := hlev x hxsrcJ
          linarith
        rw [h1, abs_lt]
        exact ⟨by linarith [hband.1], by linarith [hband.2]⟩
      have h4 := lob_im_sq_ge_of_norm_ge hRpos.le hηp.le hRle hre
      have h5 : (lam0 ^ 2) ^ 2 ≤ ((Zs x) ^ 2).im ^ 2 := by
        have h6 : lam0 ^ 4 ≤ (D.ρ D.j) ^ 4 - (lam0 ^ 2 * η) ^ 2 := by linarith [hηR]
        have h7 : (lam0 ^ 2) ^ 2 = lam0 ^ 4 := by ring
        rw [h7]
        linarith
      have h8 := (sq_le_sq (a := lam0 ^ 2) (b := ((Zs x) ^ 2).im)).mp h5
      rwa [abs_of_nonneg (sq_nonneg lam0)] at h8
    · have h0pos : (0 : ℝ) < lam0 ^ 2 := pow_pos hlam0pos 2
      calc lam0 ^ 2 = 1 * lam0 ^ 2 := by ring
        _ ≤ c₀ * lam0 ^ 2 := by nlinarith [hc₀, h0pos]
        _ ≤ |((Zs x) ^ 2).im| := hbox2
  -- ### step 2: the journey never enters the marked small ball
  have hBall : ∀ v ∈ Set.Icc T 0, D.Φ (v, x) ∉ modelBall φ' lam0 := by
    intro v hv hbv
    have hv0 : v ≤ 0 := hv.2
    have hbvC : D.Φ (v, x) ∈ D.C D.j := by
      rw [hball] at hbv
      exact D.hCop D.j (lob_modelBall_mono (D.φ D.j) hlam0_le_R hbv)
    set E : Set ℝ := {u : ℝ | u ∈ Set.Icc v 0 ∧
      ∀ w ∈ Set.Icc v u, D.Φ (w, x) ∈ D.C D.j} with hE
    have hvE : v ∈ E := by
      rw [hE]
      refine ⟨⟨le_rfl, hv0⟩, fun w hw => ?_⟩
      have hwv : w = v := le_antisymm hw.2 hw.1
      rw [hwv]; exact hbvC
    have hEne : E.Nonempty := ⟨v, hvE⟩
    have hEbdd : BddAbove E := ⟨0, fun u hu => (by rw [hE] at hu; exact hu.1.2)⟩
    set a : ℝ := sSup E with ha
    have hva : v ≤ a := le_csSup hEbdd hvE
    have ha0 : a ≤ 0 := csSup_le hEne (fun u hu => by rw [hE] at hu; exact hu.1.2)
    have hacl : a ∈ closure E := csSup_mem_closure hEne hEbdd
    have hCrun : ∀ w ∈ Set.Icc v a, D.Φ (w, x) ∈ D.C D.j := by
      intro w hw
      rcases lt_or_eq_of_le hw.2 with hlt | heq
      · obtain ⟨u, huE, hwu⟩ := (lt_csSup_iff hEbdd hEne).mp hlt
        rw [hE] at huE
        exact huE.2 w ⟨hw.1, le_of_lt hwu⟩
      · subst heq
        have himg : D.Φ (a, x) ∈ (fun t : ℝ => D.Φ (t, x)) '' closure E := ⟨a, hacl, rfl⟩
        have hsub : (fun t : ℝ => D.Φ (t, x)) '' E ⊆ D.C D.j := by
          rintro _ ⟨u, huE, rfl⟩
          rw [hE] at huE
          exact huE.2 u ⟨huE.1.1, le_rfl⟩
        have hcl : closure ((fun t : ℝ => D.Φ (t, x)) '' E) ⊆ D.C D.j := by
          rw [← (D.hCclosed D.j).closure_eq]
          exact closure_mono hsub
        exact hcl ((image_closure_subset_closure_image hjour) himg)
    have hbnd : |((Zs (D.Φ (v, x))) ^ 2).im| < lam0 ^ 2 := by
      have hnorm : ‖Zs (D.Φ (v, x))‖ < lam0 := by
        rw [lob_norm_eq_of_chart φ' Zs hZs (D.Φ (v, x))]
        exact hbv.2
      exact lob_im_sq_lt_of_norm_lt hlam0pos hnorm
    have hima : ((Zs (D.Φ (a, x))) ^ 2).im = ((Zs (D.Φ (v, x))) ^ 2).im := by
      have hseg : ∀ u ∈ Set.Icc (min 0 (a - v)) (max 0 (a - v)),
          D.Φ (u, D.Φ (v, x)) ∈ D.C D.j := by
        intro u hu
        rw [min_eq_left (by linarith : (0 : ℝ) ≤ a - v),
          max_eq_right (by linarith : (0 : ℝ) ≤ a - v)] at hu
        rw [D.hΦcomp u v x]
        exact hCrun (u + v) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have h := him (D.Φ (v, x)) (a - v) hseg
      rw [D.hΦcomp (a - v) v x, show a - v + v = a from by ring] at h
      exact h
    rcases lt_or_eq_of_le ha0 with halt | haeq
    · -- ### the run stops strictly before `0`: an exit point of radius at least `ρ j`
      have haC : D.Φ (a, x) ∈ D.C D.j := hCrun a ⟨hva, le_rfl⟩
      have hRa : D.Φ (a, x) ∉ modelBall φ' (D.ρ D.j) := by
        intro hmem
        have hpre : {t : ℝ | D.Φ (t, x) ∈ modelBall φ' (D.ρ D.j)} ∈ 𝓝 a :=
          hjour.continuousAt ((lob_isOpen_modelBall φ' (D.ρ D.j)).mem_nhds hmem)
        obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp hpre
        set s : ℝ := a + min ε (-a) / 2 with hsdef
        have hsa : a < s := by
          rw [hsdef]
          have : 0 < min ε (-a) := lt_min hε0 (by linarith)
          linarith
        have hs0 : s ≤ 0 := by
          rw [hsdef]
          have h2 : min ε (-a) ≤ -a := min_le_right _ _
          linarith
        have hsE : s ∈ E := by
          rw [hE]
          refine ⟨⟨le_trans hva hsa.le, hs0⟩, fun w hw => ?_⟩
          rcases le_or_gt w a with hwa | hwa
          · exact hCrun w ⟨hw.1, hwa⟩
          · have hd : dist w a < ε := by
              rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - a)]
              have h3 : min ε (-a) ≤ ε := min_le_left _ _
              linarith [hw.2, h3]
            exact hCV (hε (Metric.mem_ball.mpr hd))
        have := le_csSup hEbdd hsE
        linarith
      have hnorma : D.ρ D.j ≤ ‖Zs (D.Φ (a, x))‖ := by
        rw [lob_norm_eq_of_chart φ' Zs hZs (D.Φ (a, x))]
        by_contra hlt
        push_neg at hlt
        exact hRa ⟨hCsrc' haC, hlt⟩
      have hIma : |((Zs (D.Φ (a, x))) ^ 2).im| < lam0 ^ 2 := by rw [hima]; exact hbnd
      have hkey := lob_re_sq_ge_of_norm_ge_of_im_lt (R := D.ρ D.j) (r := lam0) hRpos.le hnorma hIma
      have hsqrt : Real.sqrt ((D.ρ D.j) ^ 4 - lam0 ^ 4) ≤ |((Zs (D.Φ (a, x))) ^ 2).re| := by
        have := Real.sqrt_le_sqrt hkey
        rwa [Real.sqrt_sq_eq_abs] at this
      have hrea : ((Zs (D.Φ (a, x))) ^ 2).re = f (D.Φ (a, x)) - f p := by
        have h2 := hlev (D.Φ (a, x)) (hCsrcJ haC)
        linarith
      have hrealt : ((Zs (D.Φ (a, x))) ^ 2).re < lam0 ^ 2 * η := by
        rw [hrea]
        have hmonoa : f (D.Φ (a, x)) ≤ f x := by
          have h := hmono a 0 halt.le
          rwa [D.hΦ0] at h
        linarith [hband.2]
      have h1 : lam0 ^ 2 + 2 * (lam0 ^ 2 * η) < |((Zs (D.Φ (a, x))) ^ 2).re| :=
        lt_of_lt_of_le hnum hsqrt
      have h2 : ((Zs (D.Φ (a, x))) ^ 2).re < 0 := by
        by_contra h
        push_neg at h
        rw [abs_of_nonneg h] at h1
        nlinarith [h1, hrealt, hηp, hlam0pos]
      have hfalse : ((Zs (D.Φ (a, x))) ^ 2).re < -(lam0 ^ 2 + 2 * (lam0 ^ 2 * η)) := by
        rw [abs_of_neg h2] at h1
        linarith
      have hreva : ((Zs (D.Φ (v, x))) ^ 2).re = f (D.Φ (v, x)) - f p := by
        have h2 := hlev (D.Φ (v, x)) (hCsrcJ hbvC)
        linarith
      have hmonov : f (D.Φ (v, x)) ≤ f (D.Φ (a, x)) := hmono v a hva
      have hcontr : ((Zs (D.Φ (v, x))) ^ 2).re ≤ ((Zs (D.Φ (a, x))) ^ 2).re := by
        rw [hreva, hrea]; linarith
      have hnormv : ‖Zs (D.Φ (v, x))‖ < lam0 := by
        rw [lob_norm_eq_of_chart φ' Zs hZs (D.Φ (v, x))]
        exact hbv.2
      have hgv := lob_neg_sq_lt_re_of_norm_lt hlam0pos hnormv
      linarith
    · -- ### the run reaches `0`: the entry inequality at `x` is contradicted
      have hxC : x ∈ D.C D.j := by
        have h := hCrun 0 ⟨le_trans hva ha0, le_of_eq haeq.symm⟩
        rwa [D.hΦ0 x] at h
      have hH := hH_of hxC
      have h0 : D.Φ (a, x) = x := by rw [haeq, D.hΦ0]
      rw [← hima, h0] at hbnd
      linarith [hH, hbnd]
  -- ### step 3: the journey never enters the other charts' forbidden set
  have hxK : x ∉ otherBalls D := by
    intro hx
    have h := hKval x hx
    have hb : |f x - f p| < lam0 ^ 2 * η := by
      rw [abs_lt]
      exact ⟨by linarith [hband.1], by linarith [hband.2]⟩
    linarith
  have hKavoid : ∀ v ∈ Set.Icc T 0, D.Φ (v, x) ∉ otherBalls D := by
    intro v hv hKv
    set A : Set ℝ := (fun u : ℝ => D.Φ (u, x)) ⁻¹' otherBalls D ∩ Set.Icc T 0 with hA
    have hAcl : IsClosed A := (hKcl.preimage hjour).inter isClosed_Icc
    have hAne : A.Nonempty := ⟨v, hKv, hv⟩
    have hAbdd : BddAbove A := ⟨0, fun u hu => hu.2.2⟩
    set s : ℝ := sSup A with hs
    have hsA : s ∈ A := hAcl.csSup_mem hAne hAbdd
    have hsK : D.Φ (s, x) ∈ otherBalls D := hsA.1
    have hsT0 : s ∈ Set.Icc T 0 := hsA.2
    have hsne : s ≠ 0 := by intro h0; rw [h0, D.hΦ0] at hsK; exact hxK hsK
    have hslt : s < 0 := lt_of_le_of_ne hsT0.2 hsne
    have hlaw : ∀ t ∈ Set.Ioc s 0, f (D.Φ (t, x)) = f x + t := by
      intro t ht
      have htI : t ∈ Set.Icc T 0 := ⟨le_trans hsT0.1 ht.1.le, ht.2⟩
      refine D.hlevel x t (fun w hw i => ?_)
      rw [min_eq_right ht.2, max_eq_left ht.2] at hw
      have hwI : w ∈ Set.Icc T 0 := ⟨le_trans htI.1 hw.1, hw.2⟩
      refine notMem_modelBall_of_notMem D φ' hlam0 hball (hBall w hwI) (fun hwK => ?_) i
      have hws : w ≤ s := by
        rw [hs]
        exact le_csSup hAbdd (show w ∈ A from ⟨hwK, hwI⟩)
      linarith [hw.1, hws, ht.1]
    have hsb : f (D.Φ (s, x)) ≤ f x + s := by
      by_contra hcon
      push_neg at hcon
      have hε : 0 < f (D.Φ (s, x)) - (f x + s) := by linarith
      set t : ℝ := s + min ((f (D.Φ (s, x)) - (f x + s)) / 2) ((-s) / 2) with htdef
      have hst : s < t := by
        rw [htdef]
        have : 0 < min ((f (D.Φ (s, x)) - (f x + s)) / 2) ((-s) / 2) :=
          lt_min (by linarith) (by linarith)
        linarith
      have ht0 : t ≤ 0 := by
        rw [htdef]
        have h2 : min ((f (D.Φ (s, x)) - (f x + s)) / 2) ((-s) / 2) ≤ (-s) / 2 :=
          min_le_right _ _
        linarith
      have ht : t ∈ Set.Ioc s 0 := ⟨hst, ht0⟩
      have hval := hlaw t ht
      have hmon := hmono s t hst.le
      have hle : f (D.Φ (s, x)) ≤ f x + t := by rw [← hval]; exact hmon
      have hlt' : t < s + (f (D.Φ (s, x)) - (f x + s)) := by
        rw [htdef]
        have h2 : min ((f (D.Φ (s, x)) - (f x + s)) / 2) ((-s) / 2)
            ≤ (f (D.Φ (s, x)) - (f x + s)) / 2 := min_le_left _ _
        linarith
      linarith
    have hsa : f x + s ≤ f (D.Φ (s, x)) := by
      have h := orbit_pair_bound D x s 0 hslt.le
      rw [D.hΦ0 x] at h
      linarith
    have hsval : f (D.Φ (s, x)) = f x + s := le_antisymm hsb hsa
    have hsband : |f (D.Φ (s, x)) - f p| ≤ lam0 ^ 2 * η := by
      rw [hsval, abs_le]
      exact ⟨by linarith [hsT0.1, hTdef], by linarith [hsT0.2, hband.2]⟩
    have h := hKval (D.Φ (s, x)) hsK
    linarith
  -- ### step 4: the value row
  intro u hu
  rw [min_eq_right hTneg.le, max_eq_left hTneg.le] at hu
  refine ⟨fun i => notMem_modelBall_of_notMem D φ' hlam0 hball (hBall u hu) (hKavoid u hu) i, ?_⟩
  have hval : f (D.Φ (u, x)) = f x + u := by
    refine D.hlevel x u (fun w hw i => ?_)
    rw [min_eq_right hu.2, max_eq_left hu.2] at hw
    have hwI : w ∈ Set.Icc T 0 := ⟨le_trans hu.1 hw.1, hw.2⟩
    exact notMem_modelBall_of_notMem D φ' hlam0 hball (hBall w hwI) (hKavoid w hwI) i
  rw [hval, Set.mem_Icc]
  exact ⟨by linarith [hu.1, hTdef], by linarith [hu.2, hband.2]⟩

theorem landingOfBox2 {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs : M → ℂ) (lam0 : ℝ)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀ : 1 < c₀)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd)
    {x : M}
    (hbox : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
      c₀ * lam0 ^ 2 ≤ |((Zs x) ^ 2).im|)
    (hband : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    f (D.Φ (f p - lam0 ^ 2 * η - f x, x)) = f p - lam0 ^ 2 * η := by
  have h := journeyAvoidsOfBox D φ' Zs lam0 hlam0 hsrc hball hZs hlev him hη hη' hc₀ hsep hbox hband
  have hlaw := D.hlevel x (f p - lam0 ^ 2 * η - f x)
    (fun u hu i => (h u hu).1 i)
  rw [hlaw]
  ring

end Work.Drive.N2
