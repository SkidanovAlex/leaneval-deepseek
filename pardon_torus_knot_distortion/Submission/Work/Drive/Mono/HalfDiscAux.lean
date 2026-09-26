import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.GaugeRadialDefs

/-!
# Half-discs, the coning of a circle homeomorphism, and the gluing lemma

Local copy (for the `emptyInterior_discParam` development) of the definitions and lemmas
that live in `Submission.Work.Drive.Mono.exists_discParam_of_two_convex_glued` and
`Submission.Work.Drive.Mono.halfDisc_map_of_segment`.  The latter module does not compile
(heartbeat timeout), so its definitions are duplicated here.  This module is complete.
-/

namespace Work.Drive.Mono

open Set
open scoped Pointwise

noncomputable section

/-! ## The half-discs of the unit disc of `ℂ` -/

/-- The closed upper half-disc of the unit disc of `ℂ`. -/
def upperHalfDisc : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.im}

/-- The closed lower half-disc of the unit disc of `ℂ`. -/
def lowerHalfDisc : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 ∧ z.im ≤ 0}

@[simp] lemma mem_upperHalfDisc {z : ℂ} : z ∈ upperHalfDisc ↔ ‖z‖ ≤ 1 ∧ 0 ≤ z.im := Iff.rfl

@[simp] lemma mem_lowerHalfDisc {z : ℂ} : z ∈ lowerHalfDisc ↔ ‖z‖ ≤ 1 ∧ z.im ≤ 0 := Iff.rfl

lemma upperHalfDisc_subset_closedBall : upperHalfDisc ⊆ Metric.closedBall (0 : ℂ) 1 :=
  fun _ hz => by rw [Metric.mem_closedBall, dist_zero_right]; exact hz.1

lemma lowerHalfDisc_subset_closedBall : lowerHalfDisc ⊆ Metric.closedBall (0 : ℂ) 1 :=
  fun _ hz => by rw [Metric.mem_closedBall, dist_zero_right]; exact hz.1

lemma isClosed_upperHalfDisc : IsClosed upperHalfDisc := by
  have h : upperHalfDisc = Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im} := by
    ext z; simp [upperHalfDisc, Metric.mem_closedBall, dist_zero_right]
  rw [h]
  exact Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

lemma isClosed_lowerHalfDisc : IsClosed lowerHalfDisc := by
  have h : lowerHalfDisc = Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im ≤ 0} := by
    ext z; simp [lowerHalfDisc, Metric.mem_closedBall, dist_zero_right]
  rw [h]
  exact Metric.isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const)

/-! ## Coning a homeomorphism of the circle to a map of the disc -/

lemma inv_smul_mem_sphere {z : ℂ} (hz : z ≠ 0) : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

/-- The "coning" of a homeomorphism `g` of the unit circle: the norm is unchanged and the
direction of `z` is moved by `g`. -/
def coneDisc (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) : ℂ → ℂ := by
  classical
  exact fun z => if hz : z = 0 then 0 else
    ‖z‖ • ((g ⟨‖z‖⁻¹ • z, inv_smul_mem_sphere hz⟩ : Metric.sphere (0 : ℂ) 1) : ℂ)

lemma coneDisc_zero (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    coneDisc g 0 = 0 := by
  classical
  simp [coneDisc]

lemma coneDisc_apply_of_ne (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) {z : ℂ}
    (hz : z ≠ 0) :
    coneDisc g z
      = ‖z‖ • ((g ⟨‖z‖⁻¹ • z, inv_smul_mem_sphere hz⟩ : Metric.sphere (0 : ℂ) 1) : ℂ) := by
  classical
  simp only [coneDisc, dif_neg hz]

lemma norm_coneDisc (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) (z : ℂ) :
    ‖coneDisc g z‖ = ‖z‖ := by
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [coneDisc_zero, norm_zero]
  · rw [coneDisc_apply_of_ne g hz, norm_smul, Real.norm_of_nonneg (norm_nonneg z)]
    have h := (g ⟨‖z‖⁻¹ • z, inv_smul_mem_sphere hz⟩).2
    rw [Metric.mem_sphere, dist_zero_right] at h
    rw [h, mul_one]

lemma coneDisc_eq_of_mem_sphere (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    coneDisc g z = ((g ⟨z, hz⟩ : Metric.sphere (0 : ℂ) 1) : ℂ) := by
  classical
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [Metric.mem_sphere, dist_zero_right, norm_zero] at hz
    exact zero_ne_one hz
  have hn : ‖z‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hz
  have hsub : (⟨‖z‖⁻¹ • z, inv_smul_mem_sphere hz0⟩ : Metric.sphere (0 : ℂ) 1) = ⟨z, hz⟩ := by
    refine Subtype.ext ?_
    show ‖z‖⁻¹ • z = z
    rw [hn, inv_one, one_smul]
  rw [coneDisc_apply_of_ne g hz0, hsub, hn, one_smul]

lemma injOn_coneDisc (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Set.InjOn (coneDisc g) (Metric.closedBall (0 : ℂ) 1) := by
  classical
  intro z _ z' _ h
  have hn : ‖z‖ = ‖z'‖ := by rw [← norm_coneDisc g z, h, norm_coneDisc g z']
  rcases eq_or_ne z 0 with rfl | hz
  · rw [norm_zero] at hn
    exact (norm_eq_zero.mp hn.symm).symm
  · have hz' : z' ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hn
      exact hz (norm_eq_zero.mp hn)
    rw [coneDisc_apply_of_ne g hz, coneDisc_apply_of_ne g hz'] at h
    have hne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hne' : ‖z'‖ ≠ 0 := norm_ne_zero_iff.mpr hz'
    have hg : g ⟨‖z‖⁻¹ • z, inv_smul_mem_sphere hz⟩
        = g ⟨‖z'‖⁻¹ • z', inv_smul_mem_sphere hz'⟩ := by
      refine Subtype.ext ?_
      refine (smul_right_inj (M := ℂ) hne).mp ?_
      rw [h, hn]
    have hv : ‖z‖⁻¹ • z = ‖z'‖⁻¹ • z' := congrArg Subtype.val (g.injective hg)
    rw [show z = ‖z‖ • (‖z‖⁻¹ • z) from by rw [smul_smul, mul_inv_cancel₀ hne, one_smul], hv,
      hn, smul_smul, mul_inv_cancel₀ hne', one_smul]

lemma coneDisc_surjOn (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ∃ z ∈ Metric.closedBall (0 : ℂ) 1, coneDisc g z = w := by
  classical
  intro w hw
  have hwn : ‖w‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨0, by rw [Metric.mem_closedBall, dist_zero_right, norm_zero]; norm_num,
      coneDisc_zero g⟩
  · have hwne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    obtain ⟨u, hu⟩ := g.surjective ⟨‖w‖⁻¹ • w, inv_smul_mem_sphere hw0⟩
    have hu1 : ‖(u : ℂ)‖ = 1 := by
      have h := u.2
      rwa [Metric.mem_sphere, dist_zero_right] at h
    have hz0 : ‖w‖ • (u : ℂ) ≠ 0 := by
      intro hcon
      rcases smul_eq_zero.mp hcon with h | h
      · exact hwne h
      · rw [h, norm_zero] at hu1
        exact zero_ne_one hu1
    refine ⟨‖w‖ • (u : ℂ), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (norm_nonneg w), hu1, mul_one]
      exact hwn
    · have hdir : ‖‖w‖ • (u : ℂ)‖⁻¹ • (‖w‖ • (u : ℂ)) = (u : ℂ) := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg w), hu1, mul_one, smul_smul,
          inv_mul_cancel₀ hwne, one_smul]
      have hsub : (⟨‖‖w‖ • (u : ℂ)‖⁻¹ • (‖w‖ • (u : ℂ)), inv_smul_mem_sphere hz0⟩
          : Metric.sphere (0 : ℂ) 1) = u := Subtype.ext hdir
      rw [coneDisc_apply_of_ne g hz0, hsub, norm_smul, Real.norm_of_nonneg (norm_nonneg w),
        hu1, mul_one, hu]
      rw [show ((⟨‖w‖⁻¹ • w, inv_smul_mem_sphere hw0⟩ : Metric.sphere (0 : ℂ) 1) : ℂ)
          = ‖w‖⁻¹ • w from rfl]
      rw [smul_smul, mul_inv_cancel₀ hwne, one_smul]

/-! ## Convexity and topology of the half-discs -/

lemma convex_upperHalfDisc : Convex ℝ upperHalfDisc := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by
          have h1 := hx.1
          have h2 := hy.1
          nlinarith
      _ = 1 := by rw [mul_one, mul_one, hab]
  · rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    have h1 := hx.2
    have h2 := hy.2
    nlinarith

lemma convex_lowerHalfDisc : Convex ℝ lowerHalfDisc := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by
          have h1 := hx.1
          have h2 := hy.1
          nlinarith
      _ = 1 := by rw [mul_one, mul_one, hab]
  · rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    have h1 := hx.2
    have h2 := hy.2
    nlinarith

lemma isBounded_upperHalfDisc : Bornology.IsBounded upperHalfDisc :=
  (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset upperHalfDisc_subset_closedBall

lemma isBounded_lowerHalfDisc : Bornology.IsBounded lowerHalfDisc :=
  (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset lowerHalfDisc_subset_closedBall

lemma I_div_two_mem_interior_upperHalfDisc : (Complex.I / 2) ∈ interior upperHalfDisc := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨1 / 4, by norm_num, fun w hw => ?_⟩
  have hw' : ‖w - Complex.I / 2‖ < 1 / 4 := by simpa [dist_eq_norm] using hw
  have hI : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_I, Complex.norm_ofNat]
  refine ⟨?_, ?_⟩
  · have h1 : ‖w‖ ≤ ‖w - Complex.I / 2‖ + ‖Complex.I / 2‖ := by
      calc ‖w‖ = ‖(w - Complex.I / 2) + Complex.I / 2‖ := by
            conv_lhs => rw [show w = (w - Complex.I / 2) + Complex.I / 2 from by ring]
        _ ≤ ‖w - Complex.I / 2‖ + ‖Complex.I / 2‖ := norm_add_le _ _
    linarith
  · have h1 : |(w - Complex.I / 2).im| ≤ ‖w - Complex.I / 2‖ := Complex.abs_im_le_norm _
    have h2 : (Complex.I / 2 : ℂ).im = 1 / 2 := by simp
    have h3 : w.im = (w - Complex.I / 2).im + (Complex.I / 2 : ℂ).im := by
      rw [Complex.sub_im]; ring
    have h4 : -(1 / 4) < (w - Complex.I / 2).im := (abs_lt.mp (lt_of_le_of_lt h1 hw')).1
    rw [h3, h2]
    linarith

/-! ## Continuity of the coning map -/

lemma continuousAt_coneDisc (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    ∀ z : ℂ, ContinuousAt (coneDisc g) z := by
  intro z
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero, coneDisc_zero]
    simp only [sub_zero]
    have hfun : (fun z : ℂ => ‖coneDisc g z‖) = fun z => ‖z‖ := funext (norm_coneDisc g)
    rw [hfun]
    simpa using continuous_norm.tendsto (0 : ℂ)
  · have hmap : Continuous (fun w : {w : ℂ // w ≠ 0} =>
        (⟨‖(w : ℂ)‖⁻¹ • (w : ℂ), inv_smul_mem_sphere w.2⟩ : Metric.sphere (0 : ℂ) 1)) :=
      Continuous.subtype_mk (((continuous_norm.comp continuous_subtype_val).inv₀
        (fun w => norm_ne_zero_iff.mpr w.2)).smul continuous_subtype_val)
        (fun w => inv_smul_mem_sphere w.2)
    have hcont : ContinuousOn (coneDisc g) {w : ℂ | w ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hfun : ({w : ℂ | w ≠ 0}.domRestrict (coneDisc g)) =
          fun w : {w : ℂ // w ≠ 0} =>
            ‖(w : ℂ)‖ • ((g ⟨‖(w : ℂ)‖⁻¹ • (w : ℂ), inv_smul_mem_sphere w.2⟩
              : Metric.sphere (0 : ℂ) 1) : ℂ) := by
        funext w
        exact coneDisc_apply_of_ne g w.2
      rw [hfun]
      exact (continuous_norm.comp continuous_subtype_val).smul
        (continuous_subtype_val.comp (g.continuous.comp hmap))
    exact hcont.continuousAt (isOpen_ne.mem_nhds hz)

lemma continuous_coneDisc (g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Continuous (coneDisc g) :=
  continuous_iff_continuousAt.mpr (continuousAt_coneDisc g)


/-! ## Gluing two half-disc maps along the diameter -/

lemma upperHalfDisc_union_lowerHalfDisc :
    upperHalfDisc ∪ lowerHalfDisc = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact upperHalfDisc_subset_closedBall hz
    · exact lowerHalfDisc_subset_closedBall hz
  · intro hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rcases le_total 0 z.im with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩

/-- The map glued from a map of the closed upper half-disc and a map of the closed lower half-disc. -/
def glueFun (fA fB : ℂ → ℂ) : ℂ → ℂ := fun z => if 0 ≤ z.im then fA z else fB z

lemma glueFun_of_nonneg {fA fB : ℂ → ℂ} {z : ℂ} (hz : 0 ≤ z.im) : glueFun fA fB z = fA z := by
  rw [glueFun]; exact if_pos hz

lemma glueFun_of_neg {fA fB : ℂ → ℂ} {z : ℂ} (hz : z.im < 0) : glueFun fA fB z = fB z := by
  rw [glueFun]; exact if_neg (not_le.mpr hz)

/-- Glue a map of the closed upper half-disc and a map of the closed lower half-disc into a map of
the closed unit disc, when the two agree on the common diameter and the images meet exactly in the
image of the diameter. -/
theorem glued_disc_map {A B : Set ℂ} {fA fB : ℂ → ℂ}
    (hAcont : ContinuousOn fA upperHalfDisc) (hBcont : ContinuousOn fB lowerHalfDisc)
    (hAinj : Set.InjOn fA upperHalfDisc) (hBinj : Set.InjOn fB lowerHalfDisc)
    (hrangeA : fA '' upperHalfDisc = A) (hrangeB : fB '' lowerHalfDisc = B)
    (hagree : ∀ z ∈ upperHalfDisc ∩ lowerHalfDisc, fA z = fB z)
    (hglue : fA '' (upperHalfDisc ∩ lowerHalfDisc) = A ∩ B) :
    ∃ e : ℂ → ℂ, ContinuousOn e (Metric.closedBall (0 : ℂ) 1) ∧
      Set.InjOn e (Metric.closedBall (0 : ℂ) 1) ∧
      e '' Metric.closedBall (0 : ℂ) 1 = A ∪ B ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ z.im → e z = fA z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im ≤ 0 → e z = fB z) := by
  classical
  have heu : ∀ z ∈ upperHalfDisc, glueFun fA fB z = fA z := fun z hz => glueFun_of_nonneg hz.2
  have hel : ∀ z ∈ lowerHalfDisc, glueFun fA fB z = fB z := by
    intro z hz
    rcases lt_or_eq_of_le hz.2 with h | h
    · exact glueFun_of_neg h
    · rw [glueFun_of_nonneg (le_of_eq h.symm), hagree z ⟨⟨hz.1, le_of_eq h.symm⟩, hz⟩]
  have hglueB : fB '' (upperHalfDisc ∩ lowerHalfDisc) = A ∩ B := by
    rw [← Set.image_congr (fun z hz => hagree z hz), hglue]
  have hcover := upperHalfDisc_union_lowerHalfDisc
  have hcont : ContinuousOn (glueFun fA fB) (Metric.closedBall (0 : ℂ) 1) := by
    rw [← hcover]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_upperHalfDisc isClosed_lowerHalfDisc
    · exact hAcont.congr heu
    · exact hBcont.congr hel
  have hinj : Set.InjOn (glueFun fA fB) (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz z' hz' heq
    have hzD : z ∈ upperHalfDisc ∪ lowerHalfDisc := by rw [hcover]; exact hz
    have hz'D : z' ∈ upperHalfDisc ∪ lowerHalfDisc := by rw [hcover]; exact hz'
    rcases hzD with hzU | hzL
    · rcases hz'D with hz'U | hz'L
      · have hff : fA z = fA z' := (heu z hzU).symm.trans (heq.trans (heu z' hz'U))
        exact hAinj hzU hz'U hff
      · have hmemA : fA z ∈ A := by rw [← hrangeA]; exact ⟨z, hzU, rfl⟩
        have hmemB : fA z ∈ B := by
          rw [← hrangeB]
          exact ⟨z', hz'L, (hel z' hz'L).symm.trans (heq.symm.trans (heu z hzU))⟩
        have hmem : fA z ∈ fA '' (upperHalfDisc ∩ lowerHalfDisc) := by
          rw [hglue]; exact ⟨hmemA, hmemB⟩
        obtain ⟨w, hw, hwz⟩ := hmem
        have hzw : z = w := hAinj hzU hw.1 hwz.symm
        have hzL2 : z ∈ lowerHalfDisc := by rw [hzw]; exact hw.2
        have hff : fB z = fB z' := (hel z hzL2).symm.trans (heq.trans (hel z' hz'L))
        exact hBinj hzL2 hz'L hff
    · rcases hz'D with hz'U | hz'L
      · have hmemB : fB z ∈ B := by rw [← hrangeB]; exact ⟨z, hzL, rfl⟩
        have hmemA : fB z ∈ A := by
          rw [← hrangeA]
          exact ⟨z', hz'U, (heu z' hz'U).symm.trans (heq.symm.trans (hel z hzL))⟩
        have hmem : fB z ∈ fB '' (upperHalfDisc ∩ lowerHalfDisc) := by
          rw [hglueB]; exact ⟨hmemA, hmemB⟩
        obtain ⟨w, hw, hwz⟩ := hmem
        have hzw : z = w := hBinj hzL hw.2 hwz.symm
        have hzU2 : z ∈ upperHalfDisc := by rw [hzw]; exact hw.1
        have hff : fA z = fA z' := (heu z hzU2).symm.trans (heq.trans (heu z' hz'U))
        exact hAinj hzU2 hz'U hff
      · have hff : fB z = fB z' := (hel z hzL).symm.trans (heq.trans (hel z' hz'L))
        exact hBinj hzL hz'L hff
  refine ⟨glueFun fA fB, hcont, hinj, ?_, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzD : z ∈ upperHalfDisc ∪ lowerHalfDisc := by rw [hcover]; exact hz
      rcases hzD with hzU | hzL
      · exact Or.inl (by rw [← hrangeA]; exact ⟨z, hzU, (heu z hzU).symm⟩)
      · exact Or.inr (by rw [← hrangeB]; exact ⟨z, hzL, (hel z hzL).symm⟩)
    · rintro (hw | hw)
      · obtain ⟨z, hzU, hz⟩ := (show w ∈ fA '' upperHalfDisc from by rw [hrangeA]; exact hw)
        exact ⟨z, upperHalfDisc_subset_closedBall hzU, by rw [heu z hzU, hz]⟩
      · obtain ⟨z, hzL, hz⟩ := (show w ∈ fB '' lowerHalfDisc from by rw [hrangeB]; exact hw)
        exact ⟨z, lowerHalfDisc_subset_closedBall hzL, by rw [hel z hzL, hz]⟩
  · intro z hz hle
    exact heu z ⟨by rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz, hle⟩
  · intro z hz hle
    exact hel z ⟨by rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz, hle⟩


end

/-! ## Two elementary facts about the closed upper half-disc -/

/-- The real diameter of the closed upper half-disc does not meet its interior. -/
lemma ofReal_notMem_interior_upperHalfDisc (t : ℝ) :
    (t : ℂ) ∉ interior upperHalfDisc := by
  intro h
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  have hmem : (t : ℂ) - ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ upperHalfDisc := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (t : ℂ) - ((ε / 2 : ℝ) : ℂ) * Complex.I - (t : ℂ)
        = -(((ε / 2 : ℝ) : ℂ) * Complex.I) := by ring
    rw [hsub, norm_neg, Complex.norm_def, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_I, mul_one, ← sq, Real.sqrt_sq (by positivity)]
    linarith
  have him : ((t : ℂ) - ((ε / 2 : ℝ) : ℂ) * Complex.I).im = -(ε / 2) := by
    simp [Complex.sub_im, Complex.mul_im]
  have h2 := hmem.2
  rw [him] at h2
  linarith

/-- Every point of the real diameter `[-1,1]` lies in the frontier of the closed upper half-disc. -/
lemma ofReal_mem_frontier_upperHalfDisc {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (t : ℂ) ∈ frontier upperHalfDisc := by
  rw [← closure_sdiff_interior, Set.mem_sdiff]
  refine ⟨subset_closure ?_, ofReal_notMem_interior_upperHalfDisc t⟩
  rw [mem_upperHalfDisc]
  refine ⟨?_, by simp⟩
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
  exact abs_le.mpr ⟨ht.1, ht.2⟩

end Work.Drive.Mono
