import Mathlib
import Submission.Work.Drive.PolarTwist.radialGraph_flat
import Submission.Work.OneDim.CirclePtFacts
import Submission.Work.OneDim.circle_gluing_prereq
import Submission.Work.OneDim.seam_chart_data
import Submission.Work.Drive.PolarTwist.spherePt_eq_exp

/-!
# The radial-graph isotopy, in manifold form

`Work.Drive.PolarTwist.radialGraph_isotopy`: for a smooth positive function `rad` on the circle
there is a jointly smooth family `gc` of maps `Circle → ℝ × ℝ` which starts at the radial graph
`x ↦ (rad x · re x, rad x · im x)`, ends at the ellipse `z ↦ (2 re z, im z)` and is a smooth
embedding at every parameter `s ∈ [0,1]`.

## The construction

The family is the one of `Submission/Work/Drive/PolarTwist/radialGraph_flat.lean`:
`gc s x = (1+s) · ρ_s x · (re x, im x)` with `ρ_s = (1-s)·rad + s`.

The content of the file is the proof that every slice is a *smooth embedding* (in the sense of
`Manifold.IsSmoothEmbedding`), which is the manifold-theoretic statement needed by the
`isotopy_to_ellipse` route.  The two ingredients of `IsSmoothEmbedding` are treated separately.

* The slice is injective (`radialGraphFamily_injective`, from the flat file) and continuous, hence a
  topological embedding: `Continuous.isClosedEmbedding` for a continuous injective map from the
  compact circle into the Hausdorff plane.  Continuity of `rad` itself is deduced from the
  hypothesis that `t ↦ rad (Circle.exp t)` is smooth, because `Circle.exp` is a covering map and
  hence a quotient map (`continuous_of_contDiff_exp`).

* For the immersion, the file constructs, at an arbitrary base point `x₀ ∈ Circle`, an explicit
  pair of charts straightening the slice near `x₀`:

  * on the circle, the *rotated stereographic chart* `arcChart d c` (`d = -x₀`, `c = d⁻¹`), whose
    parametrisation is `v ↦ pcircle d hd v = d · spherePt' v`; it is centred at `x₀` and its source
    is the small arc `|sphereCoord' (z·c)| < 1`;
  * on the plane, the chart `straightenChart` which maps the parametrised curve to a straight
    segment.  In its coordinates the curve point `r · p` (radius `r`, unit direction `p`) is sent to
    `(0, α)` where `α` is the stereographic coordinate of the *direction* of `r · p`, whence the
    curve is straightened because the radius function along the parametrisation is identified with
    an explicit smooth function `Hfun` via the Weierstrass substitution
    `spherePt' v = Circle.exp (π - 2 arctan v)` (`spherePt_eq_exp`, proved in the sibling file
    `spherePt_eq_exp.lean`).

The two charts satisfy the normal form required by
`Manifold.IsImmersionAtOfComplement.mk_of_charts`, which yields `IsImmersion`; the chart
`straightenChart` is also reused by the isotopy stages built on top of this lemma.
-/


set_option autoImplicit false

namespace Work.Drive.PolarTwist

open scoped Manifold ContDiff Topology
open Set

noncomputable section
/-- The complex number attached to a plane point. -/
def ofPair (q : ℝ × ℝ) : ℂ := Complex.equivRealProdCLM.symm q

/-- The plane point attached to a complex number. -/
def toPair (z : ℂ) : ℝ × ℝ := Complex.equivRealProdCLM z

@[simp] lemma toPair_ofPair (q : ℝ × ℝ) : toPair (ofPair q) = q := by
  simp only [toPair, ofPair]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

@[simp] lemma ofPair_toPair (z : ℂ) : ofPair (toPair z) = z := by
  simp only [toPair, ofPair]
  exact ContinuousLinearEquiv.symm_apply_apply _ _

@[simp] lemma ofPair_zero : ofPair (0 : ℝ × ℝ) = 0 := by simp [ofPair]

lemma ofPair_add (q r : ℝ × ℝ) : ofPair (q + r) = ofPair q + ofPair r := by
  simp [ofPair]

lemma ofPair_smul (t : ℝ) (q : ℝ × ℝ) : ofPair (t • q) = t • ofPair q := by
  simp [ofPair]

lemma ofPair_neg (q : ℝ × ℝ) : ofPair (-q) = -ofPair q := by
  simp [ofPair]

lemma ofPair_sub (q r : ℝ × ℝ) : ofPair (q - r) = ofPair q - ofPair r := by
  simp [ofPair]

/-- Euclidean radius of a plane point. -/
def rfun (q : ℝ × ℝ) : ℝ := ‖ofPair q‖

/-- The unit direction of a plane point (junk at the origin, where the radius vanishes). -/
def dirn (q : ℝ × ℝ) : ℂ := (rfun q)⁻¹ • ofPair q

lemma rfun_nonneg (q : ℝ × ℝ) : 0 ≤ rfun q := norm_nonneg _

lemma rfun_eq_zero_iff (q : ℝ × ℝ) : rfun q = 0 ↔ ofPair q = 0 := by
  rw [rfun, norm_eq_zero]

lemma rfun_pos_iff (q : ℝ × ℝ) : 0 < rfun q ↔ ofPair q ≠ 0 := by
  rw [rfun, norm_pos_iff]

lemma rfun_ne_zero (q : ℝ × ℝ) (h : ofPair q ≠ 0) : rfun q ≠ 0 := by
  rwa [ne_eq, rfun_eq_zero_iff]

lemma norm_dirn (q : ℝ × ℝ) (h : ofPair q ≠ 0) : ‖dirn q‖ = 1 := by
  have hq : 0 < rfun q := by rwa [rfun_pos_iff]
  rw [dirn, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  show (rfun q)⁻¹ * rfun q = 1
  exact inv_mul_cancel₀ (ne_of_gt hq)

lemma rfun_smul_dirn (q : ℝ × ℝ) (h : ofPair q ≠ 0) : rfun q • dirn q = ofPair q := by
  have hq : rfun q ≠ 0 := rfun_ne_zero q h
  rw [dirn, smul_smul, mul_inv_cancel₀ hq, one_smul]

lemma dirn_eq_self {z : ℂ} (hz : ‖z‖ = 1) : dirn (toPair z) = z := by
  rw [dirn, rfun, ofPair_toPair, hz, inv_one, one_smul]

lemma dirn_smul {t : ℝ} (ht : 0 < t) (q : ℝ × ℝ) : dirn (t • q) = dirn q := by
  rcases eq_or_ne (ofPair q) 0 with h | h
  · have h1 : ofPair (t • q) = 0 := by rw [ofPair_smul, h, smul_zero]
    simp [dirn, rfun, h1, h]
  · have h1 : ofPair (t • q) ≠ 0 := by rw [ofPair_smul]; exact smul_ne_zero (ne_of_gt ht) h
    have hr : rfun (t • q) = t * rfun q := by
      rw [rfun, rfun, ofPair_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [dirn, dirn, hr, ofPair_smul, smul_smul]
    congr 1
    have hq : rfun q ≠ 0 := rfun_ne_zero q h
    field_simp

/-- The parametrisation `v ↦ d · spherePt' v` of the circle, as a plane point. -/
def pvec (d : ℂ) (v : ℝ) : ℝ × ℝ := toPair (d * (Work.OneDim.spherePt' v : ℂ))

/-- The circle point `d · spherePt' v`. -/
def pcircle (d : ℂ) (hd : ‖d‖ = 1) (v : ℝ) : Circle :=
  ⟨d * (Work.OneDim.spherePt' v : ℂ),
    by simpa [Submonoid.unitSphere, norm_mul, hd] using (Work.OneDim.spherePt' v).2⟩

@[simp] lemma ofPair_pvec (d : ℂ) (v : ℝ) :
    ofPair (pvec d v) = d * (Work.OneDim.spherePt' v : ℂ) := by
  simp [pvec]

@[simp] lemma pcircle_coe (d : ℂ) (hd : ‖d‖ = 1) (v : ℝ) :
    ((pcircle d hd v : Circle) : ℂ) = ofPair (pvec d v) := by
  simp [pcircle, pvec]

lemma norm_ofPair_pvec {d : ℂ} (hd : ‖d‖ = 1) (v : ℝ) : ‖ofPair (pvec d v)‖ = 1 := by
  rw [ofPair_pvec, norm_mul, hd, one_mul]
  simpa [Submonoid.unitSphere] using (Work.OneDim.spherePt' v).2

lemma dirn_smul_pvec {d : ℂ} (hd : ‖d‖ = 1) {v t : ℝ} (ht : 0 < t) :
    dirn (t • pvec d v) = d * (Work.OneDim.spherePt' v : ℂ) := by
  rw [dirn_smul ht]
  exact dirn_eq_self (norm_ofPair_pvec hd v)

lemma rfun_smul_pvec {d : ℂ} (hd : ‖d‖ = 1) {v t : ℝ} (ht : 0 < t) :
    rfun (t • pvec d v) = t := by
  rw [rfun, ofPair_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, norm_ofPair_pvec hd, mul_one]

/-- The stereographic coordinate of the direction of a plane point, for the chart rotated by
`c = d⁻¹`. -/
def alphaPt (c : ℂ) (q : ℝ × ℝ) : ℝ := Work.OneDim.sphereCoord' (dirn q * c)

lemma alphaPt_smul_pvec {c d : ℂ} (hcd : c * d = 1) (hd : ‖d‖ = 1) {v t : ℝ} (ht : 0 < t) :
    alphaPt c (t • pvec d v) = v := by
  have h1 : d * (Work.OneDim.spherePt' v : ℂ) * c = (Work.OneDim.spherePt' v : ℂ) := by
    rw [mul_assoc, mul_comm (Work.OneDim.spherePt' v : ℂ) c, ← mul_assoc, mul_comm d c, hcd,
      one_mul]
  rw [alphaPt, dirn_smul_pvec hd ht, h1, Work.OneDim.sphereCoord'_spherePt']

/-- The diagonal scaling `(x, y) ↦ (x/σ, y/τ)`. -/
def Din (σ τ : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 / σ, q.2 / τ)

/-- The inverse diagonal scaling `(x, y) ↦ (σ x, τ y)`. -/
def Dout (σ τ : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (σ * q.1, τ * q.2)

@[simp] lemma Din_apply (σ τ : ℝ) (q : ℝ × ℝ) : Din σ τ q = (q.1 / σ, q.2 / τ) := rfl
@[simp] lemma Dout_apply (σ τ : ℝ) (q : ℝ × ℝ) : Dout σ τ q = (σ * q.1, τ * q.2) := rfl

lemma Din_Dout {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) (q : ℝ × ℝ) :
    Din σ τ (Dout σ τ q) = q := by
  ext <;> simp [hσ, hτ]

lemma Dout_Din {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) (q : ℝ × ℝ) :
    Dout σ τ (Din σ τ q) = q := by
  ext
  · show σ * (q.1 / σ) = q.1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hσ]
  · show τ * (q.2 / τ) = q.2
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hτ]




/-! ## The radius along the parameter -/

/-- The radius of the curve at parameter `v`, as a function of the smooth function `h` of the
angle. -/
def Hfun (h : ℝ → ℝ) (t : ℝ) (v : ℝ) : ℝ := h (t - 2 * Real.arctan v)

lemma contDiff_Hfun {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => Hfun h t v) := by
  refine hh.comp ?_
  exact contDiff_const.sub (contDiff_const.mul Real.contDiff_arctan)

lemma Hfun_pos {h : ℝ → ℝ} (hh : ∀ v, 0 < h v) (t v : ℝ) : 0 < Hfun h t v := hh _

/-! ## Continuity and smoothness of the auxiliary maps -/

lemma continuousAt_sphereCoord' {z : ℂ} (hz : z.re ≠ 1) :
    ContinuousAt Work.OneDim.sphereCoord' z := by
  show ContinuousAt (fun z : ℂ => z.im / (1 - z.re)) z
  refine ContinuousAt.div ?_ ?_ ?_
  · exact Complex.continuous_im.continuousAt
  · exact (continuous_const.sub Complex.continuous_re).continuousAt
  · simpa using sub_ne_zero.mpr (Ne.symm hz)

lemma contDiffOn_sphereCoord' :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im / (1 - z.re))
      {z : ℂ | 1 - z.re ≠ 0} := by
  refine ContDiffOn.div ?_ ?_ ?_
  · exact Complex.imCLM.contDiff.contDiffOn
  · exact (contDiff_const.sub Complex.reCLM.contDiff).contDiffOn
  · intro z hz; exact hz

lemma continuous_rfun : Continuous rfun := by
  show Continuous (fun q : ℝ × ℝ => ‖ofPair q‖)
  exact Complex.equivRealProdCLM.symm.continuous.norm

lemma contDiffOn_rfun : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rfun {q : ℝ × ℝ | ofPair q ≠ 0} := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => ‖ofPair q‖) {q : ℝ × ℝ | ofPair q ≠ 0}
  exact ContDiffOn.norm (𝕜 := ℝ) (f := fun q : ℝ × ℝ => ofPair q)
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun q hq => hq)

lemma continuousAt_dirn {q : ℝ × ℝ} (hq : ofPair q ≠ 0) : ContinuousAt dirn q := by
  show ContinuousAt (fun q : ℝ × ℝ => (rfun q)⁻¹ • ofPair q) q
  exact ((continuous_rfun.continuousAt).inv₀ (rfun_ne_zero q hq)).smul
    Complex.equivRealProdCLM.symm.continuous.continuousAt

lemma contDiffOn_dirn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dirn {q : ℝ × ℝ | ofPair q ≠ 0} := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (rfun q)⁻¹ • ofPair q) _
  have hsm : (fun q : ℝ × ℝ => (rfun q)⁻¹ • ofPair q)
      = fun q : ℝ × ℝ => ((rfun q)⁻¹ : ℂ) * ofPair q := by
    funext q
    rw [Algebra.smul_def, map_inv₀]
    simp
  rw [hsm]
  refine ContDiffOn.mul ?_ Complex.equivRealProdCLM.symm.contDiff.contDiffOn
  refine ContDiffOn.congr (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_rfun.inv (fun q hq => rfun_ne_zero q hq))) (fun q hq => ?_)
  simp

lemma continuousAt_alphaPt {c : ℂ} {x : ℝ × ℝ} (hq : ofPair x ≠ 0)
    (hc : (dirn x * c).re ≠ 1) : ContinuousAt (alphaPt c) x := by
  exact ContinuousAt.comp (g := Work.OneDim.sphereCoord')
    (f := fun q : ℝ × ℝ => dirn q * c) (x := x)
    (continuousAt_sphereCoord' hc) ((continuousAt_dirn hq).mul continuousAt_const)

lemma contDiffOn_alphaPt (c : ℂ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaPt c)
    {q : ℝ × ℝ | ofPair q ≠ 0 ∧ (dirn q * c).re ≠ 1} := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : ℝ × ℝ => Work.OneDim.sphereCoord' (dirn q * c)) _
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => dirn q * c)
      {q : ℝ × ℝ | ofPair q ≠ 0 ∧ (dirn q * c).re ≠ 1} :=
    (contDiffOn_dirn.mul contDiffOn_const).mono (fun q hq => hq.1)
  refine ContDiffOn.congr (contDiffOn_sphereCoord'.comp h1 ?_) (fun q hq => ?_)
  · intro q hq
    show 1 - (dirn q * c).re ≠ 0
    simpa using sub_ne_zero.mpr (Ne.symm hq.2)
  · exact rfl

lemma continuous_Din (σ τ : ℝ) : Continuous (Din σ τ) := by
  rw [show Din σ τ = fun q : ℝ × ℝ => (q.1 / σ, q.2 / τ) from rfl]
  fun_prop

lemma continuous_Dout (σ τ : ℝ) : Continuous (Dout σ τ) := by
  rw [show Dout σ τ = fun q : ℝ × ℝ => (σ * q.1, τ * q.2) from rfl]
  fun_prop

lemma contDiff_Din (σ τ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Din σ τ) := by
  rw [show Din σ τ = fun q : ℝ × ℝ => (q.1 / σ, q.2 / τ) from rfl]
  exact (contDiff_fst.div_const σ).prodMk (contDiff_snd.div_const τ)

lemma contDiff_Dout (σ τ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dout σ τ) := by
  rw [show Dout σ τ = fun q : ℝ × ℝ => (σ * q.1, τ * q.2) from rfl]
  exact (contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)

lemma toPair_smul (t : ℝ) (z : ℂ) : toPair (t • z) = t • toPair z := by
  simp [toPair]

lemma norm_spherePt'_coe (v : ℝ) : ‖((Work.OneDim.spherePt' v : Circle) : ℂ)‖ = 1 := by
  simpa [Submonoid.unitSphere] using (Work.OneDim.spherePt' v).2

lemma eq_one_of_re_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re = 1) : z = 1 := by
  have him : z.im = 0 := by
    have h := Complex.sq_norm z
    rw [hz, one_pow, Complex.normSq_apply] at h
    nlinarith [h]
  refine Complex.ext ?_ ?_
  · simpa using hre
  · simpa using him

lemma spherePt'_re_ne_one (v : ℝ) : ((Work.OneDim.spherePt' v : Circle) : ℂ).re ≠ 1 :=
  fun h => Work.OneDim.spherePt'_ne_Q v (Subtype.ext (eq_one_of_re_eq_one (norm_spherePt'_coe v) h))

lemma mul_spherePt'_mul (c d : ℂ) (hcd : c * d = 1) (v : ℝ) :
    d * (Work.OneDim.spherePt' v : ℂ) * c = (Work.OneDim.spherePt' v : ℂ) := by
  rw [mul_assoc, mul_comm (Work.OneDim.spherePt' v : ℂ) c, ← mul_assoc, mul_comm d c, hcd, one_mul]

lemma spherePt'_sphereCoord'_coe {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ((Work.OneDim.spherePt' (Work.OneDim.sphereCoord' z) : Circle) : ℂ) = z := by
  have hmem : z ∈ Submonoid.unitSphere ℂ := by simpa [Submonoid.unitSphere] using hz
  have h : (⟨z, hmem⟩ : Circle) ≠ Work.OneDim.Q := by
    intro hh
    exact hz1 (by simpa [Work.OneDim.Q_coe] using congrArg Subtype.val hh)
  have h2 := Work.OneDim.spherePt'_sphereCoord' (⟨z, hmem⟩ : Circle) h
  simpa using congrArg Subtype.val h2

/-- The key point: `w` is the positive multiple `rfun w` of the parametrisation point whose
parameter is the direction coordinate of `w`. -/
lemma smul_pvec_alphaPt {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1) {w : ℝ × ℝ}
    (hw : ofPair w ≠ 0) (hcr : (dirn w * c).re ≠ 1) :
    rfun w • pvec d (alphaPt c w) = w := by
  have hcd' : d * c = 1 := by rw [mul_comm]; exact hcd
  have hnormc : ‖c‖ = 1 := by
    have h := norm_mul c d
    rw [hcd, norm_one, hd, mul_one] at h
    exact h.symm
  have hζ1 : ‖dirn w * c‖ = 1 := by rw [norm_mul, norm_dirn w hw, hnormc, one_mul]
  have hζne : dirn w * c ≠ 1 := fun h => hcr (by rw [h]; simp)
  have hp : pvec d (alphaPt c w) = toPair (dirn w) := by
    rw [pvec, alphaPt, spherePt'_sphereCoord'_coe hζ1 hζne]
    congr 1
    rw [mul_comm (dirn w) c, ← mul_assoc, hcd', one_mul]
  rw [hp, ← toPair_smul, rfun_smul_dirn w hw, toPair_ofPair]

/-! ## The straightening chart -/

lemma finrank_real_complex_fact'' : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'

lemma contDiff_spherePt'_coe : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun v : ℝ => ((Work.OneDim.spherePt' v : Circle) : ℂ)) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact''
  have h1 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => ((Work.OneDim.spherePt' v : Circle) : ℂ)) :=
    contMDiff_coe_sphere.comp Work.OneDim.contMDiff_spherePt'
  exact contMDiff_iff_contDiff.mp h1

lemma contDiff_pvec (d : ℂ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => pvec d v) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => d * (Work.OneDim.spherePt' v : ℂ)) :=
    contDiff_const.mul contDiff_spherePt'_coe
  rw [show (fun v : ℝ => pvec d v)
      = fun v : ℝ => toPair (d * (Work.OneDim.spherePt' v : ℂ)) from rfl]
  exact Complex.equivRealProdCLM.contDiff.comp h

lemma isOpen_straighten_source (c d : ℂ) (σ τ : ℝ) :
    IsOpen ({q : ℝ × ℝ | 0 < rfun (Din σ τ q)} ∩ {q : ℝ × ℝ | (dirn (Din σ τ q) * c).re ≠ 1} ∩
      {q : ℝ × ℝ | alphaPt c (Din σ τ q) ∈ Ioo (-1) 1}) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  obtain ⟨⟨h1, h2⟩, h3⟩ := hq
  have h1' : 0 < rfun (Din σ τ q) := h1
  have h2' : (dirn (Din σ τ q) * c).re ≠ 1 := h2
  have h3' : alphaPt c (Din σ τ q) ∈ Ioo (-1) 1 := h3
  have hD : ContinuousAt (fun q : ℝ × ℝ => Din σ τ q) q := (continuous_Din σ τ).continuousAt
  have hwin1 : {q : ℝ × ℝ | 0 < rfun (Din σ τ q)} ∈ 𝓝 q :=
    ((continuous_rfun.comp (continuous_Din σ τ)).continuousAt).preimage_mem_nhds
      (isOpen_Ioi.mem_nhds h1')
  have hwin2 : {q : ℝ × ℝ | (dirn (Din σ τ q) * c).re ≠ 1} ∈ 𝓝 q := by
    have hdir : ContinuousAt (fun q : ℝ × ℝ => dirn (Din σ τ q)) q :=
      ContinuousAt.comp (g := dirn) (f := Din σ τ) (x := q)
        (continuousAt_dirn ((rfun_pos_iff _).mp h1')) hD
    have hmul : ContinuousAt (fun q : ℝ × ℝ => dirn (Din σ τ q) * c) q :=
      ContinuousAt.comp (g := fun z : ℂ => z * c)
        (f := fun q : ℝ × ℝ => dirn (Din σ τ q)) (x := q)
        (continuous_id.continuousAt.mul continuousAt_const) hdir
    have hc : ContinuousAt (fun q : ℝ × ℝ => (dirn (Din σ τ q) * c).re) q :=
      ContinuousAt.comp (g := fun z : ℂ => z.re)
        (f := fun q : ℝ × ℝ => dirn (Din σ τ q) * c) (x := q)
        Complex.continuous_re.continuousAt hmul
    exact hc.preimage_mem_nhds (isOpen_ne.mem_nhds h2')
  have hwin3 : {q : ℝ × ℝ | alphaPt c (Din σ τ q) ∈ Ioo (-1) 1} ∈ 𝓝 q :=
    (ContinuousAt.comp (g := alphaPt c)
      (continuousAt_alphaPt ((rfun_pos_iff _).mp h1') h2') hD).preimage_mem_nhds
      (isOpen_Ioo.mem_nhds h3')
  exact Filter.inter_mem (Filter.inter_mem hwin1 hwin2) hwin3

lemma isOpen_straighten_target (H : ℝ → ℝ) (hH : Continuous H) :
    IsOpen ({p : ℝ × ℝ | p.2 ∈ Ioo (-1) 1} ∩ {p : ℝ × ℝ | 0 < p.1 + H p.2}) :=
  (isOpen_Ioo.preimage continuous_snd).inter
    (isOpen_Ioi.preimage (continuous_fst.add (hH.comp continuous_snd)))

lemma contDiffOn_straighten_toFun {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1)
    {H : ℝ → ℝ} (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (σ τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (rfun (Din σ τ q) - H (alphaPt c (Din σ τ q)),
        alphaPt c (Din σ τ q)))
      ({q : ℝ × ℝ | 0 < rfun (Din σ τ q)} ∩ {q : ℝ × ℝ | (dirn (Din σ τ q) * c).re ≠ 1} ∩
        {q : ℝ × ℝ | alphaPt c (Din σ τ q) ∈ Ioo (-1) 1}) := by
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < rfun (Din σ τ q)} ∩
    {q : ℝ × ℝ | (dirn (Din σ τ q) * c).re ≠ 1} ∩
    {q : ℝ × ℝ | alphaPt c (Din σ τ q) ∈ Ioo (-1) 1} with hS
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Din σ τ) := contDiff_Din σ τ
  have hmaps : MapsTo (Din σ τ) S {q : ℝ × ℝ | ofPair q ≠ 0 ∧ (dirn q * c).re ≠ 1} := by
    intro q hq
    have h1 : 0 < rfun (Din σ τ q) := hq.1.1
    have h2 : (dirn (Din σ τ q) * c).re ≠ 1 := hq.1.2
    exact ⟨(rfun_pos_iff _).mp h1, h2⟩
  have hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => alphaPt c (Din σ τ q)) S :=
    (contDiffOn_alphaPt c).comp hD.contDiffOn hmaps
  have hr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => rfun (Din σ τ q)) S :=
    contDiffOn_rfun.comp hD.contDiffOn (fun q hq => (rfun_pos_iff _).mp hq.1.1)
  refine ContDiffOn.prodMk ?_ hα
  exact hr.sub (hH.contDiffOn.comp (t := Set.univ) hα (fun q hq => trivial))

lemma contDiffOn_straighten_invFun {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1)
    {H : ℝ → ℝ} (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (σ τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Dout σ τ ((p.1 + H p.2) • pvec d p.2))
      ({p : ℝ × ℝ | p.2 ∈ Ioo (-1) 1} ∩ {p : ℝ × ℝ | 0 < p.1 + H p.2}) := by
  have hpv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => pvec d p.2) :=
    (contDiff_pvec d).comp contDiff_snd
  have hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => p.1 + H p.2) :=
    contDiff_fst.add (hH.comp contDiff_snd)
  have hinner_eq : (fun p : ℝ × ℝ => (p.1 + H p.2) • pvec d p.2)
      = fun p : ℝ × ℝ => ((p.1 + H p.2) * (pvec d p.2).1, (p.1 + H p.2) * (pvec d p.2).2) := by
    funext p
    rfl
  have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (p.1 + H p.2) • pvec d p.2) := by
    rw [hinner_eq]
    exact (hfst.mul (contDiff_fst.comp hpv)).prodMk (hfst.mul (contDiff_snd.comp hpv))
  exact (contDiff_Dout σ τ).contDiffOn.comp (t := Set.univ) hinner.contDiffOn (fun p hp => trivial)

/-- The straightening chart of the plane near the parametrised curve
`v ↦ (σ · H v · a v, τ · H v · b v)`: in its coordinates the curve becomes the segment
`v ↦ (0, v)`. -/
def straightenChart (c d : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) (H : ℝ → ℝ)
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (σ τ : ℝ)
    (hσ : σ ≠ 0) (hτ : τ ≠ 0) : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := fun q => (rfun (Din σ τ q) - H (alphaPt c (Din σ τ q)), alphaPt c (Din σ τ q))
  invFun := fun p => Dout σ τ ((p.1 + H p.2) • pvec d p.2)
  source := {q : ℝ × ℝ | 0 < rfun (Din σ τ q)} ∩ {q : ℝ × ℝ | (dirn (Din σ τ q) * c).re ≠ 1} ∩
    {q : ℝ × ℝ | alphaPt c (Din σ τ q) ∈ Ioo (-1) 1}
  target := {p : ℝ × ℝ | p.2 ∈ Ioo (-1) 1} ∩ {p : ℝ × ℝ | 0 < p.1 + H p.2}
  map_source' := by
    rintro q ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, by simpa [sub_add_cancel] using h1⟩
  map_target' := by
    rintro p ⟨h1, h2⟩
    have hD : Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2)) = (p.1 + H p.2) • pvec d p.2 :=
      Din_Dout hσ hτ _
    have hD' : Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2)) = (p.1 + H p.2) • pvec d p.2 := hD
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show 0 < rfun (Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2)))
      rw [hD, rfun_smul_pvec (d := d) hd h2]
      exact h2
    · show (dirn (Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2))) * c).re ≠ 1
      rw [hD, dirn_smul_pvec (d := d) hd h2, mul_spherePt'_mul c d hcd p.2]
      exact spherePt'_re_ne_one p.2
    · show alphaPt c (Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2))) ∈ Ioo (-1) 1
      rw [hD, alphaPt_smul_pvec hcd hd h2]
      exact h1
  left_inv' := by
    rintro q ⟨⟨h1, h2⟩, h3⟩
    have h1' : 0 < rfun (Din σ τ q) := h1
    have h2' : (dirn (Din σ τ q) * c).re ≠ 1 := h2
    show Dout σ τ (((rfun (Din σ τ q) - H (alphaPt c (Din σ τ q))) +
      H (alphaPt c (Din σ τ q))) • pvec d (alphaPt c (Din σ τ q))) = q
    rw [sub_add_cancel,
      smul_pvec_alphaPt (d := d) hd hcd ((rfun_pos_iff _).mp h1') h2',
      Dout_Din hσ hτ q]
  right_inv' := by
    rintro p ⟨h1, h2⟩
    have hD : Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2)) = (p.1 + H p.2) • pvec d p.2 :=
      Din_Dout hσ hτ _
    show (rfun (Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2))) -
        H (alphaPt c (Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2)))),
      alphaPt c (Din σ τ (Dout σ τ ((p.1 + H p.2) • pvec d p.2)))) = p
    rw [hD, rfun_smul_pvec hd h2, alphaPt_smul_pvec hcd hd h2]
    exact Prod.ext (by ring) rfl
  open_source := isOpen_straighten_source c d σ τ
  open_target := isOpen_straighten_target H hH.continuous
  continuousOn_toFun := by
    show ContinuousOn (fun q : ℝ × ℝ => (rfun (Din σ τ q) - H (alphaPt c (Din σ τ q)),
      alphaPt c (Din σ τ q))) _
    exact (contDiffOn_straighten_toFun hd hcd hH σ τ).continuousOn
  continuousOn_invFun := by
    show ContinuousOn (fun p : ℝ × ℝ => Dout σ τ ((p.1 + H p.2) • pvec d p.2)) _
    exact (contDiffOn_straighten_invFun hd hcd hH σ τ).continuousOn

/-! ## Smoothness, openness and the atlas membership of the straightening chart -/

lemma source_straighten (c d : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) (H : ℝ → ℝ)
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (σ τ : ℝ) (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    (straightenChart c d hd hcd H hH σ τ hσ hτ).source =
      {q : ℝ × ℝ | 0 < rfun (Din σ τ q)} ∩ {q : ℝ × ℝ | (dirn (Din σ τ q) * c).re ≠ 1} ∩
        {q : ℝ × ℝ | alphaPt c (Din σ τ q) ∈ Ioo (-1) 1} := rfl

lemma target_straighten (c d : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) (H : ℝ → ℝ)
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (σ τ : ℝ) (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    (straightenChart c d hd hcd H hH σ τ hσ hτ).target =
      {p : ℝ × ℝ | p.2 ∈ Ioo (-1) 1} ∩ {p : ℝ × ℝ | 0 < p.1 + H p.2} := rfl

lemma straightenChart_mem_maximalAtlas {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1)
    {H : ℝ → ℝ} (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (σ τ : ℝ) (hσ : σ ≠ 0)
    (hτ : τ ≠ 0) :
    straightenChart c d hd hcd H hH σ τ hσ hτ ∈
      IsManifold.maximalAtlas (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (ℝ × ℝ) := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · show ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (rfun (Din σ τ q) - H (alphaPt c (Din σ τ q)),
        alphaPt c (Din σ τ q))) _
    exact ContDiffOn.contMDiffOn (contDiffOn_straighten_toFun hd hcd hH σ τ)
  · show ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Dout σ τ ((p.1 + H p.2) • pvec d p.2)) _
    exact ContDiffOn.contMDiffOn (contDiffOn_straighten_invFun hd hcd hH σ τ)

/-- The curve point at parameter `v` lies in the source of the straightening chart. -/
lemma curvePt_mem_source {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1) {h : ℝ → ℝ}
    (hh : ∀ v, 0 < h v) (hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (t : ℝ)
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) {v : ℝ} (hv : |v| < 1) :
    Dout σ τ (Hfun h t v • pvec d v) ∈
      (straightenChart c d hd hcd (Hfun h t) (contDiff_Hfun hhs t) σ τ hσ hτ).source := by
  have hpos : 0 < Hfun h t v := Hfun_pos hh t v
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 0 < rfun (Din σ τ (Dout σ τ (Hfun h t v • pvec d v)))
    rw [Din_Dout hσ hτ, rfun_smul_pvec (d := d) hd hpos]
    exact hpos
  · show (dirn (Din σ τ (Dout σ τ (Hfun h t v • pvec d v))) * c).re ≠ 1
    rw [Din_Dout hσ hτ, dirn_smul_pvec (d := d) hd hpos, mul_spherePt'_mul c d hcd v]
    exact spherePt'_re_ne_one v
  · show alphaPt c (Din σ τ (Dout σ τ (Hfun h t v • pvec d v))) ∈ Ioo (-1) 1
    rw [Din_Dout hσ hτ, alphaPt_smul_pvec hcd hd hpos]
    exact abs_lt.mp hv

/-- In the coordinates of the straightening chart, the parametrised curve is the segment
`v ↦ (0, v)`. -/
lemma straightenChart_curve {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1) {h : ℝ → ℝ}
    (hh : ∀ v, 0 < h v) (hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (t : ℝ)
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) {v : ℝ} (hv : |v| < 1) :
    straightenChart c d hd hcd (Hfun h t) (contDiff_Hfun hhs t) σ τ hσ hτ
      (Dout σ τ (Hfun h t v • pvec d v)) = (0, v) := by
  have hpos : 0 < Hfun h t v := Hfun_pos hh t v
  show (rfun (Din σ τ (Dout σ τ (Hfun h t v • pvec d v))) -
      Hfun h t (alphaPt c (Din σ τ (Dout σ τ (Hfun h t v • pvec d v)))),
      alphaPt c (Din σ τ (Dout σ τ (Hfun h t v • pvec d v)))) = (0, v)
  rw [Din_Dout hσ hτ, rfun_smul_pvec (d := d) hd hpos, alphaPt_smul_pvec hcd hd hpos]
  norm_num

/-! ## The rotated stereographic chart on the circle -/

lemma norm_circle_coe (z : Circle) : ‖(z : ℂ)‖ = 1 := by
  simpa [Submonoid.unitSphere] using z.2

lemma re_ne_one_of_ne_one {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) : z.re ≠ 1 :=
  fun h => hne (eq_one_of_re_eq_one hz h)

lemma pcircle_coe_eq (d : ℂ) (hd : ‖d‖ = 1) (v : ℝ) :
    ((pcircle d hd v : Circle) : ℂ) = d * (Work.OneDim.spherePt' v : ℂ) := by
  rw [pcircle_coe, ofPair_pvec]

lemma norm_of_mul_eq_one {c d : ℂ} (hd : ‖d‖ = 1) (hcd : c * d = 1) : ‖c‖ = 1 := by
  have h := norm_mul c d
  rw [hcd, norm_one, hd, mul_one] at h
  exact h.symm

lemma contMDiffOn_sphereCoord_rot (c : ℂ) :
    ContMDiffOn Work.OneDim.I1 (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Circle => Work.OneDim.sphereCoord' ((z : ℂ) * c))
      {z : Circle | ((z : ℂ) * c).re ≠ 1} := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact''
  have hcoe : ContMDiff Work.OneDim.I1 (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have hmul : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w * c) :=
    (contDiff_id.mul contDiff_const).contMDiff
  have h1 : ContMDiffOn Work.OneDim.I1 (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Circle => (z : ℂ) * c) {z : Circle | ((z : ℂ) * c).re ≠ 1} :=
    (hmul.comp hcoe).contMDiffOn
  have h2 : ContMDiffOn (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.im / (1 - ζ.re)) {ζ : ℂ | 1 - ζ.re ≠ 0} :=
    ContDiffOn.contMDiffOn contDiffOn_sphereCoord'
  refine (h2.comp h1 ?_).congr (fun z hz => ?_)
  · intro z hz
    show 1 - ((z : ℂ) * c).re ≠ 0
    simpa using sub_ne_zero.mpr (Ne.symm hz)
  · rfl

lemma contMDiff_pcircle (d : ℂ) (hd : ‖d‖ = 1) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => pcircle d hd v) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact''
  have hcoe : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => d * (Work.OneDim.spherePt' v : ℂ)) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_const.mul (contMDiff_iff_contDiff.mp
      (contMDiff_coe_sphere.comp Work.OneDim.contMDiff_spherePt'))
  have hmem : ∀ v : ℝ, d * (Work.OneDim.spherePt' v : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    intro v
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_mul, hd, one_mul]
    simpa [Submonoid.unitSphere] using (Work.OneDim.spherePt' v).2
  refine (hcoe.codRestrict_sphere hmem).congr (fun v => ?_)
  exact Subtype.ext rfl

lemma contMDiffOn_arcChart_toFun (d c : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) :
    ContMDiffOn Work.OneDim.I1 Work.OneDim.I1 ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Circle => Work.OneDim.stdLEsd (Work.OneDim.sphereCoord' ((z : ℂ) * c)))
      ({z : Circle | (z : ℂ) * c ≠ 1} ∩
        {z : Circle | |Work.OneDim.sphereCoord' ((z : ℂ) * c)| < 1}) := by
  have hstd : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ Work.OneDim.E1)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => Work.OneDim.stdLEsd v) Set.univ :=
    ((Work.OneDim.stdLEsd).contDiff.contMDiff).contMDiffOn
  have h3 : ContMDiffOn Work.OneDim.I1 (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Circle => Work.OneDim.sphereCoord' ((z : ℂ) * c))
      ({z : Circle | (z : ℂ) * c ≠ 1} ∩
        {z : Circle | |Work.OneDim.sphereCoord' ((z : ℂ) * c)| < 1}) :=
    (contMDiffOn_sphereCoord_rot c).mono (fun z hz => by
      have hnorm : ‖(z : ℂ) * c‖ = 1 := by
        rw [norm_mul, norm_circle_coe z, norm_of_mul_eq_one hd hcd, one_mul]
      exact re_ne_one_of_ne_one hnorm hz.1)
  exact (hstd.comp (t := Set.univ) h3 (fun z hz => trivial)).congr (fun z hz => rfl)

lemma contMDiffOn_arcChart_invFun (d c : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) :
    ContMDiffOn Work.OneDim.I1 Work.OneDim.I1 ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Work.OneDim.E1 => pcircle d hd (Work.OneDim.stdLEsd.symm w))
      {w : Work.OneDim.E1 | Work.OneDim.stdLEsd.symm w ∈ Ioo (-1 : ℝ) 1} := by
  have hstd : ContMDiff Work.OneDim.I1 (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Work.OneDim.E1 => Work.OneDim.stdLEsd.symm w) :=
    ((Work.OneDim.stdLEsd).symm).contDiff.contMDiff
  exact ((contMDiff_pcircle d hd).comp hstd).contMDiffOn

/-- The rotated stereographic chart of the circle: it is centred at the parametrisation point
`v = 0`, and its parametrisation is `v ↦ pcircle d hd v = d · spherePt' v`. -/
def arcChart (d c : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) :
    OpenPartialHomeomorph Circle Work.OneDim.E1 where
  toFun := fun z => Work.OneDim.stdLEsd (Work.OneDim.sphereCoord' ((z : ℂ) * c))
  invFun := fun w => pcircle d hd (Work.OneDim.stdLEsd.symm w)
  source := {z : Circle | (z : ℂ) * c ≠ 1} ∩
    {z : Circle | |Work.OneDim.sphereCoord' ((z : ℂ) * c)| < 1}
  target := {w : Work.OneDim.E1 | Work.OneDim.stdLEsd.symm w ∈ Ioo (-1 : ℝ) 1}
  map_source' := by
    rintro z ⟨h1, h2⟩
    show Work.OneDim.stdLEsd.symm
      (Work.OneDim.stdLEsd (Work.OneDim.sphereCoord' ((z : ℂ) * c))) ∈ Ioo (-1 : ℝ) 1
    rw [Work.OneDim.stdLEsd.symm_apply_apply]
    exact abs_lt.mp h2
  map_target' := by
    rintro w hw
    have hw' : Work.OneDim.stdLEsd.symm w ∈ Ioo (-1 : ℝ) 1 := hw
    have hcoe : ((pcircle d hd (Work.OneDim.stdLEsd.symm w) : Circle) : ℂ) * c
        = (Work.OneDim.spherePt' (Work.OneDim.stdLEsd.symm w) : ℂ) := by
      rw [pcircle_coe_eq, mul_spherePt'_mul c d hcd]
    have hcoord : Work.OneDim.sphereCoord'
        (((pcircle d hd (Work.OneDim.stdLEsd.symm w) : Circle) : ℂ) * c)
        = Work.OneDim.stdLEsd.symm w := by
      rw [hcoe, Work.OneDim.sphereCoord'_spherePt']
    refine ⟨?_, ?_⟩
    · show ((pcircle d hd (Work.OneDim.stdLEsd.symm w) : Circle) : ℂ) * c ≠ 1
      rw [hcoe]
      intro h
      exact Work.OneDim.spherePt'_ne_Q _
        (Subtype.ext (by rw [h, Work.OneDim.Q_coe]))
    · show |Work.OneDim.sphereCoord'
        (((pcircle d hd (Work.OneDim.stdLEsd.symm w) : Circle) : ℂ) * c)| < 1
      rw [hcoord]
      exact abs_lt.mpr hw'
  left_inv' := by
    rintro z ⟨h1, h2⟩
    have h1' : (z : ℂ) * c ≠ 1 := h1
    have hnorm : ‖(z : ℂ) * c‖ = 1 := by
      rw [norm_mul, norm_circle_coe z, norm_of_mul_eq_one hd hcd, one_mul]
    show pcircle d hd (Work.OneDim.stdLEsd.symm
      (Work.OneDim.stdLEsd (Work.OneDim.sphereCoord' ((z : ℂ) * c)))) = z
    rw [Work.OneDim.stdLEsd.symm_apply_apply]
    refine Subtype.ext ?_
    show d * (Work.OneDim.spherePt' (Work.OneDim.sphereCoord' ((z : ℂ) * c)) : ℂ) = (z : ℂ)
    rw [spherePt'_sphereCoord'_coe hnorm h1']
    rw [mul_comm (z : ℂ) c, ← mul_assoc, mul_comm d c, hcd, one_mul]
  right_inv' := by
    rintro w hw
    have hcoe : ((pcircle d hd (Work.OneDim.stdLEsd.symm w) : Circle) : ℂ) * c
        = (Work.OneDim.spherePt' (Work.OneDim.stdLEsd.symm w) : ℂ) := by
      rw [pcircle_coe_eq, mul_spherePt'_mul c d hcd]
    show Work.OneDim.stdLEsd (Work.OneDim.sphereCoord'
      (((pcircle d hd (Work.OneDim.stdLEsd.symm w) : Circle) : ℂ) * c)) = w
    rw [hcoe, Work.OneDim.sphereCoord'_spherePt']
    exact Work.OneDim.stdLEsd.apply_symm_apply w
  open_source := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨h1, h2⟩
    have h1' : (z : ℂ) * c ≠ 1 := h1
    have hnorm : ‖(z : ℂ) * c‖ = 1 := by
      rw [norm_mul, norm_circle_coe z, norm_of_mul_eq_one hd hcd, one_mul]
    have hre : ((z : ℂ) * c).re ≠ 1 := re_ne_one_of_ne_one hnorm h1'
    have hcont : ContinuousAt (fun z : Circle => (z : ℂ) * c) z :=
      ContinuousAt.mul continuous_subtype_val.continuousAt continuousAt_const
    have hwin1 : {z : Circle | (z : ℂ) * c ≠ 1} ∈ 𝓝 z :=
      hcont.preimage_mem_nhds (isOpen_ne.mem_nhds h1')
    have hwin2 : {z : Circle | |Work.OneDim.sphereCoord' ((z : ℂ) * c)| < 1} ∈ 𝓝 z := by
      have hpre : (fun z : Circle => Work.OneDim.sphereCoord' ((z : ℂ) * c)) ⁻¹'
          Ioo (-1 : ℝ) 1 ∈ 𝓝 z :=
        (ContinuousAt.comp (g := Work.OneDim.sphereCoord')
          (f := fun z : Circle => (z : ℂ) * c) (x := z)
          (continuousAt_sphereCoord' hre) hcont).preimage_mem_nhds
          (isOpen_Ioo.mem_nhds (abs_lt.mp h2))
      exact Filter.mem_of_superset hpre (fun z hz => by
        show |Work.OneDim.sphereCoord' ((z : ℂ) * c)| < 1
        exact abs_lt.mpr (by simpa using hz))
    exact Filter.inter_mem hwin1 hwin2
  open_target := by
    exact (isOpen_Ioo.preimage
      (ContinuousLinearEquiv.continuous (Work.OneDim.stdLEsd.symm)))
  continuousOn_toFun := (contMDiffOn_arcChart_toFun d c hd hcd).continuousOn
  continuousOn_invFun := (contMDiffOn_arcChart_invFun d c hd hcd).continuousOn

@[simp] lemma arcChart_symm_apply (d c : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1)
    (w : Work.OneDim.E1) :
    (arcChart d c hd hcd).symm w = pcircle d hd (Work.OneDim.stdLEsd.symm w) := rfl

@[simp] lemma arcChart_apply (d c : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) (z : Circle) :
    arcChart d c hd hcd z = Work.OneDim.stdLEsd (Work.OneDim.sphereCoord' ((z : ℂ) * c)) := rfl

lemma arcChart_mem_maximalAtlas (d c : ℂ) (hd : ‖d‖ = 1) (hcd : c * d = 1) :
    arcChart d c hd hcd ∈ IsManifold.maximalAtlas Work.OneDim.I1 ((⊤ : ℕ∞) : WithTop ℕ∞) Circle :=
  OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
    (contMDiffOn_arcChart_toFun d c hd hcd) (contMDiffOn_arcChart_invFun d c hd hcd)

lemma extend_target_self (f : OpenPartialHomeomorph Circle Work.OneDim.E1) :
    (f.extend Work.OneDim.I1).target = f.target := by
  rw [OpenPartialHomeomorph.extend_target]
  simp

lemma extend_apply_self (f : OpenPartialHomeomorph Circle Work.OneDim.E1) (x : Circle) :
    (f.extend Work.OneDim.I1) x = f x := rfl

lemma extend_symm_self (f : OpenPartialHomeomorph Circle Work.OneDim.E1)
    (u : Work.OneDim.E1) : (f.extend Work.OneDim.I1).symm u = f.symm u := rfl

/-! ## The transfer of the radius to the parameter -/

lemma exp_pi_coe : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
  rw [circleExp_coe_eq, Real.cos_pi, Real.sin_pi]
  simp

lemma pcircle_zero {d : ℂ} (hd : ‖d‖ = 1) {x₀ : Circle} (hdv : d = -(x₀ : ℂ)) :
    pcircle d hd 0 = x₀ := by
  refine Subtype.ext ?_
  rw [pcircle_coe_eq, hdv, Work.OneDim.spherePt'_zero, Work.OneDim.Qm_coe]
  ring

/-- The radius of the curve at the parameter `v`, expressed through the angle. -/
lemma rad_pcircle {rad : Circle → ℝ} {d : ℂ} {hd : ‖d‖ = 1} {x₀ : Circle} {t₀ : ℝ}
    (ht₀ : Circle.exp t₀ = x₀) (hdv : d = -(x₀ : ℂ)) (v : ℝ) :
    rad (pcircle d hd v)
      = Hfun (fun t : ℝ => rad (Circle.exp t)) (t₀ + 2 * Real.pi) v := by
  have hd' : d = ((Circle.exp (t₀ + Real.pi) : Circle) : ℂ) := by
    rw [hdv]
    calc -(x₀ : ℂ) = -((Circle.exp t₀ : Circle) : ℂ) := by rw [ht₀]
      _ = ((Circle.exp t₀ : Circle) : ℂ) * (-1) := by ring
      _ = ((Circle.exp t₀ : Circle) : ℂ) * (((Circle.exp Real.pi : Circle)) : ℂ) := by
            rw [exp_pi_coe]
      _ = (((Circle.exp t₀ * Circle.exp Real.pi : Circle)) : ℂ) := by rw [Circle.coe_mul]
      _ = ((Circle.exp (t₀ + Real.pi) : Circle) : ℂ) := by rw [Circle.exp_add]
  have hcoe : ((pcircle d hd v : Circle) : ℂ)
      = ((Circle.exp (t₀ + 2 * Real.pi - 2 * Real.arctan v) : Circle) : ℂ) := by
    rw [pcircle_coe_eq d hd v, hd',
      show ((Work.OneDim.spherePt' v : Circle) : ℂ)
        = ((Circle.exp (Real.pi - 2 * Real.arctan v) : Circle) : ℂ) from
        congrArg Subtype.val (spherePt_eq_exp v)]
    have harg : (t₀ + Real.pi) + (Real.pi - 2 * Real.arctan v)
        = t₀ + 2 * Real.pi - 2 * Real.arctan v := by ring
    rw [← Circle.coe_mul, ← Circle.exp_add, harg]
  rw [show pcircle d hd v = Circle.exp (t₀ + 2 * Real.pi - 2 * Real.arctan v) from
    Subtype.ext hcoe]
  rfl

/-! ## Continuity of a function which is smooth along `Circle.exp` -/

lemma continuous_of_contDiff_exp {ρ : Circle → ℝ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ρ (Circle.exp t))) :
    Continuous ρ := by
  have hcont : Continuous (fun t : ℝ => ρ (Circle.exp t)) := h.continuous
  have hq : Topology.IsQuotientMap (⇑Circle.exp) :=
    (Circle.isCoveringMap_exp.isOpenMap).isQuotientMap Circle.exp.continuous Circle.exp_surjective
  exact (Topology.IsQuotientMap.continuous_iff hq).mpr hcont

@[simp] lemma smul_fst (t : ℝ) (q : ℝ × ℝ) : (t • q).1 = t * q.1 := rfl
@[simp] lemma smul_snd (t : ℝ) (q : ℝ × ℝ) : (t • q).2 = t * q.2 := rfl

@[simp] lemma ofPair_fst (q : ℝ × ℝ) : (ofPair q).re = q.1 := rfl
@[simp] lemma ofPair_snd (q : ℝ × ℝ) : (ofPair q).im = q.2 := rfl

lemma extend_self_plane (f : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (y : ℝ × ℝ) :
    (f.extend (modelWithCornersSelf ℝ (ℝ × ℝ))) y = f y := rfl

/-- The slice map at a parametrisation point is the curve point of the straightening chart. -/
lemma slice_eq_curve {ρ : Circle → ℝ} {d : ℂ} {hd : ‖d‖ = 1} {x₀ : Circle} {t₀ : ℝ}
    (ht₀ : Circle.exp t₀ = x₀) (hdv : d = -(x₀ : ℂ)) (σ τ v : ℝ) :
    (σ * (ρ (pcircle d hd v) * ((pcircle d hd v : Circle) : ℂ).re),
      τ * (ρ (pcircle d hd v) * ((pcircle d hd v : Circle) : ℂ).im))
      = Dout σ τ (Hfun (fun t : ℝ => ρ (Circle.exp t)) (t₀ + 2 * Real.pi) v • pvec d v) := by
  have h1 : ρ (pcircle d hd v) = Hfun (fun t : ℝ => ρ (Circle.exp t)) (t₀ + 2 * Real.pi) v :=
    rad_pcircle ht₀ hdv v
  have h2 : ((pcircle d hd v : Circle) : ℂ) = ofPair (pvec d v) := by
    rw [pcircle_coe_eq d hd v, ofPair_pvec]
  rw [h1, h2]
  refine Prod.ext ?_ ?_ <;>
    simp only [Dout_apply, smul_fst, smul_snd, ofPair_fst, ofPair_snd] <;> ring

lemma continuous_slice {ρ : Circle → ℝ} (hρc : Continuous ρ) (σ τ : ℝ) :
    Continuous (fun x : Circle => (σ * (ρ x * (x : ℂ).re), τ * (ρ x * (x : ℂ).im))) := by
  have hcoe : Continuous (fun x : Circle => (x : ℂ)) := continuous_subtype_val
  have hre : Continuous (fun x : Circle => (x : ℂ).re) := Complex.continuous_re.comp hcoe
  have him : Continuous (fun x : Circle => (x : ℂ).im) := Complex.continuous_im.comp hcoe
  exact (continuous_const.mul (hρc.mul hre)).prodMk (continuous_const.mul (hρc.mul him))

/-! ## The main estimate: every slice is a smooth embedding -/

theorem isSmoothEmbedding_slice {ρ : Circle → ℝ} (hρpos : ∀ x, 0 < ρ x)
    (hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ρ (Circle.exp t)))
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hinj : Function.Injective
      (fun x : Circle => (σ * (ρ x * (x : ℂ).re), τ * (ρ x * (x : ℂ).im)))) :
    Manifold.IsSmoothEmbedding Work.OneDim.I1 (modelWithCornersSelf ℝ (ℝ × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Circle => (σ * (ρ x * (x : ℂ).re), τ * (ρ x * (x : ℂ).im))) := by
  have hρc : Continuous ρ := continuous_of_contDiff_exp hρs
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hτ' : τ ≠ 0 := ne_of_gt hτ
  have hhpos : ∀ v : ℝ, 0 < (fun t : ℝ => ρ (Circle.exp t)) v := fun v => hρpos _
  refine ⟨⟨ℝ, inferInstance, inferInstance, ?_⟩, ?_⟩
  · show ∀ x : Circle, Manifold.IsImmersionAtOfComplement ℝ Work.OneDim.I1
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Circle => (σ * (ρ x * (x : ℂ).re), τ * (ρ x * (x : ℂ).im))) x
    intro x₀
    obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective x₀
    obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = -(x₀ : ℂ) := ⟨_, rfl⟩
    have hd : ‖d‖ = 1 := by rw [hd_def, norm_neg]; exact norm_circle_coe x₀
    have hd0 : d ≠ 0 := by
      intro hh; rw [hh, norm_zero] at hd; norm_num at hd
    obtain ⟨c, hc_def⟩ : ∃ c : ℂ, c = d⁻¹ := ⟨_, rfl⟩
    have hcd : c * d = 1 := by rw [hc_def]; exact inv_mul_cancel₀ hd0
    have hHc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Hfun (fun t : ℝ => ρ (Circle.exp t)) (t₀ + 2 * Real.pi)) :=
      contDiff_Hfun hρs (t₀ + 2 * Real.pi)
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      ((ContinuousLinearEquiv.prodCongr (Work.OneDim.stdLEsd.symm) (1 : ℝ ≃L[ℝ] ℝ)).trans
        (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ))
      (arcChart d c hd hcd)
      (straightenChart c d hd hcd (Hfun (fun t : ℝ => ρ (Circle.exp t)) (t₀ + 2 * Real.pi))
        hHc σ τ hσ' hτ')
      ?_ ?_ ?_ ?_ ?_ ?_
    · -- the base point is in the source of the domain chart
      have hxc : (x₀ : ℂ) * c = -1 := by
        rw [hc_def, hd_def]
        have hx0 : (x₀ : ℂ) ≠ 0 := by
          intro hh
          have h1 := norm_circle_coe x₀
          rw [hh, norm_zero] at h1
          norm_num at h1
        field_simp
      refine ⟨?_, ?_⟩
      · show (x₀ : ℂ) * c ≠ 1
        rw [hxc]
        norm_num
      · show |Work.OneDim.sphereCoord' ((x₀ : ℂ) * c)| < 1
        have : |Work.OneDim.sphereCoord' (-1 : ℂ)| < 1 := by
          norm_num [Work.OneDim.sphereCoord']
        simpa [hxc] using this
    · -- the base point is in the source of the straightening chart
      have hx0p : x₀ = pcircle d hd 0 := (pcircle_zero hd hd_def).symm
      rw [hx0p, slice_eq_curve ht₀ hd_def σ τ 0]
      exact curvePt_mem_source hd hcd hhpos hρs (t₀ + 2 * Real.pi) hσ' hτ' (by norm_num)
    · exact arcChart_mem_maximalAtlas d c hd hcd
    · exact straightenChart_mem_maximalAtlas hd hcd hHc σ τ hσ' hτ'
    · -- the source of the domain chart is mapped into the source of the straightening chart
      intro z hz
      set w : Work.OneDim.E1 := arcChart d c hd hcd z with hw_def
      have hw : w ∈ (arcChart d c hd hcd).target := (arcChart d c hd hcd).map_source hz
      have hv : Work.OneDim.stdLEsd.symm w ∈ Ioo (-1 : ℝ) 1 := hw
      have hzw : z = pcircle d hd (Work.OneDim.stdLEsd.symm w) := by
        have h1 : (arcChart d c hd hcd).symm w = z := by
          rw [hw_def]
          exact (arcChart d c hd hcd).left_inv hz
        rw [← h1, arcChart_symm_apply]
      rw [hzw, Set.mem_preimage,
        slice_eq_curve ht₀ hd_def σ τ (Work.OneDim.stdLEsd.symm w)]
      exact curvePt_mem_source hd hcd hhpos hρs (t₀ + 2 * Real.pi) hσ' hτ'
        (abs_lt.mpr hv)
    · -- the straightening identity on the target of the domain chart
      intro u hu
      have hu' : u ∈ (arcChart d c hd hcd).target := by
        rwa [extend_target_self (arcChart d c hd hcd)] at hu
      have hv : Work.OneDim.stdLEsd.symm u ∈ Ioo (-1 : ℝ) 1 := hu'
      have hzu : ((arcChart d c hd hcd).extend Work.OneDim.I1).symm u
          = pcircle d hd (Work.OneDim.stdLEsd.symm u) := by
        rw [extend_symm_self, arcChart_symm_apply]
      simp only [Function.comp_apply]
      rw [hzu, slice_eq_curve ht₀ hd_def σ τ (Work.OneDim.stdLEsd.symm u),
        extend_self_plane,
        straightenChart_curve hd hcd hhpos hρs (t₀ + 2 * Real.pi) hσ' hτ' (abs_lt.mpr hv)]
      rfl
  · exact (Continuous.isClosedEmbedding (continuous_slice hρc σ τ) hinj).toIsEmbedding

theorem radialGraph_isotopy (rad : Circle → ℝ) (hrad : ∀ x, 0 < rad x)
    (hrads : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => rad (Circle.exp t))) :
    ∃ (gc : ℝ → Circle → ℝ × ℝ) (a b eps : ℝ),
      0 < a ∧ 0 < b ∧ a ≠ b ∧ (eps = 1 ∨ eps = -1) ∧
      (∀ x : Circle, gc 0 x = (rad x * Complex.re (x : ℂ), rad x * Complex.im (x : ℂ))) ∧
      (∀ z : Circle, gc 1 z = (a * Complex.re (z : ℂ), eps * (b * Complex.im (z : ℂ)))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => gc p.1 (Circle.exp p.2)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (gc s)) := by
  refine ⟨radialGraphFamily rad, 2, 1, 1, by norm_num, by norm_num, by norm_num, Or.inl rfl,
    ?_, ?_, ?_, ?_⟩
  · intro x
    rw [radialGraphFamily_zero]
  · intro z
    rw [radialGraphFamily_one]
    norm_num
  · exact contDiff_radialGraphFamily rad hrads
  · intro s hs
    have hs1 : 0 ≤ s := hs.1
    have hs2 : s ≤ 1 := hs.2
    have hσ : 0 < 1 + s := by linarith
    have hτ : 0 < 1 - s + s * 1 := by linarith
    have hρpos : ∀ x : Circle, 0 < (fun x : Circle => (1 - s) * rad x + s) x := by
      intro x
      have hx := hrad x
      show 0 < (1 - s) * rad x + s
      by_cases h0 : s = 0
      · rw [h0]; simpa using hx
      · have h1 : 0 ≤ (1 - s) * rad x := mul_nonneg (by linarith) (le_of_lt hx)
        have hs0 : 0 < s := lt_of_le_of_ne hs1 (Ne.symm h0)
        linarith
    have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (fun x : Circle => (1 - s) * rad x + s) (Circle.exp t)) :=
      (contDiff_const.mul hrads).add contDiff_const
    have hinj : Function.Injective (fun x : Circle =>
        ((1 + s) * ((fun x : Circle => (1 - s) * rad x + s) x * (x : ℂ).re),
         (1 - s + s * 1) * ((fun x : Circle => (1 - s) * rad x + s) x * (x : ℂ).im))) := by
      have hfun : (fun x : Circle =>
          ((1 + s) * ((fun x : Circle => (1 - s) * rad x + s) x * (x : ℂ).re),
           (1 - s + s * 1) * ((fun x : Circle => (1 - s) * rad x + s) x * (x : ℂ).im)))
          = radialGraphFamily rad s := rfl
      rw [hfun]
      exact radialGraphFamily_injective rad hrad hs
    exact isSmoothEmbedding_slice hρpos hρs hσ hτ hinj

end

end Work.Drive.PolarTwist
