import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.exists_Y9
import Submission.Work.C17b.isPreconnected_slitBall

/-!
# A14D: shared setup for `logCoeff_exists`

Definitions and elementary glue used by the proof of `Work.A14D.logCoeff_exists`:

* `slitDisk δ` : the disc `ball (1/9) δ` cut along the ray `(-∞, 1/9]`;
* `qZ` : the factor `-9z(1-z)` of `PZ` at `1/9`;
* `wron` : the Wronskian;
* `logTerm y` : `y · log (· - 1/9)`, holomorphic on the slit disc;
* `psiZ y` : the inhomogeneity `LZ (logTerm y)` (an entire function when `LZ y = 0`);
* the first order system `(u, u')' = sysA · (u,u') + sysb` equivalent to `LZ u = g`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- The complement of the slit ray `(-∞, 1/9]`. -/
def slitComp : Set ℂ := {z : ℂ | z.im ≠ 0 ∨ ninth.re < z.re}

/-- The slit disc: `ball (1/9) δ` with the ray `(-∞, 1/9]` removed. -/
def slitDisk (δ : ℝ) : Set ℂ := Metric.ball ninth δ ∩ slitComp

lemma mem_slitDisk_iff {δ : ℝ} {z : ℂ} :
    z ∈ slitDisk δ ↔ z ∈ Metric.ball ninth δ ∧ (z.im ≠ 0 ∨ ninth.re < z.re) := Iff.rfl

lemma isOpen_slitComp : IsOpen slitComp := by
  have hset : slitComp = {z : ℂ | z.im ≠ 0} ∪ {z : ℂ | ninth.re < z.re} := rfl
  rw [hset]
  refine (isOpen_compl_singleton.preimage Complex.continuous_im).union ?_
  exact isOpen_lt continuous_const Complex.continuous_re

lemma isOpen_slitDisk (δ : ℝ) : IsOpen (slitDisk δ) :=
  Metric.isOpen_ball.inter isOpen_slitComp

lemma slitComp_slitPlane {z : ℂ} (hz : z ∈ slitComp) : z - ninth ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hz with h | h
  · right
    have him : (z - ninth).im = z.im := by simp [ninth]
    rwa [him]
  · left
    have hre : (z - ninth).re = z.re - ninth.re := Complex.sub_re z ninth
    have h9 : ninth.re = 1 / 9 := by simp [ninth]
    rw [hre, h9]
    linarith

lemma slitPlane_slitComp {w : ℂ} (hw : w ∈ Complex.slitPlane) : w + ninth ∈ slitComp := by
  rw [Complex.mem_slitPlane_iff] at hw
  rcases hw with h | h
  · right
    have hre : (w + ninth).re = w.re + ninth.re := Complex.add_re w ninth
    have h9 : ninth.re = 1 / 9 := by simp [ninth]
    rw [hre, h9]
    linarith
  · left
    have him : (w + ninth).im = w.im := by simp [ninth]
    rwa [him]

lemma slitPlane_ne_zero {w : ℂ} (hw : w ∈ Complex.slitPlane) : w ≠ 0 := by
  rw [Complex.mem_slitPlane_iff] at hw
  rcases hw with h | h
  · intro h0; rw [h0] at h; simp at h
  · intro h0; exact h (by rw [h0]; simp)

lemma slitDisk_subset_slitComp {δ : ℝ} : slitDisk δ ⊆ slitComp := fun _ h => h.2

lemma isPreconnected_slitDisk {δ : ℝ} (hδ : 0 < δ) : IsPreconnected (slitDisk δ) := by
  have h0 : IsPreconnected (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0 ∨ u.im ≠ 0}) :=
    Work.C17b.isPreconnected_slitBall hδ
  have h9 : ninth.re = 1 / 9 := by simp [ninth]
  have himg : slitDisk δ
      = (fun u : ℂ => ninth - u) '' (Metric.ball (0 : ℂ) δ ∩ {u : ℂ | u.re < 0 ∨ u.im ≠ 0}) := by
    ext z
    constructor
    · intro hz
      have hb : ‖z - ninth‖ < δ := by
        simpa [Complex.dist_eq] using (Metric.mem_ball.mp hz.1)
      refine ⟨ninth - z, ⟨?_, ?_⟩, by ring⟩
      · rw [Metric.mem_ball]
        have h1 : dist (ninth - z) 0 = ‖z - ninth‖ := by
          rw [Complex.dist_eq]
          have : ninth - z - 0 = -(z - ninth) := by ring
          rw [this, norm_neg]
        rw [h1]; exact hb
      · rcases hz.2 with h | h
        · right
          have him : (ninth - z).im = -z.im := by simp [ninth]
          rw [him]; exact neg_ne_zero.mpr h
        · left
          have : (ninth - z).re = ninth.re - z.re := Complex.sub_re ninth z
          rw [this, h9]; linarith
    · rintro ⟨u, hu, rfl⟩
      have hb : ‖u‖ < δ := by
        simpa [Complex.dist_eq] using (Metric.mem_ball.mp hu.1)
      constructor
      · rw [Metric.mem_ball]
        have h1 : dist (ninth - u) ninth = ‖u‖ := by
          rw [Complex.dist_eq]
          have : ninth - u - ninth = -u := by ring
          rw [this, norm_neg]
        rw [h1]; exact hb
      · rcases hu.2 with h | h
        · right
          have : (ninth - u).re = ninth.re - u.re := Complex.sub_re ninth u
          rw [this, h9]; linarith
        · left
          have him : (ninth - u).im = -u.im := by simp [ninth]
          rw [him]; exact neg_ne_zero.mpr h
  rw [himg]
  exact h0.image _ (continuous_const.sub continuous_id).continuousOn

/-- `q z = -9 z (1 - z)`, so that `PZ z = (z - 1/9) * q z`. -/
def qZ (z : ℂ) : ℂ := -9 * z * (1 - z)

lemma PZ_eq_mul_qZ (z : ℂ) : PZ z = (z - ninth) * qZ z := by
  simp only [PZ, qZ, ninth]; ring

lemma PZ'_sub_qZ (z : ℂ) : PZ' z - qZ z = (18 * z - 9) * (z - ninth) := by
  simp only [PZ', qZ, ninth]; ring

lemma qZ_ninth : qZ ninth = PZ' ninth := by
  simp only [qZ, PZ', ninth]; norm_num

lemma qZ_ninth_ne_zero : qZ ninth ≠ 0 := by
  rw [qZ_ninth]; simp only [PZ', ninth]; norm_num

lemma LZ_def (f : ℂ → ℂ) (z : ℂ) :
    LZ f z = PZ z * deriv (deriv f) z + PZ' z * deriv f z + RZ z * f z := rfl

/-- The Wronskian `u v' - u' v`. -/
def wron (u v : ℂ → ℂ) (z : ℂ) : ℂ := u z * deriv v z - deriv u z * v z

/-- `y · log (· - 1/9)`. -/
def logTerm (y : ℂ → ℂ) : ℂ → ℂ := fun z => y z * Complex.log (z - ninth)

/-- The inhomogeneity `ψ = LZ (logTerm y)` for a solution `y` of `LZ y = 0`. -/
def psiZ (y : ℂ → ℂ) : ℂ → ℂ := fun z => 2 * qZ z * deriv y z + (18 * z - 9) * y z

/-- `logTerm y` is holomorphic wherever `y` is, on the slit disc. -/
lemma differentiableOn_logTerm {y : ℂ → ℂ} {δ : ℝ}
    (hy : DifferentiableOn ℂ y (Metric.ball ninth δ)) :
    DifferentiableOn ℂ (logTerm y) (slitDisk δ) := by
  refine (hy.mono Set.inter_subset_left).mul ?_
  intro z hz
  exact (Complex.differentiableAt_log (slitComp_slitPlane hz.2)).comp z
    (differentiableAt_id.sub_const ninth) |>.differentiableWithinAt

/-- Derivative of `log (· - 1/9)`. -/
lemma hasDerivAt_log_sub_19 {z : ℂ} (hz : z - ninth ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log (w - ninth)) ((z - ninth)⁻¹) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - ninth) 1 z := (hasDerivAt_id z).sub_const ninth
  have h3 := (Complex.hasDerivAt_log hz).comp z h1
  simpa [Function.comp_def] using h3

/-- Derivative of `(· - 1/9)⁻¹`. -/
lemma hasDerivAt_inv_sub {z : ℂ} (hz : z - ninth ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => (w - ninth)⁻¹) (-(z - ninth) ^ 2)⁻¹ z := by
  have h1 : HasDerivAt (fun w : ℂ => w - ninth) 1 z := (hasDerivAt_id z).sub_const ninth
  have h2 := h1.inv (slitPlane_ne_zero hz)
  have he : -1 / (z - ninth) ^ 2 = (-(z - ninth) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, inv_neg]; ring
  rw [he] at h2
  exact h2

/-- Pointwise derivative of `logTerm y`. -/
lemma hasDerivAt_logTerm {y : ℂ → ℂ} {z : ℂ} (hy : HasDerivAt y (deriv y z) z)
    (hz : z - ninth ∈ Complex.slitPlane) :
    HasDerivAt (logTerm y)
      (deriv y z * Complex.log (z - ninth) + y z * (z - ninth)⁻¹) z :=
  hy.mul (hasDerivAt_log_sub_19 hz)

/-- `deriv (logTerm y)` on the slit disc. -/
lemma deriv_logTerm {y : ℂ → ℂ} {δ : ℝ} (hy : DifferentiableOn ℂ y (slitDisk δ))
    {z : ℂ} (hz : z ∈ slitDisk δ) :
    deriv (logTerm y) z = deriv y z * Complex.log (z - ninth) + y z * (z - ninth)⁻¹ :=
  (hasDerivAt_logTerm ((hy.differentiableAt ((isOpen_slitDisk δ).mem_nhds hz)).hasDerivAt)
    (slitComp_slitPlane hz.2)).deriv

/-- `deriv (deriv (logTerm y))` on the slit disc. -/
lemma deriv_deriv_logTerm {y : ℂ → ℂ} {δ : ℝ} (hy : DifferentiableOn ℂ y (slitDisk δ))
    (hy' : DifferentiableOn ℂ (deriv y) (slitDisk δ)) {z : ℂ} (hz : z ∈ slitDisk δ) :
    deriv (deriv (logTerm y)) z
      = deriv (deriv y) z * Complex.log (z - ninth) + deriv y z * (z - ninth)⁻¹
        + deriv y z * (z - ninth)⁻¹ + y z * (-(z - ninth) ^ 2)⁻¹ := by
  have hopen := isOpen_slitDisk δ
  have hmem : z - ninth ∈ Complex.slitPlane := slitComp_slitPlane hz.2
  have hyz : HasDerivAt y (deriv y z) z := (hy.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have hyz' : HasDerivAt (deriv y) (deriv (deriv y) z) z :=
    (hy'.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have h := (hyz'.mul (hasDerivAt_log_sub_19 hmem)).add (hyz.mul (hasDerivAt_inv_sub hmem))
  have hderiv : deriv (fun w : ℂ => deriv y w * Complex.log (w - ninth) + y w * (w - ninth)⁻¹) z
      = (deriv (deriv y) z * Complex.log (z - ninth) + deriv y z * (z - ninth)⁻¹)
        + (deriv y z * (z - ninth)⁻¹ + y z * (-(z - ninth) ^ 2)⁻¹) := h.deriv
  have hev : (fun w : ℂ => deriv (logTerm y) w)
      =ᶠ[𝓝 z] fun w : ℂ => deriv y w * Complex.log (w - ninth) + y w * (w - ninth)⁻¹ := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact deriv_logTerm hy hw
  have heq : deriv (fun w : ℂ => deriv (logTerm y) w) z
      = deriv (fun w : ℂ => deriv y w * Complex.log (w - ninth) + y w * (w - ninth)⁻¹) z :=
    Filter.EventuallyEq.deriv_eq hev
  show deriv (fun w : ℂ => deriv (logTerm y) w) z = _
  rw [heq, hderiv]
  ring

/-- The computation `LZ (y · log (· - 1/9)) = ψ` for a solution `y`. -/
theorem LZ_logTerm {y : ℂ → ℂ} {δ : ℝ} (hy : DifferentiableOn ℂ y (slitDisk δ))
    (hy' : DifferentiableOn ℂ (deriv y) (slitDisk δ))
    (hode : ∀ w ∈ slitDisk δ, LZ y w = 0) {z : ℂ} (hz : z ∈ slitDisk δ) :
    LZ (logTerm y) z = psiZ y z := by
  have hmem : z - ninth ∈ Complex.slitPlane := slitComp_slitPlane hz.2
  have hzs : z - ninth ≠ 0 := slitPlane_ne_zero hmem
  have h1 := deriv_logTerm hy hz
  have h2 := deriv_deriv_logTerm hy hy' hz
  have hodez : PZ z * deriv (deriv y) z + PZ' z * deriv y z + RZ z * y z = 0 := by
    have := hode z hz; rwa [LZ_def] at this
  rw [LZ_def, h2, h1, logTerm, psiZ]
  rw [PZ_eq_mul_qZ, show PZ' z = qZ z + (18 * z - 9) * (z - ninth) by
    have := PZ'_sub_qZ z; linear_combination this] at hodez ⊢
  field_simp
  linear_combination ((z - ninth) * Complex.log (z - ninth)) * hodez

/-- The 2×2 system matrix of `LZ`: `(u, u')' = A (u, u') + b`. -/
def sysA (z : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![0, 1], ![-(RZ z / PZ z), -(PZ' z / PZ z)]]

/-- The inhomogeneity of the first order system. -/
def sysb (g : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ := ![0, g z / PZ z]

/-- `(u, u')` as a vector. -/
def toSol (u : ℂ → ℂ) : ℂ → Fin 2 → ℂ := fun z => ![u z, deriv u z]

lemma sum_sysA_zero (g : ℂ → ℂ) (z : ℂ) (u : ℂ → ℂ) :
    (∑ j, sysA z 0 j * toSol u z j + sysb g z 0) = deriv u z := by
  simp [sysA, sysb, toSol, Fin.sum_univ_two]

lemma sum_sysA_one (g : ℂ → ℂ) (z : ℂ) (u : ℂ → ℂ) :
    (∑ j, sysA z 1 j * toSol u z j + sysb g z 1)
      = -(RZ z / PZ z) * u z - (PZ' z / PZ z) * deriv u z + g z / PZ z := by
  simp only [sysA, sysb, toSol, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val']
  ring

/-- The scalar equation `LZ u = g` gives the first order system for `(u, u')`. -/
theorem hasDerivAt_toSol {u g : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℂ u z)
    (hu' : DifferentiableAt ℂ (deriv u) z) (hP : PZ z ≠ 0) (h : LZ u z = g z) :
    HasDerivAt (toSol u) (fun i => ∑ j, sysA z i j * toSol u z j + sysb g z i) z := by
  have h0 : HasDerivAt (fun x : ℂ => toSol u x 0) (deriv u z) z :=
    (hu.hasDerivAt).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => by simp [toSol]))
  have hdiv : deriv (deriv u) z
      = -(RZ z / PZ z) * u z - (PZ' z / PZ z) * deriv u z + g z / PZ z := by
    have key : deriv (deriv u) z * PZ z = g z - PZ' z * deriv u z - RZ z * u z := by
      rw [LZ_def] at h
      linear_combination h
    have key2 : deriv (deriv u) z = (g z - PZ' z * deriv u z - RZ z * u z) / PZ z := by
      rw [eq_div_iff hP]
      linear_combination key
    rw [key2]
    field_simp
    ring
  have h1 : HasDerivAt (fun x : ℂ => toSol u x 1) (deriv (deriv u) z) z :=
    (hu'.hasDerivAt).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => by simp [toSol]))
  rw [hdiv] at h1
  refine hasDerivAt_pi.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · change HasDerivAt (fun x : ℂ => toSol u x 0)
      (∑ j, sysA z 0 j * toSol u z j + sysb g z 0) z
    rw [sum_sysA_zero]; exact h0
  · change HasDerivAt (fun x : ℂ => toSol u x 1)
      (∑ j, sysA z 1 j * toSol u z j + sysb g z 1) z
    rw [sum_sysA_one]; exact h1

/-- Conversely, a system solution is `(u, u')` for a solution `u` of `LZ u = g`. -/
theorem LZ_of_hasDerivAt_toSol {u g : ℂ → ℂ} {z : ℂ}
    (h : HasDerivAt (toSol u) (fun i => ∑ j, sysA z i j * toSol u z j + sysb g z i) z)
    (hu' : DifferentiableAt ℂ (deriv u) z) (hP : PZ z ≠ 0) : LZ u z = g z := by
  have hc : HasDerivAt (fun w : ℂ => deriv u w)
      (-(RZ z / PZ z) * u z - (PZ' z / PZ z) * deriv u z + g z / PZ z) z := by
    have h1 := (hasDerivAt_pi.mp h) 1
    have hf : (fun w : ℂ => toSol u w 1) = fun w : ℂ => deriv u w := by
      funext w; simp [toSol]
    rw [hf, sum_sysA_one] at h1
    exact h1
  have h2 : deriv (deriv u) z
      = -(RZ z / PZ z) * u z - (PZ' z / PZ z) * deriv u z + g z / PZ z := hc.deriv
  rw [LZ_def, h2]
  field_simp
  ring

end

end Work.A14D
