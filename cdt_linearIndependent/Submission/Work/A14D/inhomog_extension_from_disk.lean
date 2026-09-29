import Mathlib
import Submission.Work.A14D.setup
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.OdeCont.uniqueness
import Submission.Work.OdeCont.ode_continuation

/-!
# A14D — extension of a solution of `LZ g = -κ ψ` from a small disc to `ball ninth δ`

This file proves `Work.A14D.inhomog_extension_from_disk`: a function `g` holomorphic on
`ball ninth ρ` which solves the inhomogeneous Fuchsian equation `LZ g = -κ ψ` on the punctured
ball extends to a holomorphic solution on the larger ball `ball ninth δ` (`ρ ≤ δ`).

The point is that although `1/9` is a singular point of `LZ`, a solution which is holomorphic
*at* `1/9` (as `g` is, being differentiable on the whole ball `ball ninth ρ`) has no monodromy
there and can be continued across the singularity.  Rather than invoking the local structure
theory at the singular point, we use the elementary continuation theorem for linear systems on
the disc (`Work.OdeCont.ode_continuation`): after rescaling `w = (z - 1/9)/δ` the solution
`(Y₀ w) = (g (1/9 + δ w), (deriv g) (1/9 + δ w))` of the first order linear system associated
with `LZ` is holomorphic on a disc `‖w‖ < r₁` and solves the system on the annulus
`r₀ < ‖w‖ < r₁` (`r₀ < r₁`), so it extends to the whole unit disc; the extension `Y` solves the
system there because the defect `deriv Y - A Y - b` is holomorphic on the punctured disc and
vanishes on the annulus (an open subset).  Reading off the first component gives the required
`G`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## The scaled first order system -/

/-- The system matrix of `LZ`, scaled by `δ`, evaluated at `ninth + δ w`. -/
def inh_sA (δ : ℝ) (w : ℂ) : Fin 2 → Fin 2 → ℂ := δ • sysA (ninth + δ * w)

/-- The inhomogeneity of the scaled system. -/
def inh_sB (δ : ℝ) (σ : ℂ → ℂ) (w : ℂ) : Fin 2 → ℂ := δ • sysb σ (ninth + δ * w)

/-- The candidate continuation: the first component of the extended solution. -/
def inh_contExt (δ : ℝ) (Y : ℂ → Fin 2 → ℂ) (z : ℂ) : ℂ := Y ((z - ninth) / δ) 0

lemma inh_sA_apply_zero_zero (δ : ℝ) (w : ℂ) : inh_sA δ w 0 0 = 0 := by simp [inh_sA, sysA]

lemma inh_sA_apply_zero_one (δ : ℝ) (w : ℂ) : inh_sA δ w 0 1 = (δ : ℂ) := by simp [inh_sA, sysA]

lemma inh_sA_apply_one_zero (δ : ℝ) (w : ℂ) :
    inh_sA δ w 1 0 = -(δ * (RZ (ninth + δ * w) / PZ (ninth + δ * w))) := by simp [inh_sA, sysA]

lemma inh_sA_apply_one_one (δ : ℝ) (w : ℂ) :
    inh_sA δ w 1 1 = -(δ * (PZ' (ninth + δ * w) / PZ (ninth + δ * w))) := by simp [inh_sA, sysA]

lemma inh_sB_apply_zero (δ : ℝ) (σ : ℂ → ℂ) (w : ℂ) : inh_sB δ σ w 0 = 0 := by simp [inh_sB, sysb]

lemma inh_sB_apply_one (δ : ℝ) (σ : ℂ → ℂ) (w : ℂ) :
    inh_sB δ σ w 1 = (δ : ℂ) * (σ (ninth + δ * w) / PZ (ninth + δ * w)) := by
  simp only [inh_sB, sysb, Pi.smul_apply, Complex.real_smul, Matrix.cons_val_one,
    Matrix.cons_val_zero]

/-- The scaled system is `δ • (unscaled system)`. -/
lemma inh_smul_sys (δ : ℝ) (σ : ℂ → ℂ) (w : ℂ) (v : Fin 2 → ℂ) :
    (fun i => ∑ j, inh_sA δ w i j * v j + inh_sB δ σ w i)
      = (δ : ℂ) • (fun i => ∑ j, sysA (ninth + δ * w) i j * v j
          + sysb σ (ninth + δ * w) i) := by
  funext i
  simp only [inh_sA, inh_sB, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-! ## Elementary facts about the singular points of `PZ` -/

/-- `PZ` does not vanish away from its three roots `0, 1, 1/9`. -/
lemma inh_PZ_ne_zero_of_ne {z : ℂ} (hz : z ≠ ninth) (hd : dist z ninth < 1 / 9) : PZ z ≠ 0 := by
  intro h
  have h1 : z = 0 ∨ z = 1 ∨ z = ninth := by
    simp only [PZ] at h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl (by linear_combination -h''))
    · refine Or.inr (Or.inr ?_)
      have hz9 : z = 1 / 9 := by linear_combination -h' / 9
      simpa [ninth] using hz9
  rcases h1 with rfl | rfl | rfl
  · rw [Complex.dist_eq] at hd
    have : ‖(0 : ℂ) - ninth‖ = 1 / 9 := by simp [ninth]
    rw [this] at hd
    exact absurd hd (lt_irrefl _)
  · rw [Complex.dist_eq] at hd
    have : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by norm_num [ninth, Complex.normSq]
    rw [this] at hd
    norm_num at hd
  · exact hz rfl

lemma inh_ninth_add_ne_ninth {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : 0 < ‖w‖) :
    ninth + δ * w ≠ ninth := by
  intro h
  have h1 : δ * w = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hδ))
  · exact absurd h2 (norm_pos_iff.mp hw)

lemma inh_ninth_add_norm {δ : ℝ} (hδ : 0 < δ) (w : ℂ) :
    dist (ninth + δ * w) ninth = δ * ‖w‖ := by
  rw [Complex.dist_eq]
  have h1 : ninth + δ * w - ninth = (δ : ℂ) * w := by ring
  rw [h1, norm_mul]
  have h2 : ‖(δ : ℂ)‖ = δ := by simp [abs_of_pos hδ]
  rw [h2]

lemma inh_norm_ofReal_of_pos {a : ℝ} (ha : 0 < a) : ‖(a : ℂ)‖ = a := by
  simp [abs_of_pos ha]

lemma inh_annulus_zero_maps {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    Set.MapsTo (fun w : ℂ => ninth + δ * w) (Work.OdeCont.annulus 0 1)
      ((Metric.ball ninth (1 / 9)) \ {ninth}) := by
  intro w hw
  rw [Work.OdeCont.annulus] at hw
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, inh_ninth_add_norm hδ]
    have h1 : δ * ‖w‖ < δ * 1 := mul_lt_mul_of_pos_left hw.2 hδ
    linarith
  · simp only [Set.mem_singleton_iff]
    exact inh_ninth_add_ne_ninth hδ hw.1

/-- The punctured unit disc is preconnected. -/
lemma inh_isPreconnected_annulus_zero : IsPreconnected (Work.OdeCont.annulus 0 1) := by
  have hconv : Convex ℝ {w : ℂ | w.re < 0} := convex_halfSpace_re_lt 0
  have himg : Work.OdeCont.annulus 0 1 = Complex.exp '' {w : ℂ | w.re < 0} := by
    ext z
    constructor
    · intro hz
      rw [Work.OdeCont.annulus] at hz
      refine ⟨Complex.log z, ?_, Complex.exp_log (norm_pos_iff.mp hz.1)⟩
      show (Complex.log z).re < 0
      rw [Complex.log_re]
      exact Real.log_neg hz.1 hz.2
    · rintro ⟨u, hu, rfl⟩
      rw [Work.OdeCont.annulus]
      refine ⟨?_, ?_⟩
      · rw [Complex.norm_exp]; exact Real.exp_pos u.re
      · rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.mpr hu
  rw [himg]
  exact IsPreconnected.image hconv.isPreconnected Complex.exp Complex.continuous_exp.continuousOn

/-! ## Differentiability of the scaled system -/

lemma inh_core_RZ :
    DifferentiableOn ℂ (fun z : ℂ => RZ z / PZ z) ((Metric.ball ninth (1 / 9)) \ {ninth}) := by
  intro z hz
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at hz
  have hPZ : PZ z ≠ 0 := inh_PZ_ne_zero_of_ne hz.2 (Metric.mem_ball.mp hz.1)
  exact (((by unfold RZ; fun_prop : DifferentiableAt ℂ RZ z)).div
    (by unfold PZ; fun_prop : DifferentiableAt ℂ PZ z) hPZ).differentiableWithinAt

lemma inh_core_PZ' :
    DifferentiableOn ℂ (fun z : ℂ => PZ' z / PZ z) ((Metric.ball ninth (1 / 9)) \ {ninth}) := by
  intro z hz
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at hz
  have hPZ : PZ z ≠ 0 := inh_PZ_ne_zero_of_ne hz.2 (Metric.mem_ball.mp hz.1)
  exact (((by unfold PZ'; fun_prop : DifferentiableAt ℂ PZ' z)).div
    (by unfold PZ; fun_prop : DifferentiableAt ℂ PZ z) hPZ).differentiableWithinAt

lemma inh_core_RZ_smul {δ : ℝ} :
    DifferentiableOn ℂ (fun z : ℂ => -(δ * (RZ z / PZ z)))
      ((Metric.ball ninth (1 / 9)) \ {ninth}) := by
  have h : (fun z : ℂ => -(δ * (RZ z / PZ z)))
      = (fun _ => -(δ : ℂ)) * (fun z : ℂ => RZ z / PZ z) := by
    funext z
    simp only [Pi.mul_apply]
    ring
  rw [h]
  exact (differentiableOn_const (-(δ : ℂ))).mul inh_core_RZ

lemma inh_core_PZ'_smul {δ : ℝ} :
    DifferentiableOn ℂ (fun z : ℂ => -(δ * (PZ' z / PZ z)))
      ((Metric.ball ninth (1 / 9)) \ {ninth}) := by
  have h : (fun z : ℂ => -(δ * (PZ' z / PZ z)))
      = (fun _ => -(δ : ℂ)) * (fun z : ℂ => PZ' z / PZ z) := by
    funext z
    simp only [Pi.mul_apply]
    ring
  rw [h]
  exact (differentiableOn_const (-(δ : ℂ))).mul inh_core_PZ'

/-- The holomorphy of `ψZ y9` on a ball. -/
lemma inh_differentiableOn_psiZ {y9 : ℂ → ℂ} {δ : ℝ}
    (hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ)) :
    DifferentiableOn ℂ (psiZ y9) (Metric.ball ninth δ) := by
  have hq : DifferentiableOn ℂ (fun z : ℂ => -9 * z * (1 - z)) (Metric.ball ninth δ) := by
    fun_prop
  have hd : DifferentiableOn ℂ (fun z : ℂ => deriv y9 z) (Metric.ball ninth δ) :=
    hy9d.deriv isOpen_ball
  have hl : DifferentiableOn ℂ (fun z : ℂ => (18 * z - 9)) (Metric.ball ninth δ) := by fun_prop
  have h1 : DifferentiableOn ℂ (fun z : ℂ => 2 * (-9 * z * (1 - z)) * deriv y9 z)
      (Metric.ball ninth δ) := ((differentiableOn_const (2 : ℂ)).mul hq).mul hd
  have h2 : DifferentiableOn ℂ (fun z : ℂ => (18 * z - 9) * y9 z) (Metric.ball ninth δ) :=
    hl.mul hy9d
  unfold psiZ qZ
  exact h1.add h2

lemma inh_differentiableAt_sA {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) {w : ℂ}
    (hw : w ∈ Work.OdeCont.annulus 0 1) : DifferentiableAt ℂ (inh_sA δ) w := by
  have hmem := inh_annulus_zero_maps hδ hδ20 hw
  have hPZ : PZ (ninth + δ * w) ≠ 0 :=
    inh_PZ_ne_zero_of_ne (by simpa using hmem.2) (Metric.mem_ball.mp hmem.1)
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  fin_cases i <;> fin_cases j
  · show DifferentiableAt ℂ (fun x : ℂ => inh_sA δ x 0 0) w
    rw [show (fun x : ℂ => inh_sA δ x 0 0) = fun _ => (0 : ℂ) from by funext x; simp [inh_sA, sysA]]
    exact differentiableAt_const 0
  · show DifferentiableAt ℂ (fun x : ℂ => inh_sA δ x 0 1) w
    rw [show (fun x : ℂ => inh_sA δ x 0 1) = fun _ => (δ : ℂ) from by funext x; simp [inh_sA, sysA]]
    exact differentiableAt_const (δ : ℂ)
  · show DifferentiableAt ℂ (fun x : ℂ => inh_sA δ x 1 0) w
    have hfun : (fun x : ℂ => inh_sA δ x 1 0)
        = (fun _ : ℂ => -(δ : ℂ)) * ((fun z : ℂ => RZ z / PZ z)
            ∘ (fun x : ℂ => ninth + δ * x)) := by
      funext x
      rw [inh_sA_apply_one_zero]
      simp only [Pi.mul_apply, Function.comp_apply]
      ring
    rw [hfun]
    exact (differentiableAt_const (-(δ : ℂ))).mul
      (((by unfold RZ; fun_prop : DifferentiableAt ℂ RZ (ninth + δ * w)).div
        (by unfold PZ; fun_prop : DifferentiableAt ℂ PZ (ninth + δ * w)) hPZ).comp w
        (by fun_prop))
  · show DifferentiableAt ℂ (fun x : ℂ => inh_sA δ x 1 1) w
    have hfun : (fun x : ℂ => inh_sA δ x 1 1)
        = (fun _ : ℂ => -(δ : ℂ)) * ((fun z : ℂ => PZ' z / PZ z)
            ∘ (fun x : ℂ => ninth + δ * x)) := by
      funext x
      rw [inh_sA_apply_one_one]
      simp only [Pi.mul_apply, Function.comp_apply]
      ring
    rw [hfun]
    exact (differentiableAt_const (-(δ : ℂ))).mul
      (((by unfold PZ'; fun_prop : DifferentiableAt ℂ PZ' (ninth + δ * w)).div
        (by unfold PZ; fun_prop : DifferentiableAt ℂ PZ (ninth + δ * w)) hPZ).comp w
        (by fun_prop))

lemma inh_differentiableOn_sA {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    DifferentiableOn ℂ (inh_sA δ) (Work.OdeCont.annulus 0 1) :=
  fun w hw => (inh_differentiableAt_sA hδ hδ20 hw).differentiableWithinAt

lemma inh_differentiableAt_sB {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) {σ : ℂ → ℂ}
    (hσd : DifferentiableOn ℂ σ (Metric.ball ninth δ)) {w : ℂ}
    (hw : w ∈ Work.OdeCont.annulus 0 1) : DifferentiableAt ℂ (inh_sB δ σ) w := by
  have hmem := inh_annulus_zero_maps hδ hδ20 hw
  have hmemδ : ninth + δ * w ∈ Metric.ball ninth δ := by
    rw [Metric.mem_ball, inh_ninth_add_norm hδ]
    have h1 : δ * ‖w‖ < δ * 1 := mul_lt_mul_of_pos_left hw.2 hδ
    linarith
  have hPZ : PZ (ninth + δ * w) ≠ 0 :=
    inh_PZ_ne_zero_of_ne (by simpa using hmem.2) (Metric.mem_ball.mp hmem.1)
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · show DifferentiableAt ℂ (fun x : ℂ => inh_sB δ σ x 0) w
    rw [show (fun x : ℂ => inh_sB δ σ x 0) = fun _ => (0 : ℂ) from by funext x; simp [inh_sB, sysb]]
    exact differentiableAt_const 0
  · show DifferentiableAt ℂ (fun x : ℂ => inh_sB δ σ x 1) w
    have hfun : (fun x : ℂ => inh_sB δ σ x 1)
        = (fun _ : ℂ => (δ : ℂ)) * ((fun z : ℂ => σ z / PZ z)
            ∘ (fun x : ℂ => ninth + δ * x)) := by
      funext x
      rw [inh_sB_apply_one]
      simp only [Pi.mul_apply, Function.comp_apply]
    rw [hfun]
    exact (differentiableAt_const (δ : ℂ)).mul
      (((hσd.differentiableAt (Metric.isOpen_ball.mem_nhds hmemδ)).div
        (by unfold PZ; fun_prop : DifferentiableAt ℂ PZ (ninth + δ * w)) hPZ).comp w
        (by fun_prop))

lemma inh_differentiableOn_sB {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) {σ : ℂ → ℂ}
    (hσd : DifferentiableOn ℂ σ (Metric.ball ninth δ)) :
    DifferentiableOn ℂ (inh_sB δ σ) (Work.OdeCont.annulus 0 1) :=
  fun w hw => (inh_differentiableAt_sB hδ hδ20 hσd hw).differentiableWithinAt

/-! ## The scaled system at a point of the small annulus -/

/-- `Y₀ = toSol (g ∘ (ninth + δ ·))` solves the scaled system wherever `g` solves
`LZ g = -κ ψ`. -/
lemma inh_hasDerivAt_scaled {y9 : ℂ → ℂ} {δ ρ : ℝ} (κ : ℂ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball ninth ρ))
    (hgode : ∀ z ∈ Metric.ball ninth ρ, z ≠ ninth → LZ g z = -κ * psiZ y9 z)
    {w : ℂ} (hz : ninth + δ * w ∈ Metric.ball ninth ρ) (hzne : ninth + δ * w ≠ ninth)
    (hP : PZ (ninth + δ * w) ≠ 0) :
    HasDerivAt (fun w : ℂ => toSol g (ninth + δ * w))
      (fun i => ∑ j, inh_sA δ w i j * toSol g (ninth + δ * w) j
        + inh_sB δ (fun z => -κ * psiZ y9 z) w i) w := by
  have hhu : DifferentiableAt ℂ g (ninth + δ * w) :=
    hg.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hhu' : DifferentiableAt ℂ (deriv g) (ninth + δ * w) :=
    (hg.deriv Metric.isOpen_ball).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hode : LZ g (ninth + δ * w) = (fun z => -κ * psiZ y9 z) (ninth + δ * w) :=
    hgode _ hz hzne
  have h1 : HasDerivAt (toSol g)
      (fun i => ∑ j, sysA (ninth + δ * w) i j * toSol g (ninth + δ * w) j
        + sysb (fun z => -κ * psiZ y9 z) (ninth + δ * w) i) (ninth + δ * w) :=
    hasDerivAt_toSol hhu hhu' hP hode
  have h2 : HasDerivAt (fun w : ℂ => ninth + δ * w) (δ : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (δ : ℂ)).const_add ninth
  have h3 := h1.scomp w h2
  rw [inh_smul_sys]
  exact h3

/-! ## The main theorem -/

theorem inhomog_extension_from_disk {y9 : ℂ → ℂ} {δ ρ : ℝ} (hY : Y9 y9 δ) (hρ : 0 < ρ)
    (hρδ : ρ ≤ δ) (κ : ℂ) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball ninth ρ))
    (hgode : ∀ z ∈ Metric.ball ninth ρ, z ≠ ninth → LZ g z = -κ * psiZ y9 z) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball ninth δ) ∧
      Set.EqOn G g (Metric.ball ninth ρ) ∧
      (∀ z ∈ Metric.ball ninth δ, z ≠ ninth → LZ G z = -κ * psiZ y9 z) := by
  have hδpos : 0 < δ := hY.1
  have hδ20 : δ ≤ 1 / 20 := hY.2.1
  have hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ) := hY.2.2.1
  have hσd : DifferentiableOn ℂ (fun z : ℂ => -κ * psiZ y9 z) (Metric.ball ninth δ) :=
    (differentiableOn_const (-κ)).mul (inh_differentiableOn_psiZ hy9d)
  have hδneR : δ ≠ 0 := ne_of_gt hδpos
  have hδne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδneR
  -- scaling constants
  have hr0pos : 0 < ρ / (2 * δ) := div_pos hρ (by linarith)
  have hr1pos : 0 < ρ / δ := div_pos hρ hδpos
  have hr01 : ρ / (2 * δ) < ρ / δ := by
    rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * δ) hδpos]
    nlinarith [hρ]
  have hr11 : ρ / δ ≤ 1 := by
    rw [div_le_one hδpos]; exact hρδ
  -- membership in the ball `ball ninth ρ`
  have hmemρ : ∀ w : ℂ, ‖w‖ < ρ / δ → ninth + δ * w ∈ Metric.ball ninth ρ := by
    intro w hw
    rw [Metric.mem_ball, inh_ninth_add_norm hδpos]
    have h1 : δ * ‖w‖ < δ * (ρ / δ) := mul_lt_mul_of_pos_left hw hδpos
    rw [mul_div_cancel₀ _ hδneR] at h1
    exact h1
  -- the initial datum is holomorphic
  have htoSol_d : DifferentiableOn ℂ (toSol g) (Metric.ball ninth ρ) := by
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · simpa [toSol] using hg
    · simpa [toSol] using hg.deriv isOpen_ball
  have hY0d : DifferentiableOn ℂ (fun w : ℂ => toSol g (ninth + δ * w))
      (Metric.ball 0 (ρ / δ)) :=
    htoSol_d.comp (by fun_prop) (fun w hw => hmemρ w (by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hw; exact hw))
  -- the initial datum solves the system on the annulus
  have hY0' : ∀ w : ℂ, ρ / (2 * δ) < ‖w‖ → ‖w‖ < ρ / δ →
      HasDerivAt (fun w : ℂ => toSol g (ninth + δ * w))
        (fun i => ∑ j, inh_sA δ w i j * toSol g (ninth + δ * w) j
          + inh_sB δ (fun z => -κ * psiZ y9 z) w i) w := by
    intro w hw0 hw1
    have hwpos : 0 < ‖w‖ := lt_trans hr0pos hw0
    have hw1' : ‖w‖ < 1 := lt_of_lt_of_le hw1 hr11
    have hmem : ninth + δ * w ∈ (Metric.ball ninth (1 / 9)) \ {ninth} := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, inh_ninth_add_norm hδpos]
        have h1 : δ * ‖w‖ < δ * (ρ / δ) := mul_lt_mul_of_pos_left hw1 hδpos
        rw [mul_div_cancel₀ _ hδneR] at h1
        linarith [hρδ]
      · simp only [Set.mem_singleton_iff]
        exact inh_ninth_add_ne_ninth hδpos hwpos
    exact inh_hasDerivAt_scaled κ hg hgode (hmemρ w hw1) hmem.2
      (inh_PZ_ne_zero_of_ne hmem.2 (Metric.mem_ball.mp hmem.1))
  -- holomorphy of the scaled system
  have hAd : DifferentiableOn ℂ (inh_sA δ) (Work.OdeCont.annulus 0 1) :=
    inh_differentiableOn_sA hδpos hδ20
  have hBd : DifferentiableOn ℂ (inh_sB δ (fun z => -κ * psiZ y9 z)) (Work.OdeCont.annulus 0 1) :=
    inh_differentiableOn_sB hδpos hδ20 hσd
  have hAd' : DifferentiableOn ℂ (inh_sA δ) (Work.OdeCont.annulus (ρ / (2 * δ)) 1) :=
    hAd.mono (fun w hw => ⟨lt_trans hr0pos hw.1, hw.2⟩)
  have hBd' : DifferentiableOn ℂ (inh_sB δ (fun z => -κ * psiZ y9 z))
      (Work.OdeCont.annulus (ρ / (2 * δ)) 1) :=
    hBd.mono (fun w hw => ⟨lt_trans hr0pos hw.1, hw.2⟩)
  -- apply the continuation theorem
  obtain ⟨Y, hYd, hYeq⟩ := Work.OdeCont.ode_continuation 2 (inh_sA δ)
    (inh_sB δ (fun z => -κ * psiZ y9 z)) (ρ / (2 * δ)) (ρ / δ)
    (fun w => toSol g (ninth + δ * w)) hr0pos hr01 hr11 hAd' hBd' hY0d hY0'
  -- `Y` is holomorphic on the punctured disc
  have hYdAnn : DifferentiableOn ℂ Y (Work.OdeCont.annulus 0 1) :=
    hYd.mono (fun w hw => by
      rw [Work.OdeCont.annulus] at hw
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      exact hw.2)
  -- the system holds on the whole punctured disc
  have hsys : ∀ w ∈ Work.OdeCont.annulus 0 1,
      deriv Y w = fun i => ∑ j, inh_sA δ w i j * Y w j + inh_sB δ (fun z => -κ * psiZ y9 z) w i := by
    set F : ℂ → Fin 2 → ℂ := fun w => deriv Y w
      - (fun i => ∑ j, inh_sA δ w i j * Y w j + inh_sB δ (fun z => -κ * psiZ y9 z) w i) with hFdef
    have hFd : DifferentiableOn ℂ F (Work.OdeCont.annulus 0 1) := by
      have hmono : F = fun w : ℂ => deriv Y w
          - (fun i => ∑ j, inh_sA δ w i j * Y w j + inh_sB δ (fun z => -κ * psiZ y9 z) w i) := rfl
      rw [hmono]
      refine DifferentiableOn.sub (hYdAnn.deriv (Work.OdeCont.isOpen_annulus 0 1)) ?_
      rw [differentiableOn_pi]
      intro i
      have hadd : (fun w : ℂ => ∑ j : Fin 2, inh_sA δ w i j * Y w j
            + inh_sB δ (fun z => -κ * psiZ y9 z) w i)
          = fun w : ℂ => (inh_sA δ w i 0 * Y w 0 + inh_sA δ w i 1 * Y w 1)
            + inh_sB δ (fun z => -κ * psiZ y9 z) w i := by
        funext w; rw [Fin.sum_univ_two]
      rw [hadd]
      refine DifferentiableOn.add (DifferentiableOn.add ?_ ?_) (differentiableOn_pi.mp hBd i)
      · exact ((differentiableOn_pi.mp (differentiableOn_pi.mp hAd i) 0).mul
          (differentiableOn_pi.mp hYdAnn 0))
      · exact ((differentiableOn_pi.mp (differentiableOn_pi.mp hAd i) 1).mul
          (differentiableOn_pi.mp hYdAnn 1))
    have hFzero : ∀ w ∈ Work.OdeCont.annulus (ρ / (2 * δ)) (ρ / δ), F w = 0 := by
      intro w hw
      have hwball : w ∈ Metric.ball 0 (ρ / δ) := by
        rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hw.2
      have heq : Y w = toSol g (ninth + δ * w) := hYeq hwball
      have hderiv : deriv Y w = deriv (fun w : ℂ => toSol g (ninth + δ * w)) w := by
        rw [Filter.EventuallyEq.deriv_eq
          (hYeq.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hwball))]
      have hFw : F w = deriv Y w - (fun i => ∑ j, inh_sA δ w i j * Y w j
          + inh_sB δ (fun z => -κ * psiZ y9 z) w i) := rfl
      rw [hFw, hderiv, (hY0' w hw.1 hw.2).deriv, heq, sub_self]
    -- a point of the small annulus
    have hwstar_mem : (((ρ / (2 * δ) + ρ / δ) / 2 : ℝ) : ℂ)
        ∈ Work.OdeCont.annulus (ρ / (2 * δ)) (ρ / δ) := by
      have hpos : (0 : ℝ) < (ρ / (2 * δ) + ρ / δ) / 2 := by linarith
      have hlt : (ρ / (2 * δ) + ρ / δ) / 2 < ρ / δ := by linarith
      rw [Work.OdeCont.annulus]
      exact ⟨by rw [inh_norm_ofReal_of_pos hpos]; linarith,
        by rw [inh_norm_ofReal_of_pos hpos]; exact hlt⟩
    have hwstar_ann : (((ρ / (2 * δ) + ρ / δ) / 2 : ℝ) : ℂ)
        ∈ Work.OdeCont.annulus 0 1 :=
      ⟨lt_trans hr0pos hwstar_mem.1, lt_of_lt_of_le hwstar_mem.2 hr11⟩
    have hev : F =ᶠ[𝓝 (((ρ / (2 * δ) + ρ / δ) / 2 : ℝ) : ℂ)]
        (fun _ => (0 : Fin 2 → ℂ)) :=
      Filter.eventually_of_mem
        ((Work.OdeCont.isOpen_annulus (ρ / (2 * δ)) (ρ / δ)).mem_nhds hwstar_mem)
        hFzero
    have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hFd.analyticOnNhd (Work.OdeCont.isOpen_annulus 0 1))
      (analyticOnNhd_const (v := (0 : Fin 2 → ℂ))) inh_isPreconnected_annulus_zero
      hwstar_ann hev
    intro w hw
    have h0 : F w = 0 := hEq hw
    have h1 : deriv Y w - (fun i => ∑ j, inh_sA δ w i j * Y w j
        + inh_sB δ (fun z => -κ * psiZ y9 z) w i) = 0 := h0
    exact sub_eq_zero.mp h1
  -- the main identity on the punctured ball
  have htoSol : ∀ z ∈ Metric.ball ninth δ, z ≠ ninth →
      toSol (inh_contExt δ Y) z = Y ((z - ninth) / δ) := by
    intro z hz hzne
    have hwann : (z - ninth) / δ ∈ Work.OdeCont.annulus 0 1 := by
      rw [Work.OdeCont.annulus]
      refine ⟨?_, ?_⟩
      · rw [norm_pos_iff]
        intro h
        apply hzne
        have h1 : z - ninth = 0 := by
          rw [div_eq_zero_iff] at h
          rcases h with h | h
          · exact h
          · exact absurd h hδne
        linear_combination h1
      · rw [Complex.norm_div, inh_norm_ofReal_of_pos hδpos, div_lt_one hδpos]
        rw [Metric.mem_ball, Complex.dist_eq] at hz
        exact hz
    have hwball : (z - ninth) / δ ∈ Metric.ball 0 1 := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hwann.2
    have hsysw := hsys _ hwann
    have hYw : HasDerivAt Y (fun i => ∑ j, inh_sA δ ((z - ninth) / δ) i j * Y ((z - ninth) / δ) j
        + inh_sB δ (fun z => -κ * psiZ y9 z) ((z - ninth) / δ) i) ((z - ninth) / δ) := by
      have hd : DifferentiableAt ℂ Y ((z - ninth) / δ) :=
        hYd.differentiableAt (Metric.isOpen_ball.mem_nhds hwball)
      rw [← hsysw]
      exact hd.hasDerivAt
    have h1 : deriv (inh_contExt δ Y) z = Y ((z - ninth) / δ) 1 := by
      have hEq : inh_contExt δ Y = (fun w : ℂ => Y w 0) ∘ (fun z' : ℂ => (z' - ninth) / δ) := by
        funext z'; rfl
      have hchain : deriv (inh_contExt δ Y) z
          = deriv (fun w : ℂ => Y w 0) ((z - ninth) / δ)
            * deriv (fun z' : ℂ => (z' - ninth) / δ) z := by
        rw [hEq]
        exact deriv_comp z
          ((differentiableAt_pi.mp (hYd.differentiableAt (Metric.isOpen_ball.mem_nhds hwball))) 0)
          (by fun_prop)
      rw [hchain]
      have haff : deriv (fun z' : ℂ => (z' - ninth) / δ) z = 1 / δ :=
        (((hasDerivAt_id z).sub_const ninth).div_const ((δ : ℂ))).deriv
      rw [haff]
      have hcomp0 : deriv (fun w : ℂ => Y w 0) ((z - ninth) / δ) = deriv Y ((z - ninth) / δ) 0 := by
        rw [deriv_pi (fun i => (differentiableAt_pi.mp
          (hYd.differentiableAt (Metric.isOpen_ball.mem_nhds hwball))) i)]
      rw [hcomp0, hsysw]
      have hbeta : (fun i => ∑ j, inh_sA δ ((z - ninth) / δ) i j * Y ((z - ninth) / δ) j
            + inh_sB δ (fun z => -κ * psiZ y9 z) ((z - ninth) / δ) i) 0
          = ∑ j, inh_sA δ ((z - ninth) / δ) 0 j * Y ((z - ninth) / δ) j
            + inh_sB δ (fun z => -κ * psiZ y9 z) ((z - ninth) / δ) 0 := rfl
      rw [hbeta, Fin.sum_univ_two, inh_sA_apply_zero_zero, inh_sA_apply_zero_one, inh_sB_apply_zero]
      field_simp
      ring
    have htoS0 : toSol (inh_contExt δ Y) z 0 = Y ((z - ninth) / δ) 0 := by
      show inh_contExt δ Y z = Y ((z - ninth) / δ) 0
      rfl
    have htoS1 : toSol (inh_contExt δ Y) z 1 = Y ((z - ninth) / δ) 1 := by
      show deriv (inh_contExt δ Y) z = Y ((z - ninth) / δ) 1
      exact h1
    funext i
    fin_cases i
    · exact htoS0
    · exact htoS1
  -- assemble
  refine ⟨inh_contExt δ Y, ?_, ?_, ?_⟩
  · -- holomorphy of `G`
    have hmaps : Set.MapsTo (fun z : ℂ => (z - ninth) / δ) (Metric.ball ninth δ)
        (Metric.ball 0 1) := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_div,
        inh_norm_ofReal_of_pos hδpos, div_lt_one hδpos]
      exact hz
    have hfun : (fun w : ℂ => Y w 0) ∘ (fun z : ℂ => (z - ninth) / δ) = inh_contExt δ Y := by
      funext z; rfl
    rw [← hfun]
    exact (differentiableOn_pi.mp hYd 0).comp (by fun_prop) hmaps
  · -- agreement with `g`
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hwball : (z - ninth) / δ ∈ Metric.ball 0 (ρ / δ) := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_div,
        inh_norm_ofReal_of_pos hδpos]
      exact div_lt_div_of_pos_right hz hδpos
    have h1 : Y ((z - ninth) / δ) = toSol g (ninth + δ * ((z - ninth) / δ)) := hYeq hwball
    have h2 : ninth + δ * ((z - ninth) / δ) = z := by
      field_simp
      ring
    simp only [inh_contExt]
    rw [h1]
    simp only [toSol, Matrix.cons_val_zero]
    rw [h2]
  · -- the differential equation
    intro z hz hzne
    set w : ℂ := (z - ninth) / δ with hwdef
    have hzball : z ∈ Metric.ball ninth δ := hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hwball : w ∈ Metric.ball 0 1 := by
      rw [hwdef]
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_div,
        inh_norm_ofReal_of_pos hδpos, div_lt_one hδpos]
      exact hz
    have hwne : w ≠ 0 := by
      rw [hwdef]
      intro h
      apply hzne
      have h1 : z - ninth = 0 := by
        rw [div_eq_zero_iff] at h
        rcases h with h | h
        · exact h
        · exact absurd h hδne
      linear_combination h1
    have hwann : w ∈ Work.OdeCont.annulus 0 1 := by
      rw [Work.OdeCont.annulus]
      refine ⟨norm_pos_iff.mpr hwne, ?_⟩
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hwball
      exact hwball
    have hsysw := hsys w hwann
    have hYw : HasDerivAt Y (fun i => ∑ j, inh_sA δ w i j * Y w j
        + inh_sB δ (fun z => -κ * psiZ y9 z) w i) w := by
      have hd : DifferentiableAt ℂ Y w := hYd.differentiableAt (Metric.isOpen_ball.mem_nhds hwball)
      rw [← hsysw]
      exact hd.hasDerivAt
    -- transport to `toSol (inh_contExt δ Y)` at `z`
    have hφ : HasDerivAt (fun z' : ℂ => (z' - ninth) / δ) (1 / δ) z := by
      simpa using ((hasDerivAt_id z).sub_const ninth).div_const ((δ : ℂ))
    have hcomp := hYw.scomp z hφ
    have hev : toSol (inh_contExt δ Y) =ᶠ[𝓝 z] (fun z' : ℂ => Y ((z' - ninth) / δ)) := by
      filter_upwards [(Metric.isOpen_ball).mem_nhds hzball, isOpen_ne.mem_nhds hzne] with z' hz' hz'ne
      exact htoSol z' hz' hz'ne
    have hderiv : HasDerivAt (toSol (inh_contExt δ Y)) ((1 / δ : ℂ) • (fun i =>
        ∑ j, inh_sA δ w i j * Y w j + inh_sB δ (fun z => -κ * psiZ y9 z) w i)) z :=
      hcomp.congr_of_eventuallyEq hev
    have hzw : ninth + δ * w = z := by
      rw [hwdef]; field_simp; ring
    have htoSolz : toSol (inh_contExt δ Y) z = Y w := by
      rw [htoSol z hzball hzne, hwdef]
    have hval : ((1 / δ : ℂ) • (fun i =>
          ∑ j, inh_sA δ w i j * Y w j + inh_sB δ (fun z => -κ * psiZ y9 z) w i))
        = fun i => ∑ j, sysA z i j * toSol (inh_contExt δ Y) z j
            + sysb (fun z => -κ * psiZ y9 z) z i := by
      rw [inh_smul_sys, smul_smul, show (1 / δ : ℂ) * (δ : ℂ) = 1 by field_simp, one_smul,
        htoSolz, hzw]
    rw [hval] at hderiv
    have hP : PZ z ≠ 0 := by
      refine inh_PZ_ne_zero_of_ne hzne ?_
      rw [Complex.dist_eq]
      exact lt_of_lt_of_le hz (by linarith [hδ20])
    have hderivG : DifferentiableAt ℂ (deriv (inh_contExt δ Y)) z := by
      have hmaps : Set.MapsTo (fun z : ℂ => (z - ninth) / δ) (Metric.ball ninth δ)
          (Metric.ball 0 1) := by
        intro z hz
        rw [Metric.mem_ball, Complex.dist_eq] at hz
        rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_div,
          inh_norm_ofReal_of_pos hδpos, div_lt_one hδpos]
        exact hz
      have hfun : (fun w : ℂ => Y w 0) ∘ (fun z : ℂ => (z - ninth) / δ) = inh_contExt δ Y := by
        funext z; rfl
      have hGd : DifferentiableOn ℂ (inh_contExt δ Y) (Metric.ball ninth δ) := by
        rw [← hfun]
        exact (differentiableOn_pi.mp hYd 0).comp (by fun_prop) hmaps
      exact (hGd.deriv isOpen_ball).differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
    exact LZ_of_hasDerivAt_toSol hderiv hderivG hP

end

end Work.A14D
