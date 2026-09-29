import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.H_conv_alt
import Submission.Work.A14D.H_local_at_one
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.uh_not_holo_at_ninth
import Submission.Work.A14D.hol_sol_at_ninth_smul
import Submission.Work.A14D.D_local_at_one
import Submission.Work.A14D.hol_sol_at_one_smul
import Submission.Work.A14D.D_zero_of_c_eq_zero
import Submission.Work.A14D.kappaL_conj_symm
import Submission.Work.A14D.kappaU_sub_kappaL
import Submission.Work.C17g.linear_ode_convex

namespace Work.A14D

/-
STATUS (area A14D, `Work.A14D.kappaU_zero_imp_D_zero`) — corrected picture.

The proposition is TRUE and is reduced here to two analytic inputs about the log coefficients
`κU`, `κL` of the jump `D = HU - HL` at `1/9`:

* `Work.A14D.kappaL_conj_symm` : `κL * y9 (1/9) = -conj (κU * y9 (1/9))`
  (the jump is anti-real: `HL = conj ∘ HU ∘ conj`, so `R D = -D`).
* `Work.A14D.kappaU_sub_kappaL` (the design's identity `(K)`):
  `κU - κL = -(π² c / 2) · λ`, where `λ ≠ 0` is the log coefficient of `uh` on the lens
  `ball (1/9) δ ∩ ball 1 (8/9)` (this identity comes from the *local* structure of `D` at
  `z = 1`, `Work.A14D.D_local_at_one`: `D = -2πi·e1 + (π i c/4)·uh·log (z-1)` there, so it is
  invisible to any argument which only uses `D` as a solution on the slit plane `Om1`).

Then `κU = 0` forces `κL = 0`, hence `0 = κU - κL = -(π² c / 2)·λ`, hence `c = 0`, and
`Work.A14D.D_zero_of_c_eq_zero` (proved, sorry-free) gives `D = 0` on `Om1`.
The combination is `kappaU_zero_imp_D_zero_of_symm_ident` below.

WARNING (recorded because two earlier agents got it wrong): `κU = κL` is **FALSE** in general.
The identity theorem cannot bridge the two half-discs of `ball (1/9) δ`, because every real point
of that ball lies on the slit `(-∞,1]`; numerically (continuation of the ODE to precision ~1e-14,
see `Submission/Work/A14D/_num/README.md`)
  rhs `-2` (c = 0):        κU = κL = -2πi,
  rhs `-4/(1-x)` (c = -4): κU = -16.32419427810799, κL = +16.32419427810799,
and `-(π²·(-4)/2)·λ = -32.64838855621598 = κU - κL` with `λ = -1.65398668626537` computed
independently from the continuation of `uh`.  So the design's identity `(K)` and the whole A14D
route are sound.

What is proved in this file (sorry-free):
* `lens`, `lens_subset_ball`, `lens_subset_ball1`, `isOpen_lens`, `convex_lens`, `lens_subset_slit`;
* `uh_logCoeff_lens` : `uh` has a non-zero log coefficient on the lens;
* `kappaU_zero_halfU` : `κU = 0` forces `D = α·y9` on `halfU δ`;
* `isOpen_halfL`, `convex_halfL`, `halfL_subset_slitDisk`, `halfL_subset_Om1`;
* `kappaU_zero_imp_D_zero_of_symm_ident` : the assembly described above.
The main theorem `kappaU_zero_imp_D_zero` is the instantiation of that assembly with the two
cited inputs (delegated) plus `logCoeff_exists` on `halfL δ`.
-/

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-- The lens `ball (1/9) δ ∩ ball 1 (8/9)`: the region on which `u_h` is (manifestly) holomorphic
and which accumulates at `1/9`. -/
def lens (δ : ℝ) : Set ℂ := Metric.ball ninth δ ∩ Metric.ball 1 (8 / 9)

lemma lens_subset_ball (δ : ℝ) : lens δ ⊆ Metric.ball ninth δ := Set.inter_subset_left

lemma lens_subset_ball1 (δ : ℝ) : lens δ ⊆ Metric.ball 1 (8 / 9) := Set.inter_subset_right

lemma isOpen_lens (δ : ℝ) : IsOpen (lens δ) :=
  Metric.isOpen_ball.inter Metric.isOpen_ball

lemma convex_lens (δ : ℝ) : Convex ℝ (lens δ) :=
  (convex_ball ninth δ).inter (convex_ball (1 : ℂ) (8 / 9))

lemma lens_subset_slit {δ : ℝ} :
    lens δ ⊆ Metric.ball ninth δ ∩ {z : ℂ | z.im ≠ 0 ∨ ninth.re < z.re} := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨h1, ?_⟩
  by_cases him : z.im = 0
  · right
    rw [Metric.mem_ball, Complex.dist_eq] at h2
    have h2' : ‖z - 1‖ < 8 / 9 := h2
    have h3 : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm (z - 1)
    have h3' : |(z - 1).re| < 8 / 9 := lt_of_le_of_lt h3 h2'
    have h4 : (z - 1).re = z.re - 1 := Complex.sub_re z 1
    rw [h4] at h3'
    have h5 : -(8 / 9 : ℝ) < z.re - 1 := (abs_lt.mp h3').1
    have h9 : ninth.re = 1 / 9 := by simp [ninth]
    have : (1 / 9 : ℝ) < z.re := by linarith
    simpa [h9] using this
  · exact Or.inl him

/-- The holomorphic solution `u_h` of `LZ = 0` at `z = 1` has a non-zero log coefficient at `1/9`,
witnessed on the lens `ball (1/9) δ ∩ ball 1 (8/9)`. -/
theorem uh_logCoeff_lens {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) :
    ∃ lam : ℂ, LogCoeff y9 δ (lens δ) uh lam ∧ lam ≠ 0 := by
  have hYc : Y9 y9 δ := hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  have hud : DifferentiableOn ℂ uh (lens δ) :=
    uh_ode.1.mono (fun z hz => lens_subset_ball1 δ hz)
  have hode : ∀ z ∈ lens δ, LZ uh z = 0 :=
    fun z hz => uh_ode.2.2 z (lens_subset_ball1 δ hz)
  obtain ⟨lam, hlam⟩ :=
    logCoeff_exists hYc (lens δ) (isOpen_lens δ) (convex_lens δ) (lens_subset_slit (δ := δ))
      uh hud hode
  refine ⟨lam, hlam, ?_⟩
  intro hzero
  subst hzero
  obtain ⟨h, hhd, hheq⟩ := hlam
  refine uh_not_holo_at_ninth ⟨h, δ, hδpos, hhd, ?_⟩
  intro z hz
  have hthis := hheq z hz
  simp only [zero_mul, zero_add] at hthis
  exact hthis.symm

/-- If the log coefficient of `D` at `1/9` from above vanishes, then `D` agrees with a multiple of
`y9` on the upper half disc. -/
theorem kappaU_zero_halfU {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (κU : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hκ : κU = 0) :
    ∃ α : ℂ, ∀ z ∈ halfU δ, D z = α * y9 z := by
  have hYc : Y9 y9 δ := hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  obtain ⟨hh, hhhd, hheq⟩ := hU
  have hDh : ∀ z ∈ halfU δ, D z = hh z := by
    intro z hz
    have h1 := hheq z hz
    rw [hκ] at h1
    simpa using h1
  have hhalf_sub_Om1 : halfU δ ⊆ Om1 := by
    intro z hz
    exact Or.inl (ne_of_gt hz.2)
  have hLZhalf : ∀ z ∈ halfU δ, LZ hh z = 0 := by
    intro z hz
    have h1 : LZ hh z = LZ D z :=
      LZ_congr_eqOn (isOpen_halfUp δ) (hhhd.mono (fun w hw => hw.1))
        (hD.mono hhalf_sub_Om1) (fun w hw => (hDh w hw).symm) hz
    rw [h1]
    exact hDL z (hhalf_sub_Om1 hz)
  have hFd : DifferentiableOn ℂ (fun w => LZ hh w) (ball ninth δ) := by
    have hd1 : DifferentiableOn ℂ (deriv hh) (ball ninth δ) := hhhd.deriv Metric.isOpen_ball
    have hd2 : DifferentiableOn ℂ (deriv (deriv hh)) (ball ninth δ) := hd1.deriv Metric.isOpen_ball
    have he : (fun w => LZ hh w)
        = fun w => PZ w * deriv (deriv hh) w + PZ' w * deriv hh w + RZ w * hh w := by
      funext w; rw [LZ_def]
    rw [he]
    have hPZ : DifferentiableOn ℂ PZ (ball ninth δ) := by unfold PZ; fun_prop
    have hPZ' : DifferentiableOn ℂ PZ' (ball ninth δ) := by unfold PZ'; fun_prop
    have hRZ : DifferentiableOn ℂ RZ (ball ninth δ) := by unfold RZ; fun_prop
    exact ((hPZ.mul hd2).add (hPZ'.mul hd1)).add (hRZ.mul hhhd)
  have hLZball : ∀ z ∈ ball ninth δ, LZ hh z = 0 := by
    intro z hz
    have hAn : AnalyticOnNhd ℂ (fun w => LZ hh w) (ball ninth δ) :=
      hFd.analyticOnNhd Metric.isOpen_ball
    obtain ⟨z₀, hz₀⟩ := halfUp_nonempty hδpos
    have hz₀' : z₀ ∈ ball ninth δ := hz₀.1
    have hev : (fun w => LZ hh w) =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [(isOpen_halfUp δ).mem_nhds hz₀] with w hw
      exact hLZhalf w hw
    exact hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ((convex_ball ninth δ).isPreconnected) hz₀' hev hz
  obtain ⟨α, hα⟩ := hol_sol_at_ninth_smul hYc hhhd hLZball
  refine ⟨α, fun z hz => ?_⟩
  rw [hDh z hz, hα z (Set.inter_subset_left hz)]


/-! ## Assembly

The two remaining analytic inputs are the symmetry of the two log coefficients
(`Work.A14D.kappaL_conj_symm`) and the design identity (`Work.A14D.kappaU_sub_kappaL`): -/

lemma convex_halfL (δ : ℝ) : Convex ℝ (halfL δ) := by
  have h : Convex ℝ (Set.Iio (0 : ℝ)) := convex_Iio 0
  have him : {z : ℂ | z.im < 0} = Complex.im ⁻¹' (Set.Iio (0 : ℝ)) := rfl
  rw [halfL, him]
  exact (convex_ball ninth δ).inter (h.linear_preimage { toFun := fun z : ℂ => z.im, map_add' := by intro x y; simp [Complex.add_im], map_smul' := by intro c x; simp })

lemma halfL_subset_slitDisk (δ : ℝ) : halfL δ ⊆ slitDisk δ :=
  fun z hz => ⟨hz.1, Or.inl (ne_of_lt hz.2)⟩

/-- If the two log coefficients of the jump satisfy the conjugation symmetry
(`κL * y9 (1/9) = -conj (κU * y9 (1/9))`) and the design identity
(`κU - κL = -(π²c/2)·λ` with `λ ≠ 0`), then `κU = 0` forces `c = 0`, hence `D = 0` on `Om1`
by the proved `c = 0` case `Work.A14D.D_zero_of_c_eq_zero`. -/
theorem kappaU_zero_imp_D_zero_of_symm_ident (a b c : ℤ)
    (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hκ : κU = 0)
    (hSym : κL * y9 ninth = -(star (κU * y9 ninth)))
    (hIdent : ∃ lam : ℂ, lam ≠ 0 ∧ LogCoeff y9 δ (lens δ) uh lam ∧
      κU - κL = -(Real.pi ^ 2 * (c : ℂ) / 2) * lam) :
    ∀ z ∈ Om1, D z = 0 := by
  have hYc : Y9 y9 δ := hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  -- `κL = 0`
  have hκL : κL = 0 := by
    have h1 : κL * y9 ninth = 0 := by
      rw [hSym, hκ]
      simp
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hy9ne
  -- `c = 0` from the design identity
  have hc : c = 0 := by
    obtain ⟨lam, hlam_ne, hcert, hid⟩ := hIdent
    have h2 : (Real.pi ^ 2 * (c : ℂ) / 2) * lam = 0 := by
      have h3 : (-(Real.pi ^ 2 * (c : ℂ) / 2)) * lam = 0 := by
        rw [← hid, hκ, hκL, sub_zero]
      rw [neg_mul] at h3
      exact neg_eq_zero.mp h3
    have h4 : Real.pi ^ 2 * (c : ℂ) / 2 = 0 := (mul_eq_zero.mp h2).resolve_right hlam_ne
    have h5 : Real.pi ^ 2 * (c : ℂ) = 0 := by
      rcases (div_eq_zero_iff.mp h4) with h6 | h6
      · exact h6
      · exact absurd h6 (by norm_num)
    have hp : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have h6 : (c : ℂ) = 0 := (mul_eq_zero.mp h5).resolve_left (pow_ne_zero 2 hp)
    exact_mod_cast h6
  exact D_zero_of_c_eq_zero a b c h hb hc HU HL hHU hHL y9 δ hYc D hD hDL hDj κU hU hκ

/-- **The requested lemma.**  `κU = 0` forces the jump `D` to vanish on the slit plane.

Proof: `logCoeff_exists` supplies the lower certificate `κL`; the conjugation symmetry
`Work.A14D.kappaL_conj_symm` gives `κL * y9 (1/9) = 0`, so `κL = 0`; the design identity
`Work.A14D.kappaU_sub_kappaL` gives `0 = κU - κL = -(π² c / 2)·λ` with `λ ≠ 0`, so `c = 0`;
then `Work.A14D.D_zero_of_c_eq_zero` (the already proved `c = 0` case) gives `D = 0`. -/
theorem kappaU_zero_imp_D_zero (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hκ : κU = 0) :
    ∀ z ∈ Om1, D z = 0 := by
  have hYc : Y9 y9 δ := hY
  -- the log coefficient from below
  obtain ⟨κL, hL⟩ := logCoeff_exists hYc (halfL δ) (isOpen_halfL δ) (convex_halfL δ)
    (halfL_subset_slitDisk δ) D (hD.mono (halfL_subset_Om1 δ))
    (fun z hz => hDL z (halfL_subset_Om1 δ hz))
  exact kappaU_zero_imp_D_zero_of_symm_ident a b c h hb HU HL hHU hHL y9 δ hYc D hD hDL hDj
    κU κL hU hκ
    (A14D.kappaL_conj_symm a b c h HU HL hHU hHL y9 δ hYc D hD hDL hDj κU κL hU hL)
    (A14D.kappaU_sub_kappaL a b c h HU HL hHU hHL y9 δ hYc D hD hDL hDj κU κL hU hL)

end

end Work.A14D
