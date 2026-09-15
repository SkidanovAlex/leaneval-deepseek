import Submission.FUP.BoxPorosity
import Submission.FUP.Damping
import Submission.Commons.Analysis.Fourier.fourier_comp_smul
import Submission.Commons.Analysis.Fourier.exists_schwartz_nonneg_compactSupport_fourier

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 0: the cut-off of the induction on scales

`Submission/FUP/Spec.lean` records Han–Schlag's Theorem 5.1 (`Spec.han_schlag_statement`), the
only literature input left in the whole chain for Cohen's Theorem 1.1
(see `Submission/FUP/ROADMAP.md`, session 47).  This module starts the formalisation of its proof,
which is the soft part of Han–Schlag's paper (`Anal. PDE` **13** (2020), §5): an *induction on
scales* in which at each dyadic scale the mass of `f` in the porous set `X` is reduced by a fixed
factor, the gain coming from the single-scale localisation estimate (their Corollary 4.2).

The present module contains only the cut-off layer of that argument:

* `HasFupCutoff d` — the datum of the induction: a nonnegative `C^∞` function `φ` on `ℝ^d` with
  `∫φ = 1` and compactly supported Fourier transform (Han–Schlag's "nonnegative Schwarz function
  `φ` with `supp φ̂ ⊆ [-1,1]^d` and `φ̂(0) = 1`").  Its existence is a `Prop` here because the
  construction (take `φ = |𝓕χ|²` for a `C_c^∞` bump `χ`, normalised) is not needed until later.
* `scaleFun φ c x = c^d φ (c x)`, the `L¹`-normalised dilate: `∫ scaleFun φ c = ∫φ = 1` and
  `scaleFun φ c ≥ 0`.
* `thicken S r = {y | ∃ s ∈ S, dist y s ≤ r}`, Han–Schlag's `S + [-r,r]^d`.
* `fupCutoff_lower` — for `x ∈ S`, the mass of the dilated cut-off in the `r`-neighbourhood of `S`
  around `x` is at least `1 - ∫_{‖z‖ ≥ cr} φ` (this is `Ψ_n ≥ (1 - C_φ/L^{T-1}) 1_X`),
* `fupCutoff_upper` — if every point of `S` is at distance `≥ ρ` from `x` and `r < ρ`, then the
  mass in that neighbourhood is at most `∫_{‖z‖ ≥ ρ - r} φ` (this is `Ψ_n ≤ c_φ/L^{T-1}` on the
  holes).
-/

namespace Submission.FUP

/-- The `L¹`-normalised `c`-dilate of a cut-off: `scaleFun φ c x = c^d φ (c x)`. -/
noncomputable def scaleFun (φ : ℝᵈ → ℝ) (c : ℝ) : ℝᵈ → ℝ := fun x => c ^ d * φ (c • x)

/-- The closed `r`-neighbourhood of a set (Han–Schlag's `S + [-r,r]^d`). -/
def thicken (S : Set ℝᵈ) (r : ℝ) : Set ℝᵈ := {y | ∃ s ∈ S, dist y s ≤ r}

/-! ## The cut-off datum -/

/-- The cut-off datum of Han–Schlag's §5 induction: a Schwartz function `φ` on `ℝ^d`, real-valued
and nonnegative, with `∫φ = 1`, whose Fourier transform vanishes outside the ball of radius
`radius`.  (Han–Schlag ask for `φ` Schwarz with `supp φ̂ ⊆ [-1,1]^d` and `φ̂(0) = 1`; only the
support radius and the vanishing of the tail `∫_{‖z‖ ≥ R} φ → 0` are used below.) -/
structure FupCutoff (d : ℕ) where
  fn : EuclideanSpace ℝ (Fin d) → ℝ
  continuous : Continuous fn
  integrable : Integrable fn
  nonneg : ∀ x, 0 ≤ fn x
  integral_one : ∫ x, fn x = 1
  radius : ℝ
  radius_pos : 0 < radius
  support : ∀ (c : ℝ), 0 < c → ∀ ξ : EuclideanSpace ℝ (Fin d),
    c * radius < ‖ξ‖ → FourierTransform.fourier
      (fun x : EuclideanSpace ℝ (Fin d) => (scaleFun fn c x : ℂ)) ξ = 0

/-- The set of cut-offs is nonempty. -/
def HasFupCutoff (d : ℕ) : Prop := Nonempty (FupCutoff d)

/-- **The cut-off exists** (this is the `φ` of Han–Schlag's §5): a nonnegative continuous
integrable function with `∫φ = 1` and compactly supported Fourier transform, whose every
`L¹`-normalised dilate `scaleFun φ c` has Fourier transform supported in the ball of radius
`c * radius`. -/
theorem hasFupCutoff (d : ℕ) : HasFupCutoff d := by
  obtain ⟨φ, him, hre, hsupp, hint⟩ :=
    Commons.Analysis.Fourier.exists_schwartz_nonneg_compactSupport_fourier d
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hre_apply : ∀ x, ((φ x).re : ℂ) = φ x := fun x =>
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact (him x).symm)
  refine ⟨{ fn := fun x => (φ x).re,
            continuous := Complex.continuous_re.comp φ.continuous,
            integrable := φ.integrable.re,
            nonneg := hre,
            integral_one := ?_,
            radius := max R 1,
            radius_pos := lt_of_lt_of_le one_pos (le_max_right _ _),
            support := fun c hc ξ hξ => ?_ }⟩
  · have h : ∫ x : EuclideanSpace ℝ (Fin d), ((φ x).re : ℂ) = (((∫ x, (φ x).re : ℝ)) : ℂ) :=
      integral_ofReal
    rw [funext hre_apply, hint] at h
    exact Complex.ofReal_inj.mp h.symm
  · have hfun : (fun x : EuclideanSpace ℝ (Fin d) =>
          (scaleFun (fun x => (φ x).re) c x : ℂ))
        = fun x : EuclideanSpace ℝ (Fin d) => ((c ^ d : ℝ) : ℂ) * φ (c • x) := by
      funext x
      rw [scaleFun, Complex.ofReal_mul, hre_apply]
    have hsmul : ∀ ξ : EuclideanSpace ℝ (Fin d),
        FourierTransform.fourier
            (fun x : EuclideanSpace ℝ (Fin d) => ((c ^ d : ℝ) : ℂ) * φ (c • x)) ξ
          = ((c ^ d : ℝ) : ℂ) *
              FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin d) => φ (c • x)) ξ := by
      intro ξ
      rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Circle.smul_def]
      ring
    have hnorm : max R 1 < ‖c⁻¹ • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      have h : max R 1 < ‖ξ‖ / c := (lt_div_iff₀ hc).mpr (by rwa [mul_comm] at hξ)
      rwa [div_eq_inv_mul] at h
    have hcoe : ((c ^ d : ℝ) : ℂ) * (((c ^ d)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero d hc.ne'), Complex.ofReal_one]
    rw [hfun, hsmul ξ,
      congrFun (Commons.Analysis.Fourier.fourier_comp_smul (ψ := φ) hc) ξ]
    simp only [smul_eq_mul]
    rw [← mul_assoc, hcoe, one_mul]
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    exact absurd h1 (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hnorm))

namespace FupCutoff

variable {d : ℕ} (Φ : FupCutoff d)

/-- The (real-valued) function underlying the cut-off. -/
noncomputable def reFun : EuclideanSpace ℝ (Fin d) → ℝ := Φ.fn

lemma reFun_apply (x : EuclideanSpace ℝ (Fin d)) : Φ.reFun x = Φ.fn x := rfl

lemma reFun_nonneg : ∀ x, 0 ≤ Φ.reFun x := Φ.nonneg

lemma continuous_reFun : Continuous Φ.reFun := Φ.continuous

lemma integrable_reFun : Integrable Φ.reFun := Φ.integrable

lemma integral_reFun : ∫ x, Φ.reFun x = 1 := Φ.integral_one

/-- The Fourier transform of a dilated cut-off vanishes outside the ball of radius
`c * radius`. -/
lemma dilate_fourier_eq_zero {c : ℝ} (hc : 0 < c) {ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : c * Φ.radius < ‖ξ‖) :
    FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin d) => (scaleFun Φ.reFun c x : ℂ)) ξ
      = 0 :=
  Φ.support c hc ξ hξ

end FupCutoff

lemma mem_thicken {S : Set ℝᵈ} {r : ℝ} {y : ℝᵈ} :
    y ∈ thicken S r ↔ ∃ s ∈ S, dist y s ≤ r := Iff.rfl

lemma thicken_mono {S T : Set ℝᵈ} (h : S ⊆ T) (r : ℝ) : thicken S r ⊆ thicken T r :=
  fun _ ⟨s, hs, hd⟩ => ⟨s, h hs, hd⟩

lemma self_subset_thicken (S : Set ℝᵈ) {r : ℝ} (hr : 0 ≤ r) : S ⊆ thicken S r :=
  fun s hs => ⟨s, hs, by simpa using hr⟩

lemma thicken_eq_of_le {S : Set ℝᵈ} {r r' : ℝ} (h : r ≤ r') : thicken S r ⊆ thicken S r' :=
  fun _ ⟨s, hs, hd⟩ => ⟨s, hs, le_trans hd h⟩

/-! ## Elementary properties of the dilated cut-off -/

lemma scaleFun_nonneg {φ : ℝᵈ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {c : ℝ} (hc : 0 ≤ c) :
    ∀ x, 0 ≤ scaleFun φ c x :=
  fun x => mul_nonneg (pow_nonneg hc d) (hφ _)

lemma measurable_scaleFun {φ : ℝᵈ → ℝ} (hφc : Continuous φ) (c : ℝ) :
    Measurable (scaleFun φ c) := by
  refine Measurable.mul measurable_const ?_
  exact (hφc.comp (continuous_const_smul c)).measurable

lemma integrable_scaleFun {φ : ℝᵈ → ℝ} (hφ : Integrable φ) {c : ℝ} (hc : 0 < c) :
    Integrable (scaleFun φ c) := by
  have h1 : Integrable (fun x : ℝᵈ => φ (c • x)) := hφ.comp_smul hc.ne'
  exact h1.const_mul (c ^ d)

lemma integral_scaleFun {φ : ℝᵈ → ℝ} {c : ℝ} (hc : 0 < c) :
    ∫ x, scaleFun φ c x = ∫ x, φ x := by
  have h := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure ℝᵈ)) φ c (hR := hc.le)
  rw [finrank_euclideanSpace, Fintype.card_fin] at h
  change ∫ x : ℝᵈ, c ^ d * φ (c • x) = ∫ x, φ x
  rw [integral_const_mul, h, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero d hc.ne'), one_mul]

/-- The dilated cut-off has mass one. -/
lemma scaleFun_integral_eq_one {φ : ℝᵈ → ℝ} (hφ1 : ∫ x, φ x = 1) {c : ℝ} (hc : 0 < c) :
    ∫ x, scaleFun φ c x = 1 := by
  rw [integral_scaleFun hc, hφ1]

/-! ## The two estimates on the dilated cut-off

These are the two pointwise bounds used in the induction on scales (Han–Schlag, proof of
Theorem 5.1): with `S` the union of the cubes of the `n`-th generation meeting `X`, the cut-off
`Ψ_n = scaleFun φ (L^{-(n+T)}) * 1_{S*}` is `≥ 1 - C/L^{T-1}` on `X` and `≤ C/L^{T-1}` on the
holes. -/

/-- **Lower bound.**  If `x ∈ S`, then the `L¹`-normalised dilate of `φ` puts all of its mass
except the tail `∫_{‖z‖ ≥ cr} φ` inside the `r`-neighbourhood of `S` around `x`. -/
theorem fupCutoff_lower {φ : ℝᵈ → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (hφi : Integrable φ)
    (hφ1 : ∫ x, φ x = 1) {c r : ℝ} (hc : 0 < c) {S : Set ℝᵈ} {x : ℝᵈ}
    (hx : x ∈ S) :
    1 - ∫ z in {z : ℝᵈ | c * r < ‖z‖}, φ z ≤
      ∫ z in {z : ℝᵈ | x - z ∈ thicken S r}, scaleFun φ c z := by
  have hfnn : ∀ z : ℝᵈ, 0 ≤ scaleFun φ c z := scaleFun_nonneg hφ0 hc.le
  have hfi : Integrable (scaleFun φ c) := integrable_scaleFun hφi hc
  -- the ball of radius `r` is contained in the set where the cut-off sits in `S`'s neighbourhood
  have hsub : {z : ℝᵈ | ‖z‖ ≤ r} ⊆ {z : ℝᵈ | x - z ∈ thicken S r} := by
    intro z hz
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm]
    have h1 : x - z - x = -z := by abel
    rw [h1, norm_neg]
    simpa using hz
  have hmono : ∫ z in {z : ℝᵈ | ‖z‖ ≤ r}, scaleFun φ c z
      ≤ ∫ z in {z : ℝᵈ | x - z ∈ thicken S r}, scaleFun φ c z :=
    setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hfnn)
      (Filter.Eventually.of_forall fun z hz => hsub hz)
  -- the mass of the dilate in the ball, by the change of variables `z ↦ c z`
  have hchange : ∫ z in {z : ℝᵈ | ‖z‖ ≤ r}, scaleFun φ c z
      = ∫ w in {w : ℝᵈ | ‖w‖ ≤ c * r}, φ w := by
    have hcv := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure ℝᵈ)) φ
      {z : ℝᵈ | ‖z‖ ≤ r} hc
    rw [finrank_euclideanSpace, Fintype.card_fin] at hcv
    have hset : c • {z : ℝᵈ | ‖z‖ ≤ r} = {w : ℝᵈ | ‖w‖ ≤ c * r} := by
      ext w
      simp only [Set.mem_smul_set, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_left hz hc.le
      · intro hw
        exact ⟨c⁻¹ • w, by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ hc]
          exact hw, by rw [smul_inv_smul₀ hc.ne']⟩
    rw [hset] at hcv
    change ∫ z in {z : ℝᵈ | ‖z‖ ≤ r}, c ^ d * φ (c • z) = _
    rw [integral_const_mul, hcv]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hc.ne'), one_mul]
  have htail : ∫ w in {w : ℝᵈ | ‖w‖ ≤ c * r}, φ w = 1 - ∫ z in {z : ℝᵈ | c * r < ‖z‖}, φ z := by
    have hms : MeasurableSet {w : ℝᵈ | ‖w‖ ≤ c * r} :=
      (isClosed_le continuous_norm continuous_const).measurableSet
    have hadd := integral_add_compl hms hφi (μ := (volume : Measure ℝᵈ))
    have hcompl : {w : ℝᵈ | ‖w‖ ≤ c * r}ᶜ = {z : ℝᵈ | c * r < ‖z‖} := by
      ext z; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hcompl] at hadd
    linarith [hadd, hφ1]
  calc 1 - ∫ z in {z : ℝᵈ | c * r < ‖z‖}, φ z
      = ∫ z in {z : ℝᵈ | ‖z‖ ≤ r}, scaleFun φ c z := by rw [hchange, htail]
    _ ≤ ∫ z in {z : ℝᵈ | x - z ∈ thicken S r}, scaleFun φ c z := hmono

/-- **Upper bound.**  If every point of `S` is at distance `≥ ρ` from `x` (with `r < ρ`), then the
mass of the dilated cut-off in the `r`-neighbourhood of `S` around `x` is at most the tail
`∫_{‖w‖ ≥ c(ρ-r)} φ`. -/
theorem fupCutoff_upper {φ : ℝᵈ → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (hφi : Integrable φ)
    {c r ρ : ℝ} (hc : 0 < c) {S : Set ℝᵈ} {x : ℝᵈ}
    (hsep : ∀ s ∈ S, ρ ≤ dist x s) :
    ∫ z in {z : ℝᵈ | x - z ∈ thicken S r}, scaleFun φ c z ≤
      ∫ w in {w : ℝᵈ | c * (ρ - r) ≤ ‖w‖}, φ w := by
  have hfnn : ∀ z : ℝᵈ, 0 ≤ scaleFun φ c z := scaleFun_nonneg hφ0 hc.le
  have hfi : Integrable (scaleFun φ c) := integrable_scaleFun hφi hc
  have hsub : {z : ℝᵈ | x - z ∈ thicken S r} ⊆ {z : ℝᵈ | ρ - r ≤ ‖z‖} := by
    rintro z ⟨s, hs, hd⟩
    have h1 : dist x s ≤ dist x (x - z) + dist (x - z) s := dist_triangle _ _ _
    have h3 : dist x (x - z) = ‖z‖ := by
      rw [dist_eq_norm]
      have h4 : x - (x - z) = z := by abel
      rw [h4]
    rw [h3] at h1
    show ρ - r ≤ ‖z‖
    linarith [hsep s hs]
  have hmono : ∫ z in {z : ℝᵈ | x - z ∈ thicken S r}, scaleFun φ c z
      ≤ ∫ z in {z : ℝᵈ | ρ - r ≤ ‖z‖}, scaleFun φ c z :=
    setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hfnn)
      (Filter.Eventually.of_forall fun z hz => hsub hz)
  have hchange : ∫ z in {z : ℝᵈ | ρ - r ≤ ‖z‖}, scaleFun φ c z
      = ∫ w in {w : ℝᵈ | c * (ρ - r) ≤ ‖w‖}, φ w := by
    have hcv := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure ℝᵈ)) φ
      {z : ℝᵈ | ρ - r ≤ ‖z‖} hc
    rw [finrank_euclideanSpace, Fintype.card_fin] at hcv
    have hset : c • {z : ℝᵈ | ρ - r ≤ ‖z‖} = {w : ℝᵈ | c * (ρ - r) ≤ ‖w‖} := by
      ext w
      simp only [Set.mem_smul_set, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_left hz hc.le
      · intro hw
        refine ⟨c⁻¹ • w, ?_, by rw [smul_inv_smul₀ hc.ne']⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
        have hw' : (ρ - r) * c ≤ ‖w‖ := by rw [mul_comm]; exact hw
        calc ρ - r = (ρ - r) * c * c⁻¹ := by field_simp
          _ ≤ ‖w‖ * c⁻¹ := mul_le_mul_of_nonneg_right hw' (inv_nonneg.mpr hc.le)
          _ = c⁻¹ * ‖w‖ := by ring
    rw [hset] at hcv
    change ∫ z in {z : ℝᵈ | ρ - r ≤ ‖z‖}, c ^ d * φ (c • z) = _
    rw [integral_const_mul, hcv]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hc.ne'), one_mul]
  calc ∫ z in {z : ℝᵈ | x - z ∈ thicken S r}, scaleFun φ c z
      ≤ ∫ z in {z : ℝᵈ | ρ - r ≤ ‖z‖}, scaleFun φ c z := hmono
    _ = ∫ w in {w : ℝᵈ | c * (ρ - r) ≤ ‖w‖}, φ w := hchange

end Submission.FUP
