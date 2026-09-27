import Mathlib
import Submission.Mostow.SubHypDefs
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.hdistBasic

/-!
# `even_normal_dim` (F13 of the strata design)

If `blk k m 1 R` is near the identity at some point `z`, then the normal dimension `m` is even.

The proof is in three parts, all in this file:

* `geom_scalars` — an explicit-constant real-analysis fact: for every `s₀ ≥ 0` and
  `φ₀ ∈ [0, π/2]` there are `σ, ε` with `cosh σ cosh s₀ - sinh s₀ sinh σ cos ε ≤ cosh 1` and
  `2 sinh²σ cos²(φ₀ - ε) ≥ cosh 1 - 1`.
* `even_normal_dim_core` — Fermi coordinates about the standard stratum: given the block action
  `blk k m 1 R • fermi v w = fermi v (R w)` (F4), the distance formula in Fermi coordinates (F2)
  and surjectivity of `fermi` (F1), an isometry `R` of `E m` with a unit vector `ê` satisfying
  `R ê = -ê` produces a point in the unit ball at `z` whose displacement under `blk k m 1 R`
  is at least `1`.
* `odd_isometry_neg_eigen` — linear algebra: an isometry of an odd-dimensional space with no
  nonzero fixed vector has a unit vector mapped to its negative.

Together: `NearIdAt (blk k m 1 R) z (1/2)` forces `m` even.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {m : ℕ}

/-! ## Elementary facts about `sinhc` -/

lemma sinhc_mul_self (s : ℝ) : sinhc s * s = Real.sinh s := by
  rw [sinhc]
  split_ifs with h
  · rw [h]; simp
  · rw [div_mul_cancel₀ _ h]

lemma sinhc_sq_mul_sq (s : ℝ) : sinhc s ^ 2 * s ^ 2 = Real.sinh s ^ 2 := by
  rw [← mul_pow, sinhc_mul_self]

/-! ## The displacement estimate for a `(-1)`-eigenvector -/

/-- For an isometry `R` with `R ê = -ê` and unit `ê`: `⟪R z, ê⟫ = -⟪z, ê⟫`. -/
lemma inner_R_eq_neg (R : E m ≃ₗᵢ[ℝ] E m) {ê : E m} (hRê : R ê = -ê) (z : E m) :
    inner ℝ (R z) ê = - inner ℝ z ê := by
  have h : inner ℝ (R z) (R ê) = inner ℝ z ê := LinearIsometryEquiv.inner_map_map R z ê
  rw [hRê] at h
  rw [inner_neg_right] at h
  linarith

/-- For an isometry `R` with a unit `(-1)`-eigenvector `ê` and any `u`,
`2 ⟪u, ê⟫² ≤ ‖u‖² - ⟪u, R u⟫`. -/
lemma two_inner_sq_le (R : E m ≃ₗᵢ[ℝ] E m) {ê : E m} (hê : ‖ê‖ = 1)
    (hRê : R ê = -ê) (u : E m) :
    2 * (inner ℝ u ê) ^ 2 ≤ ‖u‖ ^ 2 - inner ℝ u (R u) := by
  set a : ℝ := inner ℝ u ê with ha
  set w : E m := u - a • ê with hwdef
  have hw : inner ℝ w ê = 0 := by
    rw [hwdef, inner_sub_left, real_inner_smul_left, ← ha, real_inner_self_eq_norm_sq, hê]
    ring
  have hw' : inner ℝ ê w = 0 := by rw [real_inner_comm]; exact hw
  have hT2 : inner ℝ ê (R w) = 0 := by
    rw [real_inner_comm, inner_R_eq_neg R hRê w, hw, neg_zero]
  have huw : u = a • ê + w := by rw [hwdef]; abel
  have hnorm : ‖a • ê‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, hê, mul_one, Real.norm_eq_abs, sq_abs]
  have h1 : inner ℝ u (R u) = -a^2 + inner ℝ w (R w) := by
    simp only [huw, map_add, map_smul, hRê, smul_neg, inner_add_left, inner_add_right,
      inner_neg_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hê, hT2, hw, pow_one, one_mul, mul_one, mul_zero, add_zero]
    rw [hnorm]; ring
  have h2 : ‖u‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
    rw [huw, norm_add_sq_real, norm_smul, hê, mul_one, real_inner_smul_left, hw',
      Real.norm_eq_abs, sq_abs]
    ring
  have h3 : inner ℝ w (R w) ≤ ‖w‖ ^ 2 := by
    have h := real_inner_le_norm w (R w)
    rw [LinearIsometryEquiv.norm_map] at h
    linarith
  linarith

/-! ## A unit vector with prescribed inner products -/

/-- Given unit vectors `a`, `e` with `⟪a,e⟫ ≥ 0` and `0 ≤ ε ≤ arccos ⟪a,e⟫`, there is a unit
vector `ŵ` with `⟪ŵ,a⟫ = cos ε` and `⟪ŵ,e⟫ = cos (arccos ⟪a,e⟫ - ε)`. -/
lemma exists_dir (a e : E m) (ha : ‖a‖ = 1) (he : ‖e‖ = 1) (hc0 : 0 ≤ inner ℝ a e)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεφ : ε ≤ Real.arccos (inner ℝ a e)) :
    ∃ ŵ : E m, ‖ŵ‖ = 1 ∧ inner ℝ ŵ a = Real.cos ε ∧
      inner ℝ ŵ e = Real.cos (Real.arccos (inner ℝ a e) - ε) := by
  set c : ℝ := inner ℝ a e with hcdef
  have hc0' : 0 ≤ c := by rw [hcdef]; exact hc0
  have hc1 : c ≤ 1 := by
    have h := real_inner_le_norm a e
    rw [ha, he, mul_one] at h
    simpa [hcdef] using h
  have hcosc : Real.cos (Real.arccos c) = c := Real.cos_arccos (by linarith) hc1
  have hsinc : Real.sin (Real.arccos c) = Real.sqrt (1 - c ^ 2) := Real.sin_arccos c
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hea : inner ℝ e a = c := by rw [← real_inner_comm e a, ← hcdef]
  set p : E m := e - c • a with hpdef
  have hpa : inner ℝ p a = 0 := by
    rw [hpdef, inner_sub_left, real_inner_smul_left, hea, haa]
    ring
  have hpe : inner ℝ p e = 1 - c ^ 2 := by
    rw [hpdef, inner_sub_left, real_inner_smul_left, ← hcdef, hee]
    ring
  have hpp : inner ℝ p p = 1 - c ^ 2 := by
    rw [hpdef, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, hee, haa, hea, ← hcdef]
    ring
  by_cases hp : p = 0
  · have heq : e = c • a := by
      have h : e - c • a = 0 := by rw [← hpdef]; exact hp
      exact sub_eq_zero.mp h
    have hc_eq : c = 1 := by
      have h1 : |c| = 1 := by
        have h2 : ‖e‖ = ‖c • a‖ := by rw [heq]
        rw [he, norm_smul, ha, mul_one, Real.norm_eq_abs] at h2
        linarith [h2]
      rwa [abs_of_nonneg hc0'] at h1
    have hε : ε = 0 := by
      have h2 : ε ≤ 0 := by
        rw [hc_eq, Real.arccos_one] at hεφ; exact hεφ
      linarith
    refine ⟨a, ha, ?_, ?_⟩
    · rw [hε, Real.cos_zero, real_inner_self_eq_norm_sq, ha]; norm_num
    · rw [hε, hc_eq, Real.arccos_one, sub_zero, Real.cos_zero, ← hcdef, hc_eq]
  · have hppos : 0 < ‖p‖ := norm_pos_iff.mpr hp
    have hpnorm : ‖p‖ = Real.sqrt (1 - c ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg p), ← real_inner_self_eq_norm_sq, hpp]
    set b : E m := ‖p‖⁻¹ • p with hbdef
    have hbnorm : ‖b‖ = 1 := by
      rw [hbdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
        inv_mul_cancel₀ (ne_of_gt hppos)]
    have hba : inner ℝ b a = 0 := by
      rw [hbdef, real_inner_smul_left, hpa, mul_zero]
    have hab : inner ℝ a b = 0 := by rw [real_inner_comm]; exact hba
    have hbe : inner ℝ b e = Real.sqrt (1 - c ^ 2) := by
      rw [hbdef, real_inner_smul_left, hpe, hpnorm]
      rw [inv_mul_eq_div, Real.div_sqrt]
    refine ⟨Real.cos ε • a + Real.sin ε • b, ?_, ?_, ?_⟩
    · have hsq : ‖Real.cos ε • a + Real.sin ε • b‖ ^ 2 = 1 := by
        rw [norm_add_sq_real, norm_smul, norm_smul, ha, hbnorm, mul_one, mul_one,
          real_inner_smul_left, real_inner_smul_right, hab, mul_zero, mul_zero]
        rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
        linarith [Real.sin_sq_add_cos_sq ε]
      rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]
    · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        ha, hba, mul_zero]
      ring
    · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ← hcdef, hbe, Real.cos_sub,
        hcosc, hsinc]
      ring

/-! ## The explicit-constant scalar optimisation -/

/-- For every `s₀ ≥ 0` and `φ₀ ∈ [0, π/2]` there are `σ ≥ 0` and `ε ∈ [0, φ₀]` with
`cosh σ cosh s₀ - sinh s₀ sinh σ cos ε ≤ cosh 1` and
`cosh 1 - 1 ≤ 2 sinh²σ cos²(φ₀ - ε)`. -/
lemma geom_scalars (s₀ : ℝ) (hs₀ : 0 ≤ s₀) (φ₀ : ℝ) (hφ₀0 : 0 ≤ φ₀)
    (hφ₀ : φ₀ ≤ Real.pi / 2) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ φ₀ ∧
      Real.cosh σ * Real.cosh s₀ - Real.sinh s₀ * Real.sinh σ * Real.cos ε ≤ Real.cosh 1 ∧
      Real.cosh 1 - 1 ≤ 2 * Real.sinh σ ^ 2 * Real.cos (φ₀ - ε) ^ 2 := by
  set β : ℝ := Real.cosh 1 - 1 with hβdef
  have hβ0 : 0 < β := by
    rw [hβdef]
    have h := (Real.one_lt_cosh (x := (1:ℝ))).mpr (by norm_num)
    linarith
  have hcosh_half : Real.cosh (1/2) ^ 2 = (1 + Real.cosh 1) / 2 := by
    have h2 := Real.cosh_add (1/2) (1/2)
    rw [show (1:ℝ)/2 + 1/2 = 1 from by norm_num, ← sq, ← sq, Real.sinh_sq] at h2
    linarith
  have hsinh_half : Real.sinh (1/2) ^ 2 = β / 2 := by
    rw [Real.sinh_sq, hcosh_half, hβdef]; ring
  rcases le_or_gt (1/2) s₀ with hs | hs
  · have hsinh_ge : Real.sinh (1/2) ≤ Real.sinh s₀ := Real.sinh_le_sinh.mpr hs
    have hsinh2_ge : β / 2 ≤ Real.sinh s₀ ^ 2 := by
      rw [← hsinh_half]
      refine sq_le_sq.mpr ?_
      rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by norm_num)),
        abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by linarith))]
      exact hsinh_ge
    have hsinh2_pos : 0 < Real.sinh s₀ ^ 2 := lt_of_lt_of_le (by linarith) hsinh2_ge
    set b₀ : ℝ := β / Real.sinh s₀ ^ 2 with hb₀def
    have hb₀0 : 0 ≤ b₀ := by rw [hb₀def]; exact div_nonneg (le_of_lt hβ0) (le_of_lt hsinh2_pos)
    have hb₀2 : b₀ ≤ 2 := by rw [hb₀def, div_le_iff₀ hsinh2_pos]; linarith
    have hsinb : Real.sinh s₀ ^ 2 * b₀ = β := by
      rw [hb₀def, mul_div_cancel₀ _ (ne_of_gt hsinh2_pos)]
    set ε₀ : ℝ := Real.arccos (1 - b₀) with hε₀def
    have hcosε₀ : Real.cos ε₀ = 1 - b₀ := by
      rw [hε₀def]
      exact Real.cos_arccos (by linarith) (by linarith)
    have hε₀0 : 0 ≤ ε₀ := by rw [hε₀def]; exact Real.arccos_nonneg _
    have hε₀π : ε₀ ≤ Real.pi := by rw [hε₀def]; exact Real.arccos_le_pi _
    refine ⟨s₀, hs₀, min φ₀ ε₀, le_min hφ₀0 hε₀0, min_le_left _ _, ?_, ?_⟩
    · have hcosine : Real.cos ε₀ ≤ Real.cos (min φ₀ ε₀) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_min hφ₀0 hε₀0) hε₀π (min_le_right _ _)
      have hmul : Real.sinh s₀ ^ 2 * Real.cos ε₀ ≤ Real.sinh s₀ ^ 2 * Real.cos (min φ₀ ε₀) :=
        mul_le_mul_of_nonneg_left hcosine (by positivity)
      rw [hcosε₀] at hmul
      have hgoal : Real.cosh s₀ ^ 2 = 1 + Real.sinh s₀ ^ 2 := by
        linarith [Real.cosh_sq_sub_sinh_sq s₀]
      have hexp : Real.cosh s₀ * Real.cosh s₀ = Real.cosh s₀ ^ 2 := by ring
      have hmain : Real.cosh s₀ ^ 2 - Real.sinh s₀ ^ 2 * Real.cos (min φ₀ ε₀) ≤ Real.cosh 1 := by
        rw [show Real.cosh 1 = 1 + β from by rw [hβdef]; ring]
        nlinarith [hmul, hgoal, hsinb]
      linarith [hexp, hmain]
    · rcases le_or_gt φ₀ ε₀ with hle | hlt
      · rw [min_eq_left hle, sub_self, Real.cos_zero, one_pow, mul_one]
        have hbnd : β ≤ 2 * Real.sinh s₀ ^ 2 := by linarith [hsinh2_ge]
        rw [hβdef] at hbnd
        nlinarith [hbnd]
      · have hmin : min φ₀ ε₀ = ε₀ := min_eq_right (le_of_lt hlt)
        rw [hmin]
        have hb₀1 : b₀ < 1 := by
          have hp : Real.cos (Real.pi/2) < Real.cos ε₀ :=
            Real.cos_lt_cos_of_nonneg_of_le_pi hε₀0 (by linarith) (by linarith)
          rw [Real.cos_pi_div_two, hcosε₀] at hp
          linarith
        have hcos2 : Real.sin ε₀ ^ 2 ≤ Real.cos (φ₀ - ε₀) ^ 2 := by
          have h1 : 0 ≤ φ₀ - ε₀ := by linarith
          have h2 : φ₀ - ε₀ ≤ Real.pi/2 - ε₀ := by linarith
          have hc : Real.cos (Real.pi/2 - ε₀) ≤ Real.cos (φ₀ - ε₀) :=
            Real.cos_le_cos_of_nonneg_of_le_pi h1 (by linarith) h2
          rw [Real.cos_pi_div_two_sub] at hc
          have hnn : 0 ≤ Real.sin ε₀ := Real.sin_nonneg_of_nonneg_of_le_pi hε₀0 hε₀π
          nlinarith [hc, hnn, Real.cos_le_one (φ₀ - ε₀)]
        have hbnd : Real.cosh 1 - 1 ≤ 2 * Real.sinh s₀ ^ 2 * Real.sin ε₀ ^ 2 := by
          have h1 : Real.sin ε₀ ^ 2 = 1 - (1 - b₀) ^ 2 := by rw [Real.sin_sq, hcosε₀]
          rw [h1]
          have h2 : 1 - (1 - b₀) ^ 2 = b₀ * (2 - b₀) := by ring
          rw [h2, show 2 * Real.sinh s₀ ^ 2 * (b₀ * (2 - b₀)) =
              2 * (Real.sinh s₀ ^ 2 * b₀) * (2 - b₀) from by ring, hsinb, hβdef]
          nlinarith [hβ0, hb₀1]
        nlinarith [hcos2, hbnd, sq_nonneg (Real.sinh s₀)]
  · refine ⟨1/2, by norm_num, φ₀, hφ₀0, le_rfl, ?_, ?_⟩
    · have hcosφ₀ : 0 ≤ Real.cos φ₀ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      have hsinhs₀ : 0 ≤ Real.sinh s₀ := Real.sinh_nonneg_iff.mpr hs₀
      have hcoshs : Real.cosh s₀ ≤ Real.cosh (1/2) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg hs₀, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
        exact le_of_lt hs
      have h1 : 0 ≤ Real.sinh s₀ * Real.sinh (1/2) * Real.cos φ₀ :=
        mul_nonneg (mul_nonneg hsinhs₀ (le_of_lt (Real.sinh_pos_iff.mpr (by norm_num)))) hcosφ₀
      have h2 : Real.cosh (1/2) * Real.cosh s₀ ≤ Real.cosh (1/2) * Real.cosh (1/2) :=
        mul_le_mul_of_nonneg_left hcoshs (le_of_lt (Real.cosh_pos _))
      have h3 : Real.cosh (1/2) * Real.cosh (1/2) = (1 + Real.cosh 1)/2 := by
        rw [← sq]; exact hcosh_half
      have h4 : (1 + Real.cosh 1)/2 ≤ Real.cosh 1 := by
        have := (Real.one_lt_cosh (x := (1:ℝ))).mpr (by norm_num); linarith
      linarith [h1, h2, h3, h4]
    · rw [sub_self, Real.cos_zero, one_pow, mul_one]
      rw [show (2:ℝ) * Real.sinh (1/2) ^ 2 = β from by rw [hsinh_half]; ring, hβdef]

/-! ## Linear algebra: odd dimension forces a `(-1)`-eigenvector -/

/-- If `f` has no eigenvector with eigenvalue `-1` then `det f > 0`: the path
`t ↦ (1-t) • 1 + t • f` avoids the singular matrices on `[0,1]`. -/
lemma det_pos_of_no_neg_eigen (f : E m →ₗ[ℝ] E m)
    (hiso : ∀ x : E m, ‖f x‖ = ‖x‖)
    (hno : ∀ v : E m, v ≠ 0 → f v ≠ -v) : 0 < LinearMap.det f := by
  by_contra hle
  push Not at hle
  set b : Module.Basis (Fin m) ℝ (E m) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis with hb
  have hcont : Continuous fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f) := by
    have hfun : (fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f))
        = fun t : ℝ => (((1 - t) • (1 : Matrix (Fin m) (Fin m) ℝ)
            + t • (LinearMap.toMatrix b b f))).det := by
      funext t
      have h1 : (LinearMap.toMatrix b b) ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f)
          = (1 - t) • (1 : Matrix (Fin m) (Fin m) ℝ) + t • (LinearMap.toMatrix b b f) := by
        rw [map_add, map_smul, map_smul, LinearMap.toMatrix_one]
      rw [← LinearMap.det_toMatrix b ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f), h1]
    rw [hfun]
    exact Continuous.matrix_det (by fun_prop)
  have hker : ∀ t ∈ Set.Icc (0:ℝ) 1,
      LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f) ≠ 0 := by
    intro t ht h0
    have hne : ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f).ker ≠ ⊥ :=
      (LinearMap.det_eq_zero_iff_ker_ne_bot).mp h0
    obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hne
    have hveq : (1 - t) • v + t • (f v) = 0 := by
      have := hv
      rw [LinearMap.mem_ker] at this
      simpa using this
    have ht01 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hnorm : t * ‖v‖ = |1 - t| * ‖v‖ := by
      have h1 : t • (f v) = -((1 - t) • v) := eq_neg_of_add_eq_zero_right hveq
      have h2 : ‖t • (f v)‖ = ‖(1 - t) • v‖ := by rw [h1, norm_neg]
      rw [norm_smul, norm_smul, hiso v, Real.norm_of_nonneg ht01, Real.norm_eq_abs] at h2
      exact h2
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
    have ht_eq : t = |1 - t| := mul_right_cancel₀ hvnorm hnorm
    have ht12 : t = 1/2 := by
      have h1t : (0:ℝ) ≤ 1 - t := by linarith
      rw [abs_of_nonneg h1t] at ht_eq
      linarith
    have hfin : f v = -v := by
      have h2 : (1/2 : ℝ) • v + (1/2 : ℝ) • (f v) = 0 := by
        rw [ht12] at hveq
        norm_num at hveq
        simpa using hveq
      have h4 : v + f v = 0 := by
        have h5 := congrArg (fun z : E m => (2:ℝ) • z) h2
        simp only [smul_add, smul_smul] at h5
        simpa using h5
      exact eq_neg_of_add_eq_zero_right h4
    exact hno v hvne hfin
  have hg : ContinuousOn (fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f))
      (Set.Icc 0 1) := hcont.continuousOn
  have h0 : (fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f)) 0 = 1 := by
    simp
  have h1 : (fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f)) 1
      = LinearMap.det f := by
    simp
  have hmem : (0:ℝ) ∈ Set.Icc
      ((fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f)) 1)
      ((fun t : ℝ => LinearMap.det ((1 - t) • (1 : E m →ₗ[ℝ] E m) + t • f)) 0) := by
    refine ⟨?_, ?_⟩
    · rw [h1]; exact hle
    · rw [h0]; norm_num
  obtain ⟨t, ht, ht0⟩ := (intermediate_value_Icc' (a := (0:ℝ)) (b := 1) (by norm_num) hg) hmem
  exact hker t ht ht0

/-- If `f` has no nonzero fixed vector and `m` is odd, then `det f < 0`: the path
`t ↦ t • f - (1-t) • 1` avoids the singular matrices on `[0,1]`. -/
lemma det_neg_of_no_fixed (f : E m →ₗ[ℝ] E m) (hm : Odd m)
    (hiso : ∀ x : E m, ‖f x‖ = ‖x‖)
    (hfix : ∀ w : E m, f w = w → w = 0) : LinearMap.det f < 0 := by
  by_contra hle
  push Not at hle
  set b : Module.Basis (Fin m) ℝ (E m) := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis with hb
  have hcont : Continuous fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m)) := by
    have hfun : (fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m)))
        = fun t : ℝ => ((t • (LinearMap.toMatrix b b f)
            - (1 - t) • (1 : Matrix (Fin m) (Fin m) ℝ))).det := by
      funext t
      have h1 : (LinearMap.toMatrix b b) (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m))
          = t • (LinearMap.toMatrix b b f) - (1 - t) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
        rw [map_sub, map_smul, map_smul, LinearMap.toMatrix_one]
      rw [← LinearMap.det_toMatrix b (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m)), h1]
    rw [hfun]
    exact Continuous.matrix_det (by fun_prop)
  have hker : ∀ t ∈ Set.Icc (0:ℝ) 1,
      LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m)) ≠ 0 := by
    intro t ht h0
    have hne : (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m)).ker ≠ ⊥ :=
      (LinearMap.det_eq_zero_iff_ker_ne_bot).mp h0
    obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hne
    have hveq : t • (f v) - (1 - t) • v = 0 := by
      have := hv
      rw [LinearMap.mem_ker] at this
      simpa using this
    have ht01 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hnorm : t * ‖v‖ = |1 - t| * ‖v‖ := by
      have h1 : t • (f v) = (1 - t) • v := sub_eq_zero.mp hveq
      have h2 : ‖t • (f v)‖ = ‖(1 - t) • v‖ := by rw [h1]
      rw [norm_smul, norm_smul, hiso v, Real.norm_of_nonneg ht01, Real.norm_eq_abs] at h2
      exact h2
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
    have ht_eq : t = |1 - t| := mul_right_cancel₀ hvnorm hnorm
    have ht12 : t = 1/2 := by
      have h1t : (0:ℝ) ≤ 1 - t := by linarith
      rw [abs_of_nonneg h1t] at ht_eq
      linarith
    have hfin : f v = v := by
      have h2 : (1/2 : ℝ) • (f v) - (1/2:ℝ) • v = 0 := by
        rw [ht12] at hveq
        norm_num at hveq
        exact hveq
      have h3 : (1/2 : ℝ) • (f v) = (1/2 : ℝ) • v := by
        rw [← sub_eq_zero]; exact h2
      have h5 := congrArg (fun z : E m => (2:ℝ) • z) h3
      simp only [smul_smul] at h5
      simpa using h5
    exact hvne (hfix v hfin)
  have hg : ContinuousOn (fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m)))
      (Set.Icc 0 1) := hcont.continuousOn
  have h0 : (fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m))) 0
      = (-1:ℝ)^m := by
    have hN0 : (0:ℝ) • f - (1 - 0) • (1 : E m →ₗ[ℝ] E m) = (-1:ℝ) • (1 : E m →ₗ[ℝ] E m) := by
      simp
    have h := congrArg LinearMap.det hN0
    simp only [LinearMap.det_smul, finrank_euclideanSpace, Fintype.card_fin] at h
    simpa using h
  have h1 : (fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m))) 1
      = LinearMap.det f := by
    have hN1 : (1:ℝ) • f - (1 - 1) • (1 : E m →ₗ[ℝ] E m) = f := by simp
    have h := congrArg LinearMap.det hN1
    simpa using h
  have hmem : (0:ℝ) ∈ Set.Icc
      ((fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m))) 0)
      ((fun t : ℝ => LinearMap.det (t • f - (1 - t) • (1 : E m →ₗ[ℝ] E m))) 1) := by
    refine ⟨?_, ?_⟩
    · rw [h0, hm.neg_one_pow]; norm_num
    · rw [h1]; exact hle
  obtain ⟨t, ht, ht0⟩ := (intermediate_value_Icc (a := (0:ℝ)) (b := 1) (by norm_num) hg) hmem
  exact hker t ht ht0

/-- An isometry of an odd-dimensional real inner product space with no nonzero fixed vector
has a unit vector mapped to its negative. -/
theorem odd_isometry_neg_eigen (R : E m ≃ₗᵢ[ℝ] E m) (hm : Odd m)
    (hR : ∀ w : E m, R w = w → w = 0) : ∃ ê : E m, ‖ê‖ = 1 ∧ R ê = -ê := by
  classical
  set f : E m →ₗ[ℝ] E m := R.toLinearMap with hf
  have hfR : ∀ x : E m, f x = R x := fun x => rfl
  have hiso : ∀ x : E m, ‖f x‖ = ‖x‖ := by
    intro x; rw [hfR x]; exact R.norm_map x
  have hfix : ∀ w : E m, f w = w → w = 0 := by
    intro w hw; exact hR w (by rw [← hfR w]; exact hw)
  have h1 : LinearMap.det f < 0 := det_neg_of_no_fixed f hm hiso hfix
  by_contra hcon
  push Not at hcon
  have hno : ∀ v : E m, v ≠ 0 → f v ≠ -v := by
    intro v hv hvf
    have hnorm : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hvs : R ((‖v‖⁻¹ : ℝ) • v) = -((‖v‖⁻¹ : ℝ) • v) := by
      rw [map_smul, ← hfR v, hvf, smul_neg]
    exact hcon _ hnorm hvs
  have h2 : 0 < LinearMap.det f := det_pos_of_no_neg_eigen f hiso hno
  linarith

/-! ## The Fermi-coordinate core -/

/-- **F13, core.** Given the block action (F4), the distance formula in Fermi coordinates (F2) and
surjectivity of `fermi` (F1), an isometry `R` of `E m` with `R ê = -ê` for a unit `ê` provides a
point of the unit ball at `z` moved by at least `1` under `blk k m 1 R`. -/
theorem even_normal_dim_core (k m : ℕ) (hIk : HypIsometryProp k) (hI : HypIsometryProp (k + m))
    (hsurj : ∀ u : E (k + m), fermi k m (fermiInv k m u).1 (fermiInv k m u).2 = u)
    (hcosh : ∀ (v v' : E k) (w w' : E m),
      Real.cosh (hdist (fermi k m v w) (fermi k m v' w')) =
        Real.cosh ‖w‖ * Real.cosh ‖w'‖ * Real.cosh (hdist v v') -
          sinhc ‖w‖ * sinhc ‖w'‖ * inner ℝ w w')
    (R : E m ≃ₗᵢ[ℝ] E m) (ê : E m) (hê : ‖ê‖ = 1) (hRê : R ê = -ê)
    (hact : ∀ (v : E k) (w : E m), blk k m 1 R • fermi k m v w = fermi k m v (R w))
    (z : E (k + m)) : ∃ u : E (k + m), hdist z u ≤ 1 ∧ 1 ≤ hdist u (blk k m 1 R • u) := by
  classical
  set v₀ : E k := (fermiInv k m z).1 with hv₀
  set w₀ : E m := (fermiInv k m z).2 with hw₀
  have hz : fermi k m v₀ w₀ = z := hsurj z
  have hvv : hdist v₀ v₀ = 0 := (hIk.2.2.1 v₀ v₀).mpr rfl
  have hs₀ : 0 ≤ ‖w₀‖ := norm_nonneg _
  set d₀ : E m := if w₀ = 0 then ê else ‖w₀‖⁻¹ • w₀ with hd₀
  have hd₀norm : ‖d₀‖ = 1 := by
    by_cases hw : w₀ = 0
    · rw [hd₀, if_pos hw]; exact hê
    · rw [hd₀, if_neg hw, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hw₀d : w₀ = ‖w₀‖ • d₀ := by
    by_cases hw : w₀ = 0
    · rw [hd₀, if_pos hw, hw, norm_zero, zero_smul]
    · rw [hd₀, if_neg hw, smul_inv_smul₀ (norm_ne_zero_iff.mpr hw)]
  set e₂ : E m := if 0 ≤ inner ℝ d₀ ê then ê else -ê with he₂
  have he₂norm : ‖e₂‖ = 1 := by
    by_cases h : 0 ≤ inner ℝ d₀ ê
    · rw [he₂, if_pos h]; exact hê
    · rw [he₂, if_neg h, norm_neg]; exact hê
  have hRe₂ : R e₂ = -e₂ := by
    by_cases h : 0 ≤ inner ℝ d₀ ê
    · rw [he₂, if_pos h]; exact hRê
    · rw [he₂, if_neg h, map_neg, hRê, neg_neg]
  have hc : inner ℝ d₀ e₂ = |inner ℝ d₀ ê| := by
    by_cases h : 0 ≤ inner ℝ d₀ ê
    · rw [he₂, if_pos h, abs_of_nonneg h]
    · rw [he₂, if_neg h, inner_neg_right, abs_of_neg (lt_of_not_ge h)]
  have hc0 : 0 ≤ inner ℝ d₀ e₂ := by rw [hc]; exact abs_nonneg _
  have hc1 : inner ℝ d₀ e₂ ≤ 1 := by
    have := real_inner_le_norm d₀ e₂
    rw [hd₀norm, he₂norm, mul_one] at this; exact this
  have hφ : Real.arccos (inner ℝ d₀ e₂) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr hc0
  obtain ⟨σ, hσ0, ε, hε0, hεφ, hcons, hval⟩ :=
    geom_scalars ‖w₀‖ hs₀ (Real.arccos (inner ℝ d₀ e₂)) (Real.arccos_nonneg _) hφ
  obtain ⟨ŵ, hŵnorm, hŵd, hŵe⟩ := exists_dir d₀ e₂ hd₀norm he₂norm hc0 hε0 hεφ
  have hσn : ‖σ • ŵ‖ = σ := by
    rw [norm_smul, hŵnorm, mul_one, Real.norm_of_nonneg hσ0]
  refine ⟨fermi k m v₀ (σ • ŵ), ?_, ?_⟩
  · have hkey : Real.cosh (hdist (fermi k m v₀ (σ • ŵ)) z) =
        Real.cosh σ * Real.cosh ‖w₀‖ - Real.sinh ‖w₀‖ * Real.sinh σ * Real.cos ε := by
      have hF : inner ℝ (σ • ŵ) w₀ = σ * ‖w₀‖ * Real.cos ε := by
        have h2 : inner ℝ ŵ w₀ = ‖w₀‖ * Real.cos ε := by
          conv_lhs => rw [hw₀d]
          rw [real_inner_smul_right, hŵd]
        have h1 : inner ℝ (σ • ŵ) w₀ = σ * inner ℝ ŵ w₀ := by
          rw [real_inner_smul_left]
        rw [h1, h2]; ring
      have hF' : sinhc σ * sinhc ‖w₀‖ * (σ * ‖w₀‖ * Real.cos ε) =
          Real.sinh σ * Real.sinh ‖w₀‖ * Real.cos ε := by
        rw [show sinhc σ * sinhc ‖w₀‖ * (σ * ‖w₀‖ * Real.cos ε) =
            (sinhc σ * σ) * (sinhc ‖w₀‖ * ‖w₀‖) * Real.cos ε from by ring,
          sinhc_mul_self σ, sinhc_mul_self ‖w₀‖]
      rw [← hz, hcosh v₀ v₀ (σ • ŵ) w₀, hvv, Real.cosh_zero, mul_one, hσn, hF, hF']
      ring
    have hle : Real.cosh (hdist (fermi k m v₀ (σ • ŵ)) z) ≤ Real.cosh 1 := by
      rw [hkey]; exact hcons
    have h1 := (Real.cosh_le_cosh (x := hdist (fermi k m v₀ (σ • ŵ)) z)).mp hle
    rw [abs_of_nonneg (hI.1 _ _), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] at h1
    rw [hI.2.1 z (fermi k m v₀ (σ • ŵ))]
    exact h1
  · have hblk : blk k m 1 R • fermi k m v₀ (σ • ŵ) = fermi k m v₀ (σ • R ŵ) := by
      rw [hact v₀ (σ • ŵ), map_smul]
    have hRn : ‖σ • R ŵ‖ = σ := by
      rw [norm_smul, LinearIsometryEquiv.norm_map, hŵnorm, mul_one, Real.norm_of_nonneg hσ0]
    have hkey : Real.cosh (hdist (fermi k m v₀ (σ • ŵ))
          (blk k m 1 R • fermi k m v₀ (σ • ŵ))) =
        Real.cosh σ ^ 2 - Real.sinh σ ^ 2 * inner ℝ ŵ (R ŵ) := by
      have hG : inner ℝ (σ • ŵ) (σ • R ŵ) = σ ^ 2 * inner ℝ ŵ (R ŵ) := by
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      have hG' : sinhc σ * sinhc σ * (σ ^ 2 * inner ℝ ŵ (R ŵ)) =
          Real.sinh σ ^ 2 * inner ℝ ŵ (R ŵ) := by
        rw [show sinhc σ * sinhc σ * (σ ^ 2 * inner ℝ ŵ (R ŵ)) =
            (sinhc σ * σ) * (sinhc σ * σ) * inner ℝ ŵ (R ŵ) from by ring,
          sinhc_mul_self σ]
        rw [show (Real.sinh σ * Real.sinh σ) = Real.sinh σ ^ 2 from by ring]
      rw [hblk, hcosh v₀ v₀ (σ • ŵ) (σ • R ŵ), hvv, Real.cosh_zero, mul_one, hσn, hRn,
        hG, hG']
      rw [show Real.cosh σ * Real.cosh σ = Real.cosh σ ^ 2 from by ring]
    have hbd : inner ℝ ŵ (R ŵ) ≤ 1 - 2 * (inner ℝ ŵ e₂) ^ 2 := by
      have h := two_inner_sq_le R he₂norm hRe₂ ŵ
      rw [hŵnorm] at h
      linarith
    have hge : Real.cosh 1 ≤ Real.cosh (hdist (fermi k m v₀ (σ • ŵ))
        (blk k m 1 R • fermi k m v₀ (σ • ŵ))) := by
      rw [hkey]
      have hs2 : 0 ≤ Real.sinh σ ^ 2 := sq_nonneg _
      have hmult : Real.sinh σ ^ 2 * inner ℝ ŵ (R ŵ) ≤
          Real.sinh σ ^ 2 * (1 - 2 * (inner ℝ ŵ e₂) ^ 2) :=
        mul_le_mul_of_nonneg_left hbd hs2
      have hsq : Real.cosh σ ^ 2 - Real.sinh σ ^ 2 * inner ℝ ŵ (R ŵ) ≥
          1 + 2 * Real.sinh σ ^ 2 * (inner ℝ ŵ e₂) ^ 2 := by
        nlinarith [Real.cosh_sq_sub_sinh_sq σ, hmult]
      have hval' : Real.cosh 1 - 1 ≤ 2 * Real.sinh σ ^ 2 * (inner ℝ ŵ e₂) ^ 2 := by
        have hv := hval
        rw [← hŵe] at hv
        exact hv
      linarith
    have h2 := (Real.cosh_le_cosh (x := 1) (y := hdist (fermi k m v₀ (σ • ŵ))
      (blk k m 1 R • fermi k m v₀ (σ • ŵ)))).mp hge
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1), abs_of_nonneg (hI.1 _ _)] at h2
    exact h2

/-! ## F13 -/

/-- **F13.** There is `η₀ > 0` such that whenever `blk k m 1 R` is `η₀`-near the identity at `z`
and `R` has no nonzero fixed vector, the normal dimension `m` is even. -/
theorem even_normal_dim : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (k m : ℕ), POActionProp k → HypIsometryProp k →
    POActionProp (k + m) → HypIsometryProp (k + m) → ∀ (R : E m ≃ₗᵢ[ℝ] E m) (z : E (k + m)),
      (∀ w, R w = w → w = 0) → NearIdAt (blk k m 1 R) z η₀ → Even m := by
  refine ⟨1/2, by norm_num, ?_⟩
  intro k m hAk hIk hA hI R z hR hNear
  by_contra heven
  have hodd : Odd m := by
    by_contra h
    exact heven (Nat.not_odd_iff_even.mp h)
  obtain ⟨ê, hê, hRê⟩ := odd_isometry_neg_eigen R hodd hR
  obtain ⟨u, hu1, hu2⟩ :=
    even_normal_dim_core k m hIk hI (fun u => (fermi_inv k m).2.1 u)
      (fun v v' w w' => cosh_hdist_fermi k m v v' w w')
      R ê hê hRê (fun v w => by
        have hone : (1 : PO k 1) • v = v := hAk.2.2.2.1 v
        have hb := blk_smul_fermi k m hAk hIk hA hI 1 R v w
        rw [hone] at hb
        exact hb) z
  have := hNear u hu1
  linarith

end

end Work.Mostow
