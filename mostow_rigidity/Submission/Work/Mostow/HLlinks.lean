import Mathlib
import Submission.Work.Mostow.HLBasics

/-!
# Shared lemmas for the HL assembly (`HL_of_boundedTorsion`, `HL_of_escapeShort`)

Sorry-free toolbox for the "links + pinning" part of the horoball/parabolic (HL) argument:

* ray facts: `rayN`, `hdist_rayN*`, `busemann_rayN`, `lev_rayN*`, `yc_rayN`, `norm_yc_rayN_le`;
* boundary eigenvector bookkeeping: `bd_emat_eigen`, `no_swap_of_preserves_pair`;
* level/flat-coordinate invariance: `lev_smul_of_zero_cocycle`, `yc_dist_eq_of_zero_cocycle`;
* the "two boundary fixed points + zero cocycle ⇒ interior fixed point" trick
  (`exists_fixed_of_two_bd_fixes`);
* pigeonhole helpers `exists_frequently_fiber`, `frequently_add_imp`;
* `finite_hdist_orbit_ball` (finiteness of a bounded orbit set for a discrete group).
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Matrix

namespace Work.Mostow

noncomputable section

open Filter

variable {n : ℕ}

/-! ## Elementary ray facts -/

/-- `NearIdAt` is monotone in the bound. -/
lemma NearIdAt_mono {g : PO n 1} {z : E n} {η η' : ℝ} (h : NearIdAt g z η) (hle : η ≤ η') :
    NearIdAt g z η' := fun u hu => lt_of_lt_of_le (h u hu) hle

/-- The integral points of the ray to `ζ`. -/
def rayN (ζ : E n) (k : ℕ) : E n := Real.sinh (k : ℝ) • ζ

lemma hdist_rayN (ζ : E n) (hζ : ζ ∈ Sph n) (j k : ℕ) :
    hdist (rayN ζ j) (rayN ζ k) = |(j : ℝ) - (k : ℝ)| :=
  BdExt.hdist_ray_ray ζ hζ (j : ℝ) (k : ℝ)

lemma hdist_rayN_succ (ζ : E n) (hζ : ζ ∈ Sph n) (k : ℕ) :
    hdist (rayN ζ (k + 1)) (rayN ζ k) = 1 := by
  rw [hdist_rayN ζ hζ]
  have : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
  rw [this, abs_one]

lemma hdist_rayN_self (ζ : E n) (hζ : ζ ∈ Sph n) (k : ℕ) : hdist (rayN ζ k) (rayN ζ k) = 0 := by
  rw [hdist_rayN ζ hζ]; simp

/-- The Busemann function along a ray: `busemann ζ (sinh t • ζ) = -t`. -/
lemma busemann_ray_real (ζ : E n) (hζ : ζ ∈ Sph n) (t : ℝ) :
    busemann ζ (Real.sinh t • ζ) = -t := by
  have hnorm : ‖ζ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hζ
  have h1 : tpart (Real.sinh t • ζ) = Real.cosh t := by
    have hsq : ‖Real.sinh t • ζ‖ ^ 2 = Real.sinh t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm, one_pow, mul_one]
    rw [tpart, hsq]
    have h2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by rw [Real.cosh_sq]; ring
    rw [h2, Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
  have h2 : inner ℝ (Real.sinh t • ζ) ζ = Real.sinh t := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]; ring
  rw [busemann, h1, h2, Real.cosh_sub_sinh, Real.log_exp]

lemma busemann_rayN (ζ : E n) (hζ : ζ ∈ Sph n) (k : ℕ) :
    busemann ζ (rayN ζ k) = -(k : ℝ) :=
  busemann_ray_real ζ hζ (k : ℝ)

/-- The horospherical level of the ray points at `ζ` in the chart at `ξ`. -/
lemma lev_rayN {ξ ζ : E n} (hζ : ζ ∈ Sph n) (m : ℕ) :
    lev ξ (rayN ζ m) = Real.cosh (m : ℝ) - Real.sinh (m : ℝ) * inner ℝ ζ ξ := by
  rw [lev, rayN, tpart_sinh_smul ζ (m : ℝ) ((mem_Sph_iff ζ).mp hζ), real_inner_smul_left]

/-- The flat coordinate of the ray points at `ζ` in the chart at `ξ`. -/
lemma yc_rayN {ξ ζ : E n} (hζ : ζ ∈ Sph n) (m : ℕ) :
    yc ξ (rayN ζ m)
      = ((lev ξ (rayN ζ m))⁻¹ * Real.sinh (m : ℝ)) • (ζ - inner ℝ ζ ξ • ξ) := by
  rw [yc, wc, rayN]
  have hc : inner ℝ (Real.sinh (m : ℝ) • ζ) ξ = Real.sinh (m : ℝ) * inner ℝ ζ ξ := by
    rw [real_inner_smul_left]
  rw [hc, show Real.sinh (m : ℝ) • ζ - (Real.sinh (m : ℝ) * inner ℝ ζ ξ) • ξ
      = Real.sinh (m : ℝ) • (ζ - inner ℝ ζ ξ • ξ) by rw [smul_sub, smul_smul], smul_smul]

/-- Uniform lower bound for the level of the ray points at `ζ`. -/
lemma lev_rayN_lower {ξ ζ : E n} (hζ : ζ ∈ Sph n) (m : ℕ) :
    min 1 (1 - inner ℝ ζ ξ) * Real.cosh (m : ℝ) ≤ lev ξ (rayN ζ m) := by
  rw [lev_rayN hζ m]
  have hsin_le_cosh : Real.sinh (m : ℝ) ≤ Real.cosh (m : ℝ) := le_of_lt (Real.sinh_lt_cosh _)
  have hcosh_pos : 0 < Real.cosh (m : ℝ) := Real.cosh_pos _
  rcases le_total (inner ℝ ζ ξ) 0 with hc | hc
  · have h1 : min 1 (1 - inner ℝ ζ ξ) ≤ 1 := min_le_left _ _
    have h2 : 0 ≤ Real.sinh (m : ℝ) := Real.sinh_nonneg_iff.mpr (Nat.cast_nonneg m)
    have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hcosh_pos)
    have h4 : 0 ≤ -(inner ℝ ζ ξ) * Real.sinh (m : ℝ) := mul_nonneg (by linarith) h2
    nlinarith [hcosh_pos, h3, h4]
  · have h1 : min 1 (1 - inner ℝ ζ ξ) ≤ 1 - inner ℝ ζ ξ := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hcosh_pos)
    have h3 := mul_le_mul_of_nonneg_left hsin_le_cosh hc
    nlinarith [hcosh_pos, h2, h3]

/-- Bound on the norm of the flat coordinate of the ray points. -/
lemma norm_yc_rayN_le {ξ ζ : E n} (hξ : ξ ∈ Sph n) (hζ : ζ ∈ Sph n) (hne : ξ ≠ ζ) (m : ℕ) :
    ‖yc ξ (rayN ζ m)‖ ≤ ‖ζ - inner ℝ ζ ξ • ξ‖ / min 1 (1 - inner ℝ ζ ξ) := by
  have hζn : ‖ζ‖ = 1 := (mem_Sph_iff ζ).mp hζ
  have hc_lt : inner ℝ ζ ξ < 1 :=
    inner_lt_one_of_ne_unit hζn ((mem_Sph_iff ξ).mp hξ) (Ne.symm hne)
  have hLbpos : 0 < min 1 (1 - inner ℝ ζ ξ) := lt_min one_pos (by linarith)
  have hLlow := lev_rayN_lower (ξ := ξ) hζ m
  have hLpos : 0 < lev ξ (rayN ζ m) := lev_pos ξ hξ _
  have hsin_nonneg : 0 ≤ Real.sinh (m : ℝ) := Real.sinh_nonneg_iff.mpr (Nat.cast_nonneg m)
  have hsin_le_cosh : Real.sinh (m : ℝ) ≤ Real.cosh (m : ℝ) := le_of_lt (Real.sinh_lt_cosh _)
  rw [yc_rayN hζ m, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hsin_nonneg)]
  have hratio : (lev ξ (rayN ζ m))⁻¹ * Real.sinh (m : ℝ) ≤ 1 / min 1 (1 - inner ℝ ζ ξ) := by
    rw [inv_mul_eq_div, div_le_div_iff₀ hLpos hLbpos, one_mul]
    calc Real.sinh (m : ℝ) * min 1 (1 - inner ℝ ζ ξ)
        ≤ Real.cosh (m : ℝ) * min 1 (1 - inner ℝ ζ ξ) :=
          mul_le_mul_of_nonneg_right hsin_le_cosh hLbpos.le
      _ = min 1 (1 - inner ℝ ζ ξ) * Real.cosh (m : ℝ) := by ring
      _ ≤ lev ξ (rayN ζ m) := hLlow
  calc (lev ξ (rayN ζ m))⁻¹ * Real.sinh (m : ℝ) * ‖ζ - inner ℝ ζ ξ • ξ‖
      ≤ (1 / min 1 (1 - inner ℝ ζ ξ)) * ‖ζ - inner ℝ ζ ξ • ξ‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ = ‖ζ - inner ℝ ζ ξ • ξ‖ / min 1 (1 - inner ℝ ζ ξ) := by ring

/-! ## Minkowski-form bookkeeping -/

/-- The two Minkowski forms used in the workspace agree. -/
lemma mform_eq_hyperMink (x y : Fin n ⊕ Fin 1 → ℝ) : mform x y = Hyper.mink x y := by
  rw [mform_apply, Hyper.mink_apply]

/-- If `bd g ξ = η` then the null vector `θ ξ` is mapped to a nonzero multiple of `θ η`. -/
lemma bd_emat_eigen {g : PO n 1} {ξ η : E n} (hξ : ξ ∈ Sph n) (h : bd g ξ = η) :
    ∃ t : ℝ, t ≠ 0 ∧ emat g *ᵥ theta ξ = t • theta η := by
  have ht : (mat (rep g) *ᵥ theta ξ) (Sum.inr 0) ≠ 0 := mat_mulVec_theta_ne_zero (rep g) hξ
  have h1 := smul_theta_of_time_ne_zero (mat (rep g) *ᵥ theta ξ) ht
  have h2 : (WithLp.toLp 2 (fun i : Fin n =>
      (mat (rep g) *ᵥ theta ξ) (Sum.inl i) / (mat (rep g) *ᵥ theta ξ) (Sum.inr 0))) = η := h
  rw [h2] at h1
  refine ⟨tsign (rep g) * (mat (rep g) *ᵥ theta ξ) (Sum.inr 0), ?_, ?_⟩
  · exact mul_ne_zero (tsign_ne_zero (rep g)) ht
  · rw [emat, Matrix.smul_mulVec, h1, smul_smul]
    congr 1
    simp [theta]

/-- The Minkowski form of a combination of two boundary null vectors. -/
lemma mform_theta_comb {x y : E n} (hx : x ∈ Sph n) (hy : y ∈ Sph n) (a b : ℝ) :
    mform (a • theta x + b • theta y) (a • theta x + b • theta y)
      = 2 * a * b * (inner ℝ x y - 1) := by
  rw [mform_add_left, mform_add_right, mform_add_right]
  simp only [mform_smul]
  rw [mform_theta_theta_sph x hx, mform_theta_theta_sph y hy, mform_theta_theta_pair,
    mform_theta_theta_pair]
  have h2 : inner ℝ y x = inner ℝ x y := real_inner_comm x y
  rw [h2]; ring

/-- Normalising a timelike vector to the hyperboloid. -/
lemma mink_normalize (v : Fin n ⊕ Fin 1 → ℝ) (hmf : mform v v < 0) :
    Hyper.mink ((Real.sqrt (- mform v v))⁻¹ • v) ((Real.sqrt (- mform v v))⁻¹ • v) = -1 := by
  have hmfne : mform v v ≠ 0 := ne_of_lt hmf
  have hs2 : (Real.sqrt (- mform v v)) ^ 2 = - mform v v := Real.sq_sqrt (by linarith)
  rw [← mform_eq_hyperMink, mform_smul, ← mul_inv, ← sq, hs2, inv_mul_eq_div,
    div_eq_iff (neg_ne_zero.mpr hmfne)]
  ring

lemma time_normalize (v : Fin n ⊕ Fin 1 → ℝ) (hmf : mform v v < 0)
    (hv : 0 < v (Sum.inr 0)) :
    0 < ((Real.sqrt (- mform v v))⁻¹ • v) (Sum.inr 0) := by
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))) hv

/-- A timelike forward eigenvector of `emat g` of eigenvalue `1` gives an interior fixed point. -/
lemma fixed_of_timelike_eigen {g : PO n 1} (hne : ∀ p : E n, g • p ≠ p)
    {v : Fin n ⊕ Fin 1 → ℝ} (hmf : mform v v < 0) (htime : 0 < v (Sum.inr 0))
    (heig : emat g *ᵥ v = v) : False := by
  have hmink := mink_normalize v hmf
  have htim2 := time_normalize v hmf htime
  have hhlift := Hyper.hlift_spat_of_mink _ hmink htim2
  have hfix : emat g *ᵥ ((Real.sqrt (- mform v v))⁻¹ • v)
      = (Real.sqrt (- mform v v))⁻¹ • v := by
    rw [Matrix.mulVec_smul, heig]
  refine hne (Hyper.spat ((Real.sqrt (- mform v v))⁻¹ • v)) ?_
  apply Hyper.hlift_injective
  rw [← emat_hlift, hhlift, hfix]

/-- A timelike forward anti-eigenvector of `emat g` (eigenvalue `-1`) is impossible. -/
lemma contra_of_timelike_antiEigen {g : PO n 1}
    {v : Fin n ⊕ Fin 1 → ℝ} (hmf : mform v v < 0) (htime : 0 < v (Sum.inr 0))
    (heig : emat g *ᵥ v = -v) : False := by
  have hmink := mink_normalize v hmf
  have htim2 := time_normalize v hmf htime
  have hhlift := Hyper.hlift_spat_of_mink _ hmink htim2
  have heig' : emat g *ᵥ ((Real.sqrt (- mform v v))⁻¹ • v)
      = -((Real.sqrt (- mform v v))⁻¹ • v) := by
    rw [Matrix.mulVec_smul, heig, smul_neg]
  have hneg : (emat g *ᵥ ((Real.sqrt (- mform v v))⁻¹ • v)) (Sum.inr 0) < 0 := by
    rw [heig']
    show -(((Real.sqrt (- mform v v))⁻¹ • v) (Sum.inr 0)) < 0
    linarith
  have hpos : 0 < (emat g *ᵥ ((Real.sqrt (- mform v v))⁻¹ • v)) (Sum.inr 0) := by
    rw [← hhlift, emat_hlift]
    simpa only [hlift, Sum.elim_inr] using tpart_pos (g • Hyper.spat _)
  linarith

/-- A fixed-point-free isometry cannot swap the two points of a fixed boundary pair. -/
lemma no_swap_of_preserves_pair {g : PO n 1} {x y : E n}
    (hx : x ∈ Sph n) (hy : y ∈ Sph n) (hxy : x ≠ y)
    (hne : ∀ p : E n, g • p ≠ p)
    (h : (bd g x = x ∧ bd g y = y) ∨ (bd g x = y ∧ bd g y = x)) :
    bd g x = x ∧ bd g y = y := by
  rcases h with hfix | ⟨hxy', hyx'⟩
  · exact hfix
  · exfalso
    obtain ⟨lam, hlamne, hlam⟩ := bd_emat_eigen hx hxy'
    obtain ⟨mu, hmu_ne, hmu⟩ := bd_emat_eigen hy hyx'
    have hmf : mform (theta x) (theta y) ≠ 0 := by
      rw [mform_theta_theta_pair]
      have h1 : inner ℝ x y < 1 :=
        inner_lt_one_of_ne_unit ((mem_Sph_iff x).mp hx) ((mem_Sph_iff y).mp hy) hxy
      intro hh; linarith
    have hprod : lam * mu = 1 := by
      have h2 := mform_emat g (theta x) (theta y)
      rw [hlam, hmu, mform_smul] at h2
      rw [mform_comm (theta y) (theta x)] at h2
      have h3 : (lam * mu - 1) * mform (theta x) (theta y) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · linarith
      · exact absurd h4 hmf
    have hin : inner ℝ x y < 1 :=
      inner_lt_one_of_ne_unit ((mem_Sph_iff x).mp hx) ((mem_Sph_iff y).mp hy) hxy
    rcases lt_trichotomy lam 0 with hlt | heq | hgt
    · -- `lam < 0`: `theta x + (-lam) • theta y` is a timelike anti-eigenvector
      refine contra_of_timelike_antiEigen (g := g)
        (v := (1 : ℝ) • theta x + (-lam) • theta y) ?_ ?_ ?_
      · rw [mform_add_left, mform_add_right, mform_add_right]
        simp only [mform_smul]
        rw [mform_theta_theta_sph x hx, mform_theta_theta_sph y hy, mform_theta_theta_pair,
          mform_theta_theta_pair]
        have h2 : inner ℝ y x = inner ℝ x y := real_inner_comm x y
        rw [h2]; nlinarith
      · simp only [Pi.add_apply, theta, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]; linarith
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu]
        simp only [smul_smul, neg_mul, hprod, neg_smul, one_smul, neg_add, neg_neg, one_mul]
        module
    · exact absurd heq hlamne
    · -- `lam > 0`: `theta x + lam • theta y` is a timelike eigenvector
      refine fixed_of_timelike_eigen hne (v := (1 : ℝ) • theta x + lam • theta y) ?_ ?_ ?_
      · rw [mform_add_left, mform_add_right, mform_add_right]
        simp only [mform_smul]
        rw [mform_theta_theta_sph x hx, mform_theta_theta_sph y hy, mform_theta_theta_pair,
          mform_theta_theta_pair]
        have h2 : inner ℝ y x = inner ℝ x y := real_inner_comm x y
        rw [h2]; nlinarith
      · simp only [Pi.add_apply, theta, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]; linarith
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu]
        simp only [smul_smul, hprod, one_smul, one_mul]
        module

/-! ## Level preservation and flat-coordinate comparison -/

/-- An isometry fixing `ξ` with vanishing Busemann cocycle preserves every level. -/
lemma lev_smul_of_zero_cocycle (hI : HypIsometryProp n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n)
    (hg : bd g ξ = ξ) (hβ : busemann ξ (g • (0 : E n)) = 0) (u : E n) :
    lev ξ (g • u) = lev ξ u := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have h1 := hId.busemann_cocycle g ξ u hξ
  rw [hg, hβ, add_zero] at h1
  rw [lev_eq_exp hξ (g • u), lev_eq_exp hξ u, h1]

/-- Such an isometry also preserves the flat distance of flat coordinates. -/
lemma yc_dist_eq_of_zero_cocycle (hI : HypIsometryProp n) {g : PO n 1} {ξ : E n}
    (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) (hβ : busemann ξ (g • (0 : E n)) = 0) (u v : E n) :
    ‖yc ξ (g • u) - yc ξ (g • v)‖ = ‖yc ξ u - yc ξ v‖ := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hL : ∀ w : E n, lev ξ (g • w) = lev ξ w := lev_smul_of_zero_cocycle hI hξ hg hβ
  have hA := levYcFormula hξ u v
  have hB : Real.cosh (hdist u v) = Real.cosh (Real.log (lev ξ u / lev ξ v)) +
      (lev ξ u * lev ξ v / 2) * ‖yc ξ (g • u) - yc ξ (g • v)‖ ^ 2 := by
    have h := levYcFormula hξ (g • u) (g • v)
    rw [hL u, hL v, hId.isom_smul g u v] at h
    exact h
  have hC : (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖ ^ 2 =
      (lev ξ u * lev ξ v / 2) * ‖yc ξ (g • u) - yc ξ (g • v)‖ ^ 2 := by linarith
  have hpos : (lev ξ u * lev ξ v / 2) ≠ 0 := by
    have h1 := lev_pos ξ hξ u
    have h2 := lev_pos ξ hξ v
    positivity
  have hsq : ‖yc ξ u - yc ξ v‖ ^ 2 = ‖yc ξ (g • u) - yc ξ (g • v)‖ ^ 2 :=
    mul_left_cancel₀ hpos hC
  have hsqrt := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
  exact hsqrt.symm

/-- An isometry fixing two distinct boundary points `x`, `y` with vanishing Busemann cocycle
at `x` has an interior fixed point. -/
lemma exists_fixed_of_two_bd_fixes (hI : HypIsometryProp n) (hPS : PairStabProp n)
    {g : PO n 1} {x y : E n}
    (hx : x ∈ Sph n) (hy : y ∈ Sph n) (hxy : x ≠ y)
    (hfx : bd g x = x) (hfy : bd g y = y) (hβx : busemann x (g • (0 : E n)) = 0) :
    ∃ p : E n, g • p = p := by
  obtain ⟨p, hp⟩ := hPS x y hx hy hxy
  refine ⟨p, ?_⟩
  have h1 : hdist p (g • p) = |busemann x (g • (0 : E n))| := (hp g hfx hfy).1
  rw [hβx, abs_zero] at h1
  exact (((HypIsoData.ofProp hI).eq_zero p (g • p)).1 h1).symm

/-! ## Pigeonhole and finiteness -/

/-- A sequence taking values in a finite set has a value attained infinitely often. -/
lemma exists_frequently_fiber {α : Type*} (f : ℕ → α) (n₀ : ℕ) (S : Set α) (hS : S.Finite)
    (h : ∀ k, n₀ ≤ k → f k ∈ S) : ∃ g : α, ∃ᶠ k : ℕ in Filter.atTop, f k = g := by
  have hex : ∃ g : α, {k : ℕ | f k = g}.Infinite := by
    by_contra hcon
    have hcon' : ∀ g : α, {k : ℕ | f k = g}.Finite := fun g => by
      by_contra hg; exact hcon ⟨g, hg⟩
    have hIci : (Set.Ici n₀ : Set ℕ).Finite := by
      refine (hS.biUnion (fun g _ => hcon' g)).subset ?_
      intro k hk
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨f k, h k (Set.mem_Ici.mp hk), rfl⟩
    exact Set.Ici_infinite n₀ hIci
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, ?_⟩
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨b, hb, hbgt⟩ := hg.exists_gt (max a n₀)
  exact ⟨b, le_trans (le_max_left a n₀) (le_of_lt hbgt), hb⟩

/-- Pushing a frequently-attained value along `k ↦ k + n₀`. -/
lemma frequently_add_imp {p : ℕ → Prop} (n₀ : ℕ)
    (h : ∃ᶠ k : ℕ in Filter.atTop, p (k + n₀)) : ∃ᶠ k : ℕ in Filter.atTop, p k := by
  rw [Filter.frequently_atTop] at h ⊢
  intro a
  obtain ⟨k, hk, hpk⟩ := h a
  exact ⟨k + n₀, le_trans hk (Nat.le_add_right k n₀), hpk⟩

/-- The set of elements of a discrete group moving a fixed point by at most `R` is finite. -/
lemma finite_hdist_orbit_ball (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ)) (c : E n) (R : ℝ) :
    {γ : Γ | hdist c (((γ : Γ) : PO n 1) • c) ≤ R}.Finite := by
  have hP : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hK₂ : IsCompact {v : E n | hdist c v ≤ R} := hId.ball_compact c R
  refine (finite_nearStab_compact (K₁ := {c}) (K₂ := {v : E n | hdist c v ≤ R})
    hP hId hdisc isCompact_singleton hK₂).subset ?_
  intro γ hγ
  exact ⟨c, rfl, ((γ : Γ) : PO n 1) • c, hγ, rfl⟩

/-- Pinning for the parabolic branch: if the elements `δ k ∈ Γ` all fix `ξ ≠ ζ` with zero
Busemann drift and move the ray points `rayN ζ (φ k)` by at most `1`, then in the discrete group
`Γ` some value is attained infinitely often.  (The point is that the flat coordinate of such an
element at the base point stays in a bounded set.) -/
lemma parabolic_pin (hA : POActionProp n) (hI : HypIsometryProp n)
    {ξ ζ : E n} (hξ : ξ ∈ Sph n) (hζ : ζ ∈ Sph n) (hne : ξ ≠ ζ)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (φ : ℕ → ℕ) (δ : ℕ → Γ)
    (hfix : ∀ k, bd (((δ k : Γ) : PO n 1)) ξ = ξ)
    (hβ : ∀ k, busemann ξ (((δ k : Γ) : PO n 1) • (0 : E n)) = 0)
    (hnear : ∀ k, hdist (rayN ζ (φ k)) (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) ≤ 1) :
    ∃ g : Γ, ∃ᶠ k : ℕ in Filter.atTop, δ k = g := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hζn : ‖ζ‖ = 1 := (mem_Sph_iff ζ).mp hζ
  have hc_lt : inner ℝ ζ ξ < 1 :=
    inner_lt_one_of_ne_unit hζn ((mem_Sph_iff ξ).mp hξ) (Ne.symm hne)
  have hLbpos : 0 < min 1 (1 - inner ℝ ζ ξ) := lt_min one_pos (by linarith)
  have hcosh1 : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr one_ne_zero
  have h2nn : 0 ≤ 2 * (Real.cosh 1 - 1) := by linarith
  set B : ℝ := ‖ζ - inner ℝ ζ ξ • ξ‖ / min 1 (1 - inner ℝ ζ ξ) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  set S : ℝ := Real.sqrt (2 * (Real.cosh 1 - 1)) / min 1 (1 - inner ℝ ζ ξ) with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  have hkey : ∀ k, hdist (0 : E n) (((δ k : Γ) : PO n 1) • (0 : E n))
      ≤ Real.arcosh (1 + (2 * B + S) ^ 2 / 2) := by
    intro k
    have hLz : lev ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) = lev ξ (rayN ζ (φ k)) :=
      lev_smul_of_zero_cocycle hI hξ (hfix k) (hβ k) _
    have hL0 : lev ξ (((δ k : Γ) : PO n 1) • (0 : E n)) = lev ξ (0 : E n) :=
      lev_smul_of_zero_cocycle hI hξ (hfix k) (hβ k) 0
    have hlev0 : lev ξ (0 : E n) = 1 := by simp [lev, tpart]
    have hyc0 : yc ξ (0 : E n) = 0 := by simp [yc, wc]
    have hLzpos : 0 < lev ξ (rayN ζ (φ k)) := lev_pos ξ hξ _
    have hLzlow : min 1 (1 - inner ℝ ζ ξ) ≤ lev ξ (rayN ζ (φ k)) := by
      calc min 1 (1 - inner ℝ ζ ξ) = min 1 (1 - inner ℝ ζ ξ) * 1 := (mul_one _).symm
        _ ≤ min 1 (1 - inner ℝ ζ ξ) * Real.cosh (φ k : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.one_le_cosh _) hLbpos.le
        _ ≤ lev ξ (rayN ζ (φ k)) := lev_rayN_lower hζ (φ k)
    -- bound on the middle term
    have hterm2 : ‖yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) - yc ξ (rayN ζ (φ k))‖ ≤ S := by
      set D : ℝ := ‖yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) - yc ξ (rayN ζ (φ k))‖ with hDdef
      have hDnn : 0 ≤ D := by rw [hDdef]; positivity
      have hform := levYcFormula hξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) (rayN ζ (φ k))
      rw [hLz, div_self (ne_of_gt hLzpos), Real.log_one, Real.cosh_zero] at hform
      have hd : hdist (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) (rayN ζ (φ k)) ≤ 1 := by
        rw [hId.symm]; exact hnear k
      have hcosh : Real.cosh (hdist (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) (rayN ζ (φ k)))
          ≤ Real.cosh 1 := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (hId.nonneg _ _), abs_one]; exact hd
      have hL2 : (lev ξ (rayN ζ (φ k))) ^ 2 * D ^ 2 ≤ 2 * (Real.cosh 1 - 1) := by
        rw [← hDdef] at hform
        nlinarith [hform, hcosh]
      have hsq2 : (min 1 (1 - inner ℝ ζ ξ) * D) ^ 2 ≤ 2 * (Real.cosh 1 - 1) := by
        rw [mul_pow]
        calc (min 1 (1 - inner ℝ ζ ξ)) ^ 2 * D ^ 2
            ≤ (lev ξ (rayN ζ (φ k))) ^ 2 * D ^ 2 := by
              have h1 : (min 1 (1 - inner ℝ ζ ξ)) ^ 2
                  ≤ (lev ξ (rayN ζ (φ k))) ^ 2 := by
                simpa only [sq] using mul_self_le_mul_self hLbpos.le hLzlow
              exact mul_le_mul_of_nonneg_right h1 (sq_nonneg D)
          _ ≤ 2 * (Real.cosh 1 - 1) := hL2
      have hs1 : (Real.sqrt (2 * (Real.cosh 1 - 1))) ^ 2 = 2 * (Real.cosh 1 - 1) :=
        Real.sq_sqrt h2nn
      have hstep : min 1 (1 - inner ℝ ζ ξ) * D ≤ Real.sqrt (2 * (Real.cosh 1 - 1)) := by
        have hsq3 : (min 1 (1 - inner ℝ ζ ξ) * D) ^ 2
            ≤ (Real.sqrt (2 * (Real.cosh 1 - 1))) ^ 2 := by
          rw [hs1]; exact hsq2
        have habs := sq_le_sq.mp hsq3
        rw [abs_of_nonneg (mul_nonneg hLbpos.le hDnn),
          abs_of_nonneg (Real.sqrt_nonneg _)] at habs
        exact habs
      rw [hDdef, hSdef, le_div_iff₀ hLbpos]
      linarith [hstep]
    -- terms 1 and 3
    have h13a : ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n))
          - yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k))‖ = ‖yc ξ (rayN ζ (φ k))‖ := by
      rw [yc_dist_eq_of_zero_cocycle hI hξ (hfix k) (hβ k) 0 (rayN ζ (φ k)), hyc0, zero_sub,
        norm_neg]
    have h13b : ‖yc ξ (rayN ζ (φ k)) - yc ξ (0 : E n)‖ = ‖yc ξ (rayN ζ (φ k))‖ := by
      rw [hyc0, sub_zero]
    have hB1 : ‖yc ξ (rayN ζ (φ k))‖ ≤ B := by
      rw [hBdef]; exact norm_yc_rayN_le hξ hζ hne (φ k)
    have htr : ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n)) - yc ξ (0 : E n)‖ ≤ 2 * B + S := by
      have htri : ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n)) - yc ξ (0 : E n)‖
          ≤ ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n))
              - yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k))‖
            + ‖yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) - yc ξ (rayN ζ (φ k))‖
            + ‖yc ξ (rayN ζ (φ k)) - yc ξ (0 : E n)‖ := by
        have h1 : ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n)) - yc ξ (0 : E n)‖
            ≤ ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n))
                - yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k))‖
              + ‖yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) - yc ξ (0 : E n)‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
        have h2 : ‖yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) - yc ξ (0 : E n)‖
            ≤ ‖yc ξ (((δ k : Γ) : PO n 1) • rayN ζ (φ k)) - yc ξ (rayN ζ (φ k))‖
              + ‖yc ξ (rayN ζ (φ k)) - yc ξ (0 : E n)‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
        linarith
      linarith [htri, h13a, h13b, hB1, hterm2]
    -- conclude
    have hcs : Real.cosh (hdist (((δ k : Γ) : PO n 1) • (0 : E n)) (0 : E n))
        ≤ 1 + (2 * B + S) ^ 2 / 2 := by
      have hform := levYcFormula hξ (((δ k : Γ) : PO n 1) • (0 : E n)) (0 : E n)
      rw [hL0, hlev0, div_one, Real.log_one, Real.cosh_zero, hyc0, sub_zero] at hform
      rw [hform]
      have htr' : ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n))‖ ≤ 2 * B + S := by
        simpa only [hyc0, sub_zero] using htr
      have h2 : ‖yc ξ (((δ k : Γ) : PO n 1) • (0 : E n))‖ ^ 2 ≤ (2 * B + S) ^ 2 := by
        simpa only [sq] using mul_self_le_mul_self (norm_nonneg _) htr'
      linarith
    calc hdist (0 : E n) (((δ k : Γ) : PO n 1) • (0 : E n))
        = Real.arcosh (Real.cosh (hdist (0 : E n) (((δ k : Γ) : PO n 1) • (0 : E n)))) :=
          (Real.arcosh_cosh (hId.nonneg _ _)).symm
      _ ≤ Real.arcosh (1 + (2 * B + S) ^ 2 / 2) := by
          rw [Real.arcosh_le_arcosh (Real.cosh_pos _) (by positivity)]
          rw [hId.symm]
          exact hcs
  exact exists_frequently_fiber δ 0 _ (finite_hdist_orbit_ball hA hI hdisc (0 : E n) _)
    (fun k _ => hkey k)

/-- Bounded displacement along the ray to `ζ`, infinitely often, forces `bd g ζ = ζ`
(the "K9 / pin_fix" step). -/
lemma nearId_ray_bd (hA : POActionProp n) (hI : HypIsometryProp n)
    {ζ : E n} (hζ : ζ ∈ Sph n) (g : PO n 1) (C : ℝ)
    (h : ∃ᶠ k : ℕ in Filter.atTop, hdist (rayN ζ k) (g • rayN ζ k) ≤ C) :
    bd g ζ = ζ := by
  obtain ⟨φ, hφ, hφp⟩ := Filter.extraction_of_frequently_atTop
    (h.and_eventually (Filter.eventually_ge_atTop 1))
  have hCnn : 0 ≤ max C 0 := le_max_right _ _
  have hclose : ∀ j : ℕ, hdist (rayN ζ (φ j)) (g • rayN ζ (φ j)) ≤ max C 0 :=
    fun j => le_trans (hφp j).1 (le_max_left _ _)
  have hφR : Filter.Tendsto (fun j : ℕ => ((φ j : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hlvl : Filter.Tendsto (fun j : ℕ => BdExt.lvl (rayN ζ (φ j))) Filter.atTop Filter.atTop := by
    have h1 : (fun j : ℕ => BdExt.lvl (rayN ζ (φ j)))
        = fun j : ℕ => ((φ j : ℕ) : ℝ) := by
      funext j
      rw [BdExt.lvl, show rayN ζ (φ j) = BdExt.ray ζ (φ j : ℝ) from rfl,
        BdExt.hdist_zero_ray ζ hζ (φ j : ℝ) (Nat.cast_nonneg _)]
    rw [h1]; exact hφR
  have hlvl' : Filter.Tendsto (fun j : ℕ => BdExt.lvl (g • rayN ζ (φ j)))
      Filter.atTop Filter.atTop := by
    have hlow : ∀ j, ((φ j : ℕ) : ℝ) - max C 0 ≤ BdExt.lvl (g • rayN ζ (φ j)) := by
      intro j
      have htri := (HypIsoData.ofProp hI).triangle (0 : E n) (g • rayN ζ (φ j)) (rayN ζ (φ j))
      have hz : hdist (0 : E n) (rayN ζ (φ j)) = ((φ j : ℕ) : ℝ) := by
        rw [show rayN ζ (φ j) = BdExt.ray ζ (φ j : ℝ) from rfl,
          BdExt.hdist_zero_ray ζ hζ (φ j : ℝ) (Nat.cast_nonneg _)]
      rw [hz, (HypIsoData.ofProp hI).symm (g • rayN ζ (φ j)) (rayN ζ (φ j))] at htri
      show ((φ j : ℕ) : ℝ) - max C 0 ≤ hdist (0 : E n) (g • rayN ζ (φ j))
      linarith [htri, hclose j]
    exact tendsto_atTop_mono hlow
      (tendsto_atTop_add_const_right Filter.atTop (-(max C 0)) hφR)
  have hdirv : Filter.Tendsto (fun j : ℕ => BdExt.dirv (rayN ζ (φ j))) Filter.atTop (nhds ζ) := by
    refine Filter.Tendsto.congr (fun j => ?_) tendsto_const_nhds
    exact (BdExt.dirv_ray ζ hζ (by exact_mod_cast (hφp j).2)).symm
  have hnorm : Filter.Tendsto (fun j : ℕ => ‖rayN ζ (φ j)‖) Filter.atTop Filter.atTop := by
    have hζn : ‖ζ‖ = 1 := (mem_Sph_iff ζ).mp hζ
    have h1 : (fun j : ℕ => ‖rayN ζ (φ j)‖) = fun j : ℕ => Real.sinh ((φ j : ℕ) : ℝ) := by
      funext j
      rw [rayN, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sinh_nonneg_iff.mpr (Nat.cast_nonneg _)), hζn, mul_one]
    rw [h1]
    exact BdExt.tendsto_sinh_atTop'.comp hφR
  have hdirv1 := BdExt.closeSeq n hI (fun j => rayN ζ (φ j)) (fun j => g • rayN ζ (φ j))
    (max C 0) hCnn hclose hlvl hlvl' ζ hdirv
  have hdirv2 := BdExt.isomConv n hA hI g (fun j => rayN ζ (φ j)) ζ hζ hnorm hdirv
  exact tendsto_nhds_unique hdirv2 hdirv1

end

end Work.Mostow
