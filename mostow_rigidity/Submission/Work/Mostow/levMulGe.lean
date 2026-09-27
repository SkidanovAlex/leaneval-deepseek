import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# `1 - ⟪ξ,η⟫ ≤ 2 · lev ξ u · lev η u`

The Busemann-level (horospherical) inequality used to control the flat coordinates of the
Besson–Courtois–Gallot natural map: for two points `ξ η` of the boundary sphere and any
`u : ℍⁿ` the hyperbolic cosine identity

`2 (lev ξ u) (lev η u) ≥ 1 - ⟪ξ,η⟫`

holds, i.e. the product of the two horospherical levels through `u` dominates half the
flat distance `‖ξ - η‖²/2` between the boundary points.  Equivalently, in the hyperboloid
model, for the null vectors `X = nvec ξ = (ξ,1)`, `Y = nvec η = (η,1)` and the timelike
`U = hlift u` with `⟨U,U⟩ = -1`:

`-⟨X,Y⟩ ≤ 2 ⟨U,X⟩⟨U,Y⟩`.

## Proof

Project `X` and `Y` to `U^⊥`: with `α = ⟨U,X⟩`, `β = ⟨U,Y⟩`, put `z = X + α U` and
`w = Y + β U`.  Then `⟨z,U⟩ = ⟨w,U⟩ = 0` and `⟨z,z⟩ = α²`, `⟨w,w⟩ = β²`.  The Minkowski
form is positive definite on `U^⊥` (reverse Cauchy–Schwarz: `mink_self_nonneg_of_orth`),
so `⟨βz + αw, βz + αw⟩ ≥ 0`.  Expanding and using `⟨z,w⟩ = ⟨X,Y⟩ + αβ` gives
`0 ≤ 4α²β² + 2αβ⟨X,Y⟩ = 2αβ(2αβ + ⟨X,Y⟩)`, and since `α,β < 0` this is
`⟨X,Y⟩ ≥ -2αβ`, i.e. `1 - ⟪ξ,η⟫ ≤ 2αβ = 2 (lev ξ u)(lev η u)`.
-/

namespace Work.Mostow

open Submission.Mostow

/-! ## Minkowski-form toolkit -/

/-- The spatial part of an ambient vector. -/
private noncomputable def lspat {n : ℕ} (W : Fin n ⊕ Fin 1 → ℝ) : E n :=
  WithLp.toLp 2 (fun i => W (Sum.inl i))

/-- The time coordinate of an ambient vector. -/
private def ltco {n : ℕ} (W : Fin n ⊕ Fin 1 → ℝ) : ℝ := W (Sum.inr 0)

@[simp] private lemma lspat_hlift {n : ℕ} (u : E n) : lspat (hlift u) = u := rfl
@[simp] private lemma ltco_hlift {n : ℕ} (u : E n) : ltco (hlift u) = tpart u := rfl
@[simp] private lemma lspat_nvec {n : ℕ} (ξ : E n) : lspat (nvec ξ) = ξ := rfl
@[simp] private lemma ltco_nvec {n : ℕ} (ξ : E n) : ltco (nvec ξ) = 1 := rfl

private lemma tpart_sq' {n : ℕ} (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := Real.sq_sqrt (by positivity)

private lemma tpart_pos' {n : ℕ} (u : E n) : 0 < tpart u := Real.sqrt_pos.2 (by positivity)

/-- `mink` in terms of the spatial part and the time coordinate. -/
private lemma mink_spatial {n : ℕ} (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x y = inner ℝ (lspat x) (lspat y) - ltco x * ltco y := by
  rw [mink]
  congr 1
  rw [PiLp.inner_apply]
  simp only [lspat, WithLp.ofLp_toLp, Real.inner_apply]

private lemma mink_comm {n : ℕ} (x y : Fin n ⊕ Fin 1 → ℝ) : mink x y = mink y x := by
  simp only [mink]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ring

private lemma mink_smul_left {n : ℕ} (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) y = r * mink x y := by
  simp only [mink, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

private lemma mink_smul_right {n : ℕ} (x : Fin n ⊕ Fin 1 → ℝ) (r : ℝ) (y : Fin n ⊕ Fin 1 → ℝ) :
    mink x (r • y) = r * mink x y := by
  rw [mink_comm x (r • y), mink_smul_left, mink_comm]

private lemma mink_add_left {n : ℕ} (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink (x + y) z = mink x z + mink y z := by
  simp only [mink, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma mink_add_right {n : ℕ} (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink x (y + z) = mink x y + mink x z := by
  rw [mink_comm x (y + z), mink_add_left, mink_comm y x, mink_comm z x]

/-! ## Pairings of the basic vectors -/

/-- The hyperboloid lift of `u` is timelike of square `-1`. -/
private lemma mink_hlift_self {n : ℕ} (u : E n) : mink (hlift u) (hlift u) = -1 := by
  simp only [mink_spatial, lspat_hlift, ltco_hlift, real_inner_self_eq_norm_sq]
  have h := tpart_sq' u
  nlinarith

/-- `⟨nvec ξ, hlift u⟩ = - lev ξ u`. -/
private lemma mink_nvec_hlift {n : ℕ} (ξ u : E n) : mink (nvec ξ) (hlift u) = - lev ξ u := by
  simp only [mink_spatial, lspat_nvec, lspat_hlift, ltco_nvec, ltco_hlift, lev]
  rw [real_inner_comm ξ u]
  ring

/-- The null vector `nvec ξ` is Minkowski-null iff `ξ ∈ Sph n`. -/
private lemma mink_nvec_self {n : ℕ} (ξ : E n) : mink (nvec ξ) (nvec ξ) = ‖ξ‖ ^ 2 - 1 := by
  simp only [mink_spatial, lspat_nvec, ltco_nvec, real_inner_self_eq_norm_sq]
  ring

/-- `⟨nvec ξ, nvec η⟩ = ⟪ξ,η⟫ - 1`. -/
private lemma mink_nvec_nvec {n : ℕ} (ξ η : E n) :
    mink (nvec ξ) (nvec η) = inner ℝ ξ η - 1 := by
  simp only [mink_spatial, lspat_nvec, ltco_nvec]
  ring

/-! ## Reverse Cauchy–Schwarz: `U^⊥` is spacelike -/

/-- If `mink W (hlift u) = 0` then `mink W W ≥ 0`: the orthogonal complement of a timelike
vector is positive semidefinite. -/
private lemma mink_self_nonneg_of_orth {n : ℕ} (u : E n) (W : Fin n ⊕ Fin 1 → ℝ)
    (h : mink W (hlift u) = 0) : 0 ≤ mink W W := by
  simp only [mink_spatial, lspat_hlift, ltco_hlift] at h ⊢
  have hvv : inner ℝ (lspat W) (lspat W) = ‖lspat W‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hc : 0 ≤ inner ℝ (lspat W) (lspat W) := by rw [hvv]; positivity
  have key : (inner ℝ (lspat W) u) ^ 2 ≤ ‖lspat W‖ ^ 2 * ‖u‖ ^ 2 := by
    have h1 := real_inner_mul_inner_self_le (lspat W) u
    rw [← pow_two] at h1
    rw [real_inner_self_eq_norm_sq (lspat W), real_inner_self_eq_norm_sq u] at h1
    exact h1
  have hts : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := tpart_sq' u
  have hab : inner ℝ (lspat W) u = ltco W * tpart u := by linarith
  have hnum : 0 ≤ tpart u ^ 2 * inner ℝ (lspat W) (lspat W) - (inner ℝ (lspat W) u) ^ 2 := by
    rw [hvv]; nlinarith [key, hts, hc]
  have hkey : inner ℝ (lspat W) (lspat W) - ltco W * ltco W
      = (tpart u ^ 2 * inner ℝ (lspat W) (lspat W) - (inner ℝ (lspat W) u) ^ 2)
        / tpart u ^ 2 := by
    have hd : tpart u ^ 2 ≠ 0 := ne_of_gt (pow_pos (tpart_pos' u) 2)
    rw [eq_div_iff hd, hab]
    ring
  rw [hkey]
  exact div_nonneg hnum (by positivity)

/-! ## The level inequality -/

theorem levMulGe (n : ℕ) {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hη : η ∈ Submission.Mostow.Sph n) (u : Submission.Mostow.E n) :
    1 - inner ℝ ξ η ≤ 2 * Work.Mostow.lev ξ u * Work.Mostow.lev η u := by
  have hξn : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hηn : ‖η‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hη
  set U : Fin n ⊕ Fin 1 → ℝ := hlift u with hU
  set X : Fin n ⊕ Fin 1 → ℝ := nvec ξ with hX
  set Y : Fin n ⊕ Fin 1 → ℝ := nvec η with hY
  set α : ℝ := mink U X with hα
  set β : ℝ := mink U Y with hβ
  have hUU : mink U U = -1 := by rw [hU]; exact mink_hlift_self u
  have hXX : mink X X = 0 := by rw [hX, mink_nvec_self, hξn]; norm_num
  have hYY : mink Y Y = 0 := by rw [hY, mink_nvec_self, hηn]; norm_num
  have hUX : mink U X = α := hα
  have hXU : mink X U = α := by rw [mink_comm, hUX]
  have hUY : mink U Y = β := hβ
  have hYU : mink Y U = β := by rw [mink_comm, hUY]
  have hXY : mink X Y = inner ℝ ξ η - 1 := by rw [hX, hY, mink_nvec_nvec]
  have hαv : α = - lev ξ u := by rw [hα, hU, hX, mink_comm, mink_nvec_hlift]
  have hβv : β = - lev η u := by rw [hβ, hU, hY, mink_comm, mink_nvec_hlift]
  have hαneg : α < 0 := by rw [hαv]; linarith [lev_pos ξ hξ u]
  have hβneg : β < 0 := by rw [hβv]; linarith [lev_pos η hη u]
  -- the projections of `X`, `Y` to `U^⊥`
  set z : Fin n ⊕ Fin 1 → ℝ := X + α • U with hz
  set w : Fin n ⊕ Fin 1 → ℝ := Y + β • U with hw
  have hzU : mink z U = 0 := by
    simp only [hz, mink_add_left, mink_smul_left]
    rw [hXU, hUU]; ring
  have hwU : mink w U = 0 := by
    simp only [hw, mink_add_left, mink_smul_left]
    rw [hYU, hUU]; ring
  have hzz : mink z z = α ^ 2 := by
    simp only [hz, mink_add_left, mink_add_right, mink_smul_left, mink_smul_right]
    rw [hXX, hXU, hUX, hUU]; ring
  have hww : mink w w = β ^ 2 := by
    simp only [hw, mink_add_left, mink_add_right, mink_smul_left, mink_smul_right]
    rw [hYY, hYU, hUY, hUU]; ring
  have hzw : mink z w = mink X Y + α * β := by
    simp only [hz, hw, mink_add_left, mink_add_right, mink_smul_left, mink_smul_right]
    rw [hXU, hUY, hUU]; ring
  -- `v = β z + α w` is tangent to the hyperboloid, hence Minkowski-nonnegative
  set v : Fin n ⊕ Fin 1 → ℝ := β • z + α • w with hv
  have hvU : mink v U = 0 := by
    simp only [hv, mink_add_left, mink_smul_left]
    rw [hzU, hwU]; ring
  have hpsd : 0 ≤ mink v v := mink_self_nonneg_of_orth u v (by rw [← hU]; exact hvU)
  have hvv : mink v v = 2 * α * β * (2 * α * β + mink X Y) := by
    simp only [hv, mink_add_left, mink_add_right, mink_smul_left, mink_smul_right]
    rw [mink_comm w z, hzz, hww, hzw]
    ring
  have hbpos : 0 < 2 * α * β := by
    have hp : 0 < α * β := mul_pos_of_neg_of_neg hαneg hβneg
    nlinarith
  have hfin : 0 ≤ 2 * α * β + mink X Y := by
    have h1 : 0 ≤ 2 * α * β * (2 * α * β + mink X Y) := by rw [← hvv]; exact hpsd
    exact (mul_nonneg_iff_of_pos_left hbpos).mp h1
  have hmXY : 1 - inner ℝ ξ η ≤ 2 * α * β := by
    have h2 := hfin
    rw [hXY] at h2
    linarith
  calc 1 - inner ℝ ξ η ≤ 2 * α * β := hmXY
    _ = 2 * lev ξ u * lev η u := by rw [hαv, hβv]; ring

end Work.Mostow
