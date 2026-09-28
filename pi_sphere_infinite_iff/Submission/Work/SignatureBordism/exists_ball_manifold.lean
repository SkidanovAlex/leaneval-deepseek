import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# The closed ball `D^{n+1}` as a smooth manifold with boundary

This file constructs, for every `n : ℕ`, a `ChartedSpace` structure on the closed unit ball
`Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1` modelled on the half-space
`EuclideanHalfSpace (n+1)`, for which the ball is a smooth (`C^∞`) manifold with boundary.

The atlas consists of

* `2 * (n+1)` "half-ball" charts, indexed by a coordinate direction `i : Fin (n+1)` and a sign
  `b : Bool`: the chart is defined on the half-ball `{x | 0 < s * x i}` (where `s = ±1` is the
  sign) and is the radial "flattening" map `x ↦ (1 - ‖x‖, x_{≠i})`;
* one chart around the centre `0`, given by the translation `x ↦ x + (1/2) e₀`.

All transition maps are explicit compositions of smooth functions (norms away from the origin,
square roots of positive functions and continuous linear maps), whence the smooth structure.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Metric WithLp
open Classical

set_option maxHeartbeats 4000000

namespace Work.SignatureBordism

/-! ## Elementary continuous linear maps on `ℝ^{n+1}` -/

/-- The canonical continuous linear equivalence `ℝ^m ≃ (Fin m → ℝ)`. -/
abbrev euclToPi (m : ℕ) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] ((j : Fin m) → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)

/-- The canonical continuous linear equivalence `(Fin m → ℝ) ≃ ℝ^m`. -/
abbrev piToEucl (m : ℕ) : ((j : Fin m) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (euclToPi m).symm

/-- `Fin.tail` as a continuous linear map. -/
def tailCLM (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (piToEucl n).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k : Fin n =>
      (ContinuousLinearMap.proj k.succ).comp (euclToPi (n + 1)).toContinuousLinearMap)

/-- `Fin.cons` as a continuous linear map. -/
def consCLM (n : ℕ) : ℝ × EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (piToEucl (n + 1)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin (n + 1) =>
      Fin.cases (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
        (fun k => (ContinuousLinearMap.proj k).comp
          ((euclToPi n).toContinuousLinearMap.comp
            (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))))) j)

lemma tailCLM_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (k : Fin n) :
    tailCLM n x k = x k.succ := by
  simp [tailCLM, piToEucl, euclToPi]

lemma consCLM_apply_zero (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    consCLM n (a, z) 0 = a := by
  simp [consCLM, piToEucl, euclToPi]

lemma consCLM_apply_succ (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    consCLM n (a, z) k.succ = z k := by
  simp [consCLM, piToEucl, euclToPi]

lemma tailCLM_consCLM (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    tailCLM n (consCLM n (a, z)) = z := by
  ext k
  rw [tailCLM_apply, consCLM_apply_succ]

lemma consCLM_tail (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    consCLM n (x 0, tailCLM n x) = x := by
  ext j
  induction j using Fin.cases with
  | zero => rw [consCLM_apply_zero]
  | succ k => rw [consCLM_apply_succ, tailCLM_apply]

lemma consCLM_sub (n : ℕ) (a a' : ℝ) (z z' : EuclideanSpace ℝ (Fin n)) :
    consCLM n (a, z) - consCLM n (a', z') = consCLM n (a - a', z - z') := by
  rw [← map_sub, Prod.mk_sub_mk]

lemma norm_sq_consCLM (n : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖consCLM n (a, z)‖ ^ 2 = a ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succAbove _ 0]
  rw [Fin.succAbove_zero]
  simp only [consCLM_apply_zero, consCLM_apply_succ, Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The norm of a vector is the norm of its `cons` decomposition. -/
lemma norm_sq_eq_zero_coord_add (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + ‖tailCLM n x‖ ^ 2 := by
  rw [← norm_sq_consCLM n (x 0) (tailCLM n x), consCLM_tail]

/-- A vector whose `0`-th coordinate is non-zero has `tail` of strictly smaller norm. -/
lemma norm_tailCLM_lt (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x 0 ≠ 0) :
    ‖tailCLM n x‖ < ‖x‖ := by
  have h := norm_sq_eq_zero_coord_add n x
  have h2 : (0 : ℝ) < (x 0) ^ 2 := sq_pos_of_ne_zero hx
  have h3 : ‖tailCLM n x‖ ^ 2 < ‖x‖ ^ 2 := by nlinarith [norm_nonneg (tailCLM n x)]
  nlinarith [norm_nonneg (tailCLM n x), norm_nonneg x]

/-- The coordinate permutation of `ℝ^{n+1}` interchanging the `0`-th and `i`-th coordinates. -/
def permIso (n : ℕ) (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin (n + 1)) i)

lemma permIso_apply (n : ℕ) (i : Fin (n + 1)) (v : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) : permIso n i v j = v (Equiv.swap 0 i j) := by
  rw [permIso, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.symm_swap]

lemma permIso_apply_zero (n : ℕ) (i : Fin (n + 1)) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    permIso n i v 0 = v i := by
  rw [permIso_apply, Equiv.swap_apply_left]

lemma permIso_symm (n : ℕ) (i : Fin (n + 1)) : (permIso n i).symm = permIso n i := by
  rw [permIso, LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.symm_swap]

lemma permIso_invol (n : ℕ) (i : Fin (n + 1)) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    permIso n i (permIso n i v) = v := by
  ext j
  rw [permIso_apply, permIso_apply, Equiv.swap_apply_self]

/-- The `i`-th coordinate of a permuted vector. -/
lemma permIso_apply_self (n : ℕ) (i : Fin (n + 1)) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    permIso n i v i = v 0 := by
  rw [permIso_apply, Equiv.swap_apply_right]

lemma permIso_norm (n : ℕ) (i : Fin (n + 1)) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖permIso n i v‖ = ‖v‖ :=
  (permIso n i).norm_map v

/-! ## The model space and the ball -/

/-- The closed unit ball in `ℝ^{n+1}`. -/
abbrev Ball (n : ℕ) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The half-space of dimension `n+1`. -/
abbrev Half (n : ℕ) := EuclideanHalfSpace (n + 1)

/-- The model with corners of the half-space. -/
abbrev hModel (n : ℕ) : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Half n) :=
  modelWithCornersEuclideanHalfSpace (n + 1)

lemma norm_le_one (n : ℕ) (x : Ball n) : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
  rw [← dist_zero_right (x : EuclideanSpace ℝ (Fin (n + 1)))]
  exact x.2

lemma mem_half_iff (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    y ∈ Set.range (hModel n) ↔ 0 ≤ y 0 := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact Iff.rfl

lemma halfModel_symm_apply_of_le (n : ℕ) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : 0 ≤ x 0) :
    (hModel n).symm x = ⟨x, hx⟩ :=
  modelWithCornersEuclideanHalfSpace_symm_apply_of_le hx


/-! ## Signs -/

/-- The real number attached to a Boolean sign: `1` for `true`, `-1` for `false`. -/
def bsign (b : Bool) : ℝ := if b then 1 else -1

lemma bsign_mul_self (b : Bool) : bsign b * bsign b = 1 := by
  cases b <;> norm_num [bsign]

lemma bsign_ne_zero (b : Bool) : bsign b ≠ 0 := by
  intro h
  have h' := bsign_mul_self b
  rw [h, zero_mul] at h'
  exact one_ne_zero h'.symm

lemma bsign_eq_one_or_neg_one (b : Bool) : bsign b = 1 ∨ bsign b = -1 := by
  cases b <;> simp [bsign]

/-- For a sign `σ` with `σ * t > 0`, one has `σ * |t| = t`. -/
lemma bsign_mul_abs {b : Bool} {t : ℝ} (h : 0 < bsign b * t) : bsign b * |t| = t := by
  rcases bsign_eq_one_or_neg_one b with h1 | h1
  · rw [h1, one_mul] at h ⊢
    rw [abs_of_pos h]
  · rw [h1, neg_mul] at h ⊢
    rw [abs_of_neg (by linarith)]
    ring

lemma bsign_mul_mul {b : Bool} (t : ℝ) : bsign b * (bsign b * t) = t := by
  rw [← mul_assoc, bsign_mul_self, one_mul]

/-! ## The half-ball charts: data -/

/-- The source of the half-ball chart indexed by the coordinate `i` and the sign `b`:
the half-ball on the side `b` of the hyperplane `x i = 0`. -/
def halfSource (n : ℕ) (i : Fin (n + 1)) (b : Bool) : Set (Ball n) :=
  {x | 0 < bsign b * (x : EuclideanSpace ℝ (Fin (n + 1))) i}

/-- The (common) target of the half-ball charts. -/
def halfTarget (n : ℕ) : Set (Half n) :=
  {y | ‖tailCLM n y.val‖ + y.val 0 < 1}

/-- The forward formula of the half-ball chart, as a total map on `ℝ^{n+1}`. -/
def halfToFunE (n : ℕ) (i : Fin (n + 1)) (b : Bool) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  consCLM n (1 - ‖x‖, tailCLM n (permIso n i x))

/-- The inverse formula of the half-ball chart, as a total map on `ℝ^{n+1}`. -/
def halfInvRawE (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  permIso n i (consCLM n (bsign b * Real.sqrt ((1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2),
    tailCLM n y))

/-- The transition formula between two half-ball charts, as a total map on `ℝ^{n+1}`. -/
def halfTransFun (n : ℕ) (j j' : Fin (n + 1) × Bool)
    (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  consCLM n (1 - ‖halfInvRawE n j.1 j.2 y‖,
    tailCLM n (permIso n j'.1 (halfInvRawE n j.1 j.2 y)))

lemma halfToFunE_apply (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    halfToFunE n i b x = consCLM n (1 - ‖x‖, tailCLM n (permIso n i x)) := rfl

lemma halfToFunE_zero (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : halfToFunE n i b x 0 = 1 - ‖x‖ := by
  rw [halfToFunE_apply, consCLM_apply_zero]

lemma halfInvRawE_apply (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    halfInvRawE n i b y
      = permIso n i (consCLM n (bsign b * Real.sqrt ((1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2),
          tailCLM n y)) := rfl

lemma halfInvRawE_coord (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    halfInvRawE n i b y i = bsign b * Real.sqrt ((1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2) := by
  rw [halfInvRawE_apply, permIso_apply_self, consCLM_apply_zero]

/-- Membership in the target of the half-ball charts. -/
lemma halfTarget_iff (n : ℕ) (y : Half n) :
    y ∈ halfTarget n ↔ ‖tailCLM n y.val‖ + y.val 0 < 1 := Iff.rfl

lemma halfTarget_tail_lt (n : ℕ) {y : Half n} (hy : y ∈ halfTarget n) :
    ‖tailCLM n y.val‖ < 1 - y.val 0 := by
  have h := hy
  rw [halfTarget_iff] at h
  linarith

lemma half_coord_nonneg (n : ℕ) (y : Half n) : 0 ≤ y.val 0 := y.property

lemma halfTarget_one_sub_pos (n : ℕ) {y : Half n} (hy : y ∈ halfTarget n) :
    0 < 1 - y.val 0 := by
  have h1 := halfTarget_tail_lt n hy
  have h2 : (0 : ℝ) ≤ ‖tailCLM n y.val‖ := norm_nonneg _
  have h3 := half_coord_nonneg n y
  linarith

lemma halfTarget_g_pos (n : ℕ) {y : Half n} (hy : y ∈ halfTarget n) :
    0 < (1 - y.val 0) ^ 2 - ‖tailCLM n y.val‖ ^ 2 := by
  have h1 := halfTarget_tail_lt n hy
  have h2 := halfTarget_one_sub_pos n hy
  nlinarith [norm_nonneg (tailCLM n y.val)]

/-- The target condition, as a statement about an ambient vector. -/
lemma halfTarget_mem_iff (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : 0 ≤ y 0) :
    (⟨y, hy⟩ : Half n) ∈ halfTarget n ↔ ‖tailCLM n y‖ + y 0 < 1 := Iff.rfl

/-! ## The interior chart: data -/

/-- The centre-shift vector `(1/2) e₀`. -/
def shiftE (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := consCLM n (1 / 2, 0)

/-- The source of the interior chart: a neighbourhood of the centre inside the open ball. -/
def interiorSource (n : ℕ) : Set (Ball n) :=
  {x | -(1 / 2 : ℝ) < (x : EuclideanSpace ℝ (Fin (n + 1))) 0
        ∧ ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1}

/-- The target of the interior chart. -/
def interiorTarget (n : ℕ) : Set (Half n) :=
  {y | 0 < y.val 0 ∧ ‖y.val - shiftE n‖ < 1}

/-- The forward formula of the interior chart. -/
def interiorToFunE (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  consCLM n (max (x 0 + 1 / 2) 0, tailCLM n x)

/-- The inverse formula of the interior chart. -/
def interiorInvRawE (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) := y - shiftE n

lemma consCLM_add (n : ℕ) (a a' : ℝ) (z z' : EuclideanSpace ℝ (Fin n)) :
    consCLM n (a, z) + consCLM n (a', z') = consCLM n (a + a', z + z') := by
  rw [← map_add, Prod.mk_add_mk]

lemma shiftE_apply_zero (n : ℕ) : shiftE n 0 = 1 / 2 := by
  rw [shiftE, consCLM_apply_zero]

lemma shiftE_apply_succ (n : ℕ) (k : Fin n) : shiftE n k.succ = 0 := by
  rw [shiftE, consCLM_apply_succ]
  rfl

lemma interiorToFunE_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    interiorToFunE n x = consCLM n (max (x 0 + 1 / 2) 0, tailCLM n x) := rfl

lemma interiorToFunE_coord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    interiorToFunE n x 0 = max (x 0 + 1 / 2) 0 := by
  rw [interiorToFunE_apply, consCLM_apply_zero]

lemma consCLM_add_const (n : ℕ) (a c : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    consCLM n (a + c, z) = consCLM n (a, z) + consCLM n (c, 0) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [consCLM_apply_zero]
  | succ k => simp [consCLM_apply_succ]

lemma interiorToFunE_eq_of_pos (n : ℕ) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : -(1 / 2 : ℝ) < x 0) : interiorToFunE n x = x + shiftE n := by
  have h : 0 < x 0 + 1 / 2 := by linarith
  calc interiorToFunE n x
      = consCLM n (x 0 + 1 / 2, tailCLM n x) := by
        rw [interiorToFunE_apply, max_eq_left h.le]
    _ = consCLM n (x 0, tailCLM n x) + consCLM n (1 / 2, 0) :=
        consCLM_add_const n (x 0) (1 / 2) (tailCLM n x)
    _ = x + shiftE n := by rw [consCLM_tail]; rfl

lemma interiorInvRawE_coord (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    interiorInvRawE n y 0 = y 0 - 1 / 2 := by
  rw [interiorInvRawE]
  simp [shiftE, consCLM_apply_zero]


/-! ## The half-ball charts -/

lemma ne_zero_of_bsign_mul_pos {b : Bool} {t : ℝ} (h : 0 < bsign b * t) : t ≠ 0 := by
  intro ht
  rw [ht, mul_zero] at h
  exact absurd h (lt_irrefl 0)

lemma halfInvRawE_norm_sq (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) :
    ‖halfInvRawE n i b y.val‖ ^ 2 = (1 - y.val 0) ^ 2 := by
  have hg : (0 : ℝ) ≤ (1 - y.val 0) ^ 2 - ‖tailCLM n y.val‖ ^ 2 := (halfTarget_g_pos n hy).le
  have hσ : (bsign b * Real.sqrt ((1 - y.val 0) ^ 2 - ‖tailCLM n y.val‖ ^ 2)) ^ 2
      = (1 - y.val 0) ^ 2 - ‖tailCLM n y.val‖ ^ 2 := by
    rw [mul_pow, sq, bsign_mul_self, one_mul, Real.sq_sqrt hg]
  rw [halfInvRawE_apply, permIso_norm, norm_sq_consCLM, hσ]
  ring

lemma halfInvRawE_norm (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) : ‖halfInvRawE n i b y.val‖ = 1 - y.val 0 := by
  have h1 := halfInvRawE_norm_sq n i b hy
  have h2 : (0 : ℝ) ≤ 1 - y.val 0 := (halfTarget_one_sub_pos n hy).le
  rw [← abs_of_nonneg (norm_nonneg _), ← Real.sqrt_sq_eq_abs, h1, Real.sqrt_sq_eq_abs,
    abs_of_nonneg h2]

lemma halfInv_ball_mem (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Half n)
    (hy : y ∈ halfTarget n) :
    halfInvRawE n i b y.val ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, halfInvRawE_norm n i b hy]
  have h := half_coord_nonneg n y
  linarith

lemma halfToFunE_coord_nonneg (n : ℕ) (i : Fin (n + 1)) (b : Bool) (x : Ball n) :
    0 ≤ halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
  rw [halfToFunE_zero]
  exact sub_nonneg.mpr (norm_le_one n x)

/-- The forward map of the half-ball chart at `(i,b)`. -/
def halfToFun (n : ℕ) (i : Fin (n + 1)) (b : Bool) (x : Ball n) : Half n :=
  ⟨halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1))), halfToFunE_coord_nonneg n i b x⟩

lemma halfToFun_val (n : ℕ) (i : Fin (n + 1)) (b : Bool) (x : Ball n) :
    (halfToFun n i b x).val = halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-- The inverse of the half-ball chart, restricted to its target. -/
def halfInvFunOnTarget (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Half n)
    (hy : y ∈ halfTarget n) : Ball n :=
  ⟨halfInvRawE n i b y.val, halfInv_ball_mem n i b y hy⟩

/-- The inverse map of the half-ball chart at `(i,b)`. -/
def halfInvFun (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Half n) : Ball n :=
  dite (y ∈ halfTarget n) (halfInvFunOnTarget n i b y) (fun _ => ⟨0, by simp⟩)

lemma halfInvFun_apply (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Half n) :
    halfInvFun n i b y
      = dite (y ∈ halfTarget n) (halfInvFunOnTarget n i b y) (fun _ => ⟨0, by simp⟩) := rfl

lemma halfInvFun_val_of_mem (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) : (halfInvFun n i b y).val = halfInvRawE n i b y.val := by
  rw [halfInvFun_apply, dif_pos hy]
  rfl

lemma halfInvFunOnTarget_val (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Half n)
    (hy : y ∈ halfTarget n) :
    (halfInvFunOnTarget n i b y hy).val = halfInvRawE n i b y.val := rfl

lemma halfToFunE_halfInvRawE (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) : halfToFunE n i b (halfInvRawE n i b y.val) = y.val := by
  calc halfToFunE n i b (halfInvRawE n i b y.val)
      = consCLM n (1 - ‖halfInvRawE n i b y.val‖,
          tailCLM n (permIso n i (halfInvRawE n i b y.val))) := rfl
    _ = consCLM n (1 - (1 - y.val 0), tailCLM n y.val) := by
          rw [halfInvRawE_norm n i b hy, halfInvRawE_apply, permIso_invol, tailCLM_consCLM]
    _ = y.val := by
          rw [show (1 : ℝ) - (1 - y.val 0) = y.val 0 by ring, consCLM_tail]

lemma halfInvRawE_halfToFunE (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : 0 < bsign b * x i) :
    halfInvRawE n i b (halfToFunE n i b x) = x := by
  have hg : (1 - (halfToFunE n i b x) 0) ^ 2 - ‖tailCLM n (halfToFunE n i b x)‖ ^ 2
      = (permIso n i x 0) ^ 2 := by
    rw [halfToFunE_zero, halfToFunE_apply, tailCLM_consCLM]
    have h := norm_sq_eq_zero_coord_add n (permIso n i x)
    have h2 : ‖permIso n i x‖ = ‖x‖ := permIso_norm n i x
    rw [h2] at h
    nlinarith [h]
  have hcoord : bsign b * Real.sqrt ((1 - (halfToFunE n i b x) 0) ^ 2
      - ‖tailCLM n (halfToFunE n i b x)‖ ^ 2) = x i := by
    rw [hg, Real.sqrt_sq_eq_abs, permIso_apply_zero]
    exact bsign_mul_abs hx
  calc halfInvRawE n i b (halfToFunE n i b x)
      = permIso n i (consCLM n (bsign b * Real.sqrt ((1 - (halfToFunE n i b x) 0) ^ 2
          - ‖tailCLM n (halfToFunE n i b x)‖ ^ 2), tailCLM n (halfToFunE n i b x))) := rfl
    _ = permIso n i (consCLM n (x i, tailCLM n (permIso n i x))) := by
          rw [hcoord, halfToFunE_apply, tailCLM_consCLM]
    _ = permIso n i (permIso n i x) := by
          rw [← permIso_apply_zero n i x, consCLM_tail]
    _ = x := permIso_invol n i x

lemma halfToFun_mem_target (n : ℕ) (i : Fin (n + 1)) (b : Bool) {x : Ball n}
    (hx : x ∈ halfSource n i b) : halfToFun n i b x ∈ halfTarget n := by
  show ‖tailCLM n (halfToFun n i b x).val‖ + (halfToFun n i b x).val 0 < 1
  rw [halfToFun_val, halfToFunE_zero, halfToFunE_apply, tailCLM_consCLM]
  have hxi : (x : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0 := ne_zero_of_bsign_mul_pos hx
  have h0 : (permIso n i (x : EuclideanSpace ℝ (Fin (n + 1)))) 0 ≠ 0 := by
    rw [permIso_apply_zero]; exact hxi
  have hlt := norm_tailCLM_lt n (permIso n i (x : EuclideanSpace ℝ (Fin (n + 1)))) h0
  have hnm := permIso_norm n i (x : EuclideanSpace ℝ (Fin (n + 1)))
  linarith

lemma halfInvFun_mem_source (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) : halfInvFun n i b y ∈ halfSource n i b := by
  show 0 < bsign b * (halfInvFun n i b y).val i
  rw [halfInvFun_val_of_mem n i b hy, halfInvRawE_coord, bsign_mul_mul]
  exact Real.sqrt_pos.mpr (halfTarget_g_pos n hy)

lemma halfInvFun_left_inv (n : ℕ) (i : Fin (n + 1)) (b : Bool) {x : Ball n}
    (hx : x ∈ halfSource n i b) : halfInvFun n i b (halfToFun n i b x) = x := by
  have hmem := halfToFun_mem_target n i b hx
  apply SetCoe.ext
  rw [halfInvFun_val_of_mem n i b hmem, halfToFun_val]
  exact halfInvRawE_halfToFunE n i b hx

lemma halfToFun_right_inv (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) : halfToFun n i b (halfInvFun n i b y) = y := by
  apply EuclideanHalfSpace.ext
  rw [halfToFun_val, halfInvFun_val_of_mem n i b hy]
  exact halfToFunE_halfInvRawE n i b hy

/-- The half-ball chart at `(i,b)`. -/
def halfChart (n : ℕ) (i : Fin (n + 1)) (b : Bool) : OpenPartialHomeomorph (Ball n) (Half n) where
  source := halfSource n i b
  target := halfTarget n
  toFun := halfToFun n i b
  invFun := halfInvFun n i b
  map_source' := fun x hx => halfToFun_mem_target n i b hx
  map_target' := fun y hy => halfInvFun_mem_source n i b hy
  left_inv' := fun x hx => halfInvFun_left_inv n i b hx
  right_inv' := fun y hy => halfToFun_right_inv n i b hy
  open_source := by
    show IsOpen {x : Ball n | 0 < bsign b * (x : EuclideanSpace ℝ (Fin (n + 1))) i}
    exact isOpen_Ioi.preimage (by fun_prop : Continuous fun x : Ball n =>
      bsign b * (x : EuclideanSpace ℝ (Fin (n + 1))) i)
  open_target := by
    show IsOpen {y : Half n | ‖tailCLM n y.val‖ + y.val 0 < 1}
    exact isOpen_Iio.preimage (by fun_prop : Continuous fun y : Half n =>
      ‖tailCLM n y.val‖ + y.val 0)
  continuousOn_toFun := by
    have hcont : Continuous (fun x : Ball n =>
        (⟨halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1))),
          halfToFunE_coord_nonneg n i b x⟩ : Half n)) := by
      refine Continuous.subtype_mk (f := fun x : Ball n =>
        halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1)))) ?_ (halfToFunE_coord_nonneg n i b)
      rw [show (fun x : Ball n => halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1)))) =
            fun x : Ball n => consCLM n (1 - ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖,
              tailCLM n (permIso n i (x : EuclideanSpace ℝ (Fin (n + 1))))) by
          funext x; rw [halfToFunE_apply]]
      fun_prop
    exact hcont.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (halfTarget n).domRestrict (halfInvFun n i b) =
        fun p : (halfTarget n : Set (Half n)) =>
          halfInvFunOnTarget n i b (p : Half n) p.property := by
      funext p
      show halfInvFun n i b (p : Half n) = halfInvFunOnTarget n i b (p : Half n) p.property
      rw [halfInvFun_apply, dif_pos p.property]
    rw [hfun]
    refine Continuous.subtype_mk (f := fun p : (halfTarget n : Set (Half n)) =>
      halfInvRawE n i b (p : Half n).val) ?_ ?_
    · rw [show (fun p : (halfTarget n : Set (Half n)) => halfInvRawE n i b (p : Half n).val) =
          fun p : (halfTarget n : Set (Half n)) =>
            permIso n i (consCLM n (bsign b * Real.sqrt ((1 - (p : Half n).val 0) ^ 2
              - ‖tailCLM n (p : Half n).val‖ ^ 2), tailCLM n (p : Half n).val)) by
        funext p; rw [halfInvRawE_apply]]
      fun_prop

@[simp] lemma halfChart_source (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (halfChart n i b).source = halfSource n i b := rfl

@[simp] lemma halfChart_target (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (halfChart n i b).target = halfTarget n := rfl

@[simp] lemma halfChart_apply (n : ℕ) (i : Fin (n + 1)) (b : Bool) (x : Ball n) :
    (halfChart n i b x).val = halfToFunE n i b (x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

lemma halfChart_symm_apply (n : ℕ) (i : Fin (n + 1)) (b : Bool) {y : Half n}
    (hy : y ∈ halfTarget n) :
    ((halfChart n i b).symm y).val = halfInvRawE n i b y.val :=
  halfInvFun_val_of_mem n i b hy

/-! ## The interior chart -/

lemma interiorInv_ball_mem (n : ℕ) (y : Half n) (hy : y ∈ interiorTarget n) :
    interiorInvRawE n y.val ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt hy.2

lemma interiorToFun_coord_nonneg (n : ℕ) (x : Ball n) :
    0 ≤ interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1))) 0 := by
  rw [interiorToFunE_coord]
  exact le_max_right _ _

/-- The forward map of the interior chart. -/
def interiorToFun (n : ℕ) (x : Ball n) : Half n :=
  ⟨interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1))), interiorToFun_coord_nonneg n x⟩

lemma interiorToFun_val (n : ℕ) (x : Ball n) :
    (interiorToFun n x).val = interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

/-- The inverse of the interior chart, restricted to its target. -/
def interiorInvFunOnTarget (n : ℕ) (y : Half n) (hy : y ∈ interiorTarget n) : Ball n :=
  ⟨interiorInvRawE n y.val, interiorInv_ball_mem n y hy⟩

/-- The inverse map of the interior chart. -/
def interiorInvFun (n : ℕ) (y : Half n) : Ball n :=
  dite (y ∈ interiorTarget n) (interiorInvFunOnTarget n y) (fun _ => ⟨0, by simp⟩)

lemma interiorInvFun_apply (n : ℕ) (y : Half n) :
    interiorInvFun n y
      = dite (y ∈ interiorTarget n) (interiorInvFunOnTarget n y) (fun _ => ⟨0, by simp⟩) := rfl

lemma interiorInvFun_val_of_mem (n : ℕ) {y : Half n} (hy : y ∈ interiorTarget n) :
    (interiorInvFun n y).val = interiorInvRawE n y.val := by
  rw [interiorInvFun_apply, dif_pos hy]
  rfl

lemma interiorToFun_mem_target (n : ℕ) {x : Ball n} (hx : x ∈ interiorSource n) :
    interiorToFun n x ∈ interiorTarget n := by
  have hx1 : -(1 / 2 : ℝ) < (x : EuclideanSpace ℝ (Fin (n + 1))) 0 := hx.1
  rw [interiorTarget, Set.mem_setOf_eq]
  constructor
  · rw [interiorToFun_val, interiorToFunE_eq_of_pos n hx1]
    simp [shiftE_apply_zero]
    linarith
  · rw [interiorToFun_val, interiorToFunE_eq_of_pos n hx1, add_sub_cancel_right]
    exact hx.2

lemma interiorInvFun_mem_source (n : ℕ) {y : Half n} (hy : y ∈ interiorTarget n) :
    interiorInvFun n y ∈ interiorSource n := by
  have hy1 : 0 < (y : Half n).val 0 := hy.1
  rw [interiorSource, Set.mem_setOf_eq]
  constructor
  · rw [interiorInvFun_val_of_mem n hy, interiorInvRawE]
    simp [shiftE_apply_zero]
    linarith
  · rw [interiorInvFun_val_of_mem n hy, interiorInvRawE]
    exact hy.2

lemma interiorInvFun_left_inv (n : ℕ) {x : Ball n} (hx : x ∈ interiorSource n) :
    interiorInvFun n (interiorToFun n x) = x := by
  have hmem := interiorToFun_mem_target n hx
  apply SetCoe.ext
  rw [interiorInvFun_val_of_mem n hmem, interiorToFun_val,
    interiorToFunE_eq_of_pos n hx.1, interiorInvRawE, add_sub_cancel_right]

lemma interiorToFun_right_inv (n : ℕ) {y : Half n} (hy : y ∈ interiorTarget n) :
    interiorToFun n (interiorInvFun n y) = y := by
  apply EuclideanHalfSpace.ext
  rw [interiorToFun_val, interiorInvFun_val_of_mem n hy,
    interiorToFunE_eq_of_pos n (by
      rw [interiorInvRawE]; simp [shiftE_apply_zero]; linarith [hy.1]),
    interiorInvRawE, sub_add_cancel]

/-- The centre chart of the ball. -/
def interiorChart (n : ℕ) : OpenPartialHomeomorph (Ball n) (Half n) where
  source := interiorSource n
  target := interiorTarget n
  toFun := interiorToFun n
  invFun := interiorInvFun n
  map_source' := fun x hx => interiorToFun_mem_target n hx
  map_target' := fun y hy => interiorInvFun_mem_source n hy
  left_inv' := fun x hx => interiorInvFun_left_inv n hx
  right_inv' := fun y hy => interiorToFun_right_inv n hy
  open_source := by
    show IsOpen {x : Ball n | -(1 / 2 : ℝ) < (x : EuclideanSpace ℝ (Fin (n + 1))) 0
      ∧ ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1}
    exact (isOpen_lt continuous_const (by fun_prop : Continuous fun x : Ball n =>
        (x : EuclideanSpace ℝ (Fin (n + 1))) 0)).inter
      (isOpen_lt (by fun_prop : Continuous fun x : Ball n =>
        ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖) continuous_const)
  open_target := by
    show IsOpen {y : Half n | 0 < y.val 0 ∧ ‖y.val - shiftE n‖ < 1}
    exact (isOpen_lt continuous_const (by fun_prop : Continuous fun y : Half n =>
        y.val 0)).inter
      (isOpen_lt (by fun_prop : Continuous fun y : Half n => ‖y.val - shiftE n‖)
        continuous_const)
  continuousOn_toFun := by
    have hcont : Continuous (fun x : Ball n =>
        (⟨interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1))),
          interiorToFun_coord_nonneg n x⟩ : Half n)) := by
      refine Continuous.subtype_mk (f := fun x : Ball n =>
        interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1)))) ?_
        (interiorToFun_coord_nonneg n)
      rw [show (fun x : Ball n => interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1)))) =
            fun x : Ball n => consCLM n (max ((x : EuclideanSpace ℝ (Fin (n + 1))) 0 + 1 / 2) 0,
              tailCLM n (x : EuclideanSpace ℝ (Fin (n + 1)))) by
          funext x; rw [interiorToFunE_apply]]
      fun_prop
    exact hcont.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (interiorTarget n).domRestrict (interiorInvFun n) =
        fun p : (interiorTarget n : Set (Half n)) =>
          interiorInvFunOnTarget n (p : Half n) p.property := by
      funext p
      show interiorInvFun n (p : Half n) = interiorInvFunOnTarget n (p : Half n) p.property
      rw [interiorInvFun_apply, dif_pos p.property]
    rw [hfun]
    refine Continuous.subtype_mk (f := fun p : (interiorTarget n : Set (Half n)) =>
      interiorInvRawE n (p : Half n).val) ?_
      (fun p => interiorInv_ball_mem n (p : Half n) p.property)
    rw [show (fun p : (interiorTarget n : Set (Half n)) => interiorInvRawE n (p : Half n).val) =
          fun p : (interiorTarget n : Set (Half n)) => (p : Half n).val - shiftE n by
        funext p; rw [interiorInvRawE]]
    fun_prop

@[simp] lemma interiorChart_source (n : ℕ) : (interiorChart n).source = interiorSource n := rfl

@[simp] lemma interiorChart_target (n : ℕ) : (interiorChart n).target = interiorTarget n := rfl

@[simp] lemma interiorChart_apply (n : ℕ) (x : Ball n) :
    (interiorChart n x).val = interiorToFunE n (x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

lemma interiorChart_symm_apply (n : ℕ) {y : Half n} (hy : y ∈ interiorTarget n) :
    ((interiorChart n).symm y).val = interiorInvRawE n y.val :=
  interiorInvFun_val_of_mem n hy

/-! ## Smoothness of the transition formulas -/

/-- The coordinate functional as a continuous linear map. -/
def coordCLM (n : ℕ) (i : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (euclToPi (n + 1)).toContinuousLinearMap

lemma coordCLM_apply (n : ℕ) (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    coordCLM n i x = x i := rfl

/-- The raw inverse formula of a half-ball chart is smooth off the locus where its square root
argument vanishes. -/
theorem contDiffOn_halfInvRawE (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => halfInvRawE n i b y)
      {y : EuclideanSpace ℝ (Fin (n + 1)) | (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0} := by
  set s : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {y | (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0} with hs
  rw [show (fun y : EuclideanSpace ℝ (Fin (n + 1)) => halfInvRawE n i b y)
      = fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        permIso n i (consCLM n (bsign b * Real.sqrt ((1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2),
          tailCLM n y)) by funext y; rw [halfInvRawE_apply]]
  have hg : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2) s := by
    have h1 : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => (1 - y 0) ^ 2) s := by
      fun_prop
    have h2 : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ‖tailCLM n y‖ ^ 2) s :=
      (contDiff_norm_sq ℝ).comp_contDiffOn ((tailCLM n).contDiff.contDiffOn)
    exact h1.sub h2
  have hsqrt : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      Real.sqrt ((1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2)) s :=
    hg.sqrt (fun y hy => hy)
  have hpair : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      (bsign b * Real.sqrt ((1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2), tailCLM n y)) s :=
    ((contDiff_const (c := bsign b)).contDiffOn.mul hsqrt).prodMk
      ((tailCLM n).contDiff.contDiffOn)
  exact (permIso n i).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((consCLM n).contDiff.comp_contDiffOn hpair)

/-- The forward formula of a half-ball chart is smooth off the origin. -/
theorem contDiffOn_halfToFunE (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    ContDiffOn ℝ ⊤ (fun v : EuclideanSpace ℝ (Fin (n + 1)) => halfToFunE n i b v)
      {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0} := by
  rw [show (fun v : EuclideanSpace ℝ (Fin (n + 1)) => halfToFunE n i b v)
      = fun v : EuclideanSpace ℝ (Fin (n + 1)) =>
        consCLM n (1 - ‖v‖, tailCLM n (permIso n i v)) by funext v; rw [halfToFunE_apply]]
  have h1 : ContDiffOn ℝ ⊤ (fun v : EuclideanSpace ℝ (Fin (n + 1)) => 1 - ‖v‖)
      {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0} :=
    contDiff_const.contDiffOn.sub
      (ContDiffOn.norm ℝ contDiffOn_id (fun v hv => hv))
  have hpair : ContDiffOn ℝ ⊤ (fun v : EuclideanSpace ℝ (Fin (n + 1)) =>
      (1 - ‖v‖, tailCLM n (permIso n i v))) {v : EuclideanSpace ℝ (Fin (n + 1)) | v ≠ 0} :=
    h1.prodMk (((tailCLM n).comp (permIso n i).toContinuousLinearMap).contDiff.contDiffOn)
  exact (consCLM n).contDiff.comp_contDiffOn hpair

/-- The transition formula between two half-ball charts is smooth. -/
theorem contDiffOn_halfTransFun (n : ℕ) (j j' : Fin (n + 1) × Bool) :
    ContDiffOn ℝ ⊤ (halfTransFun n j j')
      {y : EuclideanSpace ℝ (Fin (n + 1)) |
        (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0 ∧ halfInvRawE n j.1 j.2 y ≠ 0} := by
  set s : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {y | (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0 ∧ halfInvRawE n j.1 j.2 y ≠ 0} with hs
  have hs1 : s ⊆ {y : EuclideanSpace ℝ (Fin (n + 1)) |
      (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0} := fun y hy => hy.1
  have hraw : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => halfInvRawE n j.1 j.2 y) s :=
    (contDiffOn_halfInvRawE n j.1 j.2).mono hs1
  have hgoal : ContDiffOn ℝ ⊤
      (fun y : EuclideanSpace ℝ (Fin (n + 1)) => halfToFunE n j'.1 j'.2 (halfInvRawE n j.1 j.2 y)) s :=
    (contDiffOn_halfToFunE n j'.1 j'.2).comp hraw (fun y hy => hy.2)
  exact hgoal

/-- The composite `interiorToFunE ∘ halfInvRawE` is smooth. -/
theorem contDiffOn_interiorToFunE_comp (n : ℕ) (j : Fin (n + 1) × Bool) :
    ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => interiorToFunE n (halfInvRawE n j.1 j.2 y))
      {y : EuclideanSpace ℝ (Fin (n + 1)) |
        0 < halfInvRawE n j.1 j.2 y 0 + 1 / 2 ∧ (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0} := by
  set s : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {y | 0 < halfInvRawE n j.1 j.2 y 0 + 1 / 2 ∧ (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0} with hs
  have hs1 : s ⊆ {y : EuclideanSpace ℝ (Fin (n + 1)) |
      (1 - y 0) ^ 2 - ‖tailCLM n y‖ ^ 2 ≠ 0} := fun y hy => hy.2
  have hraw : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => halfInvRawE n j.1 j.2 y) s :=
    (contDiffOn_halfInvRawE n j.1 j.2).mono hs1
  have hgoal : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      consCLM n (halfInvRawE n j.1 j.2 y 0 + 1 / 2, tailCLM n (halfInvRawE n j.1 j.2 y))) s := by
    have hc : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        halfInvRawE n j.1 j.2 y 0 + 1 / 2) s :=
      ((coordCLM n 0).contDiff.comp_contDiffOn hraw).add contDiff_const.contDiffOn
    have ht : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        tailCLM n (halfInvRawE n j.1 j.2 y)) s :=
      (tailCLM n).contDiff.comp_contDiffOn hraw
    exact (consCLM n).contDiff.comp_contDiffOn (hc.prodMk ht)
  refine ContDiffOn.congr hgoal (fun y hy => ?_)
  show interiorToFunE n (halfInvRawE n j.1 j.2 y)
    = consCLM n (halfInvRawE n j.1 j.2 y 0 + 1 / 2, tailCLM n (halfInvRawE n j.1 j.2 y))
  rw [interiorToFunE_apply, max_eq_left hy.1.le]

/-- The composite `halfToFunE ∘ interiorInvRawE` is smooth. -/
theorem contDiffOn_halfToFunE_comp (n : ℕ) (j : Fin (n + 1) × Bool) :
    ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => halfToFunE n j.1 j.2 (interiorInvRawE n y))
      {y : EuclideanSpace ℝ (Fin (n + 1)) | interiorInvRawE n y ≠ 0} := by
  have htrans : ContDiffOn ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => interiorInvRawE n y)
      {y : EuclideanSpace ℝ (Fin (n + 1)) | interiorInvRawE n y ≠ 0} := by
    rw [show (fun y : EuclideanSpace ℝ (Fin (n + 1)) => interiorInvRawE n y)
        = fun y : EuclideanSpace ℝ (Fin (n + 1)) => y - shiftE n by
      funext y; rw [interiorInvRawE]]
    fun_prop
  exact (contDiffOn_halfToFunE n j.1 j.2).comp htrans (fun y hy => hy)

/-! ## The charted space structure on the ball -/

lemma exists_coord_ne_zero (n : ℕ) {x : EuclideanSpace ℝ (Fin (n + 1))} (h : x ≠ 0) :
    ∃ i, x i ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (WithLp.ofLp_injective 2 (by funext i; exact hc i))

lemma ne_zero_of_apply_ne {m : ℕ} {v : EuclideanSpace ℝ (Fin m)} {i : Fin m} (h : v i ≠ 0) :
    v ≠ 0 := by
  intro hv
  rw [hv] at h
  simp at h

lemma bsign_decide_mul (t : ℝ) : bsign (decide (0 < t)) * t = |t| := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [decide_eq_false_iff_not.mpr (not_lt.mpr h.le), abs_of_neg h]
    simp [bsign]
  · rw [h]; simp [bsign]
  · rw [decide_eq_true_eq.mpr h, abs_of_pos h]
    simp [bsign]

/-- A coordinate at which a point of the ball is non-zero. -/
noncomputable def ballCoord (n : ℕ) (x : Ball n) (h : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :
    Fin (n + 1) :=
  Classical.choose (exists_coord_ne_zero n h)

lemma ballCoord_spec (n : ℕ) (x : Ball n) (h : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) (ballCoord n x h) ≠ 0 :=
  Classical.choose_spec (exists_coord_ne_zero n h)

lemma ball_ne_zero_of_not_mem (n : ℕ) {x : Ball n} (h : x ∉ interiorSource n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
  intro hx0
  refine h ⟨?_, ?_⟩
  · rw [hx0]; norm_num
  · rw [hx0]; simp

/-- The half-ball chart chosen at a point of the ball not covered by the interior chart. -/
noncomputable def ballHalfChartAt (n : ℕ) (x : Ball n) (h : x ∉ interiorSource n) :
    OpenPartialHomeomorph (Ball n) (Half n) :=
  halfChart n (ballCoord n x (ball_ne_zero_of_not_mem n h))
    (decide (0 < (x : EuclideanSpace ℝ (Fin (n + 1)))
      (ballCoord n x (ball_ne_zero_of_not_mem n h))))

lemma ballHalfChartAt_source (n : ℕ) (x : Ball n) (h : x ∉ interiorSource n) :
    x ∈ (ballHalfChartAt n x h).source := by
  show 0 < bsign (decide (0 < (x : EuclideanSpace ℝ (Fin (n + 1)))
      (ballCoord n x (ball_ne_zero_of_not_mem n h))))
    * (x : EuclideanSpace ℝ (Fin (n + 1))) (ballCoord n x (ball_ne_zero_of_not_mem n h))
  rw [bsign_decide_mul]
  exact abs_pos.mpr (ballCoord_spec n x (ball_ne_zero_of_not_mem n h))

/-- The preferred chart at a point of the ball. -/
noncomputable def ballChartAt (n : ℕ) (x : Ball n) : OpenPartialHomeomorph (Ball n) (Half n) :=
  dite (x ∈ interiorSource n) (fun _ => interiorChart n) (ballHalfChartAt n x)

lemma ballChartAt_of_mem (n : ℕ) {x : Ball n} (h : x ∈ interiorSource n) :
    ballChartAt n x = interiorChart n :=
  dif_pos h

lemma ballChartAt_of_not_mem (n : ℕ) {x : Ball n} (h : x ∉ interiorSource n) :
    ballChartAt n x = ballHalfChartAt n x h :=
  dif_neg h

/-- The atlas of the ball: the two families of charts. -/
def ballAtlas (n : ℕ) : Set (OpenPartialHomeomorph (Ball n) (Half n)) :=
  Set.range (fun j : Fin (n + 1) × Bool => halfChart n j.1 j.2) ∪ {interiorChart n}

/-- The charted space structure on the closed ball. -/
noncomputable def ballChartedSpace (n : ℕ) : ChartedSpace (Half n) (Ball n) where
  atlas := ballAtlas n
  chartAt := ballChartAt n
  mem_chart_source := by
    intro x
    by_cases h : x ∈ interiorSource n
    · rw [ballChartAt_of_mem n h]; exact h
    · rw [ballChartAt_of_not_mem n h]; exact ballHalfChartAt_source n x h
  chart_mem_atlas := by
    intro x
    by_cases h : x ∈ interiorSource n
    · rw [ballChartAt_of_mem n h]; exact Or.inr rfl
    · rw [ballChartAt_of_not_mem n h]
      exact Or.inl ⟨(ballCoord n x (ball_ne_zero_of_not_mem n h),
        decide (0 < (x : EuclideanSpace ℝ (Fin (n + 1)))
          (ballCoord n x (ball_ne_zero_of_not_mem n h)))), rfl⟩

/-! ## Compatibility of the charts -/

lemma mem_trans_source {n : ℕ} {e e' : OpenPartialHomeomorph (Ball n) (Half n)} {y : Half n}
    (hy : y ∈ (e.symm ≫ₕ e').source) : y ∈ e.target ∧ e.invFun y ∈ e'.source := by
  rw [OpenPartialHomeomorph.trans_source] at hy
  rw [OpenPartialHomeomorph.symm_source] at hy
  exact ⟨hy.1, hy.2⟩

lemma half_half_eqOn (n : ℕ) (j j' : Fin (n + 1) × Bool) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ (hModel n).symm ⁻¹' ((halfChart n j.1 j.2).symm ≫ₕ halfChart n j'.1 j'.2).source
      ∩ Set.range (hModel n)) :
    ((hModel n) ∘ ⇑((halfChart n j.1 j.2).symm ≫ₕ halfChart n j'.1 j'.2)
        ∘ (hModel n).symm) y = halfTransFun n j j' y := by
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 ≤ y 0 := (mem_half_iff n y).mp hy2
  have hY : (⟨y, hy0⟩ : Half n) ∈ ((halfChart n j.1 j.2).symm ≫ₕ halfChart n j'.1 j'.2).source := by
    simpa [halfModel_symm_apply_of_le n hy0] using hy1
  obtain ⟨htgt, hsrc⟩ := mem_trans_source hY
  rw [halfChart_target] at htgt
  have hinv : (halfChart n j.1 j.2).invFun ⟨y, hy0⟩
      = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt := by
    change halfInvFun n j.1 j.2 ⟨y, hy0⟩ = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt
    rw [halfInvFun_apply, dif_pos htgt]
  simp only [Function.comp_apply]
  rw [halfModel_symm_apply_of_le n hy0]
  show (halfChart n j'.1 j'.2 ((halfChart n j.1 j.2).invFun ⟨y, hy0⟩)).val = halfTransFun n j j' y
  rw [hinv]
  rfl

lemma half_interior_eqOn (n : ℕ) (j : Fin (n + 1) × Bool) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ (hModel n).symm ⁻¹' ((halfChart n j.1 j.2).symm ≫ₕ interiorChart n).source
      ∩ Set.range (hModel n)) :
    ((hModel n) ∘ ⇑((halfChart n j.1 j.2).symm ≫ₕ interiorChart n)
        ∘ (hModel n).symm) y = interiorToFunE n (halfInvRawE n j.1 j.2 y) := by
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 ≤ y 0 := (mem_half_iff n y).mp hy2
  have hY : (⟨y, hy0⟩ : Half n)
      ∈ ((halfChart n j.1 j.2).symm ≫ₕ interiorChart n).source := by
    simpa [halfModel_symm_apply_of_le n hy0] using hy1
  obtain ⟨htgt, hsrc⟩ := mem_trans_source hY
  rw [halfChart_target] at htgt
  have hinv : (halfChart n j.1 j.2).invFun ⟨y, hy0⟩
      = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt := by
    change halfInvFun n j.1 j.2 ⟨y, hy0⟩ = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt
    rw [halfInvFun_apply, dif_pos htgt]
  simp only [Function.comp_apply]
  rw [halfModel_symm_apply_of_le n hy0]
  show (interiorChart n ((halfChart n j.1 j.2).invFun ⟨y, hy0⟩)).val
    = interiorToFunE n (halfInvRawE n j.1 j.2 y)
  rw [hinv]
  rfl

lemma interior_half_eqOn (n : ℕ) (j : Fin (n + 1) × Bool) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ (hModel n).symm ⁻¹' ((interiorChart n).symm ≫ₕ halfChart n j.1 j.2).source
      ∩ Set.range (hModel n)) :
    ((hModel n) ∘ ⇑((interiorChart n).symm ≫ₕ halfChart n j.1 j.2)
        ∘ (hModel n).symm) y = halfToFunE n j.1 j.2 (interiorInvRawE n y) := by
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 ≤ y 0 := (mem_half_iff n y).mp hy2
  have hY : (⟨y, hy0⟩ : Half n)
      ∈ ((interiorChart n).symm ≫ₕ halfChart n j.1 j.2).source := by
    simpa [halfModel_symm_apply_of_le n hy0] using hy1
  obtain ⟨htgt, hsrc⟩ := mem_trans_source hY
  rw [interiorChart_target] at htgt
  have hinv : (interiorChart n).invFun ⟨y, hy0⟩
      = interiorInvFunOnTarget n ⟨y, hy0⟩ htgt := by
    change interiorInvFun n ⟨y, hy0⟩ = interiorInvFunOnTarget n ⟨y, hy0⟩ htgt
    rw [interiorInvFun_apply, dif_pos htgt]
  simp only [Function.comp_apply]
  rw [halfModel_symm_apply_of_le n hy0]
  show (halfChart n j.1 j.2 ((interiorChart n).invFun ⟨y, hy0⟩)).val
    = halfToFunE n j.1 j.2 (interiorInvRawE n y)
  rw [hinv]
  rfl

/-- The transition `halfChart j → halfChart j'` is smooth. -/
theorem compat_half_half (n : ℕ) (j j' : Fin (n + 1) × Bool) :
    ContDiffOn ℝ ⊤ ((hModel n) ∘ ⇑((halfChart n j.1 j.2).symm ≫ₕ halfChart n j'.1 j'.2)
        ∘ (hModel n).symm)
      ((hModel n).symm ⁻¹' ((halfChart n j.1 j.2).symm ≫ₕ halfChart n j'.1 j'.2).source
        ∩ Set.range (hModel n)) := by
  refine ContDiffOn.congr ?_ (fun y hy => half_half_eqOn n j j' hy)
  refine (contDiffOn_halfTransFun n j j').mono ?_
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 ≤ y 0 := (mem_half_iff n y).mp hy2
  have hY : (⟨y, hy0⟩ : Half n) ∈ ((halfChart n j.1 j.2).symm ≫ₕ halfChart n j'.1 j'.2).source := by
    simpa [halfModel_symm_apply_of_le n hy0] using hy1
  obtain ⟨htgt, hsrc⟩ := mem_trans_source hY
  rw [halfChart_target] at htgt
  refine ⟨?_, ?_⟩
  · exact ne_of_gt (halfTarget_g_pos n htgt)
  · have h3 : (halfChart n j.1 j.2).invFun ⟨y, hy0⟩
        = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt := by
      change halfInvFun n j.1 j.2 ⟨y, hy0⟩ = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt
      rw [halfInvFun_apply, dif_pos htgt]
    have h2 : 0 < bsign j'.2 * (halfInvRawE n j.1 j.2 y) j'.1 := by
      rw [h3] at hsrc
      have h2' : 0 < bsign j'.2 * ((halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt : Ball n)
          : EuclideanSpace ℝ (Fin (n + 1))) j'.1 := hsrc
      have h4 : ((halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt : Ball n)
          : EuclideanSpace ℝ (Fin (n + 1))) = halfInvRawE n j.1 j.2 y := rfl
      rwa [h4] at h2' 
    exact ne_zero_of_apply_ne (i := j'.1) (ne_zero_of_bsign_mul_pos h2)

/-- The transition `halfChart j → interiorChart` is smooth. -/
theorem compat_half_interior (n : ℕ) (j : Fin (n + 1) × Bool) :
    ContDiffOn ℝ ⊤ ((hModel n) ∘ ⇑((halfChart n j.1 j.2).symm ≫ₕ interiorChart n)
        ∘ (hModel n).symm)
      ((hModel n).symm ⁻¹' ((halfChart n j.1 j.2).symm ≫ₕ interiorChart n).source
        ∩ Set.range (hModel n)) := by
  refine ContDiffOn.congr ?_ (fun y hy => half_interior_eqOn n j hy)
  refine (contDiffOn_interiorToFunE_comp n j).mono ?_
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 ≤ y 0 := (mem_half_iff n y).mp hy2
  have hY : (⟨y, hy0⟩ : Half n) ∈ ((halfChart n j.1 j.2).symm ≫ₕ interiorChart n).source := by
    simpa [halfModel_symm_apply_of_le n hy0] using hy1
  obtain ⟨htgt, hsrc⟩ := mem_trans_source hY
  rw [halfChart_target] at htgt
  have h3 : (halfChart n j.1 j.2).invFun ⟨y, hy0⟩
      = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt := by
    change halfInvFun n j.1 j.2 ⟨y, hy0⟩ = halfInvFunOnTarget n j.1 j.2 ⟨y, hy0⟩ htgt
    rw [halfInvFun_apply, dif_pos htgt]
  have hsrc' : -(1 / 2 : ℝ) < (halfInvRawE n j.1 j.2 y) 0 := by
    rw [h3] at hsrc
    exact hsrc.1
  refine ⟨?_, ?_⟩
  · linarith
  · exact ne_of_gt (halfTarget_g_pos n htgt)

/-- The transition `interiorChart → halfChart j` is smooth. -/
theorem compat_interior_half (n : ℕ) (j : Fin (n + 1) × Bool) :
    ContDiffOn ℝ ⊤ ((hModel n) ∘ ⇑((interiorChart n).symm ≫ₕ halfChart n j.1 j.2)
        ∘ (hModel n).symm)
      ((hModel n).symm ⁻¹' ((interiorChart n).symm ≫ₕ halfChart n j.1 j.2).source
        ∩ Set.range (hModel n)) := by
  refine ContDiffOn.congr ?_ (fun y hy => interior_half_eqOn n j hy)
  refine (contDiffOn_halfToFunE_comp n j).mono ?_
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 ≤ y 0 := (mem_half_iff n y).mp hy2
  have hY : (⟨y, hy0⟩ : Half n) ∈ ((interiorChart n).symm ≫ₕ halfChart n j.1 j.2).source := by
    simpa [halfModel_symm_apply_of_le n hy0] using hy1
  obtain ⟨htgt, hsrc⟩ := mem_trans_source hY
  rw [interiorChart_target] at htgt
  have h3 : (interiorChart n).invFun ⟨y, hy0⟩ = interiorInvFunOnTarget n ⟨y, hy0⟩ htgt := by
    change interiorInvFun n ⟨y, hy0⟩ = interiorInvFunOnTarget n ⟨y, hy0⟩ htgt
    rw [interiorInvFun_apply, dif_pos htgt]
  have h2 : 0 < bsign j.2 * (interiorInvRawE n y) j.1 := by
    rw [h3] at hsrc
    have h2' : 0 < bsign j.2 * ((interiorInvFunOnTarget n ⟨y, hy0⟩ htgt : Ball n)
        : EuclideanSpace ℝ (Fin (n + 1))) j.1 := hsrc
    have h4 : ((interiorInvFunOnTarget n ⟨y, hy0⟩ htgt : Ball n)
        : EuclideanSpace ℝ (Fin (n + 1))) = interiorInvRawE n y := rfl
    rwa [h4] at h2' 
  exact ne_zero_of_apply_ne (i := j.1) (ne_zero_of_bsign_mul_pos h2)

/-- The transition between the interior chart and itself is smooth. -/
theorem compat_interior_interior (n : ℕ) :
    ContDiffOn ℝ ⊤ ((hModel n) ∘ ⇑((interiorChart n).symm ≫ₕ interiorChart n)
        ∘ (hModel n).symm)
      ((hModel n).symm ⁻¹' ((interiorChart n).symm ≫ₕ interiorChart n).source
        ∩ Set.range (hModel n)) := by
  have h := (mem_groupoid_of_pregroupoid.mp
    (symm_trans_mem_contDiffGroupoid (n := ⊤) (I := hModel n) (interiorChart n))).1
  simpa only [contDiffPregroupoid] using h

/-- The closed ball, as a smooth manifold with boundary. -/
theorem ball_isManifold (n : ℕ) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _ (EuclideanHalfSpace (n + 1)) _
      (hModel n) (⊤ : WithTop ℕ∞) (Ball n) _ (ballChartedSpace n) := by
  letI := ballChartedSpace n
  refine isManifold_of_contDiffOn (hModel n) ⊤ (Ball n) ?_
  intro e e' he he'
  rcases he with ⟨j, rfl⟩ | rfl <;> rcases he' with ⟨j', rfl⟩ | rfl
  · exact compat_half_half n j j'
  · exact compat_half_interior n j
  · exact compat_interior_half n j'
  · exact compat_interior_interior n

/-! ## The target statement -/

theorem exists_ball_manifold (n : ℕ) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace (n + 1))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _ (EuclideanHalfSpace (n + 1)) _
        (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ENat) : WithTop ENat)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) _ cs := by
  refine ⟨ballChartedSpace n, ?_⟩
  letI := ballChartedSpace n
  haveI : IsManifold (hModel n) (⊤ : WithTop ℕ∞) (Ball n) := ball_isManifold n
  exact IsManifold.of_le (n := (⊤ : WithTop ℕ∞)) le_top

end Work.SignatureBordism
