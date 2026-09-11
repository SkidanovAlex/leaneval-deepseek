import Submission.NBridge

open EquiangularLinesFixedAngle
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

/-! Lower bounds for `N α d`. We exhibit explicit unit vectors with pairwise inner products
`α`: `v i = c e_i + t·1̄` with `c = √(1−α)`, `t = (√(1−α+dα) − √(1−α))/d`. -/

/-- Build an element of `EuclideanSpace ℝ (Fin d)` from a coordinate function. -/
def eucOfFun {d : ℕ} (f : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 f

lemma eucOfFun_apply {d : ℕ} (f : Fin d → ℝ) (j : Fin d) : (eucOfFun f) j = f j := rfl

/-- The standard basis vector `e_i`. -/
def stdE {d : ℕ} (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  eucOfFun (fun k : Fin d => if k = i then (1 : ℝ) else 0)

/-- The all-ones vector. -/
def onesVec {d : ℕ} : EuclideanSpace ℝ (Fin d) :=
  eucOfFun (fun _ : Fin d => (1 : ℝ))

lemma ind_mul_self {d : ℕ} (i k : Fin d) :
    (if k = i then (1 : ℝ) else 0) * (if k = i then 1 else 0) = (if k = i then 1 else 0) := by
  by_cases h : k = i <;> simp [h]

lemma ind_mul_ne {d : ℕ} (i j k : Fin d) (hij : i ≠ j) :
    (if k = i then (1 : ℝ) else 0) * (if k = j then 1 else 0) = 0 := by
  by_cases h : k = i
  · subst k
    simp [hij]
  · by_cases g : k = j
    · subst k
      simp [h]
    · simp [h, g]

/-- `⟨e_i, e_j⟩ = δ_ij`. -/
lemma inner_stdE {d : ℕ} (i j : Fin d) :
    ⟪stdE i, stdE j⟫ = (if i = j then 1 else 0) := by
  classical
  rw [euclidean_inner_apply]
  change (∑ k : Fin d, (if k = i then (1 : ℝ) else 0) * (if k = j then 1 else 0))
    = (if i = j then 1 else 0)
  by_cases hij : i = j
  · subst j
    simp [Finset.sum_ite_eq']
  · simp [hij]
    exact fun h : j = i => hij h.symm

/-- `⟨e_i, 1̄⟩ = 1`. -/
lemma inner_stdE_ones {d : ℕ} (i : Fin d) : ⟪stdE i, onesVec (d := d)⟫ = 1 := by
  rw [euclidean_inner_apply]
  simp [stdE, onesVec, eucOfFun, Finset.sum_ite_eq']

/-- `⟨1̄, 1̄⟩ = d`. -/
lemma inner_ones_ones {d : ℕ} : ⟪onesVec (d := d), onesVec (d := d)⟫ = (d : ℝ) := by
  rw [euclidean_inner_apply]
  simp [onesVec, eucOfFun, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]

/-- Inner product of two members of the family `c e_i + t·1̄`. -/
lemma inner_pair {d : ℕ} (i j : Fin d) (c t : ℝ) :
    ⟪c • stdE i + t • onesVec (d := d), c • stdE j + t • onesVec (d := d)⟫
      = (if i = j then c ^ 2 else 0) + 2 * c * t + t ^ 2 * (d : ℝ) := by
  classical
  calc
    ⟪c • stdE i + t • onesVec (d := d), c • stdE j + t • onesVec (d := d)⟫
        = c * c * ⟪stdE i, stdE j⟫ + c * t * ⟪stdE i, onesVec (d := d)⟫
          + t * c * ⟪onesVec (d := d), stdE j⟫ + t * t * ‖onesVec (d := d)‖ ^ 2 := by
          simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, star_trivial,
            mul_assoc, mul_comm, mul_left_comm]
          ring
    _ = (if i = j then c ^ 2 else 0) + 2 * c * t + t ^ 2 * (d : ℝ) := by
          have hnorm : ‖onesVec (d := d)‖ ^ 2 = (d : ℝ) := by
            rw [← real_inner_self_eq_norm_sq]
            exact inner_ones_ones (d := d)
          rw [inner_stdE, inner_stdE_ones, hnorm]
          rw [real_inner_comm]
          rw [inner_stdE_ones]
          by_cases hij : i = j
          · subst j
            simp
            ring
          · simp [hij]
            ring

/-- The constant `t` from the construction. -/
noncomputable def pairT (α : ℝ) (d : ℕ) : ℝ :=
  (Real.sqrt (1 - α + (d : ℝ) * α) - Real.sqrt (1 - α)) / (d : ℝ)

/-- The constant `c` from the construction. -/
noncomputable def pairC (α : ℝ) : ℝ := Real.sqrt (1 - α)

/-- Key identity: `d t² + 2 c t = α`. -/
lemma pair_key {α : ℝ} {d : ℕ} (hα0 : 0 < α) (hα1 : α < 1) (hd : d ≠ 0) :
    (d : ℝ) * (pairT α d) ^ 2 + 2 * pairC α * pairT α d = α := by
  classical
  let c : ℝ := pairC α
  let u : ℝ := Real.sqrt (1 - α + (d : ℝ) * α)
  let t : ℝ := pairT α d
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hnonneg1 : 0 ≤ 1 - α := by linarith
  have hnonneg2 : 0 ≤ 1 - α + (d : ℝ) * α := by
    have h2 : 0 ≤ (d : ℝ) * α := by positivity
    nlinarith
  have hu : u ^ 2 = c ^ 2 + (d : ℝ) * α := by
    dsimp [u, c, pairC]
    rw [Real.sq_sqrt hnonneg2]
    rw [Real.sq_sqrt hnonneg1]
  have hmain : (d : ℝ) * t ^ 2 + 2 * c * t = α := by
    change (d : ℝ) * ((u - c) / (d : ℝ)) ^ 2 + 2 * c * ((u - c) / (d : ℝ)) = α
    field_simp [hdne]
    nlinarith [hu]
  change (d : ℝ) * t ^ 2 + 2 * c * t = α
  exact hmain

/-- The explicit equiangular family: `v i = c e_i + t·1̄`. -/
noncomputable def pairVec (α : ℝ) {d : ℕ} (hd : d ≠ 0) : Fin d → EuclideanSpace ℝ (Fin d) :=
  fun i => pairC α • stdE i + pairT α d • onesVec (d := d)

/-- Each `v i` is a unit vector. -/
lemma pairVec_norm {α : ℝ} {d : ℕ} (hα0 : 0 < α) (hα1 : α < 1) (hd : d ≠ 0) (i : Fin d) :
    ‖pairVec α hd i‖ = 1 := by
  classical
  have hkey := pair_key (α := α) (d := d) hα0 hα1 hd
  have hsq : ‖pairVec α hd i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold pairVec
    rw [inner_pair i i (pairC α) (pairT α d)]
    have hc2 : (pairC α) ^ 2 = 1 - α := by
      dsimp [pairC]
      rw [Real.sq_sqrt]
      linarith
    calc
      (if i = i then (pairC α) ^ 2 else 0) + 2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)
          = (pairC α) ^ 2 + (2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)) := by
            simp
            ring
      _ = (pairC α) ^ 2 + α := by
            rw [show 2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)
                  = (d : ℝ) * (pairT α d) ^ 2 + 2 * pairC α * pairT α d by ring]
            rw [hkey]
      _ = 1 := by
            rw [hc2]
            ring
  have hcases := sq_eq_one_iff.mp hsq
  rcases hcases with h | h
  · exact h
  · linarith [norm_nonneg (pairVec α hd i)]

/-- Pairwise inner products are `α`. -/
lemma pairVec_inner {α : ℝ} {d : ℕ} (hα0 : 0 < α) (hα1 : α < 1) (hd : d ≠ 0)
    {i j : Fin d} : ⟪pairVec α hd i, pairVec α hd j⟫ = (if i = j then 1 else α) := by
  classical
  unfold pairVec
  rw [inner_pair i j (pairC α) (pairT α d)]
  have hkey := pair_key (α := α) (d := d) hα0 hα1 hd
  have hc2 : (pairC α) ^ 2 = 1 - α := by
    dsimp [pairC]
    rw [Real.sq_sqrt]
    linarith
  by_cases hij : i = j
  · subst j
    calc
      (if i = i then (pairC α) ^ 2 else 0) + 2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)
          = (pairC α) ^ 2 + (2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)) := by
            simp
            ring
      _ = (pairC α) ^ 2 + α := by
            rw [show 2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)
                  = (d : ℝ) * (pairT α d) ^ 2 + 2 * pairC α * pairT α d by ring]
            rw [hkey]
      _ = 1 := by
            rw [hc2]
            ring
      _ = if i = i then 1 else α := by simp
  · calc
      (if i = j then (pairC α) ^ 2 else 0) + 2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ)
          = 2 * pairC α * pairT α d + (pairT α d) ^ 2 * (d : ℝ) := by
            simp [hij]
      _ = (d : ℝ) * (pairT α d) ^ 2 + 2 * pairC α * pairT α d := by ring
      _ = α := by rw [hkey]
      _ = if i = j then 1 else α := by simp [hij]

lemma pairVec_angle {α : ℝ} {d : ℕ} (hα0 : 0 < α) (hα1 : α < 1) (hd : d ≠ 0)
    {i j : Fin d} (hij : i ≠ j) : |⟪pairVec α hd i, pairVec α hd j⟫| = α := by
  rw [pairVec_inner (α := α) (d := d) hα0 hα1 hd]
  simp [hij, abs_of_nonneg (le_of_lt hα0)]

/-- `N α d ≥ d` for every dimension `d`. -/
lemma N_ge_d {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (d : ℕ) : d ≤ N α d := by
  classical
  by_cases hd : d = 0
  · subst d
    exact Nat.zero_le _
  · have hvnorm : ∀ i : Fin d, ‖pairVec α hd i‖ = 1 := pairVec_norm (α := α) (d := d) hα0 hα1 hd
    have hvangle : ∀ ⦃i j : Fin d⦄, i ≠ j → |⟪pairVec α hd i, pairVec α hd j⟫| = α :=
      fun i j hij => pairVec_angle (α := α) (d := d) hα0 hα1 hd hij
    exact le_N_of_hasLines hα0 hα1 ⟨pairVec α hd, hvnorm, hvangle⟩

end Submission
