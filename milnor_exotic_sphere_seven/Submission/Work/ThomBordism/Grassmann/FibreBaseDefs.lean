import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.GrassmannianTopology
import Submission.Work.ThomBordism.Grassmann.SphereCover
import Submission.Work.ThomBordism.Grassmann.Frame
import Submission.Work.ThomBordism.Grassmann.InclDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-!
# The fibre of the tautological bundle at the base vector

Linear-algebra bookkeeping for `fibreBaseHomeomorph`: the index conventions `ct` / `lastk` for
`Fin k`, the identification `snocE` of `ℝ^{(k-1)+m}` with the hyperplane `baseVec k m ^⊥ ⊂ ℝ^{k+m}`
together with its inverse `truncE`, and the splitting of sums over `Fin k`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-! ## Index conventions for `Fin k` -/

/-- The last index `k-1` of `Fin k` (for `k ≥ 1`). -/
def lastk (k : ℕ) (hk : 1 ≤ k) : Fin k := ⟨k-1, by omega⟩

@[simp] theorem lastk_val (k : ℕ) (hk : 1 ≤ k) : (lastk k hk).val = k - 1 := rfl

/-- The inclusion of the first `k-1` indices into `Fin k` (for `k ≥ 1`). -/
def ct (k : ℕ) (hk : 1 ≤ k) : Fin (k-1) → Fin k := fun j => ⟨j.val, by omega⟩

@[simp] theorem ct_val (k : ℕ) (hk : 1 ≤ k) (j : Fin (k-1)) : (ct k hk j).val = j.val := rfl

theorem ct_injective (k : ℕ) (hk : 1 ≤ k) : Function.Injective (ct k hk) :=
  fun i j h => Fin.ext (by simpa using congrArg Fin.val h)

theorem ct_ne_lastk (k : ℕ) (hk : 1 ≤ k) (j : Fin (k-1)) : ct k hk j ≠ lastk k hk := by
  intro h
  have h2 : (ct k hk j).val = (lastk k hk).val := by rw [h]
  simp only [ct_val, lastk_val] at h2
  have := j.isLt
  omega

theorem eq_lastk_or_eq_ct (k : ℕ) (hk : 1 ≤ k) (i : Fin k) :
    i = lastk k hk ∨ ∃ j : Fin (k-1), i = ct k hk j := by
  by_cases h : i.val < k-1
  · exact Or.inr ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · refine Or.inl (Fin.ext ?_)
    simp only [lastk_val]
    omega

/-- The equivalence `Fin (k-1) ⊕ Fin 1 ≃ Fin k` underlying the decomposition of a sum. -/
def sumEquiv (k : ℕ) (hk : 1 ≤ k) : Fin (k-1) ⊕ Fin 1 ≃ Fin k where
  toFun x := Sum.elim (ct k hk) (fun _ => lastk k hk) x
  invFun i := if h : i.val < k - 1 then Sum.inl ⟨i.val, h⟩ else Sum.inr 0
  left_inv := by
    rintro (j | x)
    · simp only [Sum.elim_inl]
      rw [dif_pos (by rw [ct_val]; exact j.isLt)]
      exact congrArg Sum.inl (Fin.ext rfl)
    · simp only [Sum.elim_inr]
      rw [dif_neg (by rw [lastk_val]; omega)]
      exact congrArg Sum.inr (Subsingleton.elim 0 x)
  right_inv := by
    intro i
    by_cases h : i.val < k - 1
    · simp only [h, dif_pos, Sum.elim_inl]
      exact Fin.ext rfl
    · simp only [h, dif_neg, not_false_iff, Sum.elim_inr]
      rcases eq_lastk_or_eq_ct k hk i with h2 | ⟨j, hj⟩
      · exact h2.symm
      · exact absurd (hj ▸ j.isLt) h

@[simp] theorem sumEquiv_inl (k : ℕ) (hk : 1 ≤ k) (j : Fin (k-1)) :
    sumEquiv k hk (Sum.inl j) = ct k hk j := rfl

@[simp] theorem sumEquiv_inr (k : ℕ) (hk : 1 ≤ k) (x : Fin 1) :
    sumEquiv k hk (Sum.inr x) = lastk k hk := rfl

/-- **Splitting a sum over `Fin k` into its first `k-1` terms and the last one.** -/
theorem sum_fin_eq {M : Type*} [AddCommMonoid M] (k : ℕ) (hk : 1 ≤ k) (f : Fin k → M) :
    ∑ i, f i = (∑ j : Fin (k-1), f (ct k hk j)) + f (lastk k hk) := by
  rw [Fintype.sum_equiv (sumEquiv k hk).symm f
    (fun x : Fin (k-1) ⊕ Fin 1 => f (sumEquiv k hk x)) (fun x => by simp)]
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  simp only [sumEquiv_inl, sumEquiv_inr]

/-! ## The base vector -/

theorem baseVec_eq_single (k m : ℕ) (hk : 1 ≤ k) :
    baseVec k m = EuclideanSpace.single (lastk (k+m) (by omega)) (1 : ℝ) := by
  rw [baseVec, dif_neg (by omega : ¬ (k + m = 0))]
  congr 1

theorem inner_baseVec (k m : ℕ) (hk : 1 ≤ k) (v : Amb (k+m)) :
    inner ℝ v (baseVec k m) = v.ofLp (lastk (k+m) (by omega)) := by
  rw [baseVec_eq_single k m hk, EuclideanSpace.inner_single_right]
  simp

theorem inner_baseVec_self (k m : ℕ) (hk : 1 ≤ k) :
    inner ℝ (baseVec k m) (baseVec k m) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_baseVec (by omega : k + m ≠ 0)]
  norm_num

/-! ## Appending a zero coordinate -/

theorem snoc0_ofLp_lt (n : ℕ) (y : Amb n) (j : Fin (n+1)) (hj : j.val < n) :
    (snoc0 n y).ofLp j = y.ofLp ⟨j.val, hj⟩ := by
  have h := snoc0_ofLp_castSucc n y (⟨j.val, hj⟩ : Fin n)
  rw [show (⟨j.val, hj⟩ : Fin n).castSucc = j from Fin.ext rfl] at h
  exact h

/-- **The isometric embedding of `ℝ^{(k-1)+m}` into `ℝ^{k+m}` as the last-coordinate-zero
hyperplane** (the orthogonal complement of `baseVec k m`). -/
def snocE (k m : ℕ) (hk : 1 ≤ k) : Amb ((k-1)+m) →ₗᵢ[ℝ] Amb (k+m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by omega : (k-1)+m+1 = k+m))).toLinearIsometry.comp
    (snoc0LI ((k-1)+m))

theorem snocE_apply_ofLp (k m : ℕ) (hk : 1 ≤ k) (x : Amb ((k-1)+m)) (i : Fin (k+m)) :
    (snocE k m hk x).ofLp i
      = (snoc0 ((k-1)+m) x).ofLp ((finCongr (show (k-1)+m+1 = k+m by omega)).symm i) := by
  have key : snocE k m hk x
      = (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (show (k-1)+m+1 = k+m by omega)))
          (snoc0 ((k-1)+m) x) := rfl
  rw [key, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem snocE_apply_ofLp_lt (k m : ℕ) (hk : 1 ≤ k) (x : Amb ((k-1)+m)) (i : Fin (k+m))
    (hi : i.val < (k-1)+m) :
    (snocE k m hk x).ofLp i = x.ofLp ⟨i.val, hi⟩ := by
  rw [snocE_apply_ofLp]
  have h3 : (finCongr (show (k-1)+m+1 = k+m by omega)).symm i
      = (⟨i.val, hi⟩ : Fin ((k-1)+m)).castSucc := by
    apply Fin.ext
    simp [finCongr]
  rw [h3, snoc0_ofLp_castSucc]

theorem snocE_apply_ofLp_lastN (k m : ℕ) (hk : 1 ≤ k) (x : Amb ((k-1)+m)) :
    (snocE k m hk x).ofLp (lastk (k+m) (by omega)) = 0 := by
  rw [snocE_apply_ofLp]
  have h3 : (finCongr (show (k-1)+m+1 = k+m by omega)).symm (lastk (k+m) (by omega))
      = Fin.last ((k-1)+m) := by
    apply Fin.ext
    rw [finCongr_symm_apply, Fin.val_cast, lastk_val, Fin.val_last]
    omega
  rw [h3, snoc0_ofLp_last]

/-- `snocE` lands in the orthogonal complement of `baseVec k m`. -/
theorem inner_snocE_baseVec (k m : ℕ) (hk : 1 ≤ k) (x : Amb ((k-1)+m)) :
    inner ℝ (snocE k m hk x) (baseVec k m) = 0 := by
  rw [inner_baseVec k m hk, snocE_apply_ofLp_lastN]

theorem inner_baseVec_snocE (k m : ℕ) (hk : 1 ≤ k) (x : Amb ((k-1)+m)) :
    inner ℝ (baseVec k m) (snocE k m hk x) = 0 := by
  rw [real_inner_comm, inner_snocE_baseVec]

/-- Dropping the last coordinate: a left inverse of `snocE` on the last-coordinate-zero hyperplane. -/
def truncE (k m : ℕ) (hk : 1 ≤ k) (v : Amb (k+m)) : Amb ((k-1)+m) :=
  WithLp.toLp 2 (fun j : Fin ((k-1)+m) => v.ofLp ⟨j.val, by omega⟩)

theorem truncE_ofLp (k m : ℕ) (hk : 1 ≤ k) (v : Amb (k+m)) (j : Fin ((k-1)+m)) :
    (truncE k m hk v).ofLp j = v.ofLp ⟨j.val, by omega⟩ := rfl

theorem snocE_truncE (k m : ℕ) (hk : 1 ≤ k) (v : Amb (k+m))
    (hv : inner ℝ v (baseVec k m) = 0) : snocE k m hk (truncE k m hk v) = v := by
  have hv' : v.ofLp (lastk (k+m) (by omega)) = 0 := by
    rw [← inner_baseVec k m hk v]; exact hv
  apply PiLp.ext
  intro i
  by_cases hi : i.val < (k-1)+m
  · rw [snocE_apply_ofLp_lt k m hk _ i hi, truncE_ofLp]
  · have hlast : i = lastk (k+m) (by omega) := by
      apply Fin.ext
      simp only [lastk_val]
      have := i.isLt
      omega
    rw [hlast, snocE_apply_ofLp_lastN, hv']

theorem snocE_injective (k m : ℕ) (hk : 1 ≤ k) : Function.Injective (snocE k m hk) :=
  (snocE k m hk).injective

/-! ## The block matrix `diag(B,1)`, indexed by `Fin k` -/

/-- The block matrix `diag(B,1)` indexed by `Fin k` (for `k ≥ 1`): acting as `B` on the first `k-1`
coordinates and as `1` on the last one. -/
def blockMat (k : ℕ) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if hi : i.val < k-1 then
      (if hj : j.val < k-1 then B ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if _ : j.val < k-1 then 0 else 1)

@[simp] theorem blockMat_ct_ct (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ)
    (i j : Fin (k-1)) : blockMat k B (ct k hk i) (ct k hk j) = B i j := by
  rw [blockMat, dif_pos (by rw [ct_val]; exact i.isLt), dif_pos (by rw [ct_val]; exact j.isLt)]
  congr 1 <;> exact Fin.ext rfl

@[simp] theorem blockMat_ct_last (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ)
    (i : Fin (k-1)) : blockMat k B (ct k hk i) (lastk k hk) = 0 := by
  rw [blockMat, dif_pos (by rw [ct_val]; exact i.isLt), dif_neg (by rw [lastk_val]; omega)]

@[simp] theorem blockMat_last_ct (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ)
    (j : Fin (k-1)) : blockMat k B (lastk k hk) (ct k hk j) = 0 := by
  rw [blockMat, dif_neg (by rw [lastk_val]; omega), dif_pos (by rw [ct_val]; exact j.isLt)]

@[simp] theorem blockMat_last_last (k : ℕ) (hk : 1 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ) :
    blockMat k B (lastk k hk) (lastk k hk) = 1 := by
  rw [blockMat, dif_neg (by rw [lastk_val]; omega), dif_neg (by rw [lastk_val]; omega)]

end

end Work.ThomBordism.Grassmann
