import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

/-!
# `U_ij` is an admissible (horospherical) subgroup

`Work.EKLContract.IsHoro U` is the frozen contract that `U ≤ SL₃(ℝ)` be a **closed** subgroup,
**normalised** by the diagonal group `A = {aDiag t}`, and **contracted** by some `aDiag t`
(EKL §2.1, Pisa Def. 6.2: the subgroups for which leafwise measures are available).

This file verifies it for the root groups `U_ij = {u_ij(s) = 1 + s E_ij}`, `i ≠ j`: the
result below states that `Work.EKLContract.IsHoro (Uij h)` holds.

The mathematical content:
* `Uij h` is the *range* of the one-parameter subgroup `s ↦ uij h s`
  (`horoUij_mem_iff`), hence
* it is closed: it is the set of `SL₃(ℝ)`-elements whose matrix agrees with the identity
  outside the single slot `(i,j)` (`horoUij_isClosed`);
* `aDiag t * u_ij(s) * (aDiag t)⁻¹ = u_ij(exp(t i - t j) * s)` (`horoUij_aDiag_conj`),
  because `aDiag t` is diagonal with entries `exp(t k - (∑t)/3)`; consequently the group is
  normalised by `A`;
* choosing `t` with `t i < t j` (e.g. `t k = if k = j then 1 else 0`), the conjugation
  factors `exp(n (t i - t j)) × s → 0`, so the `n`-th conjugate of any element of `U_ij`
  tends to `1` (`horoUij_tendsto_conj`).

Everything is proved from `Matrix.SpecialLinearGroup.transvection` and explicit `3 × 3`
matrix bookkeeping; nothing outside `Mathlib` is assumed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-! ## The one-parameter root subgroups `s ↦ u_ij(s)` -/

/-- `u_ij(s) = 1 + s E_ij` as an explicit matrix identity. -/
theorem horoUij_toMat {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    toMat (uij h s) = (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s :=
  Matrix.SpecialLinearGroup.transvection_coe h s

/-- `u_ij(0) = 1`. -/
theorem horoUij_zero {i j : Fin 3} (h : i ≠ j) : uij h 0 = (1 : SL3) :=
  Matrix.SpecialLinearGroup.transvection_coeff_zero h

/-- `U_ij` is exactly the range of the one-parameter subgroup `s ↦ u_ij(s)`
(the range is already a subgroup, so it equals its closure). -/
theorem horoUij_mem_iff {i j : Fin 3} (h : i ≠ j) (g : SL3) :
    g ∈ Uij h ↔ ∃ s : ℝ, uij h s = g := by
  constructor
  · intro hg
    let S : Subgroup SL3 :=
      { carrier := Set.range fun s : ℝ => uij h s
        one_mem' := ⟨0, horoUij_zero h⟩
        mul_mem' := by
          rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩
          exact ⟨s + t, Matrix.SpecialLinearGroup.transvection_add h s t⟩
        inv_mem' := by
          rintro a ⟨s, rfl⟩
          exact ⟨-s, (Matrix.SpecialLinearGroup.transvection_inv h s).symm⟩ }
    have hle : Uij h ≤ S := (Subgroup.closure_le S).2 (fun x hx => hx)
    exact hle hg
  · rintro ⟨s, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self s)

/-- `s ↦ u_ij(s)` is continuous (entrywise continuity of `1 + s E_ij`). -/
theorem horoUij_cont {i j : Fin 3} (h : i ≠ j) : Continuous (fun s : ℝ => uij h s) := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun s : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s) ?_ ?_
  refine Continuous.add continuous_const ?_
  refine continuous_matrix fun k l => ?_
  by_cases hkl : i = k ∧ j = l
  · simp only [Matrix.single_apply, if_pos hkl]; exact continuous_id
  · simp only [Matrix.single_apply, if_neg hkl]; exact continuous_const

/-! ## Closedness of `U_ij` -/

/-- Away from the slot `(i,j)`, `u_ij(s)` agrees with the identity. -/
theorem horoUij_apply_ne {i j : Fin 3} (h : i ≠ j) (s : ℝ) {k l : Fin 3}
    (hkl : ¬(i = k ∧ j = l)) :
    toMat (uij h s) k l = (1 : Matrix (Fin 3) (Fin 3) ℝ) k l := by
  rw [horoUij_toMat h, Matrix.add_apply, Matrix.single_apply, if_neg hkl, add_zero]

/-- Conversely, an element of `SL₃(ℝ)` agreeing with the identity outside the slot `(i,j)`
is `u_ij` of its `(i,j)`-entry. -/
theorem horoUij_eq_of_offdiag {i j : Fin 3} (h : i ≠ j) (A : SL3)
    (H : ∀ k l : Fin 3, ¬(i = k ∧ j = l) →
      toMat A k l = (1 : Matrix (Fin 3) (Fin 3) ℝ) k l) :
    uij h (toMat A i j) = A := by
  apply ext_toMat
  rw [horoUij_toMat h]
  ext k l
  rw [Matrix.add_apply, Matrix.single_apply]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl
    rw [if_pos ⟨rfl, rfl⟩, Matrix.one_apply_ne h, zero_add]
  · rw [if_neg hkl, add_zero, H k l hkl]

/-- `U_ij` is closed: as a set it is cut out by the (finitely many, continuous) conditions
that the entries outside the slot `(i,j)` equal those of the identity matrix. -/
theorem horoUij_isClosed {i j : Fin 3} (h : i ≠ j) :
    IsClosed ((Uij h : Subgroup SL3) : Set SL3) := by
  have hchar : ((Uij h : Subgroup SL3) : Set SL3) =
      {A : SL3 | ∀ k l : Fin 3, ¬(i = k ∧ j = l) →
        toMat A k l = (1 : Matrix (Fin 3) (Fin 3) ℝ) k l} := by
    ext A
    change A ∈ Uij h ↔ (∀ k l : Fin 3, ¬(i = k ∧ j = l) →
        toMat A k l = (1 : Matrix (Fin 3) (Fin 3) ℝ) k l)
    rw [horoUij_mem_iff h]
    constructor
    · rintro ⟨s, rfl⟩ k l hkl
      exact horoUij_apply_ne h s hkl
    · intro H
      exact ⟨toMat A i j, horoUij_eq_of_offdiag h A H⟩
  rw [hchar]
  have hset : {A : SL3 | ∀ k l : Fin 3, ¬(i = k ∧ j = l) →
        toMat A k l = (1 : Matrix (Fin 3) (Fin 3) ℝ) k l}
      = ⋂ (p : {p : Fin 3 × Fin 3 // ¬(i = p.1 ∧ j = p.2)}),
        {A : SL3 | toMat A p.1.1 p.1.2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1.1 p.1.2} := by
    ext A
    simp only [Set.mem_iInter, Subtype.forall]
    constructor
    · intro H a b; exact H a.1 a.2 b
    · intro H k l b; exact H (k, l) b
  rw [hset]
  refine isClosed_iInter fun p => ?_
  refine isClosed_eq ?_ continuous_const
  have hrow : Continuous fun A : SL3 => A p.1.1 :=
    Matrix.SpecialLinearGroup.continuous_apply _ continuous_id p.1.1
  exact (continuous_apply p.1.2).comp hrow

/-! ## Conjugation by the diagonal group `aDiag t` -/

/-- `diag(d) * (c · E_ij) = (d i · c) · E_ij`. -/
theorem horoUij_diagonal_mul_single (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext k l
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply, mul_ite, mul_zero]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl; simp
  · rw [if_neg hkl, if_neg hkl]

/-- `(c · E_ij) * diag(d) = (c · d j) · E_ij`. -/
theorem horoUij_single_mul_diagonal (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply, ite_mul, zero_mul]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl; simp
  · rw [if_neg hkl, if_neg hkl]

/-- `aDiag t · u_ij(s) = u_ij(exp(t i - t j) s) · aDiag t` (stated without inverting). -/
theorem horoUij_aDiag_mul (t : Fin 3 → ℝ) {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    aDiag t * uij h s = uij h (Real.exp (t i - t j) * s) * aDiag t := by
  apply ext_toMat
  rw [toMat_mul, toMat_mul, toMat_aDiag]
  rw [show toMat (uij h s) = (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s from
    Matrix.SpecialLinearGroup.transvection_coe h s]
  rw [show toMat (uij h (Real.exp (t i - t j) * s)) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j (Real.exp (t i - t j) * s) from
    Matrix.SpecialLinearGroup.transvection_coe h _]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul,
    horoUij_diagonal_mul_single, horoUij_single_mul_diagonal]
  rw [add_right_inj]
  congr 1
  have hexp : Real.exp (t i - t j) * Real.exp (t j - (∑ k, t k) / 3)
      = Real.exp (t i - (∑ k, t k) / 3) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (t i - (∑ k, t k) / 3) * s
      = s * Real.exp (t i - (∑ k, t k) / 3) := by ring
    _ = s * (Real.exp (t i - t j) * Real.exp (t j - (∑ k, t k) / 3)) := by rw [hexp]
    _ = (Real.exp (t i - t j) * s) * Real.exp (t j - (∑ k, t k) / 3) := by ring

/-- **Conjugation formula**: `aDiag t · u_ij(s) · (aDiag t)⁻¹ = u_ij(exp(t i - t j) · s)`.
In particular the diagonal group normalises `U_ij`. -/
theorem horoUij_aDiag_conj (t : Fin 3 → ℝ) {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    aDiag t * uij h s * (aDiag t)⁻¹ = uij h (Real.exp (t i - t j) * s) := by
  rw [horoUij_aDiag_mul t h s, mul_assoc, mul_inv_cancel, mul_one]

/-- `(aDiag t)^n = aDiag (n • t)`, in coordinates. -/
theorem horoUij_aDiag_pow (t : Fin 3 → ℝ) (n : ℕ) :
    (aDiag t) ^ n = aDiag (fun k => (n : ℝ) * t k) := by
  induction n with
  | zero =>
    rw [pow_zero]
    rw [show (fun k : Fin 3 => ((0 : ℕ) : ℝ) * t k) = (0 : Fin 3 → ℝ) from
      funext fun k => by simp]
    exact (aDiag_zero).symm
  | succ n ih =>
    have hthis : ((fun k : Fin 3 => (n : ℝ) * t k) + t)
        = fun k : Fin 3 => ((n + 1 : ℕ) : ℝ) * t k := by
      funext k
      change (n : ℝ) * t k + t k = ((n + 1 : ℕ) : ℝ) * t k
      push_cast
      ring
    rw [pow_succ, ih, aDiag_add, hthis]

/-! ## Contraction of `U_ij` -/

/-- If `t i < t j`, the `n`-th `aDiag t`-conjugate of `u_ij(s)` tends to `1`. -/
theorem horoUij_tendsto_conj (t : Fin 3 → ℝ) {i j : Fin 3} (h : i ≠ j) (ht : t i < t j)
    (s : ℝ) :
    Tendsto (fun n : ℕ => aDiag t ^ n * uij h s * (aDiag t ^ n)⁻¹) atTop (𝓝 1) := by
  have hseq : ∀ n : ℕ, aDiag t ^ n * uij h s * (aDiag t ^ n)⁻¹
      = uij h (Real.exp ((n : ℝ) * (t i - t j)) * s) := by
    intro n
    rw [horoUij_aDiag_pow t n, horoUij_aDiag_conj]
    congr 1
    rw [show (((fun k : Fin 3 => (n : ℝ) * t k) i) - ((fun k : Fin 3 => (n : ℝ) * t k) j))
        = (n : ℝ) * (t i - t j) from by ring]
  have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * s) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => Real.exp (t i - t j) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
        (Real.exp_lt_one_iff.mpr (by linarith))
    have hp' : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j))) atTop (𝓝 0) := by
      simpa only [Real.exp_nat_mul] using hp
    simpa using hp'.mul_const s
  have hmain : Tendsto (fun n : ℕ => uij h (Real.exp ((n : ℝ) * (t i - t j)) * s))
      atTop (𝓝 (uij h 0)) := (horoUij_cont h).tendsto 0 |>.comp htend
  rw [horoUij_zero h] at hmain
  simpa only [hseq] using hmain

/-! ## The target -/

theorem isHoro_Uij {i j : Fin 3} (h : i ≠ j) : Work.EKLContract.IsHoro (Work.EKLContract.Uij h) := by
  refine ⟨horoUij_isClosed h, ?_, ?_⟩
  · intro t u hu
    obtain ⟨s, rfl⟩ := (horoUij_mem_iff h u).mp hu
    rw [horoUij_aDiag_conj]
    exact (horoUij_mem_iff h _).mpr ⟨_, rfl⟩
  · refine ⟨fun k : Fin 3 => if k = j then 1 else 0, ?_⟩
    intro u hu
    obtain ⟨s, rfl⟩ := (horoUij_mem_iff h u).mp hu
    refine horoUij_tendsto_conj (fun k : Fin 3 => if k = j then 1 else 0) h ?_ s
    show (if i = j then 1 else 0) < (if j = j then 1 else 0)
    rw [if_neg h, if_pos rfl]
    norm_num

end Work.EKLContract.Lemmas
