import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero

/-!
# Transference auxiliary definitions (`Work.HP.Transf.Basic`)

Shared definitions and elementary calculus for the transference bound
`Work.HP.Transf.lamR_dual_le` (Mahler's transference, elementary proof).

* `dotRL v` : the linear functional `x ↦ ⟪v,x⟫` on `ι → ℝ`;
* `secLat v L` : the section lattice `L ∩ v^⊥` (a `ℤ`-submodule of `ι → ℝ`);
* `rkR L` : the dimension of the real span of a `ℤ`-submodule `L ⊆ ι → ℝ`;
* `trConst` : the recursive constant of the induction;
* elementary calculus for `dotR` / `rNorm`, and the basic API for `lamR`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

/-! ## Elementary calculus of `dotR` and `rNorm` -/

lemma dotR_comm (x y : ι → ℝ) : dotR x y = dotR y x := by
  rw [dotR, dotR]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dotR_add_left (x y z : ι → ℝ) : dotR (x + y) z = dotR x z + dotR y z := by
  simp only [dotR, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotR_add_right (x y z : ι → ℝ) : dotR x (y + z) = dotR x y + dotR x z := by
  simp only [dotR, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotR_sub_right (x y z : ι → ℝ) : dotR x (y - z) = dotR x y - dotR x z := by
  simp only [dotR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma dotR_sub_left (x y z : ι → ℝ) : dotR (x - y) z = dotR x z - dotR y z := by
  simp only [dotR, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma dotR_smul_left (c : ℝ) (x y : ι → ℝ) : dotR (c • x) y = c * dotR x y := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_smul_right (c : ℝ) (x y : ι → ℝ) : dotR x (c • y) = c * dotR x y := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_self_nonneg (x : ι → ℝ) : 0 ≤ dotR x x := by
  rw [dotR]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma rNorm_nonneg (x : ι → ℝ) : 0 ≤ rNorm x := Real.sqrt_nonneg _

lemma rNorm_sq (x : ι → ℝ) : rNorm x ^ 2 = dotR x x := by
  rw [rNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i)), dotR]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] lemma rNorm_eq_zero_iff {x : ι → ℝ} : rNorm x = 0 ↔ x = 0 := by
  have h : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [rNorm, Real.sqrt_eq_zero h]
  constructor
  · intro h0
    funext i
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp h0 i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  · rintro rfl
    simp

@[simp] lemma rNorm_zero : rNorm (0 : ι → ℝ) = 0 := rNorm_eq_zero_iff.mpr rfl

@[simp] lemma dotR_self_eq_zero {x : ι → ℝ} : dotR x x = 0 ↔ x = 0 := by
  rw [← rNorm_sq, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), rNorm_eq_zero_iff]

@[simp] lemma dotR_zero_left (y : ι → ℝ) : dotR 0 y = 0 := by
  rw [dotR]; simp

@[simp] lemma dotR_zero_right (x : ι → ℝ) : dotR x 0 = 0 := by
  rw [dotR_comm, dotR_zero_left]

lemma rNorm_pos_iff {x : ι → ℝ} : 0 < rNorm x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    rw [hx, rNorm_zero] at h
    exact absurd h (lt_irrefl 0)
  · intro hx
    refine lt_of_le_of_ne (rNorm_nonneg x) (fun h => hx ?_)
    exact rNorm_eq_zero_iff.mp h.symm

lemma rNorm_smul (c : ℝ) (x : ι → ℝ) : rNorm (c • x) = |c| * rNorm x := by
  have hsum : (∑ i, ((c • x) i) ^ 2) = c ^ 2 * ∑ i, (x i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [rNorm, hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rfl

lemma dotR_cauchy (x y : ι → ℝ) : |dotR x y| ≤ rNorm x * rNorm y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) x y
  have hx : rNorm x ^ 2 = ∑ i, (x i) ^ 2 := by
    rw [rNorm_sq, dotR]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hy : rNorm y ^ 2 = ∑ i, (y i) ^ 2 := by
    rw [rNorm_sq, dotR]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : dotR x y ^ 2 ≤ (rNorm x * rNorm y) ^ 2 := by
    rw [dotR, mul_pow, hx, hy]
    exact h
  calc |dotR x y| = √(dotR x y ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √((rNorm x * rNorm y) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = rNorm x * rNorm y := by
        rw [Real.sqrt_sq_eq_abs _, abs_of_nonneg (mul_nonneg (rNorm_nonneg x) (rNorm_nonneg y))]

lemma rNorm_triangle (x y : ι → ℝ) : rNorm (x + y) ≤ rNorm x + rNorm y := by
  have h1 : rNorm (x + y) ^ 2 = rNorm x ^ 2 + 2 * dotR x y + rNorm y ^ 2 := by
    rw [rNorm_sq, rNorm_sq, rNorm_sq, dotR_add_left, dotR_add_right, dotR_add_right, dotR_comm y x]
    ring
  have h2 : rNorm (x + y) ^ 2 ≤ (rNorm x + rNorm y) ^ 2 := by
    rw [h1]
    nlinarith [dotR_cauchy x y, le_abs_self (dotR x y), rNorm_nonneg x, rNorm_nonneg y]
  have h3 := sq_le_sq.mp h2
  rwa [abs_of_nonneg (rNorm_nonneg _),
    abs_of_nonneg (add_nonneg (rNorm_nonneg x) (rNorm_nonneg y))] at h3

lemma rNorm_sub_le (x y : ι → ℝ) : rNorm (x - y) ≤ rNorm x + rNorm y := by
  have h : x - y = x + (-1 : ℝ) • y := by
    ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h]
  refine (rNorm_triangle x ((-1 : ℝ) • y)).trans_eq ?_
  rw [rNorm_smul]
  simp

lemma rNorm_le_rNorm_sub_add (x y : ι → ℝ) : rNorm x ≤ rNorm (x - y) + rNorm y := by
  have h : x = (x - y) + y := by abel
  conv_lhs => rw [h]
  exact rNorm_triangle _ _

lemma rNorm_sum_le {α : Type*} (s : Finset α) (f : α → ι → ℝ) :
    rNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, rNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (rNorm_triangle _ _).trans (add_le_add le_rfl ih)

lemma rNorm_add_sq_of_orthogonal {x y : ι → ℝ} (h : dotR x y = 0) :
    rNorm (x + y) ^ 2 = rNorm x ^ 2 + rNorm y ^ 2 := by
  rw [rNorm_sq, rNorm_sq, rNorm_sq, dotR_add_left, dotR_add_right, dotR_add_right, h,
    dotR_comm y x, h]
  ring

lemma dotR_proj_perp (v w : ι → ℝ) :
    dotR v (w - ((dotR v w) / (rNorm v) ^ 2) • v) = 0 := by
  rw [dotR_sub_right, dotR_smul_right, ← rNorm_sq]
  by_cases hv : rNorm v = 0
  · rw [rNorm_eq_zero_iff.mp hv]
    simp
  · field_simp
    ring

/-! ## The linear functional `x ↦ ⟪v,x⟫` and the section lattice -/

/-- The `ℝ`-linear functional `x ↦ ⟪v,x⟫`. -/
def dotRL (v : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, v i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] lemma dotRL_apply (v x : ι → ℝ) : dotRL v x = ∑ i, v i * x i := rfl

lemma dotRL_eq_dotR (v x : ι → ℝ) : dotRL v x = dotR v x := rfl

/-- The section lattice `L ∩ v^⊥`. -/
def secLat (v : ι → ℝ) (L : Submodule ℤ (ι → ℝ)) : Submodule ℤ (ι → ℝ) where
  carrier := {y | y ∈ L ∧ dotR v y = 0}
  zero_mem' := ⟨L.zero_mem, by simp [dotR]⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨L.add_mem ha1 hb1, by rw [dotR_add_right, ha2, hb2, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨L.smul_mem c ha1, ?_⟩
    have h : dotR v (c • a) = (c : ℝ) * dotR v a := by
      simp only [dotR, Pi.smul_apply, zsmul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, ha2, mul_zero]

@[simp] lemma mem_secLat {v y : ι → ℝ} {L : Submodule ℤ (ι → ℝ)} :
    y ∈ secLat v L ↔ y ∈ L ∧ dotR v y = 0 := Iff.rfl

lemma secLat_le (v : ι → ℝ) (L : Submodule ℤ (ι → ℝ)) : secLat v L ≤ L :=
  fun _ hy => hy.1

/-- The dimension of the real span of a `ℤ`-submodule of `ℝ^ι`. -/
def rkR (L : Submodule ℤ (ι → ℝ)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (L : Set (ι → ℝ)))

lemma rkR_le_card (L : Submodule ℤ (ι → ℝ)) : rkR L ≤ Fintype.card ι := by
  have h := Submodule.finrank_le (Submodule.span ℝ (L : Set (ι → ℝ)))
  rwa [Module.finrank_fintype_fun_eq_card] at h

/-! ## The basic API for `lamR` -/

lemma bddBelow_lamRset (L : Submodule ℤ (ι → ℝ)) (i : ℕ) :
    BddBelow {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r} :=
  ⟨0, fun _ hr => hr.1⟩

lemma lamR_nonneg (L : Submodule ℤ (ι → ℝ)) (i : ℕ) : 0 ≤ lamR L i := by
  have hdef : lamR L i = sInf (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r) := rfl
  rw [hdef]
  by_cases h : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r).Nonempty
  · exact le_csInf h fun x hx => hx.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- The first successive minimum is at most the norm of any nonzero lattice vector. -/
lemma lamR_le_rNorm (L : Submodule ℤ (ι → ℝ)) {v : ι → ℝ} (hv : v ∈ L) (hv0 : v ≠ 0) :
    lamR L 1 ≤ rNorm v := by
  rw [lamR]
  refine csInf_le (bddBelow_lamRset L 1) ?_
  refine ⟨rNorm_nonneg v, fun _ : Fin 1 => v, fun _ => hv, ?_, fun _ => le_rfl⟩
  rw [linearIndependent_unique_iff]
  exact hv0

/-- If `L` contains a nonzero vector, every `c > lamR L 1` is the norm bound of a nonzero
vector of `L`. -/
lemma exists_norm_le_of_lamR_lt (L : Submodule ℤ (ι → ℝ)) (hne : ∃ v ∈ L, v ≠ 0) {c : ℝ}
    (h : lamR L 1 < c) : ∃ v ∈ L, v ≠ 0 ∧ rNorm v ≤ c := by
  have hsetne : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin 1 → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r).Nonempty := by
    obtain ⟨v, hv, hv0⟩ := hne
    exact ⟨rNorm v, rNorm_nonneg v, fun _ : Fin 1 => v, fun _ => hv,
      by rw [linearIndependent_unique_iff]; exact hv0, fun _ => le_rfl⟩
  rw [lamR] at h
  obtain ⟨r, ⟨hr0, f, hfL, hfI, hfr⟩, hrc⟩ := exists_lt_of_csInf_lt hsetne h
  exact ⟨f 0, hfL 0, hfI.ne_zero 0, (hfr 0).trans hrc.le⟩

/-- If all elements of `L` vanish then `lamR L 1 = 0`. -/
lemma lamR_eq_zero_of_all_zero (L : Submodule ℤ (ι → ℝ)) (h : ∀ v ∈ L, v = 0) :
    lamR L 1 = 0 := by
  have hdef : lamR L 1 = sInf (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin 1 → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r) := rfl
  rw [hdef]
  have hempty : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin 1 → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r) = ∅ := by
    ext r
    constructor
    · rintro ⟨-, f, hfL, hfI, -⟩
      exact absurd (h (f 0) (hfL 0)) (hfI.ne_zero 0)
    · intro hr
      exact absurd hr (Set.notMem_empty r)
  rw [hempty, Real.sInf_empty]

lemma exists_ne_zero_of_lamR_ne_zero (L : Submodule ℤ (ι → ℝ))
    (h : lamR L 1 ≠ 0) : ∃ v ∈ L, v ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (lamR_eq_zero_of_all_zero L fun v hv => hc v hv)

/-! ## The recursive constant -/

/-- The constant of the induction: `trConst R` bounds `λ_R(L)·λ_1(L*)`. -/
def trConst : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 8 * ((n : ℝ) + 1) * trConst n + 2

lemma trConst_zero : trConst 0 = 1 := rfl

lemma trConst_succ (n : ℕ) : trConst (n + 1) = 8 * ((n : ℝ) + 1) * trConst n + 2 := rfl

lemma trConst_pos : ∀ n, 0 < trConst n
  | 0 => by rw [trConst_zero]; norm_num
  | (n + 1) => by
      rw [trConst_succ]
      have h1 := trConst_pos n
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith

lemma trConst_le_succ (n : ℕ) : trConst n ≤ trConst (n + 1) := by
  rw [trConst_succ]
  have h1 := trConst_pos n
  have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

lemma trConst_mono : ∀ {m n : ℕ}, m ≤ n → trConst m ≤ trConst n
  | m, 0, h => by simp only [Nat.le_zero.mp h, le_rfl]
  | m, (n + 1), h => by
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact (trConst_mono (Nat.lt_succ_iff.mp hlt)).trans (trConst_le_succ n)

lemma four_trConst_le (n : ℕ) : 4 * trConst n ≤ trConst (n + 1) := by
  rw [trConst_succ]
  have h1 := trConst_pos n
  have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  nlinarith

end Work.HP.Transf

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

@[simp] lemma dotR_neg_right (x y : ι → ℝ) : dotR x (-y) = -dotR x y := by
  rw [neg_eq_zero_sub, dotR_sub_right, dotR_zero_right, zero_sub]

@[simp] lemma dotR_neg_left (x y : ι → ℝ) : dotR (-x) y = -dotR x y := by
  rw [neg_eq_zero_sub, dotR_sub_left, dotR_zero_left, zero_sub]

lemma dotR_zsmul_right (c : ℤ) (x y : ι → ℝ) : dotR x (c • y) = (c : ℝ) * dotR x y := by
  simp only [dotR, Pi.smul_apply, zsmul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_zsmul_left (c : ℤ) (x y : ι → ℝ) : dotR (c • x) y = (c : ℝ) * dotR x y := by
  simp only [dotR, Pi.smul_apply, zsmul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_natCast_smul_right (c : ℕ) (x y : ι → ℝ) : dotR x (c • y) = (c : ℝ) * dotR x y := by
  simpa using dotR_zsmul_right (ι := ι) (c := (c : ℤ)) x y

end Work.HP.Transf
