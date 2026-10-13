import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

/-!
## The Taylor remainder estimate for EA functions: shared vocabulary

This module fixes the small vocabulary used by the proof of `eaTaylor_remainder`:

* `miFinset k N` is the finite set of multi-indices summed over by `eaTaylor`;
* `eMI i` is the multi-index `e_i` and `miS m i` is `m - e_i`;
* `eTayCoeff`, `eTay` and `eDTay` are the individual summands of a Taylor sum, the sum itself,
  and the summand of its `i`-th partial derivative.
-/

/-! ### Multi-index bookkeeping -/

/-- The finite set of multi-indices summed over by `eaTaylor`. -/
def miFinset (k N : ℕ) : Finset (Fin k → ℕ) :=
  ((Finset.univ : Finset (Fin k → Fin (N + 1))).image (fun m i => (m i : ℕ))).filter
    (fun m => ∑ i, m i ≤ N)

/-- `eaTaylor` rewritten as a sum over `miFinset`. -/
theorem eaTaylor_eq_sum {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) (y x : Fin k → ℝ) :
    eaTaylor c Q N y x = ∑ m ∈ miFinset k N,
      eaEval c (eaDmulti c m Q) y * ∏ i, (x i - y i) ^ m i / ((m i).factorial : ℝ) := rfl

theorem mem_miFinset {k N : ℕ} {m : Fin k → ℕ} : m ∈ miFinset k N ↔ ∑ i, m i ≤ N := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    refine Finset.mem_image.mpr ⟨fun i => ⟨m i, ?_⟩, Finset.mem_univ _, ?_⟩
    · exact Nat.lt_succ_of_le
        (le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) h)
    · rfl

/-- The multi-index `e_i`. -/
def eMI {k : ℕ} (i : Fin k) : Fin k → ℕ := fun j => if j = i then 1 else 0

/-- The multi-index `m - e_i`. -/
def miS {k : ℕ} (m : Fin k → ℕ) (i : Fin k) : Fin k → ℕ := m - eMI i

theorem eMI_apply {k : ℕ} (i j : Fin k) : eMI i j = if j = i then 1 else 0 := rfl

theorem miS_apply {k : ℕ} (m : Fin k → ℕ) (i j : Fin k) :
    miS m i j = m j - (if j = i then 1 else 0) := rfl

theorem miS_add_eMI {k : ℕ} {m : Fin k → ℕ} {i : Fin k} (h : 0 < m i) :
    miS m i + eMI i = m := by
  funext j
  simp only [Pi.add_apply, miS_apply, eMI_apply]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl]
    omega
  · rw [if_neg hj]
    omega

theorem sum_eMI {k : ℕ} (i : Fin k) : ∑ j, eMI i j = 1 := by
  rw [Finset.sum_eq_single i]
  · simp [eMI_apply]
  · intro j _ hj
    simp [eMI_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem miS_mem_miFinset {k N : ℕ} {m : Fin k → ℕ} {i : Fin k}
    (hm : m ∈ miFinset k (N + 1)) (hi : 0 < m i) : miS m i ∈ miFinset k N := by
  rw [mem_miFinset] at hm ⊢
  have hsum : ∑ j, m j = ∑ j, miS m i j + 1 := by
    conv_lhs => rw [← miS_add_eMI hi]
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_eMI i]
  omega

theorem eMI_mem_miFinset {k N : ℕ} {m : Fin k → ℕ} {i : Fin k} (hm : m ∈ miFinset k N) :
    m + eMI i ∈ miFinset k (N + 1) := by
  rw [mem_miFinset] at hm ⊢
  have hsum : ∑ j, (m + eMI i) j = ∑ j, m j + 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_eMI i]
  omega

theorem miS_eMI {k : ℕ} (m : Fin k → ℕ) (i : Fin k) : miS (m + eMI i) i = m := by
  funext j
  simp only [miS_apply, Pi.add_apply, eMI_apply]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl]
    omega
  · rw [if_neg hj]
    omega

/-! ### Taylor sums with arbitrary coefficients -/

/-- A single term of a Taylor sum: coefficient times the multi-index monomial. -/
def eTayCoeff {k : ℕ} (y : Fin k → ℝ) (b : (Fin k → ℕ) → ℝ) (m : Fin k → ℕ)
    (x : Fin k → ℝ) : ℝ :=
  b m * ∏ i, (x i - y i) ^ m i / ((m i).factorial : ℝ)

/-- A Taylor sum over a finite set `S` of multi-indices. -/
def eTay {k : ℕ} (y : Fin k → ℝ) (S : Finset (Fin k → ℕ)) (b : (Fin k → ℕ) → ℝ)
    (x : Fin k → ℝ) : ℝ :=
  ∑ m ∈ S, eTayCoeff y b m x

/-- The `i`-th partial derivative of a Taylor summand: the coefficient indexed by `m`, the
monomial shifted down by `e_i`. -/
def eDTay {k : ℕ} (y : Fin k → ℝ) (b : (Fin k → ℕ) → ℝ) (i : Fin k) (m : Fin k → ℕ)
    (x : Fin k → ℝ) : ℝ :=
  b m * ∏ j, (x j - y j) ^ (miS m i j) / ((miS m i j).factorial : ℝ)

theorem eTay_eq {k : ℕ} (y : Fin k → ℝ) (S : Finset (Fin k → ℕ))
    (b : (Fin k → ℕ) → ℝ) (x : Fin k → ℝ) :
    eTay y S b x = ∑ m ∈ S, eTayCoeff y b m x := rfl

theorem eaTaylor_eq_eTay {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) (y x : Fin k → ℝ) :
    eaTaylor c Q N y x = eTay y (miFinset k N) (fun m => eaEval c (eaDmulti c m Q) y) x :=
  eaTaylor_eq_sum c Q N y x

/-! ### The operators `eaDmulti` -/

/-- Iterating the identities leaves `Q` unchanged. -/
theorem foldr_eaD_zero {k r : ℕ} (c : EAChain k r) :
    ∀ (L : List (Fin k)) (g : EAPoly k r),
      L.foldr (fun i g => (eaD c i)^[((0 : Fin k → ℕ)) i] g) g = g := by
  intro L
  induction L with
  | nil => intro g; rfl
  | cons a l ih =>
    intro g
    show (eaD c a)^[((0 : Fin k → ℕ)) a]
        (l.foldr (fun i g => (eaD c i)^[((0 : Fin k → ℕ)) i] g) g) = g
    rw [ih]
    simp

theorem eaDmulti_zero {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    eaDmulti c 0 Q = Q :=
  foldr_eaD_zero c (List.finRange k) Q

/-- A fold whose exponents vanish off `i` does nothing. -/
theorem foldr_eMI_zero {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    ∀ (L : List (Fin k)) (i : Fin k), i ∉ L →
      L.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q = Q := by
  intro L
  induction L with
  | nil => intro i _; rfl
  | cons a l ih =>
    intro i hi
    rw [List.foldr_cons]
    show (eaD c a)^[((eMI i) a)]
        (List.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q l) = Q
    have ha : ¬ (a = i) := fun h => hi (by rw [← h]; exact List.mem_cons_self)
    have h0 : ((eMI i) a : ℕ) = 0 := by simp [eMI_apply, ha]
    rw [h0]
    show List.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q l = Q
    exact ih i (fun h => hi (List.mem_cons_of_mem a h))

/-- `eaDmulti c (e_i) Q = eaD c i Q`. -/
theorem eaDmulti_eMI {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    eaDmulti c (eMI i) Q = eaD c i Q := by
  have key : ∀ (L : List (Fin k)), L.Nodup → i ∈ L →
      L.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q = eaD c i Q := by
    intro L
    induction L with
    | nil => intro _ hmem; exact absurd hmem (by simp)
    | cons a l ih =>
      intro hnd hmem
      obtain ⟨hanot, hndl⟩ := List.nodup_cons.mp hnd
      rw [List.foldr_cons]
      show (eaD c a)^[((eMI i) a)]
          (List.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q l) = eaD c i Q
      rcases List.mem_cons.mp hmem with hia | hmeml
      · have hQ : List.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q l = Q :=
          foldr_eMI_zero c Q l i (fun h => hanot (by rw [← hia]; exact h))
        rw [hQ]
        rw [← hia]
        simp [eMI_apply, Function.iterate_one]
      · have ha : ¬ (a = i) := fun h => hanot (by rw [h]; exact hmeml)
        have h0 : ((eMI i) a : ℕ) = 0 := by simp [eMI_apply, ha]
        rw [h0]
        show List.foldr (fun j g => (eaD c j)^[((eMI i) j)] g) Q l = eaD c i Q
        exact ih hndl hmeml
  exact key (List.finRange k) (List.nodup_finRange k) (List.mem_finRange i)

/-! ### The values of `eaTaylor` at `x = y` -/

theorem eaTaylor_zero {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (y x : Fin k → ℝ) :
    eaTaylor c Q 0 y x = eaEval c Q y := by
  rw [eaTaylor_eq_sum, Finset.sum_eq_single (0 : Fin k → ℕ)]
  · rw [eaDmulti_zero]
    simp
  · intro m hm hne
    exfalso
    refine hne (funext fun i => ?_)
    exact Nat.eq_zero_of_le_zero (le_trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
      (mem_miFinset.mp hm))
  · intro h0
    exact absurd (mem_miFinset.mpr (by simp)) h0

theorem eaTaylor_self {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) (y : Fin k → ℝ) :
    eaTaylor c Q N y y = eaEval c Q y := by
  rw [eaTaylor_eq_sum, Finset.sum_eq_single (0 : Fin k → ℕ)]
  · rw [eaDmulti_zero]
    simp
  · intro m hm hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
    have hfac : ((y i0 - y i0) ^ (m i0) / ((m i0).factorial : ℝ)) = 0 := by
      rw [sub_self, zero_pow hi0, zero_div]
    have hprod : (∏ i, (y i - y i) ^ (m i) / ((m i).factorial : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i0) hfac
    rw [hprod, mul_zero]
  · intro h0
    exact absurd (mem_miFinset.mpr (by simp)) h0

/-! ### Bounds for coordinate-weighted linear maps -/

theorem norm_sum_smul_proj_le {k : ℕ} (a : Fin k → ℝ) :
    ‖(∑ i, a i • (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) :
        (Fin k → ℝ) →L[ℝ] ℝ)‖ ≤ ∑ i, |a i| := by
  let L : (Fin k → ℝ) →L[ℝ] ℝ :=
    ∑ i, a i • (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)
  change ‖L‖ ≤ ∑ i, |a i|
  refine ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg fun i _ => abs_nonneg _)
    fun v => ?_
  have h1 : L v = ∑ i, a i * v i := by
    simp [L, smul_eq_mul]
  rw [h1, Real.norm_eq_abs]
  calc |∑ i, a i * v i| ≤ ∑ i, |a i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |v i| := by simp [abs_mul]
    _ ≤ ∑ i, |a i| * ‖v‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)
    _ = (∑ i, |a i|) * ‖v‖ := by rw [Finset.sum_mul]

theorem pow_le_pow_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  have hb : 0 ≤ b := le_trans ha h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih h ha (pow_nonneg hb n)

/-- The derivative of a difference of two coordinate-weighted linear maps. -/
theorem sum_smul_proj_sub {k : ℕ} (a b : Fin k → ℝ) :
    ((∑ i, a i • (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) :
        (Fin k → ℝ) →L[ℝ] ℝ)
      - ∑ i, b i • (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i))
      = ∑ i, (a i - b i) • (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) := by
  ext v
  simp [Finset.sum_sub_distrib, sub_mul]

end

end Work.WilE3.API
