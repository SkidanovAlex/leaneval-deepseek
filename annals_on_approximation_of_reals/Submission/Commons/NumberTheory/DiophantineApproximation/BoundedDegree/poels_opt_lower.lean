import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Log.mul_log_one_add_inv_le_one
import Submission.Commons.Analysis.SpecialFunctions.Log.three_sub_two_mul_add_log_le
import Submission.Commons.Analysis.SpecialFunctions.Log.two_sub_log_two_pos
import Submission.Commons.NumberTheory.Pow.rat_pow_ne_two

open Real
open scoped BigOperators

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

set_option autoImplicit false

/-! ## Logarithm facts.  The main constant is `c := 1 / (2 - log 2)`. -/

lemma log_two_lt_one : Real.log 2 < 1 := by
  have h := log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h
  exact h

lemma two_sub_log_two_pos' : 0 < (2 : ℝ) - Real.log 2 := by
  linarith [log_two_lt_one]

lemma two_sub_log_two_ge_one : (1 : ℝ) ≤ 2 - Real.log 2 := by
  linarith [log_two_lt_one]

noncomputable def cval : ℝ := 1 / (2 - Real.log 2)

lemma cval_pos : 0 < cval := by
  unfold cval
  exact one_div_pos.mpr two_sub_log_two_pos'

lemma cval_le_one : cval ≤ 1 := by
  unfold cval
  rw [div_le_iff₀ two_sub_log_two_pos']
  simpa using two_sub_log_two_ge_one

lemma cval_ne_zero : cval ≠ 0 := ne_of_gt cval_pos

lemma two_sub_log_two_mul_cval : (2 - Real.log 2) * cval = 1 := by
  unfold cval
  field_simp [ne_of_gt two_sub_log_two_pos']

lemma cval_mul_two_sub_log_two : cval * (2 - Real.log 2) = 1 := by
  rw [mul_comm, two_sub_log_two_mul_cval]

/-! For the final step we use the two logarithm bounds from the commons:
`mul_log_one_add_inv_le_one` : `t * log (1 + 1/t) ≤ 1` for `t > 0`
`three_sub_two_mul_add_log_le` : `3 - 2t + log t ≤ 2 - log 2` for `t > 0`. -/

/-! ## Shifted-index representation
We index the meaningful terms of a sequence by `j = 0, ..., n-1`
(corresponding to paper indices `2, ..., n+1`, i.e. `a (j+2)`).
`bpart b m = ∑_{j < m} b j` is the partial sum of the first `m` terms. -/

section Defs

/-- partial sum of the first `m` terms -/
noncomputable def bpart (b : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, b j

/-- total sum `x = ∑_{j < n} b j` -/
noncomputable def bx (b : ℕ → ℝ) (n : ℕ) : ℝ := bpart b n

/-- `2x - 2(n-1-m) - (sum of first m+1 terms)`, over `b m` -/
noncomputable def brat (n : ℕ) (x : ℝ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  (2 * x - 2 * ((n : ℝ) - 1 - (m : ℝ)) - bpart b (m + 1)) / b m

/-- the max over `m ∈ range n` of `brat` -/
noncomputable def bF (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (b : ℕ → ℝ) : ℝ :=
  (Finset.range n).sup' (Finset.nonempty_range_iff.mpr (by omega : n ≠ 0)) (fun m => brat n x b m)

lemma bF_le_iff (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (b : ℕ → ℝ) (y : ℝ) :
    bF n hn x b ≤ y ↔ ∀ m ∈ Finset.range n, brat n x b m ≤ y := by
  unfold bF
  rw [Finset.sup'_le_iff]

lemma le_bF_of_mem (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (b : ℕ → ℝ) {m : ℕ}
    (hm : m ∈ Finset.range n) : brat n x b m ≤ bF n hn x b := by
  unfold bF
  exact Finset.le_sup' (fun m => brat n x b m) hm

lemma bpart_succ (b : ℕ → ℝ) (m : ℕ) : bpart b (m + 1) = bpart b m + b m := by
  unfold bpart
  rw [Finset.sum_range_succ]

lemma bx_eq_bpart (b : ℕ → ℝ) (n : ℕ) : bx b n = bpart b n := rfl

/-- `brat` at the last index `n-1` equals `x / b(n-1)` (for `1 ≤ n`) -/
lemma brat_last (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (b : ℕ → ℝ) (hx : bx b n = x) :
    brat n x b (n - 1) = x / b (n - 1) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hnat : ((n - 1 : ℕ) + 1 : ℕ) = n := Nat.sub_add_cancel hn
    have h1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast hnat
    linarith
  have h : ((n : ℝ) - 1 - ((n - 1 : ℕ) : ℝ)) = 0 := by
    rw [hcast]
    ring
  have hnat' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hsum : (∑ j ∈ Finset.range (n - 1 + 1), b j) = (∑ j ∈ Finset.range n, b j) := by
    rw [hnat']
  unfold brat at ⊢
  unfold bx at hx
  rw [h]
  norm_num
  change (2 * x - (∑ j ∈ Finset.range (n - 1 + 1), b j)) / b (n - 1) = x / b (n - 1)
  rw [hsum]
  have hpart : (∑ j ∈ Finset.range n, b j) = x := by simpa [bx, bpart] using hx
  rw [hpart]
  ring

/-- `brat` at index `0` equals `2x - 2(n-1) - 1` when `b 0 = 1` -/
lemma brat_zero (n : ℕ) (x : ℝ) (b : ℕ → ℝ) (hb0 : b 0 = 1) :
    brat n x b 0 = 2 * x - 2 * ((n : ℝ) - 1) - 1 := by
  unfold brat
  have hb : bpart b 1 = 1 := by
    unfold bpart
    simp [hb0]
  rw [hb, hb0]
  simp

end Defs

/-! ## The domain `D` : admissible, total in `[n, (3n-1)/2]`, tail padded by 1 -/

section Domain

/-- basic admissibility: `b 0 = 1`, terms `≥ 1`, weakly increasing, total `≥ n`. -/
def bAdm (n : ℕ) (b : ℕ → ℝ) : Prop :=
  b 0 = 1 ∧ (∀ j, j < n → 1 ≤ b j) ∧ (∀ j, j + 1 < n → b j ≤ b (j + 1)) ∧
    ((n : ℝ) ≤ bx b n)

/-- the feasible (compact) domain: admissible, `bx ≤ (3n-1)/2`, tail equal to 1. -/
def D (n : ℕ) : Set (ℕ → ℝ) :=
  {b | bAdm n b ∧ bx b n ≤ ((3 * (n : ℝ) - 1) / 2) ∧ ∀ j, n ≤ j → b j = 1}

/-- value functional with `x = bx b n` -/
noncomputable def bval (n : ℕ) (hn : 2 ≤ n) (b : ℕ → ℝ) : ℝ := bF n hn (bx b n) b

lemma bAdm_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) : bAdm n b := (hb.1)
lemma bx_le_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) : bx b n ≤ ((3 * (n : ℝ) - 1) / 2) := hb.2.1
lemma tail_one_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) {j : ℕ} (hj : n ≤ j) : b j = 1 := hb.2.2 j hj
lemma b0_eq_one_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) : b 0 = 1 :=
  (bAdm_of_mem_D hb).1
lemma one_le_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) {j : ℕ} (hj : j < n) : 1 ≤ b j :=
  (bAdm_of_mem_D hb).2.1 j hj
lemma mono_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) {j : ℕ} (hj : j + 1 < n) : b j ≤ b (j + 1) :=
  (bAdm_of_mem_D hb).2.2.1 j hj
lemma n_le_bx_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) : (n : ℝ) ≤ bx b n :=
  (bAdm_of_mem_D hb).2.2.2
lemma bpos_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) {j : ℕ} (hj : j < n) : b j ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num) (one_le_of_mem_D hb hj))

/-- the box of all coordinates, compact by Tychonoff -/
def BoxAll (n : ℕ) : Set (ℕ → ℝ) := {b | ∀ j, (0 : ℝ) ≤ b j ∧ b j ≤ (n : ℝ)}

lemma isCompact_BoxAll (n : ℕ) : IsCompact (BoxAll n) := by
  have hpi : IsCompact {x : ℕ → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) (n : ℝ)} := by
    exact isCompact_pi_infinite (fun _ : ℕ => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (n : ℝ))))
  simpa [BoxAll, Set.mem_Icc] using hpi

end Domain

/-- monotone consequence of the consecutive monotonicity inside `D` -/
lemma mono_le_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    b i ≤ b j := by
  have main : ∀ t : ℕ, ∀ i j : ℕ, i ≤ j → j - i = t → j < n → b i ≤ b j := by
    intro t
    induction t with
    | zero =>
        intro i j hij hdiff hj
        have : i = j := by omega
        subst j
        exact le_rfl
    | succ t ih =>
        intro i j hij hdiff hj
        by_cases h : i = j
        · subst j
          exact le_rfl
        · have hlt : i < j := lt_of_le_of_ne hij h
          have hsub : (j - 1) - i = t := by omega
          have hmem : i ≤ j - 1 := by omega
          have hltn : j - 1 < n := by omega
          have hprev := ih i (j - 1) hmem hsub hltn
          have hsub' : (j - 1) + 1 = j := by omega
          have hstep : b (j - 1) ≤ b j := by
            have hst := mono_of_mem_D hb (n := n) (j := j - 1) (by omega : (j - 1) + 1 < n)
            simpa [hsub'] using hst
          exact le_trans hprev hstep
  exact main (j - i) i j hij rfl hj

/-- inside `D`, `b j ≤ n` for `j < n` -/
lemma coord_box_of_mem_D {n : ℕ} {b : ℕ → ℝ} (hb : b ∈ D n) (j : ℕ) (hj : j < n) :
    (0 : ℝ) ≤ b j ∧ b j ≤ (n : ℝ) := by
  constructor
  · linarith [one_le_of_mem_D hb hj]
  · let s' : Finset ℕ := (Finset.range n).erase j
    have hj' : j ∈ Finset.range n := Finset.mem_range.mpr hj
    have hdecomp : (∑ i ∈ Finset.range n, b i) = b j + (∑ i ∈ s', b i) := by
      calc
        (∑ i ∈ Finset.range n, b i) = (∑ i ∈ insert j s', b i) := by
          rw [Finset.insert_erase hj']
        _ = b j + (∑ i ∈ s', b i) := by
          rw [Finset.sum_insert (by simp [s']) ]
    have hterm : ∀ x ∈ s', (1 : ℝ) ≤ b x := by
      intro x hx
      exact one_le_of_mem_D hb (Finset.mem_range.mp (Finset.mem_erase.mp hx).2)
    have hcard : (s'.card : ℝ) = (n - 1 : ℕ) := by
      simp [s', Finset.card_erase_of_mem hj']
    have hge : ((n - 1 : ℕ) : ℝ) ≤ (∑ i ∈ s', b i) := by
      calc
        ((n - 1 : ℕ) : ℝ) = (s'.card : ℝ) := by rw [hcard]
        _ = (∑ i ∈ s', (1 : ℝ)) := by simp
        _ ≤ (∑ i ∈ s', b i) := Finset.sum_le_sum hterm
    have hsum : bx b n = b j + (∑ i ∈ s', b i) := by
      unfold bx bpart
      exact hdecomp
    have hle : b j ≤ bx b n - ((n - 1 : ℕ) : ℝ) := by linarith
    have hupper : bx b n - ((n - 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
      have h1 : bx b n ≤ ((3 * (n : ℝ) - 1) / 2) := bx_le_of_mem_D hb
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      linarith
    have hcast2 : ((n : ℝ) + 1) / 2 ≤ (n : ℝ) := by
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    nlinarith


/-! ## Continuity facts -/

section ContinuousFacts

lemma continuous_bpart (n : ℕ) : Continuous fun b : ℕ → ℝ => bpart b n := by
  induction n with
  | zero =>
      have h : (fun b : ℕ → ℝ => bpart b 0) = fun _ => (0 : ℝ) := by
        funext b
        simp [bpart]
      rw [h]
      fun_prop
  | succ n ih =>
      have h : (fun b : ℕ → ℝ => bpart b (n + 1)) = fun b => bpart b n + b n := by
        funext b
        rw [bpart_succ]
      rw [h]
      exact ih.add (continuous_apply n)

lemma continuousOn_bx_D (n : ℕ) : ContinuousOn (fun b : ℕ → ℝ => bx b n) (D n) := by
  unfold bx
  exact (continuous_bpart n).continuousOn (s := D n)

lemma continuousOn_brat_D (n : ℕ) (m : ℕ) (hm : m < n) :
    ContinuousOn (fun b : ℕ → ℝ => brat n (bx b n) b m) (D n) := by
  unfold brat
  refine ContinuousOn.div₀ ?hf ?hg ?h₀
  · have h1 : Continuous (fun b : ℕ → ℝ => (2 : ℝ) * bx b n) := by
      unfold bx
      exact (continuous_bpart n).const_mul 2
    have h2 : Continuous (fun b : ℕ → ℝ => 2 * ((n : ℝ) - 1 - (m : ℝ))) := continuous_const
    have h3 : Continuous (fun b : ℕ → ℝ => bpart b (m + 1)) := continuous_bpart (m + 1)
    have hnum : Continuous
        (fun b : ℕ → ℝ => 2 * bx b n - 2 * ((n : ℝ) - 1 - (m : ℝ)) - bpart b (m + 1)) :=
      (h1.sub h2).sub h3
    exact hnum.continuousOn (s := D n)
  · exact (continuous_apply m).continuousOn (s := D n)
  · intro b hb
    exact bpos_of_mem_D hb (by omega : m < n)

/-- `bval` is continuous on `D` -/
lemma continuousOn_bval_D (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (fun b : ℕ → ℝ => bval n hn b) (D n) := by
  unfold bval bF
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr (by omega : n ≠ 0)
  apply ContinuousOn.finset_sup'_apply hne
  intro m hm
  exact continuousOn_brat_D n m (Finset.mem_range.mp hm)

end ContinuousFacts

/-! ## Compactness of `D` and the minimizer -/

section Minimizer

lemma forall_lt_nat_iff_fin (n : ℕ) (P : ℕ → Prop) :
    (∀ j, j < n → P j) ↔ ∀ j : Fin n, P j.val := by
  constructor
  · intro h j
    exact h j.val j.isLt
  · intro h j hj
    exact h ⟨j, hj⟩

lemma forall_succ_lt_iff_fin (n : ℕ) (P : ℕ → Prop) :
    (∀ j : ℕ, j + 1 < n → P j) ↔ ∀ j : Fin n, j.val + 1 < n → P j.val := by
  constructor
  · intro h j hj
    exact h j.val hj
  · intro h j hj
    exact h ⟨j, (by omega : j < n)⟩ hj

lemma forall_ge_nat_iff_subtype (n : ℕ) (P : ℕ → Prop) :
    (∀ j, n ≤ j → P j) ↔ ∀ j : {j : ℕ // n ≤ j}, P j.val := by
  constructor
  · intro h j
    exact h j.val j.property
  · intro h j hj
    exact h ⟨j, hj⟩

lemma isClosed_D (n : ℕ) : IsClosed (D n) := by
  have h1 : IsClosed {b : ℕ → ℝ | b 0 = 1} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have h2 : IsClosed {b : ℕ → ℝ | ∀ j : Fin n, 1 ≤ b j.val} := by
    have hEq : {b : ℕ → ℝ | ∀ j : Fin n, 1 ≤ b j.val} =
        ⋂ j : Fin n, {b : ℕ → ℝ | 1 ≤ b j.val} := by
      ext b
      simp
    rw [hEq]
    exact isClosed_iInter (fun j : Fin n => isClosed_le continuous_const (continuous_apply j.val))
  have h3 : IsClosed {b : ℕ → ℝ | ∀ j : Fin n, j.val + 1 < n → b j.val ≤ b (j.val + 1)} := by
    have hEq : {b : ℕ → ℝ | ∀ j : Fin n, j.val + 1 < n → b j.val ≤ b (j.val + 1)} =
        ⋂ j : Fin n, {b : ℕ → ℝ | j.val + 1 < n → b j.val ≤ b (j.val + 1)} := by
      ext b
      simp
    rw [hEq]
    exact isClosed_iInter (fun j : Fin n => by
      by_cases h : j.val + 1 < n
      · have : {b : ℕ → ℝ | j.val + 1 < n → b j.val ≤ b (j.val + 1)}
          = {b | b j.val ≤ b (j.val + 1)} := by
          ext b
          simp [h]
        rw [this]
        exact isClosed_le (continuous_apply j.val) (continuous_apply (j.val + 1))
      · have : {b : ℕ → ℝ | j.val + 1 < n → b j.val ≤ b (j.val + 1)} = Set.univ := by
          ext b
          simp [h]
        rw [this]
        exact isClosed_univ)
  have h4 : IsClosed {b : ℕ → ℝ | (n : ℝ) ≤ bx b n} := by
    unfold bx
    exact isClosed_le continuous_const (continuous_bpart n)
  have h5 : IsClosed {b : ℕ → ℝ | bx b n ≤ ((3 * (n : ℝ) - 1) / 2)} := by
    unfold bx
    exact isClosed_le (continuous_bpart n) continuous_const
  have h6 : IsClosed {b : ℕ → ℝ | ∀ j : {j : ℕ // n ≤ j}, b j.val = 1} := by
    have hEq : {b : ℕ → ℝ | ∀ j : {j : ℕ // n ≤ j}, b j.val = 1} =
        ⋂ j : {j : ℕ // n ≤ j}, {b : ℕ → ℝ | b j.val = 1} := by
      ext b
      simp
    rw [hEq]
    exact isClosed_iInter (fun j : {j : ℕ // n ≤ j} =>
      isClosed_eq (continuous_apply j.val) continuous_const)
  -- D n equals that intersection
  have hEq : D n = {b | b 0 = 1} ∩ {b | ∀ j : Fin n, 1 ≤ b j.val} ∩
      {b | ∀ j : Fin n, j.val + 1 < n → b j.val ≤ b (j.val + 1)} ∩
      {b | (n : ℝ) ≤ bx b n} ∩ {b | bx b n ≤ ((3 * (n : ℝ) - 1) / 2)} ∩
      {b | ∀ j : {j : ℕ // n ≤ j}, b j.val = 1} := by
    ext b
    simp only [D, bAdm, Set.mem_setOf_eq, Set.mem_inter_iff]
    -- LHS: (b0=1 ∧ (∀j<n,1≤bj) ∧ (∀j,j+1<n,bj≤bj+1) ∧ n≤bx) ∧ upper ∧ (∀j≥n, bj=1)
    rw [forall_lt_nat_iff_fin n (fun j => 1 ≤ b j)]
    rw [forall_succ_lt_iff_fin n (fun j => b j ≤ b (j + 1))]
    rw [forall_ge_nat_iff_subtype n (fun j => b j = 1)]
    tauto
  rw [hEq]
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

lemma D_subset_BoxAll (n : ℕ) (hn : 2 ≤ n) : D n ⊆ BoxAll n := by
  intro b hb j
  by_cases hj : j < n
  · exact coord_box_of_mem_D hb j hj
  · have hnle : n ≤ j := by omega
    have htail : b j = 1 := tail_one_of_mem_D hb hnle
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    rw [htail]
    constructor <;> linarith

lemma isCompact_D (n : ℕ) (hn : 2 ≤ n) : IsCompact (D n) :=
  IsCompact.of_isClosed_subset (isCompact_BoxAll n) (isClosed_D n) (D_subset_BoxAll n hn)

/-- the all-ones function -/
noncomputable def ones (n : ℕ) : ℕ → ℝ := fun _ => 1

lemma bx_ones (n : ℕ) : bx (ones n) n = (n : ℝ) := by
  unfold bx bpart ones
  simp

/-- `brat` only depends on `b j` for `j ≤ m` -/
lemma brat_congr_head (n : ℕ) (x : ℝ) (b c : ℕ → ℝ) (m : ℕ)
    (h : ∀ j, j ≤ m → b j = c j) : brat n x b m = brat n x c m := by
  unfold brat
  have hsum : bpart b (m + 1) = bpart c (m + 1) := by
    unfold bpart
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ m := by
      have hj2 : j < m + 1 := Finset.mem_range.mp hj
      omega
    exact h j hj'
  rw [hsum, h m le_rfl]

/-- `bval` only depends on the first `n` coordinates -/
lemma bval_congr_tail (n : ℕ) (hn : 2 ≤ n) (b c : ℕ → ℝ)
    (h : ∀ j, j < n → b j = c j) : bval n hn b = bval n hn c := by
  have hx : bx b n = bx c n := by
    unfold bx bpart
    exact Finset.sum_congr rfl (fun j hj => h j (Finset.mem_range.mp hj))
  unfold bval
  rw [hx]
  unfold bF
  apply Finset.sup'_congr (Finset.nonempty_range_iff.mpr (by omega : n ≠ 0)) rfl
  intro m hm
  have hm' : m < n := Finset.mem_range.mp hm
  exact brat_congr_head n (bx c n) b c m (fun j hj => h j (by omega))

lemma ones_mem_D (n : ℕ) (hn : 2 ≤ n) : ones n ∈ D n := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by simp [ones], ?_, ?_, ?_⟩
    · intro j hj
      simp [ones]
    · intro j hj
      simp [ones]
    · rw [bx_ones]
  · rw [bx_ones]
    norm_num
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
  · intro j hj
    simp [ones]

/-- a lower bound for the value functional on `D` -/
lemma one_le_bval_of_mem_D (n : ℕ) (hn : 2 ≤ n) {b : ℕ → ℝ} (hb : b ∈ D n) :
    (1 : ℝ) ≤ bval n hn b := by
  have hb0 : b 0 = 1 := b0_eq_one_of_mem_D hb
  have hbrat0 : brat n (bx b n) b 0 = 2 * (bx b n - (n : ℝ)) + 1 := by
    rw [brat_zero _ _ _ hb0]
    ring
  have hx : (n : ℝ) ≤ bx b n := n_le_bx_of_mem_D hb
  have h1 : (1 : ℝ) ≤ brat n (bx b n) b 0 := by
    rw [hbrat0]
    nlinarith
  have hm0 : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega : 0 < n)
  exact le_trans h1 (le_bF_of_mem n hn (bx b n) b hm0)

/-- existence of a minimizer of `bval` on `D` -/
lemma exists_minimizer (n : ℕ) (hn : 2 ≤ n) :
    ∃ m ∈ D n, ∀ b ∈ D n, bval n hn m ≤ bval n hn b := by
  have hK : IsCompact (D n) := isCompact_D n hn
  have hcont : ContinuousOn (fun b : ℕ → ℝ => bval n hn b) (D n) := continuousOn_bval_D n hn
  have him : IsCompact ((fun b : ℕ → ℝ => bval n hn b) '' (D n)) :=
    hK.image_of_continuousOn hcont
  have hne : ((fun b : ℕ → ℝ => bval n hn b) '' (D n)).Nonempty := by
    refine ⟨bval n hn (ones n), ?_⟩
    exact ⟨ones n, ones_mem_D n hn, rfl⟩
  have hbdd : BddBelow ((fun b : ℕ → ℝ => bval n hn b) '' (D n)) := by
    refine ⟨(0 : ℝ), ?_⟩
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    linarith [one_le_bval_of_mem_D n hn hb]
  have hsInf : sInf ((fun b : ℕ → ℝ => bval n hn b) '' (D n))
      ∈ ((fun b : ℕ → ℝ => bval n hn b) '' (D n)) := him.sInf_mem hne
  rcases hsInf with ⟨m, hmD, hmval⟩
  refine ⟨m, hmD, ?_⟩
  intro b hb
  have hle := csInf_le hbdd (show bval n hn b ∈ ((fun b : ℕ → ℝ => bval n hn b) '' (D n)) from ⟨b, hb, rfl⟩)
  simpa [hmval] using hle

end Minimizer



/-! ## The numerators `A_k` and elementary facts -/

section AkFacts

/-- `A_k := 2x - 2(n-1-k) - (partial sum of first k+1 terms)` -/
noncomputable def Ak (n : ℕ) (x : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  2 * x - 2 * ((n : ℝ) - 1 - (k : ℝ)) - bpart b (k + 1)

lemma brat_eq_div (n : ℕ) (x : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    brat n x b k = Ak n x b k / b k := rfl

lemma Ak_succ (n : ℕ) (x : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    Ak n x b (k + 1) = Ak n x b k + (2 - b (k + 1)) := by
  unfold Ak
  rw [bpart_succ, bpart_succ]
  push_cast
  ring_nf

/-- `A_k = x - Σ_{i=k+1}^{n-1} (2 - b i)` for `k < n` -/
lemma Ak_eq_sub_tail (n : ℕ) (x : ℝ) (b : ℕ → ℝ) (hx : bx b n = x) {k : ℕ}
    (hk : k < n) :
    Ak n x b k = x - (∑ j ∈ Finset.range (n - 1 - k), (2 - b (k + 1 + j))) := by
  unfold Ak
  have hsplit := Finset.sum_range_add (f := b) (k + 1) (n - 1 - k)
  have harg : (k + 1) + (n - 1 - k) = n := by omega
  have hdecomp : (∑ j ∈ Finset.range (k + 1), b j) +
      (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j)) = (∑ j ∈ Finset.range n, b j) := by
    rw [← hsplit]
    congr 1
    exact congrArg Finset.range harg
  have hcast : ((n : ℝ) - 1 - (k : ℝ)) = ((n - 1 - k : ℕ) : ℝ) := by
    have hnsub : n - 1 - k = n - (k + 1) := by omega
    have hk1 : k + 1 ≤ n := by omega
    rw [hnsub, Nat.cast_sub hk1]
    norm_num
    ring
  have hbpart : bpart b (k + 1) = (∑ j ∈ Finset.range n, b j) - (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j)) := by
    unfold bpart
    linarith [hdecomp]
  have hsub2 : (∑ j ∈ Finset.range (n - 1 - k), (2 - b (k + 1 + j)))
      = 2 * ((n - 1 - k : ℕ) : ℝ) - (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j)) := by
    rw [Finset.sum_sub_distrib]
    have hc : (∑ _j ∈ Finset.range (n - 1 - k), (2 : ℝ)) = 2 * ((n - 1 - k : ℕ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul, mul_comm]
    rw [hc]
  calc
    (2 * x - 2 * ((n : ℝ) - 1 - (k : ℝ)) - bpart b (k + 1))
        = 2 * x - 2 * ((n - 1 - k : ℕ) : ℝ) - bpart b (k + 1) := by rw [hcast]
    _ = 2 * x - 2 * ((n - 1 - k : ℕ) : ℝ)
        - ((∑ j ∈ Finset.range n, b j) - (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j))) := by
          rw [hbpart]
    _ = x - (∑ j ∈ Finset.range (n - 1 - k), (2 - b (k + 1 + j))) := by
          rw [hsub2]
          rw [← hx]
          unfold bx bpart
          ring

/-- for the last index, `A = x` -/
lemma Ak_last (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (b : ℕ → ℝ) (hx : bx b n = x) :
    Ak n x b (n - 1) = x := by
  unfold Ak
  have h : ((n : ℝ) - 1 - ((n - 1 : ℕ) : ℝ)) = 0 := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
    ring
  rw [h]
  norm_num
  have hsum : (∑ j ∈ Finset.range (n - 1 + 1), b j) = (∑ j ∈ Finset.range n, b j) := by
    rw [Nat.sub_add_cancel hn]
  change 2 * x - (∑ j ∈ Finset.range (n - 1 + 1), b j) = x
  rw [hsum]
  have hpart : (∑ j ∈ Finset.range n, b j) = x := by simpa [bx, bpart] using hx
  rw [hpart]
  ring

/-- positive numerators: `A_k ≥ 1` for sequences in `D` -/
lemma Ak_pos_of_mem_D (n : ℕ) (hn : 2 ≤ n) {b : ℕ → ℝ} (hb : b ∈ D n) {k : ℕ}
    (hk : k < n) : (1 : ℝ) ≤ Ak n (bx b n) b k := by
  have htail_lower : ((n - 1 - k : ℕ) : ℝ) ≤
      (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j)) := by
    have hterm : ∀ j ∈ Finset.range (n - 1 - k), (1 : ℝ) ≤ b (k + 1 + j) := by
      intro j hj
      have hj' : j < n - 1 - k := Finset.mem_range.mp hj
      exact one_le_of_mem_D hb (by omega : k + 1 + j < n)
    calc
      ((n - 1 - k : ℕ) : ℝ) = (∑ j ∈ Finset.range (n - 1 - k), (1 : ℝ)) := by simp
      _ ≤ (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j)) := Finset.sum_le_sum hterm
  have hdecomp' : Ak n (bx b n) b k
      = (bx b n) - (∑ j ∈ Finset.range (n - 1 - k), (2 - b (k + 1 + j))) := by
    exact Ak_eq_sub_tail n (bx b n) b rfl hk
  have hsub2 : (∑ j ∈ Finset.range (n - 1 - k), (2 - b (k + 1 + j)))
      = 2 * ((n - 1 - k : ℕ) : ℝ) - (∑ j ∈ Finset.range (n - 1 - k), b (k + 1 + j)) := by
    rw [Finset.sum_sub_distrib]
    have hc : (∑ _j ∈ Finset.range (n - 1 - k), (2 : ℝ)) = 2 * ((n - 1 - k : ℕ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul, mul_comm]
    rw [hc]
  rw [hdecomp', hsub2]
  have hx : (n : ℝ) ≤ bx b n := n_le_bx_of_mem_D hb
  have hcast : ((n - 1 - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    have hnsub : n - 1 - k = n - (k + 1) := by omega
    have hk1 : k + 1 ≤ n := by omega
    rw [hnsub, Nat.cast_sub hk1]
    norm_num
    ring
  -- 1 ≤ bx - 2*c + tail, with c ≤ tail and n ≤ bx and c ≤ n-1 ≤ ...
  have hle1 : (1 : ℝ) ≤ (n : ℝ) - ((n - 1 - k : ℕ) : ℝ) := by
    rw [hcast]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  nlinarith

end AkFacts



/-! ## Structure of the minimizer -/

section Structure

/-- the constant-one-on-first-`n-1` sequence with value `1+eps` at the last index -/
noncomputable def bump (n : ℕ) (eps : ℝ) : ℕ → ℝ :=
  fun j => if j = n - 1 then 1 + eps else 1

lemma bpart_bump (n : ℕ) (hn : 2 ≤ n) (eps : ℝ) {r : ℕ} (hr : r < n - 1) :
    bpart (bump n eps) (r + 1) = (r + 1 : ℕ) := by
  unfold bpart bump
  have hconst : ∀ j ∈ Finset.range (r + 1), (if j = n - 1 then 1 + eps else 1) = 1 := by
    intro j hj
    have hj' : j < r + 1 := Finset.mem_range.mp hj
    have hne : j ≠ n - 1 := by omega
    simp [hne]
  calc
    (∑ j ∈ Finset.range (r + 1), (if j = n - 1 then 1 + eps else 1))
        = (∑ j ∈ Finset.range (r + 1), (1 : ℝ)) := Finset.sum_congr rfl hconst
    _ = (r + 1 : ℕ) := by
        simp [Finset.sum_const, Finset.card_range]

lemma bx_bump (n : ℕ) (hn : 2 ≤ n) (eps : ℝ) : bx (bump n eps) n = (n : ℝ) + eps := by
  unfold bx bpart bump
  have hdec : (∑ j ∈ Finset.range n, (if j = n - 1 then 1 + eps else 1))
      = (∑ j ∈ Finset.range (n - 1), (if j = n - 1 then 1 + eps else 1)) + (1 + eps) := by
    -- range n = range (n-1+1)
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
    rw [← hnsub]
    rw [Finset.sum_range_succ]
    simp
  rw [hdec]
  have hconst : ∀ j ∈ Finset.range (n - 1), (if j = n - 1 then 1 + eps else 1) = 1 := by
    intro j hj
    have hj' : j < n - 1 := Finset.mem_range.mp hj
    have hne : j ≠ n - 1 := by omega
    simp [hne]
  rw [Finset.sum_congr rfl hconst]
  simp [Finset.sum_const, Finset.card_range]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  ring

lemma bump_mem_D (n : ℕ) (hn : 2 ≤ n) (eps : ℝ) (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 2) :
    bump n eps ∈ D n := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have h0 : (0 : ℕ) ≠ n - 1 := by omega
      simp [bump, h0]
    · intro j hj
      by_cases h : j = n - 1
      · simp [bump, h]
        linarith
      · simp [bump, h]
    · intro j hj
      by_cases h : j = n - 1
      · exfalso
        omega
      · by_cases h2 : j + 1 = n - 1
        · have hnot : j ≠ n - 1 := by omega
          simp [bump, hnot, h2]
          linarith
        · have hnot : j ≠ n - 1 := h
          have hnot2 : j + 1 ≠ n - 1 := h2
          simp [bump, hnot, hnot2]
    · rw [bx_bump n hn eps]
      norm_num
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith
  · rw [bx_bump n hn eps]
    norm_num
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hepsle : eps ≤ 1 / 2 := heps
    nlinarith
  · intro j hj
    by_cases h : j = n - 1
    · exfalso
      omega
    · simp [bump, h]

/-- the value at `bump n eps` is `< n` for `0 < eps < 1/2` -/
lemma bump_value_lt (n : ℕ) (hn : 2 ≤ n) (eps : ℝ) (heps0 : 0 < eps) (heps : eps < 1 / 2) :
    bval n hn (bump n eps) < (n : ℝ) := by
  have hbrat : ∀ r ∈ Finset.range n, brat n (bx (bump n eps) n) (bump n eps) r < (n : ℝ) := by
    intro r hr
    have hr' : r < n := Finset.mem_range.mp hr
    have hx : bx (bump n eps) n = (n : ℝ) + eps := bx_bump n hn eps
    by_cases hlast : r = n - 1
    · -- ratio at last = (n+eps)/(1+eps)
      subst r
      rw [brat_last n (by omega : 1 ≤ n) (bx (bump n eps) n) (bump n eps) rfl]
      have hb : (bump n eps) (n - 1) = 1 + eps := by simp [bump]
      rw [hx, hb]
      have hn1 : (1 : ℝ) < (n : ℝ) := by
        have hnn : (2 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      have hepspos : 0 < eps := heps0
      field_simp
      nlinarith
    · -- r ≤ n-2: ratio = r + 1 + 2 eps < n
      have hrle : r < n - 1 := by omega
      have hpart : bpart (bump n eps) (r + 1) = (r + 1 : ℕ) := bpart_bump n hn eps hrle
      have hb : (bump n eps) r = 1 := by
        simp [bump, show r ≠ n - 1 from (by omega : r ≠ n - 1)]
      have hrat : brat n (bx (bump n eps) n) (bump n eps) r = (r : ℝ) + 1 + 2 * eps := by
        unfold brat
        rw [hx, hpart, hb]
        norm_num
        ring_nf
      rw [hrat]
      have hrle' : (r : ℝ) + 1 ≤ (n : ℝ) - 1 := by
        have hcastadd : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by simp [Nat.cast_add]
        have hcastsub : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          norm_num
        rw [← hcastadd, hcastsub]
        exact_mod_cast (by omega : r + 1 ≤ n - 1)
      have hepsh : 2 * eps < 1 := by linarith
      nlinarith
  rcases Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr (by omega : n ≠ 0))
      (fun r => brat n (bx (bump n eps) n) (bump n eps) r) with ⟨r, hr, hrval⟩
  have this : bval n hn (bump n eps) = brat n (bx (bump n eps) n) (bump n eps) r := by
    unfold bval bF
    exact hrval
  rw [this]
  exact hbrat r hr

end Structure

/-! ## Basic consequences for a minimizer -/

section MinConseq

lemma minimizer_M_lt_n (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) : bval n hn m < (n : ℝ) := by
  have hbD : bump n (1 / 4) ∈ D n := by
    apply bump_mem_D n hn (1 / 4) <;> norm_num
  have hv : bval n hn (bump n (1 / 4)) < (n : ℝ) := by
    apply bump_value_lt n hn (1 / 4) <;> norm_num
  have hle : bval n hn m ≤ bval n hn (bump n (1 / 4)) := hmin _ hbD
  linarith

/-- if total is exactly `n` then all terms are 1 -/
lemma all_one_of_bx_eq_n (n : ℕ) (hn : 2 ≤ n) {b : ℕ → ℝ} (hb : b ∈ D n)
    (hx : bx b n = (n : ℝ)) : ∀ j, j < n → b j = 1 := by
  have hge : ∀ x ∈ Finset.range n, (0 : ℝ) ≤ b x - 1 := by
    intro x hx
    exact sub_nonneg.mpr (one_le_of_mem_D hb (Finset.mem_range.mp hx))
  have hzero : (∑ x ∈ Finset.range n, (b x - 1)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hc : (∑ x ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) := by
      simp [Finset.sum_const, Finset.card_range]
    unfold bx bpart at hx
    rw [hc, hx]
    ring
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range n) (f := fun x => b x - 1) hge).1 hzero
  intro j hj
  have := hall j (Finset.mem_range.mpr hj)
  linarith

/-- the value at the all-ones sequence is exactly `n` -/
lemma bval_ones (n : ℕ) (hn : 2 ≤ n) : bval n hn (ones n) = (n : ℝ) := by
  have hbrat : ∀ r ∈ Finset.range n, brat n (bx (ones n) n) (ones n) r = (r : ℝ) + 1 := by
    intro r hr
    have hr' : r < n := Finset.mem_range.mp hr
    have hx : bx (ones n) n = (n : ℝ) := bx_ones n
    have hpart : bpart (ones n) (r + 1) = (r + 1 : ℝ) := by
      unfold bpart ones
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul]
    unfold brat
    rw [hx, hpart]
    have hb : (ones n) r = 1 := by simp [ones]
    rw [hb]
    norm_num
    ring_nf
  apply le_antisymm
  · change bF n hn (bx (ones n) n) (ones n) ≤ (n : ℝ)
    rw [bF_le_iff n hn (bx (ones n) n) (ones n) (n : ℝ)]
    intro r hr
    rw [hbrat r hr]
    have hr1 : (r + 1 : ℕ) ≤ n := by
      have hr' : r < n := Finset.mem_range.mp hr
      omega
    exact_mod_cast hr1
  · have hm : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega : n - 1 < n)
    have hle := le_bF_of_mem n hn (bx (ones n) n) (ones n) hm
    rw [hbrat (n - 1) hm] at hle
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1]
      norm_num
    rw [hc] at hle
    exact hle

lemma minimizer_x_gt_n (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) : (n : ℝ) < bx m n := by
  have hle : (n : ℝ) ≤ bx m n := n_le_bx_of_mem_D hmD
  by_contra h
  have hx : bx m n = (n : ℝ) := le_antisymm (le_of_not_gt h) hle
  have hone : ∀ j, j < n → m j = 1 := all_one_of_bx_eq_n n hn hmD hx
  have hones : ∀ j, j < n → m j = (ones n) j := fun j hj => by
    rw [hone j hj]
    simp [ones]
  have hval : bval n hn m = (n : ℝ) := by
    have hcong : bval n hn m = bval n hn (ones n) := bval_congr_tail n hn m (ones n) hones
    rw [hcong, bval_ones n hn]
  have hlt := minimizer_M_lt_n n hn hmD hmin
  linarith

/-- the total of a minimizer is `< (3n-1)/2` -/
lemma minimizer_x_lt_upper (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) :
    bx m n < ((3 * (n : ℝ) - 1) / 2) := by
  have hle : bx m n ≤ ((3 * (n : ℝ) - 1) / 2) := bx_le_of_mem_D hmD
  by_contra h
  have hx : bx m n = ((3 * (n : ℝ) - 1) / 2) := le_antisymm hle (le_of_not_gt h)
  -- ratio at 0 = 2(x-n)+1 = n; M ≥ that → contradiction
  have hb0 : m 0 = 1 := b0_eq_one_of_mem_D hmD
  have hbrat0 : brat n (bx m n) m 0 = 2 * (bx m n - (n : ℝ)) + 1 := by
    rw [brat_zero _ _ _ hb0]
    ring
  have hm0 : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega : 0 < n)
  have hleM : brat n (bx m n) m 0 ≤ bval n hn m := le_bF_of_mem n hn (bx m n) m hm0
  have hval : (n : ℝ) ≤ bval n hn m := by
    rw [hbrat0] at hleM
    rw [hx] at hleM
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
  have hlt := minimizer_M_lt_n n hn hmD hmin
  linarith

end MinConseq


/-- perturb coordinate `j0` of `m` by `-eps` -/
noncomputable def perturb (m : ℕ → ℝ) (j0 : ℕ) (eps : ℝ) : ℕ → ℝ :=
  fun j => if j = j0 then m j - eps else m j

lemma perturb_self {m : ℕ → ℝ} {j0 : ℕ} {eps : ℝ} : perturb m j0 eps j0 = m j0 - eps := by
  simp [perturb]
lemma perturb_other {m : ℕ → ℝ} {j0 : ℕ} {eps : ℝ} {j : ℕ} (h : j ≠ j0) :
    perturb m j0 eps j = m j := by
  simp [perturb, h]
lemma sum_indicator_mem (s : Finset ℕ) {j0 : ℕ} (hj0 : j0 ∈ s) (eps : ℝ) :
    (∑ j ∈ s, (if j = j0 then eps else (0 : ℝ))) = eps := by
  rw [Finset.sum_eq_single j0]
  · simp
  · intro b hb hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot hj0)
lemma bpart_perturb_lt {m : ℕ → ℝ} {j0 : ℕ} {eps : ℝ} {r : ℕ} (hr : r < j0) :
    bpart (perturb m j0 eps) (r + 1) = bpart m (r + 1) := by
  unfold bpart perturb
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < r + 1 := Finset.mem_range.mp hj
  have hne : j ≠ j0 := by omega
  simp [hne]
lemma bpart_perturb_ge {m : ℕ → ℝ} {j0 : ℕ} {eps : ℝ} {r : ℕ} (hj0 : j0 ≤ r) :
    bpart (perturb m j0 eps) (r + 1) = bpart m (r + 1) - eps := by
  calc
    bpart (perturb m j0 eps) (r + 1)
        = (∑ j ∈ Finset.range (r + 1), (m j - (if j = j0 then eps else 0))) := by
          unfold bpart perturb
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : j = j0
          · subst j; simp
          · simp [h]
    _ = (∑ j ∈ Finset.range (r + 1), m j) - (∑ j ∈ Finset.range (r + 1), (if j = j0 then eps else 0)) := by
          rw [Finset.sum_sub_distrib]
    _ = bpart m (r + 1) - eps := by
          unfold bpart
          have hj0' : j0 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
          rw [sum_indicator_mem (Finset.range (r + 1)) hj0' eps]

lemma bx_perturb {m : ℕ → ℝ} {n j0 : ℕ} {eps : ℝ} (hj0 : j0 < n) :
    bx (perturb m j0 eps) n = bx m n - eps := by
  -- same as bpart_perturb_ge with r = n-1
  have h : n - 1 ≥ j0 := by omega
  have hb := bpart_perturb_ge (m := m) (j0 := j0) (eps := eps) (r := n - 1) (by omega : j0 ≤ n - 1)
  unfold bx
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [← hnsub, ← hnsub]
  exact hb

section Step1Dev

lemma perturb_mem_D (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    {t : ℕ} (ht : t + 1 < n) (hstrict : m t < m (t + 1)) {eps : ℝ}
    (heps0 : 0 < eps) (heps : eps < m (t + 1) - m t) (hepsx : eps < bx m n - (n : ℝ)) :
    perturb m (t + 1) eps ∈ D n := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have h0 : (0 : ℕ) ≠ t + 1 := by omega
      rw [perturb_other h0]
      exact b0_eq_one_of_mem_D hmD
    · intro j hj
      by_cases h : j = t + 1
      · subst j
        rw [perturb_self]
        have hmt : m t ≤ m (t + 1) - eps := by linarith
        linarith [one_le_of_mem_D hmD (by omega : t < n)]
      · rw [perturb_other h]
        exact one_le_of_mem_D hmD hj
    · intro j hj1
      by_cases h1 : j = t + 1
      · subst j
        have hneq : (t + 1) + 1 ≠ t + 1 := by omega
        rw [perturb_self, perturb_other hneq]
        have hm : m (t + 1) ≤ m (t + 2) := by
          have hlt : (t + 1) + 1 < n := by omega
          exact mono_of_mem_D hmD hlt
        linarith
      · rw [perturb_other h1]
        by_cases h2 : j + 1 = t + 1
        · have hjt : j = t := by omega
          subst j
          rw [perturb_self]
          have hmono : m t ≤ m (t + 1) := mono_of_mem_D hmD ht
          linarith
        · rw [perturb_other h2]
          exact mono_of_mem_D hmD hj1
    · -- n ≤ sum
      rw [bx_perturb (by omega : t + 1 < n)]
      have hx : (n : ℝ) ≤ bx m n := n_le_bx_of_mem_D hmD
      linarith
  · -- upper
    rw [bx_perturb (by omega : t + 1 < n)]
    have hupper : bx m n ≤ ((3 * (n : ℝ) - 1) / 2) := bx_le_of_mem_D hmD
    linarith
  · intro j hj
    have hjne : j ≠ t + 1 := by omega
    rw [perturb_other hjne]
    exact tail_one_of_mem_D hmD hj

lemma brat_le_val_of_mem_range (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    {r : ℕ} (hr : r < n) : brat n (bx m n) m r ≤ bval n hn m := by
  exact le_bF_of_mem n hn (bx m n) m (Finset.mem_range.mpr hr)

lemma Ak_perturb_lt (n : ℕ) {m : ℕ → ℝ} {t r : ℕ} {eps : ℝ} (X : ℝ)
    (hr : r < t + 1) : Ak n (X - eps) (perturb m (t + 1) eps) r
      = Ak n X m r - 2 * eps := by
  unfold Ak
  have hb : bpart (perturb m (t + 1) eps) (r + 1) = bpart m (r + 1) :=
    bpart_perturb_lt (m := m) (j0 := t + 1) (eps := eps) (r := r) (by omega : r < t + 1)
  rw [hb]
  ring

lemma Ak_perturb_ge (n : ℕ) {m : ℕ → ℝ} {t r : ℕ} {eps : ℝ} (X : ℝ)
    (hr : t + 1 ≤ r) : Ak n (X - eps) (perturb m (t + 1) eps) r
      = Ak n X m r - eps := by
  unfold Ak
  have hb : bpart (perturb m (t + 1) eps) (r + 1) = bpart m (r + 1) - eps :=
    bpart_perturb_ge (m := m) (j0 := t + 1) (eps := eps) (r := r) (by omega : t + 1 ≤ r)
  rw [hb]
  ring

/-- numerators (hence ratios) strictly decrease at non-perturbed indices -/
lemma ratio_perturb_lt (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    {t r : ℕ} {eps : ℝ} (X : ℝ) (hr : r < n) (hne : r ≠ t + 1)
    (heps0 : 0 < eps) : brat n (X - eps) (perturb m (t + 1) eps) r < brat n X m r := by
  have hpos : (0 : ℝ) < m r := lt_of_lt_of_le (by norm_num) (one_le_of_mem_D hmD hr)
  by_cases hlt : r < t + 1
  · have hne2 : r ≠ t + 1 := by omega
    change Ak n (X - eps) (perturb m (t + 1) eps) r / (perturb m (t + 1) eps) r
        < Ak n X m r / m r
    have hAk := Ak_perturb_lt n (m := m) (t := t) (r := r) (eps := eps) X hlt
    rw [hAk, perturb_other hne2]
    have h1 : Ak n X m r - 2 * eps < Ak n X m r := by linarith
    exact div_lt_div_of_pos_right h1 hpos
  · have hge : t + 1 ≤ r := by omega
    change Ak n (X - eps) (perturb m (t + 1) eps) r / (perturb m (t + 1) eps) r
        < Ak n X m r / m r
    have hAk := Ak_perturb_ge n (m := m) (t := t) (r := r) (eps := eps) X hge
    rw [hAk, perturb_other hne]
    have h1 : Ak n X m r - eps < Ak n X m r := by linarith
    exact div_lt_div_of_pos_right h1 hpos

/-- step 1 (perturbation) for a minimizer -/
lemma step1 (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {t : ℕ} (ht : t + 1 < n)
    (hstrict : m t < m (t + 1)) : brat n (bx m n) m (t + 1) = bval n hn m := by
  let X := bx m n
  let M := bval n hn m
  have hXgt : (n : ℝ) < X := by
    dsimp [X]
    exact minimizer_x_gt_n n hn hmD hmin
  have hM1le : (1 : ℝ) ≤ M := by
    dsimp [M]
    exact one_le_bval_of_mem_D n hn hmD
  have hd1 : 0 < m (t + 1) - m t := sub_pos.mpr hstrict
  have hd2 : 0 < X - (n : ℝ) := sub_pos.mpr hXgt
  have hbratle : brat n X m (t + 1) ≤ M := by
    dsimp [M]
    exact le_bF_of_mem n hn X m (Finset.mem_range.mpr (by omega : t + 1 < n))
  have hmain : ∀ eps : ℝ, 0 < eps → eps < min (m (t + 1) - m t) (X - (n : ℝ)) →
      (Ak n X m (t + 1) - eps) / (m (t + 1) - eps) ≥ M := by
    intro eps he0 hesmall
    have hd1e : eps < m (t + 1) - m t := lt_of_lt_of_le hesmall (min_le_left _ _)
    have hd2e : eps < X - (n : ℝ) := lt_of_lt_of_le hesmall (min_le_right _ _)
    have hmem : perturb m (t + 1) eps ∈ D n := perturb_mem_D n hn hmD ht hstrict he0 hd1e hd2e
    have hminb : M ≤ bval n hn (perturb m (t + 1) eps) := by
      dsimp [M]
      exact hmin (perturb m (t + 1) eps) hmem
    have hbrp : brat n (X - eps) (perturb m (t + 1) eps) (t + 1)
        = (Ak n X m (t + 1) - eps) / (m (t + 1) - eps) := by
      change Ak n (X - eps) (perturb m (t + 1) eps) (t + 1) / (perturb m (t + 1) eps) (t + 1)
          = (Ak n X m (t + 1) - eps) / (m (t + 1) - eps)
      have hAk := Ak_perturb_ge n (m := m) (t := t) (r := t + 1) (eps := eps) X (by omega)
      rw [hAk, perturb_self]
    by_contra hneg
    have hltge : (Ak n X m (t + 1) - eps) / (m (t + 1) - eps) < M := lt_of_not_ge hneg
    have hneg' : brat n (X - eps) (perturb m (t + 1) eps) (t + 1) < M := by
      rwa [hbrp]
    have hall : ∀ r ∈ Finset.range n, brat n (X - eps) (perturb m (t + 1) eps) r < M := by
      intro r hr
      have hr' : r < n := Finset.mem_range.mp hr
      by_cases hne : r = t + 1
      · subst r
        exact hneg'
      · have hlt := ratio_perturb_lt n hn hmD (t := t) (r := r) X hr' hne he0
        have hle2 : brat n X m r ≤ M := by
          dsimp [M]
          exact le_bF_of_mem n hn X m (Finset.mem_range.mpr hr')
        linarith
    rcases Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr (by omega : n ≠ 0))
        (fun r => brat n (X - eps) (perturb m (t + 1) eps) r) with ⟨r, hr, hsup⟩
    have hbx : bx (perturb m (t + 1) eps) n = X - eps := by
      dsimp [X]
      exact bx_perturb (by omega : t + 1 < n)
    have hbval : bval n hn (perturb m (t + 1) eps)
        = brat n (X - eps) (perturb m (t + 1) eps) r := by
      unfold bval bF
      rw [hbx]
      exact hsup
    have hsmall : brat n (X - eps) (perturb m (t + 1) eps) r < M := hall r hr
    rw [← hbval] at hsmall
    linarith
  let b := m (t + 1)
  let A := Ak n X m (t + 1)
  have hbpos : (0 : ℝ) < b := by
    dsimp [b]
    exact lt_of_lt_of_le (by norm_num) (one_le_of_mem_D hmD (by omega : t + 1 < n))
  have hgeq : (0 : ℝ) ≤ M * b - A := by
    have hle : A ≤ M * b := by
      have hbrle := hbratle
      dsimp [A, b] at hbrle ⊢
      rw [brat_eq_div] at hbrle
      exact (div_le_iff₀ hbpos).mp hbrle
    linarith
  have hbnd : ∀ eps : ℝ, 0 < eps → eps < min (m (t + 1) - m t) (X - (n : ℝ)) →
      M * b - A ≤ (M - 1) * eps := by
    intro eps he0 hesmall
    have hineq := hmain eps he0 hesmall
    have hbeps : 0 < b - eps := by
      dsimp [b]
      have he1 : eps < m (t + 1) - m t := lt_of_lt_of_le hesmall (min_le_left _ _)
      have hmt : (0 : ℝ) ≤ m t := by linarith [one_le_of_mem_D hmD (by omega : t < n)]
      linarith
    have hle' : M * (b - eps) ≤ A - eps := by
      dsimp [A]
      exact (le_div_iff₀ hbeps).mp hineq
    dsimp [A, b]
    nlinarith
  have hclaim : M * b - A ≤ 0 := by
    by_cases hM1 : M = 1
    · have hE : 0 < min (m (t + 1) - m t) (X - (n : ℝ)) := lt_min hd1 hd2
      let eps := min (m (t + 1) - m t) (X - (n : ℝ)) / 2
      have heps0 : 0 < eps := by dsimp [eps]; linarith
      have heps1 : eps < min (m (t + 1) - m t) (X - (n : ℝ)) := by
        dsimp [eps]
        linarith
      have hb := hbnd eps heps0 heps1
      rw [hM1] at hb
      norm_num at hb
      nlinarith
    · have hMg : 1 < M := lt_of_le_of_ne hM1le (Ne.symm hM1)
      have hDpos : 0 < M - 1 := by linarith
      by_contra hpos
      have hD : 0 < M * b - A := by exact not_le.mp hpos
      have hE : 0 < min (m (t + 1) - m t) (X - (n : ℝ)) := lt_min hd1 hd2
      have hM1' : 0 < M - 1 := by linarith
      let eps := min (min (m (t + 1) - m t) (X - (n : ℝ)) / 2)
          ((M * b - A) / (2 * (M - 1)))
      have heps0 : 0 < eps := by
        dsimp [eps]
        have h1 : 0 < min (m (t + 1) - m t) (X - (n : ℝ)) / 2 := by linarith
        have h2 : 0 < (M * b - A) / (2 * (M - 1)) := by positivity
        positivity
      have heps1 : eps < min (m (t + 1) - m t) (X - (n : ℝ)) := by
        dsimp [eps]
        have hP : 0 < min (m (t + 1) - m t) (X - (n : ℝ)) := lt_min hd1 hd2
        have h1 : min (min (m (t + 1) - m t) (X - (n : ℝ)) / 2) ((M * b - A) / (2 * (M - 1)))
            ≤ min (m (t + 1) - m t) (X - (n : ℝ)) / 2 := min_le_left _ _
        have h2 : min (m (t + 1) - m t) (X - (n : ℝ)) / 2 < min (m (t + 1) - m t) (X - (n : ℝ)) := by linarith
        exact lt_of_le_of_lt h1 h2
      have hb := hbnd eps heps0 heps1
      have hle2 : eps ≤ (M * b - A) / (2 * (M - 1)) := by
        dsimp [eps]
        exact min_le_right _ _
      have hpos2 : (0 : ℝ) < 2 * (M - 1) := by positivity
      have hle2' : eps * (2 * (M - 1)) ≤ M * b - A :=
        (le_div_iff₀ (a := eps) (b := M * b - A) (c := 2 * (M - 1)) hpos2).mp hle2
      nlinarith
  have hAeq : A = M * b := by linarith
  -- brat at t+1 = M
  have hbr : brat n X m (t + 1) = M := by
    change Ak n X m (t + 1) / m (t + 1) = M
    dsimp [A, b] at hAeq hbpos
    rw [hAeq]
    field_simp [ne_of_gt hbpos]
  dsimp [X, M] at hbr
  exact hbr

end Step1Dev


/-! ## Step 2: `m (n-1) < 2` -/

section Step2


lemma exists_crossing_two (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (h : 2 ≤ m (n - 1)) : ∃ t : ℕ, 1 ≤ t ∧ t < n ∧ m (t - 1) < 2 ∧ 2 ≤ m t := by
  classical
  let P : ℕ → Prop := fun j => 1 ≤ j ∧ j < n ∧ 2 ≤ m j
  have hPnm : P (n - 1) := by
    dsimp [P]
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · simpa using h
  have hex : ∃ j, P j := ⟨n - 1, hPnm⟩
  let t := Nat.find hex
  have htP : P t := Nat.find_spec hex
  have hmin : ∀ j, P j → t ≤ j := fun j hj => Nat.find_min' hex hj
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · exact htP.1
  · exact htP.2.1
  · by_contra hnge
    have hge2 : 2 ≤ m (t - 1) := le_of_not_gt hnge
    by_cases ht1 : t = 1
    · have : m (t - 1) = m 0 := by congr 1; omega
      rw [this] at hge2
      have hm0 : m 0 = 1 := b0_eq_one_of_mem_D hmD
      linarith
    · have ht2 : 2 ≤ t := by omega
      have ht'1 : 1 ≤ t - 1 := by omega
      have ht'n : t - 1 < n := by omega
      have hPt : P (t - 1) := ⟨ht'1, ht'n, hge2⟩
      have hle := hmin (t - 1) hPt
      omega
  · exact htP.2.2

/-- numerator inequality giving ratio_{t-1} > ratio_t -/
lemma step2_ratio_gt (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    {t : ℕ} (ht1 : 1 ≤ t) (htn : t < n) (hprev : m (t - 1) < 2) (hcur : 2 ≤ m t) :
    brat n (bx m n) m t < brat n (bx m n) m (t - 1) := by
  let X := bx m n
  have hAk : Ak n X m t = Ak n X m (t - 1) + (2 - m t) := by
    dsimp [X]
    have h0 := Ak_succ n X m (t - 1)
    have hsub : t - 1 + 1 = t := by omega
    simpa [hsub] using h0
  have hposa : (0 : ℝ) < m (t - 1) := by
    have hge1 : 1 ≤ m (t - 1) := one_le_of_mem_D hmD (by omega : t - 1 < n)
    linarith
  have hpost : (0 : ℝ) < m t := by
    have hge1 : 1 ≤ m t := one_le_of_mem_D hmD (by omega : t < n)
    linarith
  have hApos : (1 : ℝ) ≤ Ak n X m (t - 1) := by
    dsimp [X]
    exact Ak_pos_of_mem_D n hn hmD (by omega : t - 1 < n)
  have hnum : (m t - m (t - 1)) * Ak n X m (t - 1) > m (t - 1) * (2 - m t) := by
    have h1 : (m t - m (t - 1)) * Ak n X m (t - 1) ≥ m t - m (t - 1) := by nlinarith
    have hmt : m t - m (t - 1) > 0 := by linarith
    have hl : m (t - 1) * (2 - m t) ≤ 0 := by nlinarith
    nlinarith
  change Ak n X m t / m t < Ak n X m (t - 1) / m (t - 1)
  rw [hAk]
  rw [div_lt_div_iff₀ hpost hposa]
  nlinarith

/-- Step 2: `m (n-1) < 2` -/
lemma step2_last_lt_two (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) : m (n - 1) < 2 := by
  by_contra h
  have hge : 2 ≤ m (n - 1) := le_of_not_gt h
  rcases exists_crossing_two n hn hmD hge with ⟨t, ht1, htn, hprev, hcur⟩
  -- strict increase at (t-1, t); apply step1 to get ratio_t = M
  have hstrict : m (t - 1) < m t := by linarith
  have hrat : brat n (bx m n) m t = bval n hn m := by
    have hsub : t - 1 + 1 = t := by omega
    have hs := step1 n hn hmD hmin (t := t - 1) (by omega : (t - 1) + 1 < n)
      (by simpa [hsub] using hstrict)
    simpa [hsub] using hs
  have hgt : brat n (bx m n) m t < brat n (bx m n) m (t - 1) :=
    step2_ratio_gt n hn hmD ht1 htn hprev hcur
  have hle : brat n (bx m n) m (t - 1) ≤ bval n hn m :=
    le_bF_of_mem n hn (bx m n) m (Finset.mem_range.mpr (by omega : t - 1 < n))
  linarith

end Step2

/-! ## Step 3: structure of the minimizer (run of ones, strict increasing tail) -/

section Step3


lemma minimizer_has_jump_index (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) :
    ∃ L : ℕ, 1 ≤ L ∧ L < n ∧ (∀ j, j < L → m j = 1) ∧ 1 < m L := by
  classical
  have hXgt : (n : ℝ) < bx m n := minimizer_x_gt_n n hn hmD hmin
  by_cases hex : ∃ j : ℕ, 1 ≤ j ∧ j < n ∧ 1 < m j
  · let L := Nat.find hex
    have hLspec : 1 ≤ L ∧ L < n ∧ 1 < m L := by
      dsimp [L]
      exact Nat.find_spec hex
    refine ⟨L, hLspec.1, hLspec.2.1, ?_, hLspec.2.2⟩
    · intro j hj
      have hge : 1 ≤ m j := one_le_of_mem_D hmD (by omega : j < n)
      have hnot : ¬ 1 < m j := by
        intro hgtj
        by_cases hj0 : j = 0
        · subst j
          have hm0 : m 0 = 1 := b0_eq_one_of_mem_D hmD
          linarith
        · have hj1 : 1 ≤ j := by omega
          have hfind : L ≤ j := by
            dsimp [L]
            exact Nat.find_min' hex ⟨hj1, ⟨(by omega : j < n), hgtj⟩⟩
          omega
      exact le_antisymm (le_of_not_gt hnot) hge
  · -- no index > 1: all terms = 1
    have hall : ∀ j, j < n → m j = 1 := by
      intro j hj
      have hge : 1 ≤ m j := one_le_of_mem_D hmD hj
      by_cases h : j = 0
      · subst j
        exact b0_eq_one_of_mem_D hmD
      · have hj1 : 1 ≤ j := by omega
        have hnot : ¬ 1 < m j := by
          intro hgtj
          exact hex ⟨j, hj1, hj, hgtj⟩
        exact le_antisymm (le_of_not_gt hnot) hge
    have hx : bx m n = (n : ℝ) := by
      unfold bx bpart
      calc
        (∑ j ∈ Finset.range n, m j) = (∑ j ∈ Finset.range n, (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hmem
          rw [hall j (Finset.mem_range.mp hmem)]
        _ = (n : ℝ) := by simp [Finset.sum_const, Finset.card_range]
    linarith

/-- every term is `< 2` (from Step 2 and monotonicity) -/
lemma minimizer_all_lt_two (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {j : ℕ} (hj : j < n) : m j < 2 := by
  have hle : m j ≤ m (n - 1) := by
    apply mono_le_of_mem_D hmD (by omega : j ≤ n - 1)
    omega
  have hlast : m (n - 1) < 2 := step2_last_lt_two n hn hmD hmin
  linarith

/-- the tail from `L` is strictly increasing -/
lemma minimizer_tail_strict (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) {j : ℕ} (hjL : L ≤ j) (hjn : j < n - 1) :
    m j < m (j + 1) := by
  classical
  by_contra hle
  have hmono : m j ≤ m (j + 1) := mono_of_mem_D hmD (by omega : j + 1 < n)
  have hrev : m (j + 1) ≤ m j := le_of_not_gt hle
  have heq : m j = m (j + 1) := (le_antisymm hrev hmono).symm
  -- j0 := the first equality index in [L..n-2]
  have hex : ∃ q : ℕ, L ≤ q ∧ q < n - 1 ∧ m q = m (q + 1) := ⟨j, hjL, hjn, heq⟩
  let j0 := Nat.find hex
  have hj0spec : L ≤ j0 ∧ j0 < n - 1 ∧ m j0 = m (j0 + 1) := by
    dsimp [j0]
    exact Nat.find_spec hex
  -- strict increase just before j0:
  have hprev_strict : m (j0 - 1) < m j0 := by
    by_cases hj0eqL : j0 = L
    · have hLm : m (L - 1) = 1 := hone (L - 1) (by omega)
      rw [hj0eqL]
      rw [hLm]
      exact hLgt
    · have hj0gt : L < j0 := by omega
      have hprevge : L ≤ j0 - 1 := by omega
      have hprevn : j0 - 1 < n - 1 := by omega
      have hne : m (j0 - 1) ≠ m j0 := by
        intro h_eq
        have hq : L ≤ j0 - 1 ∧ j0 - 1 < n - 1 ∧ m (j0 - 1) = m (j0 - 1 + 1) := by
          refine ⟨hprevge, hprevn, ?_⟩
          have hsub' : (j0 - 1) + 1 = j0 := by omega
          simpa [hsub'] using h_eq
        have hfind : j0 ≤ j0 - 1 := by
          dsimp [j0]
          exact Nat.find_min' hex hq
        omega
      have hmono' : m (j0 - 1) ≤ m j0 := by
        apply mono_le_of_mem_D hmD (by omega : j0 - 1 ≤ j0)
        omega
      exact lt_of_le_of_ne hmono' hne
  -- ratio at j0 equals M (Step 1)
  have hrat_j0 : brat n (bx m n) m j0 = bval n hn m := by
    have hsub : (j0 - 1) + 1 = j0 := by omega
    have hs := step1 n hn hmD hmin (t := j0 - 1) (by omega : (j0 - 1) + 1 < n)
      (by simpa [hsub] using hprev_strict)
    simpa [hsub] using hs
  -- ratio at j0+1 > M, contradiction
  have hmj02 : m j0 < 2 := minimizer_all_lt_two n hn hmD hmin (by omega : j0 < n)
  have hposj0 : (0 : ℝ) < m j0 := by
    have hg := one_le_of_mem_D hmD (by omega : j0 < n)
    linarith
  have hsucc : brat n (bx m n) m (j0 + 1)
      = brat n (bx m n) m j0 + (2 - m j0) / m j0 := by
    change Ak n (bx m n) m (j0 + 1) / m (j0 + 1)
        = Ak n (bx m n) m j0 / m j0 + (2 - m j0) / m j0
    have hAk := Ak_succ n (bx m n) m j0
    rw [hAk]
    have heq' : m (j0 + 1) = m j0 := hj0spec.2.2.symm
    rw [heq']
    ring
  have hle_next : brat n (bx m n) m (j0 + 1) ≤ bval n hn m :=
    le_bF_of_mem n hn (bx m n) m (Finset.mem_range.mpr (by omega : j0 + 1 < n))
  have hgtnext : bval n hn m < brat n (bx m n) m (j0 + 1) := by
    rw [hsucc, hrat_j0]
    have hpos : 0 < (2 - m j0) / m j0 := by positivity
    linarith
  linarith

end Step3

/-! ## Active ratios and `y`-bounds -/

section ActiveY


/-- all ratios are the maximum `M` on the tail `[L, n-1]` -/
lemma active_ratio (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) {t : ℕ} (htL : L ≤ t) (htn : t < n) :
    brat n (bx m n) m t = bval n hn m := by
  have hstrict : ∀ j, L ≤ j → j < n - 1 → m j < m (j + 1) := by
    intro j hj1 hj2
    exact minimizer_tail_strict n hn hmD hmin hL1 hLn hone hLgt hj1 hj2
  -- induction on t - L
  have main : ∀ q : ℕ, ∀ t : ℕ, L ≤ t → t - L = q → t < n →
      brat n (bx m n) m t = bval n hn m := by
    intro q
    induction q with
    | zero =>
        intro t htL hdiff htn
        have ht : t = L := by omega
        subst t
        have hsub : (L - 1) + 1 = L := by omega
        have hprev : m (L - 1) < m L := by
          have hone' : m (L - 1) = 1 := hone (L - 1) (by omega)
          rw [hone']
          exact hLgt
        have hs := step1 n hn hmD hmin (t := L - 1) (by omega : (L - 1) + 1 < n)
          (by simpa [hsub] using hprev)
        simpa [hsub] using hs
    | succ q ih =>
        intro t htL hdiff htn
        -- t ≥ L+1: use step1 at pair (t-1, t)
        have htn1 : t - 1 < n - 1 := by omega
        have hsub : (t - 1) + 1 = t := by omega
        have hprev : m (t - 1) < m t := by
          simpa [hsub] using hstrict (t - 1) (by omega) htn1
        have hs := step1 n hn hmD hmin (t := t - 1) (by omega : (t - 1) + 1 < n)
          (by simpa [hsub] using hprev)
        simpa [hsub] using hs
  exact main (t - L) t htL rfl htn

/-- value `y = 2 (x - n) + L`, shown equal to the ratio at `L - 1` -/
lemma y_ratio (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n) {L : ℕ}
    (hL1 : 1 ≤ L) (hL2 : L ≤ n) (hone : ∀ j, j < L → m j = 1) :
    brat n (bx m n) m (L - 1) = 2 * (bx m n - (n : ℝ)) + L := by
  have hm : m (L - 1) = 1 := hone (L - 1) (by omega)
  have hbpart : bpart m L = (L : ℝ) := by
    calc
      bpart m L = (∑ j ∈ Finset.range L, (1 : ℝ)) := by
        unfold bpart
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < L := Finset.mem_range.mp hj
        rw [hone j hj']
      _ = (L : ℝ) := by simp [Finset.sum_const, Finset.card_range]
  change Ak n (bx m n) m (L - 1) / m (L - 1) = 2 * (bx m n - (n : ℝ)) + (L : ℝ)
  rw [hm]
  have hcastL1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    norm_num
  unfold Ak
  have hsubL : L - 1 + 1 = L := by omega
  rw [hsubL]
  rw [hcastL1, hbpart]
  ring_nf

lemma y_bounds (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    (2 * (bx m n - (n : ℝ)) + L ≤ bval n hn m ∧
     bval n hn m < 2 * (bx m n - (n : ℝ)) + L + 1) := by
  let yR : ℝ := 2 * (bx m n - (n : ℝ)) + (L : ℝ)
  have hy : brat n (bx m n) m (L - 1) = yR := by
    dsimp [yR]
    exact y_ratio n hn hmD hL1 (by omega) hone
  have hmem : L - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega : L - 1 < n)
  have hle : yR ≤ bval n hn m := by
    rw [← hy]
    exact le_bF_of_mem n hn (bx m n) m hmem
  -- upper bound: A_L < yR + 1 and M = A_L / mL ≤ A_L
  have hA_L : Ak n (bx m n) m L = Ak n (bx m n) m (L - 1) + (2 - m L) := by
    have h0 := Ak_succ n (bx m n) m (L - 1)
    have hsub : (L - 1) + 1 = L := by omega
    simpa [hsub] using h0
  have hA_Lm : Ak n (bx m n) m (L - 1) = yR := by
    -- brat(L-1) = yR = A(L-1)/m(L-1); m(L-1) = 1
    have hm : m (L - 1) = 1 := hone (L - 1) (by omega)
    rw [brat_eq_div] at hy
    change Ak n (bx m n) m (L - 1) / m (L - 1) = yR at hy
    rw [hm] at hy
    simpa using hy
  have hA_L_lt : Ak n (bx m n) m L < yR + 1 := by
    rw [hA_L, hA_Lm]
    have hmL : m L > 1 := hLgt
    linarith
  have hM_le_AL : bval n hn m ≤ Ak n (bx m n) m L := by
    have hratL : brat n (bx m n) m L = bval n hn m :=
      active_ratio n hn hmD hmin hL1 hLn hone hLgt (by omega : L ≤ L) (by omega : L < n)
    rw [← hratL]
    rw [brat_eq_div]
    have hpos : (0 : ℝ) < m L := by
      have hg := one_le_of_mem_D hmD (by omega : L < n)
      linarith
    have hposA : (0 : ℝ) ≤ Ak n (bx m n) m L := by
      have h1 := Ak_pos_of_mem_D n hn hmD (by omega : L < n)
      linarith
    -- A_L / mL ≤ A_L ⟺ A_L ≤ A_L·mL; since mL ≥ 1 and A_L ≥ 0
    rw [div_le_iff₀ hpos]
    have hmL1 : (1 : ℝ) ≤ m L := by
      have hg := one_le_of_mem_D hmD (by omega : L < n)
      exact hg
    nlinarith
  have hgt : bval n hn m < yR + 1 := by linarith
  dsimp [yR] at hle hgt
  exact ⟨hle, hgt⟩

end ActiveY

/-! ## Geometric decay of the defects -/

section DefectGeo


/-- The defect recursion `2 - m(k+1) = u·(2 - m k)` on the active tail. -/
lemma defect_rec (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) {k : ℕ}
    (hkL : L ≤ k) (hkn : k + 1 < n) :
    (2 - m (k + 1)) * (bval n hn m + 1) = (2 - m k) * bval n hn m := by
  -- from ratio_{k+1} = ratio_k = M: A_{k+1} = A_k + 2 - m(k+1): M·m(k+1) = M·m(k) + 2 - m(k+1)
  let M := bval n hn m
  have hAk : Ak n (bx m n) m (k + 1) = Ak n (bx m n) m k + (2 - m (k + 1)) :=
    Ak_succ n (bx m n) m k
  have hrat_k : brat n (bx m n) m k = M := by
    dsimp [M]
    exact active_ratio n hn hmD hmin hL1 hLn hone hLgt hkL (by omega : k < n)
  have hrat_k1 : brat n (bx m n) m (k + 1) = M := by
    dsimp [M]
    exact active_ratio n hn hmD hmin hL1 hLn hone hLgt (by omega : L ≤ k + 1) (by omega : k + 1 < n)
  have hpos : (0 : ℝ) < m k := by
    have hg := one_le_of_mem_D hmD (by omega : k < n)
    linarith
  have hpos1 : (0 : ℝ) < m (k + 1) := by
    have hg := one_le_of_mem_D hmD (by omega : k + 1 < n)
    linarith
  have hA_mul : Ak n (bx m n) m k = M * m k := by
    have hb := hrat_k
    dsimp [M]
    rw [brat_eq_div] at hb
    exact (div_eq_iff (ne_of_gt hpos)).mp hb
  have hA1_mul : Ak n (bx m n) m (k + 1) = M * m (k + 1) := by
    have hb := hrat_k1
    dsimp [M]
    rw [brat_eq_div] at hb
    exact (div_eq_iff (ne_of_gt hpos1)).mp hb
  have hlin : M * m (k + 1) = M * m k + (2 - m (k + 1)) := by
    rw [← hA1_mul, ← hA_mul, hAk]
  nlinarith

/-- iterate: `(2 - m t)·(M+1)^(t-L) = (2 - m L)·M^(t-L)` for `L ≤ t < n`. -/
lemma defect_geo (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) {t : ℕ}
    (htL : L ≤ t) (htn : t < n) :
    (2 - m t) * (bval n hn m + 1) ^ (t - L) = (2 - m L) * bval n hn m ^ (t - L) := by
  let M := bval n hn m
  have hstep : ∀ k : ℕ, L ≤ k → k + 1 < n →
      (2 - m (k + 1)) * (M + 1) = (2 - m k) * M := by
    intro k hk1 hk2
    have h := defect_rec n hn hmD hmin hL1 hLn hone hLgt hk1 hk2
    dsimp [M] at h ⊢
    exact h
  have main : ∀ q : ℕ, L + q < n →
      (2 - m (L + q)) * (M + 1) ^ ((L + q) - L) = (2 - m L) * M ^ ((L + q) - L) := by
    intro q
    induction q with
    | zero =>
        intro hn0
        have : (L + 0) - L = 0 := by omega
        simp [this]
    | succ q ih =>
        intro hn0
        have hlt : L + q < n := by omega
        have hprev := ih hlt
        have hs : (2 - m (L + q + 1)) * (M + 1) = (2 - m (L + q)) * M := by
          have hs0 := hstep (L + q) (by omega : L ≤ L + q) (by omega : (L + q) + 1 < n)
          have hsub : (L + q) + 1 = L + q + 1 := by omega
          simpa [hsub] using hs0
        have he1 : (L + q + 1) - L = q + 1 := by omega
        have he2 : L + q - L = q := by omega
        have hprev' : (2 - m (L + q)) * (M + 1) ^ q = (2 - m L) * M ^ q := by
          simpa [he2] using hprev
        calc
          (2 - m (L + q + 1)) * (M + 1) ^ ((L + q + 1) - L)
              = (2 - m (L + q + 1)) * (M + 1) ^ (q + 1) := by rw [he1]
          _ = (2 - m (L + q + 1)) * (M + 1) * (M + 1) ^ q := by
                rw [pow_succ]
                ring
          _ = (2 - m (L + q)) * M * (M + 1) ^ q := by rw [hs]
          _ = (2 - m (L + q)) * (M + 1) ^ q * M := by ring
          _ = (2 - m L) * M ^ q * M := by rw [hprev']
          _ = (2 - m L) * M ^ (q + 1) := by
                rw [pow_succ]
                ring
          _ = (2 - m L) * M ^ ((L + q + 1) - L) := by rw [he1]
  -- instantiate with q := t - L
  have hq : L + (t - L) < n := by omega
  have hres := main (t - L) hq
  have hsum : L + (t - L) = t := by omega
  have hdiff1 : (L + (t - L)) - L = t - L := by omega
  have hres' : (2 - m t) * (M + 1) ^ (t - L) = (2 - m L) * M ^ (t - L) := by
    simpa [hsum, hdiff1] using hres
  dsimp [M] at hres' ⊢
  exact hres'

end DefectGeo

/-! ## Consistency relations for the minimizer -/

section Consistency


/-- `x = M·m(n-1)`: the value is `x / m(n-1)` at the last index. -/
lemma x_eq_M_mul_last (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) :
    bx m n = (bval n hn m) * m (n - 1) := by
  have hlast : brat n (bx m n) m (n - 1) = bval n hn m := by
    rcases minimizer_has_jump_index n hn hmD hmin with ⟨L, hL1, hLn, hone, hLgt⟩
    exact active_ratio n hn hmD hmin hL1 hLn hone hLgt (by omega : L ≤ n - 1) (by omega : n - 1 < n)
  have hbr : brat n (bx m n) m (n - 1) = (bx m n) / m (n - 1) :=
    brat_last n (by omega : 1 ≤ n) (bx m n) m rfl
  rw [hbr] at hlast
  have hpos : m (n - 1) ≠ 0 := by
    have hg : 1 ≤ m (n - 1) := one_le_of_mem_D hmD (by omega : n - 1 < n)
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hg)
  exact (div_eq_iff hpos).mp hlast

/-- defect at `L`: `(2 - m L)·(M+1) = 2M - y`. -/
lemma defect_base (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    (2 - m L) * (bval n hn m + 1) = 2 * (bval n hn m) - (2 * (bx m n - (n : ℝ)) + L) := by
  -- from ratio_L = M and A_L = A_{L-1} + 2 - m L, A_{L-1} = y
  let M := bval n hn m
  let X := bx m n
  have hratL : brat n X m L = M := by
    dsimp [X, M]
    exact active_ratio n hn hmD hmin hL1 hLn hone hLgt (by omega : L ≤ L) (by omega : L < n)
  have hy : brat n X m (L - 1) = 2 * (X - (n : ℝ)) + L := by
    dsimp [X]
    exact y_ratio n hn hmD hL1 (by omega) hone
  -- A_L = A_{L-1} + 2 - mL ; ratio_L = M: M·mL = A_L; ratio_{L-1} = A_{L-1}/m(L-1) = A_{L-1} = y
  have hposL : m L ≠ 0 := by
    have hg : 1 ≤ m L := one_le_of_mem_D hmD (by omega : L < n)
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hg)
  have hpos : m (L - 1) ≠ 0 := by
    have hg : 1 ≤ m (L - 1) := one_le_of_mem_D hmD (by omega : L - 1 < n)
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hg)
  have hAkL : M * m L = Ak n X m (L - 1) + (2 - m L) := by
    -- A_L = M·mL (from ratio), A_L = A_{L-1} + 2 - mL
    have hA1 : Ak n X m L = M * m L := by
      have hb := hratL
      rw [brat_eq_div] at hb
      -- hb: (Ak L)/mL = M: Ak L = M·mL
      exact (div_eq_iff hposL).mp hb
    have hA0 := Ak_succ n X m (L - 1)
    have hsub : (L - 1) + 1 = L := by omega
    have hsucc : Ak n X m L = Ak n X m (L - 1) + (2 - m L) := by simpa [hsub] using hA0
    rw [hsucc] at hA1
    exact hA1.symm
  have hAk0 : Ak n X m (L - 1) = 2 * (X - (n : ℝ)) + L := by
    -- from hy: brat(L-1) = A(L-1)/1 = A(L-1) = y
    have hb := hy
    rw [brat_eq_div] at hb
    have hm : m (L - 1) = 1 := hone (L - 1) (by omega)
    change Ak n X m (L - 1) / m (L - 1) = 2 * (X - (n : ℝ)) + L at hb
    rw [hm] at hb
    simpa using hb
  -- (2 - mL)(M+1) = M + 2 - mL·? expand: from M·mL = y + 2 - mL: M·mL + mL = y + 2 → (M+1)mL = y+2 → 2 - mL = ...; (2-mL)(M+1) = 2(M+1) - mL(M+1) = 2M+2-(y+2) = 2M - y ✓
  dsimp [M, X] at hAkL hAk0 ⊢
  have hlin : bval n hn m * m L = (2 * (bx m n - (n : ℝ)) + L) + (2 - m L) := by
    have h1 := hAkL
    rw [hAk0] at h1
    simpa using h1
  nlinarith

/-- power-form of the defect at `n - 1`. -/
lemma defect_last_pow (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    (2 - m (n - 1)) * (bval n hn m + 1) ^ (n - 1 - L)
      = (2 - m L) * bval n hn m ^ (n - 1 - L) := by
  exact defect_geo n hn hmD hmin hL1 hLn hone hLgt (by omega : L ≤ n - 1) (by omega : n - 1 < n)

end Consistency

/-! ## The relation `X·(M+1)^s = 2M·(M+1)^s - (2M-y)·M^s` -/

section LastRel


/-- combine defect-base and the defect at the last index -/
lemma m_last_times (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    (2 - m (n - 1)) * (bval n hn m + 1) ^ (n - L)
      = (2 * bval n hn m - (2 * (bx m n - (n : ℝ)) + L)) * (bval n hn m) ^ (n - 1 - L) := by
  have hdL := defect_base n hn hmD hmin hL1 hLn hone hLgt
  have hdp := defect_last_pow n hn hmD hmin hL1 hLn hone hLgt
  have hs : n - 1 - L + 1 = n - L := by omega
  have hdp' : (2 - m (n - 1)) * (bval n hn m + 1) ^ (n - L)
      = (2 - m L) * (bval n hn m) ^ (n - 1 - L) * (bval n hn m + 1) := by
    calc
      (2 - m (n - 1)) * (bval n hn m + 1) ^ (n - L)
          = (2 - m (n - 1)) * ((bval n hn m + 1) ^ (n - 1 - L) * (bval n hn m + 1)) := by
            congr 1
            rw [← hs, pow_succ]
      _ = (2 - m (n - 1)) * (bval n hn m + 1) ^ (n - 1 - L) * (bval n hn m + 1) := by ring
      _ = (2 - m L) * (bval n hn m) ^ (n - 1 - L) * (bval n hn m + 1) := by
            rw [hdp]
  have hdL' : (2 - m L) * (bval n hn m + 1) = 2 * bval n hn m - (2 * (bx m n - (n : ℝ)) + L) := hdL
  calc
    (2 - m (n - 1)) * (bval n hn m + 1) ^ (n - L)
        = (2 - m L) * (bval n hn m) ^ (n - 1 - L) * (bval n hn m + 1) := hdp'
    _ = ((2 - m L) * (bval n hn m + 1)) * (bval n hn m) ^ (n - 1 - L) := by ring
    _ = (2 * bval n hn m - (2 * (bx m n - (n : ℝ)) + L)) * (bval n hn m) ^ (n - 1 - L) := by rw [hdL']

end LastRel

/-! ## The relation `x = 2M - (2M-y)·(M/(M+1))^{n-L}` -/

section XRel


/-- `X = 2M - (2M-y)·θ` with `θ = (M/(M+1))^(n-L)` -/
lemma x_eq_twoM_sub (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    bx m n = 2 * bval n hn m
      - (2 * bval n hn m - (2 * (bx m n - (n : ℝ)) + L))
        * (bval n hn m / (bval n hn m + 1)) ^ (n - L) := by
  let M := bval n hn m
  let X := bx m n
  let yR : ℝ := 2 * (X - (n : ℝ)) + L
  let s := n - L
  have hM1 : 0 < M := by
    dsimp [M]
    have h := one_le_bval_of_mem_D n hn hmD
    linarith
  have hM1p : M + 1 ≠ 0 := by linarith
  have hXeq : X = M * m (n - 1) := by
    dsimp [M, X]
    exact x_eq_M_mul_last n hn hmD hmin
  have hlast := m_last_times n hn hmD hmin hL1 hLn hone hLgt
  have hpow : (2 - m (n - 1)) * (M + 1) ^ s = (2 * M - yR) * M ^ (s - 1) := by
    dsimp [M, X, yR, s]
    have hExp : n - L - 1 = n - 1 - L := by omega
    rw [hExp]
    exact hlast
  have hs1 : (s - 1) + 1 = s := by dsimp [s]; omega
  have hMs : M ^ (s - 1) * M = M ^ s := by
    rw [← pow_succ]
    rw [hs1]
  have hmm : M * ((2 * M - yR) * M ^ (s - 1)) = (2 * M - yR) * M ^ s := by
    calc
      M * ((2 * M - yR) * M ^ (s - 1)) = ((2 * M - yR) * M ^ (s - 1)) * M := by ring
      _ = (2 * M - yR) * (M ^ (s - 1) * M) := by ring
      _ = (2 * M - yR) * M ^ s := by rw [hMs]
  have hx' : X * (M + 1) ^ s = 2 * M * (M + 1) ^ s - (2 * M - yR) * M ^ s := by
    calc
      X * (M + 1) ^ s = (M * m (n - 1)) * (M + 1) ^ s := by rw [hXeq]
      _ = M * (m (n - 1) * (M + 1) ^ s) := by ring
      _ = M * (2 * (M + 1) ^ s - (2 - m (n - 1)) * (M + 1) ^ s) := by ring
      _ = M * (2 * (M + 1) ^ s - (2 * M - yR) * M ^ (s - 1)) := by
            rw [hpow]
      _ = 2 * M * (M + 1) ^ s - M * ((2 * M - yR) * M ^ (s - 1)) := by ring
      _ = 2 * M * (M + 1) ^ s - (2 * M - yR) * M ^ s := by rw [hmm]
  have hp : (M + 1) ^ s ≠ 0 := pow_ne_zero _ hM1p
  have hXb : X * (M + 1) ^ s
      = (2 * M - (2 * M - yR) * (M ^ s / (M + 1) ^ s)) * (M + 1) ^ s := by
    rw [hx']
    field_simp [hp]
  have hmain : X = 2 * M - (2 * M - yR) * (M ^ s / (M + 1) ^ s) :=
    mul_right_cancel₀ hp hXb
  have hdiv : M ^ s / (M + 1) ^ s = (M / (M + 1)) ^ s := by
    exact (div_pow (a := M) (b := M + 1) (n := s)).symm
  have hfin : X = 2 * M - (2 * M - yR) * (M / (M + 1)) ^ s := by
    rw [hdiv] at hmain
    exact hmain
  dsimp [M, X, yR] at hfin ⊢
  exact hfin

end XRel

/-! ## The perturbation parameter family
We build, for a real parameter `F` near the minimizer's value `M`, a sequence
`wF n L F` of the geometric shape and show it is admissible with value `F`.
-/

set_option autoImplicit false

/-! ### Parameter family: geometric shape used in the perturbation -/

noncomputable def uu (F : ℝ) : ℝ := F / (F + 1)
noncomputable def th (n L : ℕ) (F : ℝ) : ℝ := (F / (F + 1)) ^ (n - L)
/-- the solution `y'` of the fixed point `y' = 2(x'-n)+L` with sum consistency -/
noncomputable def yF (n L : ℕ) (F : ℝ) : ℝ :=
  (2 * (n : ℝ) - (L : ℝ) - 4 * F * (1 - th n L F)) / (2 * th n L F - 1)
/-- the total sum `x' = n + (y'-L)/2` -/
noncomputable def xF (n L : ℕ) (F : ℝ) : ℝ := (n : ℝ) + (yF n L F - (L : ℝ)) / 2
/-- the sequence `w(F)`: `1` before `L`, geometric shape on `[L,n)`, `1` after -/
noncomputable def wF (n L : ℕ) (F : ℝ) : ℕ → ℝ :=
  fun j => if j < L then 1 else if j < n then
    2 - ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L) else 1

lemma geom_sum_one_sub (u : ℝ) (hu : u ≠ 1) (s : ℕ) :
    (∑ i ∈ Finset.range s, u ^ i) = (1 - u ^ s) / (1 - u) := by
  have hg := geom_sum_eq hu s
  rw [hg]
  field_simp [sub_ne_zero.mpr hu]
  ring

lemma tail_geom_Ico (n L : ℕ) (u : ℝ) (hu : u ≠ 1) :
    (∑ j ∈ Finset.Ico L n, (u ^ (j - L))) = (1 - u ^ (n - L)) / (1 - u) := by
  have hs := Finset.sum_Ico_eq_sum_range (fun j => u ^ (j - L)) L n
  rw [hs]
  have hc : ∀ k ∈ Finset.range (n - L), u ^ ((L + k) - L) = u ^ k := by
    intro k hk
    congr 1
    omega
  rw [Finset.sum_congr rfl hc]
  exact geom_sum_one_sub u hu (n - L)

lemma uu_ne_one_of_ne (F : ℝ) (hF : F + 1 ≠ 0) : uu F ≠ 1 := by
  dsimp [uu]
  intro h
  field_simp [hF] at h
  linarith

lemma one_sub_uu (F : ℝ) (hF : F + 1 ≠ 0) : 1 - uu F = (1 : ℝ) / (F + 1) := by
  dsimp [uu]
  field_simp [hF]
  ring

lemma yF_mul (n L : ℕ) (F : ℝ) (hd : 2 * th n L F - 1 ≠ 0) :
    yF n L F * (2 * th n L F - 1)
      = 2 * (n : ℝ) - (L : ℝ) - 4 * F * (1 - th n L F) := by
  dsimp [yF]
  field_simp [hd]

lemma yF_eq_xF (n L : ℕ) (F : ℝ) : yF n L F = 2 * (xF n L F - (n : ℝ)) + (L : ℝ) := by
  dsimp [xF]
  ring

lemma xF_consistency (n L : ℕ) (F : ℝ) (hd : 2 * th n L F - 1 ≠ 0) :
    xF n L F = (2 * (n : ℝ) - (L : ℝ)) - (2 * F - yF n L F) * (1 - th n L F) := by
  have hy := yF_mul n L F hd
  dsimp [xF]
  field_simp [hd]
  nlinarith [hy]

-- term values of wF
lemma wF_head (n L : ℕ) (F : ℝ) {j : ℕ} (hj : j < L) : wF n L F j = 1 := by
  simp [wF, hj]

lemma wF_tail (n L : ℕ) (F : ℝ) {j : ℕ} (hjL : L ≤ j) (hjn : j < n) :
    wF n L F j = 2 - ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L) := by
  have hnot : ¬ j < L := by omega
  simp [wF, hnot, hjn]

lemma wF_tail1 (n L : ℕ) {F : ℝ} {j : ℕ} (hLn : L < n) (hj : n ≤ j) : wF n L F j = 1 := by
  have hnot1 : ¬ j < L := by omega
  have hnot2 : ¬ j < n := by omega
  simp [wF, hnot1, hnot2]

/-- the tail sum over `[L, n)` in closed form -/

lemma wF_L_val (n L : ℕ) (F : ℝ) (hL : L < n) :
    wF n L F L = 2 - (2 * F - yF n L F) / (F + 1) := by
  have ht := wF_tail n L F (le_rfl : L ≤ L) hL
  rw [ht]
  simp

lemma bpart_wF_head (n L : ℕ) (F : ℝ) :
    bpart (wF n L F) L = (L : ℝ) := by
  unfold bpart
  calc
    (∑ j ∈ Finset.range L, wF n L F j) = (∑ j ∈ Finset.range L, (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact wF_head n L F (Finset.mem_range.mp hj)
    _ = (L : ℝ) := by simp [Finset.sum_const, Finset.card_range]

lemma tail_wF_closed (n L : ℕ) (hLn : L < n) (F : ℝ) (hF : F + 1 ≠ 0) :
    (∑ j ∈ Finset.Ico L n, wF n L F j)
      = 2 * ((n : ℝ) - (L : ℝ)) - (2 * F - yF n L F) * (1 - th n L F) := by
  have hconst : (∑ j ∈ Finset.Ico L n, (2 : ℝ)) = 2 * ((n : ℝ) - (L : ℝ)) := by
    have hc := Finset.sum_Ico_eq_sum_range (fun _ : ℕ => (2 : ℝ)) L n
    rw [hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Nat.cast_sub (by omega : L ≤ n)]
    ring
  have hB : (∑ j ∈ Finset.Ico L n, (((2 * F - yF n L F) / (F + 1)) * (uu F ^ (j - L))))
      = (2 * F - yF n L F) * (1 - th n L F) := by
    calc
      (∑ j ∈ Finset.Ico L n, (((2 * F - yF n L F) / (F + 1)) * (uu F ^ (j - L))))
          = ((2 * F - yF n L F) / (F + 1)) * (∑ j ∈ Finset.Ico L n, (uu F ^ (j - L))) := by
            symm
            rw [Finset.mul_sum]
      _ = ((2 * F - yF n L F) / (F + 1)) * ((1 - (uu F) ^ (n - L)) / (1 - uu F)) := by
            rw [tail_geom_Ico n L (uu F) (uu_ne_one_of_ne F hF)]
      _ = (2 * F - yF n L F) * (1 - (uu F) ^ (n - L)) := by
            rw [one_sub_uu F hF]
            field_simp [hF]
      _ = (2 * F - yF n L F) * (1 - th n L F) := by
            have hth : (uu F) ^ (n - L) = th n L F := by dsimp [th, uu]
            rw [hth]
  calc
    (∑ j ∈ Finset.Ico L n, wF n L F j)
        = (∑ j ∈ Finset.Ico L n, ((2 : ℝ) - (((2 * F - yF n L F) / (F + 1)) * (uu F ^ (j - L))))) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact wF_tail n L F (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    _ = (∑ j ∈ Finset.Ico L n, (2 : ℝ))
          - (∑ j ∈ Finset.Ico L n, (((2 * F - yF n L F) / (F + 1)) * (uu F ^ (j - L)))) := by
          rw [Finset.sum_sub_distrib]
    _ = 2 * ((n : ℝ) - (L : ℝ))
          - (2 * F - yF n L F) * (1 - th n L F) := by
          rw [hconst, hB]

/-- total sum of the shape: `bx (wF n L F) n = (2n-L) - (2F-yF)(1-θ)` -/
lemma bx_wF_shape (n L : ℕ) (hLn : L < n) (F : ℝ) (hF : F + 1 ≠ 0) :
    bx (wF n L F) n = (2 * (n : ℝ) - (L : ℝ)) - (2 * F - yF n L F) * (1 - th n L F) := by
  unfold bx bpart
  rw [← (Finset.sum_range_add_sum_Ico (fun j => wF n L F j) (by omega : L ≤ n))]
  have hhead : (∑ j ∈ Finset.range L, wF n L F j) = (L : ℝ) := by
    calc
      (∑ j ∈ Finset.range L, wF n L F j) = (∑ j ∈ Finset.range L, (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact wF_head n L F (Finset.mem_range.mp hj)
      _ = (L : ℝ) := by simp [Finset.sum_const, Finset.card_range]
  have htail := tail_wF_closed n L hLn F hF
  rw [hhead, htail]
  ring

/-- the total is exactly `xF` when the denominator does not vanish -/
lemma bx_wF (n L : ℕ) (hLn : L < n) (F : ℝ) (hF : F + 1 ≠ 0) (hd : 2 * th n L F - 1 ≠ 0) :
    bx (wF n L F) n = xF n L F := by
  rw [bx_wF_shape n L hLn F hF, xF_consistency n L F hd]

set_option autoImplicit false

/-! ## Inequalities for the shape `wF` -/

lemma uu_pos_of_pos (F : ℝ) (hF : 0 < F) : 0 < uu F := by
  dsimp [uu]
  exact div_pos hF (by linarith)

lemma uu_lt_one_of_pos (F : ℝ) (hF : 0 < F) : uu F < 1 := by
  dsimp [uu]
  rw [div_lt_one (by linarith : 0 < F + 1)]
  linarith

lemma uu_pow_pos (F : ℝ) (hF : 0 < F) (k : ℕ) : 0 < uu F ^ k :=
  pow_pos (uu_pos_of_pos F hF) k

lemma uu_pow_le_one (F : ℝ) (hF : 0 < F) (k : ℕ) : uu F ^ k ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hlt := pow_lt_one₀ (a := uu F) (n := k) (le_of_lt (uu_pos_of_pos F hF))
        (uu_lt_one_of_pos F hF) (by omega : k ≠ 0)
    linarith

/-- `0 < c` where `c := (2F-yF)/(F+1)` -/
lemma c_pos (n L : ℕ) (F : ℝ) (hF : 0 < F) (hyl : yF n L F ≤ F) :
    0 < (2 * F - yF n L F) / (F + 1) := by
  have hpos : 0 < 2 * F - yF n L F := by nlinarith
  exact div_pos hpos (by linarith : 0 < F + 1)

/-- `c < 1` where `c := (2F-yF)/(F+1)` -/
lemma c_lt_one (n L : ℕ) (F : ℝ) (hF : 0 < F) (hyu : F < yF n L F + 1) :
    (2 * F - yF n L F) / (F + 1) < 1 := by
  rw [div_lt_one (by linarith : 0 < F + 1)]
  linarith

/-- on the active tail, `1 < w j < 2` -/
lemma wF_tail_bounds (n L : ℕ) (F : ℝ) (hF : 0 < F) (hyl : yF n L F ≤ F)
    (hyu : F < yF n L F + 1) {j : ℕ} (hjL : L ≤ j) (hjn : j < n) :
    (1 : ℝ) < wF n L F j ∧ wF n L F j < 2 := by
  have hval : wF n L F j = 2 - ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L) :=
    wF_tail n L F hjL hjn
  have hc0 : 0 < (2 * F - yF n L F) / (F + 1) := c_pos n L F hF hyl
  have hc1 : (2 * F - yF n L F) / (F + 1) < 1 := c_lt_one n L F hF hyu
  have hu0 : 0 < uu F ^ (j - L) := uu_pow_pos F hF (j - L)
  have hu1 : uu F ^ (j - L) ≤ 1 := uu_pow_le_one F hF (j - L)
  have hprod_pos : 0 < ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L) :=
    mul_pos hc0 hu0
  have hprod_lt : ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L) < 1 := by
    have hle : ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L)
        ≤ (2 * F - yF n L F) / (F + 1) := by
      calc
        ((2 * F - yF n L F) / (F + 1)) * uu F ^ (j - L)
            ≤ ((2 * F - yF n L F) / (F + 1)) * 1 := mul_le_mul_of_nonneg_left hu1 (le_of_lt hc0)
        _ = (2 * F - yF n L F) / (F + 1) := by ring
    linarith
  rw [hval]
  constructor <;> linarith

lemma wF_one_le (n L : ℕ) (F : ℝ) (hF : 0 < F) (hyl : yF n L F ≤ F)
    (hyu : F < yF n L F + 1) {j : ℕ} (hj : j < n) : (1 : ℝ) ≤ wF n L F j := by
  by_cases hjL : j < L
  · rw [wF_head n L F hjL]
  · have hge : L ≤ j := by omega
    have hb := wF_tail_bounds n L F hF hyl hyu hge hj
    linarith

lemma wF_tail_strict (n L : ℕ) (F : ℝ) (hF : 0 < F) (hyl : yF n L F ≤ F)
    (hyu : F < yF n L F + 1) {j : ℕ} (hjL : L ≤ j) (hjn : j + 1 < n) :
    wF n L F j < wF n L F (j + 1) := by
  let c : ℝ := (2 * F - yF n L F) / (F + 1)
  let u : ℝ := uu F
  have hc0 : 0 < c := by
    dsimp [c]
    exact c_pos n L F hF hyl
  have hu0 : 0 < u := by dsimp [u]; exact uu_pos_of_pos F hF
  have hu1 : u < 1 := by dsimp [u]; exact uu_lt_one_of_pos F hF
  have hv1 : wF n L F j = 2 - c * u ^ (j - L) := by
    dsimp [c, u]
    rw [wF_tail n L F hjL (by omega : j < n)]
  have hv2 : wF n L F (j + 1) = 2 - c * u ^ (j + 1 - L) := by
    dsimp [c, u]
    rw [wF_tail n L F (by omega : L ≤ j + 1) hjn]
  have hexp : j + 1 - L = (j - L) + 1 := by omega
  have hpowpos : 0 < u ^ (j - L) := pow_pos hu0 (j - L)
  have hdiff : wF n L F (j + 1) - wF n L F j
      = c * u ^ (j - L) * (1 - u) := by
    rw [hv2, hv1, hexp, pow_succ]
    ring
  have hpos : 0 < c * u ^ (j - L) * (1 - u) := by
    have h1 : 0 < 1 - u := by linarith
    positivity
  linarith

lemma wF_mono (n L : ℕ) (F : ℝ) (hF : 0 < F) (hyl : yF n L F ≤ F)
    (hyu : F < yF n L F + 1) {j : ℕ} (hjn : j + 1 < n) :
    wF n L F j ≤ wF n L F (j + 1) := by
  by_cases hjL : j < L
  · by_cases hj1L : j + 1 < L
    · rw [wF_head n L F hjL, wF_head n L F hj1L]
    · have hge : L ≤ j + 1 := by omega
      have hlt : j + 1 < n := hjn
      have hgt := wF_tail_bounds n L F hF hyl hyu hge hlt
      rw [wF_head n L F hjL]
      linarith
  · have hge : L ≤ j := by omega
    exact le_of_lt (wF_tail_strict n L F hF hyl hyu hge hjn)

/-- membership in `D` -/
lemma wF_mem_D (n L : ℕ) (hn : 2 ≤ n) (hL1 : 1 ≤ L) (hLn : L < n) (F : ℝ)
    (hF : 0 < F) (hyl : yF n L F ≤ F) (hyu : F < yF n L F + 1)
    (hd : 2 * th n L F - 1 ≠ 0)
    (hxlo : (n : ℝ) ≤ xF n L F) (hxup : xF n L F ≤ ((3 * (n : ℝ) - 1) / 2)) :
    wF n L F ∈ D n := by
  have hbx : bx (wF n L F) n = xF n L F := bx_wF n L hLn F (by linarith : F + 1 ≠ 0) hd
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have h0 : (0 : ℕ) < L := by omega
      exact wF_head n L F h0
    · intro j hj
      exact wF_one_le n L F hF hyl hyu hj
    · intro j hj1
      exact wF_mono n L F hF hyl hyu hj1
    · rw [hbx]
      exact hxlo
  · rw [hbx]
    exact hxup
  · intro j hj
    exact wF_tail1 n L hLn hj

set_option autoImplicit false

/-! ## Ratios of the shape `wF`: head ratios `≤ yF`, tail ratios `= F` -/

/-- `w_L = (yF+2)/(F+1)` -/
lemma wF_L_val' (n L : ℕ) (hLn : L < n) (F : ℝ) (hF : F + 1 ≠ 0) :
    wF n L F L = (yF n L F + 2) / (F + 1) := by
  rw [wF_L_val n L F hLn]
  field_simp [hF]
  ring

/-- the head part of `A` before `L` is `yF` at index `L-1` -/
lemma A_Lm1_eq_yF (n L : ℕ) (hL1 : 1 ≤ L) (F : ℝ) :
    Ak n (xF n L F) (wF n L F) (L - 1) = yF n L F := by
  unfold Ak
  have hbpart : bpart (wF n L F) (L - 1 + 1) = (L : ℝ) := by
    have hs : L - 1 + 1 = L := by omega
    rw [hs]
    exact bpart_wF_head n L F
  rw [hbpart]
  have hcast : ((n : ℝ) - 1 - ((L - 1 : ℕ) : ℝ)) = (n : ℝ) - (L : ℝ) := by
    have hc : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ L)]
      norm_num
    rw [hc]
    ring
  rw [hcast]
  have hy := yF_eq_xF n L F
  ring_nf at hy ⊢
  nlinarith

/-- base of the tail: `A_L = F·w_L` -/
lemma A_L_mul (n L : ℕ) (hL1 : 1 ≤ L) (hLn : L < n) (F : ℝ) (hF : F + 1 ≠ 0) :
    Ak n (xF n L F) (wF n L F) L = F * wF n L F L := by
  have hAsucc := Ak_succ n (xF n L F) (wF n L F) (L - 1)
  have hsub : (L - 1) + 1 = L := by omega
  have hA : Ak n (xF n L F) (wF n L F) L = Ak n (xF n L F) (wF n L F) (L - 1) + (2 - wF n L F L) := by
    simpa [hsub] using hAsucc
  rw [hA, A_Lm1_eq_yF n L hL1 F]
  have hwL : wF n L F L = (yF n L F + 2) / (F + 1) := wF_L_val' n L hLn F hF
  -- need: yF + 2 - wL = F·wL  ⟺  wL = (yF+2)/(F+1)  ✓
  rw [hwL]
  field_simp [hF]
  ring

/-- shape recursion on the tail: `(F+1)·w_{m+1} = F·w_m + 2` -/
lemma wF_rec (n L : ℕ) (F : ℝ) (hF : F + 1 ≠ 0) {m : ℕ} (hmL : L ≤ m) (hmn : m + 1 < n) :
    (F + 1) * wF n L F (m + 1) = F * wF n L F m + 2 := by
  have hv1 : wF n L F m = 2 - ((2 * F - yF n L F) / (F + 1)) * uu F ^ (m - L) := by
    rw [wF_tail n L F hmL (by omega : m < n)]
  have hv2 : wF n L F (m + 1) = 2 - ((2 * F - yF n L F) / (F + 1)) * uu F ^ (m + 1 - L) := by
    rw [wF_tail n L F (by omega : L ≤ m + 1) hmn]
  have hexp : m + 1 - L = (m - L) + 1 := by omega
  have hrel : (F + 1) * uu F = F := by
    dsimp [uu]
    field_simp [hF]
  rw [hv2, hv1, hexp, pow_succ]
  dsimp [uu]
  field_simp [hF]
  ring

/-- on the tail the ratio equals `F`: `A_m = F·w_m` -/
lemma tail_A_mul (n L : ℕ) (hL1 : 1 ≤ L) (hLn : L < n) (F : ℝ) (hF : F + 1 ≠ 0)
    {m : ℕ} (hmL : L ≤ m) (hmn : m < n) :
    Ak n (xF n L F) (wF n L F) m = F * wF n L F m := by
  have main : ∀ q : ℕ, ∀ m : ℕ, L ≤ m → m - L = q → m < n →
      Ak n (xF n L F) (wF n L F) m = F * wF n L F m := by
    intro q
    induction q with
    | zero =>
        intro m hmL hdiff hmn
        have hm : m = L := by omega
        subst m
        exact A_L_mul n L hL1 hLn F hF
    | succ q ih =>
        intro m hmL hdiff hmn
        have hprev : m - 1 ≥ L := by omega
        have hprevn : m - 1 < n := by omega
        have hprevq : (m - 1) - L = q := by omega
        have hih := ih (m - 1) hprev hprevq hprevn
        have hAsucc := Ak_succ n (xF n L F) (wF n L F) (m - 1)
        have hsub : (m - 1) + 1 = m := by omega
        have hA : Ak n (xF n L F) (wF n L F) m
            = Ak n (xF n L F) (wF n L F) (m - 1) + (2 - wF n L F m) := by
          simpa [hsub] using hAsucc
        rw [hA, hih]
        have hrec0 := wF_rec n L F hF hprev (by omega : (m - 1) + 1 < n)
        have hrec : (F + 1) * wF n L F m = F * wF n L F (m - 1) + 2 := by
          have hsubst : (m - 1) + 1 = m := by omega
          simpa [hsubst] using hrec0
        have hrec' : F * wF n L F m = F * wF n L F (m - 1) + 2 - wF n L F m := by
          nlinarith
        rw [hrec']
        ring
  exact main (m - L) m hmL rfl hmn

/-- ratio equals `F` on the tail -/
lemma tail_brat_eq_F (n L : ℕ) (hL1 : 1 ≤ L) (hLn : L < n) (F : ℝ) (hF : 0 < F)
    (hyl : yF n L F ≤ F) (hyu : F < yF n L F + 1)
    {m : ℕ} (hmL : L ≤ m) (hmn : m < n) :
    brat n (xF n L F) (wF n L F) m = F := by
  have hAm := tail_A_mul n L hL1 hLn F (by linarith : F + 1 ≠ 0) hmL hmn
  have hwm : wF n L F m ≠ 0 := by
    have hgt := (wF_tail_bounds n L F hF hyl hyu hmL hmn).1
    linarith
  rw [brat_eq_div, hAm]
  field_simp [hwm]

/-- head ratios: at `m < L` the ratio is `2(xF-n)+m+1` -/
lemma head_brat_val (n L : ℕ) (F : ℝ) {m : ℕ} (hm : m < L) :
    brat n (xF n L F) (wF n L F) m = 2 * (xF n L F - (n : ℝ)) + (m : ℝ) + 1 := by
  have hbpart : bpart (wF n L F) (m + 1) = (m + 1 : ℝ) := by
    unfold bpart
    calc
      (∑ j ∈ Finset.range (m + 1), wF n L F j) = (∑ j ∈ Finset.range (m + 1), (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < m + 1 := Finset.mem_range.mp hj
        exact wF_head n L F (by omega : j < L)
      _ = (m + 1 : ℝ) := by simp [Finset.sum_const, Finset.card_range]
  have hw : wF n L F m = 1 := wF_head n L F hm
  unfold brat
  rw [hbpart, hw]
  ring_nf

/-- head ratios are `≤ yF ≤ F` -/
lemma head_brat_le_yF (n L : ℕ) (F : ℝ) {m : ℕ} (hm : m < L) :
    brat n (xF n L F) (wF n L F) m ≤ yF n L F := by
  rw [head_brat_val n L F hm, yF_eq_xF n L F]
  have hmle : (m : ℝ) + 1 ≤ (L : ℝ) := by
    have hm1 : m + 1 ≤ L := by omega
    exact_mod_cast hm1
  linarith

/-- the value of `wF` is exactly `F` -/
lemma bval_wF_eq_F (n L : ℕ) (hn : 2 ≤ n) (hL1 : 1 ≤ L) (hLn : L < n) (F : ℝ)
    (hF : 0 < F) (hyl : yF n L F ≤ F) (hyu : F < yF n L F + 1)
    (hd : 2 * th n L F - 1 ≠ 0) :
    bval n hn (wF n L F) = F := by
  have hbx : bx (wF n L F) n = xF n L F := bx_wF n L hLn F (by linarith : F + 1 ≠ 0) hd
  apply le_antisymm
  · -- all ratios ≤ F
    rw [bval, hbx]
    rw [bF_le_iff n hn (xF n L F) (wF n L F) F]
    intro m hm
    have hm' : m < n := Finset.mem_range.mp hm
    by_cases hmL : m < L
    · have hle := head_brat_le_yF n L F hmL
      linarith [hyl]
    · have hge : L ≤ m := by omega
      rw [tail_brat_eq_F n L hL1 hLn F hF hyl hyu hge hm']
  · -- ratio at L equals F
    have hmem : L ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have hle := le_bF_of_mem n hn (xF n L F) (wF n L F) hmem
    have heq : brat n (xF n L F) (wF n L F) L = F :=
      tail_brat_eq_F n L hL1 hLn F hF hyl hyu (by omega : L ≤ L) (by omega : L < n)
    rw [bval, hbx]
    rw [heq] at hle
    exact hle


set_option autoImplicit false

lemma rat_pow_ne_two_real (p : ℕ) (s : ℕ) (hs : 2 ≤ s) :
    (((p + 2 : ℕ) : ℝ) / (p : ℝ)) ^ s ≠ 2 := by
  intro h
  have hQ : (((p + 2 : ℕ) : ℚ) / (p : ℚ)) ^ s ≠ 2 :=
    Commons.NumberTheory.Pow.rat_pow_ne_two (((p + 2 : ℕ) : ℚ) / (p : ℚ)) s hs
  have hnotR : ((((p + 2 : ℕ) : ℚ) / (p : ℚ)) : ℝ) ^ s ≠ (2 : ℝ) := by
    exact_mod_cast hQ
  have hcast : ((((p + 2 : ℕ) : ℚ) / (p : ℚ)) : ℝ) = ((p + 2 : ℕ) : ℝ) / (p : ℝ) := by
    norm_num
  exact hnotR (by rw [hcast]; exact h)

lemma R4_real (n M X y L θ : ℝ)
    (hR1 : X = 2 * M - (2 * M - y) * θ) (hy : y = 2 * (X - n) + L) :
    (3 - 2 * θ) * M = (2 * n - L) + (2 * θ - 1) * (M - y) := by
  ring_nf at hR1 hy ⊢
  nlinarith

/-- `θ = (M/(M+1))^(n-L) ≠ 1/2` at a minimizer -/
lemma theta_ne_half (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    (bval n hn m / (bval n hn m + 1)) ^ (n - L) ≠ (1 : ℝ) / 2 := by
  let M := bval n hn m
  let X := bx m n
  let yR : ℝ := 2 * (X - (n : ℝ)) + (L : ℝ)
  let u : ℝ := M / (M + 1)
  let s := n - L
  have hML : 1 ≤ M := by dsimp [M]; exact one_le_bval_of_mem_D n hn hmD
  have hMp : M + 1 ≠ 0 := by linarith
  intro hθ
  have hupow : u ^ s = (1 : ℝ) / 2 := by
    dsimp [u, s]
    simpa using hθ
  have hR1 : X = 2 * M - (2 * M - yR) * (u ^ s) := by
    dsimp [M, X, yR, u, s]
    exact x_eq_twoM_sub n hn hmD hmin hL1 hLn hone hLgt
  have hy : yR = 2 * (X - (n : ℝ)) + (L : ℝ) := rfl
  have hR4 := R4_real (n : ℝ) M X yR (L : ℝ) (u ^ s) hR1 hy
  have hM : M = (2 * (n : ℝ) - (L : ℝ)) / 2 := by
    rw [hupow] at hR4
    norm_num at hR4
    linarith
  let p : ℕ := 2 * n - L
  have hp0 : p ≠ 0 := by
    dsimp [p]
    omega
  have hp_eq : (p : ℝ) = 2 * (n : ℝ) - (L : ℝ) := by
    dsimp [p]
    rw [Nat.cast_sub (by omega : L ≤ 2 * n)]
    rw [Nat.cast_mul]
    norm_num
  have hu : u = (p : ℝ) / (p + 2) := by
    dsimp [u]
    have hM2 : M = (p : ℝ) / 2 := by
      rw [hM, hp_eq]
    rw [hM2]
    have hpp : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
    have hpp2 : (p : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hpp, hpp2]
  by_cases hs1 : s = 1
  · have hu12 : u = (1 : ℝ) / 2 := by
      have : u ^ 1 = (1 : ℝ) / 2 := by simpa [hs1] using hupow
      simpa using this
    have hM1 : M = 1 := by
      dsimp [u] at hu12
      field_simp [hMp] at hu12
      linarith
    have hL : (L : ℝ) = 2 * (n : ℝ) - 2 := by
      have hh := hM
      rw [hM1] at hh
      norm_num at hh
      linarith
    have hLnR : (L : ℝ) < (n : ℝ) := by exact_mod_cast hLn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  · have hs2 : 2 ≤ s := by omega
    have hu2 : ((p : ℝ) / (p + 2)) ^ s = (1 : ℝ) / 2 := by
      rw [← hu]
      exact hupow
    have hinv : ((p : ℝ) / (p + 2))⁻¹ = ((p + 2 : ℕ) : ℝ) / (p : ℝ) := by
      have hpp : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
      have hpp2 : (p : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hpp, hpp2]
      norm_num
    have hpown : ((p : ℝ) / (p + 2))⁻¹ ^ s = 2 := by
      rw [inv_pow, hu2]
      norm_num
    have hpown' : (((p + 2 : ℕ) : ℝ) / (p : ℝ)) ^ s = 2 := by
      rw [hinv] at hpown
      exact hpown
    have hne := rat_pow_ne_two_real p s hs2
    exact (hne hpown').elim

set_option autoImplicit false

/-! ## Continuity of the parameter functions and the choice of `F` -/

lemma continuousAt_th (n L : ℕ) (F0 : ℝ) (hF : F0 + 1 ≠ 0) :
    ContinuousAt (fun F : ℝ => th n L F) F0 := by
  have hid : ContinuousAt (fun F : ℝ => F) F0 := continuousAt_id
  have hadd : ContinuousAt (fun F : ℝ => F + 1) F0 := by
    change ContinuousAt ((fun F : ℝ => F) + fun _ : ℝ => (1 : ℝ)) F0
    exact hid.add continuousAt_const
  have hdiv : ContinuousAt (fun F : ℝ => F / (F + 1)) F0 := by
    change ContinuousAt ((fun F : ℝ => F) / fun F : ℝ => F + 1) F0
    exact hid.div₀ hadd hF
  have hpow : ContinuousAt (fun F : ℝ => (F / (F + 1)) ^ (n - L)) F0 := hdiv.pow (n - L)
  change ContinuousAt (fun F : ℝ => th n L F) F0
  simpa [th] using hpow

lemma continuousAt_thden (n L : ℕ) (F0 : ℝ) (hF : F0 + 1 ≠ 0) :
    ContinuousAt (fun F : ℝ => 2 * th n L F - 1) F0 := by
  have hth := continuousAt_th n L F0 hF
  have hmul : ContinuousAt (fun F : ℝ => 2 * th n L F) F0 := by
    change ContinuousAt ((fun _ : ℝ => (2 : ℝ)) * fun F : ℝ => th n L F) F0
    exact continuousAt_const.mul hth
  change ContinuousAt ((fun F : ℝ => 2 * th n L F) - fun _ : ℝ => (1 : ℝ)) F0
  exact hmul.sub continuousAt_const

lemma continuousAt_yF (n L : ℕ) (F0 : ℝ) (hF : F0 + 1 ≠ 0) (hd : 2 * th n L F0 - 1 ≠ 0) :
    ContinuousAt (fun F : ℝ => yF n L F) F0 := by
  have hth := continuousAt_th n L F0 hF
  have hnum : ContinuousAt (fun F : ℝ => 2 * (n : ℝ) - (L : ℝ) - 4 * F * (1 - th n L F)) F0 := by
    have hc : ContinuousAt (fun F : ℝ => (2 * (n : ℝ) - (L : ℝ) : ℝ)) F0 := continuousAt_const
    have h4 : ContinuousAt (fun F : ℝ => 4 * F) F0 := by
      change ContinuousAt ((fun _ : ℝ => (4 : ℝ)) * fun F : ℝ => F) F0
      exact continuousAt_const.mul continuousAt_id
    have hsub : ContinuousAt (fun F : ℝ => 1 - th n L F) F0 := by
      change ContinuousAt ((fun _ : ℝ => (1 : ℝ)) - fun F : ℝ => th n L F) F0
      exact continuousAt_const.sub hth
    have hprod : ContinuousAt (fun F : ℝ => 4 * F * (1 - th n L F)) F0 := by
      change ContinuousAt ((fun F : ℝ => 4 * F) * fun F : ℝ => 1 - th n L F) F0
      exact h4.mul hsub
    have hneg : ContinuousAt (fun F : ℝ => -(4 * F * (1 - th n L F))) F0 := by
      change ContinuousAt (fun F : ℝ => -((fun F : ℝ => 4 * F * (1 - th n L F)) F)) F0
      exact hprod.neg
    change ContinuousAt ((fun F : ℝ => (2 * (n : ℝ) - (L : ℝ) : ℝ))
        + fun F : ℝ => -(4 * F * (1 - th n L F))) F0
    exact hc.add hneg
  have hden := continuousAt_thden n L F0 hF
  have hmain := hnum.div₀ hden hd
  change ContinuousAt (fun F : ℝ => yF n L F) F0
  simpa [yF] using hmain

lemma continuousAt_xF (n L : ℕ) (F0 : ℝ) (hF : F0 + 1 ≠ 0) (hd : 2 * th n L F0 - 1 ≠ 0) :
    ContinuousAt (fun F : ℝ => xF n L F) F0 := by
  have hy := continuousAt_yF n L F0 hF hd
  have hsub : ContinuousAt (fun F : ℝ => yF n L F - (L : ℝ)) F0 := by
    change ContinuousAt ((fun F : ℝ => yF n L F) - fun _ : ℝ => (L : ℝ)) F0
    exact hy.sub continuousAt_const
  have hmul : ContinuousAt (fun F : ℝ => (yF n L F - (L : ℝ)) * (1 / 2 : ℝ)) F0 := by
    change ContinuousAt ((fun F : ℝ => yF n L F - (L : ℝ)) * fun _ : ℝ => (1 / 2 : ℝ)) F0
    exact hsub.mul continuousAt_const
  have hadd : ContinuousAt (fun F : ℝ => (n : ℝ) + (yF n L F - (L : ℝ)) * (1 / 2 : ℝ)) F0 := by
    change ContinuousAt ((fun _ : ℝ => (n : ℝ)) + fun F : ℝ => (yF n L F - (L : ℝ)) * (1 / 2 : ℝ)) F0
    exact continuousAt_const.add hmul
  change ContinuousAt (fun F : ℝ => xF n L F) F0
  -- xF F = n + (yF F − L)/2 : rewrite /2 as *(1/2)
  simpa [xF, div_eq_mul_inv, one_div] using hadd

/-- if `g` is continuous at `M` with `g M < c`, then eventually `g F < c` -/
lemma eventually_lt_of_continuousAt {M c : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousAt g M) (h : g M < c) : ∀ᶠ F : ℝ in nhds M, g F < c := by
  have hmem : Set.Iio c ∈ nhds (g M) := isOpen_Iio.mem_nhds h
  simpa [Set.mem_Iio] using hg.tendsto.eventually hmem

/-- if `g` is continuous at `M` with `c < g M`, then eventually `c < g F` -/
lemma eventually_gt_of_continuousAt {M c : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousAt g M) (h : c < g M) : ∀ᶠ F : ℝ in nhds M, c < g F := by
  have hmem : Set.Ioi c ∈ nhds (g M) := isOpen_Ioi.mem_nhds h
  simpa [Set.mem_Ioi] using hg.tendsto.eventually hmem

/-- if `g` is continuous at `M` and `g M ≠ a`, then eventually `g F ≠ a` -/
lemma eventually_ne_of_continuousAt {M a : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousAt g M) (h : g M ≠ a) : ∀ᶠ F : ℝ in nhds M, g F ≠ a := by
  have hmem : {y : ℝ | y ≠ a} ∈ nhds (g M) := isOpen_ne.mem_nhds h
  simpa using hg.tendsto.eventually hmem

/-- main existence: a parameter `F < M` close to `M` where everything behaves -/
lemma exists_F_good (n L : ℕ) (M : ℝ)
    (hM : 0 < M)
    (hθ : 2 * th n L M - 1 ≠ 0)
    (hA : yF n L M < M)
    (hB : M < yF n L M + 1)
    (hC : (n : ℝ) < xF n L M)
    (hD : xF n L M < (3 * (n : ℝ) - 1) / 2) :
    ∃ F : ℝ, 0 < F ∧ F < M ∧ yF n L F ≤ F ∧ F < yF n L F + 1 ∧
      (n : ℝ) ≤ xF n L F ∧ xF n L F ≤ ((3 * (n : ℝ) - 1) / 2) ∧
      2 * th n L F - 1 ≠ 0 := by
  have hFp : M + 1 ≠ 0 := by linarith
  have hthy : ContinuousAt (fun F : ℝ => th n L F) M := continuousAt_th n L M hFp
  have hyy : ContinuousAt (fun F : ℝ => yF n L F) M := continuousAt_yF n L M hFp hθ
  have hxx : ContinuousAt (fun F : ℝ => xF n L F) M := continuousAt_xF n L M hFp hθ
  have hdenc : ContinuousAt (fun F : ℝ => 2 * th n L F - 1) M := continuousAt_thden n L M hFp
  have hA' : (fun F : ℝ => yF n L F - F) M < 0 := by
    change yF n L M - M < 0
    exact sub_neg.mpr hA
  have hB' : (fun F : ℝ => F - (yF n L F + 1)) M < 0 := by
    change M - (yF n L M + 1) < 0
    exact sub_neg.mpr hB
  have hD' : (fun F : ℝ => xF n L F - ((3 * (n : ℝ) - 1) / 2)) M < 0 := by
    change xF n L M - (3 * (n : ℝ) - 1) / 2 < 0
    exact sub_neg.mpr hD
  have hev1 : ∀ᶠ F : ℝ in nhds M, yF n L F ≤ F := by
    have he := eventually_lt_of_continuousAt (g := fun F : ℝ => yF n L F - F)
      (hyy.sub continuousAt_id) hA'
    exact he.mono (fun F hF => by
      have hyf : yF n L F < F := by linarith
      exact le_of_lt hyf)
  have hev2 : ∀ᶠ F : ℝ in nhds M, F < yF n L F + 1 := by
    have he := eventually_lt_of_continuousAt (g := fun F : ℝ => F - (yF n L F + 1))
      (continuousAt_id.sub (hyy.add continuousAt_const)) hB'
    exact he.mono (fun F hF => by linarith)
  have hev3 : ∀ᶠ F : ℝ in nhds M, (n : ℝ) ≤ xF n L F := by
    have he := eventually_gt_of_continuousAt (g := fun F : ℝ => xF n L F) hxx hC
    exact he.mono (fun F hF => le_of_lt hF)
  have hev4 : ∀ᶠ F : ℝ in nhds M, xF n L F ≤ ((3 * (n : ℝ) - 1) / 2) := by
    have he := eventually_lt_of_continuousAt (g := fun F : ℝ => xF n L F - ((3 * (n : ℝ) - 1) / 2))
      (hxx.sub continuousAt_const) hD'
    exact he.mono (fun F hF => by
      have hx : xF n L F < (3 * (n : ℝ) - 1) / 2 := by linarith
      exact le_of_lt hx)
  have hev5 : ∀ᶠ F : ℝ in nhds M, 2 * th n L F - 1 ≠ 0 := by
    have he := eventually_ne_of_continuousAt (g := fun F : ℝ => 2 * th n L F - 1) hdenc hθ
    exact he
  have hev6 : ∀ᶠ F : ℝ in nhds M, 0 < F := by
    have he := eventually_gt_of_continuousAt (g := fun F : ℝ => F)
      (continuousAt_id : ContinuousAt (id : ℝ → ℝ) M) hM
    simpa using he
  have hall : ∀ᶠ F : ℝ in nhds M,
      0 < F ∧ yF n L F ≤ F ∧ F < yF n L F + 1 ∧ (n : ℝ) ≤ xF n L F ∧
      xF n L F ≤ ((3 * (n : ℝ) - 1) / 2) ∧ 2 * th n L F - 1 ≠ 0 := by
    exact Filter.Eventually.and hev6
      (Filter.Eventually.and hev1 (Filter.Eventually.and hev2
        (Filter.Eventually.and hev3 (Filter.Eventually.and hev4 hev5))))
  rcases Metric.eventually_nhds_iff.mp hall with ⟨eps, heps, hball⟩
  let eps' : ℝ := min eps M
  have heps' : 0 < eps' := by
    dsimp [eps']
    exact lt_min heps hM
  let F0 : ℝ := M - eps' / 2
  have hF0lt : F0 < M := by
    dsimp [F0]
    linarith
  have hF0pos : 0 < F0 := by
    dsimp [F0]
    have hle : eps' / 2 < M := by
      have h1 : eps' ≤ M := min_le_right eps M
      nlinarith
    linarith
  have hball0 : 0 < F0 ∧ yF n L F0 ≤ F0 ∧ F0 < yF n L F0 + 1 ∧ (n : ℝ) ≤ xF n L F0 ∧
      xF n L F0 ≤ ((3 * (n : ℝ) - 1) / 2) ∧ 2 * th n L F0 - 1 ≠ 0 := by
    apply hball
    have hd1 : dist F0 M < eps := by
      rw [Real.dist_eq]
      have habs : |F0 - M| = eps' / 2 := by
        dsimp [F0]
        have h0 : 0 ≤ eps' / 2 := by positivity
        ring_nf
        rw [abs_mul, abs_of_nonneg (le_of_lt heps')]
        norm_num
      rw [habs]
      have hle : eps' / 2 < eps := by
        have h1 : eps' ≤ eps := min_le_left eps M
        nlinarith
      linarith
    exact hd1
  exact ⟨F0, hF0pos, hF0lt, hball0.2.1, hball0.2.2.1, hball0.2.2.2.1, hball0.2.2.2.2.1, hball0.2.2.2.2.2⟩

set_option autoImplicit false

/-! ## The perturbation forces `y = M` at a minimizer -/

lemma yF_at_min (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    yF n L (bval n hn m) = 2 * (bx m n - (n : ℝ)) + (L : ℝ) := by
  let M := bval n hn m
  let X := bx m n
  let yR : ℝ := 2 * (X - (n : ℝ)) + (L : ℝ)
  have hMp : M + 1 ≠ 0 := by
    dsimp [M]
    have hg := one_le_bval_of_mem_D n hn hmD
    linarith
  have hθ : 2 * th n L M - 1 ≠ 0 := by
    have htn := theta_ne_half n hn hmD hmin hL1 hLn hone hLgt
    dsimp [M] at htn
    intro hz
    apply htn
    dsimp [th] at hz ⊢
    nlinarith
  have hxR1 : X = 2 * M - (2 * M - yR) * th n L M := by
    dsimp [M, X, yR]
    exact x_eq_twoM_sub n hn hmD hmin hL1 hLn hone hLgt
  have hy : yR = 2 * (X - (n : ℝ)) + (L : ℝ) := rfl
  have hR4 := R4_real (n : ℝ) M X yR (L : ℝ) (th n L M) hxR1 hy
  have hyrel : yR * (2 * th n L M - 1) = 2 * (n : ℝ) - (L : ℝ) - 4 * M * (1 - th n L M) := by
    nlinarith
  have hytot : yF n L M * (2 * th n L M - 1)
      = 2 * (n : ℝ) - (L : ℝ) - 4 * M * (1 - th n L M) := by
    exact yF_mul n L M hθ
  have heq : yF n L M = yR := by
    have hmul : (yF n L M - yR) * (2 * th n L M - 1) = 0 := by
      nlinarith
    have hz : yF n L M - yR = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hθ
    linarith
  dsimp [M, yR] at heq ⊢
  exact heq

lemma xF_at_min (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    xF n L (bval n hn m) = bx m n := by
  have hy := yF_at_min n hn hmD hmin hL1 hLn hone hLgt
  calc
    xF n L (bval n hn m) = (n : ℝ) + (yF n L (bval n hn m) - (L : ℝ)) / 2 := rfl
    _ = (n : ℝ) + ((2 * (bx m n - (n : ℝ)) + (L : ℝ)) - (L : ℝ)) / 2 := by rw [hy]
    _ = bx m n := by ring

/-- the minimizer satisfies `y = M` -/
lemma minimizer_y_eq_M (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) {L : ℕ} (hL1 : 1 ≤ L) (hLn : L < n)
    (hone : ∀ j, j < L → m j = 1) (hLgt : 1 < m L) :
    2 * (bx m n - (n : ℝ)) + (L : ℝ) = bval n hn m := by
  let M := bval n hn m
  let X := bx m n
  let yR : ℝ := 2 * (X - (n : ℝ)) + (L : ℝ)
  have hMpos : 0 < M := by
    dsimp [M]
    have h := one_le_bval_of_mem_D n hn hmD
    linarith
  have hyF_le : yR ≤ M := by
    dsimp [M, yR]
    exact (y_bounds n hn hmD hmin hL1 hLn hone hLgt).1
  have hM_lt : M < yR + 1 := by
    dsimp [M, yR]
    exact (y_bounds n hn hmD hmin hL1 hLn hone hLgt).2
  have hyF_M : yF n L M = yR := by
    dsimp [M, yR]
    exact yF_at_min n hn hmD hmin hL1 hLn hone hLgt
  have hxF_M : xF n L M = X := by
    dsimp [M, X]
    exact xF_at_min n hn hmD hmin hL1 hLn hone hLgt
  by_cases hyM : yR = M
  · dsimp [yR, M] at hyM ⊢
    exact hyM
  · have hy_lt : yR < M := lt_of_le_of_ne hyF_le hyM
    have hθM : 2 * th n L M - 1 ≠ 0 := by
      have htn := theta_ne_half n hn hmD hmin hL1 hLn hone hLgt
      dsimp [M] at htn
      intro hz
      apply htn
      dsimp [th] at hz ⊢
      nlinarith
    have hA : yF n L M < M := by rw [hyF_M]; exact hy_lt
    have hB : M < yF n L M + 1 := by rw [hyF_M]; linarith [hM_lt]
    have hC : (n : ℝ) < xF n L M := by rw [hxF_M]; exact minimizer_x_gt_n n hn hmD hmin
    have hD : xF n L M < (3 * (n : ℝ) - 1) / 2 := by
      rw [hxF_M]
      exact minimizer_x_lt_upper n hn hmD hmin
    obtain ⟨F, hF0, hFlt, hyl, hyu, hxlo, hxup, hd⟩ :=
      exists_F_good n L M hMpos hθM hA hB hC hD
    have hmem : wF n L F ∈ D n :=
      wF_mem_D n L hn hL1 hLn F hF0 hyl hyu hd hxlo hxup
    have hval : bval n hn (wF n L F) = F :=
      bval_wF_eq_F n L hn hL1 hLn F hF0 hyl hyu hd
    have hleM : M ≤ bval n hn (wF n L F) := by
      dsimp [M]
      exact hmin (wF n L F) hmem
    linarith

set_option autoImplicit false

/-! ## The explicit log lower bound for the minimizer -/

lemma log_theta_eq (M : ℝ) (hM : 0 < M) (s : ℕ) :
    Real.log ((M / (M + 1)) ^ s) = - ((s : ℝ) * Real.log (1 + 1 / M)) := by
  have hMp : M + 1 ≠ 0 := by linarith
  have hMpos1 : 0 < M + 1 := by linarith
  have hdiv : Real.log (M / (M + 1)) = Real.log M - Real.log (M + 1) := by
    exact Real.log_div (ne_of_gt hM) hMp
  have hinv : Real.log (1 + 1 / M) = Real.log (M + 1) - Real.log M := by
    have h : 1 + 1 / M = (M + 1) / M := by
      field_simp [ne_of_gt hM]
    rw [h]
    exact Real.log_div (by linarith : (M + 1) ≠ 0) (ne_of_gt hM)
  rw [Real.log_pow]
  have hlogM1 : (M / (M + 1)) ≠ 0 := by
    intro hz
    have hnum : M ≠ 0 := ne_of_gt hM
    have : M / (M + 1) = 0 := hz
    field_simp [hMp] at this
    linarith
  -- (s : ℝ) * log (M/(M+1)) = -s * log(1+1/M)
  calc
    (s : ℝ) * Real.log (M / (M + 1)) = (s : ℝ) * (Real.log M - Real.log (M + 1)) := by rw [hdiv]
    _ = -((s : ℝ) * (Real.log (M + 1) - Real.log M)) := by ring
    _ = -((s : ℝ) * Real.log (1 + 1 / M)) := by rw [hinv]

/-- the value `M` of a minimizer satisfies `cval·n ≤ M` -/
lemma minimizer_lower_bound (n : ℕ) (hn : 2 ≤ n) {m : ℕ → ℝ} (hmD : m ∈ D n)
    (hmin : ∀ b ∈ D n, bval n hn m ≤ bval n hn b) :
    cval * (n : ℝ) ≤ bval n hn m := by
  rcases minimizer_has_jump_index n hn hmD hmin with ⟨L, hL1, hLn, hone, hLgt⟩
  let M := bval n hn m
  let X := bx m n
  let s := n - L
  let θ : ℝ := th n L M
  have hM0 : 0 < M := by
    dsimp [M]
    have hg := one_le_bval_of_mem_D n hn hmD
    linarith
  have hsℝ : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 0 ≤ n - L)
  have hθpos : 0 < θ := by
    dsimp [θ, th]
    positivity
  have hyM : 2 * (X - (n : ℝ)) + (L : ℝ) = M := by
    dsimp [M, X]
    exact minimizer_y_eq_M n hn hmD hmin hL1 hLn hone hLgt
  -- R4: (3−2θ)M = 2n − L
  have hxR1 : X = 2 * M - (2 * M - (2 * (X - (n : ℝ)) + (L : ℝ))) * θ := by
    dsimp [M, X, θ]
    exact x_eq_twoM_sub n hn hmD hmin hL1 hLn hone hLgt
  have hy : (2 * (X - (n : ℝ)) + (L : ℝ)) = 2 * (X - (n : ℝ)) + (L : ℝ) := rfl
  have hR4 := R4_real (n : ℝ) M X (2 * (X - (n : ℝ)) + (L : ℝ)) (L : ℝ) θ hxR1 hy
  have hR5 : (3 - 2 * θ) * M = 2 * (n : ℝ) - (L : ℝ) := by
    have hyM' : 2 * (X - (n : ℝ)) + (L : ℝ) = M := hyM
    nlinarith
  -- log θ ≥ −s/M · hmm: M·logθ ≥ −(s:ℝ)
  have hlog1 : Real.log θ = - ((s : ℝ) * Real.log (1 + 1 / M)) := by
    dsimp [θ, th]
    exact log_theta_eq M hM0 s
  have hlogM : M * Real.log θ ≥ - (s : ℝ) := by
    have hp : M * Real.log (1 + 1 / M) ≤ 1 :=
      Commons.Analysis.SpecialFunctions.Log.mul_log_one_add_inv_le_one M hM0
    have h2 : (s : ℝ) * (M * Real.log (1 + 1 / M)) ≤ (s : ℝ) := by
      calc
        (s : ℝ) * (M * Real.log (1 + 1 / M)) ≤ (s : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hp hsℝ
        _ = (s : ℝ) := by ring
    have hrew : M * Real.log θ = - ((s : ℝ) * (M * Real.log (1 + 1 / M))) := by
      rw [hlog1]
      ring
    rw [hrew]
    linarith
  have hmain : (3 - 2 * θ + Real.log θ) * M ≥ (n : ℝ) := by
    have hcast : ((n - L : ℕ) : ℝ) = (n : ℝ) - (L : ℝ) := by
      rw [Nat.cast_sub (by omega : L ≤ n)]
    have h1 : (3 - 2 * θ + Real.log θ) * M = (3 - 2 * θ) * M + M * Real.log θ := by ring
    nlinarith
  have hlogb : (3 - 2 * θ + Real.log θ) ≤ 2 - Real.log 2 :=
    Commons.Analysis.SpecialFunctions.Log.three_sub_two_mul_add_log_le θ hθpos
  have hprod : (3 - 2 * θ + Real.log θ) * M ≤ (2 - Real.log 2) * M := by
    exact mul_le_mul_of_nonneg_right hlogb (le_of_lt hM0)
  have hle : (n : ℝ) ≤ (2 - Real.log 2) * M := by nlinarith
  have hpos2 : 0 < 2 - Real.log 2 := two_sub_log_two_pos'
  have hdiv : (n : ℝ) / (2 - Real.log 2) ≤ M := by
    exact (div_le_iff₀ hpos2).mpr (by nlinarith)
  -- cval·n = n/(2−log2)
  have hrew : cval * (n : ℝ) = (n : ℝ) / (2 - Real.log 2) := by
    unfold cval
    field_simp [ne_of_gt hpos2]
  rw [hrew]
  exact hdiv

set_option autoImplicit false

/-! ## The `D`-lower bound for all admissible sequences and the bridge -/

lemma D_lower_bound (n : ℕ) (hn : 2 ≤ n) {b : ℕ → ℝ} (hb : b ∈ D n) :
    cval * (n : ℝ) ≤ bval n hn b := by
  rcases exists_minimizer n hn with ⟨m, hmD, hmin⟩
  have hle : bval n hn m ≤ bval n hn b := hmin b hb
  have hm_bd := minimizer_lower_bound n hn hmD hmin
  linarith

/-! ### Padding an arbitrary admissible sequence into `D` -/

/-- pad `a` (indexed from `2`) to a sequence in `D` by tail-ones -/
noncomputable def pad (a : ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun j => if j < n then a (j + 2) else 1

lemma pad_lt (a : ℕ → ℝ) (n : ℕ) {j : ℕ} (hj : j < n) : pad a n j = a (j + 2) := by
  simp [pad, hj]

lemma pad_ge (a : ℕ → ℝ) (n : ℕ) {j : ℕ} (hj : n ≤ j) : pad a n j = 1 := by
  have hnot : ¬ j < n := by omega
  simp [pad, hnot]

/-- reindexing: sum of `a (j+2)` over `range (m+1)` equals sum of `a i` over `Icc 2 (m+2)` -/
lemma sum_Icc2_add2 (a : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), a (j + 2)) = (∑ i ∈ Finset.Icc 2 (m + 2), a i) := by
  have hs := Finset.sum_Ico_eq_sum_range (fun i => a i) 2 (m + 3)
  -- hs : Σ_{i ∈ Ico 2 (m+3)} a i = Σ_{k ∈ range (m+1)} a (2 + k)
  have harg : m + 3 - 2 = m + 1 := by omega
  rw [harg] at hs
  have hIcc : Finset.Ico 2 (m + 3) = Finset.Icc 2 (m + 2) := by
    have hstep : (m + 2) + 1 = m + 3 := by omega
    rw [← hstep, Finset.Ico_add_one_right_eq_Icc 2 (m + 2)]
  -- LHS of goal: Σ_{j ∈ range(m+1)} a (j+2) — match with hs RHS Σ a(2+k) by reindexing k ↔ j
  calc
    (∑ j ∈ Finset.range (m + 1), a (j + 2)) = (∑ k ∈ Finset.range (m + 1), a (2 + k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      omega
    _ = (∑ i ∈ Finset.Ico 2 (m + 3), a i) := by rw [hs]
    _ = (∑ i ∈ Finset.Icc 2 (m + 2), a i) := by rw [hIcc]

lemma bx_pad_eq (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) :
    bx (pad a n) n = x := by
  unfold bx bpart
  calc
    (∑ j ∈ Finset.range n, pad a n j)
        = (∑ j ∈ Finset.range n, a (j + 2)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : j < n := Finset.mem_range.mp hj
          exact pad_lt a n hj'
    _ = (∑ i ∈ Finset.Icc 2 (n + 1), a i) := by
          -- n = (n-1)+1 case of sum_Icc2_add2
          have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn
          have hs := sum_Icc2_add2 a (n - 1)
          rw [hn'] at hs
          have htop : (n - 1) + 2 = n + 1 := by omega
          rw [htop] at hs
          exact hs
    _ = x := hx

/-- membership of the padded sequence -/
lemma pad_mem_D (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (a : ℕ → ℝ)
    (ha2 : a 2 = 1)
    (hmono : ∀ i : ℕ, i ∈ Finset.Icc 2 n → a i ≤ a (i + 1))
    (hsum : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x)
    (ha1 : ∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → (1 : ℝ) ≤ a i)
    (hxlo : (n : ℝ) ≤ x) (hxup : x ≤ ((3 * (n : ℝ) - 1) / 2)) :
    pad a n ∈ D n := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- b 0 = 1
      rw [pad_lt a n (by omega : (0 : ℕ) < n)]
      exact ha2
    · intro j hj
      rw [pad_lt a n hj]
      exact ha1 (j + 2) (by
        rw [Finset.mem_Icc]
        constructor <;> omega)
    · intro j hj1
      have hj2 : j + 2 ∈ Finset.Icc 2 n := by
        rw [Finset.mem_Icc]
        constructor <;> omega
      rw [pad_lt a n (by omega : j < n), pad_lt a n (by omega : j + 1 < n)]
      exact hmono (j + 2) hj2
    · -- n ≤ bx
      rw [bx_pad_eq a n (by omega : 1 ≤ n) x hsum]
      exact hxlo
  · rw [bx_pad_eq a n (by omega : 1 ≤ n) x hsum]
    exact hxup
  · intro j hj
    exact pad_ge a n hj

/-! ### The value of the padded sequence equals the paper maximum -/

/-- paper ratio (target form) -/
noncomputable def pratio (n : ℕ) (x : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (2 * x - 2 * ((n : ℝ) - (k : ℝ) + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k

/-- `brat` on the padded sequence equals the paper ratio at `m+2` -/
lemma brat_pad (n : ℕ) (x : ℝ) (a : ℕ → ℝ) {m : ℕ} (hm : m < n) :
    brat n x (pad a n) m = pratio n x a (m + 2) := by
  unfold brat pratio
  have hb : pad a n m = a (m + 2) := pad_lt a n hm
  have hbpart : bpart (pad a n) (m + 1) = (∑ i ∈ Finset.Icc 2 (m + 2), a i) := by
    unfold bpart
    calc
      (∑ j ∈ Finset.range (m + 1), pad a n j) = (∑ j ∈ Finset.range (m + 1), a (j + 2)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < m + 1 := Finset.mem_range.mp hj
        exact pad_lt a n (by omega : j < n)
      _ = (∑ i ∈ Finset.Icc 2 (m + 2), a i) := sum_Icc2_add2 a m
  rw [hb, hbpart]
  congr 2
  congr 1
  -- 2·((n:ℝ) − 1 − (m:ℝ)) = 2·((n:ℝ) − (m+2:ℝ) + 1)
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by norm_num
  rw [hcast]
  ring


lemma pratio_eq (n k : ℕ) (x : ℝ) (a : ℕ → ℝ) :
    pratio n x a k = (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k := by
  unfold pratio
  rfl

lemma bval_pad_le_rawsup (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (a : ℕ → ℝ)
    (hsum : (∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) :
    bval n hn (pad a n)
      ≤ (Finset.Icc 2 (n + 1)).sup' (show (Finset.Icc 2 (n + 1)).Nonempty by
          refine ⟨2, ?_⟩
          rw [Finset.mem_Icc]
          constructor <;> omega)
          (fun k => (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) := by
  have hbx : bx (pad a n) n = x := bx_pad_eq a n (by omega : 1 ≤ n) x hsum
  rw [bval, hbx]
  rw [bF_le_iff]
  intro m hm
  have hm' : m < n := Finset.mem_range.mp hm
  have heq : brat n x (pad a n) m = pratio n x a (m + 2) := brat_pad n x a hm'
  rw [heq, pratio_eq]
  apply Finset.le_sup' (fun k => (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k)
  rw [Finset.mem_Icc]
  constructor <;> omega

set_option autoImplicit false

theorem poels_opt_lower (n : ℕ) (hn : 2 ≤ n) :
    ∀ x : ℝ, n ≤ x → ∀ a : ℕ → ℝ,
      (a 2 = 1 ∧
       (∀ i : ℕ, i ∈ Finset.Icc 2 n → a i ≤ a (i + 1)) ∧
       ((∑ i ∈ Finset.Icc 2 (n + 1), a i) = x) ∧
       (∀ i : ℕ, i ∈ Finset.Icc 2 (n + 1) → 1 ≤ a i)) →
      (1 / (2 - Real.log 2)) * n ≤
        (if h : (Finset.Icc 2 (n + 1)).Nonempty then
           (Finset.Icc 2 (n + 1)).sup' h (fun k =>
             (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k)
         else 0) := by
  intro x hx a ha
  rcases ha with ⟨ha2, hmono, hsum, ha1⟩
  have hne : (Finset.Icc 2 (n + 1)).Nonempty := ⟨2, by
    rw [Finset.mem_Icc]
    constructor <;> omega⟩
  rw [dif_pos hne]
  by_cases hbig : ((3 * (n : ℝ) - 1) / 2) ≤ x
  · -- case x large: ratio at index 2 already ≥ n
    have hmem2 : 2 ∈ Finset.Icc 2 (n + 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hsup2 : (2 * x - 2 * (n - 2 + 1) - (∑ i ∈ Finset.Icc 2 2, a i)) / a 2
        ≤ (Finset.Icc 2 (n + 1)).sup' hne (fun k =>
            (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) :=
      Finset.le_sup' (fun k : ℕ =>
        (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) hmem2
    have hsum2 : (∑ i ∈ Finset.Icc 2 2, a i) = a 2 := by
      simp
    have hcast : (2 : ℝ) * (n - 2 + 1) = 2 * ((n : ℝ) - 1) := by ring
    have hge : (n : ℝ) ≤ 2 * (x - (n : ℝ)) + 1 := by nlinarith [hbig]
    have hraw2 : (n : ℝ) ≤ (2 * x - 2 * (n - 2 + 1) - (∑ i ∈ Finset.Icc 2 2, a i)) / a 2 := by
      rw [hsum2, ha2, hcast]
      have hnum : 2 * x - 2 * ((n : ℝ) - 1) - 1 = 2 * (x - (n : ℝ)) + 1 := by ring
      rw [hnum]
      norm_num
      exact hge
    have hle1 : cval * (n : ℝ) ≤ (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 0 ≤ n)
      exact mul_le_of_le_one_left hn0 cval_le_one
    have hfin : cval * (n : ℝ)
        ≤ (Finset.Icc 2 (n + 1)).sup' hne (fun k =>
            (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) := by
      linarith
    simpa [cval] using hfin
  · -- case x < (3n−1)/2 : pad and use the D-minimizer bound
    have hxup : x ≤ ((3 * (n : ℝ) - 1) / 2) := le_of_not_ge hbig
    have hbD : pad a n ∈ D n := pad_mem_D n hn x a ha2 hmono hsum ha1 hx hxup
    have hlow : cval * (n : ℝ) ≤ bval n hn (pad a n) := D_lower_bound n hn hbD
    have hleS : bval n hn (pad a n)
        ≤ (Finset.Icc 2 (n + 1)).sup' hne (fun k =>
            (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) := by
      simpa using bval_pad_le_rawsup n hn x a hsum
    have hfin : cval * (n : ℝ)
        ≤ (Finset.Icc 2 (n + 1)).sup' hne (fun k =>
            (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k) := by
      linarith
    simpa [cval] using hfin


