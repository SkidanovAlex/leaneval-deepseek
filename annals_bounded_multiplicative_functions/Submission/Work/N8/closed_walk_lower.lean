import Mathlib
import Submission.Work.N8.closed_walk_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace Work.N8

variable {V : Type} [Fintype V] [DecidableEq V]

lemma dotProduct_sq_le (u v : V → ℝ) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have h1 : (∑ i ∈ Finset.univ, u i * v i) = u ⬝ᵥ v := rfl
  have h2 : (∑ i ∈ Finset.univ, u i ^ 2) = u ⬝ᵥ u := by
    rw [show u ⬝ᵥ u = ∑ i, u i * u i from rfl]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : (∑ i ∈ Finset.univ, v i ^ 2) = v ⬝ᵥ v := by
    rw [show v ⬝ᵥ v = ∑ i, v i * v i from rfl]
    exact Finset.sum_congr rfl fun i _ => by ring
  rwa [h1, h2, h3] at h

lemma symm_dotProduct_mulVec {A : Matrix V V ℝ} (hA : A.IsSymm) (u v : V → ℝ) :
    (A.mulVec u) ⬝ᵥ v = u ⬝ᵥ (A.mulVec v) := by
  rw [Matrix.dotProduct_mulVec]
  congr 1
  rw [← Matrix.vecMul_transpose, hA.eq]

theorem logconvex_lower (a : ℕ → ℝ) (h0 : a 0 = 1) (hpos : ∀ k, 0 ≤ a k)
    (hconv : ∀ k, 1 ≤ k → (a k) ^ 2 ≤ a (k - 1) * a (k + 1)) :
    ∀ k, (a 1) ^ k ≤ a k := by
  rcases eq_or_lt_of_le (hpos 1) with h1 | h1
  · intro k
    rcases k with _ | k
    · rw [← h1, pow_zero, h0]
    · rw [← h1]
      have hz : (0 : ℝ) ^ (k + 1) = 0 := zero_pow (Nat.succ_ne_zero k)
      rw [hz]
      exact hpos _
  · have hc : 0 < a 1 := h1
    have hpos_strong : ∀ k, 0 < a k := fun k =>
      Nat.strong_induction_on k (fun k ih => by
        rcases k with _ | _ | n
        · rw [h0]; norm_num
        · exact hc
        · have hh : (a (n + 1)) ^ 2 ≤ a n * a (n + 2) := by
            have h := hconv (n + 1) (by omega)
            have e1 : (n + 1) - 1 = n := by omega
            have e2 : (n + 1) + 1 = n + 2 := by omega
            rw [e1, e2] at h
            exact h
          have hn : 0 < a n := ih n (by omega)
          have hn1 : 0 < a (n + 1) := ih (n + 1) (by omega)
          have hmul : 0 < a n * a (n + 2) := lt_of_lt_of_le (pow_pos hn1 2) hh
          exact pos_of_mul_pos_right hmul (le_of_lt hn))
    set b : ℕ → ℝ := fun k => a k / (a 1) ^ k with hb
    have hb0 : b 0 = 1 := by simp [hb, h0]
    have hb1 : b 1 = 1 := by
      simp only [hb, pow_one]
      exact div_self (ne_of_gt hc)
    have hbc : ∀ k, 1 ≤ k → (b k) ^ 2 ≤ b (k - 1) * b (k + 1) := by
      intro k hk
      have hck : (a 1) ^ (k - 1) * (a 1) ^ (k + 1) = ((a 1) ^ k) ^ 2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      simp only [hb, div_pow, div_mul_div_comm, hck]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right (hconv k hk) (by positivity)
    have key : ∀ k, 1 ≤ b k ∧ b k ≤ b (k + 1) := by
      intro k
      induction k with
      | zero => constructor <;> simp [hb0, hb1]
      | succ k ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hbk : 0 < b k := lt_of_lt_of_le zero_lt_one ih1
        have hbkp : 0 < b (k + 1) := lt_of_lt_of_le zero_lt_one (le_trans ih1 ih2)
        have hstep : (b (k + 1)) ^ 2 / b k ≤ b (k + 2) := by
          rw [div_le_iff₀ hbk]
          have hh : (b (k + 1)) ^ 2 ≤ b k * b (k + 2) := by
            have h := hbc (k + 1) (by omega)
            have e1 : (k + 1) - 1 = k := by omega
            have e2 : (k + 1) + 1 = k + 2 := by omega
            rw [e1, e2] at h
            exact h
          nlinarith [hh]
        constructor
        · exact le_trans ih1 ih2
        · calc b (k + 1) = (b (k + 1)) ^ 2 / b (k + 1) := by
                rw [eq_div_iff (ne_of_gt hbkp), pow_two]
            _ ≤ (b (k + 1)) ^ 2 / b k := div_le_div_of_nonneg_left (by positivity) hbk ih2
            _ ≤ b (k + 2) := hstep
    intro k
    calc (a 1) ^ k = 1 * (a 1) ^ k := by rw [one_mul]
      _ ≤ b k * (a 1) ^ k := mul_le_mul_of_nonneg_right (key k).1 (by positivity)
      _ = a k := by
          rw [hb]
          exact div_mul_cancel₀ _ (pow_ne_zero k (ne_of_gt hc))

theorem spectral_chain (A : Matrix V V ℝ) (hA : A.IsSymm) (x : V → ℝ)
    (hx : x ⬝ᵥ x = 1) (m : ℕ) :
    (x ⬝ᵥ (A.mulVec x)) ^ (2 * m) ≤ (A ^ (2 * m)).trace := by
  let y : ℕ → V → ℝ := fun k => (A ^ k).mulVec x
  let a : ℕ → ℝ := fun k => y k ⬝ᵥ y k
  have y_succ : ∀ k, y (k+1) = A.mulVec (y k) := by
    intro k
    show (A ^ (k+1)).mulVec x = A.mulVec ((A ^ k).mulVec x)
    rw [pow_succ', Matrix.mulVec_mulVec]
  have ha0 : a 0 = 1 := by
    show y 0 ⬝ᵥ y 0 = 1
    have hy0 : y 0 = x := by
      show (A ^ 0).mulVec x = x
      rw [pow_zero, Matrix.one_mulVec]
    rw [hy0, hx]
  have hapos : ∀ k, 0 ≤ a k := by
    intro k
    have h1 : a k = ∑ i, y k i * y k i := rfl
    rw [h1]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hconv : ∀ k, 1 ≤ k → (a k) ^ 2 ≤ a (k - 1) * a (k + 1) := by
    intro k hk
    have hyk : y k = A.mulVec (y (k-1)) := by
      rw [show k = (k-1)+1 from (Nat.sub_add_cancel hk).symm]
      exact y_succ (k-1)
    have hmid : y (k-1) ⬝ᵥ y (k+1) = a k := by
      rw [y_succ k, ← symm_dotProduct_mulVec hA (y (k-1)) (y k), ← hyk]
    calc (a k) ^ 2 = (y (k-1) ⬝ᵥ y (k+1)) ^ 2 := by rw [hmid]
      _ ≤ (y (k-1) ⬝ᵥ y (k-1)) * (y (k+1) ⬝ᵥ y (k+1)) := dotProduct_sq_le _ _
      _ = a (k-1) * a (k+1) := rfl
  have ha1 : a 1 = x ⬝ᵥ ((A * A).mulVec x) := by
    show y 1 ⬝ᵥ y 1 = x ⬝ᵥ ((A * A).mulVec x)
    have hy1 : y 1 = A.mulVec x := by
      show (A ^ 1).mulVec x = A.mulVec x
      rw [pow_one]
    rw [hy1, symm_dotProduct_mulVec hA x (A.mulVec x), Matrix.mulVec_mulVec]
  have hbase : (x ⬝ᵥ (A.mulVec x)) ^ 2 ≤ x ⬝ᵥ ((A * A).mulVec x) := by
    have h := dotProduct_sq_le x (A.mulVec x)
    rw [hx, one_mul] at h
    rwa [symm_dotProduct_mulVec hA x (A.mulVec x), Matrix.mulVec_mulVec] at h
  have hlog : (x ⬝ᵥ ((A * A).mulVec x)) ^ m ≤ a m := by
    have h := logconvex_lower a ha0 hapos hconv m
    rwa [ha1] at h
  have hbound : a m ≤ (A ^ (2 * m)).trace := by
    have hsymm : (A ^ m).IsSymm := hA.pow m
    have htrace : (A ^ (2 * m)).trace = ∑ i, ∑ j, ((A ^ m) i j) ^ 2 := by
      simp only [Matrix.trace, Matrix.diag]
      rw [show (A : Matrix V V ℝ) ^ (2*m) = A ^ m * A ^ m from by
            rw [show 2 * m = m * 2 from by omega, pow_mul, pow_two]]
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm.apply j i]; ring
    rw [htrace]
    have ham : a m = ∑ i, (y m i) ^ 2 := by
      have h1 : a m = ∑ i, y m i * y m i := rfl
      rw [h1]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [ham]
    refine Finset.sum_le_sum fun i _ => ?_
    have hy : y m i = ∑ j, (A ^ m) i j * x j := rfl
    rw [hy]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => (A ^ m) i j) x
    have hx2 : (∑ j, (x j) ^ 2) = 1 := by
      have h2 : x ⬝ᵥ x = ∑ j, x j * x j := rfl
      rw [← hx, h2]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hx2, mul_one] at hcs
    exact hcs
  calc (x ⬝ᵥ (A.mulVec x)) ^ (2 * m) = ((x ⬝ᵥ (A.mulVec x)) ^ 2) ^ m := by rw [pow_mul]
    _ ≤ (x ⬝ᵥ ((A * A).mulVec x)) ^ m := pow_le_pow_left₀ (sq_nonneg _) hbase m
    _ ≤ a m := hlog
    _ ≤ (A ^ (2 * m)).trace := hbound

lemma dotProduct_const_const (c : ℝ) :
    (fun _ : V => c) ⬝ᵥ (fun _ : V => c) = (Fintype.card V : ℝ) * c ^ 2 := by
  change (∑ _ : V, c * c) = (Fintype.card V : ℝ) * c ^ 2
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma dotProduct_const_mulVec (A : Matrix V V ℝ) (c : ℝ) :
    (fun _ : V => c) ⬝ᵥ (A.mulVec (fun _ : V => c)) = c ^ 2 * (∑ i, ∑ j, A i j) := by
  change (∑ i : V, c * (∑ j : V, A i j * c)) = c ^ 2 * (∑ i, ∑ j, A i j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

theorem trace_lower_bound (A : Matrix V V ℝ) (hA : A.IsSymm) (m : ℕ) (hm : 1 ≤ m) :
    ((∑ i, ∑ j, A i j) / (Fintype.card V : ℝ)) ^ (2 * m) ≤ (A ^ (2 * m)).trace := by
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have hsum : (∑ i, ∑ j, A i j) = 0 := by simp
    have htr : (A ^ (2 * m)).trace = 0 := by simp [Matrix.trace]
    rw [hsum, htr, hV, Nat.cast_zero, zero_div,
      zero_pow (by omega : 2 * m ≠ 0)]
  · have hcard : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
    have hN : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hcard
    let x : V → ℝ := fun _ => 1 / Real.sqrt (Fintype.card V)
    have hsq : (1 / Real.sqrt (Fintype.card V)) ^ 2 = 1 / (Fintype.card V : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hN)]
    have hxx : x ⬝ᵥ x = 1 := by
      rw [show x = (fun _ : V => 1 / Real.sqrt (Fintype.card V)) from rfl]
      rw [dotProduct_const_const, hsq, mul_one_div, div_self (ne_of_gt hN)]
    have hxAx : x ⬝ᵥ (A.mulVec x) = (∑ i, ∑ j, A i j) / (Fintype.card V : ℝ) := by
      rw [show x = (fun _ : V => 1 / Real.sqrt (Fintype.card V)) from rfl]
      rw [dotProduct_const_mulVec, hsq, div_mul_eq_mul_div, one_mul]
    have hspec := spectral_chain A hA x hxx m
    rwa [hxAx] at hspec

abbrev IsWalk (Adj : V → V → Prop) {k : ℕ} (f : Fin (k+1) → V) : Prop :=
  ∀ t : Fin k, Adj (f t.castSucc) (f t.succ)

def walkSet (Adj : V → V → Prop) [DecidableRel Adj] (k : ℕ) (i j : V) :
    Finset (Fin (k+1) → V) :=
  Finset.univ.filter (fun f => f 0 = i ∧ f (Fin.last k) = j ∧ IsWalk Adj f)

lemma mem_walkSet {Adj : V → V → Prop} [DecidableRel Adj] {k : ℕ} {i j : V}
    {f : Fin (k+1) → V} :
    f ∈ walkSet Adj k i j ↔ f 0 = i ∧ f (Fin.last k) = j ∧ IsWalk Adj f := by
  simp [walkSet]

lemma castSucc_zero (k : ℕ) : Fin.castSucc (0 : Fin (k+1)) = (0 : Fin (k+2)) :=
  Fin.ext (by simp)

theorem walkSet_succ_card (Adj : V → V → Prop) [DecidableRel Adj] (k : ℕ) (i j : V) :
    (walkSet Adj (k+1) i j).card
      = ∑ u ∈ Finset.univ.filter (fun u : V => Adj i u), (walkSet Adj k u j).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij'
    (fun f _ => ⟨f (Fin.succ 0), fun t => f (Fin.succ t)⟩)
    (fun b _ => Fin.cases (motive := fun _ => V) i (fun t => b.2 t)) ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_walkSet] at hf
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h := hf.2.2 (0 : Fin (k+1))
      rw [castSucc_zero k, hf.1] at h
      exact h
    · rw [mem_walkSet]
      refine ⟨rfl, ?_, ?_⟩
      · show f (Fin.succ (Fin.last k)) = j
        rw [Fin.succ_last]
        exact hf.2.1
      · intro t
        show Adj (f (Fin.succ (Fin.castSucc t))) (f (Fin.succ (Fin.succ t)))
        have h := hf.2.2 (Fin.succ t)
        rw [← Fin.succ_castSucc] at h
        exact h
  · intro b hb
    rw [Finset.mem_sigma] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [Finset.mem_filter] at hb1
    obtain ⟨-, hb1⟩ := hb1
    rw [mem_walkSet] at hb2
    rw [mem_walkSet]
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.cases_zero]
    · rw [show Fin.last (k+1) = Fin.succ (Fin.last k) from (Fin.succ_last k).symm,
          Fin.cases_succ, hb2.2.1]
    · intro t
      refine Fin.cases ?_ (fun s => ?_) t
      · simp only [castSucc_zero k, Fin.cases_zero, Fin.cases_succ, hb2.1]
        exact hb1
      · simp only [Fin.cases_succ]
        exact hb2.2.2 s
  · intro f hf
    rw [mem_walkSet] at hf
    funext m
    refine Fin.cases ?_ (fun t => ?_) m
    · rw [Fin.cases_zero]; exact hf.1.symm
    · rw [Fin.cases_succ]
  · rintro ⟨u, g⟩ hb
    rw [Finset.mem_sigma] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [Finset.mem_filter] at hb1
    obtain ⟨-, hb1⟩ := hb1
    rw [mem_walkSet] at hb2
    have key0 : (Fin.cases (motive := fun _ => V) i (fun t => g t)) (Fin.succ (0 : Fin (k+1))) = u := by
      rw [Fin.cases_succ]
      exact hb2.1
    have key1 : (fun t : Fin (k+1) => (Fin.cases (motive := fun _ => V) i (fun t => g t)) (Fin.succ t)) = g := by
      funext t; rw [Fin.cases_succ]
    show (⟨(Fin.cases (motive := fun _ => V) i (fun t => g t)) (Fin.succ (0 : Fin (k+1))),
        (fun t : Fin (k+1) => (Fin.cases (motive := fun _ => V) i (fun t => g t)) (Fin.succ t))⟩ :
        Sigma (fun _ : V => Fin (k+1) → V)) = ⟨u, g⟩
    rw [key0, key1]

theorem walk_count (Adj : V → V → Prop) [DecidableRel Adj] (k : ℕ) (i j : V) :
    (AdjMat Adj ^ k) i j = ((walkSet Adj k i j).card : ℝ) := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      have hset : walkSet Adj 0 i i = {fun _ : Fin 1 => i} := by
        ext f
        rw [Finset.mem_singleton, mem_walkSet]
        constructor
        · rintro ⟨h0, -, -⟩
          funext m
          rw [Fin.eq_zero m]
          simpa using h0
        · rintro rfl
          exact ⟨rfl, rfl, fun t => Fin.elim0 t⟩
      rw [hset, Finset.card_singleton, if_pos rfl]
      norm_num
    · have hset : walkSet Adj 0 i j = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨f, hf⟩
        rw [mem_walkSet] at hf
        exact h (hf.1.symm.trans hf.2.1)
      rw [hset, Finset.card_empty, if_neg h]
      norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    have h1 : ∀ u : V, AdjMat Adj i u * (AdjMat Adj ^ k) u j
        = (if Adj i u then ((walkSet Adj k u j).card : ℝ) else 0) := by
      intro u
      rw [AdjMat_apply, ih u j]
      split <;> ring
    simp only [h1]
    rw [← Finset.sum_filter, walkSet_succ_card, Nat.cast_sum]

theorem cycle_count (Adj : V → V → Prop) [DecidableRel Adj] (N : ℕ) (hN : 0 < N) :
    (Finset.univ.filter (fun v : Fin N → V =>
        ∀ j : Fin N, Adj (v j) (v ⟨((j : ℕ) + 1) % N, Nat.mod_lt _ hN⟩))).card
      = ∑ i : V, (walkSet Adj N i i).card := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  have hcast (s : Fin N) :
      (⟨(Fin.castSucc s).val % N, Nat.mod_lt _ hN⟩ : Fin N) = s :=
    Fin.ext (by simp [Fin.val_castSucc, Nat.mod_eq_of_lt s.isLt])
  rw [← Finset.card_sigma]
  refine Finset.card_bij'
    (fun v _ => ⟨v 0, fun t : Fin (N+1) => v ⟨t.val % N, Nat.mod_lt _ hN⟩⟩)
    (fun b _ => fun t : Fin N => b.2 ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨-, hv⟩ := hv
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mem_walkSet]
    refine ⟨?_, ?_, ?_⟩
    · show v ⟨(0 : Fin (N+1)).val % N, Nat.mod_lt _ hN⟩ = v 0
      exact congrArg v (Fin.ext (by simp))
    · show v ⟨(Fin.last N).val % N, Nat.mod_lt _ hN⟩ = v 0
      exact congrArg v (Fin.ext (by simp))
    · intro s
      have e1 : (fun t : Fin (N+1) => v ⟨t.val % N, Nat.mod_lt _ hN⟩) (Fin.castSucc s) = v s :=
        congrArg v (hcast s)
      have e2 : (fun t : Fin (N+1) => v ⟨t.val % N, Nat.mod_lt _ hN⟩) (Fin.succ s)
              = v ⟨(s.val + 1) % N, Nat.mod_lt _ hN⟩ :=
        congrArg v (Fin.ext (by simp [Fin.val_succ]))
      show Adj ((fun t : Fin (N+1) => v ⟨t.val % N, Nat.mod_lt _ hN⟩) (Fin.castSucc s))
               ((fun t : Fin (N+1) => v ⟨t.val % N, Nat.mod_lt _ hN⟩) (Fin.succ s))
      rw [e1, e2]
      exact hv s
  · intro b hb
    rw [Finset.mem_sigma] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [mem_walkSet] at hb2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t
    show Adj (b.2 ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩)
             (b.2 ⟨(t.val + 1) % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩)
    have e1 : (⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ : Fin (N+1)) = Fin.castSucc t :=
      Fin.ext (by simp [Fin.val_castSucc])
    have e2 : b.2 (Fin.succ t)
            = b.2 ⟨(t.val + 1) % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt t.isLt) with h | h
      · rw [Nat.succ_eq_add_one] at h
        exact congrArg b.2 (Fin.ext (by simp [Fin.val_succ, Nat.mod_eq_of_lt h]))
      · rw [Nat.succ_eq_add_one] at h
        have hs : (Fin.succ t : Fin (N+1)) = Fin.last N := Fin.ext (by simp [Fin.val_succ, h])
        have h0 : (⟨(t.val + 1) % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N+1)) = 0 := by
          apply Fin.ext; simp [h]
        rw [hs, h0, hb2.2.1, hb2.1]
    rw [e1, ← e2]
    exact hb2.2.2 t
  · intro a ha
    funext t
    show a ⟨t.val % N, Nat.mod_lt _ hN⟩ = a t
    exact congrArg a (Fin.ext (by simp [Nat.mod_eq_of_lt t.isLt]))
  · rintro ⟨i, f⟩ hb
    rw [Finset.mem_sigma] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [mem_walkSet] at hb2
    refine Sigma.ext ?_ ?_
    · show f (0 : Fin (N+1)) = i
      exact hb2.1
    · rw [heq_eq_eq]
      funext s
      show f ⟨s.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ = f s
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp s.isLt) with h | h
      · exact congrArg f (Fin.ext (by simp [Nat.mod_eq_of_lt h]))
      · have hs : (⟨s.val, s.isLt⟩ : Fin (N+1)) = Fin.last N := Fin.ext h
        have h0 : (⟨s.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N+1)) = 0 := by
          apply Fin.ext; simp [h]
        rw [h0, show s = (⟨s.val, s.isLt⟩ : Fin (N+1)) from rfl, hs]
        exact hb2.1.trans hb2.2.1.symm

/-- **Main lemma**: the number of closed walks of even length `2m` in a graph dominates the
`2m`-th power of the average degree. -/
theorem closed_walk_lower {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj] (hsym : ∀ a b, Adj a b ↔ Adj b a)
    (m : ℕ) (hm : 1 ≤ m) :
    (((Finset.univ.filter (fun p : V × V ↦ Adj p.1 p.2)).card : ℝ) / (Fintype.card V : ℝ)) ^ (2 * m)
      ≤ ((Finset.univ.filter (fun v : Fin (2 * m) → V ↦ ∀ j : Fin (2 * m),
            Adj (v j) (v ⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩))).card : ℝ)
:= by
  have hcount :
      ((Finset.univ.filter (fun v : Fin (2 * m) → V => ∀ j : Fin (2 * m),
          Adj (v j) (v ⟨((j : ℕ) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩))).card : ℝ)
        = (AdjMat Adj ^ (2 * m)).trace := by
    rw [cycle_count Adj (2 * m) (by omega)]
    simp only [Nat.cast_sum, Matrix.trace, Matrix.diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [walk_count Adj (2 * m) i i]
  rw [hcount, ← edges_eq_sum]
  exact trace_lower_bound (AdjMat Adj) (AdjMat_isSymm Adj hsym) m hm

end Work.N8
