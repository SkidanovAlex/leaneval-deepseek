import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.HalesJewett

open Combinatorics

namespace Commons.Combinatorics.Ramsey

/-- Composition of combinatorial subspaces: `subspaceComp S T` is the subspace obtained by
first applying `T` and then `S`. -/
def subspaceComp {η η' α ι : Type*} (S : Combinatorics.Subspace η α ι)
    (T : Combinatorics.Subspace η' α η) : Combinatorics.Subspace η' α ι where
  idxFun i := (S.idxFun i).elim (fun a => Sum.inl a) T.idxFun
  proper e := by
    obtain ⟨e', he'⟩ := T.proper e
    obtain ⟨i, hi⟩ := S.proper e'
    exact ⟨i, by rw [hi]; exact he'⟩

@[simp] lemma subspaceComp_apply {η η' α ι : Type*} (S : Combinatorics.Subspace η α ι)
    (T : Combinatorics.Subspace η' α η) (x : η' → α) : subspaceComp S T x = S (T x) := by
  funext i
  cases h : S.idxFun i <;> simp [subspaceComp, h, Subspace.coe_apply]

/-- Given a subspace `S` and a line `l` in the domain of `S`, the composite `subspaceCompLine S l`
is a line in the ambient cube. -/
def subspaceCompLine {η α ι : Type*} (S : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) : Combinatorics.Line α ι where
  idxFun i := (S.idxFun i).elim (fun a => some a) l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := S.proper e
    exact ⟨i, by rw [hi]; exact he⟩

@[simp] lemma subspaceCompLine_apply {η α ι : Type*} (S : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) (x : α) : subspaceCompLine S l x = S (l x) := by
  funext i
  cases h : S.idxFun i <;> simp [subspaceCompLine, h, Line.apply_def, Subspace.coe_apply]

theorem dkt_dhj_of_increment (k : ℕ) (hk : 1 ≤ k)
    (hinc : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∀ d0 : ℕ, 1 ≤ d0 → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ d : ℝ, δ ≤ d → d ≤ 1 → ∀ T : Finset (Fin n → Fin k),
        d * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T) ∨
        ∃ S : Combinatorics.Subspace (Fin d0) (Fin k) (Fin n),
          (1 + c) * d * (k : ℝ) ^ d0
            ≤ ((Finset.univ : Finset (Fin d0 → Fin k)).filter (fun x => S x ∈ T)).card) :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T := by
  classical
  intro δ hδ0
  -- Cardinality of a subset of `[k]^m` is at most `k^m`.
  have hcard_le : ∀ {m : ℕ} (U : Finset (Fin m → Fin k)), (U.card : ℝ) ≤ (k : ℝ) ^ m := by
    intro m U
    have h1 : U.card ≤ Fintype.card (Fin m → Fin k) := Finset.card_le_univ U
    have h2 : Fintype.card (Fin m → Fin k) = k ^ m := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    calc (U.card : ℝ) ≤ (Fintype.card (Fin m → Fin k) : ℝ) := by exact_mod_cast h1
      _ = ((k ^ m : ℕ) : ℝ) := by rw [h2]
      _ = (k : ℝ) ^ m := by push_cast; ring
  by_cases hδ1 : δ ≤ 1
  · obtain ⟨c, hcpos, hc⟩ := hinc δ hδ0 hδ1
    have h1c : (1 : ℝ) < 1 + c := by linarith
    -- A bound `L` with `(1+c)^L * δ > 1`.
    have hex : ∃ L : ℕ, 1 < (1 + c) ^ L * δ := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt δ⁻¹ h1c
      refine ⟨n, ?_⟩
      have h := mul_lt_mul_of_pos_left hn hδ0
      rw [mul_inv_cancel₀ (ne_of_gt hδ0)] at h
      rw [mul_comm δ ((1 + c) ^ n)] at h
      exact h
    let L := Nat.find hex
    have hL : 1 < (1 + c) ^ L * δ := Nat.find_spec hex
    have hLmin : ∀ j, j < L → (1 + c) ^ j * δ ≤ 1 := fun j hj =>
      not_lt.mp (Nat.find_min hex hj)
    -- `N d` is the dimension threshold supplied by the increment hypothesis at target `d`.
    let N : ℕ → ℕ := fun d => if hd : 1 ≤ d then (hc d hd).choose else 0
    -- Core induction: for a dimension threshold function `M` satisfying the recursion
    -- `M (i+1) = max (M i) (N (M i))`, a line-free set of dimension `m ≥ M j` is *strictly*
    -- below the target density `(1+c)^(L-j) * δ`.
    have key_aux : ∀ (M : ℕ → ℕ), M 0 = 1 →
        (∀ i, M (i + 1) = max (M i) (N (M i))) →
        ∀ j : ℕ, j ≤ L → ∀ m : ℕ, M j ≤ m →
        ∀ U : Finset (Fin m → Fin k),
        (¬ ∃ l : Combinatorics.Line (Fin k) (Fin m), ∀ x : Fin k, l x ∈ U) →
        (U.card : ℝ) < (1 + c) ^ (L - j) * δ * (k : ℝ) ^ m := by
      intro M hM0 hMs
      have hMpos : ∀ i, 1 ≤ M i := by
        intro i
        induction i with
        | zero => rw [hM0]
        | succ i ih => rw [hMs i]; exact le_trans ih (le_max_left _ _)
      intro j
      induction j with
      | zero =>
        intro _ m hm U hU
        rw [Nat.sub_zero]
        have hkpos : (0 : ℝ) < (k : ℝ) ^ m := pow_pos (by exact_mod_cast hk) m
        calc (U.card : ℝ) ≤ (k : ℝ) ^ m := hcard_le U
          _ = 1 * (k : ℝ) ^ m := by ring
          _ < ((1 + c) ^ L * δ) * (k : ℝ) ^ m := mul_lt_mul_of_pos_right hL hkpos
      | succ j ih =>
        intro hj1 m hm U hU
        by_contra hcon
        rw [not_lt] at hcon
        have hdδ : δ ≤ (1 + c) ^ (L - (j + 1)) * δ := by
          have h1 : (1 : ℝ) ≤ (1 + c) ^ (L - (j + 1)) :=
            one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + c)
          have := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ0)
          rwa [one_mul] at this
        have hd1 : (1 + c) ^ (L - (j + 1)) * δ ≤ 1 :=
          hLmin (L - (j + 1)) (by omega)
        have hmN : N (M j) ≤ m := by
          have h1 : N (M j) ≤ M (j + 1) := by rw [hMs j]; exact le_max_right _ _
          exact le_trans h1 hm
        have hNval : N (M j) = (hc (M j) (hMpos j)).choose := by
          show (if hd : 1 ≤ M j then (hc (M j) hd).choose else 0)
            = (hc (M j) (hMpos j)).choose
          exact dif_pos (hMpos j)
        have hres := (hc (M j) (hMpos j)).choose_spec m (by rw [← hNval]; exact hmN)
            ((1 + c) ^ (L - (j + 1)) * δ) hdδ hd1 U hcon
        rcases hres with ⟨l, hl⟩ | ⟨S, hS⟩
        · exact hU ⟨l, hl⟩
        · let U' : Finset (Fin (M j) → Fin k) :=
            (Finset.univ : Finset (Fin (M j) → Fin k)).filter (fun x => S x ∈ U)
          have hU'def : U' = (Finset.univ : Finset (Fin (M j) → Fin k)).filter
              (fun x => S x ∈ U) := rfl
          have hU'free : ¬ ∃ l : Combinatorics.Line (Fin k) (Fin (M j)), ∀ x : Fin k, l x ∈ U' := by
            rintro ⟨l, hl⟩
            refine hU ⟨subspaceCompLine S l, ?_⟩
            intro x
            have hx : S (l x) ∈ U := by
              have h := hl x
              rw [hU'def] at h
              exact (Finset.mem_filter.mp h).2
            rw [subspaceCompLine_apply]
            exact hx
          have hkey := ih (le_trans (Nat.le_succ j) hj1) (M j) le_rfl U' hU'free
          have hS' : (1 + c) * ((1 + c) ^ (L - (j + 1)) * δ) * (k : ℝ) ^ (M j)
              ≤ (U'.card : ℝ) := by
            rw [hU'def]; exact hS
          have hpow : (1 + c) * ((1 + c) ^ (L - (j + 1)) * δ) = (1 + c) ^ (L - j) * δ := by
            have h1 : L - (j + 1) + 1 = L - j := by omega
            rw [← mul_assoc, ← pow_succ', h1]
          rw [hpow] at hS'
          linarith [hkey, hS']
    -- Instantiate the threshold function.
    let M : ℕ → ℕ := fun i => Nat.rec 1 (fun _ Mj => max Mj (N Mj)) i
    have hM0 : M 0 = 1 := rfl
    have hMs : ∀ i, M (i + 1) = max (M i) (N (M i)) := fun i => rfl
    have key := key_aux M hM0 hMs
    refine ⟨M L, ?_⟩
    intro n hn T hT
    by_contra hno
    have hkey := key L le_rfl n hn T hno
    rw [Nat.sub_self, pow_zero, one_mul] at hkey
    linarith [hT, hkey]
  · have hδ1' : (1 : ℝ) < δ := not_le.mp hδ1
    refine ⟨0, ?_⟩
    intro n _ T hT
    exfalso
    have hkpos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos (by exact_mod_cast hk) n
    have hlt : (k : ℝ) ^ n < δ * (k : ℝ) ^ n := by
      have := mul_lt_mul_of_pos_right hδ1' hkpos
      rwa [one_mul] at this
    linarith [hT, hcard_le T, hlt]

end Commons.Combinatorics.Ramsey