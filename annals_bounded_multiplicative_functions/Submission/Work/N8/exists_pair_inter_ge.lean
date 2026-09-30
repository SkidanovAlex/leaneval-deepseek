import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Pairwise intersection lower bound for a family of prime sets

`Work.N8.exists_pair_inter_ge`: if `A 0, …, A (K-1)` are subsets of the primes in `(P₂/2, P₂]`,
each of cardinality at least `δ · π₀(P₂)`, and `1 - δ¹² ≤ K (δ² - δ¹²)`, then some two distinct
sets intersect in at least `δ¹² · π₀(P₂)` elements.

The proof is a double-counting / second-moment argument.  Writing `c_p` for the number of sets
containing the prime `p`:

* `∑_p c_p = ∑_i #(A_i) ≥ K δ π₀(P₂)` and `∑_p c_p = ∑_i #(A_i) ≤ K π₀(P₂)`;
* `∑_p c_p² = ∑_{i,j} #(A_i ∩ A_j) = ∑_{i≠j} #(A_i ∩ A_j) + ∑_i #(A_i)`;
* Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) gives `(∑ c_p)² ≤ #(⋃ A_i) · ∑ c_p²`.

Combining, `∑_{i≠j} #(A_i ∩ A_j) ≥ K π₀(P₂) (K δ² - 1) ≥ K(K-1) δ¹² π₀(P₂)`, and averaging over
the `K(K-1)` ordered pairs of distinct sets yields the claim.

The file first establishes the three purely combinatorial identities (`fiber_sum_cardR`,
`fiber_sq_sum_cardR`, `sum_inter_eq_erase_addR`), the averaging step (`pair_pigeonhole`) and the
real-arithmetic core (`arith_core`), and then assembles them.
-/

set_option maxHeartbeats 1000000

open Finset

namespace Work.N8

/-- Cast of `Finset.card_filter` to `ℝ`: the cardinality of a filtered finset is the sum of the
indicators. -/
private theorem card_filter_cast {ι : Type*} (p : ι → Prop) [DecidablePred p] (s : Finset ι) :
    (((s.filter p).card : ℕ) : ℝ) = ∑ i ∈ s, (if p i then (1:ℝ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p i <;> simp [h]

/-- **First double-count.**  If every `A i` (`i ∈ s`) is a subset of `U`, then the sum over
`p ∈ U` of the number of sets `A i` containing `p` equals `∑_{i ∈ s} #(A i)`. -/
theorem fiber_sum_cardR {ι : Type*} [DecidableEq ι] (s : Finset ι) (U : Finset ℕ)
    (A : ι → Finset ℕ) (hA : ∀ i ∈ s, A i ⊆ U) :
    (∑ p ∈ U, (((s.filter (fun i => p ∈ A i)).card : ℕ) : ℝ)) = ∑ i ∈ s, (((A i).card : ℕ) : ℝ) := by
  have step : ∀ p : ℕ, (((s.filter (fun i => p ∈ A i)).card : ℕ) : ℝ)
      = ∑ i ∈ s, (if p ∈ A i then (1:ℝ) else 0) := by
    intro p
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : p ∈ A i <;> simp [h]
  calc (∑ p ∈ U, (((s.filter (fun i => p ∈ A i)).card : ℕ) : ℝ))
      = ∑ p ∈ U, ∑ i ∈ s, (if p ∈ A i then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro p hp; exact step p
    _ = ∑ i ∈ s, ∑ p ∈ U, (if p ∈ A i then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ i ∈ s, (((A i).card : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi
        rw [← card_filter_cast (fun p => p ∈ A i) U]
        have hfe : U.filter (fun p => p ∈ A i) = A i := by
          ext p
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hA i hi h, h⟩⟩
        rw [hfe]

/-- **Second double-count (second moment).**  With `c p = #{i ∈ s : p ∈ A i}` and `A i ⊆ U`,
the sum of squares `∑_{p ∈ U} c_p²` equals `∑_{i,j ∈ s} #(A i ∩ A j)`. -/
theorem fiber_sq_sum_cardR {ι : Type*} [DecidableEq ι] (s : Finset ι) (U : Finset ℕ)
    (A : ι → Finset ℕ) (hA : ∀ i ∈ s, A i ⊆ U) :
    (∑ p ∈ U, (((s.filter (fun i => p ∈ A i)).card : ℕ) : ℝ)^2)
      = ∑ i ∈ s, ∑ j ∈ s, (((A i ∩ A j).card : ℕ) : ℝ) := by
  have step : ∀ p : ℕ, (((s.filter (fun i => p ∈ A i)).card : ℕ) : ℝ)
      = ∑ i ∈ s, (if p ∈ A i then (1:ℝ) else 0) := by
    intro p
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : p ∈ A i <;> simp [h]
  calc (∑ p ∈ U, (((s.filter (fun i => p ∈ A i)).card : ℕ) : ℝ)^2)
      = ∑ p ∈ U, (∑ i ∈ s, (if p ∈ A i then (1:ℝ) else 0)) * (∑ j ∈ s, (if p ∈ A j then (1:ℝ) else 0)) := by
        apply Finset.sum_congr rfl; intro p hp; rw [step p, sq]
    _ = ∑ p ∈ U, ∑ i ∈ s, ∑ j ∈ s, (if p ∈ A i then (1:ℝ) else 0) * (if p ∈ A j then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro p hp
        rw [Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ p ∈ U, (if p ∈ A i then (1:ℝ) else 0) * (if p ∈ A j then (1:ℝ) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i hi
        rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, (((A i ∩ A j).card : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        have hpp : ∀ p : ℕ, (if p ∈ A i then (1:ℝ) else 0) * (if p ∈ A j then (1:ℝ) else 0)
            = (if p ∈ A i ∩ A j then (1:ℝ) else 0) := by
          intro p
          by_cases h1 : p ∈ A i <;> by_cases h2 : p ∈ A j <;> simp [h1, h2]
        rw [Finset.sum_congr rfl (fun p _ => hpp p), ← card_filter_cast (fun p => p ∈ A i ∩ A j) U]
        have hfe : U.filter (fun p => p ∈ A i ∩ A j) = A i ∩ A j := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_inter]
          exact ⟨fun h => h.2, fun h => ⟨hA i hi h.1, h⟩⟩
        rw [hfe]

/-- **Splitting the double sum along the diagonal.**  The full double sum of pairwise intersection
sizes equals the off-diagonal sum plus the diagonal `∑_i #(A i)`. -/
theorem sum_inter_eq_erase_addR {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Finset ℕ) :
    (∑ i ∈ s, ∑ j ∈ s, (((A i ∩ A j).card : ℕ) : ℝ))
      = (∑ i ∈ s, ∑ j ∈ s.erase i, (((A i ∩ A j).card : ℕ) : ℝ)) + ∑ i ∈ s, (((A i).card : ℕ) : ℝ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i hi
  have hii : (((A i ∩ A i).card : ℕ) : ℝ) = (((A i).card : ℕ) : ℝ) := by rw [Finset.inter_self]
  conv_rhs => rw [← hii]
  rw [← Finset.sum_erase_add _ _ hi]

/-- **Averaging (`pigeonhole`).**  If the sum of `x i j` over the `#s · (#s - 1)` ordered pairs of
distinct elements dominates `#s · (#s - 1) · t`, then some pair satisfies `t ≤ x i j`. -/
theorem pair_pigeonhole {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ι → ℝ) (t : ℝ)
    (hcard : 2 ≤ s.card)
    (h : (s.card : ℝ) * ((s.card : ℝ) - 1) * t ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, x i j) :
    ∃ i ∈ s, ∃ j ∈ s.erase i, t ≤ x i j := by
  by_contra hcon
  push Not at hcon
  have hs1 : 1 ≤ s.card := by omega
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i0, hi0⟩ := hne
  have hinner : ∀ i ∈ s, ∑ j ∈ s.erase i, x i j < (s.card : ℝ) * t - t := by
    intro i hi
    have hsub : ((s.erase i).card : ℕ) = s.card - 1 := Finset.card_erase_of_mem hi
    have hcast : ((s.erase i).card : ℝ) = (s.card : ℝ) - 1 := by
      rw [hsub, Nat.cast_sub hs1]; norm_num
    have hnei : (s.erase i).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have h0 : (s.erase i).card = 0 := by rw [he]; rfl
      rw [hsub] at h0
      omega
    obtain ⟨j0, hj0⟩ := hnei
    calc ∑ j ∈ s.erase i, x i j
        < ∑ j ∈ s.erase i, t :=
          Finset.sum_lt_sum (fun j hj => le_of_lt (hcon i hi j hj)) ⟨j0, hj0, hcon i hi j0 hj0⟩
      _ = ((s.erase i).card : ℝ) * t := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (s.card : ℝ) * t - t := by rw [hcast]; ring
  have houter : ∑ i ∈ s, ∑ j ∈ s.erase i, x i j < ∑ i ∈ s, ((s.card : ℝ) * t - t) :=
    Finset.sum_lt_sum (fun i hi => le_of_lt (hinner i hi)) ⟨i0, hi0, hinner i0 hi0⟩
  have hsum2 : ∑ i ∈ s, ((s.card : ℝ) * t - t) = (s.card : ℝ) * ((s.card : ℝ) * t - t) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hfinal : ∑ i ∈ s, ∑ j ∈ s.erase i, x i j < (s.card : ℝ) * ((s.card : ℝ) - 1) * t := by
    rw [hsum2] at houter
    have heq : (s.card : ℝ) * ((s.card : ℝ) * t - t) = (s.card : ℝ) * ((s.card : ℝ) - 1) * t := by ring
    linarith [houter, heq]
  linarith [hfinal, h]

/-- **Real-arithmetic core.**  From `Q = Or + C`, `C²/N ≤ Q`, `K δ N ≤ C ≤ K N`, `N > 0` and
`1 - δ¹² ≤ K (δ² - δ¹²)` (equivalently `K δ² - 1 ≥ (K-1) δ¹²`), conclude
`K (K-1) δ¹² N ≤ Or`. -/
theorem arith_core (δ N C Q Or : ℝ) (K : ℕ) (hδ : 0 < δ) (hK : 2 ≤ K)
    (hKδ : 1 - δ ^ 12 ≤ (K : ℝ) * (δ ^ 2 - δ ^ 12))
    (hN : 0 < N) (hQeq : Q = Or + C) (hQge : C ^ 2 / N ≤ Q)
    (hClow : (K : ℝ) * (δ * N) ≤ C) (hCup : C ≤ (K : ℝ) * N) :
    (K : ℝ) * ((K : ℝ) - 1) * (δ ^ 12 * N) ≤ Or := by
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKNnn : 0 ≤ (K:ℝ) * N := by positivity
  have hbase_nn : 0 ≤ (K:ℝ) * (δ * N) := by positivity
  have hsq : ((K:ℝ) * (δ * N))^2 ≤ C^2 := pow_le_pow_left₀ hbase_nn hClow 2
  have hQlow : ((K:ℝ) * (δ * N))^2 / N ≤ Q := by
    rw [div_le_iff₀ hN]
    have h2 : C^2 ≤ Q * N := by
      have := (div_le_iff₀ hN).mp hQge
      linarith [this]
    linarith [hsq, h2]
  have hOr : Or = Q - C := by linarith [hQeq]
  have hOr1 : ((K:ℝ) * (δ * N))^2 / N - C ≤ Or := by
    rw [hOr]; linarith [hQlow]
  have heq : ((K:ℝ) * (δ * N))^2 / N = (K:ℝ)^2 * δ^2 * N := by
    rw [div_eq_iff hN.ne']; ring
  have hOrlow : (K:ℝ)^2 * δ^2 * N - C ≤ Or := by linarith [hOr1, heq]
  have hmiddle : (K:ℝ) * N * ((K:ℝ) * δ^2 - 1) ≤ Or := by
    have h1 : (K:ℝ)^2 * δ^2 * N - (K:ℝ) * N ≤ (K:ℝ)^2 * δ^2 * N - C := by linarith [hCup]
    have h2 : (K:ℝ)^2 * δ^2 * N - (K:ℝ) * N = (K:ℝ) * N * ((K:ℝ) * δ^2 - 1) := by ring
    linarith [hOrlow, h1, h2]
  have hgoal : (K:ℝ) * ((K:ℝ) - 1) * (δ ^ 12 * N) ≤ (K:ℝ) * N * ((K:ℝ) * δ^2 - 1) := by
    have h2 : ((K:ℝ) - 1) * δ^12 ≤ (K:ℝ) * δ^2 - 1 := by nlinarith [hKδ]
    have h3 := mul_le_mul_of_nonneg_left h2 hKNnn
    calc (K:ℝ) * ((K:ℝ) - 1) * (δ ^ 12 * N)
        = ((K:ℝ) * N) * (((K:ℝ) - 1) * δ^12) := by ring
      _ ≤ ((K:ℝ) * N) * ((K:ℝ) * δ^2 - 1) := h3
  linarith [hmiddle, hgoal]

/-- Unfolding `IsPrimeIn` into membership of the corresponding `primesIn` finset. -/
theorem mem_primesIn_of_isPrimeIn (a b : ℝ) (p : ℕ) (h : Work.BMF.IsPrimeIn a b p) :
    p ∈ Work.BMF.primesIn a b := by
  obtain ⟨hpp, h1, h2⟩ := h
  simp only [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hpp⟩

/-- The counting core: `K` subsets of `U` (a finset of naturals of cardinality at most `N`), each
of size at least `δ N`, contain two distinct members with intersection at least `δ¹² N`. -/
private theorem core (δ N : ℝ) (hδ : 0 < δ) (K : ℕ) (hK : 2 ≤ K)
    (hKδ : 1 - δ ^ 12 ≤ (K : ℝ) * (δ ^ 2 - δ ^ 12))
    (U : Finset ℕ) (A : Fin K → Finset ℕ)
    (hAU : ∀ i, A i ⊆ U) (hUcard : (U.card : ℝ) ≤ N)
    (hcard : ∀ i, δ * N ≤ ((A i).card : ℝ)) (hN : 0 < N) :
    ∃ i j : Fin K, i ≠ j ∧ δ ^ 12 * N ≤ ((A i ∩ A j).card : ℝ) := by
  classical
  set C : ℝ := ∑ i : Fin K, (((A i).card : ℕ) : ℝ) with hC
  set Q : ℝ := ∑ p ∈ U, ((((Finset.univ : Finset (Fin K)).filter (fun i => p ∈ A i)).card : ℕ) : ℝ)^2 with hQ
  set Or : ℝ := ∑ i : Fin K, ∑ j ∈ (Finset.univ : Finset (Fin K)).erase i, (((A i ∩ A j).card : ℕ) : ℝ) with hOr
  have hIde1 := fiber_sum_cardR (Finset.univ : Finset (Fin K)) U A (fun i _ => hAU i)
  have hIde2 := fiber_sq_sum_cardR (Finset.univ : Finset (Fin K)) U A (fun i _ => hAU i)
  have hIde3 := sum_inter_eq_erase_addR (Finset.univ : Finset (Fin K)) A
  have hC_low : (K:ℝ) * (δ * N) ≤ C := by
    rw [hC]
    calc (K:ℝ) * (δ * N) = ∑ _i : Fin K, (δ * N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin K, (((A i).card : ℕ) : ℝ) := Finset.sum_le_sum (fun i _ => hcard i)
  have hC_up : C ≤ (K:ℝ) * N := by
    rw [hC]
    have hle : ∀ i : Fin K, (((A i).card : ℕ) : ℝ) ≤ N := by
      intro i
      have h1 : (A i).card ≤ U.card := Finset.card_le_card (hAU i)
      have h2 : ((A i).card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast h1
      linarith [hUcard]
    calc ∑ i : Fin K, (((A i).card : ℕ) : ℝ) ≤ ∑ _i : Fin K, N := Finset.sum_le_sum (fun i _ => hle i)
      _ = (K:ℝ) * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hQ_low : C ^ 2 / N ≤ Q := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := U)
      (f := fun p => ((((Finset.univ : Finset (Fin K)).filter (fun i => p ∈ A i)).card : ℕ) : ℝ))
    have hsum : (∑ p ∈ U, ((((Finset.univ : Finset (Fin K)).filter (fun i => p ∈ A i)).card : ℕ) : ℝ)) = C := by
      rw [hC]; exact hIde1
    have hsq : (∑ p ∈ U, ((((Finset.univ : Finset (Fin K)).filter (fun i => p ∈ A i)).card : ℕ) : ℝ)^2) = Q := by
      rw [hQ]
    rw [hsum, hsq] at hcs
    have hQnn : 0 ≤ Q := by
      rw [hQ]; apply Finset.sum_nonneg; intro p hp; exact sq_nonneg _
    have h2 : (U.card : ℝ) * Q ≤ N * Q := mul_le_mul_of_nonneg_right hUcard hQnn
    rw [div_le_iff₀ hN]
    calc C ^ 2 ≤ (U.card : ℝ) * Q := hcs
      _ ≤ N * Q := h2
      _ = Q * N := mul_comm N Q
  have hQ_eq : Q = Or + C := by
    have h1 : Q = ∑ i ∈ (Finset.univ : Finset (Fin K)), ∑ j ∈ (Finset.univ : Finset (Fin K)), (((A i ∩ A j).card : ℕ) : ℝ) := by
      rw [hQ]; exact hIde2
    have h2 : (∑ i ∈ (Finset.univ : Finset (Fin K)), ∑ j ∈ (Finset.univ : Finset (Fin K)), (((A i ∩ A j).card : ℕ) : ℝ))
        = (∑ i ∈ (Finset.univ : Finset (Fin K)), ∑ j ∈ (Finset.univ : Finset (Fin K)).erase i, (((A i ∩ A j).card : ℕ) : ℝ)) + C := by
      rw [hC]; exact hIde3
    rw [h1, h2, hOr]
  have hArith := arith_core δ N C Q Or K hδ hK hKδ hN hQ_eq hQ_low hC_low hC_up
  have hKcard : ((Finset.univ : Finset (Fin K)).card : ℝ) = (K:ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hArith2 : ((Finset.univ : Finset (Fin K)).card : ℝ) * (((Finset.univ : Finset (Fin K)).card : ℝ) - 1) * (δ ^ 12 * N)
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin K)), ∑ j ∈ (Finset.univ : Finset (Fin K)).erase i, (((A i ∩ A j).card : ℕ) : ℝ) := by
    rw [hKcard, ← hOr]; exact hArith
  obtain ⟨i, -, j, hj, hle⟩ := pair_pigeonhole (Finset.univ : Finset (Fin K))
      (fun i j => (((A i ∩ A j).card : ℕ) : ℝ)) (δ ^ 12 * N)
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hK) hArith2
  exact ⟨i, j, Ne.symm (Finset.mem_erase.mp hj).1, hle⟩

theorem exists_pair_inter_ge (δ P₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (K : ℕ) (hK : 2 ≤ K)
    (hKδ : 1 - δ ^ 12 ≤ (K : ℝ) * (δ ^ 2 - δ ^ 12))
    (hcount : ∀ P : ℝ, 1 < P → ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤ Work.BMF.pi0 P)
    (A : Fin K → Finset ℕ)
    (hA : ∀ i, ∀ p ∈ A i, Work.BMF.IsPrimeIn (P₂ / 2) P₂ p)
    (hcard : ∀ i, δ * Work.BMF.pi0 P₂ ≤ ((A i).card : ℝ)) :
    ∃ i j : Fin K, i ≠ j ∧ δ ^ 12 * Work.BMF.pi0 P₂ ≤ ((A i ∩ A j).card : ℝ) := by
  classical
  have h0K : 0 < K := by omega
  have h1K : 1 < K := by omega
  have hAU : ∀ i, A i ⊆ Work.BMF.primesIn (P₂ / 2) P₂ := fun i p hp =>
    mem_primesIn_of_isPrimeIn (P₂ / 2) P₂ p (hA i p hp)
  by_cases hN : 0 < Work.BMF.pi0 P₂
  · -- non-trivial case: `π₀(P₂) > 0`, so some `A i` is non-empty and hence `1 < P₂`
    have hP₂ : 1 < P₂ := by
      have hne : (A ⟨0, h0K⟩).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have h0 : (A ⟨0, h0K⟩).card = 0 := by simp [hempty]
        have hc := hcard ⟨0, h0K⟩
        rw [h0] at hc
        simp only [Nat.cast_zero] at hc
        have hpos : 0 < δ * Work.BMF.pi0 P₂ := mul_pos hδ hN
        linarith
      obtain ⟨p, hp⟩ := hne
      obtain ⟨hpp, h1, h2⟩ := hA ⟨0, h0K⟩ p hp
      have h2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hUcard : ((Work.BMF.primesIn (P₂ / 2) P₂).card : ℝ) ≤ Work.BMF.pi0 P₂ := hcount P₂ hP₂
    exact core δ (Work.BMF.pi0 P₂) hδ K hK hKδ (Work.BMF.primesIn (P₂ / 2) P₂) A hAU hUcard hcard hN
  · -- trivial case: `π₀(P₂) ≤ 0`, any two distinct indices work
    refine ⟨⟨0, h0K⟩, ⟨1, h1K⟩, ?_, ?_⟩
    · intro h
      have h2 : (0:ℕ) = 1 := congrArg Fin.val h
      omega
    · have hNle : Work.BMF.pi0 P₂ ≤ 0 := not_lt.mp hN
      have h1 : δ ^ 12 * Work.BMF.pi0 P₂ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hNle
      have h2 : (0:ℝ) ≤ ((A ⟨0, h0K⟩ ∩ A ⟨1, h1K⟩).card : ℝ) := by positivity
      linarith

end Work.N8
