import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

open Finset

/-! ## Part 1: elementary counting lemmas -/

/-- In `{1,…,H}` a single residue class modulo `m` has at most `H/m + 1` elements. -/
lemma card_Icc_modEq_le (H m r : ℕ) (hm : 0 < m) :
    ((Finset.Icc 1 H).filter (fun n => n ≡ r [MOD m])).card ≤ H / m + 1 := by
  set S := (Finset.Icc 1 H).filter (fun n => n ≡ r [MOD m]) with hS
  have hinj : Set.InjOn (fun n => n / m) ↑S := by
    intro x hx y hy hxy
    have hxS : x ∈ S := hx
    have hyS : y ∈ S := hy
    rw [hS, Finset.mem_filter] at hxS hyS
    have hxr : x % m = r % m := hxS.2
    have hyr : y % m = r % m := hyS.2
    simp only at hxy
    calc x = m * (x / m) + x % m := (Nat.div_add_mod x m).symm
      _ = m * (y / m) + y % m := by rw [hxy, hxr, hyr]
      _ = y := Nat.div_add_mod y m
  have hmap : Set.MapsTo (fun n => n / m) ↑S ↑(Finset.Icc 0 (H / m)) := by
    intro x hx
    have hxS : x ∈ S := hx
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hxS
    have hxH : x ≤ H := hxS.1.2
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.div_le_div_right hxH⟩
  calc S.card ≤ (Finset.Icc 0 (H/m)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = H/m+1 := by rw [Nat.card_Icc, Nat.sub_zero]

/-- Real-valued form of `card_Icc_modEq_le`. -/
lemma sum_Icc_indicator_modEq_le (H m r : ℕ) (hm : 0 < m) :
    (∑ n ∈ Finset.Icc 1 H, (if n ≡ r [MOD m] then (1:ℝ) else 0)) ≤ (H:ℝ)/m + 1 := by
  have heq : (∑ n ∈ Finset.Icc 1 H, (if n ≡ r [MOD m] then (1:ℝ) else 0))
      = (((Finset.Icc 1 H).filter (fun n => n ≡ r [MOD m])).card : ℝ) := by
    rw [← Finset.sum_filter]; simp
  rw [heq]
  have h := card_Icc_modEq_le H m r hm
  calc (((Finset.Icc 1 H).filter (fun n => n ≡ r [MOD m])).card : ℝ)
      ≤ ((H/m + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((H/m : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (H:ℝ)/m + 1 := by
        have hc : ((H/m : ℕ) : ℝ) ≤ (H:ℝ)/m := Nat.cast_div_le
        linarith

/-- Two congruence conditions with coprime moduli cut out a residue class mod `u*v`. -/
lemma card_Icc_modEq_pair_le (H u v r s : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hcop : Nat.Coprime u v) :
    ((Finset.Icc 1 H).filter (fun n => n ≡ r [MOD u] ∧ n ≡ s [MOD v])).card
      ≤ H / (u*v) + 1 := by
  set T := (Finset.Icc 1 H).filter (fun n => n ≡ r [MOD u] ∧ n ≡ s [MOD v]) with hT
  rcases T.eq_empty_or_nonempty with hem | ⟨n0, hn0⟩
  · rw [hem]; simp
  · have hsub : T ⊆ (Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD (u*v)]) := by
      intro n hn
      rw [hT, Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      refine ⟨hn.1, ?_⟩
      have hn0' : n0 ∈ Finset.Icc 1 H ∧ n0 ≡ r [MOD u] ∧ n0 ≡ s [MOD v] := by
        rw [hT, Finset.mem_filter] at hn0
        exact ⟨hn0.1, hn0.2.1, hn0.2.2⟩
      rcases le_total n0 n with hle | hle
      · have h1 : u ∣ n - n0 := (Nat.modEq_iff_dvd' hle).mp (hn0'.2.1.trans hn.2.1.symm)
        have h2 : v ∣ n - n0 := (Nat.modEq_iff_dvd' hle).mp (hn0'.2.2.trans hn.2.2.symm)
        exact ((Nat.modEq_iff_dvd' hle).mpr (hcop.mul_dvd_of_dvd_of_dvd h1 h2)).symm
      · have h1 : u ∣ n0 - n := (Nat.modEq_iff_dvd' hle).mp (hn.2.1.trans hn0'.2.1.symm)
        have h2 : v ∣ n0 - n := (Nat.modEq_iff_dvd' hle).mp (hn.2.2.trans hn0'.2.2.symm)
        exact (Nat.modEq_iff_dvd' hle).mpr (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
    calc T.card ≤ ((Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD (u*v)])).card :=
          Finset.card_le_card hsub
      _ ≤ H/(u*v)+1 := card_Icc_modEq_le H (u*v) n0 (Nat.mul_pos hu hv)

/-- Real-valued form of `card_Icc_modEq_pair_le`. -/
lemma sum_Icc_indicator_modEq_pair_le (H u v r s : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hcop : Nat.Coprime u v) :
    (∑ n ∈ Finset.Icc 1 H, (if n ≡ r [MOD u] ∧ n ≡ s [MOD v] then (1:ℝ) else 0))
      ≤ (H:ℝ)/(u*v) + 1 := by
  have heq : (∑ n ∈ Finset.Icc 1 H, (if n ≡ r [MOD u] ∧ n ≡ s [MOD v] then (1:ℝ) else 0))
      = (((Finset.Icc 1 H).filter (fun n => n ≡ r [MOD u] ∧ n ≡ s [MOD v])).card : ℝ) := by
    rw [← Finset.sum_filter]; simp
  rw [heq]
  have h := card_Icc_modEq_pair_le H u v r s hu hv hcop
  calc (((Finset.Icc 1 H).filter (fun n => n ≡ r [MOD u] ∧ n ≡ s [MOD v])).card : ℝ)
      ≤ ((H/(u*v) + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((H/(u*v) : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (H:ℝ)/(u*v) + 1 := by
        have hc : ((H/(u*v) : ℕ) : ℝ) ≤ (H:ℝ)/(u*v) := by
          have := Nat.cast_div_le (α := ℝ) (m := H) (n := u*v)
          simpa using this
        linarith

/-- Combining congruences modulo coprime moduli. -/
lemma modEq_mul_of_coprime {m N a b : ℕ} (hcop : Nat.Coprime m N)
    (h1 : a ≡ b [MOD m]) (h2 : a ≡ b [MOD N]) : a ≡ b [MOD m * N] := by
  rcases le_total a b with hle | hle
  · have d1 : m ∣ b - a := (Nat.modEq_iff_dvd' hle).mp h1
    have d2 : N ∣ b - a := (Nat.modEq_iff_dvd' hle).mp h2
    exact (Nat.modEq_iff_dvd' hle).mpr (hcop.mul_dvd_of_dvd_of_dvd d1 d2)
  · have d1 : m ∣ a - b := (Nat.modEq_iff_dvd' hle).mp h1.symm
    have d2 : N ∣ a - b := (Nat.modEq_iff_dvd' hle).mp h2.symm
    exact ((Nat.modEq_iff_dvd' hle).mpr (hcop.mul_dvd_of_dvd_of_dvd d1 d2)).symm

/-- A family of congruences modulo pairwise coprime moduli is a single congruence
modulo the product. -/
lemma modEq_prod_of_coprime {s : Finset ℕ} (hcop : (s : Set ℕ).Pairwise Nat.Coprime)
    {a b : ℕ} (h : ∀ m ∈ s, a ≡ b [MOD m]) : a ≡ b [MOD ∏ m ∈ s, m] := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq, Nat.mod_one]
  | insert m s hm ih =>
      rw [Finset.prod_insert hm]
      have hcop_s : (s : Set ℕ).Pairwise Nat.Coprime := by
        intro x hx y hy hxy
        exact hcop (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy) hxy
      have ih' := ih hcop_s (fun x hx => h x (Finset.mem_insert_of_mem hx))
      have hcop_ms : Nat.Coprime m (∏ x ∈ s, x) := by
        apply Nat.Coprime.prod_right
        intro x hx
        have hne : m ≠ x := fun hh => hm (hh ▸ hx)
        exact hcop (Finset.mem_insert_self m s) (Finset.mem_insert_of_mem hx) hne
      exact modEq_mul_of_coprime hcop_ms (h m (Finset.mem_insert_self m s)) ih'

/-- Cardinality bound for a family of congruences with pairwise coprime moduli. -/
lemma card_Icc_modEq_finset_le (H : ℕ) (s : Finset ℕ) (r : ℕ → ℕ)
    (hcop : (s : Set ℕ).Pairwise Nat.Coprime) (hpos : ∀ m ∈ s, 0 < m) :
    ((Finset.Icc 1 H).filter (fun n => ∀ m ∈ s, n ≡ r m [MOD m])).card
      ≤ H / (∏ m ∈ s, m) + 1 := by
  set T := (Finset.Icc 1 H).filter (fun n => ∀ m ∈ s, n ≡ r m [MOD m]) with hT
  rcases T.eq_empty_or_nonempty with hem | ⟨n0, hn0⟩
  · rw [hem]; simp
  · have hn0' : ∀ m ∈ s, n0 ≡ r m [MOD m] := by
      rw [hT, Finset.mem_filter] at hn0; exact hn0.2
    have hsub : T ⊆ (Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD ∏ m ∈ s, m]) := by
      intro n hn
      rw [hT, Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      exact ⟨hn.1, modEq_prod_of_coprime hcop (fun m hm => (hn.2 m hm).trans (hn0' m hm).symm)⟩
    calc T.card ≤ ((Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD ∏ m ∈ s, m])).card :=
          Finset.card_le_card hsub
      _ ≤ H/(∏ m ∈ s, m) + 1 := card_Icc_modEq_le H _ n0 (Finset.prod_pos hpos)

/-- Real-valued form of `card_Icc_modEq_finset_le`. -/
lemma sum_Icc_indicator_modEq_finset_le (H : ℕ) (s : Finset ℕ) (r : ℕ → ℕ)
    (hcop : (s : Set ℕ).Pairwise Nat.Coprime) (hpos : ∀ m ∈ s, 0 < m) :
    (∑ n ∈ Finset.Icc 1 H, (if ∀ m ∈ s, n ≡ r m [MOD m] then (1:ℝ) else 0))
      ≤ (H:ℝ)/(∏ m ∈ s, m) + 1 := by
  have heq : (∑ n ∈ Finset.Icc 1 H, (if ∀ m ∈ s, n ≡ r m [MOD m] then (1:ℝ) else 0))
      = (((Finset.Icc 1 H).filter (fun n => ∀ m ∈ s, n ≡ r m [MOD m])).card : ℝ) := by
    rw [← Finset.sum_filter]; simp
  rw [heq]
  have h := card_Icc_modEq_finset_le H s r hcop hpos
  calc (((Finset.Icc 1 H).filter (fun n => ∀ m ∈ s, n ≡ r m [MOD m])).card : ℝ)
      ≤ ((H/(∏ m ∈ s, m) + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((H/(∏ m ∈ s, m) : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (H:ℝ)/(∏ m ∈ s, m) + 1 := by
        have hc : ((H/(∏ m ∈ s, m) : ℕ) : ℝ) ≤ (H:ℝ)/(∏ m ∈ s, m) := by
          have := Nat.cast_div_le (α := ℝ) (m := H) (n := ∏ m ∈ s, m)
          simpa using this
        linarith

/-- Elementary indicator identities. -/
lemma ind_comm (n a b : ℕ) :
    (if a ≡ b [MOD n] then (1:ℝ) else 0) = (if b ≡ a [MOD n] then (1:ℝ) else 0) := by
  by_cases h : a ≡ b [MOD n]
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

lemma ind_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1:ℝ) else 0) * (if Q then (1:ℝ) else 0) = (if P ∧ Q then (1:ℝ) else 0) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

lemma ind_mul3 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    (if P then (1:ℝ) else 0) * (if Q then (1:ℝ) else 0) * (if R then (1:ℝ) else 0)
      = (if P ∧ Q ∧ R then (1:ℝ) else 0) := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;> simp [hp, hq, hr]

/-- Three congruences with pairwise coprime moduli give a residue class mod the product. -/
lemma card_Icc_modEq_triple_le (H u v w r1 r2 r3 : ℕ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h1 : Nat.Coprime u v) (h2 : Nat.Coprime u w) (h3 : Nat.Coprime v w) :
    ((Finset.Icc 1 H).filter
        (fun n => n ≡ r1 [MOD u] ∧ n ≡ r2 [MOD v] ∧ n ≡ r3 [MOD w])).card
      ≤ H / (u*v*w) + 1 := by
  set T := (Finset.Icc 1 H).filter
      (fun n => n ≡ r1 [MOD u] ∧ n ≡ r2 [MOD v] ∧ n ≡ r3 [MOD w]) with hT
  rcases T.eq_empty_or_nonempty with hem | ⟨n0, hn0⟩
  · rw [hem]; simp
  · have hn0' : n0 ∈ Finset.Icc 1 H ∧ n0 ≡ r1 [MOD u] ∧ n0 ≡ r2 [MOD v] ∧ n0 ≡ r3 [MOD w] := by
      rw [hT, Finset.mem_filter] at hn0; exact ⟨hn0.1, hn0.2.1, hn0.2.2.1, hn0.2.2.2⟩
    have hsub : T ⊆ (Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD (u*v*w)]) := by
      intro n hn
      rw [hT, Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      refine ⟨hn.1, ?_⟩
      have e1 : n ≡ n0 [MOD (u*v)] :=
        modEq_mul_of_coprime h1 (hn.2.1.trans hn0'.2.1.symm) (hn.2.2.1.trans hn0'.2.2.1.symm)
      have e2 : n ≡ n0 [MOD w] := hn.2.2.2.trans hn0'.2.2.2.symm
      exact modEq_mul_of_coprime (h2.mul_left h3) e1 e2
    calc T.card ≤ ((Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD (u*v*w)])).card :=
          Finset.card_le_card hsub
      _ = ((Finset.Icc 1 H).filter (fun n => n ≡ n0 [MOD (u*(v*w))])).card := by
          rw [mul_assoc]
      _ ≤ H/(u*(v*w))+1 := card_Icc_modEq_le H (u*(v*w)) n0 (by positivity)
      _ = H/(u*v*w)+1 := by rw [mul_assoc]

/-- Real-valued form of `card_Icc_modEq_triple_le`. -/
lemma sum_Icc_indicator_modEq_triple_le (H u v w r1 r2 r3 : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (h1 : Nat.Coprime u v) (h2 : Nat.Coprime u w) (h3 : Nat.Coprime v w) :
    (∑ n ∈ Finset.Icc 1 H,
        (if n ≡ r1 [MOD u] ∧ n ≡ r2 [MOD v] ∧ n ≡ r3 [MOD w] then (1:ℝ) else 0))
      ≤ (H:ℝ)/(u*v*w) + 1 := by
  have heq : (∑ n ∈ Finset.Icc 1 H,
        (if n ≡ r1 [MOD u] ∧ n ≡ r2 [MOD v] ∧ n ≡ r3 [MOD w] then (1:ℝ) else 0))
      = (((Finset.Icc 1 H).filter
          (fun n => n ≡ r1 [MOD u] ∧ n ≡ r2 [MOD v] ∧ n ≡ r3 [MOD w])).card : ℝ) := by
    rw [← Finset.sum_filter]; simp
  rw [heq]
  have h := card_Icc_modEq_triple_le H u v w r1 r2 r3 hu hv hw h1 h2 h3
  calc (((Finset.Icc 1 H).filter
          (fun n => n ≡ r1 [MOD u] ∧ n ≡ r2 [MOD v] ∧ n ≡ r3 [MOD w])).card : ℝ)
      ≤ ((H/(u*v*w) + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((H/(u*v*w) : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (H:ℝ)/(u*v*w) + 1 := by
        have hc : ((H/(u*v*w) : ℕ) : ℝ) ≤ (H:ℝ)/(u*v*w) := by
          have := Nat.cast_div_le (α := ℝ) (m := H) (n := u*v*w)
          simpa using this
        linarith

/-- The main counting bound: for pairwise coprime `u`, `w`, `w'`, the number of quadruples
satisfying the six congruences is at most `H (H/u+1) (H/(ww')+1) (H/(uww')+1)`. -/
lemma sum_T3_le (H u w w' : ℕ) (hu : 0 < u) (hw : 0 < w) (hw' : 0 < w')
    (h1 : Nat.Coprime u w) (h2 : Nat.Coprime u w') (h3 : Nat.Coprime w w') :
    (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H, ∑ d ∈ Finset.Icc 1 H,
        (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if c ≡ d [MOD u] then (1:ℝ) else 0) *
        (if a ≡ c [MOD w] then (1:ℝ) else 0) * (if b ≡ d [MOD w] then (1:ℝ) else 0) *
        (if a ≡ d [MOD w'] then (1:ℝ) else 0) * (if b ≡ c [MOD w'] then (1:ℝ) else 0))
      ≤ (H:ℝ) * ((H:ℝ)/u + 1) * ((H:ℝ)/(w*w') + 1) * ((H:ℝ)/(u*w*w') + 1) := by
  have hd : ∀ a b c : ℕ, (∑ d ∈ Finset.Icc 1 H,
        (if c ≡ d [MOD u] then (1:ℝ) else 0) * (if b ≡ d [MOD w] then (1:ℝ) else 0)
          * (if a ≡ d [MOD w'] then (1:ℝ) else 0)) ≤ (H:ℝ)/(u*w*w') + 1 := by
    intro a b c
    have hcong : (∑ d ∈ Finset.Icc 1 H,
        (if c ≡ d [MOD u] then (1:ℝ) else 0) * (if b ≡ d [MOD w] then (1:ℝ) else 0)
          * (if a ≡ d [MOD w'] then (1:ℝ) else 0))
        = (∑ d ∈ Finset.Icc 1 H,
            (if d ≡ c [MOD u] ∧ d ≡ b [MOD w] ∧ d ≡ a [MOD w'] then (1:ℝ) else 0)) := by
      apply Finset.sum_congr rfl; intro d _
      rw [ind_comm u c d, ind_comm w b d, ind_comm w' a d, ind_mul3]
    rw [hcong]
    exact sum_Icc_indicator_modEq_triple_le H u w w' c b a hu hw hw' h1 h2 h3
  have hc : ∀ a b : ℕ, (∑ c ∈ Finset.Icc 1 H,
        (if a ≡ c [MOD w] then (1:ℝ) else 0) * (if b ≡ c [MOD w'] then (1:ℝ) else 0))
        ≤ (H:ℝ)/(w*w') + 1 := by
    intro a b
    have hcong : (∑ c ∈ Finset.Icc 1 H,
        (if a ≡ c [MOD w] then (1:ℝ) else 0) * (if b ≡ c [MOD w'] then (1:ℝ) else 0))
        = (∑ c ∈ Finset.Icc 1 H, (if c ≡ a [MOD w] ∧ c ≡ b [MOD w'] then (1:ℝ) else 0)) := by
      apply Finset.sum_congr rfl; intro c _
      rw [ind_comm w a c, ind_comm w' b c, ind_mul]
    rw [hcong]
    exact sum_Icc_indicator_modEq_pair_le H w w' a b hw hw' h3
  have hb : (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
        (if a ≡ b [MOD u] then (1:ℝ) else 0)) ≤ (H:ℝ) * ((H:ℝ)/u + 1) := by
    have step : ∀ a : ℕ, (∑ b ∈ Finset.Icc 1 H, (if a ≡ b [MOD u] then (1:ℝ) else 0))
        ≤ (H:ℝ)/u + 1 := by
      intro a
      calc (∑ b ∈ Finset.Icc 1 H, (if a ≡ b [MOD u] then (1:ℝ) else 0))
          = (∑ b ∈ Finset.Icc 1 H, (if b ≡ a [MOD u] then (1:ℝ) else 0)) := by
            apply Finset.sum_congr rfl; intro b _; rw [ind_comm]
        _ ≤ (H:ℝ)/u + 1 := sum_Icc_indicator_modEq_le H u a hu
    calc (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, (if a ≡ b [MOD u] then (1:ℝ) else 0))
        ≤ ∑ _a ∈ Finset.Icc 1 H, ((H:ℝ)/u + 1) := Finset.sum_le_sum (fun a _ => step a)
      _ = (H:ℝ) * ((H:ℝ)/u + 1) := by
            rw [Finset.sum_const, Nat.card_Icc]
            have hh : H + 1 - 1 = H := Nat.add_sub_cancel H 1
            rw [hh, nsmul_eq_mul]
  calc (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H, ∑ d ∈ Finset.Icc 1 H,
        (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if c ≡ d [MOD u] then (1:ℝ) else 0) *
        (if a ≡ c [MOD w] then (1:ℝ) else 0) * (if b ≡ d [MOD w] then (1:ℝ) else 0) *
        (if a ≡ d [MOD w'] then (1:ℝ) else 0) * (if b ≡ c [MOD w'] then (1:ℝ) else 0))
      = (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if a ≡ c [MOD w] then (1:ℝ) else 0)
            * (if b ≡ c [MOD w'] then (1:ℝ) else 0)
            * (∑ d ∈ Finset.Icc 1 H, (if c ≡ d [MOD u] then (1:ℝ) else 0)
                * (if b ≡ d [MOD w] then (1:ℝ) else 0)
                * (if a ≡ d [MOD w'] then (1:ℝ) else 0))) := by
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        ring
    _ ≤ (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if a ≡ c [MOD w] then (1:ℝ) else 0)
            * (if b ≡ c [MOD w'] then (1:ℝ) else 0) * ((H:ℝ)/(u*w*w') + 1)) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        apply Finset.sum_le_sum; intro c _
        exact mul_le_mul_of_nonneg_left (hd a b c) (by positivity)
    _ = ((∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if a ≡ c [MOD w] then (1:ℝ) else 0)
            * (if b ≡ c [MOD w'] then (1:ℝ) else 0))) * ((H:ℝ)/(u*w*w') + 1) := by
        simp only [Finset.sum_mul]
    _ ≤ ((H:ℝ) * ((H:ℝ)/u + 1) * ((H:ℝ)/(w*w') + 1)) * ((H:ℝ)/(u*w*w') + 1) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
              (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if a ≡ c [MOD w] then (1:ℝ) else 0)
                * (if b ≡ c [MOD w'] then (1:ℝ) else 0))
            ≤ (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
                (if a ≡ b [MOD u] then (1:ℝ) else 0) * ((H:ℝ)/(w*w') + 1)) := by
              apply Finset.sum_le_sum; intro a _
              apply Finset.sum_le_sum; intro b _
              calc (∑ c ∈ Finset.Icc 1 H,
                    (if a ≡ b [MOD u] then (1:ℝ) else 0) * (if a ≡ c [MOD w] then (1:ℝ) else 0)
                      * (if b ≡ c [MOD w'] then (1:ℝ) else 0))
                  = (if a ≡ b [MOD u] then (1:ℝ) else 0) * (∑ c ∈ Finset.Icc 1 H,
                      (if a ≡ c [MOD w] then (1:ℝ) else 0) * (if b ≡ c [MOD w'] then (1:ℝ) else 0)) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl; intro c _; ring
                _ ≤ (if a ≡ b [MOD u] then (1:ℝ) else 0) * ((H:ℝ)/(w*w') + 1) :=
                    mul_le_mul_of_nonneg_left (hc a b) (by positivity)
          _ = (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
                (if a ≡ b [MOD u] then (1:ℝ) else 0)) * ((H:ℝ)/(w*w') + 1) := by
              simp only [Finset.sum_mul]
          _ ≤ ((H:ℝ) * ((H:ℝ)/u + 1)) * ((H:ℝ)/(w*w') + 1) :=
              mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (H:ℝ) * ((H:ℝ)/u + 1) * ((H:ℝ)/(w*w') + 1) * ((H:ℝ)/(u*w*w') + 1) := by ring

/-! ## Part 2: a powerset product identity -/

/-- `∑_{A ⊆ s} ∑_{B ⊆ s\A} (∏_{A} α)(∏_{B} β) = ∏_{s} (1 + α + β)`. -/
theorem sum_powerset_disjoint_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α β : ι → ℝ) :
    (∑ A ∈ s.powerset, ∑ B ∈ (s \ A).powerset, (∏ p ∈ A, α p) * (∏ p ∈ B, β p))
      = ∏ p ∈ s, (1 + α p + β p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha]
      have hkey : ∀ A ∈ s.powerset,
          (∑ B ∈ ((insert a s) \ A).powerset, (∏ p ∈ A, α p) * (∏ p ∈ B, β p))
            + (∑ B ∈ ((insert a s) \ insert a A).powerset,
                (∏ p ∈ insert a A, α p) * (∏ p ∈ B, β p))
          = (1 + α a + β a) * (∑ B ∈ (s \ A).powerset, (∏ p ∈ A, α p) * (∏ p ∈ B, β p)) := by
        intro A hA
        have hAs : A ⊆ s := Finset.mem_powerset.mp hA
        have haA : a ∉ A := fun h => ha (hAs h)
        have ha_sA : a ∉ s \ A := fun h => ha (Finset.mem_sdiff.mp h).1
        have e1 : (insert a s) \ A = insert a (s \ A) := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, hxA⟩
            rcases hx with rfl | hxs
            · exact Or.inl rfl
            · exact Or.inr ⟨hxs, hxA⟩
          · rintro (rfl | ⟨hxs, hxA⟩)
            · exact ⟨Or.inl rfl, haA⟩
            · exact ⟨Or.inr hxs, hxA⟩
        have e2 : (insert a s) \ insert a A = s \ A := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hx, hxn⟩
            rcases hx with rfl | hxs
            · exact absurd (Or.inl rfl) hxn
            · exact ⟨hxs, fun hxA => hxn (Or.inr hxA)⟩
          · rintro ⟨hxs, hxA⟩
            exact ⟨Or.inr hxs, fun h => h.elim (fun hh => ha (hh ▸ hxs)) hxA⟩
        rw [e1, e2]
        have hS1 : (∑ B ∈ (insert a (s \ A)).powerset, (∏ p ∈ A, α p) * (∏ p ∈ B, β p))
            = (1 + β a) * (∑ B ∈ (s \ A).powerset, (∏ p ∈ A, α p) * (∏ p ∈ B, β p)) := by
          rw [Finset.sum_powerset_insert ha_sA]
          have hf : ∀ B ∈ (s\A).powerset, (∏ p ∈ A, α p) * (∏ p ∈ insert a B, β p)
              = β a * ((∏ p ∈ A, α p) * (∏ p ∈ B, β p)) := by
            intro B hB
            have hBsub : B ⊆ s := fun x hx =>
              (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB hx)).1
            have haB : a ∉ B := fun h => ha (hBsub h)
            rw [Finset.prod_insert haB]; ring
          rw [Finset.sum_congr rfl hf, ← Finset.sum_add_distrib]
          have haux : ∀ B ∈ (s\A).powerset,
              (∏ p ∈ A, α p) * (∏ p ∈ B, β p) + β a * ((∏ p ∈ A, α p) * (∏ p ∈ B, β p))
              = (1 + β a) * ((∏ p ∈ A, α p) * (∏ p ∈ B, β p)) := by
            intro B hB; ring
          rw [Finset.sum_congr rfl haux, ← Finset.mul_sum]
        have hS2 : (∑ B ∈ (s \ A).powerset, (∏ p ∈ insert a A, α p) * (∏ p ∈ B, β p))
            = α a * (∑ B ∈ (s \ A).powerset, (∏ p ∈ A, α p) * (∏ p ∈ B, β p)) := by
          rw [Finset.prod_insert haA]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro B hB; ring
        rw [hS1, hS2]
        ring
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl hkey]
      rw [← Finset.mul_sum]
      rw [ih]

/-! ## Part 3: the multiset structure of `{a,b} = {c,d}` over `ZMod p` -/

/-- Over `ZMod p` (`p` prime), equal sum and product forces the multisets `{a,b}`, `{c,d}`
to coincide. -/
theorem add_mul_eq_iff_swap (p : ℕ) [Fact p.Prime] (a b c d : ℕ) :
    ((a : ZMod p) + (b : ZMod p) = (c : ZMod p) + (d : ZMod p) ∧
      (a : ZMod p) * (b : ZMod p) = (c : ZMod p) * (d : ZMod p))
      ↔ ((a : ZMod p) = (c : ZMod p) ∧ (b : ZMod p) = (d : ZMod p)) ∨
        ((a : ZMod p) = (d : ZMod p) ∧ (b : ZMod p) = (c : ZMod p)) := by
  have key : ∀ x : ℕ, ((x : ZMod p) - (a : ZMod p)) * ((x : ZMod p) - (b : ZMod p))
      = (x : ZMod p) * (x : ZMod p) - (x : ZMod p) * ((a : ZMod p) + b) + (a : ZMod p) * b := by
    intro x; ring
  constructor
  · rintro ⟨h1, h2⟩
    have hc0 : ((c : ZMod p) - (a : ZMod p)) * ((c : ZMod p) - (b : ZMod p)) = 0 := by
      rw [key c, h1, h2]; ring
    have hc' : (c : ZMod p) = (a : ZMod p) ∨ (c : ZMod p) = (b : ZMod p) := by
      rcases mul_eq_zero.mp hc0 with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    rcases hc' with h | h
    · left
      have hbd : (b : ZMod p) = (d : ZMod p) := by
        have e : (a : ZMod p) + (b : ZMod p) = (a : ZMod p) + (d : ZMod p) := by
          calc (a : ZMod p) + (b : ZMod p) = (c : ZMod p) + (d : ZMod p) := h1
            _ = (a : ZMod p) + (d : ZMod p) := by rw [← h]
        exact add_left_cancel e
      exact ⟨h.symm, hbd⟩
    · right
      have had : (a : ZMod p) = (d : ZMod p) := by
        have e : (b : ZMod p) + (a : ZMod p) = (b : ZMod p) + (d : ZMod p) := by
          calc (b : ZMod p) + (a : ZMod p) = (a : ZMod p) + (b : ZMod p) := by ring
            _ = (c : ZMod p) + (d : ZMod p) := h1
            _ = (b : ZMod p) + (d : ZMod p) := by rw [← h]
        exact add_left_cancel e
      exact ⟨had, h.symm⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by rw [h1, h2], by rw [h1, h2]⟩
    · exact ⟨by rw [h1, h2]; ring, by rw [h1, h2]; ring⟩

/-! ## Part 4: the arithmetic functions `Eg0`, `Eg1` and indicator bookkeeping -/

/-- `gcd(gcd(a-b,c-d), q)` as a natural number. -/
def Eg0 (q a b c d : ℕ) : ℕ :=
  Nat.gcd (Int.gcd ((a:ℤ) - (b:ℤ)) ((c:ℤ) - (d:ℤ))) q

/-- `gcd(gcd(a+b-c-d, ab-cd), q)` as a natural number. -/
def Eg1 (q a b c d : ℕ) : ℕ :=
  Nat.gcd (Int.gcd (((a:ℤ) + (b:ℤ)) - ((c:ℤ) + (d:ℤ)))
    ((a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ))) q

lemma squarefree_ne_zero {n : ℕ} (h : Squarefree n) : n ≠ 0 := by
  intro hn; subst hn
  rw [Nat.squarefree_iff_prime_squarefree] at h
  exact h 2 Nat.prime_two (dvd_zero (2*2))

lemma int_dvd_sub_iff_modEq (p a b : ℕ) : (p:ℤ) ∣ (a:ℤ) - (b:ℤ) ↔ a ≡ b [MOD p] := by
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
  rw [show ((b:ℤ) - (a:ℤ)) = -(((a:ℤ)-(b:ℤ))) by ring, dvd_neg]

lemma dvd_Eg0_iff {p q a b c d : ℕ} (hpq : p ∣ q) :
    p ∣ Eg0 q a b c d ↔ (a ≡ b [MOD p] ∧ c ≡ d [MOD p]) := by
  unfold Eg0
  rw [Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨h1, _⟩
    have h3 : (p:ℤ) ∣ ((Int.gcd ((a:ℤ)-(b:ℤ)) ((c:ℤ)-(d:ℤ)) : ℕ) : ℤ) := by exact_mod_cast h1
    exact ⟨(int_dvd_sub_iff_modEq p a b).mp (h3.trans (Int.gcd_dvd_left _ _)),
           (int_dvd_sub_iff_modEq p c d).mp (h3.trans (Int.gcd_dvd_right _ _))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Int.dvd_gcd ((int_dvd_sub_iff_modEq p a b).mpr h1)
        ((int_dvd_sub_iff_modEq p c d).mpr h2), hpq⟩

lemma dvd_Eg1_iff {p q a b c d : ℕ} (hpq : p ∣ q) :
    p ∣ Eg1 q a b c d ↔
      ((a:ZMod p) + (b:ZMod p) = (c:ZMod p) + (d:ZMod p) ∧
       (a:ZMod p) * (b:ZMod p) = (c:ZMod p) * (d:ZMod p)) := by
  unfold Eg1
  rw [Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨h1, _⟩
    have h3 : (p:ℤ) ∣ ((Int.gcd (((a:ℤ)+(b:ℤ))-((c:ℤ)+(d:ℤ)))
        ((a:ℤ)*(b:ℤ)-(c:ℤ)*(d:ℤ)) : ℕ) : ℤ) := by exact_mod_cast h1
    have e1 : (p:ℤ) ∣ ((a:ℤ)+(b:ℤ)) - ((c:ℤ)+(d:ℤ)) := h3.trans (Int.gcd_dvd_left _ _)
    have e2 : (p:ℤ) ∣ ((a:ℤ)*(b:ℤ)) - ((c:ℤ)*(d:ℤ)) := h3.trans (Int.gcd_dvd_right _ _)
    constructor
    · have hs : (a+b) ≡ (c+d) [MOD p] :=
        (int_dvd_sub_iff_modEq p (a+b) (c+d)).mp (by convert e1 using 2 <;> push_cast <;> ring)
      rw [← Nat.cast_add, ← Nat.cast_add]
      exact (ZMod.natCast_eq_natCast_iff (a+b) (c+d) p).mpr hs
    · have hpr : (a*b) ≡ (c*d) [MOD p] :=
        (int_dvd_sub_iff_modEq p (a*b) (c*d)).mp (by convert e2 using 2 <;> push_cast <;> ring)
      rw [← Nat.cast_mul, ← Nat.cast_mul]
      exact (ZMod.natCast_eq_natCast_iff (a*b) (c*d) p).mpr hpr
  · rintro ⟨h1, h2⟩
    refine ⟨Int.dvd_gcd ?_ ?_, hpq⟩
    · apply (int_dvd_sub_iff_modEq p (a+b) (c+d)).mpr
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [h1]
    · apply (int_dvd_sub_iff_modEq p (a*b) (c*d)).mpr
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [h2]

/-- If `p` (prime, `p ∣ q`) divides `Eg1`, then the multisets `{a,b}`, `{c,d}` agree mod `p`. -/
lemma Eg1_dvd_or {p q a b c d : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    (h : p ∣ Eg1 q a b c d) :
    (a ≡ c [MOD p] ∧ b ≡ d [MOD p]) ∨ (a ≡ d [MOD p] ∧ b ≡ c [MOD p]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h' := (dvd_Eg1_iff hpq).mp h
  rcases (add_mul_eq_iff_swap p a b c d).mp h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨(ZMod.natCast_eq_natCast_iff a c p).mp e1,
      (ZMod.natCast_eq_natCast_iff b d p).mp e2⟩
  · exact Or.inr ⟨(ZMod.natCast_eq_natCast_iff a d p).mp e1,
      (ZMod.natCast_eq_natCast_iff b c p).mp e2⟩

lemma Eg0_dvd_q (q a b c d : ℕ) : Eg0 q a b c d ∣ q := Nat.gcd_dvd_right _ _
lemma Eg1_dvd_q (q a b c d : ℕ) : Eg1 q a b c d ∣ q := Nat.gcd_dvd_right _ _

lemma lcm_Eg_dvd_q (q a b c d : ℕ) :
    Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) ∣ q :=
  Nat.lcm_dvd (Eg0_dvd_q q a b c d) (Eg1_dvd_q q a b c d)

/-- Real indicator of `a ≡ b` and `c ≡ d` modulo `p`. -/
noncomputable def xind (p a b c d : ℕ) : ℝ :=
  if (a ≡ b [MOD p] ∧ c ≡ d [MOD p]) then 1 else 0

/-- Real indicator of `{a,b} = {c,d}` modulo `p`. -/
noncomputable def yind (p a b c d : ℕ) : ℝ :=
  if ((a ≡ c [MOD p] ∧ b ≡ d [MOD p]) ∨ (a ≡ d [MOD p] ∧ b ≡ c [MOD p])) then 1 else 0

lemma xind_eq (p a b c d : ℕ) :
    xind p a b c d
      = (if a ≡ b [MOD p] then (1:ℝ) else 0) * (if c ≡ d [MOD p] then (1:ℝ) else 0) := by
  unfold xind; rw [ind_mul]

lemma yind_le (p a b c d : ℕ) :
    yind p a b c d
      ≤ (if a ≡ c [MOD p] then (1:ℝ) else 0) * (if b ≡ d [MOD p] then (1:ℝ) else 0)
        + (if a ≡ d [MOD p] then (1:ℝ) else 0) * (if b ≡ c [MOD p] then (1:ℝ) else 0) := by
  unfold yind
  by_cases h : (a ≡ c [MOD p] ∧ b ≡ d [MOD p]) ∨ (a ≡ d [MOD p] ∧ b ≡ c [MOD p])
  · rw [if_pos h]
    rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have hterm : (if a ≡ c [MOD p] then (1:ℝ) else 0) * (if b ≡ d [MOD p] then (1:ℝ) else 0) = 1 := by
        simp [h1, h2]
      rw [hterm]
      have h2' : (0:ℝ) ≤ (if a ≡ d [MOD p] then (1:ℝ) else 0) * (if b ≡ c [MOD p] then (1:ℝ) else 0) :=
        mul_nonneg (by positivity) (by positivity)
      linarith
    · have hterm : (if a ≡ d [MOD p] then (1:ℝ) else 0) * (if b ≡ c [MOD p] then (1:ℝ) else 0) = 1 := by
        simp [h1, h2]
      rw [hterm]
      have h1' : (0:ℝ) ≤ (if a ≡ c [MOD p] then (1:ℝ) else 0) * (if b ≡ d [MOD p] then (1:ℝ) else 0) :=
        mul_nonneg (by positivity) (by positivity)
      linarith
  · rw [if_neg h]
    have h1 : (0:ℝ) ≤ (if a ≡ c [MOD p] then (1:ℝ) else 0) * (if b ≡ d [MOD p] then (1:ℝ) else 0) :=
      mul_nonneg (by positivity) (by positivity)
    have h2 : (0:ℝ) ≤ (if a ≡ d [MOD p] then (1:ℝ) else 0) * (if b ≡ c [MOD p] then (1:ℝ) else 0) :=
      mul_nonneg (by positivity) (by positivity)
    linarith

lemma prod_ind_modEq_eq (A : Finset ℕ) (hcop : (A : Set ℕ).Pairwise Nat.Coprime) (a b : ℕ) :
    (∏ p ∈ A, (if a ≡ b [MOD p] then (1:ℝ) else 0))
      = (if a ≡ b [MOD ∏ p ∈ A, p] then (1:ℝ) else 0) := by
  rw [Finset.prod_boole]
  by_cases h : ∀ p ∈ A, a ≡ b [MOD p]
  · rw [if_pos h, if_pos (modEq_prod_of_coprime hcop h)]
  · rw [if_neg h, if_neg (fun hh => h (fun p hp =>
      hh.of_dvd (Finset.dvd_prod_of_mem (fun x => x) hp)))]

lemma prod_xind_eq (A : Finset ℕ) (hcop : (A : Set ℕ).Pairwise Nat.Coprime) (a b c d : ℕ) :
    (∏ p ∈ A, xind p a b c d)
      = (if a ≡ b [MOD ∏ p ∈ A, p] then (1:ℝ) else 0)
        * (if c ≡ d [MOD ∏ p ∈ A, p] then (1:ℝ) else 0) := by
  rw [Finset.prod_congr rfl (fun p _ => xind_eq p a b c d), Finset.prod_mul_distrib,
      prod_ind_modEq_eq A hcop a b, prod_ind_modEq_eq A hcop c d]

/-! ## Part 5a: the pointwise bound `√(lcm Eg0 Eg1) ≤ ∏ (1 + (√p-1)(x+y))` -/

lemma xind_nonneg (p a b c d : ℕ) : 0 ≤ xind p a b c d := by unfold xind; positivity
lemma yind_nonneg (p a b c d : ℕ) : 0 ≤ yind p a b c d := by unfold yind; positivity
lemma xind_le_one (p a b c d : ℕ) : xind p a b c d ≤ 1 := by unfold xind; split <;> norm_num
lemma yind_le_one (p a b c d : ℕ) : yind p a b c d ≤ 1 := by unfold yind; split <;> norm_num

lemma sqrt_lcm_le_prod (q a b c d : ℕ) (hq : Squarefree q) :
    Real.sqrt (Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d))
      ≤ ∏ p ∈ q.primeFactors, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)) := by
  set L := Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d) with hLdef
  set P := q.primeFactors with hPdef
  have hq0 : q ≠ 0 := squarefree_ne_zero hq
  have hLq : L ∣ q := lcm_Eg_dvd_q q a b c d
  have hL0 : L ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hLq))
  have hLsq : Squarefree L := Squarefree.squarefree_of_dvd hLq hq
  have hsqrt : Real.sqrt L = ∏ p ∈ L.primeFactors, Real.sqrt (p:ℝ) := by
    have h1 : ((∏ p ∈ L.primeFactors, p : ℕ) : ℝ) = (L:ℝ) := by
      rw [Nat.prod_primeFactors_of_squarefree hLsq]
    calc Real.sqrt (L:ℝ) = Real.sqrt ((∏ p ∈ L.primeFactors, p : ℕ) : ℝ) := by rw [h1]
      _ = Real.sqrt (∏ p ∈ L.primeFactors, ((p:ℕ):ℝ)) := by rw [Nat.cast_prod]
      _ = ∏ p ∈ L.primeFactors, Real.sqrt ((p:ℕ):ℝ) := Real.sqrt_prod _ (fun p hp => by positivity)
  have hpf : L.primeFactors = P.filter (fun p => p ∣ L) := by
    ext p
    simp only [hPdef, Nat.mem_primeFactors, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpL, _⟩
      exact ⟨⟨hp, hpL.trans hLq, hq0⟩, hpL⟩
    · rintro ⟨⟨hp, hpq, _⟩, hpL⟩
      exact ⟨hp, hpL, hL0⟩
  rw [hsqrt, hpf, Finset.prod_filter]
  apply Finset.prod_le_prod₀
  · intro p hp
    by_cases h : p ∣ L
    · rw [if_pos h]; exact Real.sqrt_nonneg _
    · rw [if_neg h]; norm_num
  · intro p hP
    rw [hPdef, Nat.mem_primeFactors] at hP
    obtain ⟨hpp, hpq, _⟩ := hP
    have hsqrt1 : (1:ℝ) ≤ Real.sqrt p := Real.one_le_sqrt.mpr (by exact_mod_cast hpp.one_le)
    have hxnn : 0 ≤ xind p a b c d := xind_nonneg p a b c d
    have hynn : 0 ≤ yind p a b c d := yind_nonneg p a b c d
    by_cases h : p ∣ L
    · rw [if_pos h]
      have hxy : 1 ≤ xind p a b c d + yind p a b c d := by
        rcases (hpp.dvd_lcm).mp h with h0 | h1
        · have hcond := (dvd_Eg0_iff hpq).mp h0
          have hx : xind p a b c d = 1 := by unfold xind; rw [if_pos hcond]
          linarith
        · have hy : yind p a b c d = 1 := by
            unfold yind; rw [if_pos (Eg1_dvd_or hpp hpq h1)]
          linarith
      nlinarith [hsqrt1, hxy]
    · rw [if_neg h]
      have : 0 ≤ (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d) :=
        mul_nonneg (by linarith) (by linarith)
      linarith

/-! ## Part 5b: swapping a fourfold `ℕ`-sum with a `Finset`-sum -/

lemma swap_four {ι : Type*} (s : Finset ℕ) (c : Finset ι) (f : ℕ → ℕ → ℕ → ℕ → ι → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ d ∈ s, ∑ C ∈ c, f a b c' d C)
      = (∑ C ∈ c, ∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ d ∈ s, f a b c' d C) := by
  have h1 : (∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ d ∈ s, ∑ C ∈ c, f a b c' d C)
          = (∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ C ∈ c, ∑ d ∈ s, f a b c' d C) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c' _
    exact Finset.sum_comm
  rw [h1]
  have h2 : (∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ C ∈ c, ∑ d ∈ s, f a b c' d C)
          = (∑ a ∈ s, ∑ b ∈ s, ∑ C ∈ c, ∑ c' ∈ s, ∑ d ∈ s, f a b c' d C) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    exact Finset.sum_comm
  rw [h2]
  have h3 : (∑ a ∈ s, ∑ b ∈ s, ∑ C ∈ c, ∑ c' ∈ s, ∑ d ∈ s, f a b c' d C)
          = (∑ a ∈ s, ∑ C ∈ c, ∑ b ∈ s, ∑ c' ∈ s, ∑ d ∈ s, f a b c' d C) := by
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [h3]
  exact Finset.sum_comm

/-! ## Part 5c: the counting bound for `∑ X_A Y_B` -/

lemma two_sum_mul_const (P : Finset ℕ) (c : ℝ) (f : Finset ℕ → Finset ℕ → ℝ) :
    (∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset, c * f A B)
      = c * (∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset, f A B) := by
  simp only [Finset.mul_sum]

lemma four_sum_mul_const (s : Finset ℕ) (c : ℝ) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ d ∈ s, c * f a b c' d)
      = c * (∑ a ∈ s, ∑ b ∈ s, ∑ c' ∈ s, ∑ d ∈ s, f a b c' d) := by
  simp only [Finset.mul_sum]

lemma pairwise_coprime_of_prime {A : Finset ℕ} (h : ∀ p ∈ A, p.Prime) :
    (A : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (h p hp) (h q hq)).mpr hpq

lemma coprime_prod_disjoint {A B : Finset ℕ} (hdisj : Disjoint A B)
    (h : ∀ p ∈ A ∪ B, p.Prime) : Nat.Coprime (∏ p ∈ A, p) (∏ p ∈ B, p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  have hp' : p.Prime := h p (Finset.mem_union_left _ hp)
  have hq' : q.Prime := h q (Finset.mem_union_right _ hq)
  exact (Nat.coprime_primes hp' hq').mpr (fun hh => (Finset.disjoint_left.mp hdisj) hp (hh ▸ hq))

lemma prod_pair_ind_eq (C : Finset ℕ) (hcop : (C : Set ℕ).Pairwise Nat.Coprime)
    (x y z w : ℕ) :
    (∏ p ∈ C, ((if x ≡ y [MOD p] then (1:ℝ) else 0) * (if z ≡ w [MOD p] then (1:ℝ) else 0)))
      = (if x ≡ y [MOD ∏ p ∈ C, p] then (1:ℝ) else 0)
        * (if z ≡ w [MOD ∏ p ∈ C, p] then (1:ℝ) else 0) := by
  rw [Finset.prod_mul_distrib, prod_ind_modEq_eq C hcop x y, prod_ind_modEq_eq C hcop z w]

lemma count_XY_le (H : ℕ) (A B : Finset ℕ) (hdisj : Disjoint A B)
    (hprime : ∀ p ∈ A ∪ B, p.Prime) :
    (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H, ∑ d ∈ Finset.Icc 1 H,
        (∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d))
      ≤ (2:ℝ)^B.card
        * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1) * ((H:ℝ)/(∏ p ∈ B, p) + 1)
          * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1)) := by
  have hcopA : (A : Set ℕ).Pairwise Nat.Coprime :=
    pairwise_coprime_of_prime (fun p hp => hprime p (Finset.mem_union_left _ hp))
  have hstep : ∀ a b c d : ℕ,
      (∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d)
      ≤ ∑ C ∈ B.powerset,
          (if a ≡ b [MOD ∏ p∈A, p] then (1:ℝ) else 0) * (if c ≡ d [MOD ∏ p∈A, p] then (1:ℝ) else 0)
          * (if a ≡ c [MOD ∏ p∈C, p] then (1:ℝ) else 0) * (if b ≡ d [MOD ∏ p∈C, p] then (1:ℝ) else 0)
          * (if a ≡ d [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)
          * (if b ≡ c [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0) := by
    intro a b c d
    rw [prod_xind_eq A hcopA a b c d]
    have hY : (∏ p ∈ B, yind p a b c d)
        ≤ ∑ C ∈ B.powerset,
            ((if a ≡ c [MOD ∏ p∈C, p] then (1:ℝ) else 0)
              * (if b ≡ d [MOD ∏ p∈C, p] then (1:ℝ) else 0))
            * ((if a ≡ d [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)
              * (if b ≡ c [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)) := by
      calc (∏ p ∈ B, yind p a b c d)
          ≤ ∏ p ∈ B, (((if a ≡ c [MOD p] then (1:ℝ) else 0)
                * (if b ≡ d [MOD p] then (1:ℝ) else 0))
              + ((if a ≡ d [MOD p] then (1:ℝ) else 0)
                * (if b ≡ c [MOD p] then (1:ℝ) else 0))) :=
            Finset.prod_le_prod₀ (fun p _ => yind_nonneg p a b c d) (fun p _ => yind_le p a b c d)
        _ = ∑ C ∈ B.powerset,
              (∏ p ∈ C, ((if a ≡ c [MOD p] then (1:ℝ) else 0)
                * (if b ≡ d [MOD p] then (1:ℝ) else 0)))
              * (∏ p ∈ B\C, ((if a ≡ d [MOD p] then (1:ℝ) else 0)
                * (if b ≡ c [MOD p] then (1:ℝ) else 0))) :=
            Finset.prod_add _ _ B
        _ = ∑ C ∈ B.powerset,
              ((if a ≡ c [MOD ∏ p∈C, p] then (1:ℝ) else 0)
                * (if b ≡ d [MOD ∏ p∈C, p] then (1:ℝ) else 0))
              * ((if a ≡ d [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)
                * (if b ≡ c [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)) := by
            apply Finset.sum_congr rfl; intro C hC
            have hCB : C ⊆ B := Finset.mem_powerset.mp hC
            have hcopC : (C : Set ℕ).Pairwise Nat.Coprime :=
              pairwise_coprime_of_prime (fun p hp => hprime p (Finset.mem_union_right _ (hCB hp)))
            have hcopBC : (((B\C : Finset ℕ)) : Set ℕ).Pairwise Nat.Coprime :=
              pairwise_coprime_of_prime (fun p hp =>
                hprime p (Finset.mem_union_right _ (Finset.mem_sdiff.mp hp).1))
            rw [prod_pair_ind_eq C hcopC a c b d, prod_pair_ind_eq (B\C) hcopBC a d b c]
    refine le_trans (mul_le_mul_of_nonneg_left hY (by positivity)) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro C hC
    exact le_of_eq (by ring)
  calc (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H, ∑ d ∈ Finset.Icc 1 H,
        (∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d))
      ≤ ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H, ∑ d ∈ Finset.Icc 1 H,
          ∑ C ∈ B.powerset,
          (if a ≡ b [MOD ∏ p∈A, p] then (1:ℝ) else 0) * (if c ≡ d [MOD ∏ p∈A, p] then (1:ℝ) else 0)
          * (if a ≡ c [MOD ∏ p∈C, p] then (1:ℝ) else 0) * (if b ≡ d [MOD ∏ p∈C, p] then (1:ℝ) else 0)
          * (if a ≡ d [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)
          * (if b ≡ c [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0) := by
        apply Finset.sum_le_sum; intro a _
        apply Finset.sum_le_sum; intro b _
        apply Finset.sum_le_sum; intro c _
        apply Finset.sum_le_sum; intro d _
        exact hstep a b c d
    _ = ∑ C ∈ B.powerset, ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          ∑ d ∈ Finset.Icc 1 H,
          (if a ≡ b [MOD ∏ p∈A, p] then (1:ℝ) else 0) * (if c ≡ d [MOD ∏ p∈A, p] then (1:ℝ) else 0)
          * (if a ≡ c [MOD ∏ p∈C, p] then (1:ℝ) else 0) * (if b ≡ d [MOD ∏ p∈C, p] then (1:ℝ) else 0)
          * (if a ≡ d [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0)
          * (if b ≡ c [MOD ∏ p∈(B\C), p] then (1:ℝ) else 0) :=
        swap_four _ _ _
    _ ≤ ∑ C ∈ B.powerset, (H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1) * ((H:ℝ)/(∏ p ∈ B, p) + 1)
          * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1) := by
        apply Finset.sum_le_sum; intro C hC
        have hCB : C ⊆ B := Finset.mem_powerset.mp hC
        have hdisjAC : Disjoint A C := Finset.disjoint_left.mpr
          (fun x hxA hxC => (Finset.disjoint_left.mp hdisj) hxA (hCB hxC))
        have hdisjABC : Disjoint A (B\C) := Finset.disjoint_left.mpr
          (fun x hxA hxBC => (Finset.disjoint_left.mp hdisj) hxA (Finset.mem_sdiff.mp hxBC).1)
        have hdisjCBC : Disjoint C (B\C) := Finset.disjoint_left.mpr
          (fun x hxC hxBC => (Finset.mem_sdiff.mp hxBC).2 hxC)
        have hprAC : ∀ p ∈ A ∪ C, p.Prime := by
          intro p hp
          rcases Finset.mem_union.mp hp with h | h
          · exact hprime p (Finset.mem_union_left _ h)
          · exact hprime p (Finset.mem_union_right _ (hCB h))
        have hprABC : ∀ p ∈ A ∪ (B\C), p.Prime := by
          intro p hp
          rcases Finset.mem_union.mp hp with h | h
          · exact hprime p (Finset.mem_union_left _ h)
          · exact hprime p (Finset.mem_union_right _ (Finset.mem_sdiff.mp h).1)
        have hprCBC : ∀ p ∈ C ∪ (B\C), p.Prime := by
          intro p hp
          rcases Finset.mem_union.mp hp with h | h
          · exact hprime p (Finset.mem_union_right _ (hCB h))
          · exact hprime p (Finset.mem_union_right _ (Finset.mem_sdiff.mp h).1)
        have hpAC : Nat.Coprime (∏ p ∈ A, p) (∏ p ∈ C, p) := coprime_prod_disjoint hdisjAC hprAC
        have hpABC : Nat.Coprime (∏ p ∈ A, p) (∏ p ∈ B\C, p) := coprime_prod_disjoint hdisjABC hprABC
        have hpCBC : Nat.Coprime (∏ p ∈ C, p) (∏ p ∈ B\C, p) := coprime_prod_disjoint hdisjCBC hprCBC
        have hu : 0 < ∏ p ∈ A, p :=
          Finset.prod_pos (fun p hp => (hprime p (Finset.mem_union_left _ hp)).pos)
        have hw : 0 < ∏ p ∈ C, p :=
          Finset.prod_pos (fun p hp => (hprime p (Finset.mem_union_right _ (hCB hp))).pos)
        have hw' : 0 < ∏ p ∈ B\C, p :=
          Finset.prod_pos (fun p hp =>
            (hprime p (Finset.mem_union_right _ (Finset.mem_sdiff.mp hp).1)).pos)
        have h1 : ((∏ p ∈ C, p) * (∏ p ∈ B\C, p) : ℕ) = ∏ p ∈ B, p := by
          rw [mul_comm (∏ p ∈ C, p) (∏ p ∈ B\C, p)]
          exact Finset.prod_sdiff hCB
        have h1R : ((∏ p ∈ C, p : ℕ) : ℝ) * ((∏ p ∈ B\C, p : ℕ) : ℝ)
            = ((∏ p ∈ B, p : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, h1]
        have heq : (H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1) * ((H:ℝ)/((∏ p ∈ C, p) * (∏ p ∈ B\C, p)) + 1)
              * ((H:ℝ)/((∏ p ∈ A, p) * (∏ p ∈ C, p) * (∏ p ∈ B\C, p)) + 1)
            = (H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1) * ((H:ℝ)/(∏ p ∈ B, p) + 1)
              * ((H:ℝ)/((∏ p ∈ A, p) * (∏ p ∈ B, p)) + 1) := by
          rw [h1R]
          rw [show ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ C, p : ℕ) : ℝ) * ((∏ p ∈ B\C, p : ℕ) : ℝ)
              = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) by
                rw [mul_assoc, h1R]]
        exact (sum_T3_le H (∏ p ∈ A, p) (∏ p ∈ C, p) (∏ p ∈ B\C, p) hu hw hw' hpAC hpABC hpCBC).trans (le_of_eq heq)
    _ = (2:ℝ)^B.card
        * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1) * ((H:ℝ)/(∏ p ∈ B, p) + 1)
          * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
        push_cast; ring

/-! ## Part 5d: product bounds for the expansion of `Q` -/

lemma inv_sqrt_eq (p : ℝ) (hp : 0 ≤ p) : (Real.sqrt p)⁻¹ = p^(-(1/2:ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp]

lemma sqrt_mul_inv_pow_le (p : ℝ) (hp : 1 ≤ p) (a : ℕ) (ha : 1 ≤ a) :
    Real.sqrt p * (p⁻¹)^a ≤ p^(-(1/2:ℝ)) := by
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le one_pos hp
  have haR : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hpa : p ^ a = p ^ (a:ℝ) := (Real.rpow_natCast p a).symm
  rw [Real.sqrt_eq_rpow, inv_pow, hpa, ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp
  linarith

lemma prod_factor_low (P : Finset ℕ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^a + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b)
      ≤ (4:ℝ)^P.card * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) := by
  have h1 : ∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^a + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b)
      ≤ ∏ p ∈ P, (4 * (1 + (p:ℝ)^(-(1/2:ℝ)))) := by
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hP p hp
      have hle1 := sqrt_mul_inv_pow_le p hp1 a ha
      have hle2 := sqrt_mul_inv_pow_le p hp1 b hb
      have hz : (0:ℝ) ≤ (p:ℝ)^(-(1/2:ℝ)) := by positivity
      nlinarith [hle1, hle2, hz]
  rw [Finset.prod_mul_distrib, Finset.prod_const] at h1
  exact h1

lemma prod_factor_high (P : Finset ℕ) (a b : ℕ) (h : a = 0 ∨ b = 0)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^a + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b)
      ≤ (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ)) * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) := by
  have h1 : ∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^a + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b)
      ≤ ∏ p ∈ P, (4 * Real.sqrt p) := by
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hP p hp
      have hsq : (1:ℝ) ≤ Real.sqrt p := Real.one_le_sqrt.mpr hp1
      have hinv0 : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
      have hinva : ((p:ℝ)⁻¹)^a ≤ 1 := pow_le_one₀ hinv0 (inv_le_one_of_one_le₀ hp1)
      have hinvb : ((p:ℝ)⁻¹)^b ≤ 1 := pow_le_one₀ hinv0 (inv_le_one_of_one_le₀ hp1)
      have hpa : 0 ≤ Real.sqrt p * ((p:ℝ)⁻¹)^a := by positivity
      have hpb : 0 ≤ Real.sqrt p * ((p:ℝ)⁻¹)^b := by positivity
      have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
      nlinarith [hsq, hinva, hinvb, hpa, hpb, hs0]
  have h2 : ∏ p ∈ P, (4 * Real.sqrt p) = (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.sqrt_prod]
    intro p hp; positivity
  rw [h2] at h1
  refine h1.trans ?_
  have hge1 : (1:ℝ) ≤ ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) := by
    apply Finset.one_le_prod₀
    intro p hp
    have : (0:ℝ) ≤ (p:ℝ)^(-(1/2:ℝ)) := by positivity
    linarith
  calc (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ))
      = (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ)) * 1 := by ring
    _ ≤ (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ)) * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) := by
        apply mul_le_mul_of_nonneg_left hge1 (by positivity)

lemma two_pow_primeFactors_card_le (q : ℕ) (hq : Squarefree q) :
    (2:ℕ)^q.primeFactors.card ≤ q.divisors.card := by
  have hq0 : q ≠ 0 := squarefree_ne_zero hq
  rw [Nat.card_divisors hq0]
  calc (2:ℕ)^q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := (Finset.prod_const (2:ℕ)).symm
    _ ≤ ∏ p ∈ q.primeFactors, (q.factorization p + 1) := by
        apply Finset.prod_le_prod₀
        · intro p hp; norm_num
        · intro p hp
          rw [Nat.mem_primeFactors] at hp
          have h1 : 1 ≤ q.factorization p :=
            Nat.Prime.factorization_pos_of_dvd hp.1 hp.2.2 hp.2.1
          omega

/-! ## Part 6: the main theorem -/

theorem lcm_gcd_count_sqfree {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q H : ℕ), Squarefree q → H ≤ q →
      (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
        ∑ d ∈ Finset.Icc 1 H,
        Real.sqrt (Nat.lcm (Nat.gcd (Int.gcd ((a:ℤ) - (b:ℤ)) ((c:ℤ) - (d:ℤ))) q)
          (Nat.gcd (Int.gcd (((a:ℤ) + (b:ℤ)) - ((c:ℤ) + (d:ℤ)))
            ((a:ℤ) * (b:ℤ) - (c:ℤ) * (d:ℤ))) q)))
      ≤ C * (q : ℝ) ^ ε * ((H : ℝ)^4 + (H : ℝ)^2 * Real.sqrt (q : ℝ)) := by
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨C1, hC1pos, hC1⟩ := prod_primeFactors_one_add_rpow_le' (σ := (1:ℝ)/2) (by norm_num) hδ
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow δ hδ
  refine ⟨5 * C1 * C2^2 + 1, by positivity, ?_⟩
  intro q H hq hH
  have hq0 : q ≠ 0 := squarefree_ne_zero hq
  have hq1n : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1n
  -- handle H = 0
  rcases Nat.eq_zero_or_pos H with hH0 | hHpos
  · subst hH0
    have hI : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by decide
    simp only [hI, Finset.sum_empty]
    positivity
  -- main case H ≥ 1
  have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hHpos
  have hH4nn : (0:ℝ) ≤ (H:ℝ)^4 := by positivity
  have hH2sqrtnn : (0:ℝ) ≤ (H:ℝ)^2 * Real.sqrt (q:ℝ) := by positivity
  have htarget : (0:ℝ) ≤ (H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ) := by positivity
  -- constants
  have h2w : (2:ℝ)^q.primeFactors.card ≤ C2 * (q:ℝ)^δ := by
    have h1 : (2:ℕ)^q.primeFactors.card ≤ q.divisors.card := two_pow_primeFactors_card_le q hq
    calc (2:ℝ)^q.primeFactors.card = ((2:ℕ)^q.primeFactors.card : ℝ) := by push_cast; ring
      _ ≤ ((q.divisors.card : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ C2 * (q:ℝ)^δ := hC2 q
  have h4w : (4:ℝ)^q.primeFactors.card ≤ C2^2 * (q:ℝ)^(2*δ) := by
    have h4eq : (4:ℝ)^q.primeFactors.card = ((2:ℝ)^q.primeFactors.card)^2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow, sq]
    rw [h4eq]
    calc ((2:ℝ)^q.primeFactors.card)^2 ≤ (C2 * (q:ℝ)^δ)^2 := by
          gcongr
      _ = C2^2 * (q:ℝ)^(2*δ) := by
          have h1 : (q:ℝ)^(2*δ) = ((q:ℝ)^δ)^2 := by
            rw [show (2:ℝ)*δ = δ + δ by ring, Real.rpow_add (by positivity : (0:ℝ) < q), sq]
          rw [h1, mul_pow]
  have hprod1 : ∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-(1/2:ℝ))) ≤ C1 * (q:ℝ)^δ := hC1 q hq0
  have hsqrtq : Real.sqrt (∏ p ∈ q.primeFactors, (p:ℝ)) = Real.sqrt (q:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
  -- The main bound
  have key : (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
        ∑ d ∈ Finset.Icc 1 H, Real.sqrt (Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d)))
      ≤ 5 * C1 * C2^2 * (q:ℝ)^(3*δ) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)) := by
    set P : Finset ℕ := q.primeFactors with hPdef
    have hPmem : ∀ p ∈ P, p.Prime := by
      intro p hp; rw [hPdef] at hp; exact (Nat.mem_primeFactors.mp hp).1
    have hPge1 : ∀ p ∈ P, 1 ≤ p := fun p hp => (hPmem p hp).one_le
    have hPcard : P.card = q.primeFactors.card := by rw [hPdef]
    -- Step 1: S ≤ ∑_t W(t)
    have hW1 : (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          ∑ d ∈ Finset.Icc 1 H, Real.sqrt (Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d)))
        ≤ ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          ∑ d ∈ Finset.Icc 1 H,
            ∏ p ∈ P, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro d _
      rw [hPdef]
      exact sqrt_lcm_le_prod q a b c d hq
    -- Step 2: expansion of W and swap
    have hpt : ∀ a b c d : ℕ,
        (∏ p ∈ P, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)))
          = ∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
              (∏ p ∈ A, (Real.sqrt p - 1) * xind p a b c d)
                * (∏ p ∈ B, (Real.sqrt p - 1) * yind p a b c d) := by
      intro a b c d
      rw [show (∏ p ∈ P, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)))
          = ∏ p ∈ P, (1 + (Real.sqrt p - 1) * xind p a b c d
              + (Real.sqrt p - 1) * yind p a b c d) from by
            apply Finset.prod_congr rfl; intro p hp; ring]
      exact (sum_powerset_disjoint_prod P (fun p => (Real.sqrt p - 1) * xind p a b c d)
        (fun p => (Real.sqrt p - 1) * yind p a b c d)).symm
    have hW2 : (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
          ∑ d ∈ Finset.Icc 1 H,
            ∏ p ∈ P, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)))
        ≤ ∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
            ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
            * ((2:ℝ)^B.card * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1)
                * ((H:ℝ)/(∏ p ∈ B, p) + 1)
                * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1))) := by
      have hexp : (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
            ∑ d ∈ Finset.Icc 1 H,
              ∏ p ∈ P, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)))
          = ∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
              ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
                * (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
                    ∑ d ∈ Finset.Icc 1 H,
                      (∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d)) := by
        have h1 : (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
              ∑ d ∈ Finset.Icc 1 H,
                ∏ p ∈ P, (1 + (Real.sqrt p - 1) * (xind p a b c d + yind p a b c d)))
            = ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
              ∑ d ∈ Finset.Icc 1 H, ∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
                ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
                  * ((∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d)) := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro d _
          rw [hpt a b c d]
          apply Finset.sum_congr rfl; intro A hA
          apply Finset.sum_congr rfl; intro B hB
          simp only [Finset.prod_mul_distrib]; ring
        rw [h1]
        rw [swap_four _ P.powerset (fun a b c d A => ∑ B ∈ (P \ A).powerset,
              ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
                * ((∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d)))]
        apply Finset.sum_congr rfl; intro A hA
        rw [swap_four _ (P \ A).powerset (fun a b c d B =>
              ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
                * ((∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d)))]
        apply Finset.sum_congr rfl; intro B hB
        rw [four_sum_mul_const (Finset.Icc 1 H) ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
              (fun a b c d => (∏ p ∈ A, xind p a b c d) * (∏ p ∈ B, yind p a b c d))]
      rw [hexp]
      apply Finset.sum_le_sum; intro A hA
      apply Finset.sum_le_sum; intro B hB
      have hdisj : Disjoint A B := Finset.disjoint_left.mpr
        (fun x hxA hxB => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB hxB)).2 hxA)
      have hprime : ∀ p ∈ A ∪ B, p.Prime := by
        intro p hp
        rcases Finset.mem_union.mp hp with h | h
        · exact hPmem p (Finset.mem_powerset.mp hA h)
        · exact hPmem p (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB h)).1
      have hwAnn : (0:ℝ) ≤ (∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)) :=
        mul_nonneg
          (Finset.prod_nonneg (fun p hp => by
            have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPge1 p (Finset.mem_powerset.mp hA hp)
            have := Real.one_le_sqrt.mpr hp1; linarith))
          (Finset.prod_nonneg (fun p hp => by
            have hp1 : (1:ℝ) ≤ (p:ℝ) := by
              exact_mod_cast hPge1 p (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB hp)).1
            have := Real.one_le_sqrt.mpr hp1; linarith))
      apply mul_le_mul_of_nonneg_left _ hwAnn
      exact count_XY_le H A B hdisj hprime

    have hTTsum : ∀ a b : ℕ, (∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
          (∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^a) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b))
        = ∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^a + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b) := by
      intro a b
      exact sum_powerset_disjoint_prod P (fun p => Real.sqrt p * ((p:ℝ)⁻¹)^a)
        (fun p => 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b)
    have hpoint : ∀ A B : Finset ℕ, A ⊆ P → B ⊆ P →
        ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
          * ((2:ℝ)^B.card * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1)
              * ((H:ℝ)/(∏ p ∈ B, p) + 1)
              * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1)))
        ≤ (H:ℝ)^4 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^2) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^2))
          + (H:ℝ)^3 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^1) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ)^3 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^2) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ)^2 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^1) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^0))
          + (H:ℝ)^3 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^1) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^2))
          + (H:ℝ)^2 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^0) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ)^2 * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^1) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ) * ((∏ p ∈ A, Real.sqrt p * ((p:ℝ)⁻¹)^0) * (∏ p ∈ B, 2 * Real.sqrt p * ((p:ℝ)⁻¹)^0)) := by
      intro A B hAP hBP
      set U : ℝ := ((∏ p ∈ A, p : ℕ) : ℝ) with hU
      set V : ℝ := ((∏ p ∈ B, p : ℕ) : ℝ) with hV
      have hU0 : U ≠ 0 := by
        rw [hU]
        exact_mod_cast (Finset.prod_pos (fun p hp => (hPmem p (hAP hp)).pos)).ne'
      have hV0 : V ≠ 0 := by
        rw [hV]
        exact_mod_cast (Finset.prod_pos (fun p hp => (hPmem p (hBP hp)).pos)).ne'
      have hUpow : ∀ a : ℕ, (U⁻¹)^a = ∏ p ∈ A, ((p:ℝ)⁻¹)^a := by
        intro a; rw [hU, Nat.cast_prod, ← Finset.prod_inv_distrib, Finset.prod_pow]
      have hVpow : ∀ b : ℕ, (V⁻¹)^b = ∏ p ∈ B, ((p:ℝ)⁻¹)^b := by
        intro b; rw [hV, Nat.cast_prod, ← Finset.prod_inv_distrib, Finset.prod_pow]
      have hwA : (∏ p ∈ A, (Real.sqrt p - 1)) ≤ ∏ p ∈ A, Real.sqrt p := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPge1 p (hAP hp)
          have := Real.one_le_sqrt.mpr hp1; linarith
        · intro p hp; linarith [Real.sqrt_nonneg (p:ℝ)]
      have hwB : (∏ p ∈ B, (Real.sqrt p - 1)) ≤ ∏ p ∈ B, Real.sqrt p := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPge1 p (hBP hp)
          have := Real.one_le_sqrt.mpr hp1; linarith
        · intro p hp; linarith [Real.sqrt_nonneg (p:ℝ)]
      have h2B : (2:ℝ)^B.card = ∏ p ∈ B, 2 := (Finset.prod_const (2:ℝ)).symm
      have hQ : (H:ℝ) * ((H:ℝ)/U + 1) * ((H:ℝ)/V + 1) * ((H:ℝ)/(U*V) + 1)
          = (H:ℝ)^4 * (U⁻¹)^2 * (V⁻¹)^2 + (H:ℝ)^3 * (U⁻¹)^1 * (V⁻¹)^1
            + (H:ℝ)^3 * (U⁻¹)^2 * (V⁻¹)^1 + (H:ℝ)^2 * (U⁻¹)^1 * (V⁻¹)^0
            + (H:ℝ)^3 * (U⁻¹)^1 * (V⁻¹)^2 + (H:ℝ)^2 * (U⁻¹)^0 * (V⁻¹)^1
            + (H:ℝ)^2 * (U⁻¹)^1 * (V⁻¹)^1 + (H:ℝ) * (U⁻¹)^0 * (V⁻¹)^0 := by
        field_simp
        ring
      have hUeq : U = ∏ p ∈ A, (p:ℝ) := by rw [hU, Nat.cast_prod]
      have hVeq : V = ∏ p ∈ B, (p:ℝ) := by rw [hV, Nat.cast_prod]
      have hwAnn : (0:ℝ) ≤ ∏ p ∈ A, Real.sqrt p := Finset.prod_nonneg (fun p hp => Real.sqrt_nonneg _)
      have hwBnn : (0:ℝ) ≤ ∏ p ∈ B, Real.sqrt p := Finset.prod_nonneg (fun p hp => Real.sqrt_nonneg _)
      have hB2nn : (0:ℝ) ≤ ∏ p ∈ B, 2 := Finset.prod_nonneg (fun p hp => by norm_num)
      have hQnn : (0:ℝ) ≤ (H:ℝ)^4 * (U⁻¹)^2 * (V⁻¹)^2 + (H:ℝ)^3 * (U⁻¹)^1 * (V⁻¹)^1
          + (H:ℝ)^3 * (U⁻¹)^2 * (V⁻¹)^1 + (H:ℝ)^2 * (U⁻¹)^1 * (V⁻¹)^0
          + (H:ℝ)^3 * (U⁻¹)^1 * (V⁻¹)^2 + (H:ℝ)^2 * (U⁻¹)^0 * (V⁻¹)^1
          + (H:ℝ)^2 * (U⁻¹)^1 * (V⁻¹)^1 + (H:ℝ) * (U⁻¹)^0 * (V⁻¹)^0 := by
        have hH0 : (0:ℝ) ≤ (H:ℝ) := by positivity
        have hu : (0:ℝ) ≤ U⁻¹ := by rw [hUeq]; positivity
        have hv : (0:ℝ) ≤ V⁻¹ := by rw [hVeq]; positivity
        have t1 : (0:ℝ) ≤ (H:ℝ)^4 * (U⁻¹)^2 * (V⁻¹)^2 := by positivity
        have t2 : (0:ℝ) ≤ (H:ℝ)^3 * U⁻¹ * V⁻¹ :=
          mul_nonneg (mul_nonneg (by positivity) hu) hv
        have t3 : (0:ℝ) ≤ (H:ℝ)^3 * (U⁻¹)^2 * V⁻¹ :=
          mul_nonneg (mul_nonneg (by positivity) (by positivity)) hv
        have t4 : (0:ℝ) ≤ (H:ℝ)^2 * U⁻¹ := mul_nonneg (by positivity) hu
        have t5 : (0:ℝ) ≤ (H:ℝ)^3 * U⁻¹ * (V⁻¹)^2 :=
          mul_nonneg (mul_nonneg (by positivity) hu) (by positivity)
        have t6 : (0:ℝ) ≤ (H:ℝ)^2 * V⁻¹ := mul_nonneg (by positivity) hv
        have t7 : (0:ℝ) ≤ (H:ℝ)^2 * U⁻¹ * V⁻¹ :=
          mul_nonneg (mul_nonneg (by positivity) hu) hv
        linarith [t1, t2, t3, t4, t5, t6, t7, hH0]
      have hwBnn0 : (0:ℝ) ≤ ∏ p ∈ B, (Real.sqrt p - 1) :=
        Finset.prod_nonneg (fun p hp => by
          have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPge1 p (hBP hp)
          have := Real.one_le_sqrt.mpr hp1; linarith)
      have hAB : (∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1))
          ≤ (∏ p ∈ A, Real.sqrt p) * (∏ p ∈ B, Real.sqrt p) :=
        mul_le_mul hwA hwB hwBnn0 hwAnn
      rw [show ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
            * ((2:ℝ)^B.card * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1)
                * ((H:ℝ)/(∏ p ∈ B, p) + 1)
                * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1)))
          = ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
            * ((2:ℝ)^B.card * ((H:ℝ) * ((H:ℝ)/U + 1) * ((H:ℝ)/V + 1) * ((H:ℝ)/(U*V) + 1)))
          from by rw [← hU, ← hV]]
      rw [h2B, hQ]
      refine (mul_le_mul_of_nonneg_right hAB (mul_nonneg hB2nn hQnn)).trans (le_of_eq ?_)
      rw [Finset.prod_mul_distrib]
      rw [hUpow 2, hVpow 2, hUpow 1, hVpow 1, hUpow 0, hVpow 0]
      simp only [Finset.prod_mul_distrib, pow_two, pow_one, pow_zero, Finset.prod_const_one, mul_one]
      ring
    have hsat : ∀ a b : ℕ,
        (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^a + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^b))
          ≤ (4:ℝ)^P.card * (if a = 0 ∨ b = 0 then Real.sqrt (∏ p ∈ P, (p:ℝ)) else 1)
              * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) := by
      intro a b
      by_cases h : a = 0 ∨ b = 0
      · rw [if_pos h]
        exact prod_factor_high P a b h hPge1
      · rw [if_neg h, mul_one]
        push_neg at h
        exact prod_factor_low P a b (by omega) (by omega) hPge1
    have hlow : (4:ℝ)^P.card * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ)))
        ≤ C1 * C2^2 * (q:ℝ)^(3*δ) := by
      have h4 : (4:ℝ)^P.card ≤ C2^2 * (q:ℝ)^(2*δ) := by rw [hPcard]; exact h4w
      have hp1 : ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) ≤ C1 * (q:ℝ)^δ := by rw [hPdef]; exact hprod1
      calc (4:ℝ)^P.card * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ)))
          ≤ C2^2 * (q:ℝ)^(2*δ) * (C1 * (q:ℝ)^δ) :=
            mul_le_mul h4 hp1 (by positivity) (by positivity)
        _ = C1 * C2^2 * (q:ℝ)^(3*δ) := by
            rw [show (3:ℝ)*δ = 2*δ + δ by ring, Real.rpow_add (by positivity : (0:ℝ) < q)]
            ring
    have hhigh : (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ)) * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ)))
        ≤ C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ) := by
      have h4 : (4:ℝ)^P.card ≤ C2^2 * (q:ℝ)^(2*δ) := by rw [hPcard]; exact h4w
      have hp1 : ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ))) ≤ C1 * (q:ℝ)^δ := by rw [hPdef]; exact hprod1
      have hs : Real.sqrt (∏ p ∈ P, (p:ℝ)) = Real.sqrt (q:ℝ) := by rw [hPdef]; exact hsqrtq
      calc (4:ℝ)^P.card * Real.sqrt (∏ p ∈ P, (p:ℝ)) * ∏ p ∈ P, (1 + (p:ℝ)^(-(1/2:ℝ)))
          ≤ C2^2 * (q:ℝ)^(2*δ) * Real.sqrt (q:ℝ) * (C1 * (q:ℝ)^δ) := by
            rw [hs]
            exact mul_le_mul (mul_le_mul h4 le_rfl (by positivity) (by positivity)) hp1
              (by positivity) (by positivity)
        _ = C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ) := by
            rw [show (3:ℝ)*δ = 2*δ + δ by ring, Real.rpow_add (by positivity : (0:ℝ) < q)]
            ring
    have hDsplit : (∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
          ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
          * ((2:ℝ)^B.card * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1)
              * ((H:ℝ)/(∏ p ∈ B, p) + 1)
              * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1))))
        ≤ 5 * C1 * C2^2 * (q:ℝ)^(3*δ) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)) := by
      have h1 : (∑ A ∈ P.powerset, ∑ B ∈ (P \ A).powerset,
          ((∏ p ∈ A, (Real.sqrt p - 1)) * (∏ p ∈ B, (Real.sqrt p - 1)))
          * ((2:ℝ)^B.card * ((H:ℝ) * ((H:ℝ)/(∏ p ∈ A, p) + 1)
              * ((H:ℝ)/(∏ p ∈ B, p) + 1)
              * ((H:ℝ)/((∏ p ∈ A, p)*(∏ p ∈ B, p)) + 1))))
        ≤ (H:ℝ)^4 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^2 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^2))
          + (H:ℝ)^3 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ)^3 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^2 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ)^2 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^0))
          + (H:ℝ)^3 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^2))
          + (H:ℝ)^2 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^0 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ)^2 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
          + (H:ℝ) * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^0 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^0)) := by
        refine (Finset.sum_le_sum (fun A hA => Finset.sum_le_sum (fun B hB =>
          hpoint A B (Finset.mem_powerset.mp hA)
            (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB hx)).1)))).trans (le_of_eq ?_)
        simp only [Finset.sum_add_distrib, two_sum_mul_const, hTTsum]
      have hE1 : (H:ℝ)^4 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^2 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^2))
            + (H:ℝ)^3 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
            + (H:ℝ)^3 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^2 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
            + (H:ℝ)^2 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^0))
            + (H:ℝ)^3 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^2))
            + (H:ℝ)^2 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^0 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
            + (H:ℝ)^2 * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^1 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^1))
            + (H:ℝ) * (∏ p ∈ P, (1 + Real.sqrt p * ((p:ℝ)⁻¹)^0 + 2 * Real.sqrt p * ((p:ℝ)⁻¹)^0))
          ≤ (H:ℝ)^4 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^3 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^3 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^2 * (C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ))
            + (H:ℝ)^3 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^2 * (C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ))
            + (H:ℝ)^2 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ) * (C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ)) := by
        have s22 := hsat 2 2; rw [if_neg (by norm_num : ¬ ((2:ℕ) = 0 ∨ (2:ℕ) = 0)), mul_one] at s22
        have s11 := hsat 1 1; rw [if_neg (by norm_num : ¬ ((1:ℕ) = 0 ∨ (1:ℕ) = 0)), mul_one] at s11
        have s21 := hsat 2 1; rw [if_neg (by norm_num : ¬ ((2:ℕ) = 0 ∨ (1:ℕ) = 0)), mul_one] at s21
        have s10 := hsat 1 0; rw [if_pos (by norm_num : ((1:ℕ) = 0 ∨ (0:ℕ) = 0))] at s10
        have s12 := hsat 1 2; rw [if_neg (by norm_num : ¬ ((1:ℕ) = 0 ∨ (2:ℕ) = 0)), mul_one] at s12
        have s01 := hsat 0 1; rw [if_pos (by norm_num : ((0:ℕ) = 0 ∨ (1:ℕ) = 0))] at s01
        have s00 := hsat 0 0; rw [if_pos (by norm_num : ((0:ℕ) = 0 ∨ (0:ℕ) = 0))] at s00
        have h22 := mul_le_mul_of_nonneg_left (s22.trans hlow) (by positivity : (0:ℝ) ≤ (H:ℝ)^4)
        have h11 := mul_le_mul_of_nonneg_left (s11.trans hlow) (by positivity : (0:ℝ) ≤ (H:ℝ)^3)
        have h21 := mul_le_mul_of_nonneg_left (s21.trans hlow) (by positivity : (0:ℝ) ≤ (H:ℝ)^3)
        have h10 := mul_le_mul_of_nonneg_left (s10.trans hhigh) (by positivity : (0:ℝ) ≤ (H:ℝ)^2)
        have h12 := mul_le_mul_of_nonneg_left (s12.trans hlow) (by positivity : (0:ℝ) ≤ (H:ℝ)^3)
        have h01 := mul_le_mul_of_nonneg_left (s01.trans hhigh) (by positivity : (0:ℝ) ≤ (H:ℝ)^2)
        have h00 := mul_le_mul_of_nonneg_left (s00.trans hhigh) (by positivity : (0:ℝ) ≤ (H:ℝ))
        have h11' := mul_le_mul_of_nonneg_left (s11.trans hlow) (by positivity : (0:ℝ) ≤ (H:ℝ)^2)
        linarith [h22, h11, h21, h10, h12, h01, h00, h11']
      have hE2 : (H:ℝ)^4 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^3 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^3 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^2 * (C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ))
            + (H:ℝ)^3 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ)^2 * (C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ))
            + (H:ℝ)^2 * (C1 * C2^2 * (q:ℝ)^(3*δ))
            + (H:ℝ) * (C1 * C2^2 * (q:ℝ)^(3*δ) * Real.sqrt (q:ℝ))
          ≤ 5 * C1 * C2^2 * (q:ℝ)^(3*δ) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)) := by
        have h0 : (0:ℝ) ≤ C1 * C2^2 * (q:ℝ)^(3*δ) := by positivity
        have hs0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
        have hH2 : (1:ℝ) ≤ (H:ℝ)^2 := by nlinarith [hH1]
        have hH3 : (H:ℝ)^3 ≤ (H:ℝ)^4 := by nlinarith [hH1]
        have hHs : (H:ℝ) ≤ (H:ℝ)^2 := by nlinarith [hH1]
        have hH4 : (H:ℝ)^2 ≤ (H:ℝ)^4 := by nlinarith [hH2, sq_nonneg ((H:ℝ)^2 - 1)]
        have hHs2 : (H:ℝ) * Real.sqrt (q:ℝ) ≤ (H:ℝ)^2 * Real.sqrt (q:ℝ) := by nlinarith [hs0, hHs]
        nlinarith [h0, hs0, hH1, hH2, hH3, hH4, hHs, hHs2]
      exact h1.trans (hE1.trans hE2)
    exact hW1.trans (hW2.trans hDsplit)

  have hexp : (q:ℝ)^(3*δ) ≤ (q:ℝ)^ε := by
    apply Real.rpow_le_rpow_of_exponent_le hq1
    rw [hδdef]; linarith
  calc (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H, ∑ c ∈ Finset.Icc 1 H,
        ∑ d ∈ Finset.Icc 1 H, Real.sqrt (Nat.lcm (Eg0 q a b c d) (Eg1 q a b c d)))
      ≤ 5 * C1 * C2^2 * (q:ℝ)^(3*δ) * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)) := key
    _ ≤ (5 * C1 * C2^2 + 1) * (q:ℝ)^ε * ((H:ℝ)^4 + (H:ℝ)^2 * Real.sqrt (q:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ htarget
        calc 5 * C1 * C2^2 * (q:ℝ)^(3*δ) ≤ 5 * C1 * C2^2 * (q:ℝ)^ε :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (5 * C1 * C2^2 + 1) * (q:ℝ)^ε := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith

end Commons.NumberTheory.DirichletCharacter
