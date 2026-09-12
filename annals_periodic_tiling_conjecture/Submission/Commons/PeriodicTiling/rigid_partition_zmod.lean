import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder

open Filter
open scoped Topology
open scoped Pointwise

namespace Commons.PeriodicTiling

instance {α : Type*} [Add α] : HAdd (Set α) α (Set α) where
  hAdd s a := {x | ∃ y ∈ s, x = y + a}

def pairA {p : ℕ} (h : ZMod p) (k : ℕ) : ZMod p := ((2 * (k + 1) : ℕ) : ZMod p) * h
def pairB {p : ℕ} (h : ZMod p) (k : ℕ) : ZMod p := ((2 * k + 1 : ℕ) : ZMod p) * h

lemma pairB_eq_pairA_sub {p : ℕ} (h : ZMod p) (k : ℕ) : pairB h k = pairA h k - h := by
  unfold pairA pairB
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one]
  ring

lemma cover {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (h : ZMod p) (hh : h ≠ 0)
    (x : ZMod p) :
    x = 0 ∨ ∃ k : Fin ((p - 1) / 2), x = pairA h k.val ∨ x = pairB h k.val := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    let m : ℕ := (p - 1) / 2
    have hp_eq : p = 2 * m + 1 := by
      dsimp [m]
      have hodd : Odd p := hp.odd_of_ne_two hp2
      rcases hodd with ⟨a, ha⟩
      have : a = (p - 1) / 2 := by omega
      omega
    let c : ZMod p := x * h⁻¹
    have hc : c ≠ 0 := by
      intro hc0
      have hxmul : x = c * h := by
        dsimp [c]
        calc
          x = x * 1 := by simp
          _ = x * (h⁻¹ * h) := by rw [inv_mul_cancel₀ hh]
          _ = (x * h⁻¹) * h := by ring
      rw [hc0, zero_mul] at hxmul
      exact hx hxmul
    have hvpos : 0 < c.val := ZMod.val_pos.mpr hc
    have hvlt : c.val < p := ZMod.val_lt c
    have hcoeff : ((c.val : ℕ) : ZMod p) = c := by
      exact ZMod.natCast_zmod_val c
    have hxmul : c * h = x := by
      dsimp [c]
      calc
        (x * h⁻¹) * h = x * (h⁻¹ * h) := by ring
        _ = x * 1 := by rw [inv_mul_cancel₀ hh]
        _ = x := by simp
    have hcases : (∃ k : Fin m, c.val = 2 * (k.val + 1)) ∨
                  (∃ k : Fin m, c.val = 2 * k.val + 1) := by
      rcases Nat.even_or_odd c.val with ⟨a, ha⟩ | ⟨a, ha⟩
      · left
        have hapos : 0 < a := by omega
        have hale : a ≤ m := by
          have : 2 * a < 2 * m + 1 := by omega
          omega
        have hmem : a - 1 < m := by omega
        refine ⟨⟨a - 1, hmem⟩, ?_⟩
        · simp; omega
      · right
        have halt : a < m := by
          have : 2 * a + 1 < 2 * m + 1 := by omega
          omega
        refine ⟨⟨a, halt⟩, ?_⟩
        · simp; omega
    rcases hcases with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k, Or.inl ?_⟩
      calc
        x = c * h := by rw [hxmul]
        _ = ((c.val : ℕ) : ZMod p) * h := by rw [hcoeff]
        _ = ((2 * (k.val + 1) : ℕ) : ZMod p) * h := by rw [hk]
        _ = pairA h k.val := rfl
    · refine ⟨k, Or.inr ?_⟩
      calc
        x = c * h := by rw [hxmul]
        _ = ((c.val : ℕ) : ZMod p) * h := by rw [hcoeff]
        _ = ((2 * k.val + 1 : ℕ) : ZMod p) * h := by rw [hk]
        _ = pairB h k.val := rfl

lemma code_injective {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (h : ZMod p) (hh : h ≠ 0)
    {M : ℕ} (a b : ZMod p → Fin M)
    (h0 : a 0 = b 0)
    (hpa : ∀ k : Fin ((p - 1) / 2), a (pairA h k.val) = b (pairA h k.val))
    (hpb : ∀ k : Fin ((p - 1) / 2), a (pairB h k.val) = b (pairB h k.val)) :
    a = b := by
  funext x
  rcases cover hp hp2 h hh x with rfl | ⟨k, hk⟩
  · exact h0
  · rcases hk with hk | hk
    · rw [hk]; exact hpa k
    · rw [hk]; exact hpb k

lemma bad_pair_card_le {p M : ℕ} [Fintype (ZMod p)] [DecidableEq (ZMod p)]
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (h : ZMod p) (hh : h ≠ 0)
    (i j : Fin M) :
    let m := (p - 1) / 2
    let bad : Finset (ZMod p → Fin M) := by
      classical
      exact Finset.univ.filter (fun a : ZMod p → Fin M => ∀ x : ZMod p, ¬ (a x = i ∧ a (x - h) = j))
    bad.card ≤ M * (M ^ 2 - 1) ^ m := by
  classical
  intro m bad
  let C := {c : Fin M × Fin M // c ≠ (i, j)}
  let cod := Fin M × (Fin m → C)
  have hbadcard : bad.card = Fintype.card {a : ZMod p → Fin M // a ∈ bad} := by
    rw [Fintype.card_of_subtype bad (fun _ => Iff.rfl)]
  have hemb : {a : ZMod p → Fin M // a ∈ bad} ↪ cod := by
    refine ⟨fun a => (a.1 0, fun k : Fin m => ⟨(a.1 (pairA h k.val), a.1 (pairB h k.val)), ?_⟩), ?_⟩
    · have hbad : ∀ x : ZMod p, ¬ (a.1 x = i ∧ a.1 (x - h) = j) := by
        have ha := a.2
        simpa [bad] using ha
      intro hpair
      have hmain := hbad (pairA h k.val)
      apply hmain
      have hpa : a.1 (pairA h k.val) = i := congrArg Prod.fst hpair
      have hpb : a.1 (pairA h k.val - h) = j := by
        rw [← pairB_eq_pairA_sub h k.val]
        exact congrArg Prod.snd hpair
      exact ⟨hpa, hpb⟩
    · intro a b heq
      apply Subtype.ext
      apply code_injective hp hp2 h hh
      · exact congrArg Prod.fst heq
      · intro k
        exact congrArg (fun q : cod => (q.2 k).1.1) heq
      · intro k
        exact congrArg (fun q : cod => (q.2 k).1.2) heq
  have hle : Fintype.card {a : ZMod p → Fin M // a ∈ bad} ≤ Fintype.card cod :=
    Fintype.card_le_of_embedding hemb
  have hcod : Fintype.card cod = M * (M ^ 2 - 1) ^ m := by
    dsimp [cod, C]
    rw [Fintype.card_prod, Fintype.card_fun]
    have hC : Fintype.card {c : Fin M × Fin M // c ≠ (i, j)} = M ^ 2 - 1 := by
      rw [Fintype.card_subtype_compl (fun c : Fin M × Fin M => c = (i, j))]
      have heq : Fintype.card {c : Fin M × Fin M // c = (i, j)} = 1 := by
        simpa using (Fintype.card_subtype_eq (i, j))
      rw [heq]
      simp [Fintype.card_prod]
      ring_nf
    rw [hC]
    simp
  calc
    bad.card = Fintype.card {a : ZMod p → Fin M // a ∈ bad} := hbadcard
    _ ≤ Fintype.card cod := hle
    _ = M * (M ^ 2 - 1) ^ m := hcod

lemma bad_empty_card_le {p M : ℕ} [Fintype (ZMod p)] [DecidableEq (ZMod p)]
    (i : Fin M) :
    let bad : Finset (ZMod p → Fin M) := by
      classical
      exact Finset.univ.filter (fun a : ZMod p → Fin M => ∀ x : ZMod p, a x ≠ i)
    bad.card ≤ (M - 1) ^ p := by
  classical
  intro bad
  let C := {j : Fin M // j ≠ i}
  let cod := ZMod p → C
  have hbadcard : bad.card = Fintype.card {a : ZMod p → Fin M // a ∈ bad} := by
    rw [Fintype.card_of_subtype bad (fun _ => Iff.rfl)]
  have hemb : {a : ZMod p → Fin M // a ∈ bad} ↪ cod := by
    refine ⟨fun a x => ⟨a.1 x, ?_⟩, ?_⟩
    · have hbad : ∀ x : ZMod p, a.1 x ≠ i := by
        have ha := a.2
        change a.1 ∈ (Finset.univ.filter (fun a : ZMod p → Fin M => ∀ x : ZMod p, a x ≠ i)) at ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha
      exact hbad x
    · intro a b heq
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (congrFun heq x)
  have hle : Fintype.card {a : ZMod p → Fin M // a ∈ bad} ≤ Fintype.card cod :=
    Fintype.card_le_of_embedding hemb
  have hcod : Fintype.card cod = (M - 1) ^ p := by
    dsimp [cod, C]
    rw [Fintype.card_fun]
    have hC : Fintype.card {j : Fin M // j ≠ i} = M - 1 := by
      rw [Fintype.card_subtype_compl (fun j : Fin M => j = i)]
      have heq : Fintype.card {j : Fin M // j = i} = 1 := by
        simpa using (Fintype.card_subtype_eq i)
      rw [heq]
      simp
    rw [hC]
    simp [ZMod.card]
  calc
    bad.card = Fintype.card {a : ZMod p → Fin M // a ∈ bad} := hbadcard
    _ ≤ Fintype.card cod := hle
    _ = (M - 1) ^ p := hcod

lemma rigid_partition_zmod_prime_coloring (M : ℕ) (hM : 0 < M) (p : ℕ)
    (hp : Nat.Prime p)
    (hbound : M * (M - 1) ^ p + M ^ 3 * p * (M ^ 2 - 1) ^ ((p - 1) / 2) < M ^ p) :
    ∃ a : ZMod p → Fin M,
      (∀ i : Fin M, ∃ x : ZMod p, a x = i) ∧
      (∀ i j : Fin M, ∀ h : ZMod p, h ≠ 0 → ∃ x : ZMod p, a x = i ∧ a (x - h) = j) := by
  classical
  by_cases hp2 : p = 2
  · subst p
    have hM1 : M = 1 := by
      norm_num at hbound
      nlinarith
    subst M
    let a : ZMod 2 → Fin 1 := fun _ => 0
    refine ⟨a, ?_, ?_⟩
    · intro i
      fin_cases i
      exact ⟨0, rfl⟩
    · intro i j h hh
      fin_cases i
      fin_cases j
      refine ⟨0, ?_⟩
      simp [a]
  · letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    let m : ℕ := (p - 1) / 2
    let Good : (ZMod p → Fin M) → Prop := fun a =>
      (∀ i : Fin M, ∃ x : ZMod p, a x = i) ∧
      (∀ i j : Fin M, ∀ h : ZMod p, h ≠ 0 → ∃ x : ZMod p, a x = i ∧ a (x - h) = j)
    let badEmptyAll : Finset (ZMod p → Fin M) :=
      (Finset.univ : Finset (Fin M)).biUnion fun i =>
        (Finset.univ.filter (fun a : ZMod p → Fin M => ∀ x : ZMod p, a x ≠ i))
    let badPairIdx : Finset (Fin M × Fin M × ZMod p) :=
      (Finset.univ : Finset (Fin M × Fin M × ZMod p)).filter (fun t => t.2.2 ≠ 0)
    let badPairAll : Finset (ZMod p → Fin M) :=
      badPairIdx.biUnion fun t =>
        (Finset.univ.filter (fun a : ZMod p → Fin M =>
          ∀ x : ZMod p, ¬ (a x = t.1 ∧ a (x - t.2.2) = t.2.1)))
    let bad : Finset (ZMod p → Fin M) := badEmptyAll ∪ badPairAll
    have hbad_empty_i : ∀ i : Fin M,
        ((Finset.univ.filter (fun a : ZMod p → Fin M => ∀ x : ZMod p, a x ≠ i)).card) ≤ (M - 1) ^ p := by
      intro i
      simpa using bad_empty_card_le (M := M) (p := p) i
    have hbadEmptyAll : badEmptyAll.card ≤ M * (M - 1) ^ p := by
      dsimp [badEmptyAll]
      have h := Finset.card_biUnion_le_card_mul (s := (Finset.univ : Finset (Fin M)))
        (f := fun i : Fin M => (Finset.univ.filter (fun a : ZMod p → Fin M => ∀ x : ZMod p, a x ≠ i)))
        ((M - 1) ^ p) (by
          intro i hi
          exact hbad_empty_i i)
      simpa using h
    have hbad_pair_i : ∀ t : Fin M × Fin M × ZMod p, t ∈ badPairIdx →
        ((Finset.univ.filter (fun a : ZMod p → Fin M =>
          ∀ x : ZMod p, ¬ (a x = t.1 ∧ a (x - t.2.2) = t.2.1))).card) ≤ M * (M ^ 2 - 1) ^ m := by
      intro t ht
      have hh : t.2.2 ≠ 0 := by
        simpa [badPairIdx] using ht
      simpa [m] using bad_pair_card_le (M := M) (p := p) hp hp2 t.2.2 hh t.1 t.2.1
    have hidx : badPairIdx.card ≤ M ^ 2 * p := by
      dsimp [badPairIdx]
      refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
      simp [Fintype.card_prod, Fintype.card_fun, ZMod.card]
      ring_nf
      exact le_rfl
    have hbadPairAll : badPairAll.card ≤ M ^ 3 * p * (M ^ 2 - 1) ^ m := by
      dsimp [badPairAll]
      calc
        (badPairIdx.biUnion fun t => (Finset.univ.filter (fun a : ZMod p → Fin M =>
          ∀ x : ZMod p, ¬ (a x = t.1 ∧ a (x - t.2.2) = t.2.1)))).card
            ≤ badPairIdx.card * (M * (M ^ 2 - 1) ^ m) := by
              refine Finset.card_biUnion_le_card_mul (s := badPairIdx)
                (f := fun t : Fin M × Fin M × ZMod p =>
                  (Finset.univ.filter (fun a : ZMod p → Fin M =>
                    ∀ x : ZMod p, ¬ (a x = t.1 ∧ a (x - t.2.2) = t.2.1))))
                (M * (M ^ 2 - 1) ^ m) ?_
              intro t ht
              exact hbad_pair_i t ht
        _ ≤ (M ^ 2 * p) * (M * (M ^ 2 - 1) ^ m) := by
              exact Nat.mul_le_mul_right _ hidx
        _ = M ^ 3 * p * (M ^ 2 - 1) ^ m := by ring_nf
    have hbad : bad.card ≤ M * (M - 1) ^ p + M ^ 3 * p * (M ^ 2 - 1) ^ m := by
      dsimp [bad]
      exact le_trans (Finset.card_union_le _ _) (add_le_add hbadEmptyAll hbadPairAll)
    have htotal : (Finset.univ : Finset (ZMod p → Fin M)).card = M ^ p := by
      change Fintype.card (ZMod p → Fin M) = M ^ p
      rw [Fintype.card_fun]
      simp [ZMod.card]
    have hbad_lt : bad.card < M ^ p := by
      have hle' : bad.card ≤ M * (M - 1) ^ p + M ^ 3 * p * (M ^ 2 - 1) ^ m := hbad
      have hm : m = (p - 1) / 2 := rfl
      rw [hm] at hle'
      exact lt_of_le_of_lt hle' hbound
    have hbad_ne : bad ≠ Finset.univ := by
      intro h
      have hlt : M ^ p < M ^ p := by simpa [h, htotal] using hbad_lt
      exact Nat.lt_irrefl _ hlt
    have hgood_exists : ∃ a : ZMod p → Fin M, a ∉ bad := by
      classical
      by_contra h
      have hall : ∀ a : ZMod p → Fin M, a ∈ bad := by
        intro a
        by_contra ha
        exact h ⟨a, ha⟩
      have huniv : bad = Finset.univ := by
        ext a; simp [hall a]
      exact hbad_ne huniv
    rcases hgood_exists with ⟨a, ha_bad⟩
    have ha_good : Good a := by
      by_contra hng
      have hb : a ∈ bad := by
        dsimp [bad]
        rw [Finset.mem_union]
        dsimp [Good] at hng
        have hdisj := not_and_or.mp hng
        rcases hdisj with hAneg | hBneg
        · left
          dsimp [badEmptyAll]
          rw [Finset.mem_biUnion]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          push_neg at hAneg
          exact hAneg
        · right
          dsimp [badPairAll]
          have hBneg' : ∃ i : Fin M, ∃ j : Fin M, ∃ h : ZMod p, h ≠ 0 ∧
              ∀ x : ZMod p, ¬ (a x = i ∧ a (x - h) = j) := by
            push_neg at hBneg
            simpa [not_and] using hBneg
          rw [Finset.mem_biUnion]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hBneg' with ⟨i, j, h, hh, hp⟩
          refine ⟨(i, j, h), ?_, ?_⟩
          · simpa [badPairIdx] using hh
          · simpa [not_and] using hp
      exact ha_bad hb
    refine ⟨a, ha_good.1, ha_good.2⟩

lemma nat_bound_of_real_bound (M k p : ℕ) (hM : 0 < M) (hp_eq : p = 2 * k + 1)
    (hreal : (M : ℝ) * (((M - 1 : ℕ) : ℝ) / (M : ℝ)) ^ p +
        ((M ^ 2 : ℕ) : ℝ) * (p : ℝ) * (((M ^ 2 - 1 : ℕ) : ℝ) / ((M ^ 2 : ℕ) : ℝ)) ^ k < 1) :
    M * (M - 1) ^ p + M ^ 3 * p * (M ^ 2 - 1) ^ k < M ^ p := by
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hM2real : ((M ^ 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 hM.ne')
  have hposMp : 0 < ((M ^ p : ℕ) : ℝ) := by exact_mod_cast pow_pos hM p
  have h1 : ((M ^ p : ℕ) : ℝ) * ((M : ℝ) * (((M - 1 : ℕ) : ℝ) / (M : ℝ)) ^ p) =
      ((M * (M - 1) ^ p : ℕ) : ℝ) := by
    rw [div_pow]
    norm_num [Nat.cast_pow]
    field_simp [hMreal]
  have h2 : ((M ^ p : ℕ) : ℝ) * (((M ^ 2 : ℕ) : ℝ) * (p : ℝ) * (((M ^ 2 - 1 : ℕ) : ℝ) / ((M ^ 2 : ℕ) : ℝ)) ^ k) =
      ((M ^ 3 * p * (M ^ 2 - 1) ^ k : ℕ) : ℝ) := by
    rw [hp_eq]
    rw [div_pow]
    norm_num [Nat.cast_pow]
    field_simp [hMreal, hM2real]
    ring_nf
  have hmul : ((M ^ p : ℕ) : ℝ) * ((M : ℝ) * (((M - 1 : ℕ) : ℝ) / (M : ℝ)) ^ p +
        ((M ^ 2 : ℕ) : ℝ) * (p : ℝ) * (((M ^ 2 - 1 : ℕ) : ℝ) / ((M ^ 2 : ℕ) : ℝ)) ^ k) <
      ((M ^ p : ℕ) : ℝ) := by
    have := mul_lt_mul_of_pos_left hreal hposMp
    simpa [mul_add, mul_one] using this
  have hsum : ((M * (M - 1) ^ p : ℕ) : ℝ) + ((M ^ 3 * p * (M ^ 2 - 1) ^ k : ℕ) : ℝ) <
      ((M ^ p : ℕ) : ℝ) := by
    rw [mul_add] at hmul
    rw [h1, h2] at hmul
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hmul
  have hcast : ((M * (M - 1) ^ p + M ^ 3 * p * (M ^ 2 - 1) ^ k : ℕ) : ℝ) <
      ((M ^ p : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hsum
  exact_mod_cast hcast

lemma rigid_partition_count_inequality (M : ℕ) (hM : 0 < M) :
    ∃ p : ℕ, Nat.Prime p ∧
      M * (M - 1) ^ p + M ^ 3 * p * (M ^ 2 - 1) ^ ((p - 1) / 2) < M ^ p := by
  by_cases hM1 : M = 1
  · subst M
    refine ⟨3, Nat.prime_three, ?_⟩
    norm_num
  · have hM_ge2 : 2 ≤ M := by omega
    let r1 : ℝ := ((M - 1 : ℕ) : ℝ) / (M : ℝ)
    let r2 : ℝ := ((M ^ 2 - 1 : ℕ) : ℝ) / ((M ^ 2 : ℕ) : ℝ)
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hM2pos : (0 : ℝ) < (M ^ 2 : ℕ) := by exact_mod_cast pow_pos hM 2
    have hr1_lt : r1 < 1 := by
      dsimp [r1]
      rw [div_lt_one hMreal]
      have hsub : M - 1 < M := by omega
      exact_mod_cast hsub
    have hr1_nonneg : 0 ≤ r1 := by
      dsimp [r1]
      exact div_nonneg (by exact_mod_cast Nat.zero_le (M - 1)) (by exact_mod_cast hM.le)
    have hr2_lt : r2 < 1 := by
      dsimp [r2]
      change (((M ^ 2 - 1 : ℕ) : ℝ) / ((M ^ 2 : ℕ) : ℝ) < 1)
      rw [div_lt_one hM2pos]
      exact_mod_cast (Nat.sub_lt (pow_pos hM 2) (by norm_num))
    have hr2_nonneg : 0 ≤ r2 := by
      dsimp [r2]
      change 0 ≤ ((M ^ 2 - 1 : ℕ) : ℝ) / ((M ^ 2 : ℕ) : ℝ)
      exact div_nonneg (by exact_mod_cast Nat.zero_le (M ^ 2 - 1)) (by exact_mod_cast (pow_pos hM 2).le)
    have hlim1 : Tendsto (fun k : ℕ => (M : ℝ) * r1 ^ (2 * k + 1)) atTop (nhds 0) := by
      have hs_nonneg : 0 ≤ r1 ^ 2 := sq_nonneg r1
      have hs_lt : r1 ^ 2 < 1 := by
        rw [sq_lt_one_iff₀ hr1_nonneg]
        exact hr1_lt
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one hs_nonneg hs_lt
      have h' : Tendsto (fun k : ℕ => (M : ℝ) * r1 * (r1 ^ 2) ^ k) atTop (nhds 0) := by
        simpa using h.const_mul ((M : ℝ) * r1)
      refine h'.congr' ?_
      filter_upwards with k
      rw [pow_add, pow_mul, pow_one]
      ring
    have hlim2 : Tendsto (fun k : ℕ => ((M ^ 2 : ℕ) : ℝ) * (2 * k + 1) * r2 ^ k) atTop (nhds 0) := by
      have hk : Tendsto (fun k : ℕ => (k : ℝ) * r2 ^ k) atTop (nhds 0) := by
        simpa using (tendsto_pow_const_mul_const_pow_of_lt_one (k := 1) hr2_nonneg hr2_lt)
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr2_nonneg hr2_lt
      have hsum : Tendsto (fun k : ℕ => 2 * ((k : ℝ) * r2 ^ k) + r2 ^ k) atTop (nhds 0) := by
        have hmul2 : Tendsto (fun k : ℕ => 2 * ((k : ℝ) * r2 ^ k)) atTop (nhds 0) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hk.mul_const 2
        simpa using hmul2.add hpow
      have hmain : Tendsto (fun k : ℕ => (M : ℝ)^2 * (2 * ((k : ℝ) * r2 ^ k) + r2 ^ k)) atTop (nhds 0) := by
        simpa using hsum.const_mul ((M : ℝ)^2)
      refine hmain.congr' ?_
      filter_upwards with k
      dsimp [r2]
      norm_num [Nat.cast_pow, Nat.cast_add, Nat.cast_mul]
      field_simp
    let F : ℕ → ℝ := fun k =>
      (M : ℝ) * r1 ^ (2 * k + 1) + ((M ^ 2 : ℕ) : ℝ) * (2 * k + 1) * r2 ^ k
    have hlimF : Tendsto F atTop (nhds 0) := by
      simpa [F] using hlim1.add hlim2
    have hev : ∀ᶠ k in atTop, F k < 1 := (tendsto_order.mp hlimF).2 1 zero_lt_one
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    let k0 : ℕ := max N 1
    have hk0N : N ≤ k0 := le_max_left _ _
    obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (2 * k0 + 1)
    have hp_gt_2 : 2 < p := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    let k : ℕ := (p - 1) / 2
    have hp_eq : p = 2 * k + 1 := by
      dsimp [k]
      have hodd : Odd p := hp_odd
      rcases hodd with ⟨a, ha⟩
      have : a = (p - 1) / 2 := by omega
      omega
    have hk_ge_N : N ≤ k := by
      dsimp [k]
      omega
    have hFk : F k < 1 := hN k hk_ge_N
    dsimp [F] at hFk
    have hFk' : (M : ℝ) * r1 ^ p + ((M ^ 2 : ℕ) : ℝ) * (p : ℝ) * r2 ^ k < 1 := by
      simpa [hp_eq] using hFk
    have hnat := nat_bound_of_real_bound M k p hM hp_eq hFk'
    refine ⟨p, hp, ?_⟩
    simpa [k] using hnat

theorem rigid_partition_zmod (M : ℕ) (hM : 0 < M) :
    ∃ N : ℕ, 0 < N ∧ ∃ E : Fin M → Set (ZMod N),
      (∀ i : Fin M, (E i).Nonempty) ∧
      (∀ x : ZMod N, ∃ i : Fin M, x ∈ E i) ∧
      (∀ i j : Fin M, i ≠ j → Disjoint (E i) (E j)) ∧
      (∀ i j : Fin M, ∀ h : ZMod N, h ≠ 0 → (E i ∩ (E j + h)).Nonempty) := by
  classical
  rcases rigid_partition_count_inequality M hM with ⟨p, hp, hbound⟩
  rcases rigid_partition_zmod_prime_coloring M hM p hp hbound with ⟨a, ha_nonempty, ha_rigid⟩
  refine ⟨p, hp.pos, fun i => {x : ZMod p | a x = i}, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases ha_nonempty i with ⟨x, hx⟩
    exact ⟨x, hx⟩
  · intro x
    refine ⟨a x, rfl⟩
  · intro i j hij
    rw [Set.disjoint_iff_forall_ne]
    intro x hx y hy hxy
    have hxi : a x = i := hx
    have hyj : a y = j := hy
    have : i = j := by
      rw [← hxi, ← hyj, hxy]
    exact hij this
  · intro i j h hh
    rcases ha_rigid i j h hh with ⟨x, hxi, hxj⟩
    refine ⟨x, hxi, ?_⟩
    exact ⟨x - h, hxj, by simp [sub_add_cancel]⟩

end Commons.PeriodicTiling