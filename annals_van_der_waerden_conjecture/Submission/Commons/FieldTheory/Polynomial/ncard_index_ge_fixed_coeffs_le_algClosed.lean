import Mathlib
import Submission.Commons.FieldTheory.Polynomial.powerSum_system_card_le_factorial
import Submission.Commons.FieldTheory.Polynomial.multiset_psum_newton
import Submission.Commons.FieldTheory.Polynomial.natDegree_radical_eq_card_roots_toFinset
import Submission.Commons.FieldTheory.Polynomial.finite_powerSum_system
import Submission.Commons.FieldTheory.Polynomial.psum_eq_of_esymm_eq_le

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Polynomial

namespace Commons.FieldTheory.Polynomial

lemma natCast_ne_zero_of_le_factorial {F : Type*} [Field F] {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hchar : (Nat.factorial n : F) ≠ 0) : (m : F) ≠ 0 := by
  intro h
  have hdvd : m ∣ n.factorial := Nat.dvd_factorial (by omega) hmn
  have h1 : (n.factorial : F) = (m : F) * ((n.factorial / m : ℕ) : F) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  exact hchar (by rw [h1, h, zero_mul])

lemma finset_sum_cast_ne_zero {F : Type*} [Field F] {n : ℕ} (hchar : (Nat.factorial n : F) ≠ 0)
    {r : ℕ} (m : Fin r → ℕ) (hmn : ∑ i, m i = n) (hmpos : ∀ i, 1 ≤ m i)
    (s : Finset (Fin r)) (hs : s.Nonempty) : (∑ i ∈ s, (m i : F)) ≠ 0 := by
  have hle : ∑ i ∈ s, m i ≤ n := by
    rw [← hmn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => Nat.zero_le _)
  have hge : 1 ≤ ∑ i ∈ s, m i := by
    obtain ⟨i, hi⟩ := hs
    exact le_trans (hmpos i) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
  have hcast : ((∑ i ∈ s, m i : ℕ) : F) ≠ 0 := natCast_ne_zero_of_le_factorial hge hle hchar
  rwa [Nat.cast_sum] at hcast

theorem monic_splits_eq_prod_toFinset {F : Type*} [Field F] [DecidableEq F] {p : F[X]}
    (hm : p.Monic) (hs : p.Splits) :
    p = ∏ a ∈ p.roots.toFinset, (_root_.Polynomial.X - _root_.Polynomial.C a) ^ (Multiset.count a p.roots) := by
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm]
  rw [Finset.prod_multiset_map_count]

lemma esymm_roots_eq {F : Type*} [Field F] {p : F[X]} (hm : p.Monic) (hs : p.Splits)
    {i : ℕ} (hi : i ≤ p.natDegree) :
    p.roots.esymm i = (-1)^i * p.coeff (p.natDegree - i) := by
  have h := _root_.Polynomial.coeff_eq_esymm_roots_of_splits hs (k := p.natDegree - i) (by omega)
  rw [hm.leadingCoeff, one_mul, Nat.sub_sub_self hi] at h
  have hsign : ((-1 : F)^i) * ((-1 : F)^i) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [h, ← mul_assoc, hsign, one_mul]

/-- The property defining the set of polynomials we count. -/
def InS (F : Type) [Field F] [DecidableEq F] (n k : ℕ) (a : Fin (n - k) → F) (P : F[X]) : Prop :=
  P.Monic ∧ P.natDegree = n ∧ (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = a i) ∧
    k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree

/-- The solution set of the weighted power sum system attached to a multiplicity pattern `c`. -/
def PSumSol {F : Type*} [Field F] (n k : ℕ) (c₀ : ℕ → F)
    (c : {c : Composition n // c.length ≤ n - k}) : Type _ :=
  {x : Fin c.1.length → F // ∀ j : Fin c.1.length,
    ∑ i, (c.1.blocksFun i : F) * (x i) ^ ((j : ℕ) + 1) = c₀ (j : ℕ)}

theorem ncard_index_ge_fixed_coeffs_le_algClosed (F : Type) [Field F] [DecidableEq F] [IsAlgClosed F]
    (n k : ℕ) (hk : k ≤ n) (hchar : (Nat.factorial n : F) ≠ 0) (a : Fin (n - k) → F) :
    Nat.card {P : Polynomial F // P.Monic ∧ P.natDegree = n ∧
        (∀ i : Fin (n - k), P.coeff (k + (i : ℕ)) = a i) ∧
        k ≤ n - (UniqueFactorizationMonoid.radical P).natDegree} ≤
      (n + 1) * Nat.factorial n * 2 ^ n := by
  classical
  change Nat.card {P : F[X] // InS F n k a P} ≤ (n + 1) * Nat.factorial n * 2 ^ n
  by_cases hne : Nonempty {P : F[X] // InS F n k a P}
  · rcases hne with ⟨P₀, hP₀⟩
    set c₀ : ℕ → F := fun j => (P₀.roots.map (· ^ (j + 1))).sum with hc₀
    -- Step 1: the power sums of the roots are determined by the fixed top coefficients.
    have hps : ∀ (Q : {P : F[X] // InS F n k a P}) (j : ℕ), 1 ≤ j → j ≤ n - k →
        (Q.1.roots.map (· ^ j)).sum = c₀ (j - 1) := by
      intro Q j hj1 hj2
      have hcardQ : Q.1.roots.card = n := by
        rw [splits_iff_card_roots.mp (IsAlgClosed.splits Q.1), Q.2.2.1]
      have hcardP : P₀.roots.card = n := by
        rw [splits_iff_card_roots.mp (IsAlgClosed.splits P₀), hP₀.2.1]
      have hcard : Q.1.roots.card = P₀.roots.card := by rw [hcardQ, hcardP]
      have hN : n - k ≤ Q.1.roots.card := by rw [hcardQ]; omega
      have hesymm : ∀ i : ℕ, 1 ≤ i → i ≤ n - k → Q.1.roots.esymm i = P₀.roots.esymm i := by
        intro i hi1 hi2
        have hiQ : i ≤ Q.1.natDegree := by rw [Q.2.2.1]; omega
        have hiP : i ≤ P₀.natDegree := by rw [hP₀.2.1]; omega
        rw [esymm_roots_eq Q.2.1 (IsAlgClosed.splits Q.1) hiQ,
          esymm_roots_eq hP₀.1 (IsAlgClosed.splits P₀) hiP, Q.2.2.1, hP₀.2.1]
        congr 1
        have hni : k ≤ n - i := by omega
        have hlt : n - i - k < n - k := by omega
        rw [show n - i = k + (n - i - k) from by omega,
          Q.2.2.2.1 ⟨n - i - k, hlt⟩, hP₀.2.2.1 ⟨n - i - k, hlt⟩]
      have hconcl := psum_eq_of_esymm_eq_le Q.1.roots P₀.roots (n - k) hcard hN hesymm
      rw [hconcl j hj1 hj2, hc₀]
      simp only
      rw [show j - 1 + 1 = j from by omega]
    -- Step 2: every `Q` in the set comes from a pattern and a root tuple.
    have hex : ∀ (Q : {P : F[X] // InS F n k a P}),
        ∃ (c : Composition n), c.length ≤ n - k ∧ ∃ (x : Fin c.length → F),
          (∀ j : Fin c.length, ∑ i, (c.blocksFun i : F) * (x i) ^ ((j : ℕ) + 1) = c₀ (j : ℕ)) ∧
          (∏ i, (_root_.Polynomial.X - _root_.Polynomial.C (x i)) ^ (c.blocksFun i)) = Q.1 := by
      intro Q
      set S₀ : Finset F := Q.1.roots.toFinset with hS₀
      set l : List F := S₀.toList with hl
      have hl_nodup : l.Nodup := Finset.nodup_toList S₀
      have hl_len : l.length = S₀.card := Finset.length_toList S₀
      have hl_tofinset : l.toFinset = S₀ := Finset.toList_toFinset S₀
      have hcnt_pos : ∀ a ∈ l, 0 < Q.1.roots.count a := by
        intro a ha
        have haS : a ∈ S₀ := by rw [hl] at ha; exact Finset.mem_toList.mp ha
        rw [hS₀] at haS
        exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haS)
      have hsum_cnt : (l.map (fun a => Q.1.roots.count a)).sum = n := by
        rw [← List.sum_toFinset (fun a => Q.1.roots.count a) hl_nodup, hl_tofinset]
        rw [hS₀, Multiset.toFinset_sum_count_eq, splits_iff_card_roots.mp (IsAlgClosed.splits Q.1),
          Q.2.2.1]
      have hmap_pos : ∀ i, i ∈ l.map (fun a => Q.1.roots.count a) → 0 < i := by
        intro i hi
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
        exact hcnt_pos a ha
      let c : Composition n := ⟨l.map (fun a => Q.1.roots.count a), fun hi => hmap_pos _ hi,
        hsum_cnt⟩
      have hclen : c.length = l.length := by
        show (l.map (fun a => Q.1.roots.count a)).length = l.length
        rw [List.length_map]
      have hblocks : ∀ i : Fin c.length,
          c.blocksFun i = Q.1.roots.count (l.get (Fin.cast hclen i)) := by
        intro i
        show (l.map (fun a => Q.1.roots.count a)).get (i : Fin (l.map (fun a => Q.1.roots.count a)).length)
            = Q.1.roots.count (l.get (Fin.cast hclen i))
        have key : (l.map (fun a => Q.1.roots.count a)).get
              (i : Fin (l.map (fun a => Q.1.roots.count a)).length)
            = Q.1.roots.count (l.get (Fin.cast (List.length_map (fun a => Q.1.roots.count a)) i)) := by
          simp [List.get_eq_getElem, List.getElem_map]
        rw [key]
      have hc1 : c.length = (UniqueFactorizationMonoid.radical Q.1).natDegree := by
        rw [hclen, hl_len, hS₀]
        exact (natDegree_radical_eq_card_roots_toFinset Q.1 Q.2.1).symm
      have hcle : c.length ≤ n - k := by
        have hrle : (UniqueFactorizationMonoid.radical Q.1).natDegree ≤ n := by
          have h := natDegree_le_of_dvd (UniqueFactorizationMonoid.radical_dvd_self (a := Q.1))
            Q.2.1.ne_zero
          rwa [Q.2.2.1] at h
        have hkey : k ≤ n - (UniqueFactorizationMonoid.radical Q.1).natDegree := Q.2.2.2.2
        omega
      refine ⟨c, hcle, ?_⟩
      · refine ⟨fun i : Fin c.length => l.get (Fin.cast hclen i), ?_, ?_⟩
        · intro j
          calc (∑ i : Fin c.length, (c.blocksFun i : F) * (l.get (Fin.cast hclen i)) ^ ((j : ℕ) + 1))
              = ∑ b ∈ S₀, (Q.1.roots.count b : F) * b ^ ((j : ℕ) + 1) := by
                refine Finset.sum_bij (fun i _ => l.get (Fin.cast hclen i)) ?_ ?_ ?_ ?_
                · intro i _
                  rw [← hl_tofinset]
                  exact List.mem_toFinset.mpr (List.get_mem l _)
                · intro i _ k _ hik
                  exact Fin.cast_injective hclen ((hl_nodup.get_inj_iff).mp hik)
                · intro b hb
                  have hb' : b ∈ l := by rw [hl]; exact Finset.mem_toList.mpr hb
                  obtain ⟨n', hn'⟩ := List.mem_iff_get.mp hb'
                  refine ⟨Fin.cast hclen.symm n', Finset.mem_univ _, ?_⟩
                  have hcast : Fin.cast hclen (Fin.cast hclen.symm n') = n' := by
                    apply Fin.ext; simp
                  rw [hcast, hn']
                · intro i _
                  rw [hblocks i]
            _ = (Q.1.roots.map (· ^ ((j : ℕ) + 1))).sum := by
                rw [Finset.sum_multiset_map_count, hS₀]
                apply Finset.sum_congr rfl
                intro m _
                rw [nsmul_eq_mul]
            _ = c₀ (j : ℕ) := by
                rw [hps Q ((j : ℕ) + 1) (by omega) (by omega)]
                congr 1
        · rw [monic_splits_eq_prod_toFinset Q.2.1 (IsAlgClosed.splits Q.1)]
          refine Finset.prod_bij (fun i _ => l.get (Fin.cast hclen i)) ?_ ?_ ?_ ?_
          · intro i _
            have h1 : l.get (Fin.cast hclen i) ∈ S₀ := by
              rw [← hl_tofinset]
              exact List.mem_toFinset.mpr (List.get_mem l _)
            rw [hS₀] at h1
            exact h1
          · intro i _ k _ hik
            exact Fin.cast_injective hclen ((hl_nodup.get_inj_iff).mp hik)
          · intro b hb
            have hbS : b ∈ S₀ := by rw [hS₀]; exact hb
            have hb' : b ∈ l := by rw [hl]; exact Finset.mem_toList.mpr hbS
            obtain ⟨n', hn'⟩ := List.mem_iff_get.mp hb'
            refine ⟨Fin.cast hclen.symm n', Finset.mem_univ _, ?_⟩
            have hcast : Fin.cast hclen (Fin.cast hclen.symm n') = n' := by
              apply Fin.ext; simp
            rw [hcast, hn']
          · intro i _
            rw [hblocks i]
    -- Step 3: counting
    have hmF : ∀ c : {c : Composition n // c.length ≤ n - k},
        ∀ s : Finset (Fin c.1.length), s.Nonempty → ∑ i ∈ s, (c.1.blocksFun i : F) ≠ 0 := by
      intro c s hs
      exact finset_sum_cast_ne_zero hchar (fun i => c.1.blocksFun i) c.1.sum_blocksFun
        (fun i => c.1.one_le_blocksFun i) s hs
    have hFinSol : ∀ c : {c : Composition n // c.length ≤ n - k}, Finite (PSumSol n k c₀ c) := by
      intro c
      exact finite_powerSum_system F c.1.length (fun i => (c.1.blocksFun i : F))
        (fun j => c₀ (j : ℕ)) (hmF c)
    have hFinDom : Finite (Σ c : {c : Composition n // c.length ≤ n - k}, PSumSol n k c₀ c) := by
      haveI : ∀ c, Fintype (PSumSol n k c₀ c) := fun c => Fintype.ofFinite _
      haveI : Fintype (Σ c : {c : Composition n // c.length ≤ n - k}, PSumSol n k c₀ c) := inferInstance
      exact Finite.of_fintype _
    let bigprod : (Σ c : {c : Composition n // c.length ≤ n - k}, PSumSol n k c₀ c) → F[X] :=
      fun d => ∏ i : Fin d.1.1.length,
        (_root_.Polynomial.X - _root_.Polynomial.C (d.2.1 i)) ^ (d.1.1.blocksFun i)
    let ff : {P : F[X] // InS F n k a P} →
        (Σ c : {c : Composition n // c.length ≤ n - k}, PSumSol n k c₀ c) :=
      fun Q =>
        ⟨⟨Classical.choose (hex Q), (Classical.choose_spec (hex Q)).1⟩,
          ⟨Classical.choose (Classical.choose_spec (hex Q)).2,
            (Classical.choose_spec (Classical.choose_spec (hex Q)).2).1⟩⟩
    have hbig : ∀ Q, bigprod (ff Q) = Q.1 := by
      intro Q
      exact (Classical.choose_spec (Classical.choose_spec (hex Q)).2).2
    have hff_inj : Function.Injective ff := by
      intro Q Q' h
      apply Subtype.ext
      rw [← hbig Q, ← hbig Q', h]
    have hcard : Nat.card (Σ c : {c : Composition n // c.length ≤ n - k}, PSumSol n k c₀ c)
        ≤ (n + 1) * Nat.factorial n * 2 ^ n := by
      rw [Nat.card_sigma]
      have hlen_le : ∀ c : {c : Composition n // c.length ≤ n - k}, c.1.length ≤ n := by
        intro c
        have h1 : c.1.length ≤ ∑ i : Fin c.1.length, c.1.blocksFun i := by
          simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => c.1.one_le_blocksFun i)
        rw [c.1.sum_blocksFun] at h1
        exact h1
      calc ∑ c : {c : Composition n // c.length ≤ n - k}, Nat.card (PSumSol n k c₀ c)
          ≤ ∑ c : {c : Composition n // c.length ≤ n - k}, (c.1.length).factorial := by
            apply Finset.sum_le_sum
            intro c _
            exact powerSum_system_card_le_factorial F c.1.length _ _ (hmF c)
        _ ≤ ∑ _c : {c : Composition n // c.length ≤ n - k}, n.factorial := by
            apply Finset.sum_le_sum
            intro c _
            exact Nat.factorial_le (hlen_le c)
        _ = Fintype.card {c : Composition n // c.length ≤ n - k} * n.factorial := by
            rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
        _ ≤ 2 ^ n * n.factorial := by
            have h1 : Fintype.card {c : Composition n // c.length ≤ n - k} ≤ Fintype.card (Composition n) :=
              Fintype.card_subtype_le _
            have h2 : Fintype.card (Composition n) = 2 ^ (n - 1) := composition_card n
            have h3 : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
            exact Nat.mul_le_mul_right _ (le_trans h1 (le_trans (le_of_eq h2) h3))
        _ ≤ (n + 1) * Nat.factorial n * 2 ^ n := by
            rw [Nat.mul_comm (2 ^ n)]
            calc n.factorial * 2 ^ n ≤ (n + 1) * (n.factorial * 2 ^ n) :=
                  Nat.le_mul_of_pos_left _ (by omega)
              _ = (n + 1) * n.factorial * 2 ^ n := by ring
    exact le_trans (Nat.card_le_card_of_injective ff hff_inj) hcard
  · rw [not_nonempty_iff] at hne
    haveI := hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

end Commons.FieldTheory.Polynomial
