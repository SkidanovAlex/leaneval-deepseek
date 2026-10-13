import Mathlib
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Profile
import Submission.Work.WilE6.exists_cubeSaturated

set_option autoImplicit false
noncomputable section
namespace Work.WilE5.Bounds

open WilkiesDesign WilkiesDesign.E

/-!
# `countP` — the a-priori profile count of the fibrewise stratification recursion

This file proves the two counting bounds of `Work.WilE5.Bounds.countP`: the number of states at
level `k ≤ q` of the recursion `levelP` is bounded by `profCount` evaluated at `X.deg`, and the
total number of flat leaves produced up to level `q` is bounded by `bCount`.

The proof is completely elementary.  Writing `Ml := MlOf Me X.deg p q`,
`NΦ := NPhi Me X.deg p q` and
```
cfac := 2 * NΦ * ((profM Me p q (2*q+1)).eval X.deg + 1) ^ q * q
```
the `profCount` recursion is `profCount 0 = C(3^q) * (X + 1)` and
`profCount (k+1) = profCount k * (C 2 * profN Me p q (2*q+1) *
(profM Me p q (2*q+1) + C 1)^q * C q)`, so `(profCount k).eval D = 3^q * (D+1) * cfac^k`.

The three ingredients are
* `(initStates X).length ≤ 3^q * (X.deg + 1)`: there are `|X.basics.dedup| ≤ X.deg + 1` disjuncts
  and `∑_{Fy : Finset (Fin q)} 2^{|Fy|} = 3^q` face patterns;
* `(testL q M NΦ).length ≤ NΦ * (M+1)^q * q`, and every state at level `k` has at most
  `2 * |testL|` children;
* every state at level `k` has `k` pivots on top of the ≤ `q` face equations of its initial state,
  so `σ.B.length ≤ q + k ≤ 2q+1` and its test bound `Ml σ.B.length` is dominated by
  `(profM Me p q (2*q+1)).eval X.deg`.
-/

/-! ## §1. Auxiliary counting lemmas -/

/-- Congruence for `List.sum` of a `List.map`, in degree `ℕ`. -/
private lemma list_sum_congr {α : Type*} {l : List α} {f g : α → ℕ}
    (h : ∀ x ∈ l, f x = g x) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.mem_cons] at h ⊢
      rw [h a (Or.inl rfl), ih (fun x hx => h x (Or.inr hx))]

/-- Sum of a constant list: `∑_{x ∈ l} c = |l| * c`. -/
private lemma sum_map_const {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- `List.length_product` restated for the explicit `List.product` (the Mathlib lemma is phrased
with the `×ˢ` notation, which `rw` does not match against `List.product`). -/
private lemma list_product_length {α β : Type*} (l₁ : List α) (l₂ : List β) :
    (l₁.product l₂).length = l₁.length * l₂.length :=
  List.length_product l₁ l₂

/-- `∑_{s : Finset α} 2 ^ s.card = 3 ^ |α|`: expand `3 ^ |α| = ∏ i, (2 + 1)` and split the
product over a subset `t` whose elements contribute `2` and its complement which contributes `1`. -/
private lemma sum_finset_two_pow_card (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ s : Finset α, 2 ^ s.card) = 3 ^ Fintype.card α := by
  have h := Finset.prod_add (fun _ : α => (2 : ℕ)) (fun _ : α => (1 : ℕ))
    (Finset.univ : Finset α)
  rw [Finset.powerset_univ] at h
  simp only [Finset.prod_const, one_pow, mul_one, Finset.card_univ] at h
  exact h.symm

/-- `mList q M` enumerates the `(M+1)^q` multi-indices with entries `≤ M`. -/
private lemma mList_length (q M : ℕ) : (mList q M).length = (M + 1) ^ q := by
  rw [mList, List.length_map]
  show (Finset.univ : Finset (Fin q → Fin (M + 1))).toList.length = (M + 1) ^ q
  rw [Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- The test list has at most `NΦ * (M+1)^q * q` elements: it is a filtered sublist of
`range NΦ × (mList q M × finRange q)`. -/
private lemma testL_length (q M NΦ : ℕ) :
    (testL q M NΦ).length ≤ NΦ * (M + 1) ^ q * q := by
  have h1 : (testL q M NΦ).length ≤
      (((List.range NΦ).product ((mList q M).product (List.finRange q)))).length := by
    rw [testL]
    exact le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map _))
  simp only [list_product_length, List.length_range, List.length_finRange, mList_length] at h1
  refine h1.trans (le_of_eq ?_)
  ring

/-- An initial state carries one face equation per element of its face pattern. -/
private lemma initSt_B_length {p q : ℕ} (X : SemiPf (p + q)) (A : Basic (p + q) X.r)
    (Fy : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) :
    (initSt X A Fy ε).B.length = Fy.card := by
  simp only [initSt, List.length_map, Finset.length_toList, Finset.card_attach]

/-- A semi-Pfaffian `X` has at most `X.deg + 1` distinct disjuncts. -/
private lemma dedupLength_le {k : ℕ} (X : SemiPf k) :
    (X.basics.dedup).length ≤ X.deg + 1 := by
  have hnod : X.basics.dedup.Nodup := List.nodup_dedup X.basics
  have hlen : X.basics.dedup.length ≤
      (X.basics.dedup.map (Basic.deg (k := k) (r := X.r))).sum + 1 :=
    Work.WilE6.cube_nodup_length_le_sum _ hnod
  have hsum : (X.basics.dedup.map (Basic.deg (k := k) (r := X.r))).sum ≤ X.deg := by
    have h := Work.WilE6.cube_sublist_sum_map_le (f := Basic.deg (k := k) (r := X.r))
      (List.dedup_sublist X.basics)
    simpa only [WilkiesDesign.E.SemiPf.deg] using h
  omega

/-- The initial states are indexed by the distinct disjuncts of `X` and the `3^q` face patterns,
so there are at most `3^q * (X.deg + 1)` of them. -/
private lemma initStates_length {p q : ℕ} (X : SemiPf (p + q)) :
    (initStates X).length ≤ 3 ^ q * (X.deg + 1) := by
  have hblk : ∀ A : Basic (p + q) X.r,
      ((Finset.univ : Finset (Finset (Fin q))).toList.flatMap (fun Fy =>
        ((Finset.univ : Finset ({l // l ∈ Fy} → Bool)).toList).map
          (fun ε => initSt X A Fy ε))).length = 3 ^ q := by
    intro A
    rw [List.length_flatMap]
    have hg : ∀ Fy : Finset (Fin q),
        (((Finset.univ : Finset ({l // l ∈ Fy} → Bool)).toList).map
          (fun ε => initSt X A Fy ε)).length = 2 ^ Fy.card := by
      intro Fy
      rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_coe]
    rw [list_sum_congr (fun Fy _ => hg Fy)]
    rw [← List.sum_toFinset (fun Fy : Finset (Fin q) => 2 ^ Fy.card)
      (Finset.nodup_toList (Finset.univ : Finset (Finset (Fin q)))), Finset.toList_toFinset]
    simpa using sum_finset_two_pow_card (Fin q)
  have hlen : (initStates X).length =
      ((X.basics.dedup).map (fun A => ((Finset.univ : Finset (Finset (Fin q))).toList.flatMap
        (fun Fy => ((Finset.univ : Finset ({l // l ∈ Fy} → Bool)).toList).map
          (fun ε => initSt X A Fy ε))).length)).sum := by
    rw [initStates, List.length_flatMap]
  rw [hlen]
  have hsum : ((X.basics.dedup).map (fun A =>
      ((Finset.univ : Finset (Finset (Fin q))).toList.flatMap
        (fun Fy => ((Finset.univ : Finset ({l // l ∈ Fy} → Bool)).toList).map
          (fun ε => initSt X A Fy ε))).length)).sum = X.basics.dedup.length * 3 ^ q := by
    rw [list_sum_congr (fun A _ => hblk A), sum_map_const]
  rw [hsum]
  calc X.basics.dedup.length * 3 ^ q ≤ (X.deg + 1) * 3 ^ q :=
        Nat.mul_le_mul_right _ (dedupLength_le X)
    _ = 3 ^ q * (X.deg + 1) := Nat.mul_comm _ _

/-- A state has exactly two children per test. -/
private lemma childrenP_length_le {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    (childrenP X.c Ml NΦ σ).length ≤ 2 * (testL q (Ml σ.B.length) NΦ).length := by
  rw [childrenP, List.length_flatMap]
  refine le_of_eq ?_
  calc ((testLP Ml NΦ σ).map (fun t =>
        ([childStP X.c Ml NΦ σ t false, childStP X.c Ml NΦ σ t true] :
          List (St p q X.r)).length)).sum
      = ((testLP Ml NΦ σ).map (fun _ => 2)).sum := list_sum_congr (fun t _ => rfl)
    _ = (testLP Ml NΦ σ).length * 2 := sum_map_const _ 2
    _ = 2 * (testL q (Ml σ.B.length) NΦ).length := by rw [testLP]; ring

/-- Every state at level `k` has at most `q + k` pivots: an initial state has `|B| = |Fy| ≤ q`
face equations and every child adds exactly one. -/
private lemma levelP_B_length {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) :
    ∀ k (σ : St p q X.r), σ ∈ levelP X Ml NΦ k → σ.B.length ≤ q + k := by
  intro k
  induction k with
  | zero =>
      intro σ h
      rw [levelP_zero] at h
      obtain ⟨A, hA, Fy, ε, rfl⟩ := exists_of_mem_initStates X h
      rw [initSt_B_length]
      have hc := Finset.card_le_univ Fy
      simp only [Fintype.card_fin] at hc
      omega
  | succ k ih =>
      intro σ h
      rw [mem_levelP_succ] at h
      obtain ⟨σ₀, hσ₀, hmem⟩ := h
      rw [childrenP] at hmem
      obtain ⟨t, ht, hτ⟩ := List.mem_flatMap.mp hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
      rcases hτ with rfl | rfl
      · rw [childStP_level]; have := ih σ₀ hσ₀; omega
      · rw [childStP_level]; have := ih σ₀ hσ₀; omega

/-! ## §2. The `profCount` evaluation -/

private lemma profCount_succ (Me : Polynomial ℕ) (p q k : ℕ) :
    profCount Me p q (k + 1) =
      profCount Me p q k * (Polynomial.C 2 * profN Me p q (2 * q + 1) *
        (profM Me p q (2 * q + 1) + Polynomial.C 1) ^ q * Polynomial.C q) := rfl

private lemma profCount_eval_zero (Me : Polynomial ℕ) (p q D : ℕ) :
    (profCount Me p q 0).eval D = 3 ^ q * (D + 1) := by
  simp [profCount, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X]

private lemma profCount_eval_succ (Me : Polynomial ℕ) (p q k D : ℕ) :
    (profCount Me p q (k + 1)).eval D =
      (profCount Me p q k).eval D *
        (2 * (profN Me p q (2 * q + 1)).eval D *
          ((profM Me p q (2 * q + 1)).eval D + 1) ^ q * q) := by
  rw [profCount_succ]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C]

/-- The closed form `(profCount k).eval D = 3^q * (D+1) * cfac^k`. -/
private lemma profCount_eval_eq (Me : Polynomial ℕ) (p q k D : ℕ) :
    (profCount Me p q k).eval D = 3 ^ q * (D + 1) *
      (2 * (profN Me p q (2 * q + 1)).eval D *
        ((profM Me p q (2 * q + 1)).eval D + 1) ^ q * q) ^ k := by
  induction k with
  | zero => rw [profCount_eval_zero]; simp
  | succ k ih => rw [profCount_eval_succ, ih, pow_succ]; ring

private lemma profN_eval_zero (Me : Polynomial ℕ) (p q D : ℕ) :
    (profN Me p q 0).eval D = D + 1 := by
  have h : profN Me p q 0 = Polynomial.X + Polynomial.C 1 := rfl
  rw [h]
  simp [Polynomial.eval_add, Polynomial.eval_X]

/-- The multiplicative factor of `profCount` dominates `2 * q` (hence is `≥ 1` as soon as
`q ≥ 1`), because `profN` evaluates to at least `D + 1 ≥ 1`. -/
private lemma cfac_ge (Me : Polynomial ℕ) (p q D : ℕ) :
    2 * q ≤ 2 * (profN Me p q (2 * q + 1)).eval D *
        ((profM Me p q (2 * q + 1)).eval D + 1) ^ q * q := by
  have hN : 1 ≤ (profN Me p q (2 * q + 1)).eval D := by
    have hm : (profN Me p q 0).eval D ≤ (profN Me p q (2 * q + 1)).eval D :=
      profN_eval_mono Me p q D (show 0 ≤ 2 * q + 1 by omega)
    rw [profN_eval_zero Me p q D] at hm
    omega
  have hM : 1 ≤ ((profM Me p q (2 * q + 1)).eval D + 1) ^ q :=
    Nat.one_le_pow q ((profM Me p q (2 * q + 1)).eval D + 1) (by omega)
  calc 2 * q = 2 * 1 * 1 * q := by ring
    _ ≤ 2 * (profN Me p q (2 * q + 1)).eval D *
          ((profM Me p q (2 * q + 1)).eval D + 1) ^ q * q := by
        refine Nat.mul_le_mul_right q ?_
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN) hM

/-- `profCount` is monotone in the level, for levels `k ≤ q`. -/
private lemma profCount_eval_le {Me : Polynomial ℕ} {p q D k : ℕ} (hk : k ≤ q) :
    (profCount Me p q k).eval D ≤ (profCount Me p q q).eval D := by
  have hcf := cfac_ge Me p q D
  rw [profCount_eval_eq, profCount_eval_eq]
  refine Nat.mul_le_mul_left _ ?_
  rcases Nat.eq_zero_or_pos (2 * (profN Me p q (2 * q + 1)).eval D *
      ((profM Me p q (2 * q + 1)).eval D + 1) ^ q * q) with hz | hp
  · rw [hz] at hcf ⊢
    have hq0 : q = 0 := by omega
    subst hq0
    have hk0 : k = 0 := by omega
    subst hk0
    simp
  · exact Nat.pow_le_pow_right hp hk

/-! ## §3. The main induction -/

/-- The number of states at level `k ≤ q` is bounded by `profCount k` evaluated at `X.deg`. -/
private lemma levelP_length_le {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ) :
    ∀ k, k ≤ q → (levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).length ≤
      (profCount Me p q k).eval X.deg := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [levelP_zero, profCount_eval_zero]
      exact initStates_length X
  | succ k ih =>
      intro hk
      have hk' : k ≤ q := by omega
      rw [levelP_succ, List.length_flatMap]
      have hstep : ∀ σ ∈ levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k,
          (childrenP X.c (MlOf Me X.deg p q) (NPhi Me X.deg p q) σ).length ≤
            2 * (NPhi Me X.deg p q) *
              ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q := by
        intro σ hσ
        have hb : σ.B.length ≤ 2 * q + 1 := by
          have := levelP_B_length X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k σ hσ
          omega
        have hM : (MlOf Me X.deg p q) σ.B.length ≤ (profM Me p q (2 * q + 1)).eval X.deg := by
          simpa [MlOf] using profM_eval_mono Me p q X.deg hb
        have hpow : ((MlOf Me X.deg p q) σ.B.length + 1) ^ q ≤
            ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q :=
          Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) q
        have hstep1 : 2 * (testL q ((MlOf Me X.deg p q) σ.B.length) (NPhi Me X.deg p q)).length
            ≤ 2 * ((NPhi Me X.deg p q) *
                ((MlOf Me X.deg p q) σ.B.length + 1) ^ q * q) :=
          Nat.mul_le_mul_left 2 (testL_length q _ _)
        have hstep2 : 2 * ((NPhi Me X.deg p q) *
              ((MlOf Me X.deg p q) σ.B.length + 1) ^ q * q)
            ≤ 2 * ((NPhi Me X.deg p q) *
                ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q) := by
          refine Nat.mul_le_mul_left 2 ?_
          refine Nat.mul_le_mul_right q ?_
          exact Nat.mul_le_mul_left (NPhi Me X.deg p q) hpow
        calc (childrenP X.c (MlOf Me X.deg p q) (NPhi Me X.deg p q) σ).length
            ≤ 2 * (testL q ((MlOf Me X.deg p q) σ.B.length) (NPhi Me X.deg p q)).length :=
              childrenP_length_le X _ _ σ
          _ ≤ 2 * ((NPhi Me X.deg p q) *
                ((MlOf Me X.deg p q) σ.B.length + 1) ^ q * q) := hstep1
          _ ≤ 2 * ((NPhi Me X.deg p q) *
                ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q) := hstep2
          _ = 2 * (NPhi Me X.deg p q) *
                ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q := by ring
      calc ((levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).map
              (fun σ => (childrenP X.c (MlOf Me X.deg p q) (NPhi Me X.deg p q) σ).length)).sum
          ≤ ((levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).map
              (fun _ => 2 * (NPhi Me X.deg p q) *
                ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q)).sum :=
            List.sum_le_sum hstep
        _ = (levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).length *
              (2 * (NPhi Me X.deg p q) *
                ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q) := sum_map_const _ _
        _ ≤ (profCount Me p q k).eval X.deg *
              (2 * (NPhi Me X.deg p q) *
                ((profM Me p q (2 * q + 1)).eval X.deg + 1) ^ q * q) :=
            Nat.mul_le_mul_right _ (ih hk')
        _ = (profCount Me p q (k + 1)).eval X.deg := by
            rw [profCount_eval_succ]
            simp only [NPhi]

/-- The total number of flat leaves produced up to level `q` is bounded by `bCount`. -/
private lemma allStrataP_length_le {p q : ℕ} (X : SemiPf (p + q)) (Me : Polynomial ℕ) :
    (allStrataP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) q).length ≤
      (bCount Me p q).eval X.deg := by
  have hall : (allStrataP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) q).length =
      ((List.range (q + 1)).map (fun k =>
        (levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).length)).sum := by
    simp only [allStrataP, List.length_flatMap, List.length_map]
  rw [hall, bCount, Polynomial.eval_mul, Polynomial.eval_C]
  have hterm : ∀ k ∈ List.range (q + 1),
      (levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).length ≤
        (profCount Me p q q).eval X.deg := by
    intro k hk
    rw [List.mem_range] at hk
    exact (levelP_length_le X Me k (by omega)).trans (profCount_eval_le (by omega))
  calc ((List.range (q + 1)).map (fun k =>
          (levelP X (MlOf Me X.deg p q) (NPhi Me X.deg p q) k).length)).sum
      ≤ ((List.range (q + 1)).map (fun _ => (profCount Me p q q).eval X.deg)).sum :=
        List.sum_le_sum hterm
    _ = (q + 1) * (profCount Me p q q).eval X.deg := by
        rw [sum_map_const, List.length_range]

theorem countP {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Me : Polynomial ℕ) :
    (∀ k ∈ Finset.range (q + 1),
        (Work.WilE5.levelP X (Work.WilE5.MlOf Me X.deg p q) (Work.WilE5.NPhi Me X.deg p q) k).length ≤
          (Work.WilE5.profCount Me p q k).eval X.deg) ∧
    (Work.WilE5.allStrataP X (Work.WilE5.MlOf Me X.deg p q) (Work.WilE5.NPhi Me X.deg p q) q).length ≤
      (Work.WilE5.bCount Me p q).eval X.deg := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have hkq : k ≤ q := by rw [Finset.mem_range] at hk; omega
    exact levelP_length_le X Me k hkq
  · exact allStrataP_length_le X Me

end Work.WilE5.Bounds
