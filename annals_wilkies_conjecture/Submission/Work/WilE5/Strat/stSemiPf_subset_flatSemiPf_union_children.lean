import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat
open WilkiesDesign WilkiesDesign.E

variable {p q r M NΦ : ℕ}

/-! ## Helper lemmas: the test list, the test order and the state conditions -/

/-- Membership in the list of tests. -/
theorem mem_testL_iff (t : Test q) :
    t ∈ testL q M NΦ ↔ t.i < NΦ ∧ t.m ∈ mList q M ∧ t.m t.l ≠ 0 := by
  rw [testL, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hmem, hne⟩
    obtain ⟨⟨a, b, c⟩, hp, rfl⟩ := List.mem_map.mp hmem
    have hp1 : a ∈ List.range NΦ := (List.mem_product.mp hp).1
    have hp2 : (b, c) ∈ (mList q M).product (List.finRange q) := (List.mem_product.mp hp).2
    have hb : b ∈ mList q M := (List.mem_product.mp hp2).1
    exact ⟨List.mem_range.mp hp1, hb, hne⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨List.mem_map.mpr ⟨(t.i, (t.m, t.l)), ?_, rfl⟩, h3⟩
    exact List.mem_product.mpr ⟨List.mem_range.mpr h1,
      List.mem_product.mpr ⟨h2, List.mem_finRange t.l⟩⟩

/-- Membership in the list of tests preceding `t`. -/
theorem mem_prec_iff (σ : St p q r) (t t' : Test q) :
    t' ∈ prec M NΦ σ t ↔ t' ∈ testL q M NΦ ∧ valid σ t' ∧ testLt t' t = true := by
  rw [prec, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (decide (valid σ t') && testLt t' t) = true := of_decide_eq_true h2
    have h3' : decide (valid σ t') = true ∧ testLt t' t = true := by
      simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using h3
    exact ⟨h1, of_decide_eq_true h3'.1, h3'.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rw [decide_eq_true_eq, Bool.and_eq_true_eq_eq_true_and_eq_true]
    exact ⟨decide_eq_true_eq.mpr h2, h3⟩

/-- `yOpSt` with the zero multi-index is the identity. -/
theorem yOpSt_zero (c : EAChain (p + q) r) (B : List (EAPoly (p + q) r × Fin q))
    (ψ : EAPoly (p + q) r) : yOpSt c B (0 : Fin q → ℕ) ψ = ψ := by
  unfold yOpSt
  induction (List.finRange q) with
  | nil => rfl
  | cons l ls ih => rw [List.foldr_cons, Pi.zero_apply, Function.iterate_zero_apply, ih]

/-- `testPoly` in range is the corresponding member of the flatness family. -/
theorem testPoly_eq (σ : St p q r) {i : ℕ} (h : i < σ.Φ.length) :
    testPoly σ i = σ.Φ[i] := by
  rw [testPoly, List.getElem?_eq_getElem h, Option.getD_some]

/-- `testPoly` in range is a member of the flatness family. -/
theorem testPoly_mem (σ : St p q r) {i : ℕ} (h : i < σ.Φ.length) :
    testPoly σ i ∈ σ.Φ := by
  rw [testPoly_eq σ h]
  exact (List.mem_iff_getElem).mpr ⟨i, h, rfl⟩

/-- The peeled test is `testLt`-below the original test. -/
theorem testLt_peel (t : Test q) (l' : Fin q) (h : t.m t.l ≠ 0) :
    testLt (⟨t.i, mDec t.m t.l, l'⟩ : Test q) t = true := by
  unfold testLt
  rw [if_neg (lt_irrefl t.i), if_neg (lt_irrefl t.i)]
  have hsum : mSum (mDec t.m t.l) < mSum t.m := by
    rw [mSum_mDec t.m t.l h]
    have h1 : t.m t.l ≤ mSum t.m := by
      simpa [mSum] using Finset.single_le_sum (s := Finset.univ) (f := t.m)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ t.l)
    omega
  rw [if_pos hsum]

/-- The peeled test is again valid: its multi-index still vanishes in all pivots. -/
theorem valid_dec (σ : St p q r) (t : Test q) (l' : Fin q)
    (h : valid σ t) (hl : t.m t.l ≠ 0) : valid σ (⟨t.i, mDec t.m t.l, l'⟩ : Test q) := by
  obtain ⟨hi, hpiv⟩ := h
  refine ⟨hi, fun a => ?_⟩
  have ha := hpiv a
  simp only [mDec, Pi.sub_apply]
  by_cases hla : (σ.B.get a).2 = t.l
  · rw [hla] at ha
    exact absurd ha hl
  · rw [Pi.single_eq_of_ne hla, Nat.sub_zero]
    exact ha

/-- `opVal` does not depend on the peeled direction, so it agrees with `peelVal`. -/
theorem opVal_peel (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) (l' : Fin q) :
    opVal c σ (⟨t.i, mDec t.m t.l, l'⟩ : Test q) = peelVal c σ t := rfl

/-! ## The sets of a state and of a child -/

/-- The flat leaf, described by the conditions of the state and the vanishing of all the valid
test operators. -/
theorem flatSemiPf_set_eq {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    (flatSemiPf X M NΦ σ).set = X.set ∩ {x | (stCond σ).holds X.c x ∧
      ∀ f ∈ flatEqs X.c M NΦ σ, eaEval X.c f x = 0} := by
  rw [show flatSemiPf X M NΦ σ = semiPfAnd (semiPfAnd X (stCond σ))
      (Basic.eqsOf (flatEqs X.c M NΦ σ)) from rfl, semiPfAnd_set, semiPfAnd_set,
    show (semiPfAnd X (stCond σ)).c = X.c from rfl]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, (Basic.holds_eqsOf X.c (flatEqs X.c M NΦ σ) x).mp h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, (Basic.holds_eqsOf X.c (flatEqs X.c M NΦ σ) x).mpr h.2.2⟩

/-- The conditions of a child, spelled out. -/
theorem stCond_child_holds (c : EAChain (p + q) r) (M NΦ : ℕ) (σ : St p q r)
    (t : Test q) (s : Bool) (x : Fin (p + q) → ℝ) :
    (stCond (childSt c M NΦ σ t s)).holds c x ↔
      (stCond σ).holds c x ∧
      (∀ t' ∈ prec M NΦ σ t, eaEval c (opVal c σ t') x = 0) ∧
      eaEval c (peelVal c σ t) x = 0 ∧
      (if s then 0 < eaEval c (opVal c σ t) x else eaEval c (opVal c σ t) x < 0) := by
  cases s
  · have h1 : childν c σ t false = σ.ν ++ [-opVal c σ t] := rfl
    have h2 : (if (false : Bool) then (0 < eaEval c (opVal c σ t) x)
        else (eaEval c (opVal c σ t) x < 0)) ↔ (eaEval c (opVal c σ t) x < 0) := Iff.rfl
    simp only [stCond, childSt, childB, childΞ, h1, h2, Basic.holds, List.map_append,
      List.map_cons, List.map_nil, List.forall_mem_append, List.forall_mem_singleton,
      List.forall_mem_map, eaEval_neg, neg_pos]
    tauto
  · have h1 : childν c σ t true = σ.ν ++ [opVal c σ t] := rfl
    have h2 : (if (true : Bool) then (0 < eaEval c (opVal c σ t) x)
        else (eaEval c (opVal c σ t) x < 0)) ↔ (0 < eaEval c (opVal c σ t) x) := Iff.rfl
    simp only [stCond, childSt, childB, childΞ, h1, h2, Basic.holds, List.map_append,
      List.map_cons, List.map_nil, List.forall_mem_append, List.forall_mem_singleton,
      List.forall_mem_map]
    tauto

/-- The set of a child, spelled out. -/
theorem stSemiPf_child_set_eq {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) :
    (stSemiPf X (childSt X.c M NΦ σ t s)).set =
      X.set ∩ {x | (stCond σ).holds X.c x ∧
        (∀ t' ∈ prec M NΦ σ t, eaEval X.c (opVal X.c σ t') x = 0) ∧
        eaEval X.c (peelVal X.c σ t) x = 0 ∧
        (if s then 0 < eaEval X.c (opVal X.c σ t) x else eaEval X.c (opVal X.c σ t) x < 0)} := by
  have h1 : (stSemiPf X (childSt X.c M NΦ σ t s)).set
      = X.set ∩ {x | (stCond (childSt X.c M NΦ σ t s)).holds X.c x} :=
    semiPfAnd_set X (stCond (childSt X.c M NΦ σ t s))
  rw [h1]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  exact stCond_child_holds X.c M NΦ σ t s x

/-! ## A rank on the tests, decreasing along `testLt` -/

/-- Positional value of a digit list (most significant digit first) in base `B`. -/
def mval (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => a * B ^ as.length + mval B as

theorem mval_succ_le {B : ℕ} (hB : 1 ≤ B) : ∀ {xs : List ℕ},
    (∀ a ∈ xs, a ≤ B - 1) → mval B xs + 1 ≤ B ^ xs.length
  | [], _ => by simp [mval]
  | a :: as, h => by
    have ha : a ≤ B - 1 := h a (by simp)
    have has : ∀ b ∈ as, b ≤ B - 1 := fun b hb => h b (by simp [hb])
    have h1 : mval B as + 1 ≤ B ^ as.length := mval_succ_le hB has
    have h2 : a + 1 ≤ B := by omega
    have hgoal : mval B (a :: as) + 1 = a * B ^ as.length + (mval B as + 1) := by
      simp only [mval]; omega
    rw [hgoal]
    calc a * B ^ as.length + (mval B as + 1)
        ≤ a * B ^ as.length + B ^ as.length := Nat.add_le_add_left h1 _
      _ = (a + 1) * B ^ as.length := by ring
      _ ≤ B * B ^ as.length := Nat.mul_le_mul h2 le_rfl
      _ = B ^ (as.length + 1) := by rw [pow_succ]; ring

theorem mval_lt_of_mlexLtAux {B : ℕ} (hB : 1 ≤ B) {xs ys : List ℕ}
    (h : mlexLtAux xs ys = true) (hlen : xs.length = ys.length)
    (hx : ∀ a ∈ xs, a ≤ B - 1) (hy : ∀ a ∈ ys, a ≤ B - 1) :
    mval B xs < mval B ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact absurd h (by decide)
    | cons b bs => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons a as ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons b bs =>
      have hxy : ∀ x ∈ as, x ≤ B - 1 := fun x hx' => hx x (by simp [hx'])
      have hyy : ∀ x ∈ bs, x ≤ B - 1 := fun x hx' => hy x (by simp [hx'])
      have hlen' : as.length = bs.length := by
        simp only [List.length_cons] at hlen; omega
      have h1 : mval B as + 1 ≤ B ^ as.length := mval_succ_le hB hxy
      by_cases hab : a < b
      · have h2 : a + 1 ≤ b := by omega
        have key : a * B ^ as.length + mval B as + 1 ≤ b * B ^ bs.length + mval B bs := by
          have h1' : mval B as + 1 ≤ B ^ bs.length := by rw [← hlen']; exact h1
          rw [hlen']
          have e1 : a * B ^ bs.length + (mval B as + 1)
              ≤ a * B ^ bs.length + B ^ bs.length := Nat.add_le_add_left h1' _
          have e2 : a * B ^ bs.length + B ^ bs.length = (a + 1) * B ^ bs.length := by ring
          have e3 : (a + 1) * B ^ bs.length ≤ b * B ^ bs.length := Nat.mul_le_mul h2 le_rfl
          omega
        simp only [mval]
        omega
      · have hba : ¬ (b < a) := by
          intro hc
          have hh := h
          simp only [mlexLtAux] at hh
          rw [if_neg hab, if_pos hc] at hh
          exact absurd hh (by decide)
        have hrec : mlexLtAux as bs = true := by
          have hh := h
          simp only [mlexLtAux] at hh
          rwa [if_neg hab, if_neg hba] at hh
        have hab' : a = b := by omega
        subst hab'
        have hih : mval B as < mval B bs := ih hrec hlen' hxy hyy
        simp only [mval]
        rw [hlen']
        omega

theorem mval_eq_of_mlexLtAux_eq_false {B : ℕ} {xs ys : List ℕ}
    (h1 : mlexLtAux xs ys = false) (h2 : mlexLtAux ys xs = false)
    (hlen : xs.length = ys.length) : mval B xs = mval B ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp only [mval]
    | cons b bs => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons a as ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons b bs =>
      have hlen' : as.length = bs.length := by
        simp only [List.length_cons] at hlen; omega
      have hab : ¬ (a < b) := by
        intro hc
        have hh := h1
        simp only [mlexLtAux] at hh
        rw [if_pos hc] at hh
        exact absurd hh (by decide)
      have hba : ¬ (b < a) := by
        intro hc
        have hh := h2
        simp only [mlexLtAux] at hh
        rw [if_pos hc] at hh
        exact absurd hh (by decide)
      have h1' : mlexLtAux as bs = false := by
        have hh := h1
        simp only [mlexLtAux] at hh
        rwa [if_neg hab, if_neg hba] at hh
      have h2' : mlexLtAux bs as = false := by
        have hh := h2
        simp only [mlexLtAux] at hh
        rwa [if_neg hba, if_neg hab] at hh
      have hab' : a = b := by omega
      have hrec : mval B as = mval B bs := ih h1' h2' hlen'
      simp only [mval, hab', hlen', hrec]

theorem mSum_le_mul {q M : ℕ} {m : Fin q → ℕ} (hm : m ∈ mList q M) : mSum m ≤ q * M := by
  rw [mem_mList_iff] at hm
  calc mSum m = ∑ i : Fin q, m i := rfl
    _ ≤ ∑ _i : Fin q, M := Finset.sum_le_sum fun i _ => hm i
    _ = q * M := by simp [Finset.sum_const]

theorem mval_ofFn_succ_le {q M : ℕ} {m : Fin q → ℕ} (hm : m ∈ mList q M) :
    mval (M + 1) (List.ofFn m) + 1 ≤ (M + 1) ^ q := by
  have h : ∀ a ∈ List.ofFn m, a ≤ (M + 1) - 1 := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [mem_mList_iff] at hm
    have := hm i
    omega
  simpa [List.length_ofFn] using mval_succ_le (B := M + 1) (by omega) h

/-- A rank on tests, strictly decreasing along `testLt`. -/
def tRank (q M : ℕ) (t : Test q) : ℕ :=
  ((t.i * (q * M + 1) + mSum t.m) * (M + 1) ^ q + mval (M + 1) (List.ofFn t.m)) * (q + 1)
    + t.l.val

theorem lt_mul_succ_add {q X Y l l' : ℕ} (h : X < Y) (hl : l < q + 1) :
    X * (q + 1) + l < Y * (q + 1) + l' := by
  have h1 : X + 1 ≤ Y := by omega
  have h2 : X * (q + 1) + (q + 1) ≤ Y * (q + 1) := by
    have := Nat.mul_le_mul h1 (le_refl (q + 1))
    rwa [Nat.add_mul, one_mul] at this
  omega

theorem inner_lt {q M κ κ' mv mv' : ℕ} (hκ : κ + 1 ≤ κ') (hmv : mv + 1 ≤ (M + 1) ^ q) :
    κ * (M + 1) ^ q + mv < κ' * (M + 1) ^ q + mv' := by
  have h1 := Nat.mul_le_mul hκ (le_refl ((M + 1) ^ q))
  rw [Nat.add_mul, one_mul] at h1
  omega

theorem tRank_lt_of_testLt {q M : ℕ} {t t' : Test q} (h : testLt t t' = true)
    (hm : t.m ∈ mList q M) (hm' : t'.m ∈ mList q M) :
    tRank q M t < tRank q M t' := by
  have hb : ∀ a ∈ List.ofFn t.m, a ≤ M := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [mem_mList_iff] at hm
    have := hm i
    omega
  have hb' : ∀ a ∈ List.ofFn t'.m, a ≤ M := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [mem_mList_iff] at hm'
    have := hm' i
    omega
  have hp : mval (M + 1) (List.ofFn t.m) + 1 ≤ (M + 1) ^ q := mval_ofFn_succ_le hm
  have hs : mSum t.m ≤ q * M := mSum_le_mul hm
  have hl : t.l.val < q + 1 := by have := t.l.isLt; omega
  have key : (t.i * (q * M + 1) + mSum t.m) * (M + 1) ^ q + mval (M + 1) (List.ofFn t.m)
          < (t'.i * (q * M + 1) + mSum t'.m) * (M + 1) ^ q + mval (M + 1) (List.ofFn t'.m)
        ∨ ((t.i * (q * M + 1) + mSum t.m) * (M + 1) ^ q + mval (M + 1) (List.ofFn t.m)
            = (t'.i * (q * M + 1) + mSum t'.m) * (M + 1) ^ q + mval (M + 1) (List.ofFn t'.m)
          ∧ t.l.val < t'.l.val) := by
    unfold testLt at h
    by_cases h1 : t.i < t'.i
    · rw [if_pos h1] at h
      refine Or.inl (inner_lt ?_ hp)
      have h1' : t.i + 1 ≤ t'.i := by omega
      have h2 := Nat.mul_le_mul h1' (le_refl (q * M + 1))
      rw [Nat.add_mul, one_mul] at h2
      omega
    · rw [if_neg h1] at h
      by_cases h2 : t'.i < t.i
      · rw [if_pos h2] at h
        exact absurd h (by decide)
      · rw [if_neg h2] at h
        have hi : t.i = t'.i := by omega
        by_cases h3 : mSum t.m < mSum t'.m
        · rw [if_pos h3] at h
          refine Or.inl (inner_lt ?_ hp)
          rw [hi]; omega
        · rw [if_neg h3] at h
          by_cases h4 : mSum t'.m < mSum t.m
          · rw [if_pos h4] at h
            exact absurd h (by decide)
          · rw [if_neg h4] at h
            have hsum : mSum t.m = mSum t'.m := by omega
            by_cases h5 : mlexLtAux (List.ofFn t.m) (List.ofFn t'.m) = true
            · rw [if_pos h5] at h
              refine Or.inl ?_
              have hmv : mval (M + 1) (List.ofFn t.m) < mval (M + 1) (List.ofFn t'.m) :=
                mval_lt_of_mlexLtAux (by omega) h5 (by simp [List.length_ofFn]) hb hb'
              rw [hi, hsum]
              omega
            · rw [if_neg h5] at h
              by_cases h6 : mlexLtAux (List.ofFn t'.m) (List.ofFn t.m) = true
              · rw [if_pos h6] at h
                exact absurd h (by decide)
              · rw [if_neg h6] at h
                have h5' : mlexLtAux (List.ofFn t.m) (List.ofFn t'.m) = false :=
                  Bool.eq_false_of_not_eq_true h5
                have h6' : mlexLtAux (List.ofFn t'.m) (List.ofFn t.m) = false :=
                  Bool.eq_false_of_not_eq_true h6
                have hmv : mval (M + 1) (List.ofFn t.m) = mval (M + 1) (List.ofFn t'.m) :=
                  mval_eq_of_mlexLtAux_eq_false h5' h6' (by simp [List.length_ofFn])
                refine Or.inr ⟨?_, of_decide_eq_true h⟩
                rw [hi, hsum, hmv]
  rcases key with hlt | ⟨heq, hll⟩
  · exact lt_mul_succ_add hlt hl
  · have hgoal : tRank q M t < tRank q M t' := by
      simp only [tRank]
      rw [heq]
      exact Nat.add_lt_add_left hll _
    exact hgoal

/-! ## The covering step -/

/-- There is a `testLt`-least valid test on which `g` does not vanish. -/
theorem exists_minimal_valid_test_aux {p q r : ℕ} (σ : St p q r) (M NΦ : ℕ)
    (g : Test q → ℝ)
    (hne : ∃ t ∈ testL q M NΦ, valid σ t ∧ g t ≠ 0) :
    ∃ t ∈ testL q M NΦ, valid σ t ∧ g t ≠ 0 ∧
      ∀ t' ∈ testL q M NΦ, valid σ t' → testLt t' t = true → g t' = 0 := by
  classical
  obtain ⟨t, ht, hv, hg⟩ := hne
  let S : Finset (Test q) := (testL q M NΦ).toFinset.filter (fun t => valid σ t ∧ g t ≠ 0)
  have hSne : S.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ht, hv, hg⟩⟩
  obtain ⟨t₀, ht₀, hmin⟩ := Finset.exists_min_image S (tRank q M) hSne
  have ht₀' := Finset.mem_filter.mp ht₀
  have ht₀L : t₀ ∈ testL q M NΦ := List.mem_toFinset.mp ht₀'.1
  refine ⟨t₀, ht₀L, ht₀'.2.1, ht₀'.2.2, ?_⟩
  intro t' ht' hv' hlt'
  by_contra hg'
  have ht'S : t' ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ht', hv', hg'⟩
  have hle : tRank q M t₀ ≤ tRank q M t' := hmin t' ht'S
  have hlt : tRank q M t' < tRank q M t₀ :=
    tRank_lt_of_testLt hlt' ((mem_testL_iff t').mp ht').2.1 ((mem_testL_iff t₀).mp ht₀L).2.1
  omega

theorem stSemiPf_subset_flatSemiPf_union_children {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r)
    (hΦ : ∀ ψ ∈ σ.Φ, ∀ w ∈ (Work.WilE5.stSemiPf X σ).set, WilkiesDesign.E.eaEval X.c ψ w = 0)
    {z : Fin (p + q) → ℝ} (hz : z ∈ (Work.WilE5.stSemiPf X σ).set) :
    z ∈ (Work.WilE5.flatSemiPf X M NΦ σ).set ∨
      ∃ t ∈ Work.WilE5.testL q M NΦ, ∃ s : Bool,
        z ∈ (Work.WilE5.stSemiPf X (Work.WilE5.childSt X.c M NΦ σ t s)).set := by
  classical
  have hz' : z ∈ X.set ∧ (stCond σ).holds X.c z := by
    have h := hz
    rw [show (stSemiPf X σ).set = X.set ∩ {x | (stCond σ).holds X.c x} from
      semiPfAnd_set X (stCond σ)] at h
    simpa only [Set.mem_inter_iff, Set.mem_setOf_eq] using h
  by_cases hfl : ∀ t ∈ testL q M NΦ, valid σ t → eaEval X.c (opVal X.c σ t) z = 0
  · left
    rw [flatSemiPf_set_eq (X := X) (M := M) (NΦ := NΦ) (σ := σ)]
    refine ⟨hz'.1, hz'.2, ?_⟩
    intro f hf
    rw [flatEqs, List.mem_map] at hf
    obtain ⟨t, ht, rfl⟩ := hf
    rw [List.mem_filter] at ht
    exact hfl t ht.1 (of_decide_eq_true ht.2)
  · right
    push_neg at hfl
    obtain ⟨t, ht, hvt, htne, hprec0⟩ :=
      exists_minimal_valid_test_aux σ M NΦ (fun t => eaEval X.c (opVal X.c σ t) z) hfl
    have hprec : ∀ t' ∈ prec M NΦ σ t, eaEval X.c (opVal X.c σ t') z = 0 := by
      intro t' ht'
      obtain ⟨h1, h2, h3⟩ := (mem_prec_iff σ t t').mp ht'
      exact hprec0 t' h1 h2 h3
    have hpeel : eaEval X.c (peelVal X.c σ t) z = 0 := by
      by_cases hz0 : mDec t.m t.l = 0
      · rw [peelVal, hz0, yOpSt_zero]
        exact hΦ _ (testPoly_mem σ hvt.1) z hz
      · obtain ⟨l', hl'⟩ : ∃ l', mDec t.m t.l l' ≠ 0 := by
          simpa [Pi.zero_apply] using Function.ne_iff.mp hz0
        have hmemL := (mem_testL_iff t).mp ht
        have hmem : (⟨t.i, mDec t.m t.l, l'⟩ : Test q) ∈ testL q M NΦ :=
          (mem_testL_iff _).mpr ⟨hmemL.1, mDec_mem_mList hmemL.2.1 t.l, hl'⟩
        have hv : valid σ (⟨t.i, mDec t.m t.l, l'⟩ : Test q) :=
          valid_dec σ t l' hvt hmemL.2.2
        have hlt := testLt_peel t l' hmemL.2.2
        have hh := hprec0 _ hmem hv hlt
        simpa only [opVal_peel] using hh
    rcases lt_or_gt_of_ne htne with hneg | hpos
    · refine ⟨t, ht, false, ?_⟩
      rw [stSemiPf_child_set_eq (X := X) (M := M) (NΦ := NΦ) (σ := σ) (t := t) (s := false)]
      refine ⟨hz'.1, hz'.2, hprec, hpeel, ?_⟩
      simpa using hneg
    · refine ⟨t, ht, true, ?_⟩
      rw [stSemiPf_child_set_eq (X := X) (M := M) (NΦ := NΦ) (σ := σ) (t := t) (s := true)]
      refine ⟨hz'.1, hz'.2, hprec, hpeel, ?_⟩
      simpa using hpos

end Work.WilE5.Strat
