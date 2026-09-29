import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.lamDefs
import Submission.Work.Resample.lamFacts
import Submission.Work.Resample.lamMath
import Submission.Work.Resample.sigRecWord
import Submission.Work.Resample.lamElemWord

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Small helpers -/

theorem isz_nat_le_of_lt {A x : ℕ} (h : x < 2 ^ A) : isz ((x : ℤ)) ≤ A + 2 := by
  rw [isz, Int.natAbs_natCast]
  exact Nat.add_le_add_right (Nat.size_le.mpr h) 2

theorem buSZ_le_pow (p : ℕ) : buSZ p ≤ 100000 * (p + 1) ^ 2 := by
  simp only [buSZ]; nlinarith [Nat.zero_le p]

theorem egLam_le_self (s t i : ℕ) : egLam s t i ≤ s + i := by
  unfold egLam
  split
  · rename_i h
    exact le_trans (Nat.le_of_lt (Classical.choose h).isLt) (Nat.le_add_right s i)
  · exact le_rfl

private theorem range_map_eq_ofFn {α : Type} (t : ℕ) (g : ℕ → α) :
    (List.range t).map g = List.ofFn (fun i : Fin t => g i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem zl_ofFn_eq (t : ℕ) (f : ℕ → ℤ) :
    zl (List.ofFn (fun i : Fin t => f i)) =
      ofList ((List.range t).map (fun i => Val.int (f i))) := by
  rw [zl, List.map_ofFn]
  congr 1
  exact (range_map_eq_ofFn t (fun i => Val.int (f i))).symm

theorem cost_pick_le {A : List Val} {k K CU B p M : ℕ}
    (hK : 100000000 * K ≤ CU) (hM : M ≤ 1000000 * (p + 1) ^ 2)
    (hk : k + 1 ≤ 8) (hlen : A.length ≤ 9) (hA : ∀ v ∈ A, vsz v ≤ M)
    (hB : (p + 1) ^ 2 ≤ B) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ CU * B := by
  have h1 : (A.take (k + 1)).length ≤ 8 := by rw [List.length_take]; omega
  have h2 : szl (A.take (k + 1)) ≤ 8 * M :=
    le_trans (szl_le_len_mul (fun v hv => hA v (List.mem_of_mem_take hv)))
      (Nat.mul_le_mul_right _ h1)
  have h3 : szl (A.take (k + 1)) + 1 ≤ 9000000 * (p + 1) ^ 2 := by
    have h4 : 8 * M + 1 ≤ 9000000 * (p + 1) ^ 2 := by nlinarith [hM, Nat.zero_le p]
    omega
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ K * 8 * (9000000 * (p + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) h3
    _ ≤ 100000000 * K * (p + 1) ^ 2 := by
        have h8 : (8 : ℕ) * 9000000 ≤ 100000000 := by norm_num
        nlinarith
    _ ≤ CU * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hK
    _ ≤ CU * B := Nat.mul_le_mul_left _ hB

/-- The window identity of a one-element `mapList` body. -/
theorem two_le_hundredK (p : ℕ) : (2 : ℕ) ≤ 100000 * (p + 1) ^ 2 := by
  have h : 1 ≤ (p + 1) ^ 2 := Nat.one_le_pow 2 (p + 1) (by omega)
  calc (2 : ℕ) = 2 * 1 := by ring
    _ ≤ 2 * (p + 1) ^ 2 := Nat.mul_le_mul_left 2 h
    _ ≤ 100000 * (p + 1) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)

theorem le_hundredK {p x : ℕ} (h : x ≤ p + 3) : x ≤ 100000 * (p + 1) ^ 2 := by
  have h1 : p + 3 ≤ 4 * (p + 1) := by omega
  have h2 : 4 * (p + 1) ≤ 4 * (p + 1) ^ 2 := by
    have h3 : 1 ≤ (p + 1) := by omega
    calc 4 * (p + 1) = 4 * (p + 1) * 1 := by ring
      _ ≤ 4 * (p + 1) * (p + 1) := Nat.mul_le_mul_left _ h3
      _ = 4 * (p + 1) ^ 2 := by ring
  have h4 : 4 * (p + 1) ^ 2 ≤ 100000 * (p + 1) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
  exact le_trans h (le_trans (le_trans h1 h2) h4)

theorem window3 {a b c : Val} {W rest : List Val} :
    [a, b, c] ++ (W ++ rest) = a :: (([b, c] ++ W) ++ rest) := by
  simp [List.cons_append, List.append_assoc]

/-- A pointwise relation on equal-length lists gives `Forall₂`. -/
theorem forall₂_of_get {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) →
      List.Forall₂ R l₁ l₂
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | a :: t, b :: u, hlen, h => by
      refine List.Forall₂.cons (h 0 (by simp) (by simp)) (forall₂_of_get ?_ ?_)
      · simpa using hlen
      · intro i h1 h2
        have h3 := h (i + 1) (by simpa using h1) (by simpa using h2)
        simpa using h3

/-- Pointwise maps of a list are related by `Forall₂`. -/
theorem forall₂_map_map {α β : Type} (R : α → α → Prop) (l : List β) (f g : β → α)
    (h : ∀ a ∈ l, R (f a) (g a)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- Right-uniqueness lifts to `Forall₂`. -/
theorem forall₂_right_unique {α β : Type} {R : α → β → Prop}
    (hR : ∀ a b c, R a b → R a c → b = c) :
    ∀ {l : List α} {m1 m2 : List β}, List.Forall₂ R l m1 → List.Forall₂ R l m2 → m1 = m2 := by
  intro l
  induction l with
  | nil =>
    intro m1 m2 h1 h2
    cases h1
    cases h2
    rfl
  | cons a t ih =>
    intro m1 m2 h1 h2
    cases h1 with
    | cons hb1 ht1 =>
      cases h2 with
      | cons hb2 ht2 =>
        have hb : _ = _ := hR a _ _ hb1 hb2
        rw [hb, ih ht1 ht2]

theorem vsz_ofList' (l : List Val) : vsz (ofList l) = l.length + 1 + szl l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h : ofList (a :: t) = Val.cons a (ofList t) := rfl
    rw [h, vsz_cons, ih, List.length_cons, szl_cons]
    ring

theorem cost_two_le {K CU B p M a b : ℕ} (hK : 100000000 * K ≤ CU) (ha : a ≤ M) (hb : b ≤ M)
    (hM : M ≤ 1000000 * (p + 1) ^ 2) (hB : (p + 1) ^ 2 ≤ B) :
    K * (a + b + 1) ≤ CU * B := by
  have h1 : a + b + 1 ≤ 3000000 * (p + 1) ^ 2 := by nlinarith [hM, Nat.zero_le p]
  calc K * (a + b + 1) ≤ K * (3000000 * (p + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ ≤ 100000000 * K * (p + 1) ^ 2 := by
        have h3 : (3000000 : ℕ) ≤ 100000000 := by norm_num
        nlinarith
    _ ≤ CU * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hK
    _ ≤ CU * B := Nat.mul_le_mul_left _ hB

theorem cost_one_le {K CU B p M a : ℕ} (hK : 100000000 * K ≤ CU) (ha : a ≤ M)
    (hM : M ≤ 1000000 * (p + 1) ^ 2) (hB : (p + 1) ^ 2 ≤ B) :
    K * (a + 1) ≤ CU * B := by
  have h1 : a + 1 ≤ 3000000 * (p + 1) ^ 2 := by nlinarith [hM, Nat.zero_le p]
  calc K * (a + 1) ≤ K * (3000000 * (p + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ ≤ 100000000 * K * (p + 1) ^ 2 := by
        have h3 : (3000000 : ℕ) ≤ 100000000 := by norm_num
        nlinarith
    _ ≤ CU * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hK
    _ ≤ CU * B := Nat.mul_le_mul_left _ hB

/-! ## The two element words (extracted so that the main proof stays small) -/

set_option maxHeartbeats 8000000 in
theorem lamBody1 (recProg : Cmd) (Krec : ℕ)
    (hRec : ∀ (main : Cmd) (s t k : ℕ), s < t → k < t → ∀ rest : List Val, WordR main recProg
      (fun vs => vs = [Val.cons (.int (k : ℤ)) (.int 0), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest)
      (fun vs out => vs = [Val.cons (.int (k : ℤ)) (.int 0), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest ∧
        out = [Val.cons (.int ((egSigT s t k : ℕ) : ℤ)) (.int (k : ℤ)), Val.int (s : ℤ),
          Val.int (t : ℤ)] ++ rest)
      (fun _ => Krec * (isz (k : ℤ) + isz (s : ℤ) + isz (t : ℤ) + 1) ^ Krec))
    (main : Cmd) (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) :
    ∀ (x : Val), (∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0)) →
      ∀ rest : List Val, WordR main recProg
        (fun vs => vs = x :: ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest))
        (fun _ out => ∃ y, out = y :: ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest) ∧
          (∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0) ∧ y = lamRec s t k) ∧
          vsz y ≤ 4 * p + 24)
        (fun _ => Krec * (4 * (p + 2) + 1) ^ Krec) := by
  rintro x ⟨k, hk, rfl⟩ rest vs hvs s' R hR
  have hpre : vs = [Val.cons (.int (k : ℤ)) (.int 0), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest := by
    rw [hvs]; rfl
  obtain ⟨out, s'', n, ⟨-, hout⟩, hev, hn, hstk, hoth⟩ :=
    hRec main s t k hst hk rest vs hpre s' R hR
  have hsz : vsz (lamRec s t k) ≤ 4 * p + 24 := by
    rw [lamRec, vsz_cons, vsz_int, vsz_int]
    have h1 : isz ((egSigT s t k : ℕ) : ℤ) ≤ p + 2 :=
      isz_nat_le_of_lt (lt_trans (egSigT_lt s t k (by omega)) htp)
    have h2 : isz ((k : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hk (le_of_lt htp))
    omega
  refine ⟨out, s'', n, ⟨lamRec s t k, ?_, ⟨k, hk, rfl, rfl⟩, hsz⟩, hev, ?_, hstk, hoth⟩
  · rw [hout]; rfl
  · refine le_trans hn ?_
    have h1 : isz ((k : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hk (le_of_lt htp))
    have h2 : isz ((s : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_trans hst htp)
    have h3 : isz ((t : ℤ)) ≤ p + 2 := isz_nat_le_of_lt htp
    have h4 : isz ((k : ℤ)) + isz ((s : ℤ)) + isz ((t : ℤ)) + 1 ≤ 4 * (p + 2) + 1 := by omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 Krec)

set_option maxHeartbeats 8000000 in
theorem lamBody2 (elemProg : Cmd) (Kelem : ℕ)
    (hElem : ∀ (main : Cmd) (s t m i : ℕ), s < t → m < t → i < t → ∀ rest : List Val,
      WordR main elemProg
        (fun vs => vs = [Val.cons (.int (i : ℤ)) (.int (m : ℤ)), Val.int (s : ℤ),
          Val.int (t : ℤ)] ++ rest)
        (fun vs out => vs = [Val.cons (.int (i : ℤ)) (.int (m : ℤ)), Val.int (s : ℤ),
          Val.int (t : ℤ)] ++ rest ∧
          out = [Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ)), Val.int (s : ℤ),
            Val.int (t : ℤ)] ++ rest)
        (fun _ => Kelem * (isz (i : ℤ) + isz (m : ℤ) + isz (s : ℤ) + isz (t : ℤ) + 1) ^ Kelem))
    (main : Cmd) (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) (hcop : Nat.Coprime s t) (hs : 2 ≤ s) :
    ∀ (x : Val), (∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
        x = Val.cons (.int (i : ℤ)) (.int (m : ℤ))) →
      ∀ rest : List Val, WordR main elemProg
        (fun vs => vs = x :: ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest))
        (fun _ out => ∃ y, out = y :: ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest) ∧
          (∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
            x = Val.cons (.int (i : ℤ)) (.int (m : ℤ)) ∧
            y = Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ))) ∧
          vsz y ≤ 4 * p + 24)
        (fun _ => Kelem * (4 * (p + 2) + 1) ^ Kelem) := by
  rintro x ⟨i, m, hi, hm, hσ, rfl⟩ rest vs hvs s' R hR
  have hpre : vs = [Val.cons (.int (i : ℤ)) (.int (m : ℤ)), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest := by
    rw [hvs]; rfl
  obtain ⟨out, s'', n, ⟨-, hout⟩, hev, hn, hstk, hoth⟩ :=
    hElem main s t m i hst hm hi rest vs hpre s' R hR
  have hsz : vsz (Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ))) ≤ 4 * p + 24 := by
    rw [vsz_int, lamKey_eq_egLam s t m i hs hst hcop hm hi hσ]
    have h1 : egLam s t i ≤ s + i := egLam_le_self s t i
    have h2 : s + i < s + t := Nat.add_lt_add_left hi s
    have h3 : s + t < 2 ^ (p + 1) := by omega
    have h4 : egLam s t i < 2 ^ (p + 1) := lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (le_of_lt h3))
    have h5 : egLam s t i < 2 ^ (p + 22) :=
      lt_of_lt_of_le h4 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h6 : isz ((egLam s t i : ℤ)) ≤ (p + 22) + 2 := isz_nat_le_of_lt h5
    omega
  refine ⟨out, s'', n, ⟨Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ)), ?_,
    ⟨i, m, hi, hm, hσ, rfl, rfl⟩, hsz⟩, hev, ?_, hstk, hoth⟩
  · rw [hout]; rfl
  · refine le_trans hn ?_
    have h1 : isz ((i : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hi (le_of_lt htp))
    have h2 : isz ((m : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hm (le_of_lt htp))
    have h3 : isz ((s : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hst (le_of_lt htp))
    have h4 : isz ((t : ℤ)) ≤ p + 2 := isz_nat_le_of_lt htp
    have h5 : isz ((i : ℤ)) + isz ((m : ℤ)) + isz ((s : ℤ)) + isz ((t : ℤ)) + 1 ≤ 4 * (p + 2) + 1 := by
      omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 Kelem)

/-! ## The assembly -/

theorem buLamWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hcop : Nat.Coprime s t) (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog (Work.Resample.buCB p α s t)
        (Work.Resample.buL7 p α s t :: Work.Resample.buCB p α s t)
        (K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨pickProg, Kpick, hPick⟩ := KL.pick
  obtain ⟨rollProg, Kroll, hRoll⟩ := KL.roll
  obtain ⟨dropProg, Kdrop, hDrop⟩ := KL.drop
  obtain ⟨pushProg, Kpush, hPush⟩ := KL.pushVal
  obtain ⟨swapProg, Kswap, hSwap⟩ := KL.swap
  obtain ⟨mapProg, Kmap, hMap⟩ := KL.mapList
  obtain ⟨repProg, Krep, hRep⟩ := LL.replicate
  obtain ⟨enumProg, Kenum, hEnum⟩ := LL.enumerate
  obtain ⟨sortProg, Ksort, hSort⟩ := LL.sortByKey
  obtain ⟨recProg, Krec, hRec⟩ := sigRecWord KL IL
  obtain ⟨elemProg, Kelem, hElem⟩ := lamElemWord KL IL
  let MS : ℕ := Kpick + Kroll + Kdrop + Kpush + Kswap + Kmap + Krep + Kenum + Ksort + 1
  let E : ℕ := max 6 (max Krec Kelem)
  let CU : ℕ := 1000000000 * MS + 100000 * (Krec * 10 ^ Krec) + 100000 * (Kelem * 10 ^ Kelem)
    + 1000000
  let KK : ℕ := max E (20 * CU + 20)
  refine ⟨(.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 2) (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg) repProg) enumProg) (mapProg recProg)) (.seq sortProg (mapProg elemProg))) (rollProg 2)) dropProg) (rollProg 1)) dropProg), KK, ?_⟩
  intro main p α s t hs hst hcop hα hp htp hαp
  have hMSpick : Kpick ≤ MS := by simp only [MS]; omega
  have hMSroll : Kroll ≤ MS := by simp only [MS]; omega
  have hMSdrop : Kdrop ≤ MS := by simp only [MS]; omega
  have hMSpush : Kpush ≤ MS := by simp only [MS]; omega
  have hMSswap : Kswap ≤ MS := by simp only [MS]; omega
  have hMSmap : Kmap ≤ MS := by simp only [MS]; omega
  have hMSrep : Krep ≤ MS := by simp only [MS]; omega
  have hMSenum : Kenum ≤ MS := by simp only [MS]; omega
  have hMSsort : Ksort ≤ MS := by simp only [MS]; omega
  have hKrecE : Krec ≤ E := by simp only [E]; omega
  have hKelemE : Kelem ≤ E := by simp only [E]; omega
  have ht0 : 0 < t := by omega
  have hs0 : 0 < s := by omega
  have hp0 : 0 < p := by omega
  have hCUMS : 1000000000 * MS ≤ CU := by
    simp only [CU]
    exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hCUexp : 100000 * (Krec * 10 ^ Krec) ≤ CU := by
    simp only [CU]
    exact le_trans (Nat.le_add_left _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hCUexp2 : 100000 * (Kelem * 10 ^ Kelem) ≤ CU := by
    simp only [CU]
    exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have hCUAB : 1000000000 * MS + 100000 * (Krec * 10 ^ Krec) ≤ CU := by
    simp only [CU]
    exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hCUAB2 : 1000000000 * MS + 100000 * (Kelem * 10 ^ Kelem) ≤ CU := by
    simp only [CU]
    exact le_trans (Nat.add_le_add_right (Nat.le_add_right _ _) _) (Nat.le_add_right _ _)
  have hCUbig : 1000000 ≤ CU := by
    simp only [CU]
    exact Nat.le_add_left _ _
  have hCU1 : 1 ≤ CU := le_trans (by norm_num) hCUbig
  have hKpickCU : 100000000 * Kpick ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSpick)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKrollCU : 100000000 * Kroll ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSroll)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKdropCU : 100000000 * Kdrop ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSdrop)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKpushCU : 100000000 * Kpush ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSpush)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKswapCU : 100000000 * Kswap ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSswap)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKmapCU : 100000000 * Kmap ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSmap)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKrepCU : 100000000 * Krep ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSrep)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKenumCU : 100000000 * Kenum ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSenum)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  have hKsortCU : 100000000 * Ksort ≤ CU :=
    le_trans (le_trans (Nat.mul_le_mul_left _ hMSsort)
      (Nat.mul_le_mul_right _ (by norm_num))) hCUMS
  let B : ℕ := (t + 1) * (p + 1) ^ E
  have hBE : ∀ j : ℕ, j ≤ E → (p + 1) ^ j ≤ B := by
    intro j hj
    have h1 : (p + 1) ^ j ≤ (p + 1) ^ E := Nat.pow_le_pow_right (by omega) hj
    have h2 : (p + 1) ^ E ≤ (t + 1) * (p + 1) ^ E := Nat.le_mul_of_pos_left _ (by omega)
    simp only [B]
    exact le_trans h1 h2
  have hB2 : (p + 1) ^ 2 ≤ B := hBE 2 (by simp only [E]; omega)
  have hszs : isz ((s : ℤ)) ≤ p + 2 := by
    apply isz_nat_le_of_lt
    exact lt_of_lt_of_le (by omega) (le_of_lt htp)
  have hszt : isz ((t : ℤ)) ≤ p + 2 := by
    apply isz_nat_le_of_lt
    exact htp
  have hszp : isz ((p : ℤ)) ≤ p + 2 := by
    apply isz_nat_le_of_lt
    exact Nat.lt_two_pow_self
  have hsza : isz ((α : ℤ)) ≤ p + 2 := by
    apply isz_nat_le_of_lt
    have h1 : α < p := by nlinarith [hα, hαp]
    exact lt_of_lt_of_le h1 (le_of_lt (Nat.lt_two_pow_self))
  have hBlkW : ∀ v ∈ buCB p α s t, vsz v ≤ 100000 * (p + 1) ^ 2 := by
    intro v hv
    have hsmall : ∀ x : ℕ, x < 2 ^ p → vsz (Val.int (x : ℤ)) ≤ 100000 * (p + 1) ^ 2 := by
      intro x hx
      have h2 : isz ((x : ℤ)) ≤ p + 3 :=
        isz_nat_le_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [vsz_int]
      exact le_trans h2 (le_hundredK (p := p) (x := p + 3) le_rfl)
    have hbig : ∀ z : ℤ, isz z ≤ buSZ p → vsz (Val.int z) ≤ 100000 * (p + 1) ^ 2 := by
      intro z hz
      rw [vsz_int]
      exact le_trans hz (buSZ_le_pow p)
    simp only [buCB, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h | h | h
    · rw [h]; exact hsmall p (Nat.lt_two_pow_self)
    · rw [h]; exact hsmall α (lt_trans (by nlinarith [hα, hαp]) (Nat.lt_two_pow_self))
    · rw [h]; exact hsmall s (lt_trans hst htp)
    · rw [h]; exact hsmall t htp
    · rw [h]; exact hbig _ (isz_egM_le p α)
    · rw [h]
      exact hbig _ (isz_egN_le p α s t (by omega) (by omega) (by omega))
    · rw [h]; exact hbig _ (isz_auPi_le_buSZ p)
  have hrecW : ∀ x ∈ lamRecs s t, ∃ (k : ℕ) (v : Val), x = .cons (.int k) v :=
    fun x hx => lamRec_key_lt hx
  have hnodupW : ((lamRecs s t).map pairKey).Nodup := lamRecs_key_nodup s t hcop ht0
  have hrecSzs : ∀ x ∈ lamRecs s t, vsz x ≤ 4 * p + 24 := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := lamRecs_mem hx
    rw [hkx, lamRec]
    have h1 : isz ((egSigT s t k : ℕ) : ℤ) ≤ p + 2 := by
      apply isz_nat_le_of_lt
      exact lt_trans (egSigT_lt s t k ht0) htp
    have h2 : isz ((k : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hk (le_of_lt htp))
    rw [vsz_cons, vsz_int, vsz_int]
    omega
  have hrecP2 : ∀ x ∈ lamRecs s t,
      (∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧ x = .cons (.int (i : ℤ)) (.int (m : ℤ)))
        ∧ vsz x ≤ 4 * p + 24 := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := lamRecs_mem hx
    refine ⟨⟨egSigT s t k, k, egSigT_lt s t k ht0, hk, rfl, ?_⟩, hrecSzs x hx⟩
    rw [hkx, lamRec]
  let E1 : List Val := (List.range t).map (fun i : ℕ => Val.cons (.int (i : ℤ)) (.int 0))
  let Ks : List Val := (List.range t).map (fun i : ℕ => Val.int (((egLam s t i : ℕ) : ℤ)))
  let c1 : ℕ := Krec * (4 * (p + 2) + 1) ^ Krec
  let c2 : ℕ := Kelem * (4 * (p + 2) + 1) ^ Kelem
  have hE1def : E1 = (List.range t).map (fun i : ℕ => Val.cons (.int (i : ℤ)) (.int 0)) := rfl
  have hKsdef : Ks = (List.range t).map (fun i : ℕ => Val.int (((egLam s t i : ℕ) : ℤ))) := rfl
  have hc1def : c1 = Krec * (4 * (p + 2) + 1) ^ Krec := rfl
  have hc2def : c2 = Kelem * (4 * (p + 2) + 1) ^ Kelem := rfl
  -- #################### step 1 : copy `s` ####################
  have h1 : Pipe main (pickProg 2) (buCB p α s t) (Val.int (s : ℤ) :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.pickAt main hPick (A := buCB p α s t) (k := 2) (by simp [buCB])
      (v := Val.int (s : ℤ)) (by simp [buCB])) ?_
    exact cost_pick_le (A := buCB p α s t) (k := 2) (K := Kpick) (CU := CU) (B := B) (p := p)
      (M := 100000 * (p + 1) ^ 2) hKpickCU (by nlinarith [Nat.zero_le p]) (by norm_num) (by simp [buCB]) hBlkW hB2
  -- #################### step 2 : copy `t` ####################
  have h2 : Pipe main (pickProg 4) (Val.int (s : ℤ) :: buCB p α s t)
      (Val.int (t : ℤ) :: Val.int (s : ℤ) :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.pickAt main hPick (A := Val.int (s : ℤ) :: buCB p α s t) (k := 4)
      (by simp [buCB]) (v := Val.int (t : ℤ)) (by simp [buCB])) ?_
    have hA : ∀ v ∈ Val.int (s : ℤ) :: buCB p α s t, vsz v ≤ 100000 * (p + 1) ^ 2 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · rw [h, vsz_int]
        exact le_trans hszs (le_hundredK (p := p) (x := p + 2) (by omega))
      · exact hBlkW v h
    exact cost_pick_le (A := Val.int (s : ℤ) :: buCB p α s t) (k := 4) (K := Kpick) (CU := CU)
      (B := B) (p := p) (M := 100000 * (p + 1) ^ 2) hKpickCU (by nlinarith [Nat.zero_le p])
      (by norm_num) (by simp [buCB]) hA hB2
  -- #################### step 3 : swap ####################
  have h3 : Pipe main swapProg (Val.int (t : ℤ) :: Val.int (s : ℤ) :: buCB p α s t)
      (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.appendTail (buCB p α s t)
      (Pipe.swap main hSwap (Val.int (t : ℤ)) (Val.int (s : ℤ)))) ?_
    rw [vsz_int, vsz_int]
    exact cost_two_le (K := Kswap) (CU := CU) (B := B) (p := p) (M := 100000 * (p + 1) ^ 2)
      (a := isz ((t : ℤ))) (b := isz ((s : ℤ))) hKswapCU
      (le_trans hszt (le_hundredK (p := p) (x := p + 2) (by omega)))
      (le_trans hszs (le_hundredK (p := p) (x := p + 2) (by omega)))
      (by nlinarith [Nat.zero_le p]) hB2
  -- #################### step 4 : copy `t` again ####################
  have h4 : Pipe main (pickProg 5) (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.pickAt main hPick (A := Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (k := 5) (by simp [buCB]) (v := Val.int (t : ℤ)) (by simp [buCB])) ?_
    have hA : ∀ v ∈ Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t,
        vsz v ≤ 100000 * (p + 1) ^ 2 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · rw [h, vsz_int]
        exact le_trans hszs (by nlinarith [Nat.zero_le p])
      · rcases List.mem_cons.mp h with h | h
        · rw [h, vsz_int]
          exact le_trans hszt (le_hundredK (p := p) (x := p + 2) (by omega))
        · exact hBlkW v h
    exact cost_pick_le (A := Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (k := 5)
      (K := Kpick) (CU := CU) (B := B) (p := p) (M := 100000 * (p + 1) ^ 2) hKpickCU (by nlinarith [Nat.zero_le p])
      (by norm_num) (by simp [buCB]) hA hB2
  -- #################### step 5 : push `int 0` ####################
  have hsz0 : vsz (Val.int 0) ≤ 100000 * (p + 1) ^ 2 := by
    rw [vsz_int]
    have h : isz (0 : ℤ) = 2 := by simp [isz]
    rw [h]
    exact two_le_hundredK p
  have h5 : Pipe main (pushProg (.int 0))
      (Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int 0 :: Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (CU * B) := by
    refine Pipe.le (Pipe.pushOnAny
      (T := Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (hPush main (.int 0))) ?_
    exact cost_one_le (K := Kpush) (CU := CU) (B := B) (p := p) (M := 100000 * (p + 1) ^ 2)
      (a := vsz (Val.int 0)) hKpushCU hsz0 (by nlinarith [Nat.zero_le p]) hB2
  -- #################### step 6 : swap `int t` and `int 0` ####################
  have h6 : Pipe main swapProg
      (Val.int 0 :: Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (t : ℤ) :: Val.int 0 :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (CU * B) := by
    refine Pipe.le (Pipe.appendTail (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Pipe.swap main hSwap (Val.int 0) (Val.int (t : ℤ)))) ?_
    rw [vsz_int, vsz_int]
    have h0 : isz (0 : ℤ) = 2 := by simp [isz]
    rw [h0]
    exact cost_two_le (K := Kswap) (CU := CU) (B := B) (p := p) (M := 100000 * (p + 1) ^ 2)
      (a := (2 : ℕ)) (b := isz ((t : ℤ))) hKswapCU (two_le_hundredK p)
      (le_trans hszt (le_hundredK (p := p) (x := p + 2) (by omega)))
      (Nat.mul_le_mul_right _ (by norm_num)) hB2
  -- #################### step 7 : replicate ####################
  have h7nat : Pipe main repProg
      (Val.int (t : ℤ) :: Val.int 0 :: (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t))
      (ofList (List.replicate t (Val.int 0)) :: Val.int (s : ℤ) :: Val.int (t : ℤ)
        :: buCB p α s t)
      (Krep * ((t + 1) * (vsz (Val.int 0) + 1) + isz ((t : ℤ)) + 1)) := by
    intro rest vs hvs s0 R hR
    have hpre : vs = .int (t : ℤ) :: .int 0 ::
        (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest) := by
      rw [hvs]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    obtain ⟨out, s', n, ⟨rr, hpre1, hout⟩, hev, hn, hstk, hoth⟩ :=
      hRep main t (.int 0) vs ⟨_, hpre⟩ s0 R hR
    have hrr : rr = Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest := by
      have h1 : Val.int (t : ℤ) :: Val.int 0 :: rr =
          Val.int (t : ℤ) :: Val.int 0 ::
            (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest) :=
        hpre1.symm.trans hpre
      exact (List.cons.inj (List.cons.inj h1).2).2
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    show out = ofList (List.replicate t (Val.int 0)) ::
      (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest)
    rw [hout, hrr]
  have h7 : Pipe main repProg
      (Val.int (t : ℤ) :: Val.int 0 :: (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t))
      (ofList (List.replicate t (Val.int 0)) :: Val.int (s : ℤ) :: Val.int (t : ℤ)
        :: buCB p α s t) (CU * B) := by
    refine Pipe.le h7nat ?_
    rw [vsz_int]
    have h0 : isz (0 : ℤ) = 2 := by simp [isz]
    rw [h0]
    have hmid : (t + 1) * 3 + isz ((t : ℤ)) + 1 ≤ (t + 1) * (p + 6) := by
      have h1 : isz ((t : ℤ)) ≤ p + 2 := hszt
      nlinarith
    have hBp : (t + 1) * (p + 1) ≤ B := by
      simp only [B]
      exact Nat.mul_le_mul_left _ (by
        have h3 : (p + 1) ^ 1 ≤ (p + 1) ^ E :=
          Nat.pow_le_pow_right (by omega) (by simp only [E]; omega)
        simpa using h3)
    calc Krep * ((t + 1) * 3 + isz ((t : ℤ)) + 1)
        ≤ Krep * ((t + 1) * (p + 6)) := Nat.mul_le_mul_left _ hmid
      _ ≤ 7 * Krep * ((t + 1) * (p + 1)) := by
          have hp6 : p + 6 ≤ 7 * (p + 1) := by omega
          calc Krep * ((t + 1) * (p + 6)) ≤ Krep * ((t + 1) * (7 * (p + 1))) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp6)
            _ = 7 * Krep * ((t + 1) * (p + 1)) := by ring
      _ ≤ 7 * Krep * B := Nat.mul_le_mul_left _ hBp
      _ ≤ CU * B := Nat.mul_le_mul_right _ (by nlinarith [hKrepCU])
  -- #################### step 8 : enumerate ####################
  have h8nat : Pipe main enumProg
      (ofList (List.replicate t (Val.int 0)) :: Val.int (s : ℤ) :: Val.int (t : ℤ)
        :: buCB p α s t)
      ([ofList E1] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (Kenum * (vsz (ofList (List.replicate t (Val.int 0)))
        + (List.replicate t (Val.int 0)).length
          * (((List.replicate t (Val.int 0)).length.size) + 1) + 1)) := by
    intro rest vs hvs s0 R hR
    have hpre : vs = ofList (List.replicate t (Val.int 0)) ::
        (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest) := by
      rw [hvs]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    obtain ⟨out, s', n, ⟨rr, hpre1, hout⟩, hev, hn, hstk, hoth⟩ :=
      hEnum main (List.replicate t (Val.int 0)) vs ⟨_, hpre⟩ s0 R hR
    have hrr : rr = Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest := by
      have h1 : ofList (List.replicate t (Val.int 0)) :: rr =
          ofList (List.replicate t (Val.int 0)) ::
            (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest) :=
        hpre1.symm.trans hpre
      exact (List.cons.inj h1).2
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    have hgoal : out = ofList E1 ::
        (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t ++ rest) := by
      rw [hout, hrr]
      congr 1
      apply congrArg ofList
      rw [List.length_replicate, hE1def]
      apply List.map_congr_left
      intro i hi
      rw [List.getD_replicate _ (List.mem_range.mp hi)]
    exact hgoal
  have h8 : Pipe main enumProg
      (ofList (List.replicate t (Val.int 0)) :: Val.int (s : ℤ) :: Val.int (t : ℤ)
        :: buCB p α s t)
      ([ofList E1] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t)) (CU * B) := by
    refine Pipe.le h8nat ?_
    rw [List.length_replicate]
    have h1 : vsz (ofList (List.replicate t (Val.int 0))) ≤ 3 * t + 1 := by
      rw [vsz_ofList', List.length_replicate]
      have h2 : szl (List.replicate t (Val.int 0)) = 2 * t := by
        simp only [szl, List.map_replicate, List.sum_replicate, vsz_int]
        have h3 : isz (0 : ℤ) = 2 := by simp [isz]
        rw [h3]
        ring
      rw [h2]
      omega
    have h4 : t * (t.size + 1) ≤ t * (p + 2) := by
      have h5 : t.size ≤ p + 1 := by
        rw [Nat.size_le]
        exact lt_of_lt_of_le htp (Nat.pow_le_pow_right (by norm_num) (by omega))
      nlinarith
    have h6 : 3 * t + 1 + t * (p + 2) + 1 ≤ (t + 1) * (p + 6) := by nlinarith [hp0]
    have hBp : (t + 1) * (p + 1) ≤ B := by
      simp only [B]
      exact Nat.mul_le_mul_left _ (by
        have h3 : (p + 1) ^ 1 ≤ (p + 1) ^ E :=
          Nat.pow_le_pow_right (by omega) (by simp only [E]; omega)
        simpa using h3)
    have hmain : vsz (ofList (List.replicate t (Val.int 0))) + t * (t.size + 1) + 1
        ≤ (t + 1) * (p + 6) := by
      have := h4
      omega
    calc Kenum * (vsz (ofList (List.replicate t (Val.int 0))) + t * (t.size + 1) + 1)
        ≤ Kenum * ((t + 1) * (p + 6)) := Nat.mul_le_mul_left _ hmain
      _ ≤ 7 * Kenum * ((t + 1) * (p + 1)) := by
          have hp6 : p + 6 ≤ 7 * (p + 1) := by omega
          calc Kenum * ((t + 1) * (p + 6)) ≤ Kenum * ((t + 1) * (7 * (p + 1))) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp6)
            _ = 7 * Kenum * ((t + 1) * (p + 1)) := by ring
      _ ≤ 7 * Kenum * B := Nat.mul_le_mul_left _ hBp
      _ ≤ CU * B := Nat.mul_le_mul_right _ (by nlinarith [hKenumCU])
  -- #################### step 9 : the `σ_t` record word ####################
  have hE1len : E1.length = t := by simp [E1]
  have hE1mem : ∀ x ∈ E1, ∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0) := by
    intro x hx
    simp only [E1, List.mem_map] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨k, List.mem_range.mp hk, hkx.symm⟩
  have hE1sz : ∀ x ∈ E1, vsz x ≤ 4 * p + 24 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hE1mem x hx
    have h1 : isz ((k : ℤ)) ≤ p + 2 := isz_nat_le_of_lt (lt_of_lt_of_le hk (le_of_lt htp))
    have h0 : isz (0 : ℤ) = 2 := by simp [isz]
    rw [vsz_cons, vsz_int, vsz_int, h0]
    omega
  have h9nat : Pipe main (mapProg recProg)
      ([ofList E1] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      ([ofList (lamRecs s t)] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (E1.length * (c1 + Kmap * (4 * p + 24 + 1)) + Kmap) := by
    intro rest vs hvs s0 R hR
    have hBody := lamBody1 recProg Krec hRec main p s t hst htp
    obtain ⟨out, s', n, ⟨ys, hout, hF2⟩, hev, hn, hstk, hoth⟩ :=
      hMap main recProg (([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t) ++ rest)
        (fun x => ∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0))
        (fun x y => ∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0) ∧ y = lamRec s t k)
        c1 (4 * p + 24) (fun x hx => hBody x hx (buCB p α s t ++ rest)) E1
        (fun x hx => ⟨hE1mem x hx, hE1sz x hx⟩) vs
        (by rw [hvs]; simp only [List.cons_append, List.nil_append, List.append_assoc]) s0 R hR
    have hF2t : List.Forall₂ (fun x y => ∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0) ∧
        y = lamRec s t k) E1 (lamRecs s t) := by
      rw [hE1def, lamRecs]
      exact forall₂_map_map _ (List.range t) _ _
        (fun a ha => ⟨a, List.mem_range.mp ha, rfl, rfl⟩)
    have hRU : Relator.RightUnique (fun x y => ∃ k, k < t ∧ x = Val.cons (.int (k : ℤ)) (.int 0) ∧
        y = lamRec s t k) := by
      intro a b c h1 h2
      obtain ⟨k, hk, ha1, hb⟩ := h1
      obtain ⟨k', hk', ha2, hc⟩ := h2
      have h3 : (Val.cons (.int (k : ℤ)) (.int 0) : Val) = Val.cons (.int (k' : ℤ)) (.int 0) := by
        rw [← ha1, ← ha2]
      have h4 := Val.cons.inj h3
      have h5 : k = k' := by
        have h6 : (k : ℤ) = (k' : ℤ) := Val.int.inj h4.1
        exact_mod_cast h6
      rw [hb, hc, h5]
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    have hyseq : ys = lamRecs s t := forall₂_right_unique hRU hF2 hF2t
    rw [hout, hyseq]
    rfl
  have h9 : Pipe main (mapProg recProg)
      ([ofList E1] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      ([ofList (lamRecs s t)] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (CU * B) := by
    refine Pipe.le h9nat ?_
    rw [hE1len]
    have h1 : c1 ≤ Krec * 10 ^ Krec * (p + 1) ^ E := by
      have h5 : (4 * (p + 2) + 1) ^ Krec ≤ (10 * (p + 1)) ^ Krec :=
        Nat.pow_le_pow_left (by omega) Krec
      have h6 : (10 * (p + 1)) ^ Krec = 10 ^ Krec * (p + 1) ^ Krec := by rw [mul_pow]
      have h7 : (p + 1) ^ Krec ≤ (p + 1) ^ E := Nat.pow_le_pow_right (by omega) hKrecE
      calc c1 = Krec * (4 * (p + 2) + 1) ^ Krec := by rw [hc1def]
        _ ≤ Krec * (10 * (p + 1)) ^ Krec := Nat.mul_le_mul_left _ h5
        _ = Krec * 10 ^ Krec * (p + 1) ^ Krec := by rw [h6]; ring
        _ ≤ Krec * 10 ^ Krec * (p + 1) ^ E := Nat.mul_le_mul_left _ h7
    have h2 : Kmap * (4 * p + 24 + 1) ≤ 30 * Kmap * (p + 1) ^ E := by
      have h8 : (p + 1) ^ 1 ≤ (p + 1) ^ E :=
        Nat.pow_le_pow_right (by omega) (by simp only [E]; omega)
      have h8' : (p + 1) ≤ (p + 1) ^ E := by simpa using h8
      have h9b : 4 * p + 25 ≤ 30 * (p + 1) := by omega
      calc Kmap * (4 * p + 24 + 1) = Kmap * (4 * p + 25) := by ring
        _ ≤ Kmap * (30 * (p + 1)) := Nat.mul_le_mul_left _ h9b
        _ = 30 * (Kmap * (p + 1)) := by ring
        _ ≤ 30 * (Kmap * (p + 1) ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h8')
        _ = 30 * Kmap * (p + 1) ^ E := by ring
    have h3 : t * (c1 + Kmap * (4 * p + 24 + 1)) + Kmap ≤
        (Krec * 10 ^ Krec + 31 * Kmap) * B := by
      have hcz : c1 + Kmap * (4 * p + 24 + 1) ≤
          (Krec * 10 ^ Krec + 31 * Kmap) * (p + 1) ^ E := by
        have hs := add_le_add h1 h2
        have h30 : 30 * Kmap * (p + 1) ^ E ≤ 31 * Kmap * (p + 1) ^ E :=
          Nat.mul_le_mul_right _ (by omega)
        calc c1 + Kmap * (4 * p + 24 + 1)
            ≤ Krec * 10 ^ Krec * (p + 1) ^ E + 30 * Kmap * (p + 1) ^ E := hs
          _ ≤ Krec * 10 ^ Krec * (p + 1) ^ E + 31 * Kmap * (p + 1) ^ E :=
              Nat.add_le_add_left h30 _
          _ = (Krec * 10 ^ Krec + 31 * Kmap) * (p + 1) ^ E := by ring
      have hpEpos : 0 < (p + 1) ^ E := pow_pos (by omega) E
      have hKmap : Kmap ≤ Kmap * (p + 1) ^ E := Nat.le_mul_of_pos_right Kmap hpEpos
      have hZ : Kmap * (p + 1) ^ E ≤ (Krec * 10 ^ Krec + 31 * Kmap) * (p + 1) ^ E :=
        Nat.mul_le_mul_right _ (by omega)
      rw [show B = (t + 1) * (p + 1) ^ E from rfl]
      calc t * (c1 + Kmap * (4 * p + 24 + 1)) + Kmap
          ≤ t * ((Krec * 10 ^ Krec + 31 * Kmap) * (p + 1) ^ E) + Kmap * (p + 1) ^ E :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hcz) hKmap
        _ ≤ t * ((Krec * 10 ^ Krec + 31 * Kmap) * (p + 1) ^ E)
              + (Krec * 10 ^ Krec + 31 * Kmap) * (p + 1) ^ E := Nat.add_le_add_left hZ _
        _ = (Krec * 10 ^ Krec + 31 * Kmap) * ((t + 1) * (p + 1) ^ E) := by ring
    have h4 : (Krec * 10 ^ Krec + 31 * Kmap) * B ≤ CU * B := by
      apply Nat.mul_le_mul_right
      have hq1 : Krec * 10 ^ Krec ≤ 100000 * (Krec * 10 ^ Krec) :=
        Nat.le_mul_of_pos_left _ (by norm_num : (0 : ℕ) < 100000)
      have hkm : 31 * Kmap ≤ 1000000000 * MS :=
        le_trans (Nat.mul_le_mul_left _ hMSmap)
          (Nat.mul_le_mul_right _ (by norm_num : (31 : ℕ) ≤ 1000000000))
      calc Krec * 10 ^ Krec + 31 * Kmap
          ≤ 100000 * (Krec * 10 ^ Krec) + 1000000000 * MS := Nat.add_le_add hq1 hkm
        _ = 1000000000 * MS + 100000 * (Krec * 10 ^ Krec) := by ring
        _ ≤ CU := hCUAB
    exact le_trans h3 h4
  -- #################### step 10 : sort by `σ_t` and read the keys ####################
  have hKslen : Ks.length = t := by rw [hKsdef]; simp
  have hKsSz' : ∀ x ∈ Ks, vsz x ≤ p + 3 := by
    intro x hx
    rw [hKsdef] at hx
    simp only [List.mem_map] at hx
    obtain ⟨i, hi, hix⟩ := hx
    subst hix
    rw [vsz_int]
    have h1 : egLam s t i ≤ s + i := egLam_le_self s t i
    have h2 : s + i < s + t := Nat.add_lt_add_left (List.mem_range.mp hi) s
    have h3 : s + t < 2 ^ (p + 1) := by omega
    have h4 : egLam s t i < 2 ^ (p + 1) := lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (le_of_lt h3))
    have h6 : isz ((egLam s t i : ℤ)) ≤ (p + 1) + 2 := isz_nat_le_of_lt h4
    omega
  have hKsVsz : vsz (ofList Ks) ≤ t * (p + 4) + 1 := by
    rw [vsz_ofList', hKslen]
    have h1 : szl Ks ≤ t * (p + 3) :=
      le_trans (szl_le_len_mul hKsSz') (le_of_eq (by rw [hKslen]))
    have h2 : t + 1 + t * (p + 3) ≤ t * (p + 4) + 1 := by nlinarith
    omega
  have h10nat : Pipe main (.seq sortProg (mapProg elemProg))
      ([ofList (lamRecs s t)] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      ([ofList Ks] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (Ksort * (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1) +
        (t * (c2 + Kmap * (4 * p + 24 + 1)) + Kmap)) := by
    intro rest vs hvs s0 R hR
    have hpre : vs = ofList (lamRecs s t) ::
        (([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t) ++ rest) := by
      rw [hvs]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    obtain ⟨out1, s1, n1, ⟨rr, ys, hpre1, hout1, hperm, hsortp⟩, hev1, hn1, hstk1, hoth1⟩ :=
      hSort main (lamRecs s t) hrecW hnodupW vs ⟨_, hpre⟩ s0 R hR
    have hrr : rr = ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t) ++ rest := by
      have h1 : ofList (lamRecs s t) :: rr =
          ofList (lamRecs s t) :: (([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t) ++ rest) :=
        hpre1.symm.trans hpre
      exact (List.cons.inj h1).2
    have hyslen : ys.length = t := by rw [hperm.length_eq, lamRecs_length]
    have hysK : ∀ i < t, ys.getD i .nil =
        Val.cons (.int (i : ℤ)) (.int ((lamMu s t i : ℕ) : ℤ)) :=
      lamSorted_entry s t hs hst hcop ys hperm hsortp
    have hBody2 := lamBody2 elemProg Kelem hElem main p s t hst htp hcop hs
    have hyspre : ∀ x ∈ ys, (∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
        x = Val.cons (.int (i : ℤ)) (.int (m : ℤ))) ∧ vsz x ≤ 4 * p + 24 := by
      intro x hx
      have hx' : x ∈ lamRecs s t := (hperm.mem_iff).mp hx
      obtain ⟨k, hk, hkx⟩ := lamRecs_mem hx'
      refine ⟨?_, hrecSzs x hx'⟩
      exact ⟨egSigT s t k, k, egSigT_lt s t k ht0, hk, rfl, by rw [hkx, lamRec]⟩
    obtain ⟨out2, s2, n2, ⟨ys', hout2, hF2⟩, hev2, hn2, hstk2, hoth2⟩ :=
      hMap main elemProg rr
        (fun x => ∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
          x = Val.cons (.int (i : ℤ)) (.int (m : ℤ)))
        (fun x y => ∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
          x = Val.cons (.int (i : ℤ)) (.int (m : ℤ)) ∧
          y = Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ)))
        c2 (4 * p + 24) (fun x hx => by
          rw [hrr]; exact hBody2 x hx (buCB p α s t ++ rest)) ys hyspre out1
        (by rw [hout1]) s1 R hstk1
    have hKs0eq : Ks = (List.range t).map (fun i : ℕ =>
        Val.int (lamKey (s : ℤ) (t : ℤ) ((lamMu s t i : ℕ) : ℤ) (i : ℤ))) := by
      rw [hKsdef]
      apply List.map_congr_left
      intro i hi
      have hi' : i < t := List.mem_range.mp hi
      rw [lamKey_eq_egLam s t (lamMu s t i) i hs hst hcop (lamMu_lt s t hcop ht0 i hi') hi'
        (lamMu_spec s t hcop ht0 i hi')]
    have hF2t2 : List.Forall₂ (fun x y => ∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
        x = Val.cons (.int (i : ℤ)) (.int (m : ℤ)) ∧
        y = Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ))) ys
        ((List.range t).map (fun i : ℕ =>
          Val.int (lamKey (s : ℤ) (t : ℤ) ((lamMu s t i : ℕ) : ℤ) (i : ℤ)))) := by
      apply forall₂_of_get
      · rw [hyslen]; simp
      · intro i h1 h2
        have hi' : i < t := by rw [← hyslen]; exact h1
        have hget1 : ys[i] = Val.cons (.int (i : ℤ)) (.int ((lamMu s t i : ℕ) : ℤ)) := by
          rw [← List.getD_eq_getElem ys .nil h1]
          exact hysK i hi'
        have hget2 : ((List.range t).map (fun i : ℕ => Val.int (lamKey (s : ℤ) (t : ℤ)
            ((lamMu s t i : ℕ) : ℤ) (i : ℤ))))[i] =
            Val.int (lamKey (s : ℤ) (t : ℤ) ((lamMu s t i : ℕ) : ℤ) (i : ℤ)) := by
          rw [List.getElem_map, List.getElem_range]
        rw [hget1, hget2]
        exact ⟨i, lamMu s t i, hi', lamMu_lt s t hcop ht0 i hi',
          lamMu_spec s t hcop ht0 i hi', rfl, rfl⟩
    have hRU2 : Relator.RightUnique (fun x y => ∃ i m, i < t ∧ m < t ∧ egSigT s t m = i ∧
        x = Val.cons (.int (i : ℤ)) (.int (m : ℤ)) ∧
        y = Val.int (lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ))) := by
      intro a b c h1 h2
      obtain ⟨i, m, hi, hm, hσ, ha1, hb⟩ := h1
      obtain ⟨i', m', hi', hm', hσ', ha2, hc⟩ := h2
      have h3 : (Val.cons (.int (i : ℤ)) (.int (m : ℤ)) : Val) =
          Val.cons (.int (i' : ℤ)) (.int (m' : ℤ)) := by rw [← ha1, ← ha2]
      have h4 := Val.cons.inj h3
      have h5 : i = i' := by
        have h6 : (i : ℤ) = (i' : ℤ) := Val.int.inj h4.1
        exact_mod_cast h6
      have h7 : m = m' := by
        have h6 : (m : ℤ) = (m' : ℤ) := Val.int.inj h4.2
        exact_mod_cast h6
      rw [hb, hc, h5, h7]
    have hys' : ys' = (List.range t).map (fun i : ℕ =>
        Val.int (lamKey (s : ℤ) (t : ℤ) ((lamMu s t i : ℕ) : ℤ) (i : ℤ))) :=
      forall₂_right_unique hRU2 hF2 hF2t2
    refine ⟨out2, s2, n1 + n2, ?_, Eval.seq hev1 hev2, ?_, hstk2,
      fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩
    · rw [hout2, hrr, hys', hKs0eq]
      rfl
    · refine Nat.add_le_add hn1 ?_
      rw [← hyslen]
      exact hn2
  have h10 : Pipe main (.seq sortProg (mapProg elemProg))
      ([ofList (lamRecs s t)] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      ([ofList Ks] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t)) (CU * B) := by
    refine Pipe.le h10nat ?_
    have hs1 : Ksort * (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1)
        ≤ 60 * Ksort * B := by
      have hv : vsz (ofList (lamRecs s t)) ≤ t * (4 * p + 25) + 1 := by
        rw [vsz_ofList', lamRecs_length]
        have h1 : szl (lamRecs s t) ≤ t * (4 * p + 24) :=
          le_trans (szl_le_len_mul hrecSzs) (le_of_eq (by rw [lamRecs_length]))
        have h2 : t * (4 * p + 24) + (t + 1) ≤ t * (4 * p + 25) + 1 := by nlinarith
        omega
      have ht : (lamRecs s t).length.size ≤ p + 1 := by
        rw [lamRecs_length, Nat.size_le]
        exact lt_of_lt_of_le htp (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hmid : (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1)
          ≤ 60 * (t + 1) * (p + 1) ^ E := by
        have h1 : vsz (ofList (lamRecs s t)) + 1 ≤ 30 * (t + 1) * (p + 1) := by
          have h2 : vsz (ofList (lamRecs s t)) + 1 ≤ (t + 1) * (4 * p + 27) := by
            have h5 : (t + 1) * (4 * p + 27) = t * (4 * p + 27) + (4 * p + 27) := by ring
            have h6 : t * (4 * p + 25) + 2 ≤ t * (4 * p + 27) + (4 * p + 27) := by nlinarith
            rw [h5]
            omega
          have h3 : 4 * p + 27 ≤ 30 * (p + 1) := by omega
          calc vsz (ofList (lamRecs s t)) + 1 ≤ (t + 1) * (4 * p + 27) := h2
            _ ≤ (t + 1) * (30 * (p + 1)) := Nat.mul_le_mul_left _ h3
            _ = 30 * (t + 1) * (p + 1) := by ring
        have h2 : (lamRecs s t).length.size + 1 ≤ 2 * (p + 1) := by omega
        have h3 : 30 * (t + 1) * (p + 1) * (2 * (p + 1)) ≤ 60 * (t + 1) * (p + 1) ^ E := by
          have h4 : (p + 1) ^ 2 ≤ (p + 1) ^ E :=
            Nat.pow_le_pow_right (by omega) (by simp only [E]; omega)
          have h5 : (p + 1) * (p + 1) = (p + 1) ^ 2 := by ring
          calc 30 * (t + 1) * (p + 1) * (2 * (p + 1))
              = 60 * (t + 1) * ((p + 1) * (p + 1)) := by ring
            _ = 60 * (t + 1) * (p + 1) ^ 2 := by rw [h5]
            _ ≤ 60 * (t + 1) * (p + 1) ^ E := Nat.mul_le_mul_left _ h4
        calc (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1)
            ≤ (30 * (t + 1) * (p + 1)) * (2 * (p + 1)) := Nat.mul_le_mul h1 h2
          _ ≤ 60 * (t + 1) * (p + 1) ^ E := h3
      calc Ksort * (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1)
          = Ksort * ((vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1)) := by ring
        _ ≤ Ksort * (60 * (t + 1) * (p + 1) ^ E) := Nat.mul_le_mul_left _ hmid
        _ = 60 * Ksort * B := by
            rw [show B = (t + 1) * (p + 1) ^ E from rfl]; ring
    have hs2 : t * (c2 + Kmap * (4 * p + 24 + 1)) + Kmap
        ≤ (Kelem * 10 ^ Kelem + 31 * Kmap) * B := by
      have h1 : c2 ≤ Kelem * 10 ^ Kelem * (p + 1) ^ E := by
        have h5 : (4 * (p + 2) + 1) ^ Kelem ≤ (10 * (p + 1)) ^ Kelem :=
          Nat.pow_le_pow_left (by omega) Kelem
        have h6 : (10 * (p + 1)) ^ Kelem = 10 ^ Kelem * (p + 1) ^ Kelem := by rw [mul_pow]
        have h7 : (p + 1) ^ Kelem ≤ (p + 1) ^ E := Nat.pow_le_pow_right (by omega) hKelemE
        calc c2 = Kelem * (4 * (p + 2) + 1) ^ Kelem := by rw [hc2def]
          _ ≤ Kelem * (10 * (p + 1)) ^ Kelem := Nat.mul_le_mul_left _ h5
          _ = Kelem * 10 ^ Kelem * (p + 1) ^ Kelem := by rw [h6]; ring
          _ ≤ Kelem * 10 ^ Kelem * (p + 1) ^ E := Nat.mul_le_mul_left _ h7
      have h2 : Kmap * (4 * p + 24 + 1) ≤ 30 * Kmap * (p + 1) ^ E := by
        have h8 : (p + 1) ^ 1 ≤ (p + 1) ^ E :=
          Nat.pow_le_pow_right (by omega) (by simp only [E]; omega)
        have h8' : (p + 1) ≤ (p + 1) ^ E := by simpa using h8
        have h9b : 4 * p + 25 ≤ 30 * (p + 1) := by omega
        calc Kmap * (4 * p + 24 + 1) = Kmap * (4 * p + 25) := by ring
          _ ≤ Kmap * (30 * (p + 1)) := Nat.mul_le_mul_left _ h9b
          _ = 30 * (Kmap * (p + 1)) := by ring
          _ ≤ 30 * (Kmap * (p + 1) ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h8')
          _ = 30 * Kmap * (p + 1) ^ E := by ring
      have hcz : c2 + Kmap * (4 * p + 24 + 1) ≤
          (Kelem * 10 ^ Kelem + 31 * Kmap) * (p + 1) ^ E := by
        have hs := add_le_add h1 h2
        have h30 : 30 * Kmap * (p + 1) ^ E ≤ 31 * Kmap * (p + 1) ^ E :=
          Nat.mul_le_mul_right _ (by omega)
        calc c2 + Kmap * (4 * p + 24 + 1)
            ≤ Kelem * 10 ^ Kelem * (p + 1) ^ E + 30 * Kmap * (p + 1) ^ E := hs
          _ ≤ Kelem * 10 ^ Kelem * (p + 1) ^ E + 31 * Kmap * (p + 1) ^ E :=
              Nat.add_le_add_left h30 _
          _ = (Kelem * 10 ^ Kelem + 31 * Kmap) * (p + 1) ^ E := by ring
      have hpEpos : 0 < (p + 1) ^ E := pow_pos (by omega) E
      have hKmap : Kmap ≤ Kmap * (p + 1) ^ E := Nat.le_mul_of_pos_right Kmap hpEpos
      have hZ : Kmap * (p + 1) ^ E ≤ (Kelem * 10 ^ Kelem + 31 * Kmap) * (p + 1) ^ E :=
        Nat.mul_le_mul_right _ (by omega)
      rw [show B = (t + 1) * (p + 1) ^ E from rfl]
      calc t * (c2 + Kmap * (4 * p + 24 + 1)) + Kmap
          ≤ t * ((Kelem * 10 ^ Kelem + 31 * Kmap) * (p + 1) ^ E) + Kmap * (p + 1) ^ E :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hcz) hKmap
        _ ≤ t * ((Kelem * 10 ^ Kelem + 31 * Kmap) * (p + 1) ^ E)
              + (Kelem * 10 ^ Kelem + 31 * Kmap) * (p + 1) ^ E := Nat.add_le_add_left hZ _
        _ = (Kelem * 10 ^ Kelem + 31 * Kmap) * ((t + 1) * (p + 1) ^ E) := by ring
    have hsum : Ksort * (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1) +
        (t * (c2 + Kmap * (4 * p + 24 + 1)) + Kmap)
        ≤ (60 * Ksort + Kelem * 10 ^ Kelem + 31 * Kmap) * B := by
      have hAB : 60 * Ksort + (Kelem * 10 ^ Kelem + 31 * Kmap) =
          60 * Ksort + Kelem * 10 ^ Kelem + 31 * Kmap := by ring
      calc Ksort * (vsz (ofList (lamRecs s t)) + 1) * ((lamRecs s t).length.size + 1) +
          (t * (c2 + Kmap * (4 * p + 24 + 1)) + Kmap)
          ≤ 60 * Ksort * B + (Kelem * 10 ^ Kelem + 31 * Kmap) * B := add_le_add hs1 hs2
        _ = (60 * Ksort + Kelem * 10 ^ Kelem + 31 * Kmap) * B := by ring
    have hfinal10 : (60 * Ksort + Kelem * 10 ^ Kelem + 31 * Kmap) * B ≤ CU * B := by
      apply Nat.mul_le_mul_right
      have hq1 : Kelem * 10 ^ Kelem ≤ 100000 * (Kelem * 10 ^ Kelem) :=
        Nat.le_mul_of_pos_left _ (by norm_num : (0 : ℕ) < 100000)
      have hsum : 60 * Ksort + 31 * Kmap ≤ 1000000000 * MS := by
        have hks : 60 * Ksort ≤ 60 * MS := Nat.mul_le_mul_left _ hMSsort
        have hkm : 31 * Kmap ≤ 31 * MS := Nat.mul_le_mul_left _ hMSmap
        have h91 : 60 * MS + 31 * MS = 91 * MS := by ring
        have hle : 91 * MS ≤ 1000000000 * MS := Nat.mul_le_mul_right _ (by norm_num)
        omega
      calc 60 * Ksort + Kelem * 10 ^ Kelem + 31 * Kmap
          ≤ 1000000000 * MS + 100000 * (Kelem * 10 ^ Kelem) := by omega
        _ ≤ CU := hCUAB2
    exact le_trans hsum hfinal10
  -- #################### step 11 : roll the `t` copy to the top and delete it ####################
  have hBp : (t + 1) * (p + 1) ≤ B := by
    rw [show B = (t + 1) * (p + 1) ^ E from rfl]
    exact Nat.mul_le_mul_left _ (by
      have h3 : (p + 1) ^ 1 ≤ (p + 1) ^ E :=
        Nat.pow_le_pow_right (by omega) (by simp only [E]; omega)
      simpa using h3)
  have hB1 : 1 ≤ B := by
    have h3 : 1 ≤ (t + 1) * (p + 1) := Nat.mul_pos (by omega) (by omega)
    exact le_trans h3 hBp
  have hszKsv : vsz (ofList Ks) ≤ t * (p + 4) + 1 := hKsVsz
  have h11 : Pipe main (rollProg 2)
      (ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (Val.int (t : ℤ) :: ofList Ks :: Val.int (s : ℤ) :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.roll main hRoll
      (A := ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (k := 2)
      (by simp)) ?_
    have hsz : szl ((ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t).take 3)
        ≤ vsz (ofList Ks) + isz ((s : ℤ)) + isz ((t : ℤ)) := by
      have hdone : (ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t).take 3
          = [ofList Ks, Val.int (s : ℤ), Val.int (t : ℤ)] := rfl
      rw [hdone]
      simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have h1 : szl ((ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t).take 3) + 1
        ≤ 9 * ((t + 1) * (p + 1)) := by
      have h2 : isz ((s : ℤ)) ≤ p + 2 := hszs
      have h3 : isz ((t : ℤ)) ≤ p + 2 := hszt
      have h5 : t * (p + 4) + 1 + (p + 2) + (p + 2) + 1 ≤ 9 * ((t + 1) * (p + 1)) := by
        have e1 : 9 * ((t + 1) * (p + 1)) = 9 * (t * p) + 9 * t + 9 * p + 9 := by ring
        have e2 : t * (p + 4) = t * p + 4 * t := by ring
        rw [e1, e2]; omega
      have h6 : szl ((ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t).take 3) + 1
          ≤ t * (p + 4) + 1 + (p + 2) + (p + 2) + 1 := by
        have h4 := hszKsv
        omega
      exact le_trans h6 h5
    have h6 : Kroll * (2 + 1) * (szl ((ofList Ks :: Val.int (s : ℤ) :: Val.int (t : ℤ)
        :: buCB p α s t).take 3) + 1) ≤ Kroll * 3 * (9 * ((t + 1) * (p + 1))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) h1
    have h7 : Kroll * 3 * (9 * ((t + 1) * (p + 1))) ≤ 27 * Kroll * B := by
      have heq : Kroll * 3 * (9 * ((t + 1) * (p + 1))) = 27 * Kroll * ((t + 1) * (p + 1)) := by
        ring
      rw [heq]
      exact Nat.mul_le_mul_left (27 * Kroll) hBp
    have h5 : 27 * Kroll ≤ CU := by
      have h6 : 27 * Kroll ≤ 27 * MS := Nat.mul_le_mul_left _ hMSroll
      have h7 : 27 * MS ≤ 1000000000 * MS := Nat.mul_le_mul_right _ (by norm_num)
      exact le_trans h6 (le_trans h7 hCUMS)
    exact le_trans h6 (le_trans h7 (Nat.mul_le_mul_right _ h5))
  -- #################### step 12 : drop the `t` copy ####################
  have h12 : Pipe main dropProg
      (Val.int (t : ℤ) :: ofList Ks :: Val.int (s : ℤ) :: buCB p α s t)
      (ofList Ks :: Val.int (s : ℤ) :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.appendTail (ofList Ks :: Val.int (s : ℤ) :: buCB p α s t)
      (Pipe.drop main hDrop (Val.int (t : ℤ)))) ?_
    rw [vsz_int]
    have h3 : isz ((t : ℤ)) + 1 ≤ 3 * (p + 1) := by
      have h1 : isz ((t : ℤ)) ≤ p + 2 := hszt
      omega
    have hstep : Kdrop * (isz ((t : ℤ)) + 1) ≤ Kdrop * (3 * (p + 1)) :=
      Nat.mul_le_mul_left _ h3
    have hstep2 : Kdrop * (3 * (p + 1)) ≤ 10 * Kdrop * B := by
      have h7 : (3 : ℕ) * (p + 1) ≤ 10 * B := by nlinarith [hB1, Nat.zero_le p]
      have h8 := Nat.mul_le_mul_left Kdrop h7
      calc Kdrop * (3 * (p + 1)) ≤ Kdrop * (10 * B) := h8
        _ = 10 * Kdrop * B := by ring
    have h5 : 10 * Kdrop ≤ CU := by
      have h6 : 10 * Kdrop ≤ 10 * MS := Nat.mul_le_mul_left _ hMSdrop
      have h7 : 10 * MS ≤ 1000000000 * MS := Nat.mul_le_mul_right _ (by norm_num)
      exact le_trans h6 (le_trans h7 hCUMS)
    exact le_trans hstep (le_trans hstep2 (Nat.mul_le_mul_right _ h5))
  -- #################### step 13 : roll the `s` copy to the top ####################
  have h13 : Pipe main (rollProg 1)
      (ofList Ks :: Val.int (s : ℤ) :: buCB p α s t)
      (Val.int (s : ℤ) :: ofList Ks :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.roll main hRoll
      (A := ofList Ks :: Val.int (s : ℤ) :: buCB p α s t) (k := 1) (by simp)) ?_
    have hsz : szl ((ofList Ks :: Val.int (s : ℤ) :: buCB p α s t).take 2)
        ≤ vsz (ofList Ks) + isz ((s : ℤ)) := by
      have hdone : (ofList Ks :: Val.int (s : ℤ) :: buCB p α s t).take 2
          = [ofList Ks, Val.int (s : ℤ)] := rfl
      rw [hdone]
      simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have h1 : szl ((ofList Ks :: Val.int (s : ℤ) :: buCB p α s t).take 2) + 1
        ≤ 9 * ((t + 1) * (p + 1)) := by
      have h2 : isz ((s : ℤ)) ≤ p + 2 := hszs
      have h5 : t * (p + 4) + 1 + (p + 2) + 1 ≤ 9 * ((t + 1) * (p + 1)) := by
        have e1 : 9 * ((t + 1) * (p + 1)) = 9 * (t * p) + 9 * t + 9 * p + 9 := by ring
        have e2 : t * (p + 4) = t * p + 4 * t := by ring
        rw [e1, e2]; omega
      have h6 : szl ((ofList Ks :: Val.int (s : ℤ) :: buCB p α s t).take 2) + 1
          ≤ t * (p + 4) + 1 + (p + 2) + 1 := by
        have h4 := hszKsv
        omega
      exact le_trans h6 h5
    have h6 : Kroll * (1 + 1) * (szl ((ofList Ks :: Val.int (s : ℤ) :: buCB p α s t).take 2) + 1)
        ≤ Kroll * 2 * (9 * ((t + 1) * (p + 1))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by norm_num)) h1
    have h7 : Kroll * 2 * (9 * ((t + 1) * (p + 1))) ≤ 27 * Kroll * B := by
      have heq : Kroll * 2 * (9 * ((t + 1) * (p + 1))) = 18 * Kroll * ((t + 1) * (p + 1)) := by
        ring
      rw [heq]
      have h18 : 18 * Kroll * ((t + 1) * (p + 1)) ≤ 27 * Kroll * ((t + 1) * (p + 1)) :=
        Nat.mul_le_mul_right ((t + 1) * (p + 1))
          (Nat.mul_le_mul_right Kroll (by norm_num : (18 : ℕ) ≤ 27))
      exact le_trans h18 (Nat.mul_le_mul_left (27 * Kroll) hBp)
    have h5 : 27 * Kroll ≤ CU := by
      have h6 : 27 * Kroll ≤ 27 * MS := Nat.mul_le_mul_left _ hMSroll
      have h7 : 27 * MS ≤ 1000000000 * MS := Nat.mul_le_mul_right _ (by norm_num)
      exact le_trans h6 (le_trans h7 hCUMS)
    exact le_trans h6 (le_trans h7 (Nat.mul_le_mul_right _ h5))
  -- #################### step 14 : drop the `s` copy ####################
  have h14 : Pipe main dropProg
      (Val.int (s : ℤ) :: ofList Ks :: buCB p α s t)
      (ofList Ks :: buCB p α s t) (CU * B) := by
    refine Pipe.le (Pipe.appendTail (ofList Ks :: buCB p α s t)
      (Pipe.drop main hDrop (Val.int (s : ℤ)))) ?_
    rw [vsz_int]
    have h3 : isz ((s : ℤ)) + 1 ≤ 3 * (p + 1) := by
      have h1 : isz ((s : ℤ)) ≤ p + 2 := hszs
      omega
    have hstep : Kdrop * (isz ((s : ℤ)) + 1) ≤ Kdrop * (3 * (p + 1)) :=
      Nat.mul_le_mul_left _ h3
    have hstep2 : Kdrop * (3 * (p + 1)) ≤ 10 * Kdrop * B := by
      have h7 : (3 : ℕ) * (p + 1) ≤ 10 * B := by nlinarith [hB1, Nat.zero_le p]
      have h8 := Nat.mul_le_mul_left Kdrop h7
      calc Kdrop * (3 * (p + 1)) ≤ Kdrop * (10 * B) := h8
        _ = 10 * Kdrop * B := by ring
    have h5 : 10 * Kdrop ≤ CU := by
      have h6 : 10 * Kdrop ≤ 10 * MS := Nat.mul_le_mul_left _ hMSdrop
      have h7 : 10 * MS ≤ 1000000000 * MS := Nat.mul_le_mul_right _ (by norm_num)
      exact le_trans h6 (le_trans h7 hCUMS)
    exact le_trans hstep (le_trans hstep2 (Nat.mul_le_mul_right _ h5))
  -- #################### the chain and the final cost ####################
  have hc1 : Pipe main (.seq (pickProg 2) (pickProg 4)) (buCB p α s t)
      (Val.int (t : ℤ) :: Val.int (s : ℤ) :: buCB p α s t) (2 * (CU * B)) :=
    Pipe.le (Pipe.comp h1 h2) (by omega)
  have hc2 : Pipe main (.seq (.seq (pickProg 2) (pickProg 4)) swapProg) (buCB p α s t)
      (Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t) (3 * (CU * B)) :=
    Pipe.le (Pipe.comp hc1 h3) (by omega)
  have hc3 : Pipe main (.seq (.seq (.seq (pickProg 2) (pickProg 4)) swapProg) (pickProg 5))
      (buCB p α s t) (Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (4 * (CU * B)) := Pipe.le (Pipe.comp hc2 h4) (by omega)
  have hc4 : Pipe main (.seq (.seq (.seq (.seq (pickProg 2) (pickProg 4)) swapProg) (pickProg 5))
      (pushProg (.int 0))) (buCB p α s t)
      (Val.int 0 :: Val.int (t : ℤ) :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (5 * (CU * B)) := Pipe.le (Pipe.comp hc3 h5) (by omega)
  have hc5 : Pipe main (.seq (.seq (.seq (.seq (.seq (pickProg 2) (pickProg 4)) swapProg)
      (pickProg 5)) (pushProg (.int 0))) swapProg) (buCB p α s t)
      (Val.int (t : ℤ) :: Val.int 0 :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: buCB p α s t)
      (6 * (CU * B)) := Pipe.le (Pipe.comp hc4 h6) (by omega)
  have hc6 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 2) (pickProg 4)) swapProg)
      (pickProg 5)) (pushProg (.int 0))) swapProg) repProg) (buCB p α s t)
      (ofList (List.replicate t (Val.int 0)) :: Val.int (s : ℤ) :: Val.int (t : ℤ)
        :: buCB p α s t) (7 * (CU * B)) := Pipe.le (Pipe.comp hc5 h7) (by omega)
  have hc7 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 2) (pickProg 4))
      swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg) repProg) enumProg)
      (buCB p α s t) ([ofList E1] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (8 * (CU * B)) := Pipe.le (Pipe.comp hc6 h8) (by omega)
  have hc8 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 2)
      (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg) repProg) enumProg)
      (mapProg recProg)) (buCB p α s t)
      ([ofList (lamRecs s t)] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (9 * (CU * B)) := Pipe.le (Pipe.comp hc7 h9) (by omega)
  have hc9 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 2)
      (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg) repProg) enumProg)
      (mapProg recProg)) (.seq sortProg (mapProg elemProg))) (buCB p α s t)
      ([ofList Ks] ++ ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ buCB p α s t))
      (10 * (CU * B)) := Pipe.le (Pipe.comp hc8 h10) (by omega)
  have hc10 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 2)
      (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg) repProg) enumProg)
      (mapProg recProg)) (.seq sortProg (mapProg elemProg))) (rollProg 2)) (buCB p α s t)
      (Val.int (t : ℤ) :: ofList Ks :: Val.int (s : ℤ) :: buCB p α s t)
      (11 * (CU * B)) := Pipe.le (Pipe.comp hc9 h11) (by omega)
  have hc11 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
      (pickProg 2) (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg)
      repProg) enumProg) (mapProg recProg)) (.seq sortProg (mapProg elemProg))) (rollProg 2))
      dropProg) (buCB p α s t) (ofList Ks :: Val.int (s : ℤ) :: buCB p α s t)
      (12 * (CU * B)) := Pipe.le (Pipe.comp hc10 h12) (by omega)
  have hc12 : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
      (pickProg 2) (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg)
      repProg) enumProg) (mapProg recProg)) (.seq sortProg (mapProg elemProg))) (rollProg 2))
      dropProg) (rollProg 1)) (buCB p α s t)
      (Val.int (s : ℤ) :: ofList Ks :: buCB p α s t) (13 * (CU * B)) :=
    Pipe.le (Pipe.comp hc11 h13) (by omega)
  have hchain : Pipe main (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
      (.seq (pickProg 2) (pickProg 4)) swapProg) (pickProg 5)) (pushProg (.int 0))) swapProg)
      repProg) enumProg) (mapProg recProg)) (.seq sortProg (mapProg elemProg))) (rollProg 2))
      dropProg) (rollProg 1)) dropProg) (buCB p α s t)
      (ofList Ks :: buCB p α s t) (14 * (CU * B)) := Pipe.le (Pipe.comp hc12 h14) (by omega)
  have hKs7 : ofList Ks = buL7 p α s t := by
    unfold buL7 zl
    rw [List.map_ofFn]
    congr 1
    exact range_map_eq_ofFn t (fun i : ℕ => Val.int (((egLam s t i : ℕ) : ℤ)))
  have hCUKK : 20 * CU ≤ KK :=
    le_trans (Nat.le_add_right (20 * CU) 20) (le_max_right E (20 * CU + 20))
  have hpowKK : (p + 1) ^ E ≤ (p + 1) ^ KK := by
    apply Nat.pow_le_pow_right (by omega)
    exact le_max_left E (20 * CU + 20)
  refine Pipe.le (Pipe.rw hchain (by rw [hKs7])) ?_
  rw [show B = (t + 1) * (p + 1) ^ E from rfl]
  calc 14 * (CU * ((t + 1) * (p + 1) ^ E))
      = 14 * CU * ((t + 1) * (p + 1) ^ E) := by ring
    _ ≤ 20 * CU * ((t + 1) * (p + 1) ^ E) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right CU (by norm_num : (14 : ℕ) ≤ 20))
    _ ≤ KK * ((t + 1) * (p + 1) ^ E) := Nat.mul_le_mul_right _ hCUKK
    _ = (KK * (t + 1)) * (p + 1) ^ E := by ring
    _ ≤ (KK * (t + 1)) * (p + 1) ^ KK := Nat.mul_le_mul_left _ hpowKK

end Work.Resample
