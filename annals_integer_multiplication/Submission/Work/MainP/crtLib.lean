import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtMath

/-!
# `crtLib`: the shared toolkit of the CRT reindexing word

Sizes of value lists, the composition rules for `WordR`, exact-state wrappers for the library words,
a bundle `CrtLib` of the library words used by the reindexing (with their constants), and the
size/cost budget `BUD` that every phase of the word is bounded by.

`PB = vsz (ofList xs) + S * (vsz (intList ss) + 1) + 1`, `QB = S.size + 1`, `SB = PB * QB` is the
target size of the `CrtWordProp` cost, and `BUD L ss S xs = 100 * (KF L * SB ss S xs)` where
`KF L = 1000 * (KS L + 1)` dominates every library constant.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Sizes -/

private theorem sum_vsz_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    (l.map vsz).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have hx : vsz x ≤ B := h x (by simp)
      have hl : (l.map vsz).sum ≤ l.length * B := ih (fun y hy => h y (by simp [hy]))
      calc vsz x + (l.map vsz).sum ≤ B + l.length * B := Nat.add_le_add hx hl
        _ = (l.length + 1) * B := by ring

/-- `length ≤ vsz (ofList _)`. -/
theorem length_le_vsz_ofList (xs : List Val) : xs.length ≤ vsz (ofList xs) := by
  rw [vsz_ofList]; omega

theorem labVals_sz_le {lab : List ℕ} {S : ℕ} (hlen : lab.length = S)
    (hlt : ∀ i < S, lab.getD i 0 < S) :
    ((labVals lab).map vsz).sum ≤ lab.length * (S.size + 2) := by
  have hl : (labVals lab).length = lab.length := by simp [labVals]
  rw [← hl]
  apply sum_vsz_le
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  rw [← hix]
  have hiS : i < S := by rw [hl, hlen] at hi; exact hi
  have hib : i < lab.length := by rw [hlen]; exact hiS
  have h2 : (labVals lab)[i] = Val.int (↑(lab[i])) := by
    simp only [labVals, List.getElem_map]
  rw [h2, ← List.getD_eq_getElem _ _ hib]
  have h1 : lab.getD i 0 ≤ S := le_of_lt (hlt i hiS)
  rw [vsz_intNat, iszN]
  exact Nat.add_le_add_right (Nat.size_le_size h1) 2

theorem vsz_labVals_le {lab : List ℕ} {S : ℕ} (hlt : ∀ i < S, lab.getD i 0 < S)
    (hlen : lab.length = S) :
    vsz (ofList (labVals lab)) ≤ S * (S.size + 2) + S + 1 := by
  rw [vsz_ofList]
  have hl : (labVals lab).length = S := by simp [labVals, hlen]
  rw [hl]
  have h2 := labVals_sz_le hlen hlt
  rw [hlen] at h2
  omega

theorem sum_zipRec_le (xs : List Val) : ∀ (ws : List Val), xs.length = ws.length →
    ((zipRec xs ws).map vsz).sum ≤ (xs.map vsz).sum + (ws.map vsz).sum + xs.length := by
  induction xs with
  | nil => intro ws h; simp [zipRec]
  | cons x xs ih =>
      intro ws h
      cases ws with
      | nil => simp at h
      | cons w ws =>
          have h' : xs.length = ws.length := by simpa using h
          have ih' := ih ws h'
          simp only [zipRec, List.zipWith_cons_cons, List.map_cons, List.sum_cons, vsz_cons,
            List.length_cons] at ih' ⊢
          omega

theorem vsz_zipRec_le {xs ws : List Val} {S : ℕ} (hlen : xs.length = S) (hlenw : ws.length = S) :
    vsz (ofList (zipRec xs ws)) ≤ vsz (ofList xs) + vsz (ofList ws) + S := by
  rw [vsz_ofList, vsz_ofList, vsz_ofList]
  have h1 : (zipRec xs ws).length = S := by rw [zipRec_length (by omega), hlen]
  rw [h1]
  have h2 := sum_zipRec_le xs ws (by omega)
  omega

/-! ## Composition helpers -/

theorem WordR.conseqK {main : Cmd} {p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (word : WordR main p P Q C) (hK : KernelLib)
    (h1 : ∀ vs, P' vs → P vs) (h2 : ∀ vs out, P' vs → Q vs out → Q' vs out)
    (h3 : ∀ vs, P' vs → C vs ≤ C' vs) : WordR main p P' Q' C' :=
  hK.conseq main p P P' Q Q' C C' word h1 h2 h3

theorem WordR.seqK {main p q : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {P' : List Val → Prop} {Q' : List Val → List Val → Prop}
    {C' B : List Val → ℕ} (word1 : WordR main p P Q C) (word2 : WordR main q P' Q' C')
    (hK : KernelLib)
    (h : ∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ B vs) :
    WordR main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out)
      (fun vs => C vs + B vs) :=
  hK.seq main p q P Q C P' Q' C' B word1 word2 h

/-! ## Exact-state wrappers -/

theorem exSwap (hK : KernelLib) (main : Cmd) (a b : Val) (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = a :: b :: rest)
      (fun _ out => out = b :: a :: rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hK.swap
  exact ⟨p, K * (vsz a + vsz b + 1),
    WordR.conseqK (h main) hK (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hq => by
        rw [hvs] at hq
        obtain ⟨a', b', r', hab, hout⟩ := hq
        cases hab
        exact hout)
      (fun vs hvs => by rw [hvs]; simp)⟩

theorem exDup (hK : KernelLib) (main : Cmd) (a : Val) (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = a :: rest)
      (fun _ out => out = a :: a :: rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hK.dup
  exact ⟨p, K * (vsz a + 1),
    WordR.conseqK (h main) hK (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hq => by
        rw [hvs] at hq
        obtain ⟨a', r', hab, hout⟩ := hq
        cases hab
        exact hout)
      (fun vs hvs => by rw [hvs]; simp)⟩

theorem exDrop (hK : KernelLib) (main : Cmd) (a : Val) (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = a :: rest)
      (fun _ out => out = rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hK.drop
  exact ⟨p, K * (vsz a + 1),
    WordR.conseqK (h main) hK (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hq => by
        rw [hvs] at hq
        obtain ⟨a', r', hab, hout⟩ := hq
        cases hab
        exact hout)
      (fun vs hvs => by rw [hvs]; simp)⟩

theorem exPushVal (hK : KernelLib) (main : Cmd) (v : Val) (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = rest)
      (fun _ out => out = v :: rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hK.pushVal
  exact ⟨p v, K * (vsz v + 1),
    WordR.conseqK (h main v) hK (fun vs _ => trivial)
      (fun vs out hvs hq => by rw [hvs] at hq; exact hq)
      (fun vs _ => le_rfl)⟩

theorem exConsV (hK : KernelLib) (main : Cmd) (a b : Val) (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = a :: b :: rest)
      (fun _ out => out = .cons a b :: rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hK.consV
  exact ⟨p, K,
    WordR.conseqK (h main) hK (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hq => by
        rw [hvs] at hq
        obtain ⟨a', b', r', hab, hout⟩ := hq
        cases hab
        exact hout)
      (fun vs _ => le_rfl)⟩

theorem exUnconsV (hK : KernelLib) (main : Cmd) (a b : Val) (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = .cons a b :: rest)
      (fun _ out => out = a :: b :: rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hK.unconsV
  exact ⟨p, K,
    WordR.conseqK (h main) hK (fun vs hvs => by rw [hvs]; exact ⟨a, b, rest, rfl⟩)
      (fun vs out hvs hq => by
        rw [hvs] at hq
        obtain ⟨a', b', r', hab, hout⟩ := hq
        cases hab
        exact hout)
      (fun vs _ => le_rfl)⟩

theorem exLength (hK : KernelLib) (hL : LayoutLib) (main : Cmd) (xs : List Val)
    (rest : List Val) :
    ∃ (prog : Cmd) (c : ℕ), WordR main prog (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = .int (xs.length : ℤ) :: ofList xs :: rest) (fun _ => c) := by
  obtain ⟨p, K, h⟩ := hL.length
  exact ⟨p, K * (vsz (ofList xs) + 1),
    WordR.conseqK (h main xs) hK (fun vs hvs => by rw [hvs]; exact ⟨rest, rfl⟩)
      (fun vs out hvs hq => by
        rw [hvs] at hq
        obtain ⟨r', hab, hout⟩ := hq
        cases hab
        exact hout)
      (fun vs _ => le_rfl)⟩

theorem exRoll2 (hK : KernelLib) (main : Cmd) (a b c : Val) (rest : List Val) :
    ∃ (prog : Cmd) (K' : ℕ), WordR main prog (fun vs => vs = a :: b :: c :: rest)
      (fun _ out => out = c :: a :: b :: rest) (fun _ => K') := by
  obtain ⟨p, K, h⟩ := hK.roll
  refine ⟨p 2, K * 3 * (vsz a + vsz b + vsz c + 1), ?_⟩
  refine WordR.conseqK (h main 2) hK ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp
  · intro vs out hvs hq
    rw [hvs] at hq
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
      List.eraseIdx_cons_succ, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero] at hq
    exact hq
  · intro vs hvs
    rw [hvs]
    simp only [List.take_succ_cons, List.take_zero, List.map_cons,
      List.sum_cons, List.sum_nil, List.map_nil]
    exact le_of_eq (by ring)

/-! ## List lemmas -/

theorem perm_vsz {l₁ l₂ : List Val} (h : l₁.Perm l₂) : vsz (ofList l₁) = vsz (ofList l₂) := by
  rw [vsz_ofList, vsz_ofList, h.length_eq, (h.map vsz).sum_eq]

theorem eq_of_getD_eq : ∀ (n : ℕ) (l₁ l₂ : List Val), l₁.length = n → l₂.length = n →
    (∀ i < n, l₁.getD i .nil = l₂.getD i .nil) → l₁ = l₂ := by
  intro n
  induction n with
  | zero =>
      intro l₁ l₂ h₁ h₂ _
      cases l₁ with
      | nil => cases l₂ with
        | nil => rfl
        | cons _ _ => simp at h₂
      | cons _ _ => simp at h₁
  | succ n ih =>
      intro l₁ l₂ h₁ h₂ h
      cases l₁ with
      | nil => simp at h₁
      | cons a l₁ =>
          cases l₂ with
          | nil => simp at h₂
          | cons b l₂ =>
              have ha : a = b := by simpa using h 0 (by simp)
              have hl : l₁ = l₂ := by
                refine ih l₁ l₂ (by simpa using h₁) (by simpa using h₂) ?_
                intro i hi
                simpa using h (i+1) (by simp; omega)
              rw [ha, hl]

theorem forall₂_getD {Q : Val → Val → Prop} {xs ys : List Val}
    (h : List.Forall₂ Q xs ys) (hlen : xs.length = ys.length) :
    ∀ i < xs.length, Q (xs.getD i .nil) (ys.getD i .nil) := by
  intro i hi
  have hi' : i < ys.length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
  exact h.get hi hi'

private theorem ofList_inj_aux : ∀ (l₁ l₂ : List Val), ofList l₁ = ofList l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: l₁, b :: l₂, h => by
      have h' : Val.cons a (ofList l₁) = Val.cons b (ofList l₂) := h
      injection h' with h1 h2
      rw [h1, ofList_inj_aux l₁ l₂ h2]

theorem ofList_inj {l₁ l₂ : List Val} (h : ofList l₁ = ofList l₂) : l₁ = l₂ :=
  ofList_inj_aux l₁ l₂ h

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · rw [Nat.size_le]
    have ha : a < 2 ^ a.size := (Nat.size_le).mp le_rfl
    have hb : b < 2 ^ b.size := (Nat.size_le).mp le_rfl
    calc a * b < 2 ^ a.size * b := mul_lt_mul_of_pos_right ha h
      _ < 2 ^ a.size * 2 ^ b.size := mul_lt_mul_of_pos_left hb (Nat.two_pow_pos _)
      _ = 2 ^ (a.size + b.size) := (pow_add 2 _ _).symm

theorem prod_size_le_vsz_intList {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) :
    ss.prod.size ≤ vsz (intList ss) := by
  rw [vsz_intList]
  induction ss with
  | nil => simp
  | cons a l ih =>
      have hl : ∀ s ∈ l, 1 ≤ s := fun s hs => hpos s (by simp [hs])
      rw [List.map_cons, List.sum_cons, List.length_cons, List.prod_cons]
      have ih' := ih hl
      have hmul : (a * l.prod).size ≤ a.size + l.prod.size := size_mul_le a l.prod
      have h2 : a.size ≤ iszN a := by simp [iszN]
      omega

/-! ## The library bundle -/

/-- Bundles the four library-level words proved elsewhere. -/
structure CrtPieces : Prop where
  join : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (xs ws : List Val), xs.length = ws.length →
    WordR main prog
      (fun vs => ∃ rest, vs = ofList xs :: ofList ws :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: ofList ws :: rest ∧
        out = ofList (zipRec xs ws) :: rest)
      (fun vs => K * (vsz (ofList xs) + vsz (ofList ws) + 1))
  strip : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (rs : List Val),
    (∀ x ∈ rs, ∃ (k : ℤ) (v : Val), x = .cons (.int k) v) →
    WordR main prog
      (fun vs => ∃ rest, vs = ofList rs :: rest)
      (fun vs out => ∃ rest, vs = ofList rs :: rest ∧
        out = ofList (rs.map recPayload) :: rest)
      (fun vs => K * (vsz (ofList rs) + 1))
  lab : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (ss : List ℕ) (S : ℕ),
    (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    WordR main prog
      (fun vs => ∃ rest, vs = .int (S : ℤ) :: intList ss :: rest)
      (fun vs out => ∃ rest, vs = .int (S : ℤ) :: intList ss :: rest ∧
        out = intList (sigmaList ss) :: rest)
      (fun _ => K * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1))
  sorted : ∀ {S : ℕ} {xs : List Val} {lab : List ℕ},
    xs.length = S → lab.length = S →
    (∀ i < S, ∀ j < S, lab.getD i 0 = lab.getD j 0 → i = j) →
    (∀ i < S, lab.getD i 0 < S) →
    ∀ {rs' : List Val}, rs'.Perm (zipRec xs (labVals lab)) →
    rs'.Pairwise (fun a b => pairKey a < pairKey b) →
    ∀ m < S, (rs'.map recPayload).getD m .nil = xs.getD (invLab lab m) .nil

/-- All the library words (with their cost constants) used by the reindexing proof. -/
structure CrtLib where
  hK : KernelLib
  hSorted : ∀ {S : ℕ} {xs : List Val} {lab : List ℕ},
    xs.length = S → lab.length = S →
    (∀ i < S, ∀ j < S, lab.getD i 0 = lab.getD j 0 → i = j) →
    (∀ i < S, lab.getD i 0 < S) →
    ∀ {rs' : List Val}, rs'.Perm (zipRec xs (labVals lab)) →
    rs'.Pairwise (fun a b => pairKey a < pairKey b) →
    ∀ m < S, (rs'.map recPayload).getD m .nil = xs.getD (invLab lab m) .nil
  pLab : Cmd
  KLab : ℕ
  hLab : ∀ (main : Cmd) (ss : List ℕ) (S : ℕ), (∀ s ∈ ss, 1 ≤ s) → S = ss.prod →
    WordR main pLab (fun vs => ∃ rest, vs = .int (S : ℤ) :: intList ss :: rest)
      (fun vs out => ∃ rest, vs = .int (S : ℤ) :: intList ss :: rest ∧
        out = intList (sigmaList ss) :: rest)
      (fun _ => KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1))
  pJoin : Cmd
  KJoin : ℕ
  hJoin : ∀ (main : Cmd) (xs ws : List Val), xs.length = ws.length →
    WordR main pJoin
      (fun vs => ∃ rest, vs = ofList xs :: ofList ws :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: ofList ws :: rest ∧
        out = ofList (zipRec xs ws) :: rest)
      (fun vs => KJoin * (vsz (ofList xs) + vsz (ofList ws) + 1))
  pStrip : Cmd
  KStrip : ℕ
  hStrip : ∀ (main : Cmd) (rs : List Val),
    (∀ x ∈ rs, ∃ (k : ℤ) (v : Val), x = .cons (.int k) v) →
    WordR main pStrip
      (fun vs => ∃ rest, vs = ofList rs :: rest)
      (fun vs out => ∃ rest, vs = ofList rs :: rest ∧
        out = ofList (rs.map recPayload) :: rest)
      (fun vs => KStrip * (vsz (ofList rs) + 1))
  pSort : Cmd
  KSort : ℕ
  hSort : ∀ (main : Cmd) (xs : List Val),
    (∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = .cons (.int (k : ℤ)) v) → (xs.map pairKey).Nodup →
    WordR main pSort (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest ys, vs = ofList xs :: rest ∧ out = ofList ys :: rest ∧
        ys.Perm xs ∧ ys.Pairwise (fun a b => pairKey a < pairKey b))
      (fun _ => KSort * (vsz (ofList xs) + 1) * (xs.length.size + 1))
  pSwap : Cmd
  KSwap : ℕ
  hSwap : ∀ main, WordR main pSwap (fun vs => 2 ≤ vs.length)
    (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (fun vs => KSwap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
  pDup : Cmd
  KDup : ℕ
  hDup : ∀ main, WordR main pDup (fun vs => vs ≠ [])
    (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
    (fun vs => KDup * (vsz (vs.headD .nil) + 1))
  pDrop : Cmd
  KDrop : ℕ
  hDrop : ∀ main, WordR main pDrop (fun vs => vs ≠ [])
    (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
    (fun vs => KDrop * (vsz (vs.headD .nil) + 1))
  pUnc : Cmd
  KUnc : ℕ
  hUnc : ∀ main, WordR main pUnc (fun vs => ∃ a b rest, vs = .cons a b :: rest)
    (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => KUnc)
  pCons : Cmd
  KCons : ℕ
  hCons : ∀ main, WordR main pCons (fun vs => 2 ≤ vs.length)
    (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => KCons)
  pPush : Val → Cmd
  KPush : ℕ
  hPush : ∀ (main : Cmd) (v : Val), WordR main (pPush v) (fun _ => True)
    (fun vs out => out = v :: vs) (fun _ => KPush * (vsz v + 1))
  pRep : Val → Cmd
  KRep : ℕ
  hRep : ∀ (main : Cmd) (k : ℕ) (v : Val), WordR main (pRep v)
    (fun vs => ∃ rest, vs = .int (k : ℤ) :: v :: rest)
    (fun vs out => ∃ rest, vs = .int (k : ℤ) :: v :: rest ∧
      out = ofList (List.replicate k v) :: rest)
    (fun _ => KRep * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1))
  pEnum : Cmd
  KEnum : ℕ
  hEnum : ∀ (main : Cmd) (xs : List Val), WordR main pEnum (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
      out = ofList ((List.range xs.length).map fun i : ℕ =>
        Val.cons (.int (i : ℤ)) (xs.getD i .nil)) :: rest)
    (fun _ => KEnum * (vsz (ofList xs) + xs.length * (xs.length.size + 1) + 1))
  pMap : Cmd → Cmd
  KMap : ℕ
  hMap : ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ),
    (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
    ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) →
    WordR main (pMap q) (fun vs => vs = ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys)
      (fun _ => xs.length * (c + KMap * (L + 1)) + KMap)
  pRoll : ℕ → Cmd
  KRoll : ℕ
  hRoll : ∀ (main : Cmd) (k : ℕ), WordR main (pRoll k) (fun vs => k < vs.length)
    (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
    (fun vs => KRoll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
  pLen : Cmd
  KLen : ℕ
  hLen : ∀ (main : Cmd) (xs : List Val), WordR main pLen (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
      out = .int (xs.length : ℤ) :: ofList xs :: rest)
    (fun _ => KLen * (vsz (ofList xs) + 1))
  pIfz : Cmd → Cmd → Cmd
  KIfz : ℕ
  hIfz : ∀ (main q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop)
      (c₁ c₂ : ℕ),
    (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
    (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
    WordR main (pIfz q₁ q₂) (fun vs => vs = .int z :: rest)
      (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out))
      (fun _ => KIfz * (isz z + 1) + max c₁ c₂)

theorem stripPerm (hK : KernelLib) {pStrip : Cmd} {KStrip : ℕ}
    (hStrip : ∀ (main : Cmd) (rs : List Val),
      (∀ x ∈ rs, ∃ (k : ℤ) (v : Val), x = .cons (.int k) v) →
      WordR main pStrip (fun vs => ∃ rest, vs = ofList rs :: rest)
        (fun vs out => ∃ rest, vs = ofList rs :: rest ∧ out = ofList (rs.map recPayload) :: rest)
        (fun vs => KStrip * (vsz (ofList rs) + 1)))
    (main : Cmd) (recs : List Val) (rest : List Val)
    (hrec : ∀ x ∈ recs, ∃ (k : ℤ) (v : Val), x = .cons (.int k) v) :
    WordR main pStrip
      (fun vs => ∃ rs, vs = ofList rs :: rest ∧ rs.Perm recs)
      (fun vs out => ∃ rs ys, vs = ofList rs :: rest ∧ rs.Perm recs ∧
        out = ofList ys :: rest ∧ ys = rs.map recPayload)
      (fun _ => KStrip * (vsz (ofList recs) + 1)) := by
  intro vs hvs s R hs
  obtain ⟨rs, hrs, hperm⟩ := hvs
  subst hrs
  have hrs_rec : ∀ x ∈ rs, ∃ (k : ℤ) (v : Val), x = .cons (.int k) v :=
    fun x hx => hrec x (hperm.mem_iff.mp hx)
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hStrip main rs hrs_rec (ofList rs :: rest) ⟨rest, rfl⟩ s R hs
  obtain ⟨r', hab, hout⟩ := hpost
  cases hab
  refine ⟨out, s', n, ⟨rs, rs.map recPayload, rfl, hperm, hout, rfl⟩, hev, ?_, hstk, hfr⟩
  rw [perm_vsz hperm] at hn
  exact hn

/-! ## The cost budget -/

/-- The base size `vsz (ofList xs) + S * (vsz (intList ss) + 1) + 1`. -/
def PB (ss : List ℕ) (S : ℕ) (xs : List Val) : ℕ :=
  vsz (ofList xs) + S * (vsz (intList ss) + 1) + 1

/-- The length factor `S.size + 1`. -/
def QB (S : ℕ) : ℕ := S.size + 1

/-- The target size of the `CrtWordProp` cost: `(vsz xs + S (vsz ss + 1) + 1) (size S + 1)`. -/
def SB (ss : List ℕ) (S : ℕ) (xs : List Val) : ℕ := PB ss S xs * QB S

/-- Sum of all library cost constants. -/
def KS (L : CrtLib) : ℕ :=
  L.KJoin + L.KStrip + L.KSort + L.KSwap + L.KDup + L.KDrop + L.KUnc + L.KCons + L.KPush
  + L.KRep + L.KEnum + L.KMap + L.KRoll + L.KLen + L.KIfz + L.KLab

/-- Final cost constant: a large multiple of all library constants. -/
def KF (L : CrtLib) : ℕ := 1000 * (KS L + 1)

/-- One unit of cost: `KF L * SB ss S xs` (`KF L` dominates every library constant). -/
def CU (L : CrtLib) (ss : List ℕ) (S : ℕ) (xs : List Val) : ℕ := KF L * SB ss S xs

/-- The budget of the tail word: 100 cost units. -/
def BUD (L : CrtLib) (ss : List ℕ) (S : ℕ) (xs : List Val) : ℕ := 100 * CU L ss S xs

theorem BUD_eq (L : CrtLib) (ss : List ℕ) (S : ℕ) (xs : List Val) :
    BUD L ss S xs = 100 * (KF L * SB ss S xs) := by rw [BUD, CU]

/-- The list of all library constants. -/
def kList (L : CrtLib) : List ℕ :=
  [L.KJoin, L.KStrip, L.KSort, L.KSwap, L.KDup, L.KDrop, L.KUnc, L.KCons, L.KPush, L.KRep,
   L.KEnum, L.KMap, L.KRoll, L.KLen, L.KIfz, L.KLab]

theorem KF_ge (L : CrtLib) {x : ℕ} (h : x ∈ kList L) : x ≤ KF L := by
  simp only [kList, KF, KS, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem one_le_KB (L : CrtLib) : 1 ≤ KF L := by
  rw [KF]; omega

/-! ## Budget arithmetic -/

theorem one_le_PB (ss : List ℕ) (S : ℕ) (xs : List Val) : 1 ≤ PB ss S xs := by
  rw [PB]; omega

theorem V_le_PB (ss : List ℕ) (S : ℕ) (xs : List Val) : vsz (ofList xs) ≤ PB ss S xs := by
  rw [PB]; omega

theorem one_le_QB (S : ℕ) : 1 ≤ QB S := by rw [QB]; omega

theorem PB_le_SB (ss : List ℕ) (S : ℕ) (xs : List Val) : PB ss S xs ≤ SB ss S xs := by
  rw [SB]
  calc PB ss S xs = PB ss S xs * 1 := (Nat.mul_one _).symm
    _ ≤ PB ss S xs * QB S := Nat.mul_le_mul_left _ (one_le_QB S)

theorem one_le_SB (ss : List ℕ) (S : ℕ) (xs : List Val) : 1 ≤ SB ss S xs :=
  le_trans (one_le_PB ss S xs) (PB_le_SB ss S xs)

theorem prod_pos_of_pos {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) : 1 ≤ ss.prod := by
  have h : 0 < ss.prod := List.prod_pos (fun s hs => by have := hpos s hs; omega)
  omega

theorem S_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} (hxs : xs.length = S) :
    S ≤ PB ss S xs := by
  have h := length_le_vsz_ofList xs
  rw [hxs] at h
  exact le_trans h (V_le_PB ss S xs)

theorem W_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} (hS1 : 1 ≤ S) :
    vsz (intList ss) ≤ PB ss S xs := by
  rw [PB]
  calc vsz (intList ss) = vsz (intList ss) * 1 := (Nat.mul_one _).symm
    _ ≤ vsz (intList ss) * S := Nat.mul_le_mul_left _ hS1
    _ ≤ S * (vsz (intList ss) + 1) := by
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ vsz (ofList xs) + S * (vsz (intList ss) + 1) + 1 := by omega

theorem L_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} (hpos : ∀ s ∈ ss, 1 ≤ s)
    (hS : S = ss.prod) : S.size ≤ PB ss S xs := by
  subst hS
  exact le_trans (prod_size_le_vsz_intList hpos)
    (W_le_PB (S := ss.prod) (prod_pos_of_pos hpos))

/-- Every label list of length `S` with values `< S` has size `≤ 5 * PB`. -/
theorem Vlab_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} {lab : List ℕ}
    (hpos : ∀ s ∈ ss, 1 ≤ s) (hS : S = ss.prod) (hlab : lab.length = S)
    (hlt : ∀ i < S, lab.getD i 0 < S) :
    vsz (ofList (labVals lab)) ≤ 5 * PB ss S xs := by
  have h1 : vsz (ofList (labVals lab)) ≤ S * (S.size + 2) + S + 1 := vsz_labVals_le hlt hlab
  have hS1 : 1 ≤ S := by rw [hS]; exact prod_pos_of_pos hpos
  have hSf : S ≤ S * (vsz (intList ss) + 1) := by
    calc S = S * 1 := (Nat.mul_one _).symm
      _ ≤ S * (vsz (intList ss) + 1) := Nat.mul_le_mul_left _ (by omega)
  have hS2 : S ≤ PB ss S xs := by rw [PB]; omega
  have h2 : S * (S.size + 2) ≤ 2 * (S * (vsz (intList ss) + 1)) := by
    have hLW : S.size ≤ vsz (intList ss) := by rw [hS]; exact prod_size_le_vsz_intList hpos
    have h3 : S.size + 2 ≤ 2 * (vsz (intList ss) + 1) := by omega
    calc S * (S.size + 2) ≤ S * (2 * (vsz (intList ss) + 1)) := Nat.mul_le_mul_left _ h3
      _ = 2 * (S * (vsz (intList ss) + 1)) := by ring
  rw [PB] at hS2 ⊢
  omega

/-- The records of the label-and-sort word have size `≤ 10 * PB`. -/
theorem Vzip_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} {lab : List ℕ}
    (hpos : ∀ s ∈ ss, 1 ≤ s) (hS : S = ss.prod) (hxs : xs.length = S)
    (hlab : lab.length = S) (hlt : ∀ i < S, lab.getD i 0 < S) :
    vsz (ofList (zipRec xs (labVals lab))) ≤ 10 * PB ss S xs := by
  have h1 : vsz (ofList (zipRec xs (labVals lab)))
      ≤ vsz (ofList xs) + vsz (ofList (labVals lab)) + S :=
    vsz_zipRec_le hxs (by rw [labVals, List.length_map, hlab])
  have h2 : vsz (ofList (labVals lab)) ≤ 5 * PB ss S xs := Vlab_le_PB hpos hS hlab hlt
  have h3 : vsz (ofList xs) ≤ PB ss S xs := V_le_PB ss S xs
  have h4 : S ≤ PB ss S xs := S_le_PB hxs
  omega

theorem zipRec_len_eq {S : ℕ} {xs : List Val} {lab : List ℕ} (hxs : xs.length = S)
    (hlab : lab.length = S) : (zipRec xs (labVals lab)).length = S := by
  rw [zipRec_length (by rw [labVals, List.length_map, hlab]; exact hxs)]
  exact hxs

/-- The sort cost factor for the records. -/
theorem zipRec_size_eq {S : ℕ} {xs : List Val} {lab : List ℕ} (hxs : xs.length = S)
    (hlab : lab.length = S) : (zipRec xs (labVals lab)).length.size + 1 = QB S := by
  rw [zipRec_len_eq hxs hlab, QB]

end Work.MainP
