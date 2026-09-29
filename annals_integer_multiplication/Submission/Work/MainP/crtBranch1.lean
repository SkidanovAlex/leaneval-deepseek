import Mathlib
import Submission.Work.MainP.crtLib
import Submission.Work.MainP.crtTail
import Submission.Work.MainP.crtMath
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtB1_forall2_eq

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `crtBranch1`: the `dir = 1` branch of the Agarwal–Cooley reindexing

From `int S :: intList ss :: ofList xs :: rest` (with `S = ∏ ss`, `ss` pairwise coprime,
`xs.length = S`) a word produces `ofList ys :: rest` with `ys[m] = xs[crtIdx ss m]`, i.e.
`ys[m] = xs[(crtQ ss).getD m 0]`, at cost `C * CU L ss S xs`.

Following `CRTBRANCH.md`: duplicate `S`, run `pLab` (obtaining `intList (sigmaList ss)`, the list of
labels `crtIdx ss i`), push `S` copies of `nil`, run `pEnum` (labelling them `0, …, S-1`), `pMap`
off the `nil` payloads, `pJoin` with the label list `sigmaList ss`, `pSort` by key and `pStrip` the
keys — the resulting label list is `labVals (crtQ ss)`, which is fed to `tailWord`.
-/

namespace Work.MainP

open HvdH

/-! ## Arithmetic helpers -/

theorem vsz_nil_eq : vsz (Val.nil : Val) = 1 := rfl

theorem le_PB_mul_QB (ss : List ℕ) (S : ℕ) (xs : List Val) :
    PB ss S xs ≤ PB ss S xs * QB S := by
  have h := Nat.mul_le_mul_left (PB ss S xs) (one_le_QB S)
  simpa using h

theorem one_le_PB_mul_QB (ss : List ℕ) (S : ℕ) (xs : List Val) : 1 ≤ PB ss S xs * QB S :=
  le_trans (one_le_PB ss S xs) (le_PB_mul_QB ss S xs)

theorem size_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} (hxs : xs.length = S) :
    S.size ≤ PB ss S xs :=
  le_trans (Nat.size_le.mpr Nat.lt_two_pow_self) (S_le_PB hxs)

theorem mul_le_CU (L : CrtLib) {ss : List ℕ} {S : ℕ} {xs : List Val} {k m d e : ℕ}
    (hk : k ≤ KF L * e) (hm : m ≤ d * (PB ss S xs * QB S)) : k * m ≤ (d * e) * CU L ss S xs := by
  calc k * m ≤ (KF L * e) * (d * (PB ss S xs * QB S)) := Nat.mul_le_mul hk hm
    _ = (d * e) * (KF L * (PB ss S xs * QB S)) := by ring
    _ = (d * e) * CU L ss S xs := by rw [CU, SB]

theorem mul_le_CU' (L : CrtLib) {ss : List ℕ} {S : ℕ} {xs : List Val} {k m d e c : ℕ}
    (hk : k ≤ KF L * e) (hm : m ≤ d * (PB ss S xs * QB S)) (hde : d * e ≤ c) :
    k * m ≤ c * CU L ss S xs :=
  le_trans (mul_le_CU L hk hm) (Nat.mul_le_mul_right _ hde)

theorem le_mul_QB_of_le_PB {ss : List ℕ} {S : ℕ} {xs : List Val} {m d : ℕ}
    (h : m ≤ d * PB ss S xs) : m ≤ d * (PB ss S xs * QB S) :=
  le_trans h (Nat.mul_le_mul_left d (le_PB_mul_QB ss S xs))

theorem lt_S_of_lt_prod {ss : List ℕ} {S m : ℕ} (hS : S = ss.prod) (h : m < ss.prod) : m < S := by
  rw [hS]; exact h

theorem lt_prod_of_lt_S {ss : List ℕ} {S m : ℕ} (hS : S = ss.prod) (h : m < S) : m < ss.prod := by
  rw [hS] at h; exact h

/-- Composing two words whose postconditions are equalities. -/
theorem seqEqK {main p q : Cmd} {P : List Val → Prop} {S1 S2 : List Val} {C B : ℕ}
    (w1 : WordR main p P (fun _ out => out = S1) (fun _ => C))
    (w2 : WordR main q (fun vs => vs = S1) (fun _ out => out = S2) (fun _ => B))
    (hK : KernelLib) : WordR main (.seq p q) P (fun _ out => out = S2) (fun _ => C + B) := by
  refine WordR.conseqK
    (WordR.seqK w1 w2 hK (B := fun _ => B) (fun vs mid _ hq => ⟨hq, le_rfl⟩))
    hK (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro vs out _ hq
  obtain ⟨m, _hm, hout⟩ := hq
  exact hout

/-! ## The payload list `[0, …, S-1]` -/

/-- `[cons (.int 0) .nil, …, cons (.int (S-1)) .nil]`, the records with empty payloads and keys
`0, …, S-1`. -/
def recLab (S : ℕ) : List Val := (List.range S).map (fun i : ℕ => Val.cons (.int (i : ℤ)) Val.nil)

theorem recLab_length (S : ℕ) : (recLab S).length = S := by simp [recLab]

theorem recLab_getD {S i : ℕ} (h : i < S) :
    (recLab S).getD i Val.nil = Val.cons (.int (i : ℤ)) Val.nil := by
  rw [List.getD_eq_getElem _ _ (by rw [recLab_length]; exact h)]
  simp only [recLab, List.getElem_map, List.getElem_range (by simpa using h)]

theorem recLab_mem {S : ℕ} {x : Val} (hx : x ∈ recLab S) :
    ∃ j, j < S ∧ x = Val.cons (.int (j : ℤ)) Val.nil := by
  obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
  have hjS : j < S := by rwa [recLab_length] at hj
  exact ⟨j, hjS,
    by rw [← hjx, ← List.getD_eq_getElem (recLab S) Val.nil hj, recLab_getD hjS]⟩

/-- The list produced by `pEnum` out of `S` copies of `nil` is `recLab S`. -/
theorem enumList_eq_recLab (S : ℕ) :
    (List.range (List.replicate S Val.nil).length).map
        (fun i : ℕ => Val.cons (.int (i : ℤ)) ((List.replicate S Val.nil).getD i Val.nil))
      = recLab S := by
  rw [List.length_replicate]
  unfold recLab
  apply List.map_congr_left
  intro i _hi
  by_cases h : i < S
  · rw [List.getD_replicate Val.nil h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]

theorem vsz_nilRep (S : ℕ) : vsz (ofList (List.replicate S Val.nil)) = 2 * S + 1 := by
  induction S with
  | zero => simp [List.replicate_zero, ofList, vsz, Val.enc]
  | succ S ih =>
      rw [List.replicate_succ]
      show vsz (Val.cons Val.nil (ofList (List.replicate S Val.nil))) = 2 * (S + 1) + 1
      rw [vsz_cons, ih, vsz_nil_eq]
      ring

/-! ## The record list `zipRec (labVals (range S)) (labVals (sigmaList ss))` -/

/-- The sorted record list of the branch: key `crtIdx ss i`, payload `i`. -/
def crtZ (ss : List ℕ) (S : ℕ) : List Val :=
  zipRec (labVals (List.range S)) (labVals (sigmaList ss))

theorem labVals_range_length (S : ℕ) : (labVals (List.range S)).length = S := by simp [labVals]

theorem labVals_sigmaList_length (ss : List ℕ) (S : ℕ) (hS : S = ss.prod) :
    (labVals (sigmaList ss)).length = S := by
  rw [labVals, List.length_map, sigmaList_length, hS]

theorem getD_range_self {n i : ℕ} (h : i < n) : (List.range n).getD i 0 = i := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_range]),
    List.getElem_range (by rwa [List.length_range])]

theorem crtZ_length {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) : (crtZ ss S).length = S := by
  rw [crtZ, zipRec_length (xs := labVals (List.range S)) (ws := labVals (sigmaList ss))
      (by rw [labVals_range_length, labVals_sigmaList_length ss S hS]),
    labVals_range_length]

theorem labVals_range_getD {S i : ℕ} (h : i < S) :
    (labVals (List.range S)).getD i Val.nil = Val.int (i : ℤ) := by
  rw [labVals_getD (l := List.range S) (by rwa [List.length_range]), getD_range_self h]

theorem labVals_crtQ_getD {ss : List ℕ} {m : ℕ} (hm : m < ss.prod) :
    (labVals (crtQ ss)).getD m Val.nil = Val.int (crtPinv ss m : ℤ) := by
  rw [labVals_getD (l := crtQ ss) (by rw [crtQ_length]; exact hm), crtQ_getD hm]

theorem crtZ_getD {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) {i : ℕ} (hi : i < S) :
    (crtZ ss S).getD i Val.nil
      = Val.cons (Val.int ((sigmaList ss).getD i 0 : ℤ)) (Val.int (i : ℤ)) := by
  have hlen : (labVals (List.range S)).length = (labVals (sigmaList ss)).length := by
    rw [labVals_range_length, labVals_sigmaList_length ss S hS]
  rw [crtZ, zipRec_getD hlen (by rw [labVals_range_length]; exact hi),
    labVals_getD (l := sigmaList ss) (by rw [sigmaList_length]; exact lt_prod_of_lt_S hS hi),
    labVals_getD (l := List.range S) (by rw [List.length_range]; exact hi),
    getD_range_self hi]

/-! ## The label list is the sparse CRT index list -/

/-- Sorting the record list `crtZ` by key and stripping the keys yields `labVals (crtQ ss)`: this is
`L.hSorted` (`crtSorted`) read with `xs := labVals (range S)`, `lab := sigmaList ss`. -/
theorem crtB1SortStripAux (L : CrtLib) {ss : List ℕ} {S : ℕ} {rs' : List Val}
    (hpos : ∀ s ∈ ss, 1 ≤ s) (hS : S = ss.prod) (hcop : ss.Pairwise Nat.Coprime)
    (hperm : rs'.Perm (zipRec (labVals (List.range S)) (labVals (sigmaList ss))))
    (hsort : rs'.Pairwise (fun a b => pairKey a < pairKey b)) :
    rs'.map recPayload = labVals (crtQ ss) := by
  have hpos0 : ∀ s ∈ ss, 0 < s := fun s hs => by have := hpos s hs; omega
  have hXs : (labVals (List.range S)).length = S := labVals_range_length S
  have hlab : (sigmaList ss).length = S := by rw [hS]; exact sigmaList_length ss
  have hinj : ∀ i < S, ∀ j < S, (sigmaList ss).getD i 0 = (sigmaList ss).getD j 0 → i = j :=
    fun i hi j hj h => sigmaList_inj hcop hpos0 (lt_prod_of_lt_S hS hi) (lt_prod_of_lt_S hS hj) h
  have hlt : ∀ i < S, (sigmaList ss).getD i 0 < S :=
    fun i hi => lt_S_of_lt_prod hS (sigmaList_lt hpos0 (lt_prod_of_lt_S hS hi))
  have hkey := L.hSorted (S := S) (xs := labVals (List.range S)) (lab := sigmaList ss)
    hXs hlab hinj hlt hperm hsort
  refine eq_of_getD_eq S (rs'.map recPayload) (labVals (crtQ ss)) ?_ ?_ ?_
  · rw [List.length_map, hperm.length_eq,
      zipRec_length (xs := labVals (List.range S)) (ws := labVals (sigmaList ss))
        (by rw [hXs, labVals_sigmaList_length ss S hS]), hXs]
  · rw [labVals, List.length_map, crtQ_length, hS]
  · intro m hm
    have hmS : m < ss.prod := lt_prod_of_lt_S hS hm
    have hpv : crtPinv ss m < S := lt_S_of_lt_prod hS (crtPinv_lt hcop hpos0 hmS)
    rw [hkey m hm, invLab_sigmaList hcop hpos0 hmS, labVals_range_getD hpv, labVals_crtQ_getD hmS]

/-! ## The per-element program of `pMap` -/

/-- `pUnc; pSwap; pDrop` turns a record `cons (int i) nil` into `int i`, at cost
`KUnc + KSwap * (B + 2) + KDrop * (B + 2)` whenever `iszN i ≤ B`. -/
theorem crtB1MapElemAux (L : CrtLib) :
    ∃ (q : Cmd), ∀ (main : Cmd) (rest : List Val) (i B : ℕ), iszN i ≤ B →
      WordR main q
        (fun vs => vs = Val.cons (.int (i : ℤ)) Val.nil :: rest)
        (fun _ out => out = Val.int (i : ℤ) :: rest)
        (fun _ => L.KUnc + L.KSwap * (B + 2) + L.KDrop * (B + 2)) := by
  refine ⟨.seq (.seq L.pUnc L.pSwap) L.pDrop, ?_⟩
  intro main rest i B hi
  have hc1 : WordR main L.pUnc
      (fun vs => vs = Val.cons (.int (i : ℤ)) Val.nil :: rest)
      (fun _ out => out = Val.int (i : ℤ) :: Val.nil :: rest) (fun _ => L.KUnc) := by
    refine WordR.conseqK (L.hUnc main) L.hK ?_ ?_ ?_
    · intro vs hvs; exact ⟨.int (i : ℤ), .nil, rest, hvs⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨a, b, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs _; exact le_rfl
  have hc2 : WordR main L.pSwap
      (fun vs => vs = Val.int (i : ℤ) :: Val.nil :: rest)
      (fun _ out => out = Val.nil :: Val.int (i : ℤ) :: rest)
      (fun _ => L.KSwap * (vsz (Val.int (i : ℤ)) + vsz (Val.nil : Val) + 1)) := by
    refine WordR.conseqK (L.hSwap main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨a, b, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs; rw [hvs]; simp
  have hc3 : WordR main L.pDrop
      (fun vs => vs = Val.nil :: Val.int (i : ℤ) :: rest)
      (fun _ out => out = Val.int (i : ℤ) :: rest)
      (fun _ => L.KDrop * (vsz (Val.nil : Val) + 1)) := by
    refine WordR.conseqK (L.hDrop main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨v, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs; rw [hvs]; simp
  have h12 := seqEqK hc1 hc2 L.hK
  have h123 := seqEqK h12 hc3 L.hK
  refine WordR.conseqK h123 L.hK (fun vs hvs => hvs) (fun vs out _ hq => hq) ?_
  intro vs _
  rw [vsz_intNat, vsz_nil_eq]
  have h1 : iszN i + 1 + 1 ≤ B + 2 := by omega
  have h2 : (2 : ℕ) ≤ B + 2 := by omega
  exact Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ h1))
    (Nat.mul_le_mul_left _ h2)

/-! ## The head word: `labVals (crtQ ss)` from `int S :: intList ss :: ofList xs` -/

theorem crtBranch1Head (L : CrtLib) :
    ∃ (prog : Cmd) (C : ℕ),
      ∀ (main : Cmd) (ss : List ℕ) (S : ℕ) (xs : List Val) (rest : List Val),
        (∀ s ∈ ss, 1 ≤ s) → S = ss.prod → ss.Pairwise Nat.Coprime → xs.length = S →
        WordR main prog
          (fun vs => vs = .int (S : ℤ) :: intList ss :: ofList xs :: rest)
          (fun _ out => out = ofList (labVals (crtQ ss)) :: ofList xs :: rest)
          (fun _ => C * CU L ss S xs) := by
  obtain ⟨qMap, hqMap⟩ := crtB1MapElemAux L
  refine ⟨.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq L.pDup (L.pRoll 2))
    L.pSwap) L.pLab) L.pSwap) (L.pPush Val.nil)) L.pSwap) (L.pRep Val.nil)) L.pEnum)
    (L.pMap qMap)) L.pJoin) (.seq L.pSort L.pStrip), 200, ?_⟩
  intro main ss S xs rest hpos hS hcop hxs
  have hpos0 : ∀ s ∈ ss, 0 < s := fun s hs => by have := hpos s hs; omega
  have hS1 : 1 ≤ S := by rw [hS]; exact prod_pos_of_pos hpos
  have hPB1 : 1 ≤ PB ss S xs := one_le_PB ss S xs
  have hlab : (sigmaList ss).length = S := by rw [hS]; exact sigmaList_length ss
  have hlt : ∀ i < S, (sigmaList ss).getD i 0 < S :=
    fun i hi => lt_S_of_lt_prod hS (sigmaList_lt hpos0 (lt_prod_of_lt_S hS hi))
  have hA_le : vsz (Val.int (S : ℤ)) ≤ 3 * PB ss S xs := by
    rw [vsz_intNat, iszN]
    have h1 : S.size ≤ PB ss S xs := size_le_PB (ss := ss) (S := S) (xs := xs) hxs
    omega
  have hW_le : vsz (intList ss) ≤ PB ss S xs := W_le_PB (ss := ss) (S := S) (xs := xs) hS1
  have hSig_le : vsz (ofList (labVals (sigmaList ss))) ≤ 5 * PB ss S xs :=
    Vlab_le_PB (ss := ss) (S := S) (xs := xs) (lab := sigmaList ss) hpos hS hlab hlt
  -- phase 1: `pDup`
  have h1 : WordR main L.pDup
      (fun vs => vs = Val.int (S : ℤ) :: intList ss :: ofList xs :: rest)
      (fun _ out => out = Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: ofList xs :: rest)
      (fun _ => 4 * CU L ss S xs) := by
    refine WordR.conseqK (L.hDup main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨v, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.headD_cons]
      refine mul_le_CU' L (k := L.KDup) (m := vsz (Val.int (S : ℤ)) + 1) (d := 4) (e := 1)
        (c := 4) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := vsz (Val.int (S : ℤ)) + 1) (d := 4) (by omega)
  -- phase 2: `pRoll 2`
  have h2 : WordR main (L.pRoll 2)
      (fun vs => vs = Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: ofList xs :: rest)
      (fun _ out => out = intList ss :: Val.int (S : ℤ) :: Val.int (S : ℤ) :: ofList xs :: rest)
      (fun _ => 30 * CU L ss S xs) := by
    refine WordR.conseqK (L.hRoll main 2) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
        List.eraseIdx_cons_succ, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero] at hq
      exact hq
    · intro vs hvs
      rw [hvs]
      refine mul_le_CU' L (k := L.KRoll * (2 + 1))
        (m := ((List.take (2 + 1)
            (Val.int (S : ℤ) :: Val.int (S : ℤ) :: intList ss :: ofList xs :: rest)).map vsz).sum + 1)
        (d := 8) (e := 3) (c := 30)
        (Nat.mul_le_mul_right 3 (KF_ge L (by simp [kList]))) ?_ (by omega)
      refine le_mul_QB_of_le_PB (d := 8) ?_
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.sum_cons,
        List.sum_nil, List.map_nil]
      omega
  -- phase 3: `pSwap`
  have h3 : WordR main L.pSwap
      (fun vs => vs = intList ss :: Val.int (S : ℤ) :: Val.int (S : ℤ) :: ofList xs :: rest)
      (fun _ out => out = Val.int (S : ℤ) :: intList ss :: Val.int (S : ℤ) :: ofList xs :: rest)
      (fun _ => 12 * CU L ss S xs) := by
    refine WordR.conseqK (L.hSwap main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨a, b, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      refine mul_le_CU' L (k := L.KSwap) (m := vsz (intList ss) + vsz (Val.int (S : ℤ)) + 1)
        (d := 12) (e := 1) (c := 12) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := vsz (intList ss) + vsz (Val.int (S : ℤ)) + 1) (d := 12)
        (by omega)
  -- phase 4: `pLab`
  have h4 : WordR main L.pLab
      (fun vs => vs = Val.int (S : ℤ) :: intList ss :: Val.int (S : ℤ) :: ofList xs :: rest)
      (fun _ out => out = intList (sigmaList ss) :: Val.int (S : ℤ) :: ofList xs :: rest)
      (fun _ => 2 * CU L ss S xs) := by
    refine WordR.conseqK (L.hLab main ss S hpos hS) L.hK ?_ ?_ ?_
    · intro vs hvs; exact ⟨Val.int (S : ℤ) :: ofList xs :: rest, hvs⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs _
      have hKLab : L.KLab ≤ KF L := KF_ge L (by simp [kList])
      have h1 : S * (vsz (intList ss) + 1) ≤ PB ss S xs := by rw [PB]; omega
      have h2 : S * (vsz (intList ss) + 1) * (S.size + 1) ≤ SB ss S xs := by
        rw [SB, QB]
        exact Nat.mul_le_mul_right _ h1
      have h3 : S * (vsz (intList ss) + 1) * (S.size + 1) + 1 ≤ 2 * SB ss S xs := by
        have := one_le_SB ss S xs; omega
      calc L.KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1)
          ≤ KF L * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1) :=
            Nat.mul_le_mul_right _ hKLab
        _ ≤ KF L * (2 * SB ss S xs) := Nat.mul_le_mul_left _ h3
        _ = 2 * (KF L * SB ss S xs) := by ring
        _ = 2 * CU L ss S xs := by rw [CU]
  -- phase 5: `pSwap`
  have h5 : WordR main L.pSwap
      (fun vs => vs = intList (sigmaList ss) :: Val.int (S : ℤ) :: ofList xs :: rest)
      (fun _ out => out = Val.int (S : ℤ) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => 12 * CU L ss S xs) := by
    refine WordR.conseqK (L.hSwap main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨a, b, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [intList_eq_ofList (sigmaList ss)]
      refine mul_le_CU' L (k := L.KSwap)
        (m := vsz (ofList (labVals (sigmaList ss))) + vsz (Val.int (S : ℤ)) + 1)
        (d := 12) (e := 1) (c := 12) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := vsz (ofList (labVals (sigmaList ss))) + vsz (Val.int (S : ℤ)) + 1)
        (d := 12) (by omega)
  -- phase 6: `pPush .nil`
  have h6 : WordR main (L.pPush Val.nil)
      (fun vs => vs = Val.int (S : ℤ) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => out = Val.nil :: Val.int (S : ℤ) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => 5 * CU L ss S xs) := by
    refine WordR.conseqK (L.hPush main Val.nil) L.hK (fun vs _ => trivial) ?_ ?_
    · intro vs out hvs hq
      rw [hvs] at hq
      exact hq
    · intro vs _
      have hnil : vsz (Val.nil : Val) = 1 := vsz_nil_eq
      refine mul_le_CU' L (k := L.KPush) (m := vsz (Val.nil : Val) + 1) (d := 2) (e := 1) (c := 5)
        (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := vsz (Val.nil : Val) + 1) (d := 2)
        (by have := one_le_PB_mul_QB ss S xs; omega)
  -- phase 7: `pSwap`
  have h7 : WordR main L.pSwap
      (fun vs => vs = Val.nil :: Val.int (S : ℤ) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => out = Val.int (S : ℤ) :: Val.nil :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => 12 * CU L ss S xs) := by
    refine WordR.conseqK (L.hSwap main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨a, b, r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      have hnil : vsz (Val.nil : Val) = 1 := vsz_nil_eq
      refine mul_le_CU' L (k := L.KSwap) (m := vsz (Val.nil : Val) + vsz (Val.int (S : ℤ)) + 1)
        (d := 12) (e := 1) (c := 12) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := vsz (Val.nil : Val) + vsz (Val.int (S : ℤ)) + 1) (d := 12)
        (by omega)
  -- phase 8: `pRep .nil`
  have h8 : WordR main (L.pRep Val.nil)
      (fun vs => vs = Val.int (S : ℤ) :: Val.nil :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => out = ofList (List.replicate S Val.nil) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => 10 * CU L ss S xs) := by
    refine WordR.conseqK (L.hRep main S Val.nil) L.hK ?_ ?_ ?_
    · intro vs hvs; exact ⟨intList (sigmaList ss) :: ofList xs :: rest, hvs⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨r, hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs _
      have heq : L.KRep * ((S + 1) * (vsz Val.nil + 1) + isz (S : ℤ) + 1)
          = L.KRep * (2 * S + S.size + 5) := by
        rw [vsz_nil_eq, isz_natCast, iszN]; ring
      rw [heq]
      refine mul_le_CU' L (k := L.KRep) (m := 2 * S + S.size + 5) (d := 8) (e := 1) (c := 10)
        (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := 2 * S + S.size + 5) (d := 8) (by
        have h1 : S ≤ PB ss S xs := S_le_PB (ss := ss) (S := S) (xs := xs) hxs
        have h2 : S.size ≤ PB ss S xs := size_le_PB (ss := ss) (S := S) (xs := xs) hxs
        omega)
  -- phase 9: `pEnum`
  have h9 : WordR main L.pEnum
      (fun vs => vs = ofList (List.replicate S Val.nil) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => out = ofList (recLab S) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => 10 * CU L ss S xs) := by
    refine WordR.conseqK (L.hEnum main (List.replicate S Val.nil)) L.hK ?_ ?_ ?_
    · intro vs hvs; exact ⟨intList (sigmaList ss) :: ofList xs :: rest, hvs⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨r, hab, hout⟩ := hq
      cases hab
      rw [hout, enumList_eq_recLab]
    · intro vs _
      rw [List.length_replicate]
      refine mul_le_CU' L (k := L.KEnum)
        (m := vsz (ofList (List.replicate S Val.nil)) + S * (S.size + 1) + 1)
        (d := 5) (e := 1) (c := 10) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      rw [vsz_nilRep]
      have h2 : S * (S.size + 1) ≤ PB ss S xs * QB S := by
        rw [QB]
        exact Nat.mul_le_mul (S_le_PB (ss := ss) (S := S) (xs := xs) hxs) le_rfl
      have h5 : 2 * S + 2 ≤ 4 * (PB ss S xs * QB S) := by
        have h1 : S ≤ PB ss S xs := S_le_PB (ss := ss) (S := S) (xs := xs) hxs
        have h3 : PB ss S xs ≤ PB ss S xs * QB S := le_PB_mul_QB ss S xs
        have h4 : 1 ≤ PB ss S xs * QB S := one_le_PB_mul_QB ss S xs
        omega
      omega
  -- phase 10: `pMap qMap`
  have h10 : WordR main (L.pMap qMap)
      (fun vs => vs = ofList (recLab S) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => out = ofList (labVals (List.range S)) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => 30 * CU L ss S xs) := by
    have hmem : ∀ x ∈ recLab S,
        (∃ i : ℕ, x = Val.cons (.int (i : ℤ)) Val.nil ∧ iszN i ≤ S.size + 4) ∧
          vsz x ≤ S.size + 4 := by
      intro x hx
      obtain ⟨j, hjS, hxj⟩ := recLab_mem hx
      subst hxj
      refine ⟨⟨j, rfl, ?_⟩, ?_⟩
      · have hb := Nat.size_le_size (Nat.le_of_lt hjS)
        simp only [iszN]; omega
      · rw [vsz_cons, vsz_intNat, vsz_nil_eq]
        have hb := Nat.size_le_size (Nat.le_of_lt hjS)
        simp only [iszN]; omega
    have hstep : ∀ x, (∃ i : ℕ, x = Val.cons (.int (i : ℤ)) Val.nil ∧ iszN i ≤ S.size + 4) →
        WordR main qMap
          (fun vs => vs = x :: (intList (sigmaList ss) :: ofList xs :: rest))
          (fun _ out => ∃ y, out = y :: (intList (sigmaList ss) :: ofList xs :: rest) ∧
            (∃ i : ℕ, x = Val.cons (.int (i : ℤ)) Val.nil ∧ y = Val.int (i : ℤ)) ∧ vsz y ≤ S.size + 4)
          (fun _ => L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)) := by
      intro x hx
      obtain ⟨i, rfl, hi⟩ := hx
      refine WordR.conseqK
        (hqMap main (intList (sigmaList ss) :: ofList xs :: rest) i (S.size + 4) hi) L.hK
        (fun _ h => h) ?_ (fun _ _ => le_rfl)
      intro vs out hvs hq
      exact ⟨Val.int (i : ℤ), hq, ⟨i, rfl, rfl⟩, by rw [vsz_intNat]; exact hi⟩
    have hres := L.hMap main qMap (intList (sigmaList ss) :: ofList xs :: rest)
      (fun x => ∃ i : ℕ, x = Val.cons (.int (i : ℤ)) Val.nil ∧ iszN i ≤ S.size + 4)
      (fun x y => ∃ i : ℕ, x = Val.cons (.int (i : ℤ)) Val.nil ∧ y = Val.int (i : ℤ))
      (L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)) (S.size + 4)
      hstep (recLab S) hmem
    refine WordR.conseqK hres L.hK (fun _ h => h) ?_ ?_
    · intro vs out hvs hq
      obtain ⟨ys, hout, hfor⟩ := hq
      rw [hout, crtB1_forall2_eq (S := S) rfl hfor]
    · intro vs _
      rw [recLab_length]
      have hc : L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)
          ≤ KF L * (2 * S.size + 13) := by
        have h1 : L.KUnc ≤ KF L := KF_ge L (by simp [kList])
        have h2 : L.KSwap * (S.size + 4 + 2) ≤ KF L * (S.size + 4 + 2) :=
          Nat.mul_le_mul_right _ (KF_ge L (by simp [kList]))
        have h3 : L.KDrop * (S.size + 4 + 2) ≤ KF L * (S.size + 4 + 2) :=
          Nat.mul_le_mul_right _ (KF_ge L (by simp [kList]))
        calc L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)
            ≤ KF L + KF L * (S.size + 4 + 2) + KF L * (S.size + 4 + 2) :=
              Nat.add_le_add (Nat.add_le_add h1 h2) h3
          _ = KF L * (2 * S.size + 13) := by ring
      have hsum : L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)
            + L.KMap * (S.size + 4 + 1) ≤ KF L * (3 * S.size + 18) := by
        have h4 : L.KMap * (S.size + 4 + 1) ≤ KF L * (S.size + 4 + 1) :=
          Nat.mul_le_mul_right _ (KF_ge L (by simp [kList]))
        calc L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)
              + L.KMap * (S.size + 4 + 1)
            ≤ KF L * (2 * S.size + 13) + KF L * (S.size + 4 + 1) := Nat.add_le_add hc h4
          _ = KF L * (3 * S.size + 18) := by ring
      have hKM : L.KMap ≤ KF L := KF_ge L (by simp [kList])
      calc S * (L.KUnc + L.KSwap * (S.size + 4 + 2) + L.KDrop * (S.size + 4 + 2)
              + L.KMap * (S.size + 4 + 1)) + L.KMap
          ≤ S * (KF L * (3 * S.size + 18)) + KF L :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hsum) hKM
        _ = KF L * (S * (3 * S.size + 18) + 1) := by ring
        _ ≤ KF L * (22 * (PB ss S xs * QB S)) := by
              refine Nat.mul_le_mul_left (KF L) ?_
              have h1 : S ≤ PB ss S xs := S_le_PB (ss := ss) (S := S) (xs := xs) hxs
              have h2 : 3 * S.size + 18 ≤ 21 * QB S := by rw [QB]; omega
              have h3 : S * (3 * S.size + 18) ≤ PB ss S xs * (21 * QB S) := Nat.mul_le_mul h1 h2
              have h4 : S * (3 * S.size + 18) ≤ 21 * (PB ss S xs * QB S) := by
                calc S * (3 * S.size + 18) ≤ PB ss S xs * (21 * QB S) := h3
                  _ = 21 * (PB ss S xs * QB S) := by ring
              have h5 : 1 ≤ PB ss S xs * QB S := one_le_PB_mul_QB ss S xs
              omega
        _ = 22 * CU L ss S xs := by rw [CU, SB]; ring
        _ ≤ 30 * CU L ss S xs := by omega
  -- phase 11: `pJoin`
  have h11 : WordR main L.pJoin
      (fun vs => vs = ofList (labVals (List.range S)) :: intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => out = ofList (crtZ ss S) :: ofList xs :: rest)
      (fun _ => 20 * CU L ss S xs) := by
    have hlen : (labVals (List.range S)).length = (labVals (sigmaList ss)).length := by
      rw [labVals_range_length, labVals_sigmaList_length ss S hS]
    have hltR : ∀ i < S, (List.range S).getD i 0 < S := fun i hi => by
      rw [getD_range_self hi]; exact hi
    refine WordR.conseqK
      (L.hJoin main (labVals (List.range S)) (labVals (sigmaList ss)) hlen) L.hK ?_ ?_ ?_
    · intro vs hvs
      refine ⟨ofList xs :: rest, ?_⟩
      rw [hvs, intList_eq_ofList]
    · intro vs out hvs hq
      obtain ⟨r, hvsB, hout⟩ := hq
      rw [hvs] at hvsB
      rw [intList_eq_ofList (sigmaList ss)] at hvsB
      have hr : ofList xs :: rest = r := (List.cons.inj (List.cons.inj hvsB).2).2
      rw [← hr] at hout
      exact hout
    · intro vs _
      have hV1 : vsz (ofList (labVals (List.range S))) ≤ 5 * PB ss S xs :=
        Vlab_le_PB (ss := ss) (S := S) (xs := xs) (lab := List.range S) hpos hS
          List.length_range hltR
      have hV2 : vsz (ofList (labVals (sigmaList ss))) ≤ 5 * PB ss S xs :=
        Vlab_le_PB (ss := ss) (S := S) (xs := xs) (lab := sigmaList ss) hpos hS hlab hlt
      refine mul_le_CU' L (k := L.KJoin)
        (m := vsz (ofList (labVals (List.range S))) + vsz (ofList (labVals (sigmaList ss))) + 1)
        (d := 11) (e := 1) (c := 20) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB
        (m := vsz (ofList (labVals (List.range S))) + vsz (ofList (labVals (sigmaList ss))) + 1)
        (d := 11) (by omega)
  -- phases 12/13: `pSort` and `pStrip`
  have hZlen : (crtZ ss S).length = S := crtZ_length hS
  have hZget : ∀ (i : ℕ) (_ : i < (crtZ ss S).length),
      (crtZ ss S)[i] = Val.cons (Val.int ((sigmaList ss).getD i 0 : ℤ)) (Val.int (i : ℤ)) := by
    intro i hi
    have hiS : i < S := by rw [hZlen] at hi; exact hi
    rw [← List.getD_eq_getElem (crtZ ss S) Val.nil hi, crtZ_getD hS hiS]
  have hrec : ∀ x ∈ crtZ ss S, ∃ (k : ℕ) (v : Val), x = Val.cons (.int (k : ℤ)) v := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    exact ⟨_, _, by rw [← hix, hZget i hi]⟩
  have hrecZ : ∀ x ∈ crtZ ss S, ∃ (k : ℤ) (v : Val), x = Val.cons (.int k) v := by
    intro x hx
    obtain ⟨k, v, hv⟩ := hrec x hx
    exact ⟨(k : ℤ), v, hv⟩
  have hnodup : ((crtZ ss S).map pairKey).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_map] at hi hj
    intro hk
    rw [List.getElem_map, List.getElem_map, hZget i hi, hZget j hj,
      pairKey_cons, pairKey_cons] at hk
    have hiS : i < S := by rw [hZlen] at hi; exact hi
    have hjS : j < S := by rw [hZlen] at hj; exact hj
    exact Nat.ne_of_lt hij
      (sigmaList_inj hcop hpos0 (lt_prod_of_lt_S hS hiS) (lt_prod_of_lt_S hS hjS)
        (Int.ofNat.inj hk))
  have hZle : vsz (ofList (crtZ ss S)) ≤ 12 * PB ss S xs := by
    have h1 : vsz (ofList (crtZ ss S))
        ≤ vsz (ofList (labVals (List.range S))) + vsz (ofList (labVals (sigmaList ss))) + S := by
      rw [crtZ]
      exact vsz_zipRec_le (xs := labVals (List.range S)) (ws := labVals (sigmaList ss)) (S := S)
        (labVals_range_length S) (labVals_sigmaList_length ss S hS)
    have h2 : vsz (ofList (labVals (List.range S))) ≤ 5 * PB ss S xs :=
      Vlab_le_PB (ss := ss) (S := S) (xs := xs) (lab := List.range S) hpos hS
        List.length_range (fun i hi => by rw [getD_range_self hi]; exact hi)
    have h3 : vsz (ofList (labVals (sigmaList ss))) ≤ 5 * PB ss S xs :=
      Vlab_le_PB (ss := ss) (S := S) (xs := xs) (lab := sigmaList ss) hpos hS hlab hlt
    have h4 : S ≤ PB ss S xs := S_le_PB (ss := ss) (S := S) (xs := xs) hxs
    omega
  have hSort : WordR main L.pSort
      (fun vs => vs = ofList (crtZ ss S) :: ofList xs :: rest)
      (fun _ out => ∃ rs', out = ofList rs' :: ofList xs :: rest ∧ rs'.Perm (crtZ ss S) ∧
        rs'.Pairwise (fun a b => pairKey a < pairKey b))
      (fun _ => 30 * CU L ss S xs) := by
    refine WordR.conseqK (L.hSort main (crtZ ss S) hrec hnodup) L.hK ?_ ?_ ?_
    · intro vs hvs; exact ⟨ofList xs :: rest, hvs⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨r, ys, hab, hout, hperm, hsorted⟩ := hq
      cases hab
      exact ⟨ys, hout, hperm, hsorted⟩
    · intro vs _
      have h1 : vsz (ofList (crtZ ss S)) + 1 ≤ 13 * PB ss S xs := by omega
      have h2 : (crtZ ss S).length.size + 1 = QB S := by rw [hZlen, QB]
      calc L.KSort * (vsz (ofList (crtZ ss S)) + 1) * ((crtZ ss S).length.size + 1)
          ≤ L.KSort * (13 * PB ss S xs) * QB S := by
            rw [h2]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = (13 * L.KSort) * (PB ss S xs * QB S) := by ring
        _ ≤ (13 * KF L) * (PB ss S xs * QB S) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 13 (KF_ge L (by simp [kList])))
        _ = 13 * CU L ss S xs := by rw [CU, SB]; ring
        _ ≤ 30 * CU L ss S xs := by omega
  have hStrip : WordR main L.pStrip
      (fun vs => ∃ rs, vs = ofList rs :: ofList xs :: rest ∧ rs.Perm (crtZ ss S))
      (fun vs out => ∃ rs ys, vs = ofList rs :: ofList xs :: rest ∧ rs.Perm (crtZ ss S) ∧
        out = ofList ys :: ofList xs :: rest ∧ ys = rs.map recPayload)
      (fun _ => 15 * CU L ss S xs) := by
    refine WordR.conseqK
      (stripPerm L.hK L.hStrip main (crtZ ss S) (ofList xs :: rest) hrecZ) L.hK
      (fun _ h => h) (fun _ _ _ h => h) ?_
    · intro vs _
      have h1 : vsz (ofList (crtZ ss S)) + 1 ≤ 13 * PB ss S xs := by omega
      refine mul_le_CU' L (k := L.KStrip) (m := vsz (ofList (crtZ ss S)) + 1) (d := 13) (e := 1)
        (c := 15) (by simpa using KF_ge L (by simp [kList])) ?_ (by omega)
      exact le_mul_QB_of_le_PB (m := vsz (ofList (crtZ ss S)) + 1) (d := 13) (by omega)
  have hSS : WordR main (.seq L.pSort L.pStrip)
      (fun vs => vs = ofList (crtZ ss S) :: ofList xs :: rest)
      (fun _ out => out = ofList (labVals (crtQ ss)) :: ofList xs :: rest)
      (fun _ => 45 * CU L ss S xs) := by
    refine WordR.conseqK
      (WordR.seqK hSort hStrip L.hK (B := fun _ => 15 * CU L ss S xs)
        (fun vs mid _ hq => ⟨by
          obtain ⟨rs', hmid, hperm, _⟩ := hq
          exact ⟨rs', hmid, hperm⟩, le_rfl⟩))
      L.hK (fun _ h => h) ?_ (fun _ _ => by omega)
    intro vs out _ hq
    obtain ⟨mid, ⟨rs', hmid1, hperm, hsorted⟩, rs, ys, hmid2, _hperm2, hout, hys⟩ := hq
    rw [hmid1] at hmid2
    have hrs : rs' = rs := ofList_inj (List.cons.inj hmid2).1
    rw [← hrs] at hys
    rw [hout, hys, crtB1SortStripAux L hpos hS hcop hperm hsorted]
  -- assembling the chain
  have hA1 := seqEqK h1 h2 L.hK
  have hA2 := seqEqK hA1 h3 L.hK
  have hA3 := seqEqK hA2 h4 L.hK
  have hA4 := seqEqK hA3 h5 L.hK
  have hA5 := seqEqK hA4 h6 L.hK
  have hA6 := seqEqK hA5 h7 L.hK
  have hA7 := seqEqK hA6 h8 L.hK
  have hA8 := seqEqK hA7 h9 L.hK
  have hA9 := seqEqK hA8 h10 L.hK
  have hA10 := seqEqK hA9 h11 L.hK
  have hAll := seqEqK hA10 hSS L.hK
  refine WordR.conseqK hAll L.hK (fun vs hvs => hvs) (fun vs out _ hq => hq) (fun vs _ => ?_)
  omega

/-- **The `dir = 1` branch**: reindex `xs` by the inverse CRT reindexing. -/
theorem crtBranch1 (L : Work.MainP.CrtLib) :
    ∃ (prog : HvdH.Cmd) (C : ℕ),
      ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ) (xs : List HvdH.Val) (rest : List HvdH.Val),
        (∀ s ∈ ss, 1 ≤ s) → S = ss.prod → ss.Pairwise Nat.Coprime → xs.length = S →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: HvdH.ofList xs :: rest)
          (fun _ out => ∃ ys, out = HvdH.ofList ys :: rest ∧ ys.length = S ∧
            ∀ m < S, ys.getD m HvdH.Val.nil
              = xs.getD (Work.MainP.invLab (Work.MainP.crtQ ss) m) HvdH.Val.nil)
          (fun _ => C * Work.MainP.CU L ss S xs) := by
  obtain ⟨pHead, CHead, hHead⟩ := crtBranch1Head L
  obtain ⟨pTail, hTail⟩ := tailWord L
  refine ⟨.seq pHead pTail, CHead + 100, ?_⟩
  intro main ss S xs rest hpos hS hcop hxs
  have hpos0 : ∀ s ∈ ss, 0 < s := fun s hs => by have := hpos s hs; omega
  have hQlab : (crtQ ss).length = S := by rw [hS]; exact crtQ_length ss
  have hinj : ∀ i < S, ∀ j < S, (crtQ ss).getD i 0 = (crtQ ss).getD j 0 → i = j :=
    fun i hi j hj h => crtQ_inj hcop hpos0 (lt_prod_of_lt_S hS hi) (lt_prod_of_lt_S hS hj) h
  have hltQ : ∀ i < S, (crtQ ss).getD i 0 < S :=
    fun i hi => lt_S_of_lt_prod hS (crtQ_lt hcop hpos0 (lt_prod_of_lt_S hS hi))
  have hh := hHead main ss S xs rest hpos hS hcop hxs
  have ht := hTail ss (crtQ ss) S xs rest hpos hS hxs hQlab hinj hltQ main
  have hcomp := WordR.seqK hh ht L.hK (B := fun _ => BUD L ss S xs)
    (fun vs mid _ hq => ⟨hq, le_rfl⟩)
  refine WordR.conseqK hcomp L.hK (fun vs hvs => hvs) ?_ ?_
  · intro vs out _ hq
    obtain ⟨mid, hmid, ys, hout, hlen, hget⟩ := hq
    exact ⟨ys, hout, hlen, hget⟩
  · intro vs _
    rw [BUD_eq, CU]
    exact le_of_eq (by ring)

end Work.MainP
