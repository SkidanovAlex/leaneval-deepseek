import Mathlib
import Submission.Work.MainP.crtLib

/-!
# `crtTail`: the label-and-sort tail of the CRT reindexing

From `ofList (labVals lab) :: ofList xs :: rest` (with `lab.length = xs.length = S`, `lab` injective
with values `< S`) the word

`swap; join; sortByKey; strip`

produces `ofList ys :: rest` where `ys[m] = xs[invLab lab m]` for `m < S`, at cost bounded by
`BUD L ss S xs = 100 * (KF L * SB ss S xs)`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-- The cost of the tail word, as the sum of its four library phases. -/
def tailCost (L : CrtLib) (lab : List ℕ) (xs : List Val) : ℕ :=
  L.KSwap * (vsz (ofList (labVals lab)) + vsz (ofList xs) + 1)
  + (L.KJoin * (vsz (ofList xs) + vsz (ofList (labVals lab)) + 1)
  + (L.KSort * (vsz (ofList (zipRec xs (labVals lab))) + 1)
      * ((zipRec xs (labVals lab)).length.size + 1)
  + L.KStrip * (vsz (ofList (zipRec xs (labVals lab))) + 1)))

theorem tailCost_le (L : CrtLib) {ss : List ℕ} {S : ℕ} {xs : List Val} {lab : List ℕ}
    (hpos : ∀ s ∈ ss, 1 ≤ s) (hS : S = ss.prod) (hxs : xs.length = S)
    (hlab : lab.length = S) (hlt : ∀ i < S, lab.getD i 0 < S) :
    tailCost L lab xs ≤ BUD L ss S xs := by
  have hV : vsz (ofList xs) ≤ PB ss S xs := V_le_PB ss S xs
  have hVl : vsz (ofList (labVals lab)) ≤ 5 * PB ss S xs := Vlab_le_PB hpos hS hlab hlt
  have hVz : vsz (ofList (zipRec xs (labVals lab))) ≤ 10 * PB ss S xs :=
    Vzip_le_PB hpos hS hxs hlab hlt
  have hQ : (zipRec xs (labVals lab)).length.size + 1 = QB S := zipRec_size_eq hxs hlab
  have hQ1 : 1 ≤ QB S := one_le_QB S
  have hSw : L.KSwap ≤ KF L := KF_ge L (by simp [kList])
  have hJn : L.KJoin ≤ KF L := KF_ge L (by simp [kList])
  have hSr : L.KSort ≤ KF L := KF_ge L (by simp [kList])
  have hSt : L.KStrip ≤ KF L := KF_ge L (by simp [kList])
  have hPQ : PB ss S xs ≤ PB ss S xs * QB S := by
    calc PB ss S xs = PB ss S xs * 1 := (Nat.mul_one _).symm
      _ ≤ PB ss S xs * QB S := Nat.mul_le_mul_left _ hQ1
  set B : ℕ := KF L * SB ss S xs with hB
  have t1 : L.KSwap * (vsz (ofList (labVals lab)) + vsz (ofList xs) + 1) ≤ 11 * B := by
    have hb1 : 1 ≤ PB ss S xs := one_le_PB ss S xs
    have hA : vsz (ofList (labVals lab)) + vsz (ofList xs) + 1 ≤ 7 * PB ss S xs := by omega
    have hc : 7 * L.KSwap ≤ 11 * KF L := by omega
    calc L.KSwap * (vsz (ofList (labVals lab)) + vsz (ofList xs) + 1)
        ≤ L.KSwap * (7 * PB ss S xs) := Nat.mul_le_mul_left _ hA
      _ = (7 * L.KSwap) * PB ss S xs := by ring
      _ ≤ (11 * KF L) * (PB ss S xs * QB S) := Nat.mul_le_mul hc hPQ
      _ = 11 * B := by rw [hB, SB]; ring
  have t2 : L.KJoin * (vsz (ofList xs) + vsz (ofList (labVals lab)) + 1) ≤ 11 * B := by
    have hb1 : 1 ≤ PB ss S xs := one_le_PB ss S xs
    have hA : vsz (ofList xs) + vsz (ofList (labVals lab)) + 1 ≤ 7 * PB ss S xs := by omega
    have hc : 7 * L.KJoin ≤ 11 * KF L := by omega
    calc L.KJoin * (vsz (ofList xs) + vsz (ofList (labVals lab)) + 1)
        ≤ L.KJoin * (7 * PB ss S xs) := Nat.mul_le_mul_left _ hA
      _ = (7 * L.KJoin) * PB ss S xs := by ring
      _ ≤ (11 * KF L) * (PB ss S xs * QB S) := Nat.mul_le_mul hc hPQ
      _ = 11 * B := by rw [hB, SB]; ring
  have t3 : L.KSort * (vsz (ofList (zipRec xs (labVals lab))) + 1)
      * ((zipRec xs (labVals lab)).length.size + 1) ≤ 11 * B := by
    have hb1 : 1 ≤ PB ss S xs := one_le_PB ss S xs
    have hA : vsz (ofList (zipRec xs (labVals lab))) + 1 ≤ 11 * PB ss S xs := by omega
    have hc : 11 * L.KSort ≤ 11 * KF L := by omega
    rw [hQ]
    calc L.KSort * (vsz (ofList (zipRec xs (labVals lab))) + 1) * QB S
        ≤ L.KSort * (11 * PB ss S xs) * QB S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA)
      _ = (11 * L.KSort) * (PB ss S xs * QB S) := by ring
      _ ≤ (11 * KF L) * (PB ss S xs * QB S) := Nat.mul_le_mul_right _ hc
      _ = 11 * B := by rw [hB, SB]; ring
  have t4 : L.KStrip * (vsz (ofList (zipRec xs (labVals lab))) + 1) ≤ 11 * B := by
    have hb1 : 1 ≤ PB ss S xs := one_le_PB ss S xs
    have hA : vsz (ofList (zipRec xs (labVals lab))) + 1 ≤ 11 * PB ss S xs := by omega
    have hc : 11 * L.KStrip ≤ 11 * KF L := by omega
    calc L.KStrip * (vsz (ofList (zipRec xs (labVals lab))) + 1)
        ≤ L.KStrip * (11 * PB ss S xs) := Nat.mul_le_mul_left _ hA
      _ = (11 * L.KStrip) * PB ss S xs := by ring
      _ ≤ (11 * KF L) * (PB ss S xs * QB S) := Nat.mul_le_mul hc hPQ
      _ = 11 * B := by rw [hB, SB]; ring
  rw [tailCost, BUD_eq, ← hB]
  omega

/-- The tail word: label-and-sort with the label list as a parameter. -/
theorem tailWord (L : CrtLib) :
    ∃ (prog : Cmd), ∀ (ss : List ℕ) (lab : List ℕ) (S : ℕ) (xs : List Val) (rest : List Val),
      (∀ s ∈ ss, 1 ≤ s) → S = ss.prod → xs.length = S → lab.length = S →
      (∀ i < S, ∀ j < S, lab.getD i 0 = lab.getD j 0 → i = j) →
      (∀ i < S, lab.getD i 0 < S) →
      ∀ main, WordR main prog
        (fun vs => vs = ofList (labVals lab) :: ofList xs :: rest)
        (fun _ out => ∃ ys, out = ofList ys :: rest ∧ ys.length = S ∧
          ∀ m < S, ys.getD m .nil = xs.getD (invLab lab m) .nil)
        (fun _ => BUD L ss S xs) := by
  refine ⟨.seq L.pSwap (.seq L.pJoin (.seq L.pSort L.pStrip)), ?_⟩
  intro ss lab S xs rest hpos hS hxs hlab hinj hlt main
  have hT := tailCost_le L hpos hS hxs hlab hlt
  have hws_len : (labVals lab).length = S := by simp [labVals, hlab]
  have hxs_len : xs.length = (labVals lab).length := by rw [hws_len]; exact hxs
  have hrec_len_aux : (zipRec xs (labVals lab)).length = S := by
    rw [zipRec_length hxs_len, hxs]
  have hrec_eq : ∀ (i : ℕ) (_ : i < (zipRec xs (labVals lab)).length),
      (zipRec xs (labVals lab))[i] = .cons (.int ((lab.getD i 0 : ℕ) : ℤ)) (xs.getD i .nil) := by
    intro i hi
    have hiS : i < S := by rw [hrec_len_aux] at hi; exact hi
    have his : i < xs.length := by omega
    have hil : i < lab.length := by rw [hlab]; exact hiS
    rw [← List.getD_eq_getElem _ _ hi, zipRec_getD hxs_len his, labVals_getD hil]
  have hrec_prop : ∀ x ∈ zipRec xs (labVals lab),
      ∃ (k : ℕ) (v : Val), x = .cons (.int (k : ℤ)) v := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    rw [← hix, hrec_eq i hi]
    exact ⟨_, _, rfl⟩
  have hrec_propZ : ∀ x ∈ zipRec xs (labVals lab),
      ∃ (k : ℤ) (v : Val), x = .cons (.int k) v :=
    fun x hx => let ⟨k, v, h⟩ := hrec_prop x hx; ⟨(k : ℤ), v, h⟩
  have hrec_nodup : ((zipRec xs (labVals lab)).map pairKey).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_map] at hi hj
    have his : i < S := by rw [hrec_len_aux] at hi; exact hi
    have hjs : j < S := by rw [hrec_len_aux] at hj; exact hj
    intro hk
    rw [List.getElem_map, List.getElem_map,
      hrec_eq i (by rw [hrec_len_aux]; exact his), hrec_eq j (by rw [hrec_len_aux]; exact hjs),
      pairKey_cons, pairKey_cons] at hk
    exact Nat.ne_of_lt hij (hinj i his j hjs (Int.ofNat.inj hk))
  have hSwapX : WordR main L.pSwap (fun vs => vs = ofList (labVals lab) :: ofList xs :: rest)
      (fun _ out => out = ofList xs :: ofList (labVals lab) :: rest)
      (fun _ => L.KSwap * (vsz (ofList (labVals lab)) + vsz (ofList xs) + 1)) := by
    refine WordR.conseqK (L.hSwap main) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨a', b', r', hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact le_rfl
  have hJoinX : WordR main L.pJoin (fun vs => vs = ofList xs :: ofList (labVals lab) :: rest)
      (fun _ out => out = ofList (zipRec xs (labVals lab)) :: rest)
      (fun _ => L.KJoin * (vsz (ofList xs) + vsz (ofList (labVals lab)) + 1)) := by
    refine WordR.conseqK (L.hJoin main xs (labVals lab) hxs_len) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; exact ⟨rest, rfl⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨r', hab, hout⟩ := hq
      cases hab
      exact hout
    · intro vs hvs; exact le_rfl
  have hSortX : WordR main L.pSort (fun vs => vs = ofList (zipRec xs (labVals lab)) :: rest)
      (fun _ out => ∃ rs', out = ofList rs' :: rest ∧ rs'.Perm (zipRec xs (labVals lab)) ∧
        rs'.Pairwise (fun a b => pairKey a < pairKey b))
      (fun _ => L.KSort * (vsz (ofList (zipRec xs (labVals lab))) + 1)
        * ((zipRec xs (labVals lab)).length.size + 1)) := by
    refine WordR.conseqK (L.hSort main (zipRec xs (labVals lab)) hrec_prop hrec_nodup) L.hK ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; exact ⟨rest, rfl⟩
    · intro vs out hvs hq
      rw [hvs] at hq
      obtain ⟨r', rs', hab, hout, hperm, hsorted⟩ := hq
      cases hab
      exact ⟨rs', hout, hperm, hsorted⟩
    · intro vs hvs; exact le_rfl
  have hSS := by
    refine WordR.seqK hSortX
      (stripPerm L.hK L.hStrip main (zipRec xs (labVals lab)) rest hrec_propZ) L.hK
      (B := fun _ => L.KStrip * (vsz (ofList (zipRec xs (labVals lab))) + 1)) ?_
    intro vs mid hvs hq
    obtain ⟨rs', hmid, hperm, hsorted⟩ := hq
    exact ⟨⟨rs', hmid, hperm⟩, le_rfl⟩
  have hJSS := by
    refine WordR.seqK hJoinX hSS L.hK
      (B := fun _ => (L.KSort * (vsz (ofList (zipRec xs (labVals lab))) + 1)
        * ((zipRec xs (labVals lab)).length.size + 1)
        + L.KStrip * (vsz (ofList (zipRec xs (labVals lab))) + 1))) ?_
    intro vs mid hvs hq
    exact ⟨hq, le_rfl⟩
  have hAll := by
    refine WordR.seqK hSwapX hJSS L.hK
      (B := fun _ => (L.KJoin * (vsz (ofList xs) + vsz (ofList (labVals lab)) + 1)
        + (L.KSort * (vsz (ofList (zipRec xs (labVals lab))) + 1)
            * ((zipRec xs (labVals lab)).length.size + 1)
        + L.KStrip * (vsz (ofList (zipRec xs (labVals lab))) + 1)))) ?_
    intro vs mid hvs hq
    exact ⟨hq, le_rfl⟩
  refine WordR.conseqK hAll L.hK (fun vs h => h) (fun vs out h hq => ?_)
    (fun vs _ => hT)
  obtain ⟨m1, hm1, hrest⟩ := hq
  obtain ⟨m2, hm2, hrest2⟩ := hrest
  obtain ⟨m3, hsrt, hfin⟩ := hrest2
  obtain ⟨rs', hm3a, hperm, hsort⟩ := hsrt
  obtain ⟨rs, ys, hm3b, hperm2, hout, hyseq⟩ := hfin
  have hrs : rs' = rs := by
    rw [hm3a] at hm3b
    have h1 : ofList rs' = ofList rs := by injection hm3b
    exact ofList_inj h1
  subst hrs
  refine ⟨ys, hout, ?_, ?_⟩
  · rw [hyseq, List.length_map]
    exact hperm.length_eq.trans (by rw [zipRec_length (by rw [hws_len, hxs]), hxs])
  · intro m hm
    rw [hyseq]
    exact L.hSorted hxs hlab hinj hlt hperm hsort m hm

end Work.MainP
