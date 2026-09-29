import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.KronP.defs
import Submission.Work.KronP.math
import Submission.Work.KronP.specs
import Submission.Work.KronP.setup
import Submission.Work.KronP.splitPack
import Submission.Work.KronP.prodDigits
import Submission.Work.KronP.prodOffset
import Submission.Work.KronP.combine
import Submission.Work.KronP.kronFinal

/-!
# The Kronecker word (paper Lemma 2.5) — assembly

This file assembles `Work.ConvR.KroneckerSpec` from the pieces of `Submission/Work/KronP/`:

* the four program pieces `SetupSpec`, `SplitPackSpec`, `ProdDigitsSpec`, `CombineSpec`,
* the arithmetic fact `ProdOffsetSpec` (which makes `HvdH.IntLib.chunk` applicable),
* the mathematics `KronFinalSpec` (paper Lemma 2.5).

`zipFour` glues `KernelLib.zipWith` and `ProdDigitsSpec` into the four packed products;
`kronAssembly` chains the four programs and the final mathematics.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KronP

open HvdH

/-! ## Generic lemmas about `WordR` -/

/-- A `WordR` whose precondition is an existential can be packaged. -/
theorem WordR_ex_pre {main prog : Cmd} {α : Type*} {P : α → List Val → Prop}
    {Q : α → List Val → Prop} {C : ℕ}
    (h : ∀ a, WordR main prog (P a) (fun _ out => Q a out) (fun _ => C)) :
    WordR main prog (fun vs => ∃ a, P a vs) (fun _ out => ∃ a, Q a out) (fun _ => C) := by
  intro vs hvs s R hs
  obtain ⟨a, ha⟩ := hvs
  obtain ⟨out, s', n, hQ, hev, hn, hstk, hoth⟩ := h a vs ha s R hs
  exact ⟨out, s', n, ⟨a, hQ⟩, hev, hn, hstk, hoth⟩

/-- Two lists with equal length and equal `getD` entries are equal. -/
theorem list_eq_of_getD {l₁ l₂ : List Val} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i .nil = l₂.getD i .nil) : l₁ = l₂ := by
  apply List.ext_getElem
  · exact hlen
  · intro i h1 h2
    have h3 := h i h1
    rw [List.getD_eq_getElem _ _ h1] at h3
    rw [List.getD_eq_getElem _ _ h2] at h3
    exact h3

/-! ## Aliases and small conversions -/

theorem vsz_int (z : ℤ) : vsz (.int z) = isz z := Work.ConvR.vsz_int z

theorem natAbs_fst_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.1.natAbs ≤ 2 ^ p :=
  Work.ConvR.natAbs_fst_le_of_inDisc h

theorem natAbs_snd_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.2.natAbs ≤ 2 ^ p :=
  Work.ConvR.natAbs_snd_le_of_inDisc h

theorem int_three_mul (p : ℕ) : ((3 * p : ℕ) : ℤ) = 3 * (p : ℤ) := by push_cast; ring

theorem int_two_mul (r : ℕ) : ((2 * r : ℕ) : ℤ) = 2 * (r : ℤ) := by push_cast; ring

/-! ## Small facts about `chunks`, `intList` and sizes -/

theorem chunks_length (x b N : ℕ) : (chunks x b N).length = N := by
  simp [chunks]

theorem mem_chunks_lt (x b N : ℕ) : ∀ n ∈ chunks x b N, n < 2 ^ b := by
  intro n hn
  rw [chunks] at hn
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
  rw [List.mem_range] at hm
  exact Nat.mod_lt _ (Nat.pow_pos (by norm_num : (0 : ℕ) < 2))

theorem vsz_intList_le {A : List ℕ} {b : ℕ} (h : ∀ n ∈ A, n < 2 ^ b) :
    vsz (intList A) ≤ A.length * (b + 3) + A.length + 2 := by
  have h1 := Work.ConvR.vsz_intList_le A
  have h2 : (A.map fun t => t.size + 3).sum ≤ A.length * (b + 3) := by
    calc (A.map fun t => t.size + 3).sum ≤ (A.map fun _ => b + 3).sum :=
          List.sum_le_sum (fun t ht => by
            have ht2 : t.size ≤ b := Nat.size_le.mpr (h t ht)
            omega)
      _ = A.length * (b + 3) := Work.ConvR.sum_map_const A (b + 3)
  omega

theorem pack_size_le {l : List ℤ} {p r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hlen : l.length = r)
    (hb : ∀ x ∈ l, x.natAbs ≤ 2 ^ p) : (pack l (3 * p)).natAbs.size ≤ 3 * r * p := by
  have h := pack_natAbs_le l (3 * p) (2 ^ p) (by omega) hb
  rw [hlen] at h
  have h2 : (pack l (3 * p)).natAbs ≤ 2 ^ (3 * p * (r - 1) + p + 1) := by
    calc (pack l (3 * p)).natAbs ≤ 2 ^ p * 2 ^ (3 * p * (r - 1) + 1) := h
      _ = 2 ^ (3 * p * (r - 1) + p + 1) := by rw [← pow_add]; ring_nf
  have hsub : 3 * p * (r - 1) = 3 * p * r - 3 * p := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have h3pr : 3 * p ≤ 3 * p * r := by
    simpa using Nat.mul_le_mul_left (3 * p) hr
  have hlt : 3 * p * (r - 1) + p + 1 < 3 * r * p := by
    have h1 : 3 * p * (r - 1) + 3 * p = 3 * p * r := by
      rw [hsub, Nat.sub_add_cancel h3pr]
    have h2 : p + 1 < 3 * p := by omega
    have h3 : 3 * p * r = 3 * r * p := by ring
    omega
  have hfin : (pack l (3 * p)).natAbs < 2 ^ (3 * r * p) := by
    calc (pack l (3 * p)).natAbs ≤ 2 ^ (3 * p * (r - 1) + p + 1) := h2
      _ < 2 ^ (3 * r * p) := Nat.pow_lt_pow_right (by norm_num) hlt
  exact Nat.size_le.mpr hfin

/-- `r = 2 ^ (Nat.clog 2 r)` for a power of two `r`. -/
theorem clog_pow2 {r : ℕ} (hr : IsPow2 r) : r = 2 ^ (Nat.clog 2 r) := by
  obtain ⟨k, hk1, rfl⟩ := hr
  rw [Nat.clog_pow 2 k (by norm_num)]

/-- `vsz (.int X) ≤ digVSz p r` when `X` has at most `3rp` bits. -/
theorem vsz_int_le_digVSz {X : ℤ} {p r : ℕ} (hr : 1 ≤ r) (hX : X.natAbs.size ≤ 3 * r * p) :
    vsz (.int X) ≤ digVSz p r := by
  rw [vsz_int]
  simp only [isz, digVSz]
  nlinarith [hX, hr, Nat.zero_le p, Nat.zero_le r]

/-! ## The four packed products via `KernelLib.zipWith` -/

theorem zipFour (hK : KernelLib) (hzp : ProdDigitsSpec) (hpo : ProdOffsetSpec) : ZipFourSpec := by
  obtain ⟨zp, ZK, hzp'⟩ := hzp
  obtain ⟨zw, WK, hzw⟩ := hK.zipWith
  refine ⟨zw zp, 120 * ZK + 260 * WK + WK, ?_⟩
  intro main N Cm hmon hmul p r u v rest hp1 hr2 hrlt hu hv hN
  have hr1 : 1 ≤ r := by omega
  have hcX0 : (kronX0 u p).natAbs.size ≤ 3 * r * p := pack_size_le hp1 hr1 (by simp [hu.1]) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_fst_le_of_inDisc (hu.2 z hz))
  have hcX1 : (kronX1 u p).natAbs.size ≤ 3 * r * p := pack_size_le hp1 hr1 (by simp [hu.1]) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_snd_le_of_inDisc (hu.2 z hz))
  have hcY0 : (kronY0 v p).natAbs.size ≤ 3 * r * p := pack_size_le hp1 hr1 (by simp [hv.1]) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_fst_le_of_inDisc (hv.2 z hz))
  have hcY1 : (kronY1 v p).natAbs.size ≤ 3 * r * p := pack_size_le hp1 hr1 (by simp [hv.1]) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_snd_le_of_inDisc (hv.2 z hz))
  have hb1 : ∀ x ∈ u.map Prod.fst, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_fst_le_of_inDisc (hu.2 z hz)
  have hb1' : ∀ x ∈ u.map Prod.snd, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_snd_le_of_inDisc (hu.2 z hz)
  have hb2 : ∀ x ∈ v.map Prod.fst, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_fst_le_of_inDisc (hv.2 z hz)
  have hb2' : ∀ x ∈ v.map Prod.snd, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact natAbs_snd_le_of_inDisc (hv.2 z hz)
  have hlen1 : (u.map Prod.fst).length = r := by simp [hu.1]
  have hlen1' : (u.map Prod.snd).length = r := by simp [hu.1]
  have hlen2 : (v.map Prod.fst).length = r := by simp [hv.1]
  have hlen2' : (v.map Prod.snd).length = r := by simp [hv.1]
  have h00 := hpo p r hp1 hrlt (u.map Prod.fst) (v.map Prod.fst) hlen1 hlen2 hb1 hb2
  have h01 := hpo p r hp1 hrlt (u.map Prod.fst) (v.map Prod.snd) hlen1 hlen2' hb1 hb2'
  have h10 := hpo p r hp1 hrlt (u.map Prod.snd) (v.map Prod.fst) hlen1' hlen2 hb1' hb2
  have h11 := hpo p r hp1 hrlt (u.map Prod.snd) (v.map Prod.snd) hlen1' hlen2' hb1' hb2'
  set xs : List Val := [.int (kronX0 u p), .int (kronX1 u p), .int (kronX0 u p), .int (kronX1 u p)]
    with hxs
  set ys : List Val := [.int (kronY0 v p), .int (kronY1 v p), .int (kronY1 v p), .int (kronY0 v p)]
    with hys
  set L : ℕ := digVSz p r with hL
  set cF : ℕ := Cm (3 * r * p) + ZK * (30 * ((r + 1) * (p + 1) ^ 2)) with hcF
  set RT : List Val := .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) :: .int (p : ℤ) :: .int (r : ℤ) :: rest
    with hRT
  have hsub : ∀ x y : Val, (∃ X Y : ℤ, x = .int X ∧ y = .int Y ∧
        X.natAbs.size ≤ 3 * r * p ∧ Y.natAbs.size ≤ 3 * r * p ∧
        0 ≤ X * Y + digitOffset p (2 * r) ∧ X * Y + digitOffset p (2 * r) < 2 ^ (3 * p * (2 * r))) →
      WordR main zp
        (fun vs => vs = x :: y :: .int (3 * (p : ℤ)) :: .int (2 * (r : ℤ)) ::
          .int (digitOffset p (2 * r)) :: RT)
        (fun _ out => ∃ z, out = z :: .int (3 * (p : ℤ)) :: .int (2 * (r : ℤ)) ::
          .int (digitOffset p (2 * r)) :: RT ∧
          (∃ X Y : ℤ, x = .int X ∧ y = .int Y ∧
            z = intList (chunks (X * Y + digitOffset p (2 * r)).toNat (3 * p) (2 * r))) ∧
          vsz z ≤ L) (fun _ => cF) := by
    intro x y hxy
    obtain ⟨X, Y, hx, hy, hXs, hYs, hC0, hClt⟩ := hxy
    subst hx; subst hy
    have hXsN : X.natAbs.size < N := by omega
    have hYsN : Y.natAbs.size < N := by omega
    have hb3p : 1 ≤ 3 * p := by omega
    have hn2r : 1 ≤ 2 * r := by omega
    refine hK.conseq main zp _ _ _ _ _ _ (hzp' main N Cm hmon hmul X Y (3 * p) (2 * r)
      (digitOffset p (2 * r)) RT hXsN hYsN hb3p hn2r hC0 hClt) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      rw [← int_three_mul p, ← int_two_mul r]
    · intro vs out hvs hq
      refine ⟨intList (chunks (X * Y + digitOffset p (2 * r)).toNat (3 * p) (2 * r)), ?_,
        ⟨X, Y, rfl, rfl, rfl⟩, ?_⟩
      · rw [hq]
        rw [int_three_mul p, int_two_mul r]
      · have hb : ∀ n ∈ chunks (X * Y + digitOffset p (2 * r)).toNat (3 * p) (2 * r),
            n < 2 ^ (3 * p) := mem_chunks_lt _ _ _
        have h1 := vsz_intList_le hb
        rw [chunks_length] at h1
        simp only [hL, digVSz]
        nlinarith [h1, Nat.zero_le p, Nat.zero_le r, hr1]
    · intro vs _
      simp only [hcF]
      have hm : Cm (max X.natAbs.size Y.natAbs.size) ≤ Cm (3 * r * p) := hmon (max_le hXs hYs)
      have hCs : (digitOffset p (2 * r)).natAbs.size ≤ 6 * r * p + 2 * r + 1 := by
        have h := digitOffset_natAbs_le p (2 * r) hp1
        have h2 : (digitOffset p (2 * r)).natAbs < 2 ^ (6 * r * p + 2 * r + 1) := by
          refine lt_of_le_of_lt h ?_
          have h4 : 2 * r ≤ 2 ^ (2 * r) := le_of_lt (Nat.lt_two_pow_self (n := 2 * r))
          calc 2 * r * 2 ^ (3 * p * (2 * r)) ≤ 2 ^ (2 * r) * 2 ^ (3 * p * (2 * r)) :=
                Nat.mul_le_mul_right _ h4
            _ = 2 ^ (2 * r + 3 * p * (2 * r)) := by rw [← pow_add]
            _ < 2 ^ (6 * r * p + 2 * r + 1) := by
                apply Nat.pow_lt_pow_right (by norm_num)
                have he : 3 * p * (2 * r) = 6 * r * p := by ring
                rw [he]; omega
        exact Nat.size_le.mpr h2
      have h1 : X.natAbs.size + Y.natAbs.size + (2 * r + 1) * (3 * p + 1) +
          (digitOffset p (2 * r)).natAbs.size + 1 ≤ 30 * ((r + 1) * (p + 1) ^ 2) := by
        have h5 : (2 * r + 1) * (3 * p + 1) ≤ 12 * r * p := by nlinarith
        have h6 : 3 * r * p ≤ 3 * ((r + 1) * (p + 1) ^ 2) := by nlinarith
        have h7 : 6 * r * p + 2 * r + 1 ≤ 9 * ((r + 1) * (p + 1) ^ 2) := by nlinarith
        have h8 : 8 * r * p ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by nlinarith
        nlinarith [hXs, hYs, hCs, h5, h6, h7, h8]
      have h2 := Nat.mul_le_mul_left ZK h1
      have h3 := Nat.add_le_add hm h2
      exact h3
  have hxsys : xs.length = ys.length := by simp [hxs, hys]
  have hP : ∀ i, i < xs.length → ∃ X Y : ℤ, xs.getD i .nil = .int X ∧ ys.getD i .nil = .int Y ∧
      X.natAbs.size ≤ 3 * r * p ∧ Y.natAbs.size ≤ 3 * r * p ∧
      0 ≤ X * Y + digitOffset p (2 * r) ∧
      X * Y + digitOffset p (2 * r) < 2 ^ (3 * p * (2 * r)) := by
    intro i hi
    have hi4 : i < 4 := by simpa [hxs] using hi
    interval_cases i
    · exact ⟨_, _, rfl, rfl, hcX0, hcY0, h00.1, h00.2⟩
    · exact ⟨_, _, rfl, rfl, hcX1, hcY1, h11.1, h11.2⟩
    · exact ⟨_, _, rfl, rfl, hcX0, hcY1, h01.1, h01.2⟩
    · exact ⟨_, _, rfl, rfl, hcX1, hcY0, h10.1, h10.2⟩
  have hLb : ∀ x ∈ xs ++ ys, vsz x ≤ L := by
    intro x hx
    rw [hxs, hys] at hx
    rw [hL]
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [vsz_int_le_digVSz hr1 hcX0, vsz_int_le_digVSz hr1 hcX1,
        vsz_int_le_digVSz hr1 hcX0, vsz_int_le_digVSz hr1 hcX1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [vsz_int_le_digVSz hr1 hcY0, vsz_int_le_digVSz hr1 hcY1,
        vsz_int_le_digVSz hr1 hcY1, vsz_int_le_digVSz hr1 hcY0]
  have hzw := hzw main zp
    (.int (3 * (p : ℤ)) :: .int (2 * (r : ℤ)) :: .int (digitOffset p (2 * r)) :: RT)
    (fun x y => ∃ X Y : ℤ, x = .int X ∧ y = .int Y ∧
      X.natAbs.size ≤ 3 * r * p ∧ Y.natAbs.size ≤ 3 * r * p ∧
      0 ≤ X * Y + digitOffset p (2 * r) ∧ X * Y + digitOffset p (2 * r) < 2 ^ (3 * p * (2 * r)))
    (fun x y z => ∃ X Y : ℤ, x = .int X ∧ y = .int Y ∧
      z = intList (chunks (X * Y + digitOffset p (2 * r)).toNat (3 * p) (2 * r)))
    cF L hsub xs ys hxsys hP hLb
  refine hK.conseq main (zw zp) _ _ _ _ _ _ hzw ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]
    simp only [hxs, hys, hRT, zsVal, List.map_cons, List.map_nil]
  · intro vs out hvs hq
    obtain ⟨zs, hzs, hzlen, hQi⟩ := hq
    have hget0 : zs.getD 0 .nil = intList (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p)) := by
      obtain ⟨X, Y, hx, hy, hz⟩ := hQi 0 (by simp [hxs])
      rw [hxs] at hx
      rw [hys] at hy
      simp only [List.getD_cons_zero] at hx hy
      have hX : X = kronX0 u p := (Val.int.inj hx).symm
      have hY : Y = kronY0 v p := (Val.int.inj hy).symm
      rw [hz, hX, hY]; rfl
    have hget1 : zs.getD 1 .nil = intList (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)) := by
      obtain ⟨X, Y, hx, hy, hz⟩ := hQi 1 (by simp [hxs])
      rw [hxs] at hx
      rw [hys] at hy
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hx hy
      have hX : X = kronX1 u p := (Val.int.inj hx).symm
      have hY : Y = kronY1 v p := (Val.int.inj hy).symm
      rw [hz, hX, hY]; rfl
    have hget2 : zs.getD 2 .nil = intList (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p)) := by
      obtain ⟨X, Y, hx, hy, hz⟩ := hQi 2 (by simp [hxs])
      rw [hxs] at hx
      rw [hys] at hy
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hx hy
      have hX : X = kronX0 u p := (Val.int.inj hx).symm
      have hY : Y = kronY1 v p := (Val.int.inj hy).symm
      rw [hz, hX, hY]; rfl
    have hget3 : zs.getD 3 .nil = intList (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p)) := by
      obtain ⟨X, Y, hx, hy, hz⟩ := hQi 3 (by simp [hxs])
      rw [hxs] at hx
      rw [hys] at hy
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hx hy
      have hX : X = kronX1 u p := (Val.int.inj hx).symm
      have hY : Y = kronY0 v p := (Val.int.inj hy).symm
      rw [hz, hX, hY]; rfl
    have hzs4 : zs.length = 4 := by simpa [hxs] using hzlen
    have hzeq : zs = [intList (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p)),
        intList (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)),
        intList (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p)),
        intList (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p))] := by
      apply list_eq_of_getD
      · simp [hzs4]
      · intro i hi
        have hi4 : i < 4 := by simpa [hzs4] using hi
        interval_cases i
        · simpa only [List.getD_cons_zero] using hget0
        · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hget1
        · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hget2
        · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hget3
    rw [hzs, hzeq]
  · intro vs _
    have hlenx : xs.length = 4 := by simp [hxs]
    rw [hlenx]
    simp only [hcF, hL]
    have hX1 : (1 : ℕ) ≤ (r + 1) * (p + 1) ^ 2 :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hdig : digVSz p r + 1 ≤ 65 * ((r + 1) * (p + 1) ^ 2) := by
      have h1 := digVSz_le p r
      have h2 : (1 : ℕ) ≤ (r + 1) * (p + 1) ^ 2 := hX1
      nlinarith [h1, h2]
    have hZK : (4 * ZK) * (30 * ((r + 1) * (p + 1) ^ 2)) = (120 * ZK) * ((r + 1) * (p + 1) ^ 2) := by
      ring
    have hWK : (4 * WK) * (digVSz p r + 1) ≤ (4 * WK) * (65 * ((r + 1) * (p + 1) ^ 2)) :=
      Nat.mul_le_mul_left _ hdig
    nlinarith [hZK, hWK, hX1, Nat.zero_le ZK, Nat.zero_le WK, Nat.zero_le (Cm (3 * r * p))]


/-! ## Small facts about `kronDigits` -/

theorem chunks_getD_lt (x b N m : ℕ) (hm : m < N) : (chunks x b N).getD m 0 < 2 ^ b := by
  have hlen : m < (chunks x b N).length := by simp [chunks, hm]
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : (chunks x b N)[m] = x / 2 ^ (b * m) % 2 ^ b := by simp [chunks]
  rw [h1]
  exact Nat.mod_lt _ (Nat.pow_pos (by norm_num : (0 : ℕ) < 2))

theorem kronDigits_length (p N : ℕ) (X Y : ℤ) : (kronDigits p N X Y).length = N := by
  simp [kronDigits, chunks_length]

theorem kronDigits_getD_lt {p N : ℕ} {X Y : ℤ} {m : ℕ} (hm : m < N) :
    (kronDigits p N X Y).getD m 0 < 2 ^ (3 * p) := by
  unfold kronDigits
  exact chunks_getD_lt _ _ _ _ hm

theorem cvecSz_le (p r : ℕ) : Work.ConvR.cvecSz p r ≤ 20 * ((r + 1) * (p + 1) ^ 2) := by
  have hp1 : 1 ≤ p + 1 := by omega
  have hpp : (p + 1) * 1 ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ hp1
  have hX : (p + 1) ≤ (p + 1) * (p + 1) := by simpa using hpp
  simp only [Work.ConvR.cvecSz, Work.ConvR.cfxSz]
  nlinarith [hX, Nat.zero_le p, Nat.zero_le r]

/-! ## The states of the pipeline -/

/-- The precondition of the Kronecker word. -/
def KPre (p r : ℕ) : List Val → Prop := fun vs =>
  ∃ (u v : List (ℤ × ℤ)) (rest : List Val),
    vs = .int (p : ℤ) :: .int (r : ℤ) :: cvecVal u :: cvecVal v :: rest ∧
      InDiscVec p r u ∧ InDiscVec p r v

/-- The value-stack state after `Work.KronP.setup`. -/
def KSt1 (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List Val) : List Val :=
  .int (3 * (p : ℤ)) :: .int (2 * (r : ℤ)) :: .int (digitOffset p (2 * r)) ::
    .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) :: .int (p : ℤ) :: .int (r : ℤ) ::
    cvecVal u :: cvecVal v :: rest

/-- The value-stack state after `Work.KronP.splitPack`. -/
def KSt2 (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List Val) : List Val :=
  zsVal [kronX0 u p, kronX1 u p, kronX0 u p, kronX1 u p] ::
    zsVal [kronY0 v p, kronY1 v p, kronY1 v p, kronY0 v p] ::
    .int (3 * (p : ℤ)) :: .int (2 * (r : ℤ)) :: .int (digitOffset p (2 * r)) ::
    .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) :: .int (p : ℤ) :: .int (r : ℤ) :: rest

/-- The value-stack state after the four packed products. -/
def KSt3 (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List Val) : List Val :=
  ofList [intList (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p)),
    intList (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)),
    intList (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p)),
    intList (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p))] ::
    .int (3 * (p : ℤ)) :: .int (2 * (r : ℤ)) :: .int (digitOffset p (2 * r)) ::
    .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) :: .int (p : ℤ) :: .int (r : ℤ) :: rest

/-- The state after `Work.KronP.setup`. -/
def KS1 (p r : ℕ) : List Val → Prop := fun vs =>
  ∃ (u v : List (ℤ × ℤ)) (rest : List Val),
    vs = KSt1 p r u v rest ∧ InDiscVec p r u ∧ InDiscVec p r v

/-- The state after `Work.KronP.splitPack`. -/
def KS2 (p r : ℕ) : List Val → Prop := fun vs =>
  ∃ (u v : List (ℤ × ℤ)) (rest : List Val),
    vs = KSt2 p r u v rest ∧ InDiscVec p r u ∧ InDiscVec p r v

/-- The state after the four packed products. -/
def KS3 (p r : ℕ) : List Val → Prop := fun vs =>
  ∃ (u v : List (ℤ × ℤ)) (rest : List Val),
    vs = KSt3 p r u v rest ∧ InDiscVec p r u ∧ InDiscVec p r v

/-! ## The assembly -/

/-- The program of the Kronecker word: `setup`, `splitPack`, the four products, `combine`. -/
theorem kronAssembly (hK : KernelLib) (hI : IntLib) (hL : LayoutLib)
    (hsetup : SetupSpec) (hsplit : SplitPackSpec) (hzp : ProdDigitsSpec) (hpo : ProdOffsetSpec)
    (hcomb : CombineSpec) (hkf : KronFinalSpec) : Work.ConvR.KroneckerSpec := by
  obtain ⟨setP, S1, hset⟩ := hsetup
  obtain ⟨splP, S2, hspl⟩ := hsplit
  obtain ⟨zipP, S3, hzip⟩ := zipFour hK hzp hpo
  obtain ⟨comP, S4, hcom⟩ := hcomb
  refine ⟨.seq (.seq (.seq setP splP) zipP) comP, S1 + 41 * S2 + S3 + S4, ?_⟩
  intro main N Cm hmon hmul p r hr2 hpow hrlt hN
  have hr1 : 1 ≤ r := by omega
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp
    · subst hp0
      simp at hrlt
      omega
    · exact hp
  intro vs hvs s RR hs
  obtain ⟨u, v, rest, hvs', hu, hv⟩ := hvs
  subst hvs'
  -- stage 1: setup
  obtain ⟨out1, s1, n1, hout1, hev1, hn1, hstk1, hoth1⟩ :=
    hset main p r (cvecVal u) (cvecVal v) rest hp1 hr2 hpow
      (.int (p : ℤ) :: .int (r : ℤ) :: cvecVal u :: cvecVal v :: rest) rfl s RR hs
  -- stage 2: splitPack
  obtain ⟨out2, s2, n2, hout2, hev2, hn2, hstk2, hoth2⟩ :=
    hspl main p r u v rest hp1 hr2 hrlt hu hv out1 hout1 s1 RR hstk1
  -- stage 3: the four products
  obtain ⟨out3, s3, n3, hout3, hev3, hn3, hstk3, hoth3⟩ :=
    hzip main N Cm hmon hmul p r u v rest hp1 hr2 hrlt hu hv hN
      out2 hout2 s2 RR hstk2
  -- stage 4: combine
  have hlen : ∀ A ∈ [kronDigits p (2 * r) (kronX0 u p) (kronY0 v p),
      kronDigits p (2 * r) (kronX0 u p) (kronY1 v p),
      kronDigits p (2 * r) (kronX1 u p) (kronY0 v p),
      kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)], A.length = 2 * r := by
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    exacts [kronDigits_length _ _ _ _, kronDigits_length _ _ _ _,
      kronDigits_length _ _ _ _, kronDigits_length _ _ _ _]
  have hent : ∀ A ∈ [kronDigits p (2 * r) (kronX0 u p) (kronY0 v p),
      kronDigits p (2 * r) (kronX0 u p) (kronY1 v p),
      kronDigits p (2 * r) (kronX1 u p) (kronY0 v p),
      kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)],
      ∀ m, m < 2 * r → A.getD m 0 < 2 ^ (3 * p) := by
    intro A hA m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    exacts [kronDigits_getD_lt hm, kronDigits_getD_lt hm,
      kronDigits_getD_lt hm, kronDigits_getD_lt hm]
  obtain ⟨out4, s4, n4, hout4, hev4, hn4, hstk4, hoth4⟩ :=
    hcom main p r (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p))
      (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p))
      (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p))
      (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)) rest
      (hlen _ (by simp)) (hlen _ (by simp)) (hlen _ (by simp)) (hlen _ (by simp))
      hent hr2 hp1 out3 hout3 s3 RR hstk3
  -- the composite evaluation and the conclusions
  have hev : Eval main (.seq (.seq (.seq setP splP) zipP) comP) s s4 (n1 + n2 + n3 + n4) :=
    Eval.seq (Eval.seq (Eval.seq hev1 hev2) hev3) hev4
  have hoth : ∀ k : Stk, k ≠ 0 → s4.stk k = s.stk k := by
    intro k hk
    rw [hoth4 k hk, hoth3 k hk, hoth2 k hk, hoth1 k hk]
  have hf := hkf (p := p) (r := r) (clog_pow2 hpow) hr2 hrlt (u := u) (v := v) hu hv
  refine ⟨cvecVal (kronVec p r u v) :: rest, s4, n1 + n2 + n3 + n4, ?_, hev, ?_, ?_, hoth⟩
  · exact ⟨u, v, kronVec p r u v, rest, rfl, rfl, hf.1, hf.2⟩
  · have h2 : S2 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))
        ≤ S2 * ((r + 1) * (p + 1) ^ 2 + 40 * ((r + 1) * (p + 1) ^ 2)) := by
      have h1 := Work.ConvR.vsz_cvecVal_le hu
      have h2' := Work.ConvR.vsz_cvecVal_le hv
      have h3 := cvecSz_le p r
      have h5 : vsz (cvecVal u) ≤ 20 * ((r + 1) * (p + 1) ^ 2) := by omega
      have h6 : vsz (cvecVal v) ≤ 20 * ((r + 1) * (p + 1) ^ 2) := by omega
      exact Nat.mul_le_mul_left S2 (by omega)
    have hY1 : 1 ≤ (r + 1) * (p + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hn2' : n2 ≤ S2 * ((r + 1) * (p + 1) ^ 2 + 40 * ((r + 1) * (p + 1) ^ 2)) :=
      le_trans hn2 h2
    have hsum : n1 + n2 + n3 + n4 ≤
        (S1 + 41 * S2 + S3 + S4) * (r + 1) * (p + 1) ^ 2 + 4 * Cm (3 * r * p) := by
      have e1 : n1 + n2 + n3 + n4 ≤ S1 * (r + 1) * (p + 1) ^ 2 +
          S2 * ((r + 1) * (p + 1) ^ 2 + 40 * ((r + 1) * (p + 1) ^ 2)) +
          (4 * Cm (3 * r * p) + S3 * (r + 1) * (p + 1) ^ 2) +
          S4 * (r + 1) * (p + 1) ^ 2 := by
        linarith [hn1, hn2', hn3, hn4]
      have e2 : S1 * (r + 1) * (p + 1) ^ 2 +
          S2 * ((r + 1) * (p + 1) ^ 2 + 40 * ((r + 1) * (p + 1) ^ 2)) +
          (4 * Cm (3 * r * p) + S3 * (r + 1) * (p + 1) ^ 2) +
          S4 * (r + 1) * (p + 1) ^ 2 =
          (S1 + 41 * S2 + S3 + S4) * (r + 1) * (p + 1) ^ 2 + 4 * Cm (3 * r * p) := by
        ring
      linarith [e1, e2.le, e2.ge]
    linarith [hsum]
  · rw [hstk4, hout4]
    rfl


/-- Paper Lem. 2.5 (multiplication in C[y]/(y^r+1) by Kronecker substitution), as specified by ConvR. -/
theorem kronecker : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    Work.ConvR.KroneckerSpec := fun hK hI hL _ =>
  kronAssembly hK hI hL (setup hK hI) (splitPack hK hI hL) (prodDigits hK hI)
    prodOffset (combine hK hI hL) kronFinal

end Work.KronP
