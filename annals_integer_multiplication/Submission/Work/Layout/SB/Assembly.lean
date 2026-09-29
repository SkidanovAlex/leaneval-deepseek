import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.SB.Toolkit
import Submission.Work.IntLib.encodeNatBridge

/-!
# The sort-based proof of `LayoutLib.applyAlong` (paper Lemma 2.11)

`Submission/Work/Layout/SB/Assembly.lean` assembles the field
`HvdH.LayoutLib.applyAlong` from the list words (`SortSpec`, `ChunksSpec`, `EnumerateSpec`,
`ReplicateSpec`), the raw structural pieces (`PrologueSpec`, `EpilogueSpec`, `TailSpec2`) and the
two sort phases (`Phase1Spec`, `Phase3bSpec`), plus the pure list facts (`VszSpec`, `SlicesSpec`,
`Forall2Spec`, `UnsliceVszSpec`).

The program is `comb q := seqs [proP, brP, mlComb q, tailP]`:

* `proP` (raw) parks `int n` and a copy of `int B` on stack 1 and rearranges the value list into
  `ofList es :: int m :: int B :: int A :: rest`;
* `brP` builds the `A*B` slices `slices A m B es`;
* `mlComb q` runs `q` on every slice (this is the only `A*B*c` term);
* `tailP` (raw) repacks the output slices into the `A × n × B` layout and restores stack 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace Work.Layout

open HvdH

/-- the postcondition of `LayoutLib.applyAlong` as a stand-alone predicate -/
def aaPost (m n A B : ℕ) (es rest : List Val) (Q : List Val → List Val → Prop)
    (out : List Val) : Prop :=
  ∃ outs : List (List Val), out = ofList (unslices A n B outs) :: rest ∧ outs.length = A * B ∧
    ∀ s, s < A * B → (outs.getD s []).length = n ∧ Q ((slices A m B es).getD s []) (outs.getD s [])

theorem vsz_int_val_asm (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

/-- The scale `(M+1) * (L + M.size + 1) * (M.size + 1)` dominates `M * (L+3) + 1`. -/
theorem size_le_triple (M L : ℕ) :
    M * (L + 3) + 1 ≤ (M + 1) * (L + M.size + 1) * (M.size + 1) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Nat.mul_zero, Nat.zero_add, Nat.size_zero]
    omega
  · have hq : 1 ≤ M.size := Nat.size_pos.mpr hM
    have h5 : L + 4 ≤ (L + M.size + 1) * (M.size + 1) := by
      have h6 : 3 ≤ M.size * M.size + 2 * M.size := by nlinarith
      nlinarith [Nat.zero_le L, Nat.zero_le M.size]
    have h4 : (M + 1) * (L + 4) ≤ (M + 1) * (L + M.size + 1) * (M.size + 1) := by
      have h := Nat.mul_le_mul_left (M + 1) h5
      simpa only [Nat.mul_assoc] using h
    have h3 : M * (L + 1) + 2 * M + 1 ≤ (M + 1) * (L + 4) := by nlinarith
    have h1 : M * (L + 3) + 1 = M * (L + 1) + 2 * M + 1 := by ring
    rw [h1]
    exact le_trans h3 h4

/-- `Forall₂` transport for the `mapList`-shaped relation: every right entry is an `ofList`. -/
theorem forall2_ofList_mem {n : ℕ} {Q : List Val → List Val → Prop} :
    ∀ (sls : List (List Val)) (ys : List Val),
      List.Forall₂ (fun x y => ∃ (sl ol : List Val), x = ofList sl ∧ y = ofList ol ∧
        ol.length = n ∧ Q sl ol) (sls.map ofList) ys →
      ∀ y ∈ ys, ∃ ol : List Val, y = ofList ol := by
  intro sls
  induction sls with
  | nil =>
      intro ys h
      cases h with
      | nil => intro y hy; simp at hy
  | cons sl sls ih =>
      intro ys h
      cases h with
      | cons hx htl =>
          intro y hy
          rcases List.mem_cons.mp hy with hyx | hy
          · obtain ⟨sl', ol, -, hol, -⟩ := hx
            exact ⟨ol, by rw [hyx]; exact hol⟩
          · exact ih _ htl y hy

/-- **the sort-based proof of `LayoutLib.applyAlong`** (paper Lemma 2.11), modulo the list words,
the two sort phases and the structural pieces. -/
theorem applyAlongSort (hK : KernelLib) (hSo : SortSpec) (hCh : ChunksSpec)
    (hEn : EnumerateSpec) (hRp : ReplicateSpec) (hP1 : Phase1Spec) (hBr : Branch2Spec)
    (hPro : PrologueSpec) (hEpi : EpilogueSpec) (hP3 : Phase3bSpec) (hTail : TailSpec2)
    (hVsz : VszSpec) (hF2 : Forall2Spec) (hSF : SlicesSpec) (hUS : UnsliceVszSpec) :
    ApplyAlongSpec := by
  obtain ⟨brP, Kbr, hbr⟩ := hBr
  obtain ⟨proP, Kpro, hpro⟩ := hPro
  obtain ⟨tailP, Ktail, htail⟩ := hTail
  obtain ⟨mlComb, Kml, hml⟩ := hK.mapList
  set KT0 : ℕ := Kbr + Kpro + Ktail + Kml + 1 with hKT0
  set KT : ℕ := 100 * KT0 with hKT
  refine ⟨fun q => seqs [proP, brP, mlComb q, tailP], KT, ?_⟩
  intro main q rest m n P Q c L hq A B es hlen hsz hP
  set NJ : ℕ := A * B * (m + n + 1) with hNJ
  set S : ℕ := isz (A : ℤ) + isz (m : ℤ) + isz (n : ℤ) + isz (B : ℤ) with hS
  set BIG : ℕ := (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) with hBIG
  have hAB : A * B ≤ NJ := by
    rw [hNJ]
    calc A * B = A * B * 1 := (Nat.mul_one _).symm
      _ ≤ A * B * (m + n + 1) := Nat.mul_le_mul_left _ (by omega)
  have hAmB : A * m * B ≤ NJ := by
    rw [hNJ]
    calc A * m * B = A * B * m := by ring
      _ ≤ A * B * (m + n + 1) := Nat.mul_le_mul_left _ (by omega)
  have hABn : A * B * n ≤ NJ := by
    rw [hNJ]
    exact Nat.mul_le_mul_left _ (by omega)
  have hBIGpos : 0 < BIG := by rw [hBIG]; positivity
  have hBIG1 : 1 ≤ BIG := hBIGpos
  have hSpos : 0 < S := by
    rw [hS, Work.IntLib.isz_eq, Work.IntLib.isz_eq, Work.IntLib.isz_eq, Work.IntLib.isz_eq]
    omega
  -- general size bounds
  have hvszE : vsz (ofList es) + 1 ≤ 2 * BIG := by
    have h1 : vsz (ofList es) ≤ (A * m * B + 1) * (L + 1) := by
      rw [← hlen]; exact hVsz.2.1 es L hsz
    have h2 : (A * m * B + 1) * (L + 1) ≤ BIG := by
      have h3 : A * m * B + 1 ≤ NJ + 1 := by omega
      have h4 : L + 1 ≤ (L + NJ.size + 1) * (NJ.size + 1) :=
        le_trans (by omega) (Nat.le_mul_of_pos_right (L + NJ.size + 1) (by omega))
      calc (A * m * B + 1) * (L + 1) ≤ (NJ + 1) * ((L + NJ.size + 1) * (NJ.size + 1)) :=
            Nat.mul_le_mul h3 h4
        _ = BIG := by rw [hBIG]; ring
    omega
  have hLmap : A * B * ((m + n + 2) * (L + 1) + 1) ≤ 3 * BIG := by
    have hm2 : A * B * (m + n + 2) ≤ 2 * NJ := by
      rw [hNJ]
      have h : m + n + 2 ≤ 2 * (m + n + 1) := by omega
      calc A * B * (m + n + 2) ≤ A * B * (2 * (m + n + 1)) := Nat.mul_le_mul_left _ h
        _ = 2 * (A * B * (m + n + 1)) := by ring
    have hL1 : NJ * (L + 1) ≤ BIG := by
      have h4 : L + 1 ≤ (L + NJ.size + 1) * (NJ.size + 1) :=
        le_trans (by omega) (Nat.le_mul_of_pos_right (L + NJ.size + 1) (by omega))
      calc NJ * (L + 1) ≤ (NJ + 1) * ((L + NJ.size + 1) * (NJ.size + 1)) :=
            Nat.mul_le_mul (by omega) h4
        _ = BIG := by rw [hBIG]; ring
    have hNJle : NJ ≤ BIG := by
      rw [hBIG]
      calc NJ ≤ NJ + 1 := by omega
        _ ≤ (NJ + 1) * ((L + NJ.size + 1) * (NJ.size + 1)) :=
            Nat.le_mul_of_pos_right (NJ + 1) (by positivity)
        _ = (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) := by rw [Nat.mul_assoc]
    have hexp : A * B * ((m + n + 2) * (L + 1) + 1)
        = A * B * (m + n + 2) * (L + 1) + A * B := by ring
    rw [hexp]
    have := Nat.mul_le_mul_right (L + 1) hm2
    linarith
  intro vs hvs s Rg h0
  -- ================= 1. prologue =================
  obtain ⟨s1, N1, hE1, hN1, h1a, h1b, h1fr⟩ :=
    hpro main s.reg s.stk Rg A m n B es rest (by rw [h0, hvs])
  -- ================= 2. slices =================
  obtain ⟨out2, s2, hQ2, hE2, h02, h2fr⟩ :=
    WordR.applyEv (h := hbr main A m B NJ L es rest hAB hAmB hlen hsz)
      (vs := ofList es :: Val.int m :: Val.int B :: Val.int A :: rest) (hP := rfl)
      (g := s1.reg) (X := s1.stk) (R := Rg) h1a
  obtain ⟨sls, hout2, hsls2⟩ := hQ2
  have hslAB : sls.length = A * B := by rw [hsls2, hSF.1]
  have hslget : ∀ s, s < A * B → (sls.getD s []).length = m := by
    intro s hs; rw [hsls2]; exact hSF.2.1 A m B es s hs
  -- ================= 3. mapList q =================
  have hside : ∀ x ∈ sls.map ofList, (∃ sl : List Val, x = ofList sl ∧ sl.length = m ∧ P sl) ∧
      vsz x ≤ (m + n + 2) * (L + 1) := by
    intro x hx
    obtain ⟨sl, hslmem, rfl⟩ := List.mem_map.mp hx
    have hslmem' : sl ∈ slices A m B es := by rw [← hsls2]; exact hslmem
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hslmem'
    have hiAB : i < A * B := by rw [hSF.1] at hi; exact hi
    have hslsl : sl = (slices A m B es).getD i [] := by
      rw [← hget]
      exact (List.getD_eq_getElem (l := slices A m B es) (d := ([] : List Val)) (n := i) hi).symm
    have hslm : sl.length = m := by rw [hslsl]; exact hSF.2.1 A m B es i hiAB
    refine ⟨⟨sl, rfl, hslm, ?_⟩, ?_⟩
    · rw [hslsl]; exact hP i hiAB
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · have hsl_nil : sl = [] := List.eq_nil_of_length_eq_zero (by rw [hslm, hm])
        rw [hsl_nil, hm]
        have hone : vsz (ofList ([] : List Val)) = 1 := by simp [ofList, vsz, Val.enc]
        rw [hone]
        exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      · have h1 := hVsz.2.2.1 A m B es L hm hlen hsz i hiAB
        have h2 : (m + 1) * (L + 1) ≤ (m + n + 2) * (L + 1) :=
          Nat.mul_le_mul_right (L + 1) (by omega)
        rw [hslsl]
        exact le_trans h1 h2
  have hmlH : ∀ x, (∃ sl : List Val, x = ofList sl ∧ sl.length = m ∧ P sl) →
      WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧
          (∃ (sl ol : List Val), x = ofList sl ∧ y = ofList ol ∧ ol.length = n ∧
            (Q sl ol ∧ (∀ z ∈ ol, vsz z ≤ L))) ∧
          vsz y ≤ (m + n + 2) * (L + 1)) (fun _ => c) := by
    intro x hx
    obtain ⟨sl, rfl, hsl, hPsl⟩ := hx
    refine hK.conseq main q
      (fun vs => vs = ofList sl :: rest)
      (fun vs => vs = ofList sl :: rest)
      (fun _ out => ∃ ol : List Val, out = ofList ol :: rest ∧ ol.length = n ∧ Q sl ol ∧
        ∀ y ∈ ol, vsz y ≤ L)
      (fun _ out => ∃ y, out = y :: rest ∧
        (∃ (sl' ol : List Val), ofList sl = ofList sl' ∧ y = ofList ol ∧ ol.length = n ∧
          (Q sl' ol ∧ (∀ z ∈ ol, vsz z ≤ L))) ∧
        vsz y ≤ (m + n + 2) * (L + 1))
      (fun _ => c) (fun _ => c)
      (hq sl hsl hPsl) (fun vs hv => hv) ?_ (fun vs _ => le_rfl)
    · intro vs out _ hQout
      obtain ⟨ol, hout, holen, hQsl, hszol⟩ := hQout
      have hb : vsz (ofList ol) ≤ (m + n + 2) * (L + 1) := by
        have h1 := hVsz.2.1 ol L hszol
        have h2 : (ol.length + 1) * (L + 1) ≤ (m + n + 2) * (L + 1) :=
          Nat.mul_le_mul_right (L + 1) (by omega)
        exact le_trans h1 h2
      exact ⟨ofList ol, hout, ⟨sl, ol, rfl, rfl, holen, hQsl, hszol⟩, hb⟩
  obtain ⟨out3, s3, hQ3, hE3, h03, h3fr⟩ :=
    WordR.applyEv (h := hml main q rest
        (fun x => ∃ sl : List Val, x = ofList sl ∧ sl.length = m ∧ P sl)
        (fun x y => ∃ (sl ol : List Val), x = ofList sl ∧ y = ofList ol ∧ ol.length = n ∧
          (Q sl ol ∧ ∀ z ∈ ol, vsz z ≤ L))
        c ((m + n + 2) * (L + 1)) hmlH (sls.map ofList) hside)
      (vs := ofList (sls.map ofList) :: rest) (hP := rfl)
      (g := s2.reg) (X := s2.stk) (R := Rg) (by rw [h02, hout2])
  obtain ⟨ys, hys1, hys2⟩ := hQ3
  have h3b : s3.stk 1 = (Val.int B).enc ++ (Val.int n).enc ++ s.stk 1 := by
    rw [h3fr (1 : Stk) (by simp), h2fr (1 : Stk) (by simp), h1b]
  -- ================= 4. repackage =================
  have hy : ∀ y ∈ ys, ∃ ol : List Val, y = ofList ol := forall2_ofList_mem sls ys hys2
  obtain ⟨outs, houts1, houts2, houts3, houts4⟩ :=
    hF2 sls (fun sl ol => Q sl ol ∧ ∀ z ∈ ol, vsz z ≤ L) (sls.map ofList) ys
      hslAB hslget rfl hy hys2
  have houts4a : ∀ s, s < A * B → Q ((slices A m B es).getD s []) (outs.getD s []) := by
    intro s hs
    have := (houts4 s hs).1
    rwa [hsls2] at this
  have houts4b : ∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L := fun s hs => (houts4 s hs).2
  have houtsl : ∀ s, s < A * B → (outs.getD s []).length = n := houts3
  -- ================= 5. the tail =================
  have hszflat : vsz (ofList (outs.map ofList)) + 1 ≤
      (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) + 1 := by
    have h1 : vsz (ofList (outs.map ofList)) ≤ A * B * (n * (L + 1) + 1) + A * B + 1 :=
      hVsz.2.2.2 A n B outs L houts2 houts3 houts4b
    have h2 : A * B * (n * (L + 1) + 1) + A * B + 2 ≤
        (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) + 1 := by
      have hexp : A * B * (n * (L + 1) + 1) + A * B + 2
          = A * B * n * (L + 1) + 2 * (A * B) + 2 := by ring
      rw [hexp]
      have h3 : A * B * n * (L + 1) + 2 * (A * B) + 2 ≤ NJ * (L + 3) + 2 := by
        have h4 : A * B * n ≤ NJ := hABn
        have h5 : A * B ≤ NJ := hAB
        have h6 : A * B * n * (L + 1) ≤ NJ * (L + 1) := Nat.mul_le_mul_right (L + 1) h4
        nlinarith
      linarith [size_le_triple NJ L]
    omega
  have hszxout : vsz (ofList (unslices A n B outs)) + 1 ≤
      (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) + 1 := by
    have h1 : vsz (ofList (unslices A n B outs)) ≤ A * n * B * (L + 3) + 1 :=
      hUS A n B outs L houts2 houts3 houts4b
    have h2 : A * n * B ≤ NJ := by
      have h : A * n * B = A * B * n := by ring
      rw [h]; exact hABn
    have h3 : A * n * B * (L + 3) + 1 ≤ NJ * (L + 3) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right (L + 3) h2) 1
    linarith [size_le_triple NJ L]
  have h30 : s3.stk 0 = encs (ofList (outs.map ofList) :: rest) ++ Rg := by
    rw [h03, hys1, houts1]
  obtain ⟨s6, N6, hE6, hN6, h60, h61, h6fr⟩ :=
    htail main s3.reg s3.stk Rg (s.stk 1) A n B NJ L outs rest hAB hABn houts2 houts3 houts4b
      hszflat hszxout h30 h3b
  -- ================= cost =================
  obtain ⟨mm1, he1, hl1⟩ := hE1
  obtain ⟨mm2, he2, hl2⟩ := hE2
  obtain ⟨mm3, he3, hl3⟩ := hE3
  obtain ⟨mm4, he4, hl4⟩ := hE6
  rw [← hS] at hN1
  rw [List.length_map, hslAB] at hl3
  have hm1 : mm1 ≤ Kpro * S + 2 * (Kpro * BIG) := by
    have h : Kpro * (S + (vsz (ofList es) + 1)) ≤ Kpro * (S + 2 * BIG) :=
      Nat.mul_le_mul_left Kpro (by omega)
    have h' : Kpro * (S + 2 * BIG) = Kpro * S + 2 * (Kpro * BIG) := by ring
    linarith
  have hm2 : mm2 ≤ Kbr * BIG + Kbr * S := by
    have e : Kbr * (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) = Kbr * BIG := by
      rw [hBIG]; ring
    rw [e] at hl2
    have h : isz (A : ℤ) + isz (m : ℤ) + isz (B : ℤ) ≤ S := by rw [hS]; omega
    have h' : Kbr * (isz (A : ℤ) + isz (m : ℤ) + isz (B : ℤ)) ≤ Kbr * S :=
      Nat.mul_le_mul_left Kbr h
    linarith
  have hm3 : mm3 ≤ A * B * c + 4 * (Kml * BIG) := by
    have e : A * B * (c + Kml * ((m + n + 2) * (L + 1) + 1)) + Kml
        = A * B * c + Kml * (A * B * ((m + n + 2) * (L + 1) + 1)) + Kml := by ring
    rw [e] at hl3
    have h3 : Kml * (A * B * ((m + n + 2) * (L + 1) + 1)) ≤ Kml * (3 * BIG) :=
      Nat.mul_le_mul_left Kml hLmap
    have h4 : Kml ≤ Kml * BIG := by
      calc Kml = Kml * 1 := (Nat.mul_one _).symm
        _ ≤ Kml * BIG := Nat.mul_le_mul_left Kml hBIG1
    have h5 : Kml * (3 * BIG) + Kml ≤ 4 * (Kml * BIG) := by
      have e' : Kml * (3 * BIG) = 3 * (Kml * BIG) := by ring
      rw [e']
      calc 3 * (Kml * BIG) + Kml ≤ 3 * (Kml * BIG) + Kml * BIG := Nat.add_le_add_left h4 _
        _ = 4 * (Kml * BIG) := by ring
    linarith
  have hm4 : mm4 ≤ 2 * (Ktail * BIG) + Ktail * S := by
    have e : Ktail * ((NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) + (isz (n : ℤ) + isz (B : ℤ)) + 1)
        = Ktail * BIG + Ktail * (isz (n : ℤ) + isz (B : ℤ)) + Ktail := by rw [hBIG]; ring
    rw [e] at hN6
    have h : isz (n : ℤ) + isz (B : ℤ) ≤ S := by rw [hS]; omega
    have h' : Ktail * (isz (n : ℤ) + isz (B : ℤ)) ≤ Ktail * S := Nat.mul_le_mul_left Ktail h
    have h'' : Ktail ≤ Ktail * BIG := by
      calc Ktail = Ktail * 1 := (Nat.mul_one _).symm
        _ ≤ Ktail * BIG := Nat.mul_le_mul_left Ktail hBIG1
    linarith
  have hc1 : 2 * Kpro + Kbr + 4 * Kml + 2 * Ktail + 1 ≤ KT := by
    have h : 2 * Kpro + Kbr + 4 * Kml + 2 * Ktail + 1 ≤ 5 * KT0 := by omega
    have h' : 5 * KT0 ≤ KT := by
      rw [hKT]
      exact Nat.mul_le_mul_right KT0 (by norm_num : 5 ≤ 100)
    linarith
  have hc2 : Kpro + Kbr + Ktail ≤ KT := by
    have h : Kpro + Kbr + Ktail ≤ KT0 := by omega
    have h' : KT0 ≤ KT := by
      rw [hKT]
      calc KT0 = 1 * KT0 := (Nat.one_mul KT0).symm
        _ ≤ 100 * KT0 := Nat.mul_le_mul_right KT0 (by norm_num : 1 ≤ 100)
    linarith
  have hbin : (2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) * BIG + 1 ≤ KT * BIG := by
    have h1 : (2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) * BIG + 1
        ≤ ((2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) + 1) * BIG := by
      have e : ((2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) + 1) * BIG
          = (2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) * BIG + BIG := by ring
      rw [e]
      exact Nat.add_le_add_left hBIG1 _
    have h2 : ((2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) + 1) * BIG ≤ KT * BIG :=
      Nat.mul_le_mul_right BIG hc1
    linarith
  have hsum : mm1 + (mm2 + (mm3 + (mm4 + 1))) ≤
      (A * B * c + ((2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) * BIG + 1)) +
        (Kpro + Kbr + Ktail) * S := by
    have e1 : (2 * Kpro + Kbr + 4 * Kml + 2 * Ktail) * BIG + 1
        = 2 * (Kpro * BIG) + Kbr * BIG + (4 * (Kml * BIG) + 2 * (Ktail * BIG)) + 1 := by ring
    have e2 : (Kpro + Kbr + Ktail) * S = Kpro * S + (Kbr * S + Ktail * S) := by ring
    rw [e1, e2]
    linarith [hm1, hm2, hm3, hm4]
  have hfinal : mm1 + (mm2 + (mm3 + (mm4 + 1))) ≤ A * B * c + KT * BIG + KT * S := by
    refine le_trans hsum (Nat.add_le_add (Nat.add_le_add_left hbin (A * B * c)) ?_)
    exact Nat.mul_le_mul_right S hc2
  obtain ⟨ntot, hEval, hntot⟩ :=
    Ev.seqs_cons ⟨mm1, he1, le_rfl⟩ (Ev.seqs_cons ⟨mm2, he2, le_rfl⟩
      (Ev.seqs_cons ⟨mm3, he3, le_rfl⟩ (Ev.seqs_cons ⟨mm4, he4, le_rfl⟩ Ev.seqs_nil)))
  refine ⟨ofList (unslices A n B outs) :: rest, s6, ntot, ?_, hEval, ?_, h60, ?_⟩
  · exact ⟨outs, rfl, houts2, fun s hs => ⟨houtsl s hs, houts4a s hs⟩⟩
  · show ntot ≤ A * B * c + KT * (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) + KT * S
    have heq : A * B * c + KT * (NJ + 1) * (L + NJ.size + 1) * (NJ.size + 1) + KT * S
        = A * B * c + KT * BIG + KT * S := by
      rw [hBIG]; ring
    rw [heq]
    exact le_trans hntot hfinal
  · intro k hk0
    by_cases hk1 : k = 1
    · exact hk1 ▸ h61
    · exact (h6fr k hk0 hk1).trans ((h3fr k hk0).trans ((h2fr k hk0).trans (h1fr k hk0 hk1)))

end Work.Layout
