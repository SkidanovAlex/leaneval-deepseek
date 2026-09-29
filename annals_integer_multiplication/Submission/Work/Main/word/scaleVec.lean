import Mathlib
import Submission.Work.Main.defs
import Submission.Work.ConvR.dropUnder
import Submission.Work.ConvR.scaleRowWord

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.Main.word.scaleVec`: scaling a fixed-point complex vector by an integer

`Work.Main.word.scaleVec` applies `FxLib.scale` (paper Lemma 2.2) coefficientwise to a whole vector
`zs ∈ C̃◦^r`, where the scaling factor `c` and the precision `p` sit *below* the vector on the value
stack, in the order `cvecVal zs :: int c :: int p :: rest` (note: `c` on top of `p`, the reverse of
the order expected by `Work.ConvR.scaleRowWord`).

The program is assembled from `KernelLib.roll` and `Work.ConvR.scaleRowWord`:

* two `roll`s turn `[cvecVal zs, c, p] ++ rest` into `[cvecVal zs, p, c] ++ rest` (the *only*
  difference from the row word of `ConvR`);
* `Work.ConvR.scaleRowWord` (the `mapList` loop running `FxLib.scale` on every coefficient) turns
  `[cvecVal zs, p, c] ++ rest` into `[cvecVal ws, p, c] ++ rest`, with the scaled bound
  `2^p‖w̃_i - c x‖ < 2c(2^p‖ũ_i - x‖) + 3` for every complex `x` with `c‖x‖ ≤ 1`;
* two more `roll`s swap the parameters back: `[cvecVal ws, c, p] ++ rest`.

The two `roll`s around a value of encoding size `O(r p)` cost `O((r+1)(p+1)^2)`, so the total cost is
`K (r+1)(p+1)^2 + K`.  Instantiating the resulting pointwise bound with the true values `X i`
(`c‖X i‖ ≤ 1`, `2^p‖ũ_i - X i‖ ≤ E`) gives the stated strict bound `2cE + 3` on the error of the
scaled vector.
-/

namespace Work.Main.word

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- The pointwise scaled-approximation property of `scaleVec`: every coefficient of the output
vector is within `2 c ‖ũ_j - x‖ + 3` (in units of `2^{-p}`) of `c x`, for every complex number `x`
of norm at most `1/c`, where `ũ_j` is the corresponding input coefficient. -/
def ptScaled (p c : ℕ) (zs : List (ℤ × ℤ)) (v : List (ℤ × ℤ)) : Prop :=
  ∀ (j : Fin zs.length) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
    (2 : ℝ) ^ p * ‖HvdH.fxC p (v.getD j (0, 0)) - (c : ℂ) * x‖ <
      2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p (zs.getD j (0, 0)) - x‖) + 3

theorem scaleVec (hKer : HvdH.KernelLib) (hFx : HvdH.FxLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c : ℕ) (zs : List (ℤ × ℤ))
      (rest : List HvdH.Val) (X : ℕ → ℂ) (E : ℝ),
      1 ≤ c → c ≤ 2 ^ p → HvdH.InDiscVec p zs.length zs →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal zs :: HvdH.Val.int c :: HvdH.Val.int p :: rest ∧
          (∀ i < zs.length, (c : ℝ) * ‖X i‖ ≤ 1) ∧
          (∀ i < zs.length, (2 : ℝ) ^ p * ‖HvdH.fxC p (zs.getD i (0,0)) - X i‖ ≤ E))
        (fun vs out => ∃ ws, vs = HvdH.cvecVal zs :: HvdH.Val.int c :: HvdH.Val.int p :: rest ∧
          out = HvdH.cvecVal ws :: HvdH.Val.int c :: HvdH.Val.int p :: rest ∧ ws.length = zs.length ∧
          HvdH.InDiscVec p zs.length ws ∧
          ∀ i < zs.length, (2 : ℝ) ^ p * ‖HvdH.fxC p (ws.getD i (0,0)) - (c : ℂ) * X i‖ < 2 * c * E + 3)
        (fun _ => K * (zs.length + 1) * (p + 1) * (p + 1) + K) := by
  obtain ⟨rowP, Krw, hrow⟩ := Work.ConvR.scaleRowWord hKer hFx
  obtain ⟨rollP, Kr, hroll⟩ := hKer.roll
  refine ⟨rollP 2 ;;; rollP 1 ;;; rowP ;;; rollP 2 ;;; rollP 1, 300 * Kr + Krw + 1, ?_⟩
  intro main p c zs rest X E hc1 hc2 hdisc
  -- size bounds: the vector, `c` and `p` are all encoded in `O(p)` glyphs each
  have hL : HvdH.vsz (HvdH.cvecVal zs) ≤ Work.ConvR.cvecSz p zs.length :=
    Work.ConvR.vsz_cvecVal_le hdisc
  have hc_le : HvdH.isz (c : ℤ) ≤ p + 3 := Work.ConvR.isz_pow_le hc2
  have hp_le : HvdH.isz (p : ℤ) ≤ p + 2 := Work.ConvR.isz_int_le p
  -- step 1: move `p` to the front: `[U, c, p] ++ rest ↦ [p, U, c] ++ rest`
  have h1 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = HvdH.cvecVal zs :: HvdH.Val.int c :: HvdH.Val.int p :: rest)
      (fun _ out => out = HvdH.Val.int p :: HvdH.cvecVal zs :: HvdH.Val.int c :: rest)
      (Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 3) + (p + 2) + 1)) := by
    refine Work.ConvR.WordC.rollStep hKer hroll ?_ ?_ ?_
    · simp
    · simp
    · simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Work.Main.vsz_int, Nat.reduceAdd]
      apply Nat.mul_le_mul_left
      omega
  -- step 2: `[p, U, c] ++ rest ↦ [U, p, c] ++ rest`
  have h2 : Work.ConvR.WordC main (rollP 1)
      (fun vs => vs = HvdH.Val.int p :: HvdH.cvecVal zs :: HvdH.Val.int c :: rest)
      (fun _ out => out = HvdH.cvecVal zs :: HvdH.Val.int p :: HvdH.Val.int c :: rest)
      (Kr * 2 * ((p + 2) + Work.ConvR.cvecSz p zs.length + 1)) := by
    refine Work.ConvR.WordC.rollStep hKer hroll ?_ ?_ ?_
    · simp
    · simp
    · simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Work.Main.vsz_int, Nat.reduceAdd]
      apply Nat.mul_le_mul_left
      omega
  -- step 3: scale every coefficient (`ConvR.scaleRowWord`)
  have h3 : Work.ConvR.WordC main rowP
      (fun vs => vs = HvdH.cvecVal zs :: HvdH.Val.int p :: HvdH.Val.int c :: rest)
      (fun _ out => ∃ v : List (ℤ × ℤ),
        out = HvdH.cvecVal v :: HvdH.Val.int p :: HvdH.Val.int c :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (Krw * (zs.length + 1) * (p + 1) ^ 2 + Krw) := by
    refine Work.ConvR.WordC.ofWordR ?_
    exact hrow main p c zs.length hc1 hc2 zs rest hdisc
  -- step 4: `[W, p, c] ++ rest ↦ [c, W, p] ++ rest`
  have h4 : Work.ConvR.WordC main (rollP 2)
      (fun vs => ∃ v : List (ℤ × ℤ),
        vs = HvdH.cvecVal v :: HvdH.Val.int p :: HvdH.Val.int c :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (fun _ out => ∃ v : List (ℤ × ℤ),
        out = HvdH.Val.int c :: HvdH.cvecVal v :: HvdH.Val.int p :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 2) + (p + 3) + 1)) := by
    refine Work.ConvR.WordC.ofWordR (hKer.conseq main (rollP 2)
      (fun vs => 2 < vs.length)
      (fun vs => ∃ v : List (ℤ × ℤ),
        vs = HvdH.cvecVal v :: HvdH.Val.int p :: HvdH.Val.int c :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (fun vs out => out = vs.getD 2 HvdH.Val.nil :: vs.eraseIdx 2)
      (fun _ out => ∃ v : List (ℤ × ℤ),
        out = HvdH.Val.int c :: HvdH.cvecVal v :: HvdH.Val.int p :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (fun vs => Kr * (2 + 1) * (((vs.take 3).map HvdH.vsz).sum + 1))
      (fun _ => Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 2) + (p + 3) + 1))
      (hroll main 2) ?_ ?_ ?_)
    · intro vs hvs
      obtain ⟨v, rfl, hv, hpv⟩ := hvs
      simp
    · intro vs out hvs hout
      obtain ⟨v, rfl, hv, hpv⟩ := hvs
      rw [hout]
      exact ⟨v, by simp, hv, hpv⟩
    · intro vs hvs
      obtain ⟨v, rfl, hv, hpv⟩ := hvs
      have hLv : HvdH.vsz (HvdH.cvecVal v) ≤ Work.ConvR.cvecSz p zs.length :=
        Work.ConvR.vsz_cvecVal_le hv
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Work.Main.vsz_int, Nat.reduceAdd]
      apply Nat.mul_le_mul_left
      omega
  -- step 5: `[c, W, p] ++ rest ↦ [W, c, p] ++ rest`
  have h5 : Work.ConvR.WordC main (rollP 1)
      (fun vs => ∃ v : List (ℤ × ℤ),
        vs = HvdH.Val.int c :: HvdH.cvecVal v :: HvdH.Val.int p :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (fun _ out => ∃ v : List (ℤ × ℤ),
        out = HvdH.cvecVal v :: HvdH.Val.int c :: HvdH.Val.int p :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (Kr * 2 * ((p + 3) + Work.ConvR.cvecSz p zs.length + 1)) := by
    refine Work.ConvR.WordC.ofWordR (hKer.conseq main (rollP 1)
      (fun vs => 1 < vs.length)
      (fun vs => ∃ v : List (ℤ × ℤ),
        vs = HvdH.Val.int c :: HvdH.cvecVal v :: HvdH.Val.int p :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (fun vs out => out = vs.getD 1 HvdH.Val.nil :: vs.eraseIdx 1)
      (fun _ out => ∃ v : List (ℤ × ℤ),
        out = HvdH.cvecVal v :: HvdH.Val.int c :: HvdH.Val.int p :: rest ∧
        HvdH.InDiscVec p zs.length v ∧ ptScaled p c zs v)
      (fun vs => Kr * (1 + 1) * (((vs.take 2).map HvdH.vsz).sum + 1))
      (fun _ => Kr * 2 * ((p + 3) + Work.ConvR.cvecSz p zs.length + 1))
      (hroll main 1) ?_ ?_ ?_)
    · intro vs hvs
      obtain ⟨v, rfl, hv, hpv⟩ := hvs
      simp
    · intro vs out hvs hout
      obtain ⟨v, rfl, hv, hpv⟩ := hvs
      rw [hout]
      exact ⟨v, by simp, hv, hpv⟩
    · intro vs hvs
      obtain ⟨v, rfl, hv, hpv⟩ := hvs
      have hLv : HvdH.vsz (HvdH.cvecVal v) ≤ Work.ConvR.cvecSz p zs.length :=
        Work.ConvR.vsz_cvecVal_le hv
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Work.Main.vsz_int, Nat.reduceAdd]
      apply Nat.mul_le_mul_left
      omega
  -- assemble the five steps
  have h12 := Work.ConvR.WordC.seqEq hKer h1 h2
  have h123 := Work.ConvR.WordC.seq hKer h12 h3 (fun vs mid _ hq => hq)
  have h1234 := Work.ConvR.WordC.seq hKer h123 h4 (fun vs mid _ hq => by
    obtain ⟨m, _, hq3⟩ := hq
    exact hq3)
  have h12345 := Work.ConvR.WordC.seq hKer h1234 h5 (fun vs mid _ hq => by
    obtain ⟨m, _, hq4⟩ := hq
    exact hq4)
  refine Work.ConvR.WordC.conseq hKer h12345 ?_ ?_ ?_
  · -- the precondition of the library word follows from the stated precondition
    intro vs hvs
    exact hvs.1
  · -- the stated postcondition follows from the library postcondition
    intro vs out hvs hq
    obtain ⟨hvs1, hcX, hE⟩ := hvs
    obtain ⟨m4, _, h5q⟩ := hq
    obtain ⟨v, hout, hv, hpv⟩ := h5q
    refine ⟨v, hvs1, hout, hv.1, hv, ?_⟩
    intro i hi
    have hstep := hpv ⟨i, hi⟩ (X i) (hcX i hi)
    have hmono : 2 * (c : ℝ) * ((2 : ℝ) ^ p * ‖HvdH.fxC p (zs.getD i (0, 0)) - X i‖)
        ≤ 2 * (c : ℝ) * E :=
      mul_le_mul_of_nonneg_left (hE i hi) (by positivity)
    linarith
  · -- cost arithmetic
    have hLb : Work.ConvR.cvecSz p zs.length ≤ (zs.length + 1) * (2 * p + 9) := by
      simp only [Work.ConvR.cvecSz, Work.ConvR.cfxSz]
      nlinarith [Nat.zero_le p, Nat.zero_le zs.length]
    have h2p : 2 * p + 6 ≤ (zs.length + 1) * (2 * p + 6) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos zs.length)
    have hsum : (zs.length + 1) * (2 * p + 9) + (zs.length + 1) * (2 * p + 6)
        = (zs.length + 1) * (4 * p + 15) := by ring
    have hM1 : Work.ConvR.cvecSz p zs.length + (p + 3) + (p + 2) + 1
        ≤ (zs.length + 1) * (4 * p + 15) := by rw [← hsum]; omega
    have hM2 : (p + 2) + Work.ConvR.cvecSz p zs.length + 1
        ≤ (zs.length + 1) * (4 * p + 15) := by rw [← hsum]; omega
    have hM3 : (p + 3) + Work.ConvR.cvecSz p zs.length + 1
        ≤ (zs.length + 1) * (4 * p + 15) := by rw [← hsum]; omega
    have hM4 : Work.ConvR.cvecSz p zs.length + (p + 2) + (p + 3) + 1
        ≤ (zs.length + 1) * (4 * p + 15) := by rw [← hsum]; omega
    have h19 : (zs.length + 1) * (4 * p + 15) ≤ (zs.length + 1) * (19 * (p + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le p])
    have hA : Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 3) + (p + 2) + 1)
        ≤ Kr * 3 * ((zs.length + 1) * (19 * (p + 1) ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ hM1) (Nat.mul_le_mul_left _ h19)
    have hB : Kr * 2 * ((p + 2) + Work.ConvR.cvecSz p zs.length + 1)
        ≤ Kr * 2 * ((zs.length + 1) * (19 * (p + 1) ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ hM2) (Nat.mul_le_mul_left _ h19)
    have hC : Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 2) + (p + 3) + 1)
        ≤ Kr * 3 * ((zs.length + 1) * (19 * (p + 1) ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ hM4) (Nat.mul_le_mul_left _ h19)
    have hD : Kr * 2 * ((p + 3) + Work.ConvR.cvecSz p zs.length + 1)
        ≤ Kr * 2 * ((zs.length + 1) * (19 * (p + 1) ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ hM3) (Nat.mul_le_mul_left _ h19)
    calc (Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 3) + (p + 2) + 1)
            + Kr * 2 * ((p + 2) + Work.ConvR.cvecSz p zs.length + 1))
          + (Krw * (zs.length + 1) * (p + 1) ^ 2 + Krw)
          + Kr * 3 * (Work.ConvR.cvecSz p zs.length + (p + 2) + (p + 3) + 1)
          + Kr * 2 * ((p + 3) + Work.ConvR.cvecSz p zs.length + 1)
        ≤ (Kr * 3 * ((zs.length + 1) * (19 * (p + 1) ^ 2))
            + Kr * 2 * ((zs.length + 1) * (19 * (p + 1) ^ 2)))
          + (Krw * (zs.length + 1) * (p + 1) ^ 2 + Krw)
          + Kr * 3 * ((zs.length + 1) * (19 * (p + 1) ^ 2))
          + Kr * 2 * ((zs.length + 1) * (19 * (p + 1) ^ 2)) := by
          exact add_le_add (add_le_add (add_le_add (add_le_add hA hB) le_rfl) hC) hD
      _ = 190 * Kr * ((zs.length + 1) * (p + 1) ^ 2)
            + (Krw * (zs.length + 1) * (p + 1) ^ 2 + Krw) := by ring
      _ ≤ (300 * Kr + Krw + 1) * (zs.length + 1) * (p + 1) * (p + 1)
            + (300 * Kr + Krw + 1) := by
          calc 190 * Kr * ((zs.length + 1) * (p + 1) ^ 2)
                + (Krw * (zs.length + 1) * (p + 1) ^ 2 + Krw)
              = (190 * Kr + Krw) * ((zs.length + 1) * (p + 1) ^ 2) + Krw := by ring
            _ ≤ (300 * Kr + Krw + 1) * ((zs.length + 1) * (p + 1) ^ 2) + (300 * Kr + Krw + 1) := by
                exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
            _ = (300 * Kr + Krw + 1) * (zs.length + 1) * (p + 1) * (p + 1)
                  + (300 * Kr + Krw + 1) := by ring

end Work.Main.word
