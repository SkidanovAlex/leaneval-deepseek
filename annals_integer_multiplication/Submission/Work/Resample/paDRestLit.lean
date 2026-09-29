import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Params.listSizesBig

namespace Work.Resample

open HvdH

set_option autoImplicit false

/-! ## Helpers

`isz` of a natural cast, and two elementary monotonicity lemmas for `ℕ`-products (the shape in
which the absorption estimates below are written). -/

theorem paDL_isz_natCast (m : ℕ) : HvdH.isz ((m : ℕ) : ℤ) = m.size + 2 := by
  rw [HvdH.isz, Int.natAbs_natCast]

theorem paDL_one_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  simpa using Nat.mul_le_mul ha hb

theorem paDL_mul_one_le {a b : ℕ} (h : 1 ≤ a) : b ≤ a * b := by
  calc b = 1 * b := (Nat.one_mul b).symm
    _ ≤ a * b := Nat.mul_le_mul_right b h

theorem paDL_mul3_le {a a' b b' c c' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') :
    a * b * c ≤ a' * b' * c' := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-! ## Layout facts

For `h : HvdH.ResParams p α ss ts` and `j < D`: the two products `A = ∏_{i<j} t_i` and
`B = ∏_{i>j} s_i` together with the axis entries `ss_j < ts_j < 2^p` dominate the "layout" part of
the per-axis budget: with `X = A * B * (ss_j + ts_j + 1)` one has `X ≤ 3 * ts.prod` (because
`A * ts_j * ∏_{i>j} t_i = ts.prod`) and hence `X.size ≤ p * D + 2`. -/

theorem paDL_layout {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) (j : ℕ)
    (hj : j < HvdH.D) :
    1 ≤ ts.prod ∧
    (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) ≤ 3 * ts.prod ∧
    ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size
      ≤ p * HvdH.D + 2 ∧
    (ts.take j).prod ≤ ts.prod ∧
    (ss.drop (j + 1)).prod ≤ ts.prod ∧
    (ss.getD j 0).size ≤ p ∧
    (ts.getD j 0).size ≤ p := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hpt⟩ := h
  have hjts : j < ts.length := by rw [htslen]; exact hj
  obtain ⟨hs2, hst, ht2p, -, -⟩ := hpt j hj
  have ht1 : 1 ≤ ts.getD j 0 := by omega
  -- every element of `ts` is `≥ 3` and `< 2^p`
  have hts3 : ∀ x ∈ ts, 3 ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    obtain ⟨h1, h2, -, -, -⟩ := hpt i hiD
    have he : ts[i] = ts.getD i 0 := (List.getD_eq_getElem ts 0 hi).symm
    omega
  have htslt : ∀ x ∈ ts, x < 2 ^ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    obtain ⟨-, -, h3, -, -⟩ := hpt i hiD
    have he : ts[i] = ts.getD i 0 := (List.getD_eq_getElem ts 0 hi).symm
    rwa [he]
  have hts1 : ∀ x ∈ ts, 1 ≤ x := fun x hx => by have := hts3 x hx; omega
  have hT1 : 1 ≤ ts.prod := List.one_le_prod hts1
  -- the product decomposition
  have hdec : (ts.take j).prod * ts.getD j 0 * (ts.drop (j + 1)).prod = ts.prod := by
    have h1 : (ts.take j).prod * (ts.drop j).prod = ts.prod := List.prod_take_mul_prod_drop ts j
    have h2 : ts.drop j = ts.getD j 0 :: ts.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjts, List.getD_eq_getElem ts 0 hjts]
    rw [h2, List.prod_cons] at h1
    rw [← h1]; ring
  have hA : (ts.take j).prod ≤ ts.prod :=
    List.Sublist.prod_le_prod (List.take_sublist j ts) hts1
  have hB' : (ts.drop (j + 1)).prod ≤ ts.prod :=
    List.Sublist.prod_le_prod (List.drop_sublist (j + 1) ts) hts1
  -- the suffix products of `ss` and `ts` compare pointwise
  have hlen : (ss.drop (j + 1)).length = (ts.drop (j + 1)).length := by
    rw [List.length_drop, List.length_drop, hsslen, htslen]
  have hBB' : (ss.drop (j + 1)).prod ≤ (ts.drop (j + 1)).prod := by
    refine Work.MainP.prod_le_prod_of_getD hlen (fun i hi => ?_)
    rw [pa_getD_drop ss (j + 1) i hi]
    have hi' : i < (ts.drop (j + 1)).length := by rw [← hlen]; exact hi
    rw [pa_getD_drop ts (j + 1) i hi']
    have hidx : i + (j + 1) < HvdH.D := by
      have h2 := hi; rw [List.length_drop, hsslen] at h2; omega
    exact le_of_lt (hpt (i + (j + 1)) hidx).2.1
  have hB : (ss.drop (j + 1)).prod ≤ ts.prod := le_trans hBB' hB'
  -- the three summands of `X`
  have h1 : (ts.take j).prod * (ss.drop (j + 1)).prod * ss.getD j 0 ≤ ts.prod := by
    calc (ts.take j).prod * (ss.drop (j + 1)).prod * ss.getD j 0
        ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hBB') (le_of_lt hst)
      _ = ts.prod := by rw [← hdec]; ring
  have h2 : (ts.take j).prod * (ss.drop (j + 1)).prod * ts.getD j 0 ≤ ts.prod := by
    calc (ts.take j).prod * (ss.drop (j + 1)).prod * ts.getD j 0
        ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hBB')
      _ = ts.prod := by rw [← hdec]; ring
  have h3 : (ts.take j).prod * (ss.drop (j + 1)).prod ≤ ts.prod := by
    calc (ts.take j).prod * (ss.drop (j + 1)).prod
        ≤ (ts.take j).prod * (ts.drop (j + 1)).prod := Nat.mul_le_mul_left _ hBB'
      _ ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 := by
          calc (ts.take j).prod * (ts.drop (j + 1)).prod
              = (ts.take j).prod * (ts.drop (j + 1)).prod * 1 := (Nat.mul_one _).symm
            _ ≤ (ts.take j).prod * (ts.drop (j + 1)).prod * ts.getD j 0 :=
                Nat.mul_le_mul_left _ ht1
      _ = ts.prod := by rw [← hdec]; ring
  have hX : (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)
      ≤ 3 * ts.prod := by
    have he : (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)
        = (ts.take j).prod * (ss.drop (j + 1)).prod * ss.getD j 0
          + (ts.take j).prod * (ss.drop (j + 1)).prod * ts.getD j 0
          + (ts.take j).prod * (ss.drop (j + 1)).prod := by ring
    rw [he]; linarith [h1, h2, h3]
  -- `ts.prod` is below the product bound `2^(p*D)`
  have hTs : ts.prod ≤ 2 ^ (p * HvdH.D) := by
    have h1 : ts.prod ≤ (2 ^ p) ^ ts.length :=
      List.prod_le_pow_length ts (2 ^ p) (fun x hx => le_of_lt (htslt x hx))
    calc ts.prod ≤ (2 ^ p) ^ ts.length := h1
      _ = (2 ^ p) ^ HvdH.D := by rw [htslen]
      _ = 2 ^ (p * HvdH.D) := by rw [Nat.pow_mul]
  have hXsz : ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size
      ≤ p * HvdH.D + 2 := by
    rw [Nat.size_le]
    calc (ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)
        ≤ 3 * ts.prod := hX
      _ ≤ 3 * 2 ^ (p * HvdH.D) := Nat.mul_le_mul_left 3 hTs
      _ < 4 * 2 ^ (p * HvdH.D) := by
          have hpos : 0 < 2 ^ (p * HvdH.D) := pow_pos (by norm_num) _
          omega
      _ = 2 ^ (p * HvdH.D + 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_comm]
  exact ⟨hT1, hX, hXsz, hA, hB, Nat.size_le.mpr (lt_trans hst ht2p),
    Nat.size_le.mpr ht2p⟩

/-! ## The absorption arithmetic

Everything that the seven summands of `paDRest` (with `A`, `B`, the two axis entries, their four
`isz`'s, `ts.prod` and `p` abstracted as `X`, `iA`, `iB`, `is`, `it`, `T`, `p`) contribute is
absorbed by the `ts.prod * p ^ 2` term of `HvdH.resCost`. -/

theorem paDL_arith (X iA iB is it T p : ℕ) (hT : 1 ≤ T) (hp : 1 ≤ p)
    (hX : X ≤ 3 * T) (hXsz : X.size ≤ p * HvdH.D + 2)
    (hA : iA ≤ T + 2) (hB : iB ≤ T + 2) (hs : is ≤ p + 2) (ht : it ≤ p + 2) :
    64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
      + 64 * (iA + is + it + iB)
      + 1048576 * (T * (2 * p + 8) + T + 2)
      + 1048576 * ((HvdH.D + 1) * (p + 2))
      + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
      + 1048576 * ((p + 3) * (p + 3))
      + 1000000
    ≤ (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (T * p ^ 2) := by
  have hD1 : 1 ≤ HvdH.D := by norm_num [HvdH.D]
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hTp : 1 ≤ T * p ^ 2 := paDL_one_le_mul hT hp2
  have hpD1 : 1 ≤ p * HvdH.D := paDL_one_le_mul hp hD1
  have hppD : p ≤ p * HvdH.D := by nlinarith
  -- the `X`-term
  have e1 : X + 1 ≤ 4 * T := by omega
  have e2 : (2 * p + 8) + X.size + 1 ≤ 14 * (p * HvdH.D) := by
    have h1 : (2 * p + 8) + X.size + 1 ≤ 2 * p + (p * HvdH.D) + 11 := by omega
    have h2 : 2 * p + (p * HvdH.D) + 11 ≤ 14 * (p * HvdH.D) := by linarith
    linarith
  have e3 : X.size + 1 ≤ 4 * (p * HvdH.D) := by omega
  have b1 : 64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
      ≤ 14336 * HvdH.D ^ 2 * (T * p ^ 2) := by
    calc 64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
        ≤ 64 * ((4 * T) * (14 * (p * HvdH.D)) * (4 * (p * HvdH.D))) :=
          Nat.mul_le_mul_left 64 (paDL_mul3_le e1 e2 e3)
      _ = 14336 * HvdH.D ^ 2 * (T * p ^ 2) := by ring
  -- the `isz`-term
  have b2 : 64 * (iA + is + it + iB) ≤ 768 * (T * p ^ 2) := by
    have hsum : iA + is + it + iB ≤ 2 * T + 2 * p + 8 := by linarith
    have g1 : 128 * T ≤ 128 * (T * p ^ 2) := by
      apply Nat.mul_le_mul_left
      calc T = T * 1 := (Nat.mul_one T).symm
        _ ≤ T * p ^ 2 := Nat.mul_le_mul_left T hp2
    have g2 : 128 * p ≤ 128 * (T * p ^ 2) := by
      apply Nat.mul_le_mul_left
      calc p ≤ p ^ 2 := pbca_le_sq p hp
        _ = 1 * p ^ 2 := by ring
        _ ≤ T * p ^ 2 := Nat.mul_le_mul_right _ hT
    have g3 : 512 ≤ 512 * (T * p ^ 2) := by
      calc (512 : ℕ) = 512 * 1 := by ring
        _ ≤ 512 * (T * p ^ 2) := Nat.mul_le_mul_left _ hTp
    calc 64 * (iA + is + it + iB) ≤ 64 * (2 * T + 2 * p + 8) :=
          Nat.mul_le_mul_left 64 hsum
      _ = 128 * T + 128 * p + 512 := by ring
      _ ≤ 768 * (T * p ^ 2) := by linarith [g1, g2, g3]
  -- the `ts.prod * (2p+8) + ts.prod + 2`-term
  have b3 : 1048576 * (T * (2 * p + 8) + T + 2) ≤ 13631488 * (T * p ^ 2) := by
    have f1 : T * (2 * p + 8) ≤ 10 * (T * p ^ 2) := by
      calc T * (2 * p + 8) ≤ T * (10 * p) := Nat.mul_le_mul_left T (by omega)
        _ = 10 * (T * p) := by ring
        _ ≤ 10 * (T * p ^ 2) := Nat.mul_le_mul_left 10 (Nat.mul_le_mul_left T (pbca_le_sq p hp))
    have f2 : T ≤ T * p ^ 2 := by
      calc T = T * 1 := (Nat.mul_one T).symm
        _ ≤ T * p ^ 2 := Nat.mul_le_mul_left T hp2
    have f3 : 2 ≤ 2 * (T * p ^ 2) := by
      calc (2 : ℕ) = 2 * 1 := by ring
        _ ≤ 2 * (T * p ^ 2) := Nat.mul_le_mul_left 2 hTp
    calc 1048576 * (T * (2 * p + 8) + T + 2)
        ≤ 1048576 * (10 * (T * p ^ 2) + T * p ^ 2 + 2 * (T * p ^ 2)) := by
          apply Nat.mul_le_mul_left
          linarith [f1, f2, f3]
      _ = 13631488 * (T * p ^ 2) := by ring
  -- the two `(D+1) * (p+2)`-terms
  have b4 : 1048576 * ((HvdH.D + 1) * (p + 2)) ≤ 6291456 * HvdH.D * (T * p ^ 2) := by
    have f1 : (HvdH.D + 1) * (p + 2) ≤ 6 * (HvdH.D * p) := by nlinarith
    have f2 : 6 * (HvdH.D * p) ≤ 6 * HvdH.D * (T * p ^ 2) := by
      have hh : HvdH.D * p ≤ HvdH.D * (T * p ^ 2) := by
        calc HvdH.D * p ≤ HvdH.D * p ^ 2 := Nat.mul_le_mul_left _ (pbca_le_sq p hp)
          _ = HvdH.D * (1 * p ^ 2) := by ring
          _ ≤ HvdH.D * (T * p ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hT)
      calc 6 * (HvdH.D * p) ≤ 6 * (HvdH.D * (T * p ^ 2)) := Nat.mul_le_mul_left 6 hh
        _ = 6 * HvdH.D * (T * p ^ 2) := by ring
    calc 1048576 * ((HvdH.D + 1) * (p + 2))
        ≤ 1048576 * (6 * (HvdH.D * p)) := Nat.mul_le_mul_left _ f1
      _ ≤ 1048576 * (6 * HvdH.D * (T * p ^ 2)) := Nat.mul_le_mul_left _ f2
      _ = 6291456 * HvdH.D * (T * p ^ 2) := by ring
  have b5 : 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
      ≤ 37748736 * HvdH.D ^ 2 * (T * p ^ 2) := by
    have f1 : (HvdH.D + 1) * (p + 2) ≤ 6 * (HvdH.D * p) := by nlinarith
    have f2 : (HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2))
        ≤ 36 * (HvdH.D ^ 2 * p ^ 2) := by
      calc (HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2))
          ≤ (6 * (HvdH.D * p)) * (6 * (HvdH.D * p)) := Nat.mul_le_mul f1 f1
        _ = 36 * (HvdH.D ^ 2 * p ^ 2) := by ring
    have f3 : HvdH.D ^ 2 * p ^ 2 ≤ HvdH.D ^ 2 * (T * p ^ 2) :=
      Nat.mul_le_mul_left _ (paDL_mul_one_le hT)
    calc 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
        ≤ 1048576 * (36 * (HvdH.D ^ 2 * p ^ 2)) := Nat.mul_le_mul_left _ f2
      _ = 37748736 * (HvdH.D ^ 2 * p ^ 2) := by ring
      _ ≤ 37748736 * (HvdH.D ^ 2 * (T * p ^ 2)) := Nat.mul_le_mul_left _ f3
      _ = 37748736 * HvdH.D ^ 2 * (T * p ^ 2) := by ring
  -- the `(p+3)^2`-term
  have b6 : 1048576 * ((p + 3) * (p + 3)) ≤ 16777216 * (T * p ^ 2) := by
    have f1 : p + 3 ≤ 4 * p := by omega
    have f2 : (p + 3) * (p + 3) ≤ 16 * p ^ 2 := by
      calc (p + 3) * (p + 3) ≤ (4 * p) * (4 * p) := Nat.mul_le_mul f1 f1
        _ = 16 * p ^ 2 := by ring
    calc 1048576 * ((p + 3) * (p + 3)) ≤ 1048576 * (16 * p ^ 2) := Nat.mul_le_mul_left _ f2
      _ = 16777216 * p ^ 2 := by ring
      _ ≤ 16777216 * (T * p ^ 2) := Nat.mul_le_mul_left _ (paDL_mul_one_le hT)
  have b7 : 1000000 ≤ 1000000 * (T * p ^ 2) := by
    calc (1000000 : ℕ) = 1000000 * 1 := by ring
      _ ≤ 1000000 * (T * p ^ 2) := Nat.mul_le_mul_left _ hTp
  -- sum of the seven terms
  have hsum : 64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
      + 64 * (iA + is + it + iB) + 1048576 * (T * (2 * p + 8) + T + 2)
      + 1048576 * ((HvdH.D + 1) * (p + 2))
      + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
      + 1048576 * ((p + 3) * (p + 3)) + 1000000
      ≤ (14336 * HvdH.D ^ 2 + 768 + 13631488 + 6291456 * HvdH.D + 37748736 * HvdH.D ^ 2
          + 16777216 + 1000000) * (T * p ^ 2) := by
    have hl : 64 * ((X + 1) * ((2 * p + 8) + X.size + 1) * (X.size + 1))
        + 64 * (iA + is + it + iB) + 1048576 * (T * (2 * p + 8) + T + 2)
        + 1048576 * ((HvdH.D + 1) * (p + 2))
        + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
        + 1048576 * ((p + 3) * (p + 3)) + 1000000
        ≤ 14336 * HvdH.D ^ 2 * (T * p ^ 2) + 768 * (T * p ^ 2) + 13631488 * (T * p ^ 2)
          + 6291456 * HvdH.D * (T * p ^ 2) + 37748736 * HvdH.D ^ 2 * (T * p ^ 2)
          + 16777216 * (T * p ^ 2) + 1000000 * (T * p ^ 2) := by
      linarith [b1, b2, b3, b4, b5, b6, b7]
    calc _ ≤ _ := hl
      _ = (14336 * HvdH.D ^ 2 + 768 + 13631488 + 6291456 * HvdH.D + 37748736 * HvdH.D ^ 2
            + 16777216 + 1000000) * (T * p ^ 2) := by ring
  have hc : 14336 * HvdH.D ^ 2 + 768 + 13631488 + 6291456 * HvdH.D + 37748736 * HvdH.D ^ 2
      + 16777216 + 1000000 ≤ 2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5) := by
    norm_num [HvdH.D]
  exact le_trans hsum (Nat.mul_le_mul_right _ hc)

/-- The layout, `isz` and constant terms of the per-axis budget `PABr` (the body of
`Work.Resample.paDRest` of `Submission.Work.Resample.paCostD`, spelled out here so that this module
does not depend on it) are absorbed by the `ts.prod * p^2` term of `HvdH.resCost`. -/
theorem paDRest_body_le {p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts)
    (Kb j : ℕ) (hj : j < HvdH.D) :
    64 * (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) +
        ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
  + 64 * (HvdH.isz (((ts.take j).prod : ℕ) : ℤ) + HvdH.isz ((ss.getD j 0 : ℕ) : ℤ) +
      HvdH.isz ((ts.getD j 0 : ℕ) : ℤ) + HvdH.isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))
  + 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2)
  + 1048576 * ((HvdH.D + 1) * (p + 2))
  + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
  + 1048576 * ((p + 3) * (p + 3))
  + 1000000
    ≤ (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2) := by
  obtain ⟨hT, hX, hXsz, hA, hB, hs, ht⟩ := paDL_layout h j hj
  obtain ⟨-, -, hp100, -, -, -⟩ := h
  have hp : 1 ≤ p := by omega
  have hAisz : HvdH.isz (((ts.take j).prod : ℕ) : ℤ) ≤ ts.prod + 2 := by
    rw [paDL_isz_natCast]
    have hsz : (ts.take j).prod.size ≤ ts.prod :=
      le_trans (Nat.size_le_size hA) (pbca_size_le ts.prod)
    omega
  have hBisz : HvdH.isz (((ss.drop (j + 1)).prod : ℕ) : ℤ) ≤ ts.prod + 2 := by
    rw [paDL_isz_natCast]
    have hsz : (ss.drop (j + 1)).prod.size ≤ ts.prod :=
      le_trans (Nat.size_le_size hB) (pbca_size_le ts.prod)
    omega
  have hsisz : HvdH.isz (((ss.getD j 0 : ℕ)) : ℤ) ≤ p + 2 := by
    rw [paDL_isz_natCast]; omega
  have htisz : HvdH.isz (((ts.getD j 0 : ℕ)) : ℤ) ≤ p + 2 := by
    rw [paDL_isz_natCast]; omega
  exact paDL_arith
    ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1))
    (HvdH.isz (((ts.take j).prod : ℕ) : ℤ))
    (HvdH.isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))
    (HvdH.isz (((ss.getD j 0 : ℕ)) : ℤ))
    (HvdH.isz (((ts.getD j 0 : ℕ)) : ℤ))
    ts.prod p hT hp hX hXsz hAisz hBisz hsisz htisz

end Work.Resample
