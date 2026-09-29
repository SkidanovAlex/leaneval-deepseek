import Mathlib
import Submission.Work.SynFFT.kit2

namespace Work.SynFFT

open HvdH

/-! ## Arithmetic helpers

The three phases of the synthetic-FFT word contribute
`n₁ ≤ K_r (D+1) S₁`, `n₂ ≤ K_f (M r)-polynomial`, `n₃ ≤ K_d (D+1) S₃`, with `S₁, S₃` built out of
`vsz`/`isz` bounds and `D = 1729`, `l = ts.length = D-1`, `M = ts.prod`, `L = log₂(M r)`.
The two lemmas below turn these into the common shape `600 · K · D² M r p (L+1)`, with a huge
constant slack (`1729²`). -/

/-- Bound of the "`S₁`/`S₃`" contributions: with `l ≤ D`, `1 ≤ M`, `1 ≤ r`, `1 ≤ p`, `1 ≤ L`, the
bracket `(M(r(2p+6)+2)+1) + (l(p+3)+1) + (p+3) + (p+3) + c` (`c ≤ 8`) costs at most
`600 D² M r p (L+1)` after multiplication by `D+1`. -/
private lemma arith1 (D l M r p L c : ℕ) (hD : 1 ≤ D) (hl : l ≤ D) (hM : 1 ≤ M) (hr : 1 ≤ r)
    (hp : 1 ≤ p) (hL : 1 ≤ L) (hc : c ≤ 8) :
    (D + 1) * (M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + c)
      ≤ 600 * (D * D * (M * r) * p * (L + 1)) := by
  have hMr : 1 ≤ M * r := Nat.mul_pos (by omega) (by omega)
  have hT : 1 ≤ M * r * p := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hpT : p ≤ M * r * p := le_mul_of_one_le_left (Nat.zero_le p) hMr
  have hMle : M ≤ M * r * p := by
    calc M ≤ M * (r * p) :=
          le_mul_of_one_le_right (Nat.zero_le M) (Nat.mul_pos (by omega) (by omega))
      _ = M * r * p := by ring
  have hlT : l ≤ D * (M * r * p) := le_trans hl (le_mul_of_one_le_right (Nat.zero_le D) hT)
  have hbracket : M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + c
      ≤ (40 + 4 * D) * (M * r * p) := by
    have e : M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + c
        = 2 * (M * r * p) + 6 * (M * r) + 2 * M + (l * p + 3 * l) + 2 * p + (c + 8) := by ring
    rw [e]
    have h2 : 6 * (M * r) ≤ 6 * (M * r * p) :=
      Nat.mul_le_mul_left 6 (le_mul_of_one_le_right (Nat.zero_le _) hp)
    have h3 : 2 * M ≤ 2 * (M * r * p) := Nat.mul_le_mul_left 2 hMle
    have h4 : l * p ≤ D * (M * r * p) := Nat.mul_le_mul hl hpT
    have h5 : 3 * l ≤ 3 * (D * (M * r * p)) := Nat.mul_le_mul_left 3 hlT
    have h6 : 2 * p ≤ 2 * (M * r * p) := Nat.mul_le_mul_left 2 hpT
    have h7 : c + 8 ≤ 16 * (M * r * p) := by
      have hc16 : c + 8 ≤ 16 := by omega
      exact le_trans hc16 (le_mul_of_one_le_right (Nat.zero_le _) hT)
    have e2 : (40 + 4 * D) * (M * r * p) = 40 * (M * r * p) + 4 * D * (M * r * p) := by ring
    rw [e2]
    nlinarith [h2, h3, h4, h5, h6, h7]
  have hnum : (D + 1) * (40 + 4 * D) ≤ 600 * D * D * (L + 1) := by
    have ha : D + 1 ≤ 2 * D := by omega
    have hb : 40 + 4 * D ≤ 44 * D := by omega
    calc (D + 1) * (40 + 4 * D) ≤ (2 * D) * (44 * D) := Nat.mul_le_mul ha hb
      _ = 88 * (D * D) := by ring
      _ ≤ 600 * D * D * (L + 1) := by
          have h2 : 2 ≤ L + 1 := by omega
          have h88 : 88 ≤ 600 * (L + 1) := by omega
          calc 88 * (D * D) ≤ (600 * (L + 1)) * (D * D) := Nat.mul_le_mul_right _ h88
            _ = 600 * D * D * (L + 1) := by ring
  calc (D + 1) * (M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + c)
      ≤ (D + 1) * ((40 + 4 * D) * (M * r * p)) := Nat.mul_le_mul_left (D + 1) hbracket
    _ = ((D + 1) * (40 + 4 * D)) * (M * r * p) := by ring
    _ ≤ (600 * D * D * (L + 1)) * (M * r * p) := Nat.mul_le_mul_right _ hnum
    _ = 600 * (D * D * (M * r) * p * (L + 1)) := by ring

/-- Bound of the middle (`K_f`) phase: with `l ≤ D`, `1 ≤ M`, `1 ≤ r`, `1 ≤ p`, `1 ≤ L` and
`size M ≤ L+1`, the product `(l+1) M (r+1) (p+1) (size M + 2)` (plus `1`) is at most
`600 D² M r p (L+1)`. -/
private lemma arith2 (D l M r p L s : ℕ) (hD : 1 ≤ D) (hl : l ≤ D) (hM : 1 ≤ M) (hr : 1 ≤ r)
    (hp : 1 ≤ p) (hL : 1 ≤ L) (hs : s ≤ L + 1) :
    (l + 1) * M * (r + 1) * (p + 1) * (s + 2) + 1 ≤ 600 * (D * D * (M * r) * p * (L + 1)) := by
  have ha : l + 1 ≤ 2 * D := by omega
  have hb : r + 1 ≤ 2 * r := by omega
  have hc : p + 1 ≤ 2 * p := by omega
  have hd : s + 2 ≤ 2 * (L + 1) := by omega
  have hprod : (l + 1) * M * (r + 1) * (p + 1) * (s + 2)
      ≤ 16 * (D * (M * r) * p * (L + 1)) := by
    calc (l + 1) * M * (r + 1) * (p + 1) * (s + 2)
        ≤ (2 * D) * M * (2 * r) * (2 * p) * (2 * (L + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha (le_refl M)) hb) hc) hd
      _ = 16 * (D * (M * r) * p * (L + 1)) := by ring
  have hY : 0 < D * (M * r) * p * (L + 1) := by positivity
  have h16 : 16 * (D * (M * r) * p * (L + 1)) + 1 ≤ 17 * (D * (M * r) * p * (L + 1)) := by omega
  have h17D : 17 ≤ 600 * D := by omega
  have h17 : 17 * (D * (M * r) * p * (L + 1)) ≤ 600 * (D * D * (M * r) * p * (L + 1)) := by
    calc 17 * (D * (M * r) * p * (L + 1))
        = 17 * (D * ((M * r) * p * (L + 1))) := by ring
      _ ≤ (600 * D) * (D * ((M * r) * p * (L + 1))) := Nat.mul_le_mul_right _ h17D
      _ = 600 * (D * D * (M * r) * p * (L + 1)) := by ring
  calc (l + 1) * M * (r + 1) * (p + 1) * (s + 2) + 1
      ≤ 16 * (D * (M * r) * p * (L + 1)) + 1 := Nat.add_le_add_right hprod 1
    _ ≤ 17 * (D * (M * r) * p * (L + 1)) := h16
    _ ≤ 600 * (D * D * (M * r) * p * (L + 1)) := h17

theorem costArith (Kr Kd Kf : ℕ) (p r : ℕ) (ts : List ℕ) (sgn : ℤ) (us ws' : List (List (ℤ × ℤ))) (n1 n2 n3 : ℕ) (hlen : ts.length = HvdH.D - 1) (hr : 2 ≤ r) (hM : 2 ≤ ts.prod) (h1 : n1 ≤ Kr * (HvdH.D + 1) * (HvdH.vsz (HvdH.rarrVal us) + HvdH.vsz (HvdH.intList ts) + HvdH.isz (p : ℤ) + HvdH.isz (r : ℤ) + HvdH.isz sgn + 3)) (h2 : n2 ≤ Kf * (ts.length + 1) * ts.prod * (r + 1) * (p + 1) * (ts.prod.size + 2) + Kf) (h3 : n3 ≤ Kd * (HvdH.vsz (HvdH.rarrVal ws') + HvdH.vsz (HvdH.intList ts) + HvdH.isz sgn + HvdH.isz (r : ℤ) + HvdH.isz (p : ℤ) + 5)) (hus : HvdH.vsz (HvdH.rarrVal us) ≤ ts.prod * (r * (2 * p + 6) + 2) + 1) (hw' : HvdH.vsz (HvdH.rarrVal ws') ≤ ts.prod * (r * (2 * p + 6) + 2) + 1) (hts : HvdH.vsz (HvdH.intList ts) ≤ ts.length * (p + 3) + 1) (hsz : ts.prod.size ≤ Nat.log 2 (ts.prod * r) + 1) (hpisz : HvdH.isz (p : ℤ) ≤ p + 3) (hrisz : HvdH.isz (r : ℤ) ≤ p + 3) (hsisz : HvdH.isz sgn ≤ 3) : n1 + (n2 + n3) ≤ (2000 * (Kr + Kf + Kd) * HvdH.D * HvdH.D + 2000) * (ts.prod * r) * p * (Nat.log 2 (ts.prod * r) + 1) + (2000 * (Kr + Kf + Kd) * HvdH.D * HvdH.D + 2000) := by
  -- Abbreviate the paper's quantities `M = ∏ tᵢ`, `l = |ts| = D-1`, `L = log₂(M r)`, `D = 1729`.
  set M := ts.prod with hMdef
  set l := ts.length with hldef
  set L := Nat.log 2 (M * r) with hLdef
  set D := HvdH.D with hDdef
  have hM' : 2 ≤ M := by rw [hMdef]; exact hM
  have hsz' : M.size ≤ L + 1 := by rw [hLdef]; exact hsz
  have hD1 : 1 ≤ D := by rw [hDdef]; norm_num [HvdH.D]
  have hl1 : l ≤ D := by omega
  have hM1 : 1 ≤ M := by omega
  have hr1 : 1 ≤ r := by omega
  -- `isz (r : ℤ) = r.size + 2 ≤ p+3` and `r ≥ 2` force `1 ≤ p`.
  have hrsz : r.size ≤ p + 1 := by
    have h := hrisz
    simp only [HvdH.isz] at h
    rw [Int.natAbs_natCast] at h
    omega
  have hr2 : 2 ≤ r.size := by
    by_contra h
    have h1 : r.size ≤ 1 := by omega
    have h2 : r < 2 := by simpa using (Nat.size_le).mp h1
    omega
  have hp1 : 1 ≤ p := by omega
  -- `M r ≥ 4` gives `1 ≤ L`.
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have hMr2 : 2 ≤ M * r := by
      have := Nat.mul_le_mul hM' hr
      omega
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hMr2)
  -- The two `D`-brackets, with `c = 6` and `c = 8`.
  have hS1 : vsz (rarrVal us) + vsz (intList ts) + isz (p : ℤ) + isz (r : ℤ) + isz sgn + 3
      ≤ M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + 3 + 3 :=
    add_le_add
      (add_le_add (add_le_add (add_le_add (add_le_add hus hts) hpisz) hrisz) hsisz) (le_refl 3)
  have hS3 : vsz (rarrVal ws') + vsz (intList ts) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 5
      ≤ M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + 8 := by
    have h := add_le_add (add_le_add (add_le_add (add_le_add hw' hts) hsisz) hrisz) hpisz
    have h5 := add_le_add h (le_refl 5)
    exact le_trans h5 (by omega)
  have hA1 : n1 ≤ 600 * Kr * (D * D * (M * r) * p * (L + 1)) := by
    refine le_trans (le_trans h1 (Nat.mul_le_mul_left (Kr * (D + 1)) hS1)) ?_
    calc Kr * (D + 1) * (M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3)
            + 3 + 3)
        = Kr * ((D + 1) * (M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3)
            + 3 + 3)) := by ring
      _ ≤ Kr * (600 * (D * D * (M * r) * p * (L + 1))) :=
          Nat.mul_le_mul_left Kr (arith1 D l M r p L 6 hD1 hl1 hM1 hr1 hp1 hL1 (by norm_num))
      _ = 600 * Kr * (D * D * (M * r) * p * (L + 1)) := by ring
  have hY2 : (l + 1) * M * (r + 1) * (p + 1) * (M.size + 2) + 1
      ≤ 600 * (D * D * (M * r) * p * (L + 1)) :=
    arith2 D l M r p L M.size hD1 hl1 hM1 hr1 hp1 hL1 hsz'
  have hA2 : n2 ≤ 600 * Kf * (D * D * (M * r) * p * (L + 1)) := by
    refine le_trans h2 ?_
    calc Kf * (l + 1) * M * (r + 1) * (p + 1) * (M.size + 2) + Kf
        = Kf * ((l + 1) * M * (r + 1) * (p + 1) * (M.size + 2) + 1) := by ring
      _ ≤ Kf * (600 * (D * D * (M * r) * p * (L + 1))) := Nat.mul_le_mul_left Kf hY2
      _ = 600 * Kf * (D * D * (M * r) * p * (L + 1)) := by ring
  have hA3 : n3 ≤ 600 * Kd * (D * D * (M * r) * p * (L + 1)) := by
    refine le_trans h3 ?_
    calc Kd * (vsz (rarrVal ws') + vsz (intList ts) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 5)
        ≤ Kd * (M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3) + (p + 3) + 8) :=
          Nat.mul_le_mul_left Kd hS3
      _ ≤ Kd * ((D + 1) * (M * (r * (2 * p + 6) + 2) + 1 + (l * (p + 3) + 1) + (p + 3)
            + (p + 3) + 8)) :=
          Nat.mul_le_mul_left Kd (Nat.le_mul_of_pos_left _ (by omega : 0 < D + 1))
      _ ≤ Kd * (600 * (D * D * (M * r) * p * (L + 1))) :=
          Nat.mul_le_mul_left Kd (arith1 D l M r p L 8 hD1 hl1 hM1 hr1 hp1 hL1 (by norm_num))
      _ = 600 * Kd * (D * D * (M * r) * p * (L + 1)) := by ring
  -- Sum the three bounds and absorb the factor `600` into the `2000`'s.
  have htot : n1 + (n2 + n3)
      ≤ 600 * Kr * (D * D * (M * r) * p * (L + 1))
        + (600 * Kf * (D * D * (M * r) * p * (L + 1))
           + 600 * Kd * (D * D * (M * r) * p * (L + 1))) :=
    add_le_add hA1 (add_le_add hA2 hA3)
  have htot' : n1 + (n2 + n3) ≤ 600 * (Kr + Kf + Kd) * (D * D * (M * r) * p * (L + 1)) := by
    refine le_trans htot ?_
    exact le_of_eq (by ring)
  refine le_trans htot' ?_
  have hstep : 600 * (Kr + Kf + Kd) * (D * D * (M * r) * p * (L + 1))
      ≤ 2000 * (Kr + Kf + Kd) * D * D * ((M * r) * p * (L + 1)) := by
    have h0 : 600 ≤ 2000 := by omega
    have h1 : 600 * ((Kr + Kf + Kd) * (D * D)) ≤ 2000 * ((Kr + Kf + Kd) * (D * D)) :=
      Nat.mul_le_mul_right _ h0
    have h2 := Nat.mul_le_mul_right ((M * r) * p * (L + 1)) h1
    calc 600 * (Kr + Kf + Kd) * (D * D * (M * r) * p * (L + 1))
        = (600 * ((Kr + Kf + Kd) * (D * D))) * ((M * r) * p * (L + 1)) := by ring
      _ ≤ (2000 * ((Kr + Kf + Kd) * (D * D))) * ((M * r) * p * (L + 1)) := h2
      _ = 2000 * (Kr + Kf + Kd) * D * D * ((M * r) * p * (L + 1)) := by ring
  refine le_trans hstep ?_
  have e3 : (2000 * (Kr + Kf + Kd) * D * D + 2000) * (M * r) * p * (L + 1)
      = 2000 * (Kr + Kf + Kd) * D * D * ((M * r) * p * (L + 1))
        + 2000 * ((M * r) * p * (L + 1)) := by ring
  rw [e3]
  have hfin : 2000 * (Kr + Kf + Kd) * D * D * ((M * r) * p * (L + 1))
      ≤ (2000 * (Kr + Kf + Kd) * D * D * ((M * r) * p * (L + 1))
          + 2000 * ((M * r) * p * (L + 1))) + (2000 * (Kr + Kf + Kd) * D * D + 2000) :=
    le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  exact hfin

end Work.SynFFT
