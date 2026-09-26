import Mathlib
import Submission.Work.PTCert.CSAux
import Submission.Work.PTCert.cert1Aux
import Submission.Work.PTCert.rowHelp

/-!
# `PTCert` — the class witnesses of the groups of every row

`Work.PTCert.CS.gclsWitOKAll` feeds the `clsWitOK` component of `ClassSem`
(`Submission/Work/PTCert/classSem.lean`): for every row `r < 18` and every group
`g < ngE r`, the stored 4-letter word `keyWord r g` is a valid class witness for
`keyOf r g` in the witness tree `gclT`.

The kernel checks `Submission.PTCert.C.gcl_ok{r}_{j}` (`gclsOK …`) verify blocks of
`g`-values; here we turn each block into its `g`-range via `List.mem_range'` and glue
them together with `omega`.  No big data structure is evaluated: the only
`decide +kernel` facts are the `18` row codes of `rowHelp.x0cL` and the `18` row
counts `ngL`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Work.PTCert.CS

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

noncomputable section

/-- The predicate that `gclsOK` checks on a block of group indices. -/
def gP (r a b : ℕ) (T : NT) : ℕ → Bool :=
  fun g => clsWitOK canonT [invLk b, invLk a, cG T g / 128, cG T g % 128]
    (w34 gclT (2048 * r + g))

/-- The predicate of the target statement. -/
def gQ (r : ℕ) : ℕ → Bool :=
  fun g => clsWitOK canonT (keyWord r g) (w34 gclT (keyOf r g))

/-- `gP` with the row data of `gclsOK` is `gQ`, whose word is `keyWord`. -/
theorem gP_eq_gQ {r a b : ℕ} {T : NT} (hdiv : cG rowT r / 128 = a)
    (hmod : cG rowT r % 128 = b) (hT : grepTs.getD r (NT.leaf 0) = T) :
    gP r a b T = gQ r := by
  funext g
  simp only [gP, gQ, keyWord, keyOf, grepE, x0c, invLk_eq_invL, hdiv, hmod, hT]

/-- A kernel block check `allL (List.range' c n) p`, read as a range statement. -/
theorem allL_range'_get {c n : ℕ} {p : ℕ → Bool} (h : allL (List.range' c n) p = true) :
    ∀ g, c ≤ g → g < c + n → p g = true := by
  intro g hc hlt
  exact (allL_eq_true _ _).mp h g (List.mem_range'.mpr ⟨g - c, by omega, by omega⟩)

theorem gclsOK_row0 : ∀ g < ngE 0, gQ 0 g = true := by
  have hng : ngE 0 = 18 := by decide +kernel
  have h0 : allL (List.range' 0 18) (gP 0 0 0 grepT0) = true :=
    C.gcl_ok0_0
  have hdiv : cG rowT 0 / 128 = 0 := by decide +kernel
  have hmod : cG rowT 0 % 128 = 0 := by decide +kernel
  have hT : grepTs.getD 0 (NT.leaf 0) = grepT0 := rfl
  have hpq := gP_eq_gQ (r := 0) (a := 0) (b := 0) (T := grepT0) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row1 : ∀ g < ngE 1, gQ 1 g = true := by
  have hng : ngE 1 = 399 := by decide +kernel
  have h0 : allL (List.range' 0 399) (gP 1 0 1 grepT1) = true :=
    C.gcl_ok1_0
  have hdiv : cG rowT 1 / 128 = 0 := by decide +kernel
  have hmod : cG rowT 1 % 128 = 1 := by decide +kernel
  have hT : grepTs.getD 1 (NT.leaf 0) = grepT1 := rfl
  have hpq := gP_eq_gQ (r := 1) (a := 0) (b := 1) (T := grepT1) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row2 : ∀ g < ngE 2, gQ 2 g = true := by
  have hng : ngE 2 = 399 := by decide +kernel
  have h0 : allL (List.range' 0 399) (gP 2 1 1 grepT2) = true :=
    C.gcl_ok2_0
  have hdiv : cG rowT 2 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 2 % 128 = 1 := by decide +kernel
  have hT : grepTs.getD 2 (NT.leaf 0) = grepT2 := rfl
  have hpq := gP_eq_gQ (r := 2) (a := 1) (b := 1) (T := grepT2) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row3 : ∀ g < ngE 3, gQ 3 g = true := by
  have hng : ngE 3 = 215 := by decide +kernel
  have h0 : allL (List.range' 0 215) (gP 3 1 3 grepT3) = true :=
    C.gcl_ok3_0
  have hdiv : cG rowT 3 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 3 % 128 = 3 := by decide +kernel
  have hT : grepTs.getD 3 (NT.leaf 0) = grepT3 := rfl
  have hpq := gP_eq_gQ (r := 3) (a := 1) (b := 3) (T := grepT3) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row4 : ∀ g < ngE 4, gQ 4 g = true := by
  have hng : ngE 4 = 248 := by decide +kernel
  have h0 : allL (List.range' 0 248) (gP 4 1 4 grepT4) = true :=
    C.gcl_ok4_0
  have hdiv : cG rowT 4 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 4 % 128 = 4 := by decide +kernel
  have hT : grepTs.getD 4 (NT.leaf 0) = grepT4 := rfl
  have hpq := gP_eq_gQ (r := 4) (a := 1) (b := 4) (T := grepT4) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row5 : ∀ g < ngE 5, gQ 5 g = true := by
  have hng : ngE 5 = 1332 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 5 1 5 grepT5) = true :=
    C.gcl_ok5_0
  have h1 : allL (List.range' 400 400) (gP 5 1 5 grepT5) = true :=
    C.gcl_ok5_1
  have h2 : allL (List.range' 800 400) (gP 5 1 5 grepT5) = true :=
    C.gcl_ok5_2
  have h3 : allL (List.range' 1200 132) (gP 5 1 5 grepT5) = true :=
    C.gcl_ok5_3
  have hdiv : cG rowT 5 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 5 % 128 = 5 := by decide +kernel
  have hT : grepTs.getD 5 (NT.leaf 0) = grepT5 := rfl
  have hpq := gP_eq_gQ (r := 5) (a := 1) (b := 5) (T := grepT5) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · rcases Nat.lt_or_ge g 800 with hc | hc
    · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h
    · rcases Nat.lt_or_ge g 1200 with hc | hc
      · have h := allL_range'_get h2 g (by omega) (by omega); rwa [hpq] at h
      · have h := allL_range'_get h3 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row6 : ∀ g < ngE 6, gQ 6 g = true := by
  have hng : ngE 6 = 682 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 6 1 7 grepT6) = true :=
    C.gcl_ok6_0
  have h1 : allL (List.range' 400 282) (gP 6 1 7 grepT6) = true :=
    C.gcl_ok6_1
  have hdiv : cG rowT 6 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 6 % 128 = 7 := by decide +kernel
  have hT : grepTs.getD 6 (NT.leaf 0) = grepT6 := rfl
  have hpq := gP_eq_gQ (r := 6) (a := 1) (b := 7) (T := grepT6) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row7 : ∀ g < ngE 7, gQ 7 g = true := by
  have hng : ngE 7 = 399 := by decide +kernel
  have h0 : allL (List.range' 0 399) (gP 7 1 17 grepT7) = true :=
    C.gcl_ok7_0
  have hdiv : cG rowT 7 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 7 % 128 = 17 := by decide +kernel
  have hT : grepTs.getD 7 (NT.leaf 0) = grepT7 := rfl
  have hpq := gP_eq_gQ (r := 7) (a := 1) (b := 17) (T := grepT7) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row8 : ∀ g < ngE 8, gQ 8 g = true := by
  have hng : ngE 8 = 399 := by decide +kernel
  have h0 : allL (List.range' 0 399) (gP 8 1 18 grepT8) = true :=
    C.gcl_ok8_0
  have hdiv : cG rowT 8 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 8 % 128 = 18 := by decide +kernel
  have hT : grepTs.getD 8 (NT.leaf 0) = grepT8 := rfl
  have hpq := gP_eq_gQ (r := 8) (a := 1) (b := 18) (T := grepT8) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row9 : ∀ g < ngE 9, gQ 9 g = true := by
  have hng : ngE 9 = 399 := by decide +kernel
  have h0 : allL (List.range' 0 399) (gP 9 1 19 grepT9) = true :=
    C.gcl_ok9_0
  have hdiv : cG rowT 9 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 9 % 128 = 19 := by decide +kernel
  have hT : grepTs.getD 9 (NT.leaf 0) = grepT9 := rfl
  have hpq := gP_eq_gQ (r := 9) (a := 1) (b := 19) (T := grepT9) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row10 : ∀ g < ngE 10, gQ 10 g = true := by
  have hng : ngE 10 = 399 := by decide +kernel
  have h0 : allL (List.range' 0 399) (gP 10 1 20 grepT10) = true :=
    C.gcl_ok10_0
  have hdiv : cG rowT 10 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 10 % 128 = 20 := by decide +kernel
  have hT : grepTs.getD 10 (NT.leaf 0) = grepT10 := rfl
  have hpq := gP_eq_gQ (r := 10) (a := 1) (b := 20) (T := grepT10) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row11 : ∀ g < ngE 11, gQ 11 g = true := by
  have hng : ngE 11 = 1332 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 11 1 21 grepT11) = true :=
    C.gcl_ok11_0
  have h1 : allL (List.range' 400 400) (gP 11 1 21 grepT11) = true :=
    C.gcl_ok11_1
  have h2 : allL (List.range' 800 400) (gP 11 1 21 grepT11) = true :=
    C.gcl_ok11_2
  have h3 : allL (List.range' 1200 132) (gP 11 1 21 grepT11) = true :=
    C.gcl_ok11_3
  have hdiv : cG rowT 11 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 11 % 128 = 21 := by decide +kernel
  have hT : grepTs.getD 11 (NT.leaf 0) = grepT11 := rfl
  have hpq := gP_eq_gQ (r := 11) (a := 1) (b := 21) (T := grepT11) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · rcases Nat.lt_or_ge g 800 with hc | hc
    · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h
    · rcases Nat.lt_or_ge g 1200 with hc | hc
      · have h := allL_range'_get h2 g (by omega) (by omega); rwa [hpq] at h
      · have h := allL_range'_get h3 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row12 : ∀ g < ngE 12, gQ 12 g = true := by
  have hng : ngE 12 = 1332 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 12 1 23 grepT12) = true :=
    C.gcl_ok12_0
  have h1 : allL (List.range' 400 400) (gP 12 1 23 grepT12) = true :=
    C.gcl_ok12_1
  have h2 : allL (List.range' 800 400) (gP 12 1 23 grepT12) = true :=
    C.gcl_ok12_2
  have h3 : allL (List.range' 1200 132) (gP 12 1 23 grepT12) = true :=
    C.gcl_ok12_3
  have hdiv : cG rowT 12 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 12 % 128 = 23 := by decide +kernel
  have hT : grepTs.getD 12 (NT.leaf 0) = grepT12 := rfl
  have hpq := gP_eq_gQ (r := 12) (a := 1) (b := 23) (T := grepT12) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · rcases Nat.lt_or_ge g 800 with hc | hc
    · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h
    · rcases Nat.lt_or_ge g 1200 with hc | hc
      · have h := allL_range'_get h2 g (by omega) (by omega); rwa [hpq] at h
      · have h := allL_range'_get h3 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row13 : ∀ g < ngE 13, gQ 13 g = true := by
  have hng : ngE 13 = 1332 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 13 1 33 grepT13) = true :=
    C.gcl_ok13_0
  have h1 : allL (List.range' 400 400) (gP 13 1 33 grepT13) = true :=
    C.gcl_ok13_1
  have h2 : allL (List.range' 800 400) (gP 13 1 33 grepT13) = true :=
    C.gcl_ok13_2
  have h3 : allL (List.range' 1200 132) (gP 13 1 33 grepT13) = true :=
    C.gcl_ok13_3
  have hdiv : cG rowT 13 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 13 % 128 = 33 := by decide +kernel
  have hT : grepTs.getD 13 (NT.leaf 0) = grepT13 := rfl
  have hpq := gP_eq_gQ (r := 13) (a := 1) (b := 33) (T := grepT13) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · rcases Nat.lt_or_ge g 800 with hc | hc
    · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h
    · rcases Nat.lt_or_ge g 1200 with hc | hc
      · have h := allL_range'_get h2 g (by omega) (by omega); rwa [hpq] at h
      · have h := allL_range'_get h3 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row14 : ∀ g < ngE 14, gQ 14 g = true := by
  have hng : ngE 14 = 1332 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 14 1 34 grepT14) = true :=
    C.gcl_ok14_0
  have h1 : allL (List.range' 400 400) (gP 14 1 34 grepT14) = true :=
    C.gcl_ok14_1
  have h2 : allL (List.range' 800 400) (gP 14 1 34 grepT14) = true :=
    C.gcl_ok14_2
  have h3 : allL (List.range' 1200 132) (gP 14 1 34 grepT14) = true :=
    C.gcl_ok14_3
  have hdiv : cG rowT 14 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 14 % 128 = 34 := by decide +kernel
  have hT : grepTs.getD 14 (NT.leaf 0) = grepT14 := rfl
  have hpq := gP_eq_gQ (r := 14) (a := 1) (b := 34) (T := grepT14) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · rcases Nat.lt_or_ge g 800 with hc | hc
    · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h
    · rcases Nat.lt_or_ge g 1200 with hc | hc
      · have h := allL_range'_get h2 g (by omega) (by omega); rwa [hpq] at h
      · have h := allL_range'_get h3 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row15 : ∀ g < ngE 15, gQ 15 g = true := by
  have hng : ngE 15 = 712 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 15 1 37 grepT15) = true :=
    C.gcl_ok15_0
  have h1 : allL (List.range' 400 312) (gP 15 1 37 grepT15) = true :=
    C.gcl_ok15_1
  have hdiv : cG rowT 15 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 15 % 128 = 37 := by decide +kernel
  have hT : grepTs.getD 15 (NT.leaf 0) = grepT15 := rfl
  have hpq := gP_eq_gQ (r := 15) (a := 1) (b := 37) (T := grepT15) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row16 : ∀ g < ngE 16, gQ 16 g = true := by
  have hng : ngE 16 = 682 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 16 1 38 grepT16) = true :=
    C.gcl_ok16_0
  have h1 : allL (List.range' 400 282) (gP 16 1 38 grepT16) = true :=
    C.gcl_ok16_1
  have hdiv : cG rowT 16 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 16 % 128 = 38 := by decide +kernel
  have hT : grepTs.getD 16 (NT.leaf 0) = grepT16 := rfl
  have hpq := gP_eq_gQ (r := 16) (a := 1) (b := 38) (T := grepT16) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h

theorem gclsOK_row17 : ∀ g < ngE 17, gQ 17 g = true := by
  have hng : ngE 17 = 1621 := by decide +kernel
  have h0 : allL (List.range' 0 400) (gP 17 1 41 grepT17) = true :=
    C.gcl_ok17_0
  have h1 : allL (List.range' 400 400) (gP 17 1 41 grepT17) = true :=
    C.gcl_ok17_1
  have h2 : allL (List.range' 800 400) (gP 17 1 41 grepT17) = true :=
    C.gcl_ok17_2
  have h3 : allL (List.range' 1200 400) (gP 17 1 41 grepT17) = true :=
    C.gcl_ok17_3
  have h4 : allL (List.range' 1600 21) (gP 17 1 41 grepT17) = true :=
    C.gcl_ok17_4
  have hdiv : cG rowT 17 / 128 = 1 := by decide +kernel
  have hmod : cG rowT 17 % 128 = 41 := by decide +kernel
  have hT : grepTs.getD 17 (NT.leaf 0) = grepT17 := rfl
  have hpq := gP_eq_gQ (r := 17) (a := 1) (b := 41) (T := grepT17) hdiv hmod hT
  intro g hg
  rw [hng] at hg
  rcases Nat.lt_or_ge g 400 with hc | hc
  · have h := allL_range'_get h0 g (by omega) (by omega); rwa [hpq] at h
  · rcases Nat.lt_or_ge g 800 with hc | hc
    · have h := allL_range'_get h1 g (by omega) (by omega); rwa [hpq] at h
    · rcases Nat.lt_or_ge g 1200 with hc | hc
      · have h := allL_range'_get h2 g (by omega) (by omega); rwa [hpq] at h
      · rcases Nat.lt_or_ge g 1600 with hc | hc
        · have h := allL_range'_get h3 g (by omega) (by omega); rwa [hpq] at h
        · have h := allL_range'_get h4 g (by omega) (by omega); rwa [hpq] at h

theorem gclsWitOKAll : ∀ r < 18, ∀ g < Submission.PTCert.G.ngE r,
    Submission.PTCert.clsWitOK Submission.PTCert.D.canonT (Submission.PTCert.G.keyWord r g)
      (Submission.PTCert.w34 Submission.PTCert.D.gclT (Submission.PTCert.G.keyOf r g)) = true := by
  intro r hr g hg
  interval_cases r
  · simpa only [gQ] using gclsOK_row0 g hg
  · simpa only [gQ] using gclsOK_row1 g hg
  · simpa only [gQ] using gclsOK_row2 g hg
  · simpa only [gQ] using gclsOK_row3 g hg
  · simpa only [gQ] using gclsOK_row4 g hg
  · simpa only [gQ] using gclsOK_row5 g hg
  · simpa only [gQ] using gclsOK_row6 g hg
  · simpa only [gQ] using gclsOK_row7 g hg
  · simpa only [gQ] using gclsOK_row8 g hg
  · simpa only [gQ] using gclsOK_row9 g hg
  · simpa only [gQ] using gclsOK_row10 g hg
  · simpa only [gQ] using gclsOK_row11 g hg
  · simpa only [gQ] using gclsOK_row12 g hg
  · simpa only [gQ] using gclsOK_row13 g hg
  · simpa only [gQ] using gclsOK_row14 g hg
  · simpa only [gQ] using gclsOK_row15 g hg
  · simpa only [gQ] using gclsOK_row16 g hg
  · simpa only [gQ] using gclsOK_row17 g hg

end

end Work.PTCert.CS
