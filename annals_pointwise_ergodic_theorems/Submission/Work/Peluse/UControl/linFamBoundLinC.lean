import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs2
import Submission.Work.Peluse.PetLinear.linear_boxnorm_control_paper
import Submission.Work.Peluse.UControl.linFamPerFibre
import Submission.Work.Peluse.UControl.linFamGoodSet
import Submission.Work.Peluse.UControl.linFamZeroParam
import Submission.Work.Peluse.UControl.parBox_card
import Submission.Work.Peluse.UControl.arithIccWindowTransfer

/-!
# `Work.Peluse.UControl.linFamBoundLinC`

The averaged form of the last step of the proof of Peluse's Proposition 3.4, in the
**`Cne`-adaptive** normalisation: the conclusion involves `(2·Cne+1)²` in the constant and the
support is enlarged to `symIcc ((4·Cne+1)·N)` — i.e. no *a priori* bound on the shift-bound
constant `Cne` is needed (unlike `linFamBoundLin`, which requires `Cne ≤ Cne₁`).

## The three geometric regimes

Let `H = ⌊δ'M⌋`, `D₀ = 4Cne+1`, `t = |I_{d-1}|`, `sg = Σ_j |S_j|`,
`gf = ((γ/2)/D₀)²/(1000(t+1))` (the fine-window parameter of Peluse's Lemma 4.10 at the
good-set level `γ/2`).

* **small window** (`gf·M < 1`): then `2H+1 ≤ B/(γC₄)` with `B = 12000(t+1)D₀²`, and the
  zero-parameter bound (`linFamZeroParam`) at `a = 0` alone gives
  `avg ≥ (2H+1)^{-sg}(γ/(D₀·1000+…))^{Kz} ≥ γ^{sg+Kz}C₄^{sg}/((4Cne+1)^{2sg}(4Cne+2)^{Kz})`.
* **large window, `δ' ≤ gf`**: the *target* window `H` is itself admissible as the fine window of
  `linFamPerFibre`; the good set of `linFamGoodSet` gives
  `avg ≥ (γ/12)(((γ/2)/(4Cne+1))²/1000)^{KA}`.
* **large window, `gf < δ'`**: run `linFamPerFibre` at the fine window `⌊gf M⌋` and transfer to `H`
  with the window comparison (`arithIccWindowTransfer`), giving
  `avg ≥ (γ/12)(γC₄/KK)^{2t}(((γ/2)/(4Cne+1))²/1000)^{KA}`, `KK = 8000(t+1)(4Cne+1)²`.

Each of the three lower bounds beats `(γ/(C₄(2Cne+1)²))^{K₄}` for a single data-independent
`(K₄, C₄)`; the `Cne`-bookkeeping is the general arithmetic lemma `cneCompare`
(`(2Cne+1)^{2K₄}` versus `(4Cne+1)^R(4Cne+2)^S`, using `4Cne+1 ≤ 2(2Cne+1)`,
`4Cne+2 = 2(2Cne+1)`, `Cne ≥ 1` and `R+S ≤ 2K₄`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## The pure `γ`/`C₄`/`Cne` arithmetic of the final comparison -/

/-- **The final comparison.**  A lower bound of the shape
`γ^P · const · C₄^Q / ((4·Cne+1)^R (4·Cne+2)^S)` beats `(γ/(C₄(2·Cne+1)²))^{K₄}` as soon as
`P ≤ K₄`, `R+S ≤ 2K₄` and `const·C₄^{Q+K₄} ≥ 2^{R+S}`.  The `Cne`-bookkeeping uses
`4·Cne+1 ≤ 2(2·Cne+1)`, `4·Cne+2 = 2(2·Cne+1)` and `Cne ≥ 1`. -/
private theorem cneCompare {K4 P Q R S : ℕ} {γ C4 : ℝ} {nc : ℕ} {const : ℝ}
    (hK41 : 1 ≤ K4) (hP : P ≤ K4) (hRS : R + S ≤ 2 * K4)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hnc : 1 ≤ nc) (hC41 : 1 ≤ C4)
    (_hconst0 : 0 < const) (hconst : 1 ≤ const * C4 ^ (Q + K4) / 2 ^ (R + S)) :
    (γ / (C4 * (2 * (nc : ℝ) + 1) ^ 2)) ^ K4 ≤
      γ ^ P * const * C4 ^ Q / ((4 * (nc : ℝ) + 1) ^ R * (4 * (nc : ℝ) + 2) ^ S) := by
  have hnc1 : (1:ℝ) ≤ 2 * (nc:ℝ) + 1 := by
    have : (1:ℝ) ≤ (nc:ℝ) := by exact_mod_cast hnc
    linarith
  have hnc0 : (0:ℝ) < 2 * (nc:ℝ) + 1 := lt_of_lt_of_le zero_lt_one hnc1
  have hg : (0:ℝ) < 4 * (nc:ℝ) + 1 := by linarith
  have hg2 : 4 * (nc:ℝ) + 2 = 2 * (2 * (nc:ℝ) + 1) := by ring
  have hg1 : 4 * (nc:ℝ) + 1 ≤ 2 * (2 * (nc:ℝ) + 1) := by linarith
  have hpow : γ ^ K4 ≤ γ ^ P := pow_le_pow_of_le_one hγ0.le hγ1 hP
  have hnum : (4 * (nc:ℝ) + 1) ^ R * (4 * (nc:ℝ) + 2) ^ S ≤
      2 ^ (R + S) * (2 * (nc:ℝ) + 1) ^ (2 * K4) := by
    have h1 : (4 * (nc:ℝ) + 1) ^ R ≤ (2 * (2 * (nc:ℝ) + 1)) ^ R :=
      pow_le_pow_left₀ hg.le hg1 R
    have h2 : (4 * (nc:ℝ) + 2) ^ S ≤ (2 * (2 * (nc:ℝ) + 1)) ^ S := by rw [hg2]
    calc (4 * (nc:ℝ) + 1) ^ R * (4 * (nc:ℝ) + 2) ^ S
        ≤ (2 * (2 * (nc:ℝ) + 1)) ^ R * (2 * (2 * (nc:ℝ) + 1)) ^ S :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 ^ (R + S) * (2 * (nc:ℝ) + 1) ^ (R + S) := by
          rw [mul_pow, mul_pow, pow_add, pow_add]; ring
      _ ≤ 2 ^ (R + S) * (2 * (nc:ℝ) + 1) ^ (2 * K4) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnc1 hRS) (by positivity)
  have hmain : 2 ^ (R + S) ≤ const * C4 ^ (Q + K4) := by
    have h2 : (0:ℝ) < 2 ^ (R + S) := by positivity
    rw [le_div_iff₀ h2] at hconst
    linarith
  have hden1 : (0:ℝ) < C4 ^ K4 * (2 * (nc:ℝ) + 1) ^ (2 * K4) := by
    have h1 : (1:ℝ) ≤ C4 ^ K4 := one_le_pow₀ hC41
    have h2 : (0:ℝ) < (2 * (nc:ℝ) + 1) ^ (2 * K4) := pow_pos hnc0 _
    nlinarith
  have hden2 : (0:ℝ) < (4 * (nc:ℝ) + 1) ^ R * (4 * (nc:ℝ) + 2) ^ S := by
    have h1 : (0:ℝ) < (4 * (nc:ℝ) + 1) ^ R := pow_pos hg _
    have h2 : (0:ℝ) < (4 * (nc:ℝ) + 2) ^ S := by
      have : (0:ℝ) < 4 * (nc:ℝ) + 2 := by linarith
      exact pow_pos this _
    nlinarith
  rw [div_pow, mul_pow, ← pow_mul]
  rw [div_le_div_iff₀ hden1 hden2]
  calc γ ^ K4 * ((4 * (nc:ℝ) + 1) ^ R * (4 * (nc:ℝ) + 2) ^ S)
      ≤ γ ^ K4 * (2 ^ (R + S) * (2 * (nc:ℝ) + 1) ^ (2 * K4)) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ ≤ γ ^ P * (2 ^ (R + S) * (2 * (nc:ℝ) + 1) ^ (2 * K4)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ γ ^ P * (const * C4 ^ (Q + K4) * (2 * (nc:ℝ) + 1) ^ (2 * K4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmain (by positivity)) (by positivity)
    _ = γ ^ P * const * C4 ^ Q * (C4 ^ K4 * (2 * (nc:ℝ) + 1) ^ (2 * K4)) := by
        rw [pow_add]; ring

/-- The geometric-to-flat identity of the small-window regime. -/
private lemma geomA {γ C4 : ℝ} {t sg Kz nc : ℕ} :
    (γ * C4 / (12000 * ((t:ℝ)+1) * (4 * (nc:ℝ) + 1)^2)) ^ sg
        * (γ / (4 * (nc:ℝ) + 2)) ^ Kz
      = γ ^ (sg + Kz) * (1 / (12000 * ((t:ℝ) + 1)) ^ sg) * C4 ^ sg
          / ((4 * (nc:ℝ) + 1) ^ (2*sg) * (4 * (nc:ℝ) + 2) ^ Kz) := by
  rw [div_pow, div_pow, mul_pow, mul_pow, ← pow_mul]
  rw [pow_add]
  field_simp

/-- The geometric-to-flat identity of the "fine window" regime (`δ' ≤ gf`). -/
private lemma geom1 {γ : ℝ} {KA nc : ℕ} :
    (γ / 12) * (((γ / 2) / (4 * (nc:ℝ) + 1)) ^ 2 / 1000) ^ KA
      = γ ^ (1 + 2*KA) * (1 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA)) / (4 * (nc:ℝ) + 1)^(2*KA) := by
  have e1 : (((γ / 2) / (4 * (nc:ℝ) + 1)) ^ 2 / 1000) ^ KA
      = γ ^ (2*KA) / ((2:ℝ)^(2*KA) * ((4 * (nc:ℝ) + 1)^(2*KA) * (1000:ℝ)^KA)) := by
    rw [div_pow, div_pow, div_pow, ← pow_mul, ← pow_mul, div_div, div_pow]
    ring
  rw [e1, pow_add, pow_one]
  field_simp

/-- The geometric-to-flat identity of the "transferred" regime (`gf < δ'`). -/
private lemma geom2 {γ C4 : ℝ} {KA t nc : ℕ} :
    (γ / 12) * (γ * C4 / (8 * 1000 * ((t:ℝ)+1) * (4 * (nc:ℝ) + 1)^2)) ^ (2*t)
      * (((γ / 2) / (4 * (nc:ℝ) + 1)) ^ 2 / 1000) ^ KA
      = γ ^ (1 + 2*t + 2*KA)
          * (1 / (12 * (8 * 1000 * ((t:ℝ) + 1)) ^ (2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA))
          * C4 ^ (2*t) / (4 * (nc:ℝ) + 1) ^ (4*t + 2*KA) := by
  have e1 : (((γ / 2) / (4 * (nc:ℝ) + 1)) ^ 2 / 1000) ^ KA
      = γ ^ (2*KA) / ((2:ℝ)^(2*KA) * ((4 * (nc:ℝ) + 1)^(2*KA) * (1000:ℝ)^KA)) := by
    rw [div_pow, div_pow, div_pow, ← pow_mul, ← pow_mul, div_div, div_pow]
    ring
  rw [e1]
  rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
  rw [show 2 * (2*t) = 4*t from by ring]
  rw [show (1 + 2*t + 2*KA) = 1 + (2*t) + (2*KA) from by ring, pow_add, pow_add, pow_one]
  field_simp
  rw [show (4 * (nc:ℝ) + 1) ^ (4 * t + 2 * KA)
      = (4 * (nc:ℝ) + 1) ^ (4 * t) * (4 * (nc:ℝ) + 1) ^ (2 * KA) from by rw [pow_add]]
  ring

/-- **The averaging step over the good set.**  If `T ⊆ Box` has density `γ/12` and the summand is
at least `L` on `T`, then the average of the summand over `Box` is at least `(γ/12)·L`. -/
private lemma avg_lower {ι : Type*} [DecidableEq ι] {Box T : Finset ι} {γ L : ℝ}
    {F : ι → ℝ} (hTsub : T ⊆ Box) (hTcard : γ / 12 * ((Box.card : ℕ) : ℝ) ≤ (T.card : ℝ))
    (hBoxpos : 0 < ((Box.card : ℕ) : ℝ)) (hL0 : 0 ≤ L) (hfib : ∀ a ∈ T, L ≤ F a)
    (hF0 : ∀ a ∈ Box, 0 ≤ F a) :
    (γ / 12) * L ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, F a := by
  have h1 : ∑ a ∈ T, L ≤ ∑ a ∈ T, F a := Finset.sum_le_sum hfib
  have h2 : (T.card : ℝ) * L ≤ ∑ a ∈ T, F a := by
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  have h3 : ∑ a ∈ T, F a ≤ ∑ a ∈ Box, F a :=
    Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun a ha _ => hF0 a ha)
  have h5 : (γ / 12) * ((Box.card : ℕ) : ℝ) * L ≤ ∑ a ∈ Box, F a := by
    calc (γ / 12) * ((Box.card : ℕ) : ℝ) * L ≤ (T.card : ℝ) * L :=
          mul_le_mul_of_nonneg_right hTcard hL0
      _ ≤ ∑ a ∈ T, F a := h2
      _ ≤ ∑ a ∈ Box, F a := h3
  have h6 : ((Box.card : ℕ) : ℝ)⁻¹ * ((γ / 12) * ((Box.card : ℕ) : ℝ) * L)
      ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, F a :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h7 : ((Box.card : ℕ) : ℝ)⁻¹ * ((γ / 12) * ((Box.card : ℕ) : ℝ) * L) = (γ / 12) * L := by
    field_simp
  linarith [h6, h7]

/-- **The window comparison for the box-norm power along arithmetic progressions** (proved in the
sibling module `Peluse/UControl/arithIccWindowTransfer.lean`; reproduced here as the local name
used by the assembly). -/
private theorem windowTransferAux {k : ℕ} (hk : 2 ≤ k) (d : Fin k → ℤ) {N H' H : ℕ} (f : ℤ → ℂ)
    (h1 : 1 ≤ H') (h2 : H' ≤ H) (hsup : Work.Peluse.SupportIn f N) :
    (((H' : ℝ) / (H : ℝ)) ^ (2 * k)) *
        Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H')
          (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNormPow k (fun i : Fin k => Work.Peluse.arithIcc (d i) H)
          (Work.Peluse.symIcc N) f :=
  arithIccWindowTransfer hk d f h1 h2 hsup

/-! ## The theorem -/

theorem linFamBoundLinC (P : Polynomial ℤ) (D : Work.Peluse.UControl.IdxDatum) :
    ∃ K4 : ℕ, 1 ≤ K4 ∧ ∃ C4 : ℝ, 1 ≤ C4 ∧
      ∀ (N M : ℕ) (f : ℤ → ℂ) (δ' γ : ℝ) (Cne : ℕ)
        (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
        (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
        2 ≤ P.natDegree → 2 ≤ Fintype.card (D.I (P.natDegree - 1)) → 1 ≤ N → 2 ≤ M →
        0 < δ' → 0 < γ → γ ≤ 1 → 1 ≤ Cne →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f N →
        (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
          ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
            |Work.Peluse.UControl.petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
              ≤ (Cne : ℤ) * (N : ℤ)) →
        1 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
        γ ≤ Work.Peluse.UControl.linFamAvg D P.natDegree P.leadingCoeff N M
              (⌊δ' * (M : ℝ)⌋).toNat f b β →
        δ' ≤ γ / C4 →
        (γ / (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4 ≤
          (((D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat).card : ℕ) : ℝ)⁻¹ *
            ∑ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
              Work.Peluse.boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
                (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
                  Work.Peluse.arithIcc (Work.Peluse.UControl.petDir D P.natDegree
                    P.leadingCoeff a i) (⌊δ' * (M : ℝ)⌋).toNat)
                (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f := by
  classical
  by_cases hd : 2 ≤ P.natDegree
  · obtain ⟨KA, hKA1, hPerFibre⟩ := linFamPerFibre D P.leadingCoeff hd
    obtain ⟨Kz, hKz1, hZero⟩ := linFamZeroParam D P.leadingCoeff hd
    let t : ℕ := Fintype.card (D.I (P.natDegree - 1))
    let sg : ℕ := ∑ j : Fin P.natDegree, Fintype.card (D.S j)
    let C4 : ℝ := max 1 (max (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA * (2:ℝ)^(2*KA))
        (max (12 * (8 * 1000 * ((t:ℝ)+1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA
                * (2:ℝ)^(4*t+2*KA))
             (((12000:ℝ) * ((t:ℝ)+1))^sg * (2:ℝ)^(2*sg+Kz))))
    let K4 : ℕ := max 1 (max (1 + 2*KA) (max (1 + 2*t + 2*KA) (sg + Kz)))
    refine ⟨K4, le_max_left _ _, C4, le_max_left _ _, ?_⟩
    intro N M f δ' γ Cne b β hd2 hcard hN hM hδ' hγ hγ1 hCne hfb hfs hsh hH1 hlin hδ'γ
    -- ## the two constants and the elementary facts
    have hK41 : 1 ≤ K4 := le_max_left _ _
    have hC41 : 1 ≤ C4 := le_max_left _ _
    have hC4big1 : 12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA * (2:ℝ)^(2*KA) ≤ C4 :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hC4big2 : 12 * (8 * 1000 * ((t:ℝ)+1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA
        * (2:ℝ)^(4*t+2*KA) ≤ C4 :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hC4bigA : ((12000:ℝ) * ((t:ℝ)+1))^sg * (2:ℝ)^(2*sg+Kz) ≤ C4 :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hPA : sg + Kz ≤ K4 := by
      have h : sg + Kz ≤ max (1+2*KA) (max (1+2*t+2*KA) (sg+Kz)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans h (le_max_right _ _)
    have hPB1 : 1 + 2*KA ≤ K4 := by
      have h : 1 + 2*KA ≤ max (1+2*KA) (max (1+2*t+2*KA) (sg+Kz)) := le_max_left _ _
      exact le_trans h (le_max_right _ _)
    have hPB2 : 1 + 2*t + 2*KA ≤ K4 := by
      have h : 1 + 2*t + 2*KA ≤ max (1+2*KA) (max (1+2*t+2*KA) (sg+Kz)) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      exact le_trans h (le_max_right _ _)
    -- ## abbreviations
    have hcast2 : (((2 * Cne + 1 : ℕ) : ℝ) ^ 2) = (2 * (Cne:ℝ) + 1)^2 := by push_cast; ring
    rw [hcast2]
    let N0 : ℕ := (4 * Cne + 1) * N
    let H : ℕ := (⌊δ' * (M : ℝ)⌋).toNat
    let Box : Finset (D.Idx P.natDegree) := D.parBox P.natDegree H
    let KK : ℝ := 8 * 1000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2
    let gf : ℝ := ((γ/2)/(4*(Cne:ℝ)+1))^2/(1000*((t:ℝ)+1))
    let bn : D.Idx P.natDegree → ℝ := fun a =>
      boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
        (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
          arithIcc (petDir D P.natDegree P.leadingCoeff a i) H) (symIcc N0) f
    show (γ / (C4 * (2 * (Cne:ℝ) + 1) ^ 2)) ^ K4 ≤
      ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a
    have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hMge1 : (1:ℝ) ≤ M := by exact_mod_cast (by omega : 0 < M)
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    have hCne1 : (1:ℝ) ≤ (Cne:ℝ) := by exact_mod_cast hCne
    have hD0pos : (0:ℝ) < 4*(Cne:ℝ)+1 := by linarith
    have htpos : (0:ℝ) < (t:ℝ)+1 := by positivity
    have hN0pos : (0:ℝ) < (N0:ℝ) := by simp only [N0]; push_cast; positivity
    have hN0eq : (N0:ℝ) = (4*(Cne:ℝ)+1) * (N:ℝ) := by simp only [N0]; push_cast; ring
    have hNN0 : (N:ℝ)/(N0:ℝ) = 1/(4*(Cne:ℝ)+1) := by
      rw [hN0eq]; field_simp
    have hNleN0 : N ≤ N0 := by
      simp only [N0]
      calc N = 1 * N := (one_mul N).symm
        _ ≤ (4 * Cne + 1) * N := Nat.mul_le_mul_right N (by omega)
    have hfs0 : SupportIn f N0 := hfs.mono hNleN0
    have hBox0 : (0 : D.Idx P.natDegree) ∈ Box := by
      show (0 : D.Idx P.natDegree) ∈ D.parBox P.natDegree H
      rw [IdxDatum.mem_parBox]; intro j s; simp
    have hBoxpos : (0:ℝ) < ((Box.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨0, hBox0⟩
    have hbn0 : ∀ a : D.Idx P.natDegree, 0 ≤ bn a :=
      fun a => Work.Peluse.BoxNormDilation.boxNormPow_nonneg _ _ _ _
    have hboxcard : ((Box.card : ℕ) : ℝ) = (2*(H:ℝ)+1)^sg := by
      rw [show Box = D.parBox P.natDegree H from rfl, parBox_card]
      push_cast; ring
    have hHcast : (H:ℝ) ≤ δ' * (M:ℝ) := by
      have h2 : (⌊δ' * (M : ℝ)⌋ : ℝ) ≤ δ' * (M:ℝ) := Int.floor_le _
      have h3 : ((⌊δ' * (M : ℝ)⌋).toNat : ℝ) = (⌊δ' * (M : ℝ)⌋ : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))]
      rw [show H = (⌊δ' * (M : ℝ)⌋).toNat from rfl, h3]
      exact h2
    have hHpos : (0:ℝ) < H := by
      have : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
      linarith
    have hgfpos : 0 < gf := by simp only [gf]; positivity
    have hgfval : gf = γ^2 / (4*(4*(Cne:ℝ)+1)^2 * (1000*((t:ℝ)+1))) := by
      simp only [gf]; rw [div_pow]; field_simp; ring
    have hgfmul : gf * (1000*((t:ℝ)+1)) = ((γ/2)/(4*(Cne:ℝ)+1))^2 := by
      simp only [gf]; field_simp
    -- the good set of `linFamGoodSet` is used in the large-window regime
    by_cases hsmall : gf * (M:ℝ) < 1
    · -- ================= Case A: small window =================
      have hMlt : (M:ℝ) < 4000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 / γ^2 := by
        have h2 : (M:ℝ) < 1/gf := by rw [lt_div_iff₀ hgfpos]; linarith [hsmall]
        rw [hgfval] at h2
        rw [one_div, inv_div] at h2
        rwa [show 4 * (4*(Cne:ℝ)+1)^2 * (1000*((t:ℝ)+1)) / γ^2
            = 4000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 / γ^2 from by ring] at h2
      have h2Hle : 2*(H:ℝ)+1 ≤ 12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 / (γ*C4) := by
        have hC4pos : 0 < C4 := lt_of_lt_of_le zero_lt_one hC41
        have h1 : (H:ℝ) ≤ (γ/C4)*(M:ℝ) := by
          calc (H:ℝ) ≤ δ'*(M:ℝ) := hHcast
            _ ≤ (γ/C4)*(M:ℝ) := mul_le_mul_of_nonneg_right hδ'γ hMpos.le
        have h2 : 2*(H:ℝ)+1 ≤ 3*(H:ℝ) := by
          have h1H : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH1
          linarith
        have h3 : (γ/C4)*(M:ℝ) ≤ (γ/C4)*(4000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 / γ^2) :=
          (mul_lt_mul_of_pos_left hMlt (by positivity : (0:ℝ) < γ/C4)).le
        calc 2*(H:ℝ)+1 ≤ 3*(H:ℝ) := h2
          _ ≤ 3*((γ/C4)*(M:ℝ)) := by linarith [h1]
          _ ≤ 3*((γ/C4)*(4000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 / γ^2)) := by linarith [h3]
          _ = 12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 / (γ*C4) := by
              field_simp; ring
      -- the zero-parameter bound at `a = 0`
      have hsh0 : ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))),
          ∀ y ∈ Finset.Icc 1 M,
          |petDir D P.natDegree P.leadingCoeff (0:D.Idx P.natDegree) i * (y:ℤ) + β 0 i|
            ≤ (Cne:ℤ)*(N:ℤ) := fun i y hy => hsh 0 hBox0 i y hy
      have hZ := hZero N M H f Cne γ b β hcard hN hM hCne hH1 hγ hγ1 hfb hfs hsh0 hlin
      have hbn0' : (γ / (4*(Cne:ℝ)+2))^Kz ≤ ∑ a ∈ Box, bn a := by
        refine le_trans hZ ?_
        exact Finset.single_le_sum (fun a _ => hbn0 a) hBox0
      have hstep2 : (γ * C4 / (12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2))^sg
            * (γ / (4*(Cne:ℝ)+2))^Kz
          ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a := by
        have hBpos : 0 < 12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 := by positivity
        have h1 : ((Box.card : ℕ) : ℝ)⁻¹ * (γ / (4*(Cne:ℝ)+2))^Kz
            ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a :=
          mul_le_mul_of_nonneg_left hbn0' (by positivity)
        have h2H0 : 0 < 2*(H:ℝ)+1 := by positivity
        have hKle : γ * C4 / (12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2) ≤ 1/(2*(H:ℝ)+1) := by
          rw [div_le_div_iff₀ (by positivity) h2H0, one_mul]
          have h9 := mul_le_mul_of_nonneg_left h2Hle (by positivity : (0:ℝ) ≤ γ*C4)
          have h10 : γ*C4*(12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2/(γ*C4))
              = 12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2 := by field_simp
          linarith [h9, h10]
        have h3 : (γ * C4 / (12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2))^sg
            ≤ ((Box.card : ℕ) : ℝ)⁻¹ := by
          have h4 := pow_le_pow_left₀ (by positivity) hKle sg
          rwa [one_div, inv_pow, ← hboxcard] at h4
        calc (γ * C4 / (12000 * ((t:ℝ)+1) * (4*(Cne:ℝ)+1)^2))^sg
              * (γ / (4*(Cne:ℝ)+2))^Kz
            ≤ ((Box.card : ℕ) : ℝ)⁻¹ * (γ / (4*(Cne:ℝ)+2))^Kz :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a := h1
      have havg : γ ^ (sg + Kz) * (1 / (12000 * ((t:ℝ) + 1)) ^ sg) * C4 ^ sg
            / ((4 * (Cne:ℝ) + 1) ^ (2*sg) * (4 * (Cne:ℝ) + 2) ^ Kz)
          ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a := by
        rw [← geomA (t := t)]
        exact hstep2
      have hconst : 1 ≤ (1 / (12000 * ((t:ℝ) + 1)) ^ sg) * C4 ^ (sg + K4)
          / 2 ^ (2*sg + Kz) := by
        have h1 : (1 / (12000 * ((t:ℝ) + 1)) ^ sg) * C4 ^ (sg + K4)
            = C4 ^ (sg + K4) / (12000 * ((t:ℝ) + 1)) ^ sg := by ring
        rw [h1, le_div_iff₀ (by positivity), one_mul]
        have h2 : C4 ≤ C4 ^ (sg + K4) := by
          calc C4 = C4 ^ 1 := (pow_one C4).symm
            _ ≤ C4 ^ (sg + K4) := pow_le_pow_right₀ hC41 (by omega)
        calc 2 ^ (2*sg + Kz) = (12000 * ((t:ℝ) + 1))^sg * (2:ℝ)^(2*sg+Kz)
              / (12000 * ((t:ℝ) + 1))^sg := by field_simp
          _ ≤ C4 / (12000 * ((t:ℝ) + 1))^sg := by
              refine div_le_div_of_nonneg_right hC4bigA (by positivity)
          _ ≤ C4 ^ (sg + K4) / (12000 * ((t:ℝ) + 1))^sg :=
              div_le_div_of_nonneg_right h2 (by positivity)
      have hRS : 2*sg + Kz ≤ 2*K4 := by omega
      have hcmp := cneCompare (K4 := K4) (P := sg+Kz) (Q := sg) (R := 2*sg) (S := Kz)
        (γ := γ) (C4 := C4) (nc := Cne) (const := 1 / (12000 * ((t:ℝ) + 1)) ^ sg)
        hK41 hPA hRS hγ hγ1 hCne hC41 (by positivity) hconst
      exact le_trans hcmp havg
    · -- ================= Case B: large window =================
      push_neg at hsmall
      obtain ⟨T, hTsub, hTcard, hTfib⟩ :=
        linFamGoodSet D P.leadingCoeff hd N M H f Cne γ b β hcard hN hM hCne hγ hγ1 hfb hfs hlin
      have hTne : T.Nonempty := by
        refine Finset.card_pos.mp ?_
        have h1 : (0:ℝ) < (γ / 12) * ((Box.card : ℕ) : ℝ) := by
          have : (0:ℝ) < (Box.card:ℕ) := hBoxpos
          nlinarith [hγ]
        exact_mod_cast lt_of_lt_of_le h1 hTcard
      -- the per-fibre transfer inequality `((γ/2)/(4Cne+1))² ≤ (N/N0)²λ_a²`
      have hquad : ∀ a ∈ T,
          ((γ/2)/(4*(Cne:ℝ)+1))^2 ≤ ((N:ℝ)/(N0:ℝ))^2
            * (linFib D P.natDegree P.leadingCoeff N M f b β a)^2 := by
        intro a ha
        have hlam : γ/2 ≤ linFib D P.natDegree P.leadingCoeff N M f b β a := hTfib a ha
        have hlam0 : (0:ℝ) ≤ γ/2 := by linarith
        have hquad' : (γ/2)^2 ≤ (linFib D P.natDegree P.leadingCoeff N M f b β a)^2 :=
          pow_le_pow_left₀ hlam0 hlam 2
        rw [hNN0]
        calc ((γ/2)/(4*(Cne:ℝ)+1))^2 = (γ/2)^2 * (1/(4*(Cne:ℝ)+1)^2) := by
              rw [div_pow, div_eq_mul_inv, one_div]
          _ ≤ (linFib D P.natDegree P.leadingCoeff N M f b β a)^2
                * (1/(4*(Cne:ℝ)+1)^2) :=
              mul_le_mul_of_nonneg_right hquad' (by positivity)
          _ = (1/(4*(Cne:ℝ)+1))^2 * (linFib D P.natDegree P.leadingCoeff N M f b β a)^2 := by
              have h4 : (1/(4*(Cne:ℝ)+1))^2 = ((4*(Cne:ℝ)+1)^2)⁻¹ := by
                rw [one_div, inv_pow]
              rw [h4]; ring
      by_cases hgfge : δ' ≤ gf
      · -- ============ Case B1: the target window is itself fine ============
        have hHfeq : H = ⌊((H:ℝ)/(M:ℝ)) * (M:ℝ)⌋.toNat := by
          have h1 : (H:ℝ)/(M:ℝ) * (M:ℝ) = (H:ℝ) := by field_simp
          rw [h1, Int.floor_natCast, Int.toNat_natCast]
        have hfib : ∀ a ∈ T, (((γ/2)/(4*(Cne:ℝ)+1))^2/1000)^KA ≤ bn a := by
          intro a ha
          have haBox : a ∈ Box := hTsub ha
          have hγ'pos : 0 < (H:ℝ)/(M:ℝ) := by positivity
          have hgauge : ((H:ℝ)/(M:ℝ)) * (1000*((t:ℝ)+1))
              ≤ ((N:ℝ)/(N0:ℝ))^2 * (linFib D P.natDegree P.leadingCoeff N M f b β a)^2 := by
            have h1 : (H:ℝ)/(M:ℝ) ≤ δ' := by rw [div_le_iff₀ hMpos]; linarith [hHcast]
            have h2 : (H:ℝ)/(M:ℝ) * (1000*((t:ℝ)+1)) ≤ ((γ/2)/(4*(Cne:ℝ)+1))^2 := by
              calc (H:ℝ)/(M:ℝ) * (1000*((t:ℝ)+1)) ≤ δ' * (1000*((t:ℝ)+1)) :=
                    mul_le_mul_of_nonneg_right h1 (by positivity)
                _ ≤ gf * (1000*((t:ℝ)+1)) := mul_le_mul_of_nonneg_right hgfge (by positivity)
                _ = ((γ/2)/(4*(Cne:ℝ)+1))^2 := hgfmul
            exact le_trans h2 (hquad a ha)
          have hper := hPerFibre N M f Cne a b β H ((H:ℝ)/(M:ℝ)) hcard hN hM hCne hfb hfs
            (fun i y hy => hsh a haBox i y hy) hγ'pos hHfeq hH1 hgauge
          refine le_trans ?_ hper
          refine pow_le_pow_left₀ (by positivity) ?_ KA
          exact div_le_div_of_nonneg_right (hquad a ha) (by norm_num)
        have havg : (γ/12) * (((γ/2)/(4*(Cne:ℝ)+1))^2/1000)^KA
            ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a :=
          avg_lower hTsub hTcard hBoxpos (by positivity) hfib (fun a _ => hbn0 a)
        have hconst : 1 ≤ (1 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA)) * C4 ^ (0 + K4)
            / 2 ^ (2*KA + 0) := by
          have hconst' : 1 ≤ (1 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA)) * C4 ^ K4
              / 2 ^ (2*KA) := by
            have h1 : (1 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA)) * C4 ^ K4
                = C4 ^ K4 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) := by ring
            rw [h1, le_div_iff₀ (by positivity), one_mul]
            calc 2 ^ (2*KA)
                = 12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA * (2:ℝ)^(2*KA)
                    / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) := by field_simp
              _ ≤ C4 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) :=
                  div_le_div_of_nonneg_right hC4big1 (by positivity)
              _ ≤ C4 ^ K4 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) := by
                  refine div_le_div_of_nonneg_right ?_ (by positivity)
                  calc C4 = C4 ^ 1 := (pow_one C4).symm
                    _ ≤ C4 ^ K4 := pow_le_pow_right₀ hC41 hK41
          simpa using hconst'
        have hRS : 2*KA ≤ 2*K4 := by omega
        have hcmp := cneCompare (K4 := K4) (P := 1+2*KA) (Q := 0) (R := 2*KA) (S := 0)
          (γ := γ) (C4 := C4) (nc := Cne) (const := 1 / (12 * (2:ℝ)^(2*KA) * (1000:ℝ)^KA))
          hK41 hPB1 hRS hγ hγ1 hCne hC41 (by positivity) hconst
        simp only [pow_zero, mul_one] at hcmp
        rw [geom1 (KA := KA) (nc := Cne)] at havg
        exact le_trans hcmp havg
      · -- ============ Case B2: transfer from the fine window `⌊gf M⌋` ============
        push_neg at hgfge
        have ht2 : 2 ≤ t := hcard
        have hHf1 : 1 ≤ (⌊gf*(M:ℝ)⌋).toNat := by
          rw [Int.le_toNat (Int.floor_nonneg.mpr (by positivity))]
          rw [Int.le_floor]; push_cast; exact hsmall
        have hHfH : (⌊gf*(M:ℝ)⌋).toNat ≤ H := by
          show (⌊gf*(M:ℝ)⌋).toNat ≤ (⌊δ'*(M:ℝ)⌋).toNat
          rw [Int.toNat_le, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))]
          exact Int.floor_mono (le_of_lt (mul_lt_mul_of_pos_right hgfge hMpos))
        have hHf_ge : gf*(M:ℝ)/2 ≤ ((⌊gf*(M:ℝ)⌋).toNat : ℝ) := by
          rw [show ((⌊gf*(M:ℝ)⌋).toNat : ℝ) = (⌊gf*(M:ℝ)⌋ : ℝ) from
            by rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))]]
          have h5 : (1:ℝ) ≤ gf*(M:ℝ) := hsmall
          have h6 : (1:ℝ) ≤ (⌊gf*(M:ℝ)⌋ : ℝ) := by
            have h : ((1:ℤ) : ℝ) ≤ gf*(M:ℝ) := by exact_mod_cast hsmall
            exact_mod_cast (Int.le_floor.mpr h)
          by_cases hx : (2:ℝ) ≤ gf*(M:ℝ)
          · have h7 : gf*(M:ℝ) - 1 < (⌊gf*(M:ℝ)⌋ : ℝ) := by
              have := Int.lt_floor_add_one (gf*(M:ℝ))
              linarith
            linarith
          · linarith
        have h6 : γ^2*(M:ℝ) ≤ ((⌊gf*(M:ℝ)⌋).toNat : ℝ) * KK := by
          have h7 : γ^2 * (M:ℝ) = gf * (M:ℝ) / 2 * KK := by
            rw [hgfval]; simp only [KK]; field_simp; ring
          rw [h7]
          exact mul_le_mul_of_nonneg_right hHf_ge (by positivity)
        have hrat : (γ*C4/KK)^(2*t) ≤ (((⌊gf*(M:ℝ)⌋).toNat:ℝ)/(H:ℝ))^(2*t) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          rw [div_le_div_iff₀ (by positivity) hHpos]
          have h9 : C4*δ' ≤ γ := by
            have h10 := (le_div_iff₀ (by positivity : (0:ℝ) < C4)).mp hδ'γ
            linarith
          have h11 : γ*C4*(H:ℝ) ≤ γ*C4*(δ'*(M:ℝ)) :=
            mul_le_mul_of_nonneg_left hHcast (by positivity)
          have h12 : γ*C4*(H:ℝ) ≤ γ*γ*(M:ℝ) := by
            have h14 : γ * C4 * (δ' * (M:ℝ)) ≤ γ * γ * (M:ℝ) := by
              calc γ*C4*(δ'*(M:ℝ)) = (C4*δ')*(γ*(M:ℝ)) := by ring
                _ ≤ γ*(γ*(M:ℝ)) := mul_le_mul_of_nonneg_right h9 (by positivity)
                _ = γ*γ*(M:ℝ) := by ring
            linarith [h11, h14]
          nlinarith [h12, h6, hC41, hMpos.le]
        have hfib : ∀ a ∈ T, (γ*C4/KK)^(2*t) * (((γ/2)/(4*(Cne:ℝ)+1))^2/1000)^KA ≤ bn a := by
          intro a ha
          have haBox : a ∈ Box := hTsub ha
          have hgauge : gf * (1000*((t:ℝ)+1))
              ≤ ((N:ℝ)/(N0:ℝ))^2 * (linFib D P.natDegree P.leadingCoeff N M f b β a)^2 := by
            rw [hgfmul]
            exact hquad a ha
          have hper := hPerFibre N M f Cne a b β ((⌊gf*(M:ℝ)⌋).toNat) gf hcard hN hM hCne
            hfb hfs (fun i y hy => hsh a haBox i y hy) hgfpos rfl hHf1 hgauge
          have htr := windowTransferAux ht2
            (fun i : Fin t => petDir D P.natDegree P.leadingCoeff a i) f hHf1 hHfH hfs0
          refine le_trans ?_ htr
          calc (γ*C4/KK)^(2*t) * (((γ/2)/(4*(Cne:ℝ)+1))^2/1000)^KA
              ≤ (((⌊gf*(M:ℝ)⌋).toNat:ℝ)/(H:ℝ))^(2*t)
                * (((N:ℝ)/(N0:ℝ))^2
                    * (linFib D P.natDegree P.leadingCoeff N M f b β a)^2/1000)^KA :=
                mul_le_mul hrat
                  (pow_le_pow_left₀ (by positivity)
                    (div_le_div_of_nonneg_right (hquad a ha) (by norm_num)) KA)
                  (by positivity) (by positivity)
            _ ≤ (((⌊gf*(M:ℝ)⌋).toNat:ℝ)/(H:ℝ))^(2*t)
                * boxNormPow t
                    (fun i : Fin t => arithIcc (petDir D P.natDegree P.leadingCoeff a i)
                      ((⌊gf*(M:ℝ)⌋).toNat)) (symIcc N0) f :=
                mul_le_mul_of_nonneg_left hper (by positivity)
        have havg : (γ/12) * (γ*C4/KK)^(2*t) * (((γ/2)/(4*(Cne:ℝ)+1))^2/1000)^KA
            ≤ ((Box.card : ℕ) : ℝ)⁻¹ * ∑ a ∈ Box, bn a := by
          have h := avg_lower hTsub hTcard hBoxpos (by positivity) hfib (fun a _ => hbn0 a)
          simpa only [mul_assoc] using h
        have hconst : 1 ≤ (1 / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA)
              * (1000:ℝ)^KA)) * C4 ^ (2*t + K4) / 2 ^ (4*t + 2*KA + 0) := by
          have hconst' : 1 ≤ (1 / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA)
                * (1000:ℝ)^KA)) * C4 ^ (2*t + K4) / 2 ^ (4*t + 2*KA) := by
            have h1 : (1 / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA))
                  * C4 ^ (2*t + K4)
                = C4 ^ (2*t + K4)
                  / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) := by ring
            rw [h1, le_div_iff₀ (by positivity), one_mul]
            calc 2 ^ (4*t + 2*KA)
                = 12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA
                    * (2:ℝ)^(4*t+2*KA)
                  / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) := by
                  field_simp
              _ ≤ C4 / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) :=
                  div_le_div_of_nonneg_right hC4big2 (by positivity)
              _ ≤ C4 ^ (2*t + K4)
                    / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA) := by
                  refine div_le_div_of_nonneg_right ?_ (by positivity)
                  calc C4 = C4 ^ 1 := (pow_one C4).symm
                    _ ≤ C4 ^ (2*t + K4) := pow_le_pow_right₀ hC41 (by omega)
          simpa using hconst'
        have hRS : 4*t + 2*KA + 0 ≤ 2*K4 := by omega
        have hcmp := cneCompare (K4 := K4) (P := 1+2*t+2*KA) (Q := 2*t) (R := 4*t+2*KA) (S := 0)
          (γ := γ) (C4 := C4) (nc := Cne)
          (const := 1 / (12 * (8 * 1000 * ((t:ℝ) + 1))^(2*t) * (2:ℝ)^(2*KA) * (1000:ℝ)^KA))
          hK41 hPB2 hRS hγ hγ1 hCne hC41 (by positivity) hconst
        simp only [pow_zero, mul_one] at hcmp
        rw [geom2 (KA := KA) (t := t) (nc := Cne)] at havg
        exact le_trans hcmp havg
  · -- the degenerate case `¬ 2 ≤ P.natDegree`
    refine ⟨1, le_refl 1, 1, le_refl 1, ?_⟩
    intro N M f δ' γ Cne b β hdeg
    exact absurd hdeg hd

end

end Work.Peluse.UControl
