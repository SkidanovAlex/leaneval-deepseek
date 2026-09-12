import Mathlib
import Submission.Szemeredi.Removal.CountLemma
import Submission.Commons.Analysis.Real.exists_pow_log_div_sqrt_le


/-!
# The counting lemma for a general growth function

`Submission/Szemeredi/Removal/CountLemma.lean` proves the counting lemma
(Tao, Lemma `count-lemma`) with the concrete growth function `F n = 2^n`.
For the hypergraph removal lemma we need a *rapidly growing* growth function:
the removal step produces a factor equal to the number of atoms `2^{M_j}` times the
discrepancy `1/log F(M_j)`, so `F` must satisfy `log F(x) ≫ 2^x`.

This file generalises the counting lemma's lower bound to an arbitrary growth
function `F` (with the smallness hypotheses stated in terms of `log (F x)` and
`√(F x)`), and then provides the triple-exponential function
`Ffast n = 2^(2^(2^n))` together with the threshold that discharges those
hypotheses.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- **The counting lemma** (Tao, `count-lemma`), lower bound form, for a general growth
function `F`. -/
theorem counting_lemma_lower_F
    {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hFgrow : ∀ n, n + 1 ≤ F n) (hFmono : Monotone F)
    (hlog : ∀ e ∈ Hall Hd, 1 ≤ Real.log (F (M e.card)))
    (hempty : A ∅ = Finset.univ)
    (hTh : ThetaC F M d (Hall Hd).card ≤ 1 / 2)
    (hX : XC F M d (Hall Hd).card * rhoC F M
      ≤ (1 / 4) * (1 / LupC F M) ^ (Hall Hd).card) :
    (1 / 4) * (1 / LupC F M) ^ (Hall Hd).card
      ≤ Cnt (V := V) (id : ι → ι) (Hall Hd)
          (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj) := by
  classical
  have hFpos : ∀ n, 1 ≤ F n := fun n => le_trans (by omega) (hFgrow n)
  have hFposR : ∀ n, (0 : ℝ) < (F n : ℝ) := fun n =>
    (by have h := hFpos n; exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one h) :
      (0 : ℝ) < (F n : ℝ))
  have hgen := gencount (V := V) hHd hBd hAtom hGood hR (hFpos (M 0)) hFmono hFgrow hlog hempty
    (id : ι → ι) (Hall Hd) (isBundle_id Hd) (fun g hg => mem_Hall_card_le hHd hg)
  have hP0 : (0 : ℝ) ≤ ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g :=
    Finset.prod_nonneg (fun g _ => pOf_nonneg A _)
  have hLuppos : (0 : ℝ) < LupC F M := by
    unfold LupC
    have h1 : (0 : ℝ) ≤ Real.log (F (M 0)) :=
      Real.log_nonneg (by exact_mod_cast hFpos (M 0))
    linarith
  have hPL : (1 / LupC F M) ^ (Hall Hd).card ≤ ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g := by
    have hManti := hR.M_anti hFgrow
    have h1 : ∀ g ∈ Hall Hd, (1 / LupC F M) ≤ pgOf A (id : ι → ι) g := by
      intro g hg
      have hgc : g.card ≤ d := mem_Hall_card_le hHd hg
      have heR : RgOf F M (id : ι → ι) g = (F (M g.card) : ℝ) := by
        unfold RgOf
        rw [Finset.image_id]
      have hlogg : 1 ≤ Real.log (RgOf F M (id : ι → ι) g) := by
        rw [heR]; exact hlog g hg
      have h2 := gchyp_h2 (V := V) (Md := Md) (M := M) (F := F) (B := B) (B' := B')
        (A := A) (d := d) (Hd := Hd) (Bd := Bd) hGood (isBundle_id Hd) hg hlogg
      refine le_trans (one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hlogg) ?_) h2
      show Real.log (RgOf F M (id : ι → ι) g) ≤ Real.log (F (M 0)) + 2
      rw [heR]
      have h3 : M g.card ≤ M 0 := hManti 0 g.card (Nat.zero_le _) hgc
      have hle : Real.log ((F (M g.card) : ℕ) : ℝ) ≤ Real.log ((F (M 0) : ℕ) : ℝ) :=
        Real.log_le_log (hFposR (M g.card)) (by exact_mod_cast hFmono h3)
      linarith
    calc (1 / LupC F M) ^ (Hall Hd).card
        = ∏ g ∈ Hall Hd, (1 / LupC F M) := by rw [Finset.prod_const]
      _ ≤ ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g :=
          Finset.prod_le_prod (fun g _ => le_of_lt (one_div_pos.mpr hLuppos)) (fun g hg => h1 g hg)
  have hCnt : (1 / 2) * (∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g)
      - XC F M d (Hall Hd).card * rhoC F M
      ≤ Cnt (V := V) (id : ι → ι) (Hall Hd)
          (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj) := by
    have h2 : ThetaC F M d (Hall Hd).card * (∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g)
        ≤ (1 / 2) * (∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g) :=
      mul_le_mul_of_nonneg_right hTh hP0
    have h3 := neg_abs_le (Cnt (V := V) (id : ι → ι) (Hall Hd)
      (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj)
        - ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g)
    linarith [hgen]
  linarith [hPL, hX]

/-- **The counting lemma with the growth conditions discharged**, for a general growth
function `F`: all the smallness hypotheses follow from `log (F x)` and `√(F x)` being
eventually small/large, which is what `T` encodes. -/
theorem counting_lemma_lower_growth_F
    {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {F : ℕ → ℕ} {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ}
    {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M F A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md F B B' M)
    (hFgrow : ∀ n, n + 1 ≤ F n) (hFmono : Monotone F)
    (hlog : ∀ e ∈ Hall Hd, 1 ≤ Real.log (F (M e.card)))
    (hempty : A ∅ = Finset.univ)
    (hd : 1 ≤ d) (hMd3 : 3 ≤ M d) (hManti : ∀ D ≤ d, M d ≤ M D)
    {T : ℕ} (hT : T ≤ M d) (hT8 : 8 ≤ T)
    {a : ℝ} (ha0 : 0 < a)
    (hTa : ∀ x : ℕ, T ≤ x → (Real.log (F x)) ^ (2 ^ d * (Hall Hd).card)
        / Real.sqrt (F x : ℝ) ≤ a)
    {b : ℝ} (hb0 : 0 < b)
    (hTb : ∀ x : ℕ, T ≤ x → (Real.log (F x)) ^ (2 ^ d * (Hall Hd).card)
        / Real.sqrt (F x : ℝ) ≤ b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card))
    (hTc : ∀ x : ℕ, T ≤ x → 4 * Xbd d (Hall Hd).card * (2 : ℝ) ^ (Hall Hd).card
        * (b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) ≤ Real.sqrt (F x : ℝ))
    (hη : (d : ℝ) * (((2 ^ d * (Hall Hd).card : ℕ)) : ℝ)
        * (8 * a + 8 * Real.sqrt (Xbd d (2 * (2 ^ d * (Hall Hd).card))) * b) ≤ 1 / 2) :
    (1 / 4) * (1 / LupC F M) ^ (Hall Hd).card
      ≤ Cnt (V := V) (id : ι → ι) (Hall Hd)
          (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj) := by
  classical
  have hFpos : ∀ n, 1 ≤ F n := fun n => le_trans (by omega) (hFgrow n)
  have hFposR : ∀ n, (0 : ℝ) < (F n : ℝ) := fun n =>
    (by have h := hFpos n; exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one h) :
      (0 : ℝ) < (F n : ℝ))
  have hlog9 : (1 : ℝ) < Real.log 9 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by have := Real.exp_one_lt_d9; linarith)
  have hLam1 : ∀ D ≤ d, 1 ≤ LamC F M D := by
    intro D hD
    unfold LamC
    have hMD : 8 ≤ M D := le_trans hT8 (le_trans hT (hManti D hD))
    have h9 : (9 : ℝ) ≤ (F (M D) : ℝ) := by
      have h := hFgrow (M D)
      exact_mod_cast (by omega : 9 ≤ F (M D))
    exact le_trans hlog9.le (Real.log_le_log (by norm_num) h9)
  have hM03 : 3 ≤ M 0 := le_trans hMd3 (hManti 0 (Nat.zero_le d))
  have hM08 : 8 ≤ M 0 := le_trans hT8 (le_trans hT (hManti 0 (Nat.zero_le d)))
  have hlog0 : (2 : ℝ) ≤ Real.log (F (M 0)) := by
    have h9 : (9 : ℝ) ≤ (F (M 0) : ℝ) := by
      have h := hFgrow (M 0)
      exact_mod_cast (by omega : 9 ≤ F (M 0))
    have hexp2 : Real.exp 2 < 9 := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [h2]
      nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]
    have h : (2 : ℝ) < Real.log 9 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp2
    exact le_trans h.le (Real.log_le_log (by norm_num) h9)
  have hha : ∀ D ≤ d, ∀ j ≤ 2 ^ d * (Hall Hd).card,
      PsiC F M D * (LamC F M D) ^ j ≤ a := by
    intro D hD j hj
    unfold PsiC LamC
    rw [inv_mul_eq_div]
    have hMD : T ≤ M D := le_trans hT (hManti D hD)
    exact le_trans (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (hLam1 D hD) hj) (Real.sqrt_nonneg _)) (hTa (M D) hMD)
  have hhb : ∀ j ≤ 2 ^ d * (Hall Hd).card, Real.sqrt (rhoC F M) * (LupC F M) ^ j ≤ b := by
    intro j hj
    have hKj : j ≤ 2 ^ d * (Hall Hd).card := hj
    unfold rhoC LupC
    rw [one_div, Real.sqrt_inv, inv_mul_eq_div]
    have h1 : (Real.log (F (M 0)) + 2) ^ j
        ≤ (Real.log (F (M 0)) + 2) ^ (2 ^ d * (Hall Hd).card) :=
      pow_le_pow_right₀ (by linarith) hKj
    have h2 : Real.log (F (M 0)) + 2 ≤ 2 * Real.log (F (M 0)) := by linarith
    have h3 : (Real.log (F (M 0)) + 2) ^ (2 ^ d * (Hall Hd).card)
        ≤ (2 * Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card) :=
      pow_le_pow_left₀ (by linarith) h2 _
    have h4 : (2 * Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card)
        = (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)
          * (Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card) := mul_pow _ _ _
    have hM0T : T ≤ M 0 := le_trans hT (hManti 0 (Nat.zero_le d))
    have hroot : (0 : ℝ) < Real.sqrt (F (M 0) : ℝ) := Real.sqrt_pos.mpr (hFposR (M 0))
    have h5 : (Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card)
        ≤ (b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) * Real.sqrt (F (M 0) : ℝ) := by
      have h := hTb (M 0) hM0T
      rwa [div_le_iff₀ hroot] at h
    have hb0' : (0 : ℝ) ≤ b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card) := by positivity
    calc (Real.log (F (M 0)) + 2) ^ j / Real.sqrt (F (M 0) : ℝ)
        ≤ (2 * Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card)
            / Real.sqrt (F (M 0) : ℝ) :=
          div_le_div_of_nonneg_right (le_trans h1 h3) (le_of_lt hroot)
      _ = (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)
            * (Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card)
            / Real.sqrt (F (M 0) : ℝ) := by rw [h4]
      _ ≤ (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)
            * ((b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) * Real.sqrt (F (M 0) : ℝ))
            / Real.sqrt (F (M 0) : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left h5 (by positivity)) (le_of_lt hroot)
      _ = b := by field_simp
  have hTh : ThetaC F M d (Hall Hd).card ≤ 1 / 2 := by
    have h := ThetaC_bound (F := F) (M := M) (a := a) (b := b) (K := (Hall Hd).card)
      hFpos hLam1 (le_of_lt ha0) (le_of_lt hb0) hha hhb hd (by linarith [hη])
    refine le_trans (h d le_rfl (Hall Hd).card ?_) (by linarith [hη])
    rw [Nat.sub_self, pow_zero, one_mul]
  have hM0T : T ≤ M 0 := le_trans hT (hManti 0 (Nat.zero_le d))
  have hKle : (Hall Hd).card ≤ 2 ^ d * (Hall Hd).card := by
    have h := Nat.le_mul_of_pos_right (Hall Hd).card (by positivity : 0 < 2 ^ d)
    rwa [Nat.mul_comm] at h
  have hroot0 : (0 : ℝ) < Real.sqrt (F (M 0) : ℝ) := Real.sqrt_pos.mpr (hFposR (M 0))
  have hF0_2 : (2 : ℝ) ≤ (F (M 0) : ℝ) := by
    have h := hFgrow (M 0)
    exact_mod_cast (by omega : 2 ≤ F (M 0))
  have hpowle : (Real.log (F (M 0))) ^ (Hall Hd).card
      ≤ (Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card) :=
    pow_le_pow_right₀ (by linarith) hKle
  have hbound : (Real.log (F (M 0))) ^ (2 ^ d * (Hall Hd).card)
      ≤ (b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) * Real.sqrt (F (M 0) : ℝ) := by
    have h := hTb (M 0) hM0T
    rwa [div_le_iff₀ hroot0] at h
  have key : 4 * Xbd d (Hall Hd).card * (Real.log (F (M 0)) + 2) ^ (Hall Hd).card
      ≤ (F (M 0) : ℝ) := by
    have h3 : (Real.log (F (M 0)) + 2) ^ (Hall Hd).card
        ≤ (2 : ℝ) ^ (Hall Hd).card * (Real.log (F (M 0))) ^ (Hall Hd).card := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have h4 : (2 : ℝ) ^ (Hall Hd).card * (Real.log (F (M 0))) ^ (Hall Hd).card
        ≤ (2 : ℝ) ^ (Hall Hd).card
          * ((b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) * Real.sqrt (F (M 0) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_trans hpowle hbound) (by positivity)
    have h5 := hTc (M 0) hM0T
    have hXb0 : (0 : ℝ) ≤ Xbd d (Hall Hd).card := Xbd_nonneg d (Hall Hd).card
    have hq0 : (0 : ℝ) ≤ b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card) := by positivity
    have h6 : 4 * Xbd d (Hall Hd).card * ((2 : ℝ) ^ (Hall Hd).card
          * ((b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) * Real.sqrt (F (M 0) : ℝ)))
        ≤ Real.sqrt (F (M 0) : ℝ) * Real.sqrt (F (M 0) : ℝ) := by
      nlinarith [h5, hXb0, hq0, hroot0]
    calc 4 * Xbd d (Hall Hd).card * (Real.log (F (M 0)) + 2) ^ (Hall Hd).card
        ≤ 4 * Xbd d (Hall Hd).card
            * ((2 : ℝ) ^ (Hall Hd).card * (Real.log (F (M 0))) ^ (Hall Hd).card) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 4 * Xbd d (Hall Hd).card
            * ((2 : ℝ) ^ (Hall Hd).card
              * ((b / (2 : ℝ) ^ (2 ^ d * (Hall Hd).card)) * Real.sqrt (F (M 0) : ℝ))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ Real.sqrt (F (M 0) : ℝ) * Real.sqrt (F (M 0) : ℝ) := h6
      _ = (F (M 0) : ℝ) := by
          rw [← sq, Real.sq_sqrt (by positivity)]
  have hX : XC F M d (Hall Hd).card * rhoC F M
      ≤ (1 / 4) * (1 / LupC F M) ^ (Hall Hd).card := by
    unfold rhoC LupC
    have h1 : XC F M d (Hall Hd).card ≤ Xbd d (Hall Hd).card :=
      XC_le_Xbd (F := F) (M := M) hFpos d (Hall Hd).card
    refine le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) ?_
    rw [show (1 / 4) * (1 / (Real.log (F (M 0)) + 2)) ^ (Hall Hd).card
        = (1 / 4) / (Real.log (F (M 0)) + 2) ^ (Hall Hd).card from by
          rw [div_pow, one_pow]; ring]
    rw [show Xbd d (Hall Hd).card * (1 / (F (M 0) : ℝ))
        = Xbd d (Hall Hd).card / ((F (M 0) : ℝ)) from by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((F (M 0) : ℝ)))]
    rw [show ((1 / 4) / (Real.log (F (M 0)) + 2) ^ (Hall Hd).card) * (F (M 0) : ℝ)
        = ((1 / 4) * (F (M 0) : ℝ)) / (Real.log (F (M 0)) + 2) ^ (Hall Hd).card from by ring]
    rw [le_div_iff₀ (pow_pos (by linarith) _)]
    have hk : (1 / 4) * (F (M 0) : ℝ) * 4 = (F (M 0) : ℝ) := by ring
    linarith [key]
  exact counting_lemma_lower_F (V := V) hHd hBd hAtom hGood hR hFgrow hFmono hlog hempty hTh hX


/-! ## The triple-exponential growth function -/

/-- The triple-exponential growth function `n ↦ 2^(2^(2^n))`.  It satisfies
`log (Ffast x) ≫ 2^x`, which is exactly what the removal lemma requires. -/
def Ffast (n : ℕ) : ℕ := 2 ^ (2 ^ (2 ^ n))

theorem Ffast_grow (n : ℕ) : n + 1 ≤ Ffast n := by
  have h1 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have h2 : n ≤ 2 ^ (2 ^ n) := le_trans h1 (Nat.pow_le_pow_right (by norm_num) h1)
  calc n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    _ ≤ 2 ^ (2 ^ (2 ^ n)) := Nat.pow_le_pow_right (by norm_num) h2

theorem Ffast_mono : Monotone Ffast := fun a b h =>
  Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h))

theorem Ffast_pos (n : ℕ) : 1 ≤ Ffast n := le_trans (Nat.le_add_left 1 n) (Ffast_grow n)

/-- **Existence of the counting-lemma threshold** for the growth function `Ffast`. -/
theorem exists_counting_threshold_Fast (d K : ℕ) :
    ∃ T : ℕ, ∃ a b : ℝ, 8 ≤ T ∧ 0 < a ∧ 0 < b ∧
      (∀ x : ℕ, T ≤ x →
        (Real.log (Ffast x)) ^ (2 ^ d * K) / Real.sqrt (Ffast x : ℝ) ≤ a) ∧
      (∀ x : ℕ, T ≤ x →
        (Real.log (Ffast x)) ^ (2 ^ d * K) / Real.sqrt (Ffast x : ℝ)
          ≤ b / (2 : ℝ) ^ (2 ^ d * K)) ∧
      (∀ x : ℕ, T ≤ x → 4 * Xbd d K * (2 : ℝ) ^ K * (b / (2 : ℝ) ^ (2 ^ d * K))
          ≤ Real.sqrt (Ffast x : ℝ)) ∧
      ((d : ℝ) * ((2 ^ d * K : ℕ) : ℝ)
          * (8 * a + 8 * Real.sqrt (Xbd d (2 * (2 ^ d * K))) * b) ≤ 1 / 2) := by
  classical
  set X : ℝ := Real.sqrt (Xbd d (2 * (2 ^ d * K))) + 1 with hXdef
  have hXge : 1 ≤ X := by
    rw [hXdef]; linarith [Real.sqrt_nonneg (Xbd d (2 * (2 ^ d * K)))]
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXge
  have hXsub : X - 1 = Real.sqrt (Xbd d (2 * (2 ^ d * K))) := by rw [hXdef]; ring
  set D0 : ℝ := (d : ℝ) * ((2 ^ d * K : ℕ) : ℝ) + 1 with hD0def
  have hD0ge : 1 ≤ D0 := by
    rw [hD0def]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((2 ^ d * K : ℕ) : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  set a : ℝ := 1 / (40 * D0) with hadef
  have ha0 : 0 < a := by rw [hadef]; positivity
  set b : ℝ := 1 / (40 * D0 * X) with hbdef
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hη : (d : ℝ) * ((2 ^ d * K : ℕ) : ℝ)
      * (8 * a + 8 * Real.sqrt (Xbd d (2 * (2 ^ d * K))) * b) ≤ 1 / 2 := by
    have h1 : 8 * a = 2 / (10 * D0) := by rw [hadef]; ring_nf
    have h2 : 8 * Real.sqrt (Xbd d (2 * (2 ^ d * K))) * b = 8 * (X - 1) / (40 * D0 * X) := by
      rw [hbdef, hXsub]; ring
    have h3 : 8 * (X - 1) / (40 * D0 * X) ≤ 1 / (5 * D0) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 40 * D0 * X)]
      have he : (1 / (5 * D0)) * (40 * D0 * X) = 8 * X := by field_simp; ring
      rw [he]
      linarith
    have h4 : 2 / (10 * D0) + 1 / (5 * D0) = 2 / (5 * D0) := by ring_nf
    have h5 : (d : ℝ) * ((2 ^ d * K : ℕ) : ℝ) = D0 - 1 := by rw [hD0def]; ring
    rw [h1, h2, h5]
    have h6 : (D0 - 1) * (2 / (10 * D0) + 1 / (5 * D0)) ≤ 1 / 2 := by
      rw [h4]
      rw [show (D0 - 1) * (2 / (5 * D0)) = 2 * (D0 - 1) / (5 * D0) from by ring]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 5 * D0)]
      linarith
    have h7 : (D0 - 1) * (2 / (10 * D0) + 8 * (X - 1) / (40 * D0 * X))
        ≤ (D0 - 1) * (2 / (10 * D0) + 1 / (5 * D0)) :=
      mul_le_mul_of_nonneg_left (by linarith [h3]) (by linarith [hD0ge])
    linarith [h7, h6]
  obtain ⟨Y1, -, hY1⟩ :=
    Commons.Analysis.Real.exists_pow_log_div_sqrt_le (2 ^ d * K) (ε := a) ha0
  obtain ⟨Y2, -, hY2⟩ :=
    Commons.Analysis.Real.exists_pow_log_div_sqrt_le (2 ^ d * K)
      (ε := b / (2 : ℝ) ^ (2 ^ d * K)) (div_pos hb0 (by positivity))
  set C : ℝ := 4 * Xbd d K * (2 : ℝ) ^ K * (b / (2 : ℝ) ^ (2 ^ d * K)) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Xbd_nonneg d K)) (by positivity))
      (div_nonneg (le_of_lt hb0) (by positivity))
  set T0 : ℕ := max 8 (max (Nat.ceil Y1) (max (Nat.ceil Y2) (Nat.ceil (C ^ 2) + 1)))
    with hT0def
  have h8 : 8 ≤ T0 := by rw [hT0def]; exact le_max_left _ _
  have hceil1 : Nat.ceil Y1 ≤ T0 := by
    rw [hT0def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hceil2 : Nat.ceil Y2 ≤ T0 := by
    rw [hT0def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hceil3 : Nat.ceil (C ^ 2) + 1 ≤ T0 := by
    rw [hT0def]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hFx : ∀ x : ℕ, T0 ≤ x → (x : ℝ) ≤ (Ffast x : ℝ) := fun x _ =>
    (by exact_mod_cast (le_trans (Nat.le_succ x) (Ffast_grow x)) : (x : ℝ) ≤ (Ffast x : ℝ))
  refine ⟨T0, a, b, h8, ha0, hb0, ?_, ?_, ?_, hη⟩
  · intro x hx
    have hYx : Y1 ≤ (Ffast x : ℝ) := by
      have h1 : Y1 ≤ (Nat.ceil Y1 : ℝ) := Nat.le_ceil Y1
      have h2 : (Nat.ceil Y1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans hceil1 hx)
      linarith [hFx x hx]
    exact hY1 _ hYx
  · intro x hx
    have hYx : Y2 ≤ (Ffast x : ℝ) := by
      have h1 : Y2 ≤ (Nat.ceil Y2 : ℝ) := Nat.le_ceil Y2
      have h2 : (Nat.ceil Y2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans hceil2 hx)
      linarith [hFx x hx]
    exact hY2 _ hYx
  · intro x hx
    have hCx : C ≤ Real.sqrt (Ffast x : ℝ) := by
      have h1 : C ^ 2 ≤ (Nat.ceil (C ^ 2) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (C ^ 2) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (C ^ 2) ≤ x)
      have h4 : C ^ 2 ≤ (Ffast x : ℝ) := le_trans h1 (le_trans h2 (hFx x hx))
      calc C = Real.sqrt (C ^ 2) := (Real.sqrt_sq hC0).symm
        _ ≤ Real.sqrt (Ffast x : ℝ) := Real.sqrt_le_sqrt h4
    exact hCx

end Szemeredi.Removal
