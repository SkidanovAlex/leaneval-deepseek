import Mathlib
import Submission.Szemeredi.Removal.GencountSmall

/-!
# The counting lemma (Tao, Lemma `count-lemma`)

Instantiation of the generalized counting lemma `gencount` at the trivial bundle
`(κ, π, G) = (ι, id, Hall Hd)`, with the growth function `F n = 2^n`, together with the
lower bound furnished by the good-atom largeness condition.
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

/-- The concrete growth function `F n = 2^n`. -/
def Fpow (n : ℕ) : ℕ := 2 ^ n

theorem Fpow_grow (n : ℕ) : n + 1 ≤ Fpow n := by
  unfold Fpow
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem Fpow_mono : Monotone Fpow := fun a b h => by
  unfold Fpow; exact pow_le_pow_right₀ (by norm_num) h

theorem Fpow_pos (n : ℕ) : 1 ≤ Fpow n := by
  have := Fpow_grow n; omega

theorem LamC_Fpow (M : ℕ → ℕ) (n : ℕ) :
    LamC Fpow M n = (M n : ℝ) * Real.log 2 := by
  unfold LamC Fpow
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem PsiC_Fpow (M : ℕ → ℕ) (n : ℕ) :
    PsiC Fpow M n = (Real.sqrt (((2 : ℝ) ^ (M n))))⁻¹ := by
  unfold PsiC Fpow
  rw [Nat.cast_pow, Nat.cast_ofNat]

theorem LupC_Fpow (M : ℕ → ℕ) :
    LupC Fpow M = (M 0 : ℝ) * Real.log 2 + 2 := by
  unfold LupC Fpow
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem rhoC_Fpow (M : ℕ → ℕ) :
    rhoC Fpow M = 1 / (((2 : ℝ) ^ (M 0))) := by
  unfold rhoC Fpow
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- The bundle `(ι, id, Hall Hd)`. -/
theorem isBundle_id (Hd : Finset (Finset ι)) :
    IsBundle Hd (id : ι → ι) (Hall Hd) where
  closed := fun g hg g' hg' => Hall_down hg hg'
  inj := fun g _ a _ b _ hab => hab
  img := fun g hg => by simpa using hg

theorem mem_Hall_card_le {Hd : Finset (Finset ι)} {d : ℕ} (hHd : ∀ e ∈ Hd, e.card = d)
    {g : Finset ι} (hg : g ∈ Hall Hd) : g.card ≤ d := by
  obtain ⟨e, he, hsub⟩ := mem_Hall.mp hg
  exact le_trans (Finset.card_le_card hsub) (le_of_eq (hHd e he))

/-- **The counting lemma** (Tao, `count-lemma`), lower bound form. -/
theorem counting_lemma_lower
    {d : ℕ} {Hd : Finset (Finset ι)} {Bd : Finset ι → SigAlg (Pt V)} {Md : ℕ}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)} {M : ℕ → ℕ} {A : Finset ι → Finset (Pt V)}
    (hHd : ∀ e ∈ Hd, e.card = d)
    (hBd : ∀ e ∈ Hd, (Bd e).Refines (coord (V := V) e))
    (hAtom : ∀ f ∈ Hall Hd, A f ∈ (algOf (V := V) d Bd B f).atoms)
    (hGood : ∀ e ∈ Hall Hd, GoodAt (V := V) d Bd B B' M Fpow A e.card e)
    (hR : RegOK2 (V := V) d Hd Bd Md Fpow B B' M)
    (hlog : ∀ e ∈ Hall Hd, 1 ≤ Real.log ((Fpow (M e.card) : ℕ) : ℝ))
    (hempty : A ∅ = Finset.univ)
    (hTh : ThetaC Fpow M d (Hall Hd).card ≤ 1 / 2)
    (hX : XC Fpow M d (Hall Hd).card * rhoC Fpow M
      ≤ (1 / 4) * (1 / LupC Fpow M) ^ (Hall Hd).card) :
    (1 / 4) * (1 / LupC Fpow M) ^ (Hall Hd).card
      ≤ Cnt (V := V) (id : ι → ι) (Hall Hd)
          (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj) := by
  classical
  have hF1 : 1 ≤ Fpow (M 0) := Fpow_pos _
  have hgen := gencount (V := V) hHd hBd hAtom hGood hR hF1 Fpow_mono Fpow_grow hlog hempty
    (id : ι → ι) (Hall Hd) (isBundle_id Hd) (fun g hg => mem_Hall_card_le hHd hg)
  have hP0 : (0 : ℝ) ≤ ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g :=
    Finset.prod_nonneg (fun g _ => pOf_nonneg A _)
  have hLuppos : (0 : ℝ) < LupC Fpow M := by
    rw [LupC_Fpow]
    have h1 : (0 : ℝ) ≤ (M 0 : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.log_pos (by norm_num)))
    linarith
  -- the lower bound on the product of the `p`'s
  have hPL : (1 / LupC Fpow M) ^ (Hall Hd).card ≤ ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g := by
    have hManti := hR.M_anti Fpow_grow
    have h1 : ∀ g ∈ Hall Hd, (1 / LupC Fpow M) ≤ pgOf A (id : ι → ι) g := by
      intro g hg
      have hgc : g.card ≤ d := mem_Hall_card_le hHd hg
      have hlogg : 1 ≤ Real.log (RgOf Fpow M (id : ι → ι) g) := by
        have h := hlog g hg
        have he : RgOf Fpow M (id : ι → ι) g = ((Fpow (M g.card) : ℕ) : ℝ) := by
          unfold RgOf
          rw [Finset.image_id]
        rw [he]
        exact h
      have h2 := gchyp_h2 (V := V) (Md := Md) (M := M) (F := Fpow) (B := B) (B' := B')
        (A := A) (d := d) (Hd := Hd) (Bd := Bd) hGood (isBundle_id Hd) hg hlogg
      refine le_trans (one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hlogg) ?_) h2
      show Real.log (RgOf Fpow M (id : ι → ι) g) ≤ Real.log (Fpow (M 0)) + 2
      have he : RgOf Fpow M (id : ι → ι) g = ((Fpow (M g.card) : ℕ) : ℝ) := by
        unfold RgOf
        rw [Finset.image_id]
      have hle : Real.log (RgOf Fpow M (id : ι → ι) g) ≤ Real.log (Fpow (M 0)) := by
        rw [he]
        refine Real.log_le_log ?_ ?_
        · unfold Fpow; positivity
        · have h3 : M g.card ≤ M 0 := hManti 0 g.card (Nat.zero_le _) hgc
          exact_mod_cast (Fpow_mono h3)
      linarith
    calc (1 / LupC Fpow M) ^ (Hall Hd).card
        = ∏ g ∈ Hall Hd, (1 / LupC Fpow M) := by rw [Finset.prod_const]
      _ ≤ ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g :=
          Finset.prod_le_prod (fun g _ => le_of_lt (one_div_pos.mpr hLuppos)) (fun g hg => h1 g hg)
  have hCnt : (1 / 2) * (∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g)
      - XC Fpow M d (Hall Hd).card * rhoC Fpow M
      ≤ Cnt (V := V) (id : ι → ι) (Hall Hd)
          (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj) := by
    have h2 : ThetaC Fpow M d (Hall Hd).card * (∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g)
        ≤ (1 / 2) * (∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g) :=
      mul_le_mul_of_nonneg_right hTh hP0
    have h3 := neg_abs_le (Cnt (V := V) (id : ι → ι) (Hall Hd)
      (AgOf (V := V) A (id : ι → ι) (Hall Hd) (isBundle_id Hd).inj)
        - ∏ g ∈ Hall Hd, pgOf A (id : ι → ι) g)
    linarith [hgen]
  linarith [hPL, hX]

end Szemeredi.Removal
