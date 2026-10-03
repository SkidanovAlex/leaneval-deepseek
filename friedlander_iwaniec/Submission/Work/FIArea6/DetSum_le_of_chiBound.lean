/-
# `Work.FIArea6.DetSum_le_of_chiBound` — *FI* (16.11) + the trivial bound on `J(χ)`

The `ω`-detected pair sum `DetSum` of §16 is, by the exact expansion
`Work.FIArea7.section16_omegaDetect_expansion` (i.e. *FI* (16.11)/(17.10)),

  `DetSum = (1/|G|) Σ_χ J(χ)·|S_χ|²`,  `J(χ) = Σ_p ratWeight p·χ(p)`,
  `S_χ = Σ_z unitCoeff (β·ψ_k) z · χ(π z)`,

where `G = (ℤ[i]/4d)^*`, `ψ_k` is the Grossencharacter factor `(z/|z|)^k` and the characters run
over `AddChar (Additive G) ℂ`.  Two trivial bounds finish the estimate:

* `‖J(χ)‖ ≤ 4d`: `ratWeight` is supported on the *rational* classes `(ω,0)`, of which there are
  at most `|ZMod 4d| = 4d`, and `(ω|d) ∈ {0,±1}`;
* `‖S_χ‖ ≤ B` for every `χ`: the hypothesis bounds the *unstarred* sums
  `Σ_z β z·chiOf (4d) χ z·ψ_k(z)`, and conjugating the starred sum and replacing `χ` by the
  conjugated character `star ∘ χ` (again an additive character) turns it into exactly one of
  those.  Since `#(AddChar (Additive G) ℂ) = |G|`, the `1/|G|` cancels the number of characters.

Hence `‖DetSum‖ ≤ 4d·B²`.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea7.Section16Expansion
import Submission.Work.FIArea7.addChar_extends_charMod4d
import Submission.Work.FIArea7.chiOf_eq_unitInd_mul
import Submission.Work.FIArea7.norm_ratWeight_charSum_le
import Submission.Work.FIArea7.norm_unitCoeff_charSum_le
import Submission.Work.FIArea7.norm_inv_card_mul_sum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- *FI* (16.11) plus the trivial bounds on `J(χ)`: if every character sum `S_χ` of the expansion is bounded by `B`, then the `ω`-detected pair sum `DetSum` is bounded by `4d·B²` (at most `4d` rational classes, so `|J(χ)| ≤ 4d`, and the `1/|G|` of the expansion cancels the number `|G|` of characters). -/
theorem DetSum_le_of_chiBound (Pa : Work.FITop.Params) (d : ℕ) (hd : 1 ≤ d) (k : ℤ)
    (β : GaussianInt → ℂ) (B : ℝ)
    (hB : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
      ‖∑ z ∈ Work.FITop.boxN Pa, β z * Work.FIArea7.chiOf (4 * d) χ z * Work.FIArea6.psiK k z‖ ≤ B) :
    ‖Work.FIArea6.DetSum Pa d k β‖ ≤ 4 * (d : ℝ) * B ^ 2 := by
  haveI hQ : NeZero (4 * d) := ⟨by omega⟩
  -- the exact character expansion of `DetSum`
  have hexp : Work.FIArea6.DetSum Pa d k β =
      (1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * d)) : ℂ)) *
        ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
          (∑ p : Work.FIArea7.GaussUnit (4 * d), Work.FIArea7.ratWeight (4 * d) d p * χ (Additive.ofMul p)) *
            ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
                  * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))) *
             star (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
                  * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z)))) := by
    have hL : Work.FIArea6.DetSum Pa d k β =
        ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          Work.FIArea7.unitInd (4 * d) z1 * Work.FIArea7.unitInd (4 * d) z2 *
            ((fun z => β z * Work.FIArea6.psiK k z) z1 * star ((fun z => β z * Work.FIArea6.psiK k z) z2)) *
            (∑ ω : ZMod (4 * d), (if ((z1.re : ZMod (4*d)) = ω * (z2.re : ZMod (4*d))) ∧
              ((z1.im : ZMod (4*d)) = ω * (z2.im : ZMod (4*d))) then (jacobiSym (ω.val : ℤ) d : ℂ) else 0)) := by
      simp only [Work.FIArea6.DetSum, Work.FITop.boxN, Work.FIArea6.omegaDet, Work.FIArea7.omegaDetect,
        dif_neg (show ¬ (4 * d = 0) by omega)]
    rw [hL]
    exact Work.FIArea7.section16_omegaDetect_expansion (Work.FITop.radN Pa) (4 * d) d
      (fun z => β z * Work.FIArea6.psiK k z)
  -- the hypothesis, in the "unstarred" form appearing in the expansion
  have hB' : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
      ‖∑ z ∈ Work.FITop.boxN Pa, (fun z => β z * Work.FIArea6.psiK k z) z * Work.FIArea7.unitInd (4 * d) z
          * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))‖ ≤ B := by
    intro χ
    have h := hB χ
    have hsum : (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FIArea7.chiOf (4 * d) χ z * Work.FIArea6.psiK k z)
        = ∑ z ∈ Work.FITop.boxN Pa, (fun z => β z * Work.FIArea6.psiK k z) z * Work.FIArea7.unitInd (4 * d) z
            * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z)) := by
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Work.FIArea7.chiOf_eq_unitInd_mul (4 * d) χ z]
      ring
    rwa [hsum] at h
  -- each character sum of the expansion is bounded by `B`
  have hS : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
      ‖∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
          * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))‖ ≤ B :=
    fun χ => Work.FIArea7.norm_unitCoeff_charSum_le (4 * d) (Work.FITop.radN Pa)
      (fun z => β z * Work.FIArea6.psiK k z) B hB' χ
  -- the trivial bound `‖J(χ)‖ ≤ 4d` on the `ω`-weight of the expansion
  have hJ : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
      ‖∑ p : Work.FIArea7.GaussUnit (4 * d), Work.FIArea7.ratWeight (4 * d) d p * χ (Additive.ofMul p)‖
        ≤ 4 * (d : ℝ) := fun χ => by
    have h := Work.FIArea7.norm_ratWeight_charSum_le (4 * d) d χ
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  -- the pointwise bound on the terms of the expansion
  have hH : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
      ‖(∑ p : Work.FIArea7.GaussUnit (4 * d), Work.FIArea7.ratWeight (4 * d) d p * χ (Additive.ofMul p)) *
        ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
              * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))) *
         star (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
              * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))))‖ ≤ 4 * (d : ℝ) * B ^ 2 := by
    intro χ
    have h1 := hJ χ
    have h2 := hS χ
    have h3 : ‖∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
          * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))‖ *
        ‖∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
            * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))‖ ≤ B * B :=
      mul_self_le_mul_self (norm_nonneg _) h2
    calc ‖(∑ p : Work.FIArea7.GaussUnit (4 * d), Work.FIArea7.ratWeight (4 * d) d p * χ (Additive.ofMul p)) *
        ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
              * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))) *
         star (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
              * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))))‖
        = ‖∑ p : Work.FIArea7.GaussUnit (4 * d), Work.FIArea7.ratWeight (4 * d) d p * χ (Additive.ofMul p)‖ *
          (‖∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
                * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))‖ *
           ‖∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
                * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))‖) := by
          rw [norm_mul, norm_mul, norm_star]
      _ ≤ (4 * (d : ℝ)) * (B * B) := by
          refine mul_le_mul h1 h3 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
          exact le_trans (norm_nonneg _) h1
      _ = 4 * (d : ℝ) * B ^ 2 := by ring
  rw [hexp]
  refine Work.FIArea7.norm_inv_card_mul_sum_le (B := B) (C := 4 * (d : ℝ))
    (fun χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ =>
      (∑ p : Work.FIArea7.GaussUnit (4 * d), Work.FIArea7.ratWeight (4 * d) d p * χ (Additive.ofMul p)) *
        ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
              * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z))) *
         star (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.unitCoeff (4 * d) (fun z => β z * Work.FIArea6.psiK k z) z
              * χ (Additive.ofMul (Work.FIArea7.unitClassD (4 * d) z)))))
    hH

end

end Work.FIArea6
