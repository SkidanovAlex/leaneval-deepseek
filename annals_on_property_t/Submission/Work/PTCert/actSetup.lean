import Mathlib
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.Glue3

/-!
# PTCert — step (A): the action set-up on the index family `fE`

We assemble `ActSetup` from the semantic hypotheses of the kernel checks:

* `hE : ESem` gives the `CmSound` commutation table, closure of `eAll` under `normC`, and
  faithfulness of the codes (`eltC` injective on `eAll`);
* `hCF : CodeFacts` gives, for every `σ ∈ Σ₅`, a valid code `c` with `codeElt c = σ` acting on
  the letters by `actL` (values `< 81`), whence closure of `eS` under conjugation;
* `hCA : ConjActFacts` gives the action properties of `conjAct fE` (this is `actE`);
* `hAC : ActCSound` computes conjugation on codes by the letter tables (`normC`/`actC`);
* `hT : TabSem` gives the tables of the sign flips, and `hBB : BitsBridge` identifies
  `zBool (zOfSc sc)` with `scBits sc`.

The only subtle point: `conjAct f σ x` is defined by `Classical.choose` of the *existence* of a
conjugate, so to compute it we exhibit the conjugate and use that `fE` is injective.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open SigmaFacts

set_option maxRecDepth 10000

private lemma zBool_add_five (a b : Fin 5 → ZMod 2) :
    zBool (a + b) = fun k => zBool a k ^^ zBool b k := by
  funext k
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (a k) with h | h <;> rcases h2 (b k) with h' | h' <;> simp [zBool, h, h']

private lemma zBool_zero_five : zBool (0 : Fin 5 → ZMod 2) = fun _ => false := by
  funext k; simp [zBool]

theorem actSetup (hCF : CodeFacts) (hCA : ConjActFacts) (hAC : ActCSound) (hBB : BitsBridge)
    (hE : ESem) (hT : TabSem) : ActSetup := by
  classical
  obtain ⟨hCm, hNodup, hNorm, hClos, hInjE, hEm⟩ := hE
  obtain ⟨hSgSub, hSignSub, hSignSubSg⟩ := sigmaGroupFacts 5
  obtain ⟨hBB1, hBB2, hBB3, hBB4, hBB5, hBB6⟩ := hBB
  have hACc := hAC cmT hCm
  have hAC1 : ∀ a < 81, ∀ b < 81, eltC (normC cmT a b) = b1 5 a * b1 5 b ∧
      normC cmT a b / 128 < 81 ∧ normC cmT a b % 128 < 81 := hACc.1
  have hAC2 : ∀ (σ : G5) (tab : ℕ), TabOf σ tab → (∀ k < 81, lk tab k < 81) →
      ∀ c : ℕ, c / 128 < 81 → c % 128 < 81 →
        eltC (actC cmT tab c) = σ * eltC c * σ⁻¹ ∧ actC cmT tab c / 128 < 81 ∧
          actC cmT tab c % 128 < 81 := hACc.2
  -- (1) injectivity of the code family
  have hInj : Function.Injective fE := by
    intro x y h
    apply Subtype.ext
    exact hInjE x.1 (List.mem_toFinset.mp x.2) y.1 (List.mem_toFinset.mp y.2) h
  -- (2) closure of `eS` under conjugation by `Sg`
  have hclosed : ∀ σ ∈ Sg, ∀ x : EI, ∃ y : EI, fE y = σ * fE x * σ⁻¹ := by
    intro σ hσ x
    obtain ⟨c, hvc, hce⟩ := hCF.2.1 σ hσ
    obtain ⟨_, hcAct⟩ := hCF.1 c hvc
    have hxE := List.mem_toFinset.mp x.2
    have hx1 : x.1 / 128 < 81 := (hNorm x.1 hxE).1
    have hx2 : x.1 % 128 < 81 := (hNorm x.1 hxE).2.1
    have ha : actL 5 (c / 32) (c % 32) (x.1 / 128) < 81 := (hcAct _ hx1).1
    have hb : actL 5 (c / 32) (c % 32) (x.1 % 128) < 81 := (hcAct _ hx2).1
    refine ⟨⟨normC cmT (actL 5 (c / 32) (c % 32) (x.1 / 128))
        (actL 5 (c / 32) (c % 32) (x.1 % 128)),
      List.mem_toFinset.mpr (hClos _ ha _ hb)⟩, ?_⟩
    show eltC (normC cmT (actL 5 (c / 32) (c % 32) (x.1 / 128))
        (actL 5 (c / 32) (c % 32) (x.1 % 128))) = σ * eltC x.1 * σ⁻¹
    rw [(hAC1 _ ha _ hb).1, ← hce, ← (hcAct _ hx1).2, ← (hcAct _ hx2).2]
    show (codeElt c * b1 5 (x.1 / 128) * (codeElt c)⁻¹) *
        (codeElt c * b1 5 (x.1 % 128) * (codeElt c)⁻¹)
      = codeElt c * (b1 5 (x.1 / 128) * b1 5 (x.1 % 128)) * (codeElt c)⁻¹
    group
  -- (3)-(6) the `conjAct`/`actE` action facts
  have hca := hCA G5 Sg hSgSub fE hInj hclosed
  obtain ⟨hconjAct, hcomp, hid, hbij, hlast⟩ := hca
  -- (7) the letter-table formula
  have hactTbl : ∀ (σ : G5) (tab : ℕ), TabOf σ tab → (∀ k < 81, lk tab k < 81) →
      ∀ x : EI, (actE σ x).1 = actC cmT tab x.1 := by
    intro σ tab hTab hB x
    have hxE := List.mem_toFinset.mp x.2
    have hx1 : x.1 / 128 < 81 := (hNorm x.1 hxE).1
    have hx2 : x.1 % 128 < 81 := (hNorm x.1 hxE).2.1
    have hmem : actC cmT tab x.1 ∈ eS :=
      List.mem_toFinset.mpr (hClos (lk tab (x.1 / 128)) (hB _ hx1)
        (lk tab (x.1 % 128)) (hB _ hx2))
    have hval : fE ⟨actC cmT tab x.1, hmem⟩ = σ * fE x * σ⁻¹ :=
      show eltC (actC cmT tab x.1) = σ * eltC x.1 * σ⁻¹ from
        hAC2 σ tab hTab hB x.1 hx1 hx2 |>.1
    have hex : ∃ y : EI, fE y = σ * fE x * σ⁻¹ := ⟨_, hval⟩
    show (conjAct fE σ x).1 = actC cmT tab x.1
    rw [show conjAct fE σ x = Classical.choose hex from dif_pos hex]
    have hch := Classical.choose_spec hex
    rw [show Classical.choose hex = ⟨actC cmT tab x.1, hmem⟩ from hInj (by rw [hch, hval])]
  -- (8) the code formula
  have hactCd : ∀ c : ℕ, validPC 5 (c / 32) = true → ∀ x : EI,
      (actE (codeElt c) x).1 = actCode c x.1 := by
    intro c hvc x
    obtain ⟨_, hcAct⟩ := hCF.1 c hvc
    have hxE := List.mem_toFinset.mp x.2
    have hx1 : x.1 / 128 < 81 := (hNorm x.1 hxE).1
    have hx2 : x.1 % 128 < 81 := (hNorm x.1 hxE).2.1
    have ha : actL 5 (c / 32) (c % 32) (x.1 / 128) < 81 := (hcAct _ hx1).1
    have hb : actL 5 (c / 32) (c % 32) (x.1 % 128) < 81 := (hcAct _ hx2).1
    have hmem : actCode c x.1 ∈ eS := List.mem_toFinset.mpr (hClos _ ha _ hb)
    have hval : fE ⟨actCode c x.1, hmem⟩ = codeElt c * fE x * (codeElt c)⁻¹ := by
      show eltC (normC cmT (actL 5 (c / 32) (c % 32) (x.1 / 128))
          (actL 5 (c / 32) (c % 32) (x.1 % 128))) = codeElt c * eltC x.1 * (codeElt c)⁻¹
      rw [(hAC1 _ ha _ hb).1, ← (hcAct _ hx1).2, ← (hcAct _ hx2).2]
      show (codeElt c * b1 5 (x.1 / 128) * (codeElt c)⁻¹) *
          (codeElt c * b1 5 (x.1 % 128) * (codeElt c)⁻¹)
        = codeElt c * (b1 5 (x.1 / 128) * b1 5 (x.1 % 128)) * (codeElt c)⁻¹
      group
    have hex : ∃ y : EI, fE y = codeElt c * fE x * (codeElt c)⁻¹ := ⟨_, hval⟩
    show (conjAct fE (codeElt c) x).1 = actCode c x.1
    rw [show conjAct fE (codeElt c) x = Classical.choose hex from dif_pos hex]
    have hch := Classical.choose_spec hex
    rw [show Classical.choose hex = ⟨actCode c x.1, hmem⟩ from hInj (by rw [hch, hval])]
  -- (11) the sign flips lie in `Sg`
  have hSgSign : ∀ a : Fin 5 → ZMod 2, signAut (zBool a) ∈ Sg := by
    intro a
    show signAut (zBool a) ∈ SigmaSet 5
    rw [SigmaFacts.mem_SigmaSet_iff]
    exact ⟨1, zBool a, by rw [sigAut, Submission.RouteB.permAut_one, mul_one]⟩
  refine ⟨hInj, hclosed, hconjAct, ?_, ?_, ?_, hactTbl, hactCd, ?_, ?_, hSgSign, ?_⟩
  · intro σ hσ τ hτ x
    exact hcomp σ hσ τ hτ x
  · intro x
    exact hid x
  · intro σ hσ
    exact hbij σ hσ
  · intro a b x
    show conjAct fE (signAut (zBool (a + b))) x
      = conjAct fE (signAut (zBool a)) (conjAct fE (signAut (zBool b)) x)
    rw [zBool_add_five, ← SigmaFacts.signAut_mul (r := 5)]
    exact hcomp _ (hSgSign a) _ (hSgSign b) x
  · intro x
    show conjAct fE (signAut (zBool 0)) x = x
    rw [zBool_zero_five, SigmaFacts.signAut_one (r := 5)]
    exact hid x
  · intro sc hsc x
    have hTab : TabOf (signAut (zBool (zOfSc sc))) (ntab sc) := by
      rw [hBB5 sc hsc]
      exact (hT.1 sc hsc).1
    exact hactTbl _ _ hTab (hT.1 sc hsc).2 x

end Work.PTCert
