import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.lemma33Case2
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.l34ExcNeFourAux
import Submission.Work.BG.l34ne_chi_even
import Submission.Work.BG.l34ne_restrict_shape
import Submission.Work.BG.l34ne_cong_alpha
import Submission.Work.BG.l34ne_exists_fixing_action
import Submission.Work.BG.c3neDegModFour

/-!
# Area BG: the `|Λξ| ≠ 4` case of the exceptional configuration (BG 1981, Lemma 3.4)

`Work.BG.c3ExcNeFour` is the case of Bender–Glauberman 1981, Lemma 3.4 (p. 209), in which
the non-`s`-fixed member `ν ∈ 𝒮(χ)` of the exceptional configuration (`|Λν| = 4`,
`(Λν)^s = Λν`, so `|S| = 8` and `D.n = 4`) is accompanied by an `s`-fixed `ξ ∈ 𝒮(χ)` with
`|Λξ| ≠ 4` (hence `|Λξ| = 2` by Remark 3.1).  The proof is the paper's:

* `𝒮(χ) = bset C f χ = {ν, ν^s, ξ}` (Theorem 3.2 plus the three members);
* `ν|_U = β` is a single irreducible and `ξ|_U = α₁ + α₂` is the sum of the two `S₀`-conjugates
  (Remark 3.1, `Work.BG.l34ne_restrict_shape`), with `α₁ ≠ α₂` both of odd degree (so that
  `ξ 1 = 2 m` with `m` odd);
* hence `4 ∣ χ(1)` (BG's degree count, `Work.BG.l34NeDegModFourCrux`);
* Lemma 2.4 gives `χ ≡ α₁ + α₂` on `U` (`Work.BG.l34ne_cong_alpha`);
* the two distinct `t_i`-invariant irreducibles `α₁, α₂` supply an involutive automorphism `σ`
  of `↥U` with `α₁, α₂` `σ`-invariant and an index-`≤`two subgroup `L ≤ S` centralising
  `C_U(σ)` (`Work.BG.l34ne_exists_fixing_action`);
* Gorenstein 4.2.10 with `4 ∣ χ(1)` and `|G : C_G(u)|` of `2`-part at most two makes `χ` even
  on `C_U(σ)` (`Work.BG.l34ne_chi_even`), so `α₁ + α₂ ≡ 0` there;
* that contradicts the injectivity of Glauberman's correspondence (BG Lemma 1.9) for the
  distinct `σ`-invariant `α₁ ≠ α₂` (`Work.BG.l34ExcNeFour_glauberman_contra`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

theorem c3ExcNeFour {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ → OddOrder.RepresentationTheory.ClassFunction G ℂ,
      Work.GW2.C16.IsCoherent C f →
    ∀ χ : OddOrder.RepresentationTheory.ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξs hξ4
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(C.P.U) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(C.P.U) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- ## `D.n = 4` and `𝒮(χ) = {ν, ν^s, ξ}`
  have hD4 : D.n = 4 := l34ExcNeFour_n_eq_four D C hdisj hinv h4
  have hbset : bset C f χ = {ν, sconj C ν, ξ} :=
    l34ExcNeFour_bset_eq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs
  -- ## the restriction shapes on `U`
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, hα1eq, hξα⟩, hcardξ⟩ :=
    l34ne_restrict_shape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs
      hξs hξ4
  -- ## `ξ 1 = 2 m` with `m` odd
  have hξdeg : ∃ m : ℤ, ξ 1 = (2 : ℂ) * (m : ℂ) ∧ Odd m := by
    obtain ⟨n, hnpos, hrest⟩ := hα₁irr.exists_natDegree_charValue_one_dvd_card
    obtain ⟨hnval, hndvd⟩ := hrest
    have hUodd : Odd (Nat.card ↥(C.P.U)) := odd_card_U_of_compat hDC
    have hnodd : Odd n := Odd.of_dvd_nat hUodd hndvd
    have hnval' : α₁ 1 = (n : ℂ) := by simpa using hnval
    have hval : ξ 1 = α₁ 1 + α₂ 1 := by
      have h := congrArg (fun g : ClassFunction ↥(C.P.U) ℂ => g 1) hξα
      rw [ClassFunction.add_apply, restrictU_apply] at h
      have h1 : (⟨((1 : ↥(C.P.U)) : G), C.P.U_le_H0 (1 : ↥(C.P.U)).2⟩ : ↥C.P.H0) = 1 :=
        Subtype.ext (by simp)
      rw [h1] at h
      exact h
    refine ⟨(n : ℤ), ?_, ?_⟩
    · rw [hval, ← hα1eq, hnval']
      push_cast
      ring
    · obtain ⟨k, hk⟩ := hnodd
      exact ⟨(k : ℤ), by push_cast [hk]; ring⟩
  -- ## BG's degree count: `4 ∣ χ(1)`
  have hdeg4 : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) :=
    c3neDegModFour D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs
      hξs hξ4 hbset hξdeg
  -- ## the fixing involution and the index-`≤`two centralising subgroup
  obtain ⟨σ, L, hσσ, hLle, hLrel, hinvα₁, hinvα₂, hcent⟩ :=
    l34ne_exists_fixing_action D C hDC hS3 hD4 hξ.1 hξs hα₁irr hα₂irr hαne hξα hcardξ
  -- ## `χ ≡ α₁ + α₂` on `U` (BG Lemma 2.4)
  have hcongU : ∀ u : ↥(C.P.U), AlgIntModTwo (χ (u : G)) (α₁ u + α₂ u) :=
    l34ne_cong_alpha D C hDC hS3 f hf χ hχ hν hξ hne hξν hξνs hbset hβirr hνβ hsνβ hξα
  -- ## Glauberman injectivity gives the contradiction
  have hUodd : Odd (Nat.card ↥(C.P.U)) := odd_card_U_of_compat hDC
  haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine l34ExcNeFour_glauberman_contra hUodd σ hσσ hα₁irr hα₂irr hinvα₁ hinvα₂ hαne ?_
  intro c
  have hc0 : AlgIntModTwo (χ ((c : ↥(C.P.U)) : G)) 0 :=
    l34ne_chi_even (D.S) hχ hdeg4 (u := ((c : ↥(C.P.U)) : G))
      ⟨L, hLle, hLrel, fun l hl => hcent (c : ↥(C.P.U)) c.2 l hl⟩
  exact (hc0.symm.trans (hcongU c)).symm

end Work.BG
