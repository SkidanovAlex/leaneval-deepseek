import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubCorrDistinct
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.s02_bsValueT_aux
import Submission.Work.BG.l34ne_restrict_shape
import Submission.Work.BG.l34ne_cong_alpha
import Submission.Work.BG.l34ne_chi_even
import Submission.Work.BG.l34ExcNeFourAux
import Submission.Work.BG.nt_exists_fixing_action
import Submission.Work.BG.chi_deg_mod_four

/-!
# Area BG: `Work.BG.noThirdSfixedNeFour`

Bender–Glauberman 1981, Lemma 3.4, the exceptional configuration in which the non-`s`-fixed
member `ν ∈ 𝒮(χ) = bset C f χ` (`|Λν| = 4`, `(Λν)^s = Λν`, so `|S| = 8`, `D.n = 4`) is
accompanied by an `s`-fixed `ξ ∈ 𝒮(χ)` with `|Λξ| ≠ 4` (hence `|Λξ| = 2`).  No such
configuration exists: this is the `|Λξ| ≠ 4` half of `Work.BG.lemma34Exc`.

Assembly (the paper's proof, pp. 209–210):

* `𝒮(χ) = {ν, ν^s, ξ}` and `D.n = 4`
  (`Work.BG.l34ExcNeFour_bset_eq`, `Work.BG.l34ExcNeFour_n_eq_four`);
* Remark 3.1 (`Work.BG.l34ne_restrict_shape`): `ν|_U = β` irreducible,
  `ξ|_U = α₁ + α₂` with `α₁ ≠ α₂` of equal degree, and `|Λξ| = 2`;
* the paper's degree count (`Work.BG.chi_deg_mod_four`): `4 ∣ χ(1)`;
* Lemma 2.4 on `U` (`Work.BG.l34ne_cong_alpha`): `χ ≡ α₁ + α₂ (mod 2)` on `U`;
* the constituent structure of `ξ|_U` supplies an involutive automorphism `σ` of `U` fixing
  both `α₁`, `α₂`, and an index-`≤ 2` subgroup `L ≤ S` centralising `C_U(σ)`
  (`Work.BG.l34ne_exists_fixing_action`);
* Gorenstein 4.2.10 with `4 ∣ χ(1)` makes `χ` even on `C_U(σ)` (`Work.BG.l34ne_chi_even`),
  so `α₁ + α₂ ≡ 0` there, contradicting the injectivity of Glauberman's correspondence
  (BG Lemma 1.9) for the distinct `σ`-invariant `α₁ ≠ α₂`
  (`Work.BG.l34ExcNeFour_glauberman_contra`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem noThirdSfixedNeFour {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
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
  -- `D.n = 4`
  have hD4 : D.n = 4 := l34ExcNeFour_n_eq_four D C hdisj hinv h4
  -- `𝒮(χ) = {ν, ν^s, ξ}`
  have hbset : bset C f χ = {ν, sconj C ν, ξ} :=
    l34ExcNeFour_bset_eq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs
  -- the restriction shapes (Remark 3.1)
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, _hα1eq, hξα⟩, hcardξ⟩ :=
    l34ne_restrict_shape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs hξs hξ4
  -- the degree count: `4 ∣ χ(1)`
  have hdeg4 : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) :=
    chi_deg_mod_four D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξs hξ4
  -- the fixing involution and the index-`≤ 2` subgroup
  obtain ⟨σ, L, hσσ, hLle, hLrel, hinvα₁, hinvα₂, hcent⟩ :=
    nt_exists_fixing_action D C hDC hS3 hD4 hξ.1 hξs hα₁irr hα₂irr hαne hξα hcardξ
  -- `χ ≡ α₁ + α₂ (mod 2)` on `U` (Lemma 2.4)
  have hcongU : ∀ u : ↥(C.P.U), AlgIntModTwo (χ (u : G)) (α₁ u + α₂ u) :=
    l34ne_cong_alpha D C hDC hS3 f hf χ hχ hν hξ hne hξν hξνs hbset hβirr hνβ hsνβ hξα
  -- `χ ≡ 0 (mod 2)` on `C_U(σ)`, hence `α₁ + α₂ ≡ 0 (mod 2)` there
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
