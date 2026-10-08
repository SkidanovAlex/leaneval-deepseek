import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.l34Exc_sfixed_four
import Submission.Work.BG.l34Exc_sfixed_ne_four

/-!
# Area BG: the exceptional configuration of Bender–Glauberman 1981, Lemma 3.4

`Work.GW2.C16.Lemma34Prop` (BG Lemma 3.4, p. 209) says that if `χ ∈ ±Irr(G)` and `𝒮(χ)`
contains a character `ν` with `ν^s ≠ ν` and (`ν^s ∉ Λν` or `|Λν| = m`), then
`𝒮(χ) = {ν, ν^s}` and `ν̃(t) = 2ν(t)`.  `Work.BG.lemma34Leaf` assembles that from
Theorem 3.2 (`Work.BG.thm32`), Lemma 2.4 (`Work.BG.lemma24`) and the present file: in the
exceptional configuration

  `|Λν| = 4`,  `(Λν)^s = Λν`,  `𝒮(χ) ≠ {ν, ν^s}`,

there is **no third member of `𝒮(χ)`**.

## What is proved here

* `l34_sconj_mem_bset`: `𝒮(χ)` is `s`-stable (coherence gives `f (sconj C ξ) = f ξ`).
* `l34_no_third_nonfixed`: **an `s`-non-fixed third member is impossible** — if
  `ξ ∈ 𝒮(χ)`, `ξ ∉ {ν, ν^s}` and `ξ^s ≠ ξ`, then `ν, ν^s, ξ, ξ^s` are four distinct members of
  `𝒮(χ)`, contradicting BG Theorem 3.2 (`|𝒮(χ)| ≤ 3`, `Work.BG.thm32`).
* `lemma34Exc` then reduces everything to the `s`-fixed third member `ξ`.

## The remaining case (`ξ` `s`-fixed)

This is the paper's separate computation on the exceptional configuration (`|S| = 8`,
`m = |H₀ : U| = 4`).  It splits by the size of `Λξ`:

* `Work.BG.l34Exc_sfixed_four` (`|Λξ| = 4`): Lemma 3.3 together with coherence — the
  constituents of `f ξ` orthogonal to `χ = ±fν` are orthogonal to both `s`-fixed characters
  of `Λν`, and Lemma 3.3 applied to the `±Irr` element `fξ - e_ξχ` forces `D.n = 2`,
  contradicting `D.n = 4`.
* `Work.BG.l34Exc_sfixed_ne_four` (`|Λξ| ≠ 4`, hence `|Λξ| = 2` by Remark 3.1): the degree
  count on `B₁ = C_U(t₁)` — Gorenstein 4.2.10 (`Work.GW2.C16.CentralIntegralProp`, proved as
  `Work.BG.centralIntegral`) with `4 ∣ χ(1)` gives `χ ≡ 0` mod `2` on `B₁`, while Lemma 2.4
  with Lemmas 1.8/1.9 (`Work.BG.lemma18LinearIndependent`,
  `Work.GW2.C16.GlaubValueProp` proved as `Work.BG.glaubValue`) gives
  `χ ≡ α₁* + α₂*` mod `2` on `B₁` with two *distinct* irreducibles of `B₁`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- Coherence keeps membership in `𝒮(χ)` under `s`-conjugation: `f (ξ^s) = f ξ`, so
`(χ, f (ξ^s)) = (χ, f ξ)`. -/
theorem l34_sconj_mem_bset (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) {ξ : ClassFunction ↥C.P.H0 ℂ} (hξ : ξ ∈ bset C f χ) :
    sconj C ξ ∈ bset C f χ := by
  refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hξ.1, ?_⟩
  have hk : ξ ∈ orbitKey C ξ := Or.inl (s02c_LamEquiv_refl C ξ)
  have hfix : f (sconj C ξ) = f ξ := ((hf.1 ξ hξ.1) ξ hk ξ hk hξ.1 hξ.1).2.1
  rw [hfix]
  exact hξ.2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Reduction to the `s`-fixed case.**  If `ξ ∈ 𝒮(χ) ∖ {ν, ν^s}` is not `s`-fixed, then
`ν, ν^s, ξ, ξ^s` are four distinct members of `𝒮(χ)`, contradicting Theorem 3.2
(`|𝒮(χ)| ≤ 3`). -/
theorem l34_no_third_nonfixed (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (ξ : ClassFunction ↥C.P.H0 ℂ) (hξ : ξ ∈ bset C f χ) (hξν : ξ ≠ ν)
    (hξνs : ξ ≠ sconj C ν) (hξs : sconj C ξ ≠ ξ) : False := by
  have h2 : sconj C ν ∈ bset C f χ := l34_sconj_mem_bset C f hf χ hν
  have h4 : sconj C ξ ∈ bset C f χ := l34_sconj_mem_bset C f hf χ hξ
  have h12 : ν ≠ sconj C ν := fun h => hne h.symm
  have h13 : ν ≠ ξ := fun h => hξν h.symm
  have h14 : ν ≠ sconj C ξ := by
    intro h
    apply hξνs
    calc ξ = sconj C (sconj C ξ) := (s02c_sconj_involutive C ξ).symm
      _ = sconj C ν := by rw [← h]
  have h23 : sconj C ν ≠ ξ := by
    intro h
    apply h14
    calc ν = sconj C (sconj C ν) := (s02c_sconj_involutive C ν).symm
      _ = sconj C ξ := by rw [h]
  have h24 : sconj C ν ≠ sconj C ξ := by
    intro h
    apply h13
    calc ν = sconj C (sconj C ν) := (s02c_sconj_involutive C ν).symm
      _ = sconj C (sconj C ξ) := by rw [h]
      _ = ξ := s02c_sconj_involutive C ξ
  have h34 : ξ ≠ sconj C ξ := fun h => hξs h.symm
  have hsub : ({ν, sconj C ν, ξ, sconj C ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl | rfl
    · exact hν
    · exact h2
    · exact hξ
    · exact h4
  have hncard : ({ν, sconj C ν, ξ, sconj C ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13, h14]),
      Set.ncard_insert_of_notMem (by simp [h23, h24]),
      Set.ncard_insert_of_notMem (by simp [h34]), Set.ncard_singleton]
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  have hle4 : 4 ≤ (bset C f χ).ncard := by
    have := Set.ncard_le_ncard hsub hfin
    omega
  have hle3 : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  omega

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma34Exc {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs
  by_cases hfix : sconj C ξ = ξ
  · by_cases hξ4 : (lamOrbit C ξ).ncard = 4
    · exact l34Exc_sfixed_four D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv
        ξ hξ hξν hξνs hfix hξ4
    · exact l34Exc_sfixed_ne_four D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv
        ξ hξ hξν hξνs hfix hξ4
  · exact l34_no_third_nonfixed D C hDC hS3 f hf χ hχ ν hν hne ξ hξ hξν hξνs hfix

end Work.BG
