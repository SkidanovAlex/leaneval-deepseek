import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.Core24
import Submission.Work.BG.lemma36
import Submission.Work.BG.kInvNormal
import Submission.Work.BG.c3FrobDegree
import Submission.Work.BG.kNeOneAlt
import Submission.Work.BG.existsNotKerOfSimple
import Submission.Work.BG.s02_lamDual

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

section Collapse

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **The disjunction of `C3DegreeProp` collapses to its second disjunct.**
If `𝒮(χ)` contains an `s`-fixed member `ν₀`, then every `ν ∈ 𝒮(χ)` is `Λ`-conjugate to its
`s`-conjugate: otherwise Lemma 3.4 (`Work.BG.lemma34Leaf`) forces `𝒮(χ) = {ν, ν^s}`, a set
containing no `s`-fixed character. -/
theorem c3Collapse (D : BGData G) (C : Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (ψ : ClassFunction G ℂ) (hψ : IsPmIrr ψ)
    (hdisj : (∃ ν ∈ bset C f ψ, sconj C ν = ν) ∨
      (∀ ν ∈ bset C f ψ, sconj C ν ∈ lamOrbit C ν)) :
    ∀ ν ∈ bset C f ψ, sconj C ν ∈ lamOrbit C ν := by
  intro ν hν
  rcases hdisj with ⟨ν₀, hν₀, hfix⟩ | hall
  · by_contra hnot
    by_cases hsν : sconj C ν = ν
    · exact hnot (by rw [hsν]; exact s02c_LamEquiv_refl C ν)
    · obtain ⟨hbset, -⟩ :=
        lemma34Leaf D C hComp hS3 f hf ψ hψ ν hν hsν (Or.inl hnot)
      have hmem : ν₀ ∈ ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
        rw [← hbset]; exact hν₀
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact hsν (by rw [← h]; exact hfix)
      · have h2 : sconj C (sconj C ν) = sconj C ν := by rw [← h]; exact hfix
        rw [sconj_sconj] at h2
        exact hsν h2.symm
  · exact hall ν hν

end Collapse

/-
# Area BG: `Work.BG.c3Degree` — `Work.GW2.C16.C3DegreeProp` (BG 1981, C3-4)

`C3DegreeProp D C K1 K2` is the degree bound of BG 1981, p. 211 (`|χ(1)| ≥ 8A + 1` with
`A ≥ |B|` when `U ≠ BK`), consumed by `thmCBigAsm`.

The route (design pass 24, `NOTES_LEAD_gw_design24.md`) is:

* `K := K1 ⊓ K2` is non-trivial (`Work.BG.kNeOneAlt`, BG Remark 3.5), so `K ⊄ ker χ` for the
  non-principal irreducible `χ` (`Work.BG.existsNotKerOfSimple`);
* BG Lemma 3.6 in the corrected form `C24.Lemma36InvProp` (`Work.BG.lemma36`), with its group
  hypotheses supplied by G11 (`Work.BG.kInvNormal`) and assembled by the *proved*
  `Work.GW2.C24.lemma36_thmC`, gives `a ∈ Irr(U)` non-trivial on `K` with
  `2 * D.n * a(1) < χ(1)`;
* in the case `U ≠ BK` the Frobenius clause of `ThmCHyps` gives `|B| ≤ a(1)`
  (`Work.BG.c3FrobDegree`);
* since `4 ≤ D.n`, `2 * D.n * a(1) ≥ 8 a(1)`, so `A := |B|` (case `U ≠ BK`) or `A := 1`
  (case `U = BK`) works.

The disjunction hypothesis is reduced to its second disjunct by `c3Collapse` (Lemma 3.4).
-/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C24 in
theorem c3Degree {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.C3DegreeProp D C K1 K2 := by
  intro hComp hHyps hSimp hn4 f hf χ hχ hbot hdisj hne
  have hS3 : Sec3Hyp D :=
    (thmCSec3 G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1).1
  have hKne : K1 ⊓ K2 ≠ ⊥ :=
    kNeOneAlt G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1 hHyps.2.2.2.2.2 hSimp
  -- pick an irreducible `ψ` with `χ = ±ψ`
  obtain ⟨ψ, hψirr, hcases⟩ : ∃ ψ : ClassFunction G ℂ,
      IsIrreducibleCharacter ψ ∧ (χ = ψ ∨ χ = -ψ) := by
    rcases hχ with h | h
    · exact ⟨χ, h, Or.inl rfl⟩
    · exact ⟨-χ, h, Or.inr (by simp)⟩
  have hbotψ : ClassFunction.inner ψ (trivialClassFunction G) = 0 := by
    rcases hcases with h | h
    · rw [← h]; exact hbot
    · have hψeq : ψ = -χ := by rw [h]; simp
      rw [hψeq, ClassFunction.inner_neg_left, hbot, neg_zero]
  have hbset : bset C f ψ = bset C f χ := by
    rcases hcases with h | h
    · rw [h]
    · rw [h]
      ext ν
      simp only [bset, Set.mem_ofPred_eq]
      rw [ClassFunction.inner_neg_left]
      simp
  have hneψ : (bset C f ψ).Nonempty := by rwa [hbset]
  have hdisjψ : (∃ ν ∈ bset C f ψ, sconj C ν = ν) ∨
      (∀ ν ∈ bset C f ψ, sconj C ν ∈ lamOrbit C ν) := by
    rcases hdisj with ⟨ν, hν, hfix⟩ | hall
    · refine Or.inl ⟨ν, ?_, hfix⟩
      rwa [hbset]
    · refine Or.inr fun ν hν => hall ν ?_
      rwa [← hbset]
  have hsl : ∀ ν ∈ bset C f ψ, sconj C ν ∈ lamOrbit C ν :=
    c3Collapse D C K1 K2 hComp hS3 f hf ψ (Or.inl hψirr) hdisjψ
  have hKker : ∃ x ∈ K1 ⊓ K2, ψ x ≠ ψ 1 :=
    existsNotKerOfSimple (K1 ⊓ K2) ψ hKne hSimp (Or.inl hψirr) hbotψ
  -- BG Lemma 3.6 (corrected), via the proved assembly `lemma36_thmC`
  obtain ⟨a, ha, haK, dχ, da, hψ1, ha1, hineq⟩ :=
    lemma36_thmC (fun D C _ K => lemma36 D C K) kInvNormal D C K1 K2 hComp hS3 hHyps
      f hf ψ hψirr hneψ hKker hsl
  -- `a 1 ≠ 0`
  have hda1 : 1 ≤ da := by
    rcases Nat.eq_zero_or_pos da with h | h
    · exfalso
      rw [h] at ha1
      norm_num at ha1
      exact IsPmIrr.apply_one_ne_zero (Or.inl ha) ha1
    · exact h
  -- the conclusion, first for `ψ`
  have hψconc : ∃ A : ℕ, 1 ≤ A ∧ (D.U ≠ D.B ⊔ (K1 ⊓ K2) → Nat.card D.B ≤ A) ∧
      ∃ d : ℤ, ψ 1 = (d : ℂ) ∧ 8 * (A : ℤ) + 1 ≤ |d| := by
    by_cases hUBK : D.U = D.B ⊔ (K1 ⊓ K2)
    · refine ⟨1, le_refl 1, fun h => absurd hUBK h, (dχ : ℤ), ?_, ?_⟩
      · push_cast; exact hψ1
      have h9 : 9 ≤ dχ := by
        have h2 : 8 ≤ 2 * D.n := by omega
        nlinarith [hineq, h2, hda1]
      have habs : |((dχ : ℤ))| = (dχ : ℤ) := abs_of_nonneg (by positivity)
      rw [habs]
      push_cast
      exact_mod_cast h9
    · obtain ⟨da', hda', hBle⟩ := c3FrobDegree D C K1 K2 hComp hHyps a ha haK hUBK
      have hdaeq : da' = da := by
        apply Nat.cast_injective (R := ℂ)
        rw [← hda', ha1]
      have hBda : Nat.card D.B ≤ da := hdaeq ▸ hBle
      refine ⟨Nat.card D.B, ?_, fun _ => le_refl _, (dχ : ℤ), hψ1, ?_⟩
      · have := Nat.card_pos (α := ↥D.B); omega
      have h2 : 8 ≤ 2 * D.n := by omega
      have h3 : 8 * Nat.card D.B ≤ 2 * D.n * da := by
        calc 8 * Nat.card D.B ≤ 8 * da := Nat.mul_le_mul_left 8 hBda
          _ ≤ 2 * D.n * da := Nat.mul_le_mul_right da h2
      have hfin : 8 * Nat.card D.B + 1 ≤ dχ := by omega
      have habs : |((dχ : ℤ))| = (dχ : ℤ) := abs_of_nonneg (by positivity)
      rw [habs]
      push_cast
      exact_mod_cast hfin
  obtain ⟨A, hA1, hAB, d, hd, hineq'⟩ := hψconc
  rcases hcases with h | h
  · exact ⟨A, hA1, hAB, d, by rw [h]; exact hd, hineq'⟩
  · refine ⟨A, hA1, hAB, -d, ?_, ?_⟩
    · rw [h, ClassFunction.neg_apply, hd]
      push_cast
      ring
    · rw [abs_neg]; exact hineq'

end Work.BG
