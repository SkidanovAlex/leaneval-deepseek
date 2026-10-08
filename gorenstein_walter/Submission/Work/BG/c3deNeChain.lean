import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.Defs
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.hatInjCountAlt
import Submission.Work.BG.hatInjParity
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.glaubCorrDistinct
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma34Exc
import Submission.Work.BG.l34Exc_sfixed_four
import Submission.Work.BG.c3deChiEven
import Submission.Work.BG.c3deCongAlpha
import Submission.Work.BG.c3deExistsFixing
import Submission.Work.BG.c3deDegModFour
import Submission.Work.BG.c3deNeRestrictShape

/-!
# Assembly of BG Lemma 3.4 and the degree step `c3DegEq2`

This file assembles, from the pieces proved in this area, the two inputs needed by
`Work.BG.c3DegEq2`:

* `Work.BG.c3deNeFour` — the `|Λξ| ≠ 4` branch of the exceptional configuration of BG 1981
  Lemma 3.4 (p. 209), from `c3deNeRestrictShape`, `c3deDegModFour`, `c3deCongAlpha`,
  `c3deExistsFixing` and `c3deChiEven` together with Glauberman injectivity;
* `Work.BG.c3deLemma34` — BG Lemma 3.4 itself (`Work.GW2.C16.Lemma34Prop`), as an assembly of
  `c3deNeFour`, `Work.BG.l34Exc_sfixed_four` and `Work.BG.l34_no_third_nonfixed`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## Auxiliary facts about the exceptional configuration -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `𝒮(χ)` is stable under `s`-conjugation. -/
theorem c3de_sconj_mem_bset (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) {η : ClassFunction ↥C.P.H0 ℂ} (hη : η ∈ bset C f χ) :
    sconj C η ∈ bset C f χ := by
  refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hη.1, ?_⟩
  have hk : η ∈ orbitKey C η := Or.inl (s02c_LamEquiv_refl C η)
  have hfix : f (sconj C η) = f η := ((hf.1 η hη.1) η hk η hk hη.1 hη.1).2.1
  rw [hfix]
  exact hη.2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- The standing disjunction, `|Λν| = 4` and `s`-stability force `D.n = 4`. -/
theorem c3de_n_eq_four (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ}
    (hdisj : sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n)
    (hinv : sconj C '' lamOrbit C ν = lamOrbit C ν)
    (h4 : (lamOrbit C ν).ncard = 4) : D.n = 4 := by
  have hm : ν ∈ lamOrbit C ν := mem_lamOrbit_self C ν
  have hs : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, hm, rfl⟩
  rw [hinv] at hs
  rcases hdisj with h | h
  · exact absurd hs h
  · rw [h4] at h
    exact h.symm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `𝒮(χ) = {ν, ν^s, ξ}`. -/
theorem c3de_bset_eq (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hξ : ξ ∈ bset C f χ) (hξν : ξ ≠ ν) (hξνs : ξ ≠ sconj C ν) :
    bset C f χ = {ν, sconj C ν, ξ} := by
  have h2 : sconj C ν ∈ bset C f χ := c3de_sconj_mem_bset C f hf χ hν
  have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl
    · exact hν
    · exact h2
    · exact hξ
  have hsν : sconj C ν ≠ ν := hne
  have h1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hsν h.symm, fun h => hξν h.symm⟩
  have h2' : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => hξνs h.symm
  have hcard : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [show ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))
        = insert ν (insert (sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) from rfl,
      Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2' (Set.toFinite _), Set.ncard_singleton]
  have hle : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  have hge : 3 ≤ (bset C f χ).ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard hsub hfin
  have hb : (bset C f χ).ncard ≤ ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := by
    rw [hcard]; exact hle
  exact (Set.eq_of_subset_of_ncard_le hsub hb hfin).symm

open OddOrder.RepresentationTheory Work.BG in
/-- Injectivity of Glauberman's correspondence (`Work.BG.glaubCorrDistinct`) in the
"sum ≡ 0" form used by the exceptional configuration. -/
theorem c3de_glauberman_contra {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(fixedSubgroup σ)]
    [Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ)]
    {α₁ α₂ : ClassFunction U ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂)
    (hinv₁ : ∀ u : U, α₁ (σ u) = α₁ u) (hinv₂ : ∀ u : U, α₂ (σ u) = α₂ u)
    (hne : α₁ ≠ α₂)
    (hcong : ∀ c : ↥(fixedSubgroup σ),
      AlgIntModTwo (α₁ (c : U) + α₂ (c : U)) 0) : False := by
  have hcong' : ∀ c : ↥(fixedSubgroup σ), AlgIntModTwo (α₁ (c : U)) (α₂ (c : U)) := by
    intro c
    obtain ⟨z, hz, hzc⟩ := hcong c
    exact ⟨z - α₂ (c : U), hz.sub (isIntegral_apply_of_isIrreducibleCharacter hα₂ (c : U)),
      by linear_combination hzc⟩
  refine hne (glauberman_injective hU σ hσ (hatInjCountAlt hU σ hσ)
    (fun β => hatInjParity hU σ hσ β) hα₁ hinv₁ hα₂ hinv₂ (fun c => hcong' c))

/-! ## The `|Λξ| ≠ 4` branch of the exceptional configuration -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- BG 1981, Lemma 3.4, the `|Λξ| ≠ 4` branch of the exceptional configuration. -/
theorem c3deNeFour (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
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
  have hD4 : D.n = 4 := c3de_n_eq_four D C hdisj hinv h4
  have hbset : bset C f χ = {ν, sconj C ν, ξ} :=
    c3de_bset_eq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, hα1eq, hξα⟩, hcardξ⟩ :=
    c3deNeRestrictShape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs hξs hξ4
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
  have hdeg4 : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) :=
    c3deDegModFour D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs hξs
      hξ4 hbset hξdeg
  obtain ⟨σ, L, hσσ, hLle, hLrel, hinvα₁, hinvα₂, hcent⟩ :=
    c3deExistsFixing D C hDC hS3 hD4 hξ.1 hξs hα₁irr hα₂irr hαne hξα hcardξ
  have hcongU : ∀ u : ↥(C.P.U), AlgIntModTwo (χ (u : G)) (α₁ u + α₂ u) :=
    c3deCongAlpha D C hDC hS3 f hf χ hχ hν hξ hne hξν hξνs hbset hβirr hνβ hsνβ hξα
  have hUodd : Odd (Nat.card ↥(C.P.U)) := odd_card_U_of_compat hDC
  haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine c3de_glauberman_contra hUodd σ hσσ hα₁irr hα₂irr hinvα₁ hinvα₂ hαne ?_
  intro c
  have hc0 : AlgIntModTwo (χ ((c : ↥(C.P.U)) : G)) 0 :=
    c3deChiEven (D.S) hχ hdeg4 (u := ((c : ↥(C.P.U)) : G))
      ⟨L, hLle, hLrel, fun l hl => hcent (c : ↥(C.P.U)) c.2 l hl⟩
  exact (hc0.symm.trans (hcongU c)).symm

/-! ## BG Lemma 3.4 -/

section Helpers2

/-- Norm-one elements of `ℤ[Irr G]` that are not orthogonal to a signed irreducible are
`±` that irreducible. -/
private theorem c3de_eq_pm_of_inner_ne_zero {φ χ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hn : ClassFunction.inner φ φ = 1) (hχ : IsPmIrr χ)
    (h : ClassFunction.inner χ φ ≠ 0) : φ = χ ∨ φ = -χ := by
  obtain ⟨ε, ψ, hε, hφeq⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hn
  have hinner : ClassFunction.inner χ (ψ : ClassFunction G ℂ) ≠ 0 := by
    rcases hε with rfl | rfl
    · rw [one_smul] at hφeq; rw [← hφeq]; exact h
    · rw [neg_smul, one_smul] at hφeq
      have h' : ClassFunction.inner χ (-(ψ : ClassFunction G ℂ)) ≠ 0 := by
        rw [← hφeq]; exact h
      rw [ClassFunction.inner_neg_right] at h'
      exact neg_ne_zero.mp h'
  rcases hχ with hχi | hχi
  · have hχψ : χ = (ψ : ClassFunction G ℂ) := by
      by_contra hc
      have h0 : ClassFunction.inner χ (ψ : ClassFunction G ℂ) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨χ, hχi⟩ ψ]
        exact ite_eq_right (fun hh => hc (by simpa using congrArg Subtype.val hh))
      exact hinner h0
    rcases hε with rfl | rfl
    · left; rw [hφeq, one_smul]; exact hχψ.symm
    · right; rw [hφeq, neg_smul, one_smul, ← hχψ]
  · have hnegψ : -χ = (ψ : ClassFunction G ℂ) := by
      by_contra hc
      have h0 : ClassFunction.inner (-χ) (ψ : ClassFunction G ℂ) = 0 := by
        rw [irreducibleCharacter_inner_eq_ite ⟨-χ, hχi⟩ ψ]
        exact ite_eq_right (fun hh => hc (by simpa using congrArg Subtype.val hh))
      have hh := ClassFunction.inner_neg_left (G := G) χ (ψ : ClassFunction G ℂ)
      rw [h0] at hh
      exact hinner (neg_eq_zero.mp hh.symm)
    rcases hε with rfl | rfl
    · right; rw [hφeq, one_smul, ← hnegψ]
    · left
      have h2 : χ = -(ψ : ClassFunction G ℂ) := by
        have := congrArg (fun z : ClassFunction G ℂ => -z) hnegψ
        simpa using this
      rw [hφeq, neg_smul, one_smul, ← h2]

end Helpers2

/-- **BG Lemma 3.4, exceptional configuration** (BG 1981, p. 209): the assembled proof of
the "third character is impossible" statement, using `c3deNeFour` for the `|Λξ| ≠ 4` branch. -/
theorem c3deLemma34Exc (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
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
    · exact c3deNeFour D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv
        ξ hξ hξν hξνs hfix hξ4
  · exact l34_no_third_nonfixed D C hDC hS3 f hf χ hχ ν hν hne ξ hξ hξν hξνs hfix

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 in
/-- **BG Lemma 3.4** (`Work.GW2.C16.Lemma34Prop`), assembled from `c3deLemma34Exc`,
`Work.BG.thm32` and coherence. -/
theorem c3deLemma34 {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Work.GW2.C16.Lemma34Prop D C := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj
  obtain ⟨hνirr, hνne0⟩ := hν
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- the coherence clause at `(ν, ν)`
  have hkey : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  have hG := (hf.1 ν hνirr) ν hkey ν hkey hνirr hνirr
  obtain ⟨hZIfν, hsconjf, hnormf, -, -, hvi⟩ := hG
  have hnormf1 : ClassFunction.inner (f ν) (f ν) = 1 := by rw [hnormf]; simp [hne]
  -- `f ν` is a signed irreducible, and `χ = ± f ν`
  obtain ⟨ε, ψ, hε, hfeq⟩ :=
    exists_zsmul_irreducibleCharacter_of_inner_self_one hZIfν hnormf1
  have hpmfν : IsPmIrr (f ν) := by
    rcases hε with rfl | rfl
    · left; rw [hfeq, one_smul]; exact ψ.2
    · right
      have h2 : -(f ν) = (ψ : ClassFunction G ℂ) := by rw [hfeq]; simp
      rw [h2]; exact ψ.2
  have hχeq : χ = f ν ∨ χ = - f ν := by
    rcases c3de_eq_pm_of_inner_ne_zero hZIfν hnormf1 hχ hνne0 with h | h
    · exact Or.inl h.symm
    · refine Or.inr ?_
      have h2 : - f ν = χ := by rw [h]; simp
      exact h2.symm
  have hbset_eq : bset C f (f ν) = bset C f χ := by
    rcases hχeq with h | h
    · rw [h]
    · rw [h]
      ext η
      simp only [bset, Set.mem_ofPred_eq]
      rw [ClassFunction.inner_neg_left]
      simp
  have hνs_mem : sconj C ν ∈ bset C f χ := by
    refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hνirr, ?_⟩
    rw [hsconjf]; exact hνne0
  have hsub2 : ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl
    · exact ⟨hνirr, hνne0⟩
    · exact hνs_mem
  -- the value at `t`
  have hval : f ν (C.t : G) = 2 * ν C.t := by
    by_cases hexc : (lamOrbit C ν).ncard = 4 ∧ sconj C '' lamOrbit C ν = lamOrbit C ν
    · by_cases hbset : bset C f χ = {ν, sconj C ν}
      · -- only `ν`, `ν^s` occur in `𝒮(χ)`: Lemma 2.4 for `f ν` at `t`
        have hbsetν : bset C f (f ν) = {ν, sconj C ν} := by rw [hbset_eq]; exact hbset
        have hT := (lemma24 C f hf (f ν) hpmfν).2.1 C.t C.t_not_mem_U
        have hnot1 : ν ∉ ({sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
          intro hmem
          rw [Set.mem_singleton_iff] at hmem
          exact hne hmem.symm
        have hsum : (∑ᶠ η ∈ bset C f (f ν), ClassFunction.inner (f ν) (f η) * η C.t)
            = 2 * ν C.t := by
          rw [hbsetν,
            finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
              (a := ν) (s := ({sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ)))
              hnot1 (Set.toFinite _),
            finsum_mem_singleton,
            hsconjf, hnormf1, sconj_apply_t]
          ring
        rw [hsum] at hT
        exact hT
      · -- the exceptional configuration: `𝒮(χ)` cannot contain a third character
        have hne_sub : ¬ ((bset C f χ) ⊆ ({ν, sconj C ν} : Set (ClassFunction ↥C.P.H0 ℂ))) :=
          fun hsub => hbset (Set.Subset.antisymm hsub hsub2)
        obtain ⟨ξ, hξmem, hξnot⟩ := Set.not_subset.mp hne_sub
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hξnot
        exact (c3deLemma34Exc D C hDC hS3 f hf χ hχ ν ⟨hνirr, hνne0⟩ hne hdisj
          hexc.1 hexc.2 ξ hξmem (fun h => hξnot (Or.inl h))
            (fun h => hξnot (Or.inr h))).elim
    · exact hvi hne hexc
  -- `𝒮(χ) = {ν, ν^s}`
  have hcard : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  refine ⟨?_, hval⟩
  ext ξ
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hξ
    by_contra hnot
    have hξν : ξ ≠ ν := fun h => hnot (Or.inl h)
    have hξνs : ξ ≠ sconj C ν := fun h => hnot (Or.inr h)
    obtain ⟨hξirr, hξne0⟩ := hξ
    -- the three characters span `𝒮(χ)`
    have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
      intro η hη
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hη
      rcases hη with rfl | rfl | rfl
      · exact ⟨hνirr, hνne0⟩
      · exact hνs_mem
      · exact ⟨hξirr, hξne0⟩
    have hnot1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · exact hne h.symm
      · exact hξν h.symm
    have hnot2 : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      exact hξνs hmem.symm
    have h3 : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (s := ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            (a := ν) hnot1 (Set.toFinite _),
          Set.ncard_insert_of_notMem (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
            (a := sconj C ν) hnot2 (Set.toFinite _),
          Set.ncard_singleton]
    have heq : bset C f χ = {ν, sconj C ν, ξ} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [h3]; exact hcard) hfin).symm
    have hbsetν : bset C f (f ν) = {ν, sconj C ν, ξ} := by rw [hbset_eq]; exact heq
    -- Lemma 2.4 for `f ν` at `t`
    have hT := (lemma24 C f hf (f ν) hpmfν).2.1 C.t C.t_not_mem_U
    have hsum : (∑ᶠ η ∈ bset C f (f ν), ClassFunction.inner (f ν) (f η) * η C.t)
        = 2 * ν C.t + ClassFunction.inner (f ν) (f ξ) * ξ C.t := by
      rw [hbsetν,
        finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
          (a := ν) (s := ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)))
          hnot1 (Set.toFinite _),
        finsum_mem_insert (f := fun η => ClassFunction.inner (f ν) (f η) * η C.t)
          (a := sconj C ν) (s := ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot2 (Set.toFinite _),
        finsum_mem_singleton,
        hsconjf, hnormf1, sconj_apply_t]
      ring
    rw [hsum] at hT
    rw [hval] at hT
    have hξmemν : ξ ∈ bset C f (f ν) := by
      rw [hbsetν]
      exact Set.mem_insert_of_mem ν (Set.mem_insert_of_mem (sconj C ν) (Set.mem_singleton ξ))
    have hzero : ClassFunction.inner (f ν) (f ξ) * ξ C.t = 0 := by
      have h1 : 2 * ν C.t + ClassFunction.inner (f ν) (f ξ) * ξ C.t = 2 * ν C.t + 0 := by
        rw [add_zero]; exact hT.symm
      exact add_left_cancel h1
    exact mul_ne_zero hξmemν.2 (value_t_ne_zero C ξ hξirr) hzero
  · rintro (rfl | rfl)
    · exact ⟨hνirr, hνne0⟩
    · exact hνs_mem

end Work.BG
