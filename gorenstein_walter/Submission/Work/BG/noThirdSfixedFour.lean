import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma33Case2
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.lemma33Case1b
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_abstractCoherence

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-! ## 0. Elementary orthonormality facts for `ℤ[Irr G]` -/

section Elementary

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `(χ, χ) = 1` for a signed irreducible character `χ`. -/
theorem ns4_inner_self_pmIrr {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ) :
    ClassFunction.inner χ χ = 1 := by
  rcases hχ with h | h
  · exact (irreducibleCharacter_inner_eq_ite ⟨χ, h⟩ ⟨χ, h⟩).trans (ite_eq_left rfl)
  · have h2 : ClassFunction.inner (-χ) (-χ) = 1 :=
      (irreducibleCharacter_inner_eq_ite ⟨-χ, h⟩ ⟨-χ, h⟩).trans (ite_eq_left rfl)
    rwa [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg] at h2

/-- A norm-one element of `ℤ[Irr G]` that is not orthogonal to a signed irreducible `χ`
equals `±χ`. -/
theorem ns4_eq_pm_of_inner_ne_zero {φ χ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (hn : ClassFunction.inner φ φ = 1) (hχ : IsPmIrr χ)
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

/-- A virtual character `X ∈ ℤ[Irr G]` disjoint from `Y ∈ ℤ[Irr G]` is orthogonal to `Y`. -/
theorem ns4_inner_eq_zero_of_disjointCF {X Y : ClassFunction G ℂ} (hY : Y ∈ ZIrr G)
    (h : DisjointCF X Y) : ClassFunction.inner X Y = 0 := by
  classical
  obtain ⟨c, hsupp, hYeq⟩ := mem_ZIrr_repr hY
  have hcoeff : ∀ b ∈ c.support, (c b : ℂ) = 0 ∨ ClassFunction.inner X b = 0 := by
    intro b hb
    by_cases hXb : ClassFunction.inner X b = 0
    · exact Or.inr hXb
    · refine Or.inl ?_
      have hb' : IsIrreducibleCharacter b := hsupp (Finset.mem_coe.mpr hb)
      have hYb : ClassFunction.inner Y b = 0 := (h ⟨b, hb'⟩).resolve_left hXb
      rw [hYeq, inner_eq_coeff_of_repr ⟨b, hb'⟩ hsupp] at hYb
      exact hYb
  rw [hYeq, inner_sum_right]
  refine Finset.sum_eq_zero fun b hb => ?_
  rcases hcoeff b hb with h1 | h1
  · rw [h1, zero_smul, ClassFunction.inner_zero_right]
  · rw [ClassFunction.inner_smul_right, h1, mul_zero]

end Elementary

/-! ## 1. The `|S| ≥ 8` branch of BG Lemma 3.3 in "contradiction" form -/

section TwoSfixed

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **BG Lemma 3.3, contrapositive form.**  For `χ ∈ ±Irr(G)` and `4 ≤ D.n`, the support
`𝒮(χ) = bset C f χ` cannot contain two distinct `s`-fixed characters whose `Λ`-orbits have
`D.n` elements.  (Assembly: if there is a third such character, `lemma33Case2`; otherwise
`lemma33Case1b`.) -/
theorem twoSfixedMaximalClean {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Compat D C → Sec3Hyp D → 4 ≤ D.n →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
    ∀ ν₁ ∈ bset C f χ, ∀ ν₂ ∈ bset C f χ, ν₁ ≠ ν₂ →
    sconj C ν₁ = ν₁ → sconj C ν₂ = ν₂ →
    (lamOrbit C ν₁).ncard = D.n → (lamOrbit C ν₂).ncard = D.n → False := by
  intro hDC hS3 hn f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hs1 hs2 ho1 ho2
  by_cases hthird : ∃ ν₃ : ClassFunction ↥C.P.H0 ℂ,
      ν₃ ∈ bset C f χ ∧ ν₃ ≠ ν₁ ∧ ν₃ ≠ ν₂ ∧ sconj C ν₃ = ν₃ ∧
        (lamOrbit C ν₃).ncard = D.n
  · obtain ⟨ν₃, h₃mem, h₃₁, h₃₂, h₃s, h₃o⟩ := hthird
    exact lemma33Case2 D C hDC hS3 f hf χ hχ hn ν₁ hν₁ ν₂ hν₂ ν₃ h₃mem
      hne (Ne.symm h₃₁) (Ne.symm h₃₂) hs1 hs2 h₃s ho1 ho2 h₃o
  · refine lemma33Case1b D C hDC hS3 f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hs1 hs2 ho1 ho2 ?_
    intro ν hνmem hs ho
    by_contra hc
    exact hthird ⟨ν, hνmem, (fun h => hc (Or.inl h)), (fun h => hc (Or.inr h)), hs, ho⟩

end TwoSfixed

/-! ## 2. The main theorem -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem noThirdSfixedFour {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard = 4 → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4ν hinv ξ hξ hξν hξνs hξs hξ4
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  obtain ⟨hνirr, hνne0⟩ := hν
  obtain ⟨hξirr, hξne0⟩ := hξ
  have hνmem : ν ∈ bset C f χ := ⟨hνirr, hνne0⟩
  have hξmem : ξ ∈ bset C f χ := ⟨hξirr, hξne0⟩
  -- ## coherence data at `ν` and at `ξ`
  have hkeyν : ν ∈ orbitKey C ν := Or.inl (s02c_LamEquiv_refl C ν)
  obtain ⟨hZIfν, hfνs, hnormfν, -, -, -⟩ := (hf.1 ν hνirr) ν hkeyν ν hkeyν hνirr hνirr
  have hnormfν1 : ClassFunction.inner (f ν) (f ν) = 1 := by
    rw [hnormfν]; simp [hne]
  have hkeyξ : ξ ∈ orbitKey C ξ := Or.inl (s02c_LamEquiv_refl C ξ)
  obtain ⟨hZIfξ, hfξs, hnormfξ, -, -, -⟩ := (hf.1 ξ hξirr) ξ hkeyξ ξ hkeyξ hξirr hξirr
  have hnormfξ2 : ClassFunction.inner (f ξ) (f ξ) = 2 := by
    rw [hnormfξ]; simp [hξs]
  -- ## `D.n = 4`
  have hmem : sconj C ν ∈ lamOrbit C ν := by
    have h : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, s02c_LamEquiv_refl C ν, rfl⟩
    rwa [hinv] at h
  have hn4 : D.n = 4 := by
    rcases hdisj with h | h
    · exact absurd hmem h
    · omega
  -- ## `ξ ∉ Λν`
  have hbset2 := (bset_orbit_struct C f hf χ hχ).2
  have hξnotlam : ¬ LamEquiv C ν ξ :=
    fun hlam => hξνs (hbset2 ν hνmem ξ hξmem hlam hξν)
  have hnotlam' : ¬ LamEquiv C ξ ν := fun h => hξnotlam (s02c_LamEquiv_symm C h)
  have hnotlamνs : ¬ LamEquiv C (sconj C ν) ξ :=
    fun h => hξnotlam (s02c_LamEquiv_trans C hmem h)
  -- ## the two `s`-fixed members `ν'`, `ν''` of `Λν`
  have hfixν :
      ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 :=
    ((s02_lemma21 C) ν hνirr).2 hinv
  have hEνfin : ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    (orbit_finite C ν).subset (fun _ hx => hx.1)
  obtain ⟨ν', hν'Eν⟩ := (Set.ncard_pos hEνfin).mp (by omega)
  have hEνdiff : (({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)) \ {ν'}).Finite :=
    hEνfin.subset Set.sdiff_subset
  have hEνdiffcard : (({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)) \ {ν'}).ncard = 1 := by
    have h := Set.ncard_sdiff_singleton_of_mem hν'Eν
    rw [hfixν] at h
    simpa using h
  obtain ⟨ν'', hν''Eν⟩ := (Set.ncard_pos hEνdiff).mp (by rw [hEνdiffcard]; norm_num)
  have hν'memS : ν' ∈ lamOrbit C ν ∧ sconj C ν' = ν' := hν'Eν
  have hν''memS : ν'' ∈ lamOrbit C ν ∧ sconj C ν'' = ν'' := hν''Eν.1
  have hν''ne' : ν'' ≠ ν' := hν''Eν.2
  have hν'irr : IsIrreducibleCharacter ν' := irreducible_of_mem_lamOrbit C hν'memS.1 hνirr
  have hν''irr : IsIrreducibleCharacter ν'' := irreducible_of_mem_lamOrbit C hν''memS.1 hνirr
  have hν'orbit_eq : lamOrbit C ν' = lamOrbit C ν :=
    (lamOrbit_eq_of_lamEquiv hν'memS.1).symm
  have hν''orbit_eq : lamOrbit C ν'' = lamOrbit C ν :=
    (lamOrbit_eq_of_lamEquiv hν''memS.1).symm
  have hν'neν : ν' ≠ ν := by
    intro h
    exact hne (by calc sconj C ν = sconj C ν' := by rw [h]
      _ = ν' := hν'memS.2
      _ = ν := h)
  have hν''neν : ν'' ≠ ν := by
    intro h
    exact hne (by calc sconj C ν = sconj C ν'' := by rw [h]
      _ = ν'' := hν''memS.2
      _ = ν := h)
  have hν'ν''Lam : LamEquiv C ν' ν'' :=
    s02c_LamEquiv_trans C (s02c_LamEquiv_symm C hν'memS.1) hν''memS.1
  have hnormfν'2 : ClassFunction.inner (f ν') (f ν') = 2 := by
    have hkey : ν' ∈ orbitKey C ν' := Or.inl (s02c_LamEquiv_refl C ν')
    have h := ((hf.1 ν' hν'irr) ν' hkey ν' hkey hν'irr hν'irr).2.2.1
    rw [h]; simp [hν'memS.2]
  have hnormfν''2 : ClassFunction.inner (f ν'') (f ν'') = 2 := by
    have hkey : ν'' ∈ orbitKey C ν'' := Or.inl (s02c_LamEquiv_refl C ν'')
    have h := ((hf.1 ν'' hν''irr) ν'' hkey ν'' hkey hν''irr hν''irr).2.2.1
    rw [h]; simp [hν''memS.2]
  have hZIfν' : f ν' ∈ ZIrr G :=
    ((hf.1 ν' hν'irr) ν' (Or.inl (s02c_LamEquiv_refl C ν')) ν'
      (Or.inl (s02c_LamEquiv_refl C ν')) hν'irr hν'irr).1
  have hZIfν'' : f ν'' ∈ ZIrr G :=
    ((hf.1 ν'' hν''irr) ν'' (Or.inl (s02c_LamEquiv_refl C ν'')) ν''
      (Or.inl (s02c_LamEquiv_refl C ν'')) hν''irr hν''irr).1
  -- ## the second `s`-fixed member `ξ₂` of `Λξ`, and a non-fixed `μ ∈ Λξ`
  have hξstab : sconj C '' lamOrbit C ξ = lamOrbit C ξ := by
    rw [s02c_sconj_image_lamOrbit C (sconjLam C) ξ, hξs]
  have hfixξ :
      ({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 :=
    ((s02_lemma21 C) ξ hξirr).2 hξstab
  have hξinE : ξ ∈ ({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)) := ⟨s02c_LamEquiv_refl C ξ, hξs⟩
  have hEξfin : ({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    (orbit_finite C ξ).subset (fun _ hx => hx.1)
  have hEξdiff : (({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)) \ {ξ}).Finite :=
    hEξfin.subset Set.sdiff_subset
  have hEξdiffcard : (({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} :
      Set (ClassFunction ↥C.P.H0 ℂ)) \ {ξ}).ncard = 1 := by
    have h := Set.ncard_sdiff_singleton_of_mem hξinE
    rw [hfixξ] at h
    simpa using h
  obtain ⟨ξ₂, hξ₂E⟩ := (Set.ncard_pos hEξdiff).mp (by rw [hEξdiffcard]; norm_num)
  have hξ₂memS : ξ₂ ∈ lamOrbit C ξ ∧ sconj C ξ₂ = ξ₂ := hξ₂E.1
  have hξ₂ne : ξ₂ ≠ ξ := hξ₂E.2
  have hξ₂irr : IsIrreducibleCharacter ξ₂ := irreducible_of_mem_lamOrbit C hξ₂memS.1 hξirr
  have hμexists : ∃ μ : ClassFunction ↥C.P.H0 ℂ, μ ∈ lamOrbit C ξ ∧ sconj C μ ≠ μ := by
    by_contra hc
    push_neg at hc
    have hset : ({χ' ∈ lamOrbit C ξ | sconj C χ' = χ'} : Set (ClassFunction ↥C.P.H0 ℂ))
        = lamOrbit C ξ :=
      Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, hc x hx⟩⟩
    rw [hset, hξ4] at hfixξ
    norm_num at hfixξ
  obtain ⟨μ, hμorbit, hμnotfix⟩ := hμexists
  have hμirr : IsIrreducibleCharacter μ := irreducible_of_mem_lamOrbit C hμorbit hξirr
  have hμneξ : μ ≠ ξ := fun h => hμnotfix (h ▸ hξs)
  have hξ₂neμ : ξ₂ ≠ μ := fun h => hμnotfix (h ▸ hξ₂memS.2)
  have hξ₂nesμ : ξ₂ ≠ sconj C μ := by
    intro h
    have h1 : sconj C ξ₂ = sconj C (sconj C μ) := by rw [h]
    rw [hξ₂memS.2, s02c_sconj_involutive] at h1
    exact hξ₂neμ h1
  have hμLam : LamEquiv C ξ₂ μ :=
    s02c_LamEquiv_trans C (s02c_LamEquiv_symm C hξ₂memS.1) hμorbit
  -- ## non-membership of `Λξ ∖ {ξ}` and of `Λν ∖ {ν, ν^s}` in `𝒮(χ)`
  have hnotmem : ∀ η : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter η →
      η ∈ lamOrbit C ξ → η ≠ ξ → ClassFunction.inner χ (f η) = 0 := by
    intro η hηirr hηorbit hηne
    by_contra h0
    have h := hbset2 ξ hξmem η ⟨hηirr, h0⟩ hηorbit hηne
    exact hηne (by rw [h, hξs])
  have hχfξ₂ : ClassFunction.inner χ (f ξ₂) = 0 := hnotmem ξ₂ hξ₂irr hξ₂memS.1 hξ₂ne
  have hχfμ : ClassFunction.inner χ (f μ) = 0 := hnotmem μ hμirr hμorbit hμneξ
  have hχfν' : ClassFunction.inner χ (f ν') = 0 := by
    by_contra h0
    have h := hbset2 ν hνmem ν' ⟨hν'irr, h0⟩ hν'memS.1 hν'neν
    have h1 : ν = ν' := by
      calc ν = sconj C (sconj C ν) := (s02c_sconj_involutive C ν).symm
        _ = sconj C ν' := by rw [← h]
        _ = ν' := hν'memS.2
    exact hne (h.symm.trans h1.symm)
  have hχfν'' : ClassFunction.inner χ (f ν'') = 0 := by
    by_contra h0
    have h := hbset2 ν hνmem ν'' ⟨hν''irr, h0⟩ hν''memS.1 hν''neν
    have h1 : ν = ν'' := by
      calc ν = sconj C (sconj C ν) := (s02c_sconj_involutive C ν).symm
        _ = sconj C ν'' := by rw [← h]
        _ = ν'' := hν''memS.2
    exact hne (h.symm.trans h1.symm)
  -- ## `f ν = ±χ`
  have hνeqpm : f ν = χ ∨ f ν = -χ :=
    ns4_eq_pm_of_inner_ne_zero hZIfν hnormfν1 hχ hνne0
  have hνξ₂ : ClassFunction.inner (f ν) (f ξ₂) = 0 := by
    rcases hνeqpm with h | h
    · rw [h]; exact hχfξ₂
    · rw [h, ClassFunction.inner_neg_left, hχfξ₂, neg_zero]
  have hνμ : ClassFunction.inner (f ν) (f μ) = 0 := by
    rcases hνeqpm with h | h
    · rw [h]; exact hχfμ
    · rw [h, ClassFunction.inner_neg_left, hχfμ, neg_zero]
  have hνξ₂s : ClassFunction.inner (f ξ₂) (f ν) = 0 := by
    rw [ClassFunction.inner_star_comm, hνξ₂, star_zero]
  have hνμs : ClassFunction.inner (f μ) (f ν) = 0 := by
    rw [ClassFunction.inner_star_comm, hνμ, star_zero]
  -- ## `ℤ[Irr]`-data for `μ`, `ξ₂`, and the disjointness facts
  have hZIfμ : f μ ∈ ZIrr G :=
    ((hf.1 μ hμirr) μ (Or.inl (s02c_LamEquiv_refl C μ)) μ
      (Or.inl (s02c_LamEquiv_refl C μ)) hμirr hμirr).1
  have hZIfξ₂ : f ξ₂ ∈ ZIrr G :=
    ((hf.1 ξ₂ hξ₂irr) ξ₂ (Or.inl (s02c_LamEquiv_refl C ξ₂)) ξ₂
      (Or.inl (s02c_LamEquiv_refl C ξ₂)) hξ₂irr hξ₂irr).1
  have hnormfμ1 : ClassFunction.inner (f μ) (f μ) = 1 := by
    have h := ((hf.1 μ hμirr) μ (Or.inl (s02c_LamEquiv_refl C μ)) μ
      (Or.inl (s02c_LamEquiv_refl C μ)) hμirr hμirr).2.2.1
    rw [h]; simp [hμnotfix]
  have hdcfν : DisjointCF (f ν') (f ν'') :=
    ((hf.1 ν hνirr) ν' (Or.inl hν'memS.1) ν'' (Or.inl hν''memS.1) hν'irr hν''irr).2.2.2.2.1
      hν'ν''Lam (Ne.symm hν''ne') (by rw [hν''memS.2]; exact Ne.symm hν''ne')
  have hdcfξ : DisjointCF (f ξ₂) (f μ) :=
    ((hf.1 ξ hξirr) ξ₂ (Or.inl hξ₂memS.1) μ (Or.inl hμorbit) hξ₂irr hμirr).2.2.2.2.1
      hμLam hξ₂neμ hξ₂nesμ
  have hν'ν''0 : ClassFunction.inner (f ν') (f ν'') = 0 :=
    ns4_inner_eq_zero_of_disjointCF hZIfν'' hdcfν
  have hξ₂μ0 : ClassFunction.inner (f ξ₂) (f μ) = 0 :=
    ns4_inner_eq_zero_of_disjointCF hZIfμ hdcfξ
  -- ## the two cross coefficients
  set e : ℂ := ClassFunction.inner (f ν) (f ξ) with he
  set C1 : ℂ := ClassFunction.inner (f ν') (f ξ) with hC1
  set C2 : ℂ := ClassFunction.inner (f ν'') (f ξ) with hC2
  have he1 : e = 1 ∨ e = -1 := by
    have hξp := (bset_orbit_struct C f hf χ hχ).1 ξ hξmem
    have h2 : ClassFunction.inner χ (f ξ) = 1 ∨ ClassFunction.inner χ (f ξ) = -1 := hξp.2.2
    rw [he]
    rcases hνeqpm with hh | hh
    · rw [hh]; exact h2
    · rw [hh, ClassFunction.inner_neg_left]
      rcases h2 with h2 | h2
      · exact Or.inr (by rw [h2])
      · exact Or.inl (by rw [h2]; norm_num)
  have he_star : star e = e := by rcases he1 with h | h <;> rw [h] <;> norm_num
  have he_ne : e ≠ 0 := by rcases he1 with h | h <;> rw [h] <;> norm_num
  -- ## the coherence clause (iv) relations
  have expandSub : ∀ (u₁ v₁ u₂ v₂ : ClassFunction ↥C.P.H0 ℂ),
      ClassFunction.inner (f u₁ - f v₁) (f u₂ - f v₂) =
        ClassFunction.inner (f u₁) (f u₂) - ClassFunction.inner (f u₁) (f v₂) -
          ClassFunction.inner (f v₁) (f u₂) + ClassFunction.inner (f v₁) (f v₂) := by
    intro u₁ v₁ u₂ v₂
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
    ring
  have hR1 : ClassFunction.inner (f ν') (f ξ₂) = C1 - e := by
    have h := hf.2.1 ν ν' ξ ξ₂ hνirr hν'irr hξirr hξ₂irr hν'memS.1 hξ₂memS.1
      hξnotlam hnotlamνs
    rw [expandSub ν ν' ξ ξ₂, ← he, ← hC1, hνξ₂] at h
    linear_combination h
  have hR2 : ClassFunction.inner (f ν') (f μ) = C1 - e := by
    have h := hf.2.1 ν ν' ξ μ hνirr hν'irr hξirr hμirr hν'memS.1 hμorbit
      hξnotlam hnotlamνs
    rw [expandSub ν ν' ξ μ, ← he, ← hC1, hνμ] at h
    linear_combination h
  have hR3 : ClassFunction.inner (f ν'') (f ξ₂) = C2 - e := by
    have h := hf.2.1 ν ν'' ξ ξ₂ hνirr hν''irr hξirr hξ₂irr hν''memS.1 hξ₂memS.1
      hξnotlam hnotlamνs
    rw [expandSub ν ν'' ξ ξ₂, ← he, ← hC2, hνξ₂] at h
    linear_combination h
  have hR4 : ClassFunction.inner (f ν'') (f μ) = C2 - e := by
    have h := hf.2.1 ν ν'' ξ μ hνirr hν''irr hξirr hμirr hν''memS.1 hμorbit
      hξnotlam hnotlamνs
    rw [expandSub ν ν'' ξ μ, ← he, ← hC2, hνμ] at h
    linear_combination h
  have hR5 : ClassFunction.inner (f ξ₂) (f ν') = star C1 - e := by
    have h := hf.2.1 ξ ξ₂ ν ν' hξirr hξ₂irr hνirr hν'irr hξ₂memS.1 hν'memS.1
      hnotlam' (by rw [hξs]; exact hnotlam')
    rw [expandSub ξ ξ₂ ν ν', ClassFunction.inner_star_comm (f ξ) (f ν), ← he, he_star,
      ClassFunction.inner_star_comm (f ξ) (f ν'), ← hC1, hνξ₂s] at h
    linear_combination h
  have hR6 : ClassFunction.inner (f ξ₂) (f ν'') = star C2 - e := by
    have h := hf.2.1 ξ ξ₂ ν ν'' hξirr hξ₂irr hνirr hν''irr hξ₂memS.1 hν''memS.1
      hnotlam' (by rw [hξs]; exact hnotlam')
    rw [expandSub ξ ξ₂ ν ν'', ClassFunction.inner_star_comm (f ξ) (f ν), ← he, he_star,
      ClassFunction.inner_star_comm (f ξ) (f ν''), ← hC2, hνξ₂s] at h
    linear_combination h
  -- ## the key step: `C1` and `C2` cannot both vanish
  have hkey : ¬ (C1 = 0 ∧ C2 = 0) := by
    rintro ⟨hc1, hc2⟩
    have hB1 : ClassFunction.inner (f ν') (f μ) = -e := by rw [hR2, hc1]; ring
    have hB2 : ClassFunction.inner (f ν'') (f μ) = -e := by rw [hR4, hc2]; ring
    have hB1s : ClassFunction.inner (f μ) (f ν') = -e := by
      rw [ClassFunction.inner_star_comm (f μ) (f ν'), hB1, star_neg, he_star]
    have hB2s : ClassFunction.inner (f μ) (f ν'') = -e := by
      rw [ClassFunction.inner_star_comm (f μ) (f ν''), hB2, star_neg, he_star]
    have hD1 : ClassFunction.inner (f ξ₂) (f ν') = -e := by
      rw [hR5, hc1]; simp
    have hD2 : ClassFunction.inner (f ξ₂) (f ν'') = -e := by
      rw [hR6, hc2]; simp
    set a : ClassFunction G ℂ := f ν' + e • f μ with ha
    set b : ClassFunction G ℂ := f ν'' + e • f μ with hb
    have haa : ClassFunction.inner a a = 1 := by
      simp only [ha, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right]
      rw [hnormfν'2, hB1, hB1s, hnormfμ1, he_star]
      rcases he1 with h | h <;> rw [h] <;> norm_num
    have hbb : ClassFunction.inner b b = 1 := by
      simp only [hb, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right]
      rw [hnormfν''2, hB2, hB2s, hnormfμ1, he_star]
      rcases he1 with h | h <;> rw [h] <;> norm_num
    have hab : ClassFunction.inner a b = -1 := by
      simp only [ha, hb, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right]
      rw [hν'ν''0, hB1, hB2s, hnormfμ1, he_star]
      rcases he1 with h | h <;> rw [h] <;> norm_num
    have hba : ClassFunction.inner b a = -1 := by
      rw [ClassFunction.inner_star_comm b a, hab, star_neg, star_one]
    have hsum0 : ClassFunction.inner (a + b) (a + b) = 0 := by
      simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
      rw [haa, hab, hba, hbb]
      norm_num
    have hab0 : a + b = 0 := eq_zero_of_inner_self_re_eq_zero (by rw [hsum0]; rfl)
    have hlin : f ν' + f ν'' = -(2 * e) • f μ := by
      have h := hab0
      rw [ha, hb] at h
      have h5 : (f ν' + f ν'') + (2 * e) • f μ = 0 := by
        rw [← h, two_mul, add_smul]
        abel
      rw [add_eq_zero_iff_eq_neg, ← neg_smul] at h5
      exact h5
    have hzero : ClassFunction.inner (f ξ₂) (f ν') + ClassFunction.inner (f ξ₂) (f ν'') = 0 := by
      rw [← ClassFunction.inner_add_right, hlin, ClassFunction.inner_smul_right, hξ₂μ0,
        mul_zero]
    have htwo : ClassFunction.inner (f ξ₂) (f ν') + ClassFunction.inner (f ξ₂) (f ν'') =
        -2 * e := by
      rw [hD1, hD2]; ring
    rw [hzero] at htwo
    have he0 : e = 0 := by linear_combination (1/2 : ℂ) * htwo
    exact he_ne he0
  -- ## conclusion: the complementary signed irreducible sees `ξ` and one of `ν'`, `ν''`
  set eξ : ℂ := ClassFunction.inner χ (f ξ) with heξ
  have heξ1 : eξ = 1 ∨ eξ = -1 := (bset_orbit_struct C f hf χ hχ).1 ξ hξmem |>.2.2
  set ζ : ClassFunction G ℂ := f ξ - eξ • χ with hζ
  have hζZI : ζ ∈ ZIrr G := by
    rw [hζ]
    rcases heξ1 with h | h
    · rw [h, one_smul]
      exact Submodule.sub_mem _ hZIfξ (mem_ZIrr_of_isPmIrr hχ)
    · rw [h, neg_one_smul, sub_neg_eq_add]
      exact Submodule.add_mem _ hZIfξ (mem_ZIrr_of_isPmIrr hχ)
  have hζnorm : ClassFunction.inner ζ ζ = 1 := by
    rw [hζ, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_right, ClassFunction.inner_smul_right,
      ClassFunction.inner_smul_left, hnormfξ2, ns4_inner_self_pmIrr hχ,
      ClassFunction.inner_star_comm (f ξ) χ, ← heξ]
    rcases heξ1 with h | h <;> rw [h] <;> norm_num
  have hζpm : IsPmIrr ζ := isPmIrr_of_mem_ZIrr_inner_self_eq_one hζZI hζnorm
  have hξbsetζ : ξ ∈ bset C f ζ := by
    refine ⟨hξirr, ?_⟩
    rw [hζ, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, ← heξ,
      hnormfξ2]
    rcases heξ1 with h | h <;> rw [h] <;> norm_num
  have hξneν' : ξ ≠ ν' := fun h => hξnotlam (h ▸ hν'memS.1)
  have hξneν'' : ξ ≠ ν'' := fun h => hξnotlam (h ▸ hν''memS.1)
  by_cases hC1z : C1 = 0
  · by_cases hC2z : C2 = 0
    · exact absurd ⟨hC1z, hC2z⟩ hkey
    · have hν''bsetζ : ν'' ∈ bset C f ζ := by
        refine ⟨hν''irr, ?_⟩
        rw [hζ, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hχfν'']
        simp only [mul_zero, sub_zero]
        rw [ClassFunction.inner_star_comm (f ξ) (f ν''), ← hC2]
        intro hcontra
        exact hC2z (by have := congrArg star hcontra; simpa using this)
      exact twoSfixedMaximalClean D C hDC hS3 (by omega) f hf ζ hζpm ξ hξbsetζ ν'' hν''bsetζ
        hξneν'' hξs hν''memS.2 (by rw [hξ4, hn4]) (by rw [hν''orbit_eq, h4ν, hn4])
  · have hν'bsetζ : ν' ∈ bset C f ζ := by
      refine ⟨hν'irr, ?_⟩
      rw [hζ, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hχfν']
      simp only [mul_zero, sub_zero]
      rw [ClassFunction.inner_star_comm (f ξ) (f ν'), ← hC1]
      intro hcontra
      exact hC1z (by have := congrArg star hcontra; simpa using this)
    exact twoSfixedMaximalClean D C hDC hS3 (by omega) f hf ζ hζpm ξ hξbsetζ ν' hν'bsetζ
      hξneν' hξs hν'memS.2 (by rw [hξ4, hn4]) (by rw [hν'orbit_eq, h4ν, hn4])

end Work.BG
