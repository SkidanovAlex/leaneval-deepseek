import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.c3deNeChain
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_gram
import Submission.Work.BG.exists_lamCF_t_neg_one_sconj_ne
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.c3OrbitCard
import Submission.Work.BG.Core24
import Submission.Work.GLUE.Defs
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.c3LamOrbitKappa
import Submission.Work.BG.s02_indDiff

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-! ## Auxiliary lemmas -/

/-- Cancellation of the `Λ`-action on a class function `κ` that is `1` on `S₀`:
`λ_γ κ = λ_{γ'} κ` forces `γ = γ'`. -/
private theorem lamCF_mul_cancel {G : Type} [Group G] [Finite G] (D : BGData G)
    (C : Sec2Ctx G) (hcompat : Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    {γ γ' : quotGroup C.P →* ℂˣ} (h : lamCF C γ * κ = lamCF C γ' * κ) : γ = γ' := by
  have hval' : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → γ (quotMk C.P s) = γ' (quotMk C.P s) := by
    intro s hs
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ s) h
    simp only [ClassFunction.mul_apply] at h'
    rw [hκS0 s hs] at h'
    rw [lamCF_apply, lamCF_apply] at h'
    exact Units.ext (by simpa using h')
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
  obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hcompat x
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
  calc γ (quotMk C.P x) = γ (quotMk C.P s) := by rw [hπ]
    _ = γ' (quotMk C.P s) := hval' s hs
    _ = γ' (quotMk C.P x) := by rw [hπ]

/-- On a single `Λ`-orbit the coherent lifts have a common degree: `f μ 1 = f ν 1` for
`LamEquiv C μ ν`, because `f μ - f ν = (μ - ν)^{H₀→G}` and `(μ - ν)^{H₀→G}` has degree `0`. -/
private theorem orbit_degree_eq {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (μ ν : ClassFunction ↥C.P.H0 ℂ) (hμ : IsIrreducibleCharacter μ)
    (hν : IsIrreducibleCharacter ν) (hlam : LamEquiv C μ ν) : f μ 1 = f ν 1 := by
  classical
  have hν' : ν ∈ orbitKey C μ := Or.inl hlam
  have hμ' : μ ∈ orbitKey C μ := Or.inl (s02c_LamEquiv_refl C μ)
  have hG := (hf.1 μ hμ) ν hν' μ hμ' hν hμ
  have hlam' : LamEquiv C ν μ := s02c_LamEquiv_symm C hlam
  have hind : ind C (ν - μ) = f ν - f μ := hG.2.2.2.1 hlam'
  have hdeg : ind C (ν - μ) 1 = 0 := (s02_indDiff C ν μ hν hμ hlam').2
  have hsub : (f ν - f μ) 1 = 0 := by rw [← hind]; exact hdeg
  rw [ClassFunction.sub_apply] at hsub
  exact (sub_eq_zero.mp hsub).symm

/-- From a set of three pairwise distinct elements and a member `k`, extract two further
distinct members. -/
private theorem exists_two_extra {α : Type} {s : Set α} {k a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : s = {a, b, c}) (hk : k ∈ s) :
    ∃ x y : α, x ∈ s ∧ y ∈ s ∧ x ≠ k ∧ y ≠ k ∧ x ≠ y := by
  rw [hs] at hk ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with h | h | h
  · exact ⟨b, c, by simp, by simp, by rw [h]; exact hab.symm, by rw [h]; exact hac.symm, hbc⟩
  · exact ⟨a, c, by simp, by simp, by rw [h]; exact hab, by rw [h]; exact hbc.symm, hac⟩
  · exact ⟨a, b, by simp, by simp, by rw [h]; exact hac, by rw [h]; exact hbc, hab⟩

/-- **The other `s`-fixed member of a `Λ`-orbit.**  If `ν ∈ 𝒮(χ)` is `s`-fixed then (Lemma 2.1)
its orbit contains exactly two `s`-fixed characters; the second one, `μ`, is irreducible,
`Λ`-equivalent to `ν`, distinct from it, and does not lie in `𝒮(χ)`. -/
private theorem exists_other_sfixed {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hνS : ν ∈ bset C f χ) (hfix : sconj C ν = ν) :
    ∃ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ ∧ LamEquiv C ν μ ∧
      sconj C μ = μ ∧ μ ≠ ν ∧ μ ∉ bset C f χ := by
  classical
  have hνirr : IsIrreducibleCharacter ν := hνS.1
  have hstab : sconj C '' lamOrbit C ν = lamOrbit C ν := by
    rw [s02c_sconj_image_lamOrbit C (sconjLam C) ν, hfix]
  have h2 : ({χ' ∈ lamOrbit C ν | sconj C χ' = χ'} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 :=
    ((s02_lemma21 C) ν hνirr).2 hstab
  obtain ⟨μ, hμT, hμν⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := {χ' ∈ lamOrbit C ν | sconj C χ' = χ'})
      (by rw [h2]; norm_num) ν
  rw [Set.mem_setOf_eq] at hμT
  have hμorbit : μ ∈ lamOrbit C ν := hμT.1
  have hμfix : sconj C μ = μ := hμT.2
  have hμirr : IsIrreducibleCharacter μ := irreducible_of_mem_lamOrbit C hμorbit hνirr
  have hμnotmem : μ ∉ bset C f χ := by
    intro hμS
    have h := (bset_orbit_struct C f hf χ hχ).2 ν hνS μ hμS hμorbit hμν
    rw [hfix] at h
    exact hμν h
  exact ⟨μ, hμirr, hμorbit, hμfix, hμν, hμnotmem⟩

/-- **The degree step of BG p. 211**, given two distinct `s`-fixed members `ν₁ ≠ ν₂` of
`𝒮(χ₁) \ {κ}` (with `|Λνᵢ| ≠ |Λκ|`): the two `δᵢ = ν̃ᵢ - μ̃ᵢ` (`μᵢ` the other `s`-fixed member
of `Λνᵢ`) satisfy the hypotheses of `C24.degEq_of_coeffs`, whence `χ₁(1) = χ₂(1)`. -/
private theorem degEq_of_two_bset {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Compat D C) (hHyps : ThmCHyps D K1 K2) (hn4 : 4 ≤ D.n)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : IsKappa D C κ)
    (χ₁ χ₂ : ClassFunction G ℂ) (hχ₁ : IsPmIrr χ₁) (hχ₂ : IsPmIrr χ₂)
    (horth : ClassFunction.inner χ₁ χ₂ = 0) (hfκ : f κ = χ₁ + χ₂)
    (ν₁ ν₂ : ClassFunction ↥C.P.H0 ℂ)
    (hν₁S : ν₁ ∈ bset C f χ₁) (hν₂S : ν₂ ∈ bset C f χ₁)
    (hν₁κ : ν₁ ≠ κ) (hν₂κ : ν₂ ≠ κ) (hν₁ν₂ : ν₁ ≠ ν₂)
    (hfix₁ : sconj C ν₁ = ν₁) (hfix₂ : sconj C ν₂ = ν₂)
    (horb₁ : (lamOrbit C ν₁).ncard ≠ D.n) (horb₂ : (lamOrbit C ν₂).ncard ≠ D.n) :
    χ₁ 1 = χ₂ 1 := by
  classical
  -- ## standing hypotheses
  have hS3 : Sec3Hyp D := (thmCSec3 G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1).1
  have hL34 : Lemma34Prop D C := c3deLemma34 D C
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, hκne1⟩ := hκ
  -- ## the companion character `κ₃ = λ_β κ`, not `s`-fixed, with `|Λκ₃| = D.n`
  obtain ⟨β, hβt, hβsconj⟩ := exists_lamCF_t_neg_one_sconj_ne D C hComp hn4
  have hκ₃irr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hκκ₃ : LamEquiv C κ (lamCF C β * κ) := ⟨β, rfl⟩
  have hκ₃sconj : sconj C (lamCF C β * κ) ≠ lamCF C β * κ := by
    intro hfix
    have hA : sconj C (lamCF C β * κ) = lamCF C β⁻¹ * κ := by
      rw [sconjLam C β κ, hκsconj]
    have h1 : lamCF C β⁻¹ * κ = lamCF C β * κ := by rw [← hA]; exact hfix
    have h2 : β⁻¹ = β := lamCF_mul_cancel D C hComp κ hκS0 h1
    have h3 : lamCF C β⁻¹ = lamCF C β := by rw [h2]
    exact hβsconj (by rw [LamCFFixed.sconj_lamCF C β]; exact h3)
  have horbκ : (lamOrbit C κ).ncard = D.n := c3LamOrbitKappa D C hComp κ hκS0
  have horbκ₃ : (lamOrbit C (lamCF C β * κ)).ncard = D.n := by
    rw [← Work.GW2.C24.lamOrbit_eq_of_LamEquiv C hκκ₃]; exact horbκ
  -- ## the two companion members `μᵢ` of `Λνᵢ`
  have hν₁irr : IsIrreducibleCharacter ν₁ := hν₁S.1
  have hν₂irr : IsIrreducibleCharacter ν₂ := hν₂S.1
  obtain ⟨μ₁, hμ₁irr, hν₁μ₁, hμ₁fix, hμ₁ne, hμ₁notmem⟩ :=
    exists_other_sfixed C f hf χ₁ hχ₁ ν₁ hν₁S hfix₁
  obtain ⟨μ₂, hμ₂irr, hν₂μ₂, hμ₂fix, hμ₂ne, hμ₂notmem⟩ :=
    exists_other_sfixed C f hf χ₁ hχ₁ ν₂ hν₂S hfix₂
  have hν₁κLam : ¬ LamEquiv C ν₁ κ :=
    Work.GW2.C24.not_LamEquiv_of_ncard_ne C (by rw [horbκ]; exact horb₁)
  have hneLam : ¬ LamEquiv C ν₁ ν₂ := by
    intro hLam
    have h := (bset_orbit_struct C f hf χ₁ hχ₁).2 ν₁ hν₁S ν₂ hν₂S hLam (Ne.symm hν₁ν₂)
    rw [hfix₁] at h
    exact hν₁ν₂ h.symm
  -- ## `ind` expressions for the differences
  have hG₁ := (hf.1 ν₁ hν₁irr) ν₁ (Or.inl (s02c_LamEquiv_refl C ν₁)) μ₁
    (Or.inl hν₁μ₁) hν₁irr hμ₁irr
  have hind₁ : ind C (ν₁ - μ₁) = f ν₁ - f μ₁ := hG₁.2.2.2.1 hν₁μ₁
  have hG₂ := (hf.1 ν₂ hν₂irr) ν₂ (Or.inl (s02c_LamEquiv_refl C ν₂)) μ₂
    (Or.inl hν₂μ₂) hν₂irr hμ₂irr
  have hind₂ : ind C (ν₂ - μ₂) = f ν₂ - f μ₂ := hG₂.2.2.2.1 hν₂μ₂
  -- ## norm four, via the Brauer–Suzuki Gram matrix
  have hnorm₁ : ClassFunction.inner (f ν₁ - f μ₁) (f ν₁ - f μ₁) = 4 := by
    have hgram := (s02_gram C) ν₁ μ₁ ν₁ μ₁ hν₁irr hμ₁irr hν₁irr hμ₁irr hν₁μ₁ hν₁μ₁
    rw [hind₁] at hgram
    have hc11 : cH C ν₁ ν₁ = 2 := by
      have hc : cH C ν₁ ν₁ =
          (if ν₁ = ν₁ then 1 else 0) + (if ν₁ = sconj C ν₁ then 1 else 0) := rfl
      rw [hc, if_pos rfl, if_pos hfix₁.symm]; norm_num
    have hc1μ : cH C ν₁ μ₁ = 0 := by
      have hc : cH C ν₁ μ₁ =
          (if μ₁ = ν₁ then 1 else 0) + (if μ₁ = sconj C ν₁ then 1 else 0) := rfl
      rw [hc, if_neg hμ₁ne, if_neg (fun hh => hμ₁ne (hh.trans hfix₁))]; norm_num
    have hcμ1 : cH C μ₁ ν₁ = 0 := by
      have hc : cH C μ₁ ν₁ =
          (if ν₁ = μ₁ then 1 else 0) + (if ν₁ = sconj C μ₁ then 1 else 0) := rfl
      rw [hc, if_neg (Ne.symm hμ₁ne), if_neg (fun hh => hμ₁ne (hh.trans hμ₁fix).symm)]
      norm_num
    have hcμμ : cH C μ₁ μ₁ = 2 := by
      have hc : cH C μ₁ μ₁ =
          (if μ₁ = μ₁ then 1 else 0) + (if μ₁ = sconj C μ₁ then 1 else 0) := rfl
      rw [hc, if_pos rfl, if_pos hμ₁fix.symm]; norm_num
    have hval : cH C ν₁ ν₁ - cH C ν₁ μ₁ - cH C μ₁ ν₁ + cH C μ₁ μ₁ = (4 : ℂ) := by
      rw [hc11, hc1μ, hcμ1, hcμμ]; norm_num
    rw [hval] at hgram
    exact hgram
  have hnorm₂ : ClassFunction.inner (f ν₂ - f μ₂) (f ν₂ - f μ₂) = 4 := by
    have hgram := (s02_gram C) ν₂ μ₂ ν₂ μ₂ hν₂irr hμ₂irr hν₂irr hμ₂irr hν₂μ₂ hν₂μ₂
    rw [hind₂] at hgram
    have hc11 : cH C ν₂ ν₂ = 2 := by
      have hc : cH C ν₂ ν₂ =
          (if ν₂ = ν₂ then 1 else 0) + (if ν₂ = sconj C ν₂ then 1 else 0) := rfl
      rw [hc, if_pos rfl, if_pos hfix₂.symm]; norm_num
    have hc1μ : cH C ν₂ μ₂ = 0 := by
      have hc : cH C ν₂ μ₂ =
          (if μ₂ = ν₂ then 1 else 0) + (if μ₂ = sconj C ν₂ then 1 else 0) := rfl
      rw [hc, if_neg hμ₂ne, if_neg (fun hh => hμ₂ne (hh.trans hfix₂))]; norm_num
    have hcμ1 : cH C μ₂ ν₂ = 0 := by
      have hc : cH C μ₂ ν₂ =
          (if ν₂ = μ₂ then 1 else 0) + (if ν₂ = sconj C μ₂ then 1 else 0) := rfl
      rw [hc, if_neg (Ne.symm hμ₂ne), if_neg (fun hh => hμ₂ne (hh.trans hμ₂fix).symm)]
      norm_num
    have hcμμ : cH C μ₂ μ₂ = 2 := by
      have hc : cH C μ₂ μ₂ =
          (if μ₂ = μ₂ then 1 else 0) + (if μ₂ = sconj C μ₂ then 1 else 0) := rfl
      rw [hc, if_pos rfl, if_pos hμ₂fix.symm]; norm_num
    have hval : cH C ν₂ ν₂ - cH C ν₂ μ₂ - cH C μ₂ ν₂ + cH C μ₂ μ₂ = (4 : ℂ) := by
      rw [hc11, hc1μ, hcμ1, hcμμ]; norm_num
    rw [hval] at hgram
    exact hgram
  -- ## orthogonality of `δ₁` and `δ₂` (coherence clause (iv))
  have hdd : ClassFunction.inner (f ν₁ - f μ₁) (f ν₂ - f μ₂) = 0 :=
    hf.2.1 ν₁ μ₁ ν₂ μ₂ hν₁irr hμ₁irr hν₂irr hμ₂irr hν₁μ₁ hν₂μ₂ hneLam
      (by rw [hfix₁]; exact hneLam)
  -- ## `⟨δᵢ, χ₁⟩ = ±1`
  have hχfν₁ : ClassFunction.inner χ₁ (f ν₁) = 1 ∨ ClassFunction.inner χ₁ (f ν₁) = -1 :=
    ((bset_orbit_struct C f hf χ₁ hχ₁).1 ν₁ hν₁S).2.2
  have hχfν₂ : ClassFunction.inner χ₁ (f ν₂) = 1 ∨ ClassFunction.inner χ₁ (f ν₂) = -1 :=
    ((bset_orbit_struct C f hf χ₁ hχ₁).1 ν₂ hν₂S).2.2
  have hχfμ₁ : ClassFunction.inner χ₁ (f μ₁) = 0 := by
    by_contra hne
    exact hμ₁notmem ⟨hμ₁irr, hne⟩
  have hχfμ₂ : ClassFunction.inner χ₁ (f μ₂) = 0 := by
    by_contra hne
    exact hμ₂notmem ⟨hμ₂irr, hne⟩
  have hd1χ : ClassFunction.inner (f ν₁ - f μ₁) χ₁ = 1 ∨
      ClassFunction.inner (f ν₁ - f μ₁) χ₁ = -1 := by
    rw [ClassFunction.inner_sub_left]
    have h2 : ClassFunction.inner (f μ₁) χ₁ = 0 := by
      rw [ClassFunction.inner_star_comm, hχfμ₁]; simp
    rw [h2, sub_zero]
    rcases hχfν₁ with h | h
    · left; rw [ClassFunction.inner_star_comm, h]; simp
    · right; rw [ClassFunction.inner_star_comm, h]; simp
  have hd2χ : ClassFunction.inner (f ν₂ - f μ₂) χ₁ = 1 ∨
      ClassFunction.inner (f ν₂ - f μ₂) χ₁ = -1 := by
    rw [ClassFunction.inner_sub_left]
    have h2 : ClassFunction.inner (f μ₂) χ₁ = 0 := by
      rw [ClassFunction.inner_star_comm, hχfμ₂]; simp
    rw [h2, sub_zero]
    rcases hχfν₂ with h | h
    · left; rw [ClassFunction.inner_star_comm, h]; simp
    · right; rw [ClassFunction.inner_star_comm, h]; simp
  -- ## `⟨δᵢ, χ₁ + χ₂⟩ = 0`, the coefficient identity (BG p. 211)
  have hk₁ : ClassFunction.inner (f ν₁ - f μ₁) (χ₁ + χ₂) = 0 := by
    have h := Work.GW2.C24.coeff_kappa_zero D C hL34 hComp hS3 f hf κ (lamCF C β * κ) ν₁ μ₁
      hκirr hκ₃irr hν₁irr hμ₁irr hκκ₃ hκ₃sconj horbκ₃ hν₁μ₁ hfix₁ hμ₁fix hν₁κLam
    rwa [hfκ] at h
  have hk₂ : ClassFunction.inner (f ν₂ - f μ₂) (χ₁ + χ₂) = 0 := by
    have hν₂κLam : ¬ LamEquiv C ν₂ κ :=
      Work.GW2.C24.not_LamEquiv_of_ncard_ne C (by rw [horbκ]; exact horb₂)
    have h := Work.GW2.C24.coeff_kappa_zero D C hL34 hComp hS3 f hf κ (lamCF C β * κ) ν₂ μ₂
      hκirr hκ₃irr hν₂irr hμ₂irr hκκ₃ hκ₃sconj horbκ₃ hν₂μ₂ hfix₂ hμ₂fix hν₂κLam
    rwa [hfκ] at h
  -- ## the degrees of the `δᵢ` vanish
  have hdeg₁ : (f ν₁ - f μ₁) 1 = 0 := by
    rw [ClassFunction.sub_apply, orbit_degree_eq C f hf ν₁ μ₁ hν₁irr hμ₁irr hν₁μ₁, sub_self]
  have hdeg₂ : (f ν₂ - f μ₂) 1 = 0 := by
    rw [ClassFunction.sub_apply, orbit_degree_eq C f hf ν₂ μ₂ hν₂irr hμ₂irr hν₂μ₂, sub_self]
  -- ## the pure degree step
  exact Work.GW2.C24.degEq_of_coeffs χ₁ χ₂ (f ν₁ - f μ₁) (f ν₂ - f μ₂)
    (IsPmIrr.inner_self hχ₁) (IsPmIrr.inner_self hχ₂) horth
    hnorm₁ hnorm₂ hdd hd1χ hd2χ hk₁ hk₂ hdeg₁ hdeg₂

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- The degree step of BG p. 211 (see `NOTES_LEAD_gw_design24.md` Item 1 and
`Work.GW2.C24.coeff_kappa_zero` / `Work.GW2.C24.degEq_of_coeffs`). -/
theorem c3DegEq2 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2)
    (hSimp : IsSimpleGroup G) (hn4 : 4 ≤ D.n)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (κ : ClassFunction ↥C.P.H0 ℂ) (hκ : Work.GW2.C16.IsKappa D C κ)
    (χ₁ χ₂ : ClassFunction G ℂ) (hχ₁ : Work.BG.IsPmIrr χ₁) (hχ₂ : Work.BG.IsPmIrr χ₂)
    (horth : ClassFunction.inner χ₁ χ₂ = 0) (hfκ : f κ = χ₁ + χ₂)
    (h3 : (Work.GW2.C16.bset C f χ₁).ncard = 3)
    (hfix : ∀ ν ∈ Work.GW2.C16.bset C f χ₁, ν ≠ κ → Work.BG.sconj C ν = ν)
    (horb : ∀ ν ∈ Work.GW2.C16.bset C f χ₁, ν ≠ κ → (Work.BG.lamOrbit C ν).ncard ≠ D.n) :
    χ₁ 1 = χ₂ 1 := by
  classical
  -- ## `κ ∈ 𝒮(χ₁)`
  have hinnerκ : ClassFunction.inner χ₁ (f κ) = 1 := by
    rw [hfκ, ClassFunction.inner_add_right, IsPmIrr.inner_self hχ₁, horth, add_zero]
  have hκmem : κ ∈ bset C f χ₁ := ⟨hκ.1, by rw [hinnerκ]; exact one_ne_zero⟩
  -- ## extract two further members of `𝒮(χ₁)`
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Set.ncard_eq_three.mp h3
  obtain ⟨ν₁, ν₂, hν₁mem, hν₂mem, hν₁κ, hν₂κ, hν₁ν₂⟩ :=
    exists_two_extra (s := bset C f χ₁) (k := κ) hab hac hbc hs hκmem
  have hν₁S : ν₁ ∈ bset C f χ₁ := hs.symm ▸ hν₁mem
  have hν₂S : ν₂ ∈ bset C f χ₁ := hs.symm ▸ hν₂mem
  exact degEq_of_two_bset D C K1 K2 hComp hHyps hn4 f hf κ hκ χ₁ χ₂ hχ₁ hχ₂ horth hfκ
    ν₁ ν₂ hν₁S hν₂S hν₁κ hν₂κ hν₁ν₂ (hfix ν₁ hν₁S hν₁κ) (hfix ν₂ hν₂S hν₂κ)
    (horb ν₁ hν₁S hν₁κ) (horb ν₂ hν₂S hν₂κ)

end Work.BG
