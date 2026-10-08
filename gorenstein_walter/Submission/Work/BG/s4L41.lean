import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.L41Aux
import Submission.Work.BG.l41Vi
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma16_mod_two
import Submission.Work.BG.s02_lemma17T
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.s02_assemblyFull
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_twoCase
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_bsValueT
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.nCases
import Submission.Work.BG.L33DDefs
import Submission.Work.BG.lemma33Arith
import Submission.Work.BG.glaubCorrDistinct
import Submission.Work.BG.rem31ShapeLeaf
import Submission.OddOrder.GroupTheory.RepresentationTheory.ExtensionLinearTwist

set_option linter.unusedSectionVars false

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 1. Generic helpers -/

/-- The inner product is conjugate-symmetric up to `star`. -/
private theorem s4L41_inner_ne_zero_comm {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {a b : ClassFunction K ℂ}
    (h : ClassFunction.inner a b ≠ 0) : ClassFunction.inner b a ≠ 0 := by
  intro h0
  exact h (by rw [ClassFunction.inner_star_comm, h0, star_zero])

/-- A signed irreducible character that is not orthogonal to both `a` and `b` prevents `a`
and `b` from being disjoint. -/
private theorem s4L41_not_disjointCF {a b χ : ClassFunction G ℂ} (hχ : IsPmIrr χ)
    (ha : ClassFunction.inner χ a ≠ 0) (hb : ClassFunction.inner χ b ≠ 0) :
    ¬ DisjointCF a b := by
  have ha' := s4L41_inner_ne_zero_comm ha
  have hb' := s4L41_inner_ne_zero_comm hb
  intro hd
  rcases hχ with hχ | hχ
  · rcases hd (⟨χ, hχ⟩ : IrreducibleCharacter G) with h | h
    · exact ha' h
    · exact hb' h
  · rcases hd (⟨-χ, hχ⟩ : IrreducibleCharacter G) with h | h
    · rw [ClassFunction.inner_neg_right] at h
      exact ha' (neg_eq_zero.mp h)
    · rw [ClassFunction.inner_neg_right] at h
      exact hb' (neg_eq_zero.mp h)

/-- A virtual character of norm one is a signed irreducible character. -/
private theorem s4L41_pmIrr_of_norm_one {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (hn : ClassFunction.inner φ φ = 1) : IsPmIrr φ :=
  isPmIrr_of_mem_ZIrr_inner_self_eq_one hφ hn

/-! ## 2. The per-key coherence in the case `|S| = 4` -/

section GoodOn

variable (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable {β₂ : quotGroup C.P →* ℂˣ}

/-- The key `Λν ∪ (Λν)^s` of an `s`-fixed irreducible `ν`, when `Λ = {1, λ₂}`. -/
theorem s4L41_orbitKey_sfixed (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hfix : sconj C ν = ν) :
    ∀ ξ : ClassFunction ↥C.P.H0 ℂ, ξ ∈ orbitKey C ν ↔ ξ = ν ∨ ξ = lamCF C β₂ * ν := by
  intro ξ
  have hset : orbitKey C ν = {η : ClassFunction ↥C.P.H0 ℂ | η = ν ∨ η = lamCF C β₂ * ν} := by
    rw [orbitKey_eq C h2 hβ ν, hfix]
    ext η
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    tauto
  rw [hset]
  exact Iff.of_eq Set.mem_ofPred_eq

/-- The key `Λν ∪ (Λν)^s` when `Λ = {1, λ₂}`. -/
theorem s4L41_orbitKey_ne (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    ∀ ξ : ClassFunction ↥C.P.H0 ℂ,
      ξ ∈ orbitKey C ν ↔
        ξ = ν ∨ ξ = lamCF C β₂ * ν ∨ ξ = sconj C ν ∨ ξ = sconj C (lamCF C β₂ * ν) := by
  intro ξ
  have hset : orbitKey C ν =
      {η : ClassFunction ↥C.P.H0 ℂ | η = ν ∨ η = lamCF C β₂ * ν} ∪
      {η : ClassFunction ↥C.P.H0 ℂ | η = sconj C ν ∨ η = sconj C (lamCF C β₂ * ν)} := by
    rw [orbitKey_eq C h2 hβ ν, sconj_lam_two_mul C h2 hβ]
  rw [hset]
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-- `ind C (λ₂ν - ν) = - ind C (ν - λ₂ν)`. -/
theorem s4L41_ind_swap (ν : ClassFunction ↥C.P.H0 ℂ) :
    ind C (lamCF C β₂ * ν - ν) = -(ind C (ν - lamCF C β₂ * ν)) := by
  have hsum : ind C (lamCF C β₂ * ν - ν) + ind C (ν - lamCF C β₂ * ν) = 0 := by
    rw [← ClassFunction.induce_add]
    have h0 : (lamCF C β₂ * ν - ν : ClassFunction ↥C.P.H0 ℂ) +
        (ν - lamCF C β₂ * ν) = 0 := by
      ext h
      simp only [ClassFunction.add_apply, ClassFunction.sub_apply, ClassFunction.zero_apply]
      ring
    rw [h0, ClassFunction.induce_zero]
  exact eq_neg_of_add_eq_zero_left hsum

/-- The `GoodOn` witness in the `s`-fixed case. -/
theorem s4L41_goodOn_of_sfixed (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) (hfix : sconj C ν = ν) :
    ∃ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, GoodOn C (orbitKey C ν) f := by
  classical
  have hν₂ : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hν
  have hne₂ : lamCF C β₂ * ν ≠ ν := lam_two_mul_ne_self C h2 hβ hν
  have hfix₂ : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν :=
    (sconj_lam_two_mul_eq_iff C h2 hβ ν).mpr hfix
  obtain ⟨g₁, g₂, hg₁Z, hg₂Z, hg₁n, hg₂n, hdec, hdisj⟩ :=
    s02_twoCase (Work.GW2.C16.delta C β₂ ν) 2 (Or.inr rfl)
      (l41_delta_mem_ZIrr C hν) (l41_delta_apply_one C hν)
      (by rw [l41_delta_inner_self C h2 hβ hν, if_pos hfix]; norm_num)
  let f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ :=
    fun ξ => if ξ = ν then g₁ else g₂
  have hfν : f ν = g₁ := by simp only [f]; exact if_pos trivial
  have hfν₂ : f (lamCF C β₂ * ν) = g₂ := by
    simp only [f]; rw [if_neg hne₂]
  have hdelta : Work.GW2.C16.delta C β₂ ν = ind C (ν - lamCF C β₂ * ν) := rfl
  have hswap : ind C (lamCF C β₂ * ν - ν) = g₂ - g₁ := by
    rw [s4L41_ind_swap C (β₂ := β₂) ν]
    change -(Work.GW2.C16.delta C β₂ ν) = g₂ - g₁
    rw [hdec, neg_sub]
  refine ⟨f, ?_⟩
  intro μ hμE ν' hν'E hμirr hν'irr
  rw [s4L41_orbitKey_sfixed C h2 hβ hfix] at hμE hν'E
  rcases hμE with hμ | hμ <;> rcases hν'E with hν' | hν' <;> subst hν' <;> subst hμ
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfν]; exact hg₁Z
    · rw [hfix]
    · rw [hfν, if_pos hfix]; exact hg₁n
    · intro _
      rw [hfν]
      simp [ind]
    · intro _ hne _
      exact absurd rfl hne
    · intro h _
      exact absurd hfix h
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfν₂]; exact hg₂Z
    · rw [hfix₂]
    · rw [hfν₂, if_pos hfix₂]; exact hg₂n
    · intro _
      rw [hfν, hfν₂, ← hdelta]
      exact hdec
    · intro _ _ _
      rw [hfν, hfν₂]; exact hdisj
    · intro h _
      exact absurd hfix₂ h
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfν]; exact hg₁Z
    · rw [hfix]
    · rw [hfν, if_pos hfix]; exact hg₁n
    · intro _
      rw [hswap, hfν, hfν₂]
    · intro _ _ _
      rw [hfν, hfν₂]
      exact fun χ => (hdisj χ).symm
    · intro h _
      exact absurd hfix h
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfν₂]; exact hg₂Z
    · rw [hfix₂]
    · rw [hfν₂, if_pos hfix₂]; exact hg₂n
    · intro _
      rw [hfν₂]
      simp [ind]
    · intro _ hne _
      exact absurd rfl hne
    · intro h _
      exact absurd hfix₂ h

/-- The `GoodOn` witness in the non-`s`-fixed case. -/
theorem s4L41_goodOn_of_ne (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) (hfix : sconj C ν ≠ ν) :
    ∃ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, GoodOn C (orbitKey C ν) f := by
  classical
  have hν₂ : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hν
  have hνs : IsIrreducibleCharacter (sconj C ν) := IsIrreducibleCharacter.conjByH C.P C.s hν
  have hν₂s : IsIrreducibleCharacter (sconj C (lamCF C β₂ * ν)) :=
    IsIrreducibleCharacter.conjByH C.P C.s hν₂
  have hne₂ : lamCF C β₂ * ν ≠ ν := lam_two_mul_ne_self C h2 hβ hν
  have hne_s : sconj C ν ≠ lamCF C β₂ * ν := sconj_ne_lam_two_mul C h2 hβ hν
  have hfix₂ : sconj C (lamCF C β₂ * ν) ≠ lamCF C β₂ * ν :=
    fun h => hfix ((sconj_lam_two_mul_eq_iff C h2 hβ ν).mp h)
  have hfix_s : sconj C (sconj C ν) ≠ sconj C ν := by
    intro h
    exact hfix (by rw [← h, sconj_sconj C ν])
  have hfix₂s : sconj C (sconj C (lamCF C β₂ * ν)) ≠ sconj C (lamCF C β₂ * ν) := by
    intro h
    exact hfix₂ (by rw [← h, sconj_sconj C (lamCF C β₂ * ν)])
  have hne₂s_ν : sconj C (lamCF C β₂ * ν) ≠ ν := by
    intro h
    have h' : lamCF C β₂ * ν = sconj C ν := by
      have hc := congrArg (sconj C) h
      have hss : sconj C (sconj C (lamCF C β₂ * ν)) = lamCF C β₂ * ν :=
        sconj_sconj C _
      rw [hss] at hc
      exact hc
    exact hne_s h'.symm
  have hne₂s_s : sconj C (lamCF C β₂ * ν) ≠ sconj C ν := by
    intro h
    have hc := congrArg (sconj C) h
    have hss₁ : sconj C (sconj C (lamCF C β₂ * ν)) = lamCF C β₂ * ν := sconj_sconj C _
    have hss₂ : sconj C (sconj C ν) = ν := sconj_sconj C _
    rw [hss₁, hss₂] at hc
    exact hne₂ hc
  have hlam2 : lamCF C β₂ * (lamCF C β₂ * ν) = ν := by
    rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
  have hlam2s : lamCF C β₂ * sconj C (lamCF C β₂ * ν) = sconj C ν := by
    rw [← sconj_lam_two_mul C h2 hβ (lamCF C β₂ * ν), hlam2]
  obtain ⟨g₁, g₂, hg₁Z, hg₂Z, hg₁n, hg₂n, hdec, hdisj⟩ :=
    s02_twoCase (Work.GW2.C16.delta C β₂ ν) 1 (Or.inl rfl)
      (l41_delta_mem_ZIrr C hν) (l41_delta_apply_one C hν)
      (by rw [l41_delta_inner_self C h2 hβ hν, if_neg hfix]; norm_num)
  have hpm₁ : IsPmIrr g₁ := s4L41_pmIrr_of_norm_one hg₁Z (by simpa using hg₁n)
  have hpm₂ : IsPmIrr g₂ := s4L41_pmIrr_of_norm_one hg₂Z (by simpa using hg₂n)
  have hdelta : Work.GW2.C16.delta C β₂ ν = ind C (ν - lamCF C β₂ * ν) := rfl
  have hswap : ind C (lamCF C β₂ * ν - ν) = g₂ - g₁ := by
    rw [s4L41_ind_swap C (β₂ := β₂) ν]
    change -(Work.GW2.C16.delta C β₂ ν) = g₂ - g₁
    rw [hdec, neg_sub]
  have hdec' : ind C (ν - lamCF C β₂ * ν) = g₁ - g₂ := by
    rw [← hdelta]; exact hdec
  have hvg₁ : g₁ (C.t : G) = 2 * ν C.t :=
    l41Vi C (lamCF C β₂ * ν) ν hν₂ hν ⟨β₂, hlam2.symm⟩ hfix₂ hfix
      (by rw [lam_two_mul_apply_t C h2 hβ ν]) g₂ g₁ hpm₂ hpm₁ hswap
  have hvg₂ : g₂ (C.t : G) = 2 * (lamCF C β₂ * ν) C.t :=
    l41Vi C ν (lamCF C β₂ * ν) hν hν₂ ⟨β₂, rfl⟩ hfix hfix₂
      (by rw [lam_two_mul_apply_t C h2 hβ ν, neg_neg]) g₁ g₂ hpm₁ hpm₂ hdec'
  let f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ := fun ξ =>
    if ξ = ν ∨ ξ = sconj C ν then g₁
    else if ξ = lamCF C β₂ * ν ∨ ξ = sconj C (lamCF C β₂ * ν) then g₂ else 0
  have hfν : f ν = g₁ := by dsimp only [f]; rw [if_pos (Or.inl rfl)]
  have hfνs : f (sconj C ν) = g₁ := by dsimp only [f]; rw [if_pos (Or.inr rfl)]
  have hfν₂ : f (lamCF C β₂ * ν) = g₂ := by
    have h1 : ¬ (lamCF C β₂ * ν = ν ∨ lamCF C β₂ * ν = sconj C ν) := by
      rintro (h | h)
      · exact hne₂ h
      · exact hne_s h.symm
    dsimp only [f]; rw [if_neg h1, if_pos (Or.inl rfl)]
  have hfν₂s : f (sconj C (lamCF C β₂ * ν)) = g₂ := by
    have h1 : ¬ (sconj C (lamCF C β₂ * ν) = ν ∨ sconj C (lamCF C β₂ * ν) = sconj C ν) := by
      rintro (h | h)
      · exact hne₂s_ν h
      · exact hne₂s_s h
    dsimp only [f]; rw [if_neg h1, if_pos (Or.inr rfl)]
  refine ⟨f, ?_⟩
  intro μ hμE ν' hν'E hμirr hν'irr
  rw [s4L41_orbitKey_ne C h2 hβ ν] at hμE hν'E
  have hpt : ∀ ξ : ClassFunction ↥C.P.H0 ℂ,
      ξ = ν ∨ ξ = lamCF C β₂ * ν ∨ ξ = sconj C ν ∨ ξ = sconj C (lamCF C β₂ * ν) →
      f ξ ∈ ZIrr G ∧ f (sconj C ξ) = f ξ ∧
      (ClassFunction.inner (f ξ) (f ξ) = (if sconj C ξ = ξ then (2 : ℂ) else 1)) ∧
      (sconj C ξ ≠ ξ →
        ¬ ((lamOrbit C ξ).ncard = 4 ∧ sconj C '' lamOrbit C ξ = lamOrbit C ξ) →
        f ξ (C.t : G) = 2 * ξ C.t) := by
    rintro ξ (rfl | rfl | rfl | rfl)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfν]; exact hg₁Z
      · rw [hfνs, hfν]
      · rw [hfν, if_neg hfix]; simpa using hg₁n
      · intro _ _
        rw [hfν]; exact hvg₁
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfν₂]; exact hg₂Z
      · rw [hfν₂s, hfν₂]
      · rw [hfν₂, if_neg hfix₂]; simpa using hg₂n
      · intro _ _
        rw [hfν₂]; exact hvg₂
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfνs]; exact hg₁Z
      · rw [sconj_sconj C ν, hfν, hfνs]
      · rw [hfνs, if_neg hfix_s]; simpa using hg₁n
      · intro _ _
        rw [hfνs, sconj_apply_t C ν]; exact hvg₁
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hfν₂s]; exact hg₂Z
      · rw [sconj_sconj C (lamCF C β₂ * ν), hfν₂, hfν₂s]
      · rw [hfν₂s, if_neg hfix₂s]; simpa using hg₂n
      · intro _ _
        rw [hfν₂s, sconj_apply_t C (lamCF C β₂ * ν)]; exact hvg₂
  obtain ⟨h1, h2', h3, h6⟩ := hpt ν' hν'E
  refine ⟨h1, h2', h3, ?_, ?_, h6⟩
  · intro hLam
    rcases (LamEquiv_iff C h2 hβ μ ν').mp hLam with h | h
    · subst h
      rw [sub_self, sub_self]
      simp only [ind, ClassFunction.induce_zero]
    · subst h
      rcases hμE with hμ | hμ | hμ | hμ
      · subst hμ
        rw [hfν, hfν₂, ← hdelta]
        exact hdec
      · subst hμ
        rw [hlam2, hfν₂, hfν, hswap]
      · subst hμ
        rw [← sconj_lam_two_mul C h2 hβ ν, l41_ind_sconj_sub C ν (lamCF C β₂ * ν),
          hfνs, hfν₂s, ← hdelta]
        exact hdec
      · subst hμ
        rw [hlam2s, l41_ind_sconj_sub C (lamCF C β₂ * ν) ν, hfν₂s, hfνs, hswap]
  · intro hLam hne _
    rcases (LamEquiv_iff C h2 hβ μ ν').mp hLam with h | h
    · exact absurd h.symm hne
    · subst h
      rcases hμE with hμ | hμ | hμ | hμ
      · subst hμ
        rw [hfν, hfν₂]; exact hdisj
      · subst hμ
        rw [hlam2, hfν₂, hfν]
        exact fun χ => (hdisj χ).symm
      · subst hμ
        rw [← sconj_lam_two_mul C h2 hβ ν, hfνs, hfν₂s]; exact hdisj
      · subst hμ
        rw [hlam2s, hfν₂s, hfνs]
        exact fun χ => (hdisj χ).symm

end GoodOn

/-! ## 3. Auxiliary facts for the main argument -/

/-- `§3` (`Sec3Hyp`) holds trivially when `D.n = 2`: then `|S₀| = 2`, so every element of `S₀`
is an involution. -/
theorem s4L41_sec3Hyp (D : Work.GW2.BGData G) (hn : D.n = 2) : Work.GW2.C16.Sec3Hyp D := by
  intro x hx u _
  have hcard : Nat.card ↥D.S0 = 2 := by rw [(nCases G D).2, hn]
  have h : orderOf (⟨x, hx⟩ : ↥D.S0) ∣ 2 := by
    have hd := orderOf_dvd_natCard (⟨x, hx⟩ : ↥D.S0)
    rwa [hcard] at hd
  have hx2 : (⟨x, hx⟩ : ↥D.S0) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  have hx2G : x ^ 2 = 1 := by
    have := congrArg (fun y : ↥D.S0 => (y : G)) hx2
    simpa using this
  rw [hx2G, one_mul, mul_one]

/-- A sum over all irreducible characters equals the set-restricted `finsum` over `T`, when the
summand vanishes off `T` and every element of `T` is an irreducible character. -/
theorem s4L41_sum_irr_eq_finsum (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (T : Set (ClassFunction ↥C.P.H0 ℂ)) (hT : ∀ ξ ∈ T, IsIrreducibleCharacter ξ)
    (F : ClassFunction ↥C.P.H0 ℂ → ℂ)
    (hF : ∀ ν : IrreducibleCharacter ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) ∉ T →
      F (ν : ClassFunction ↥C.P.H0 ℂ) = 0) :
    (∑ ν : IrreducibleCharacter ↥C.P.H0, F (ν : ClassFunction ↥C.P.H0 ℂ)) =
      ∑ᶠ ξ ∈ T, F ξ := by
  classical
  rw [finsum_mem_def]
  have hinj : Set.InjOn (fun ν : IrreducibleCharacter ↥C.P.H0 =>
      (ν : ClassFunction ↥C.P.H0 ℂ))
      ↑(Finset.univ : Finset (IrreducibleCharacter ↥C.P.H0)) :=
    fun a _ b _ h => IrreducibleCharacter.ext h
  have hsupp : Function.support (T.indicator F) ⊆
      ↑(Finset.univ.image (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        (ν : ClassFunction ↥C.P.H0 ℂ))) := by
    intro ν hν
    rw [Function.mem_support] at hν
    have hmem : ν ∈ T := by
      by_contra h
      rw [Set.indicator_of_notMem h] at hν
      exact hν rfl
    exact Finset.mem_image.mpr ⟨⟨ν, hT ν hmem⟩, Finset.mem_univ _, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro ν _
  by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ T
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, hF ν h]

/-- A sum of an odd number of odd integers is odd. -/
theorem s4L41_odd_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, Odd (f i)) (hc : Odd (s.card : ℤ)) : Odd (∑ i ∈ s, f i) := by
  have h1 : ∑ i ∈ s, f i = (s.card : ℤ) + ∑ i ∈ s, (f i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  rw [h1]
  exact hc.add_even (Finset.even_sum _ fun i hi => (hf i hi).sub_odd odd_one)

/-- `χ(1)` is odd whenever `χ(t)` is odd. -/
theorem s4L41_odd_of_odd_t (C : Sec2Ctx G) {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ)
    (h : ∃ k : ℤ, χ (C.t : G) = (k : ℂ) ∧ Odd k) :
    ∃ d : ℤ, χ 1 = (d : ℂ) ∧ Odd d := by
  obtain ⟨k, hk, hko⟩ := h
  -- `χ(t) ≡ χ(1) (mod 2)`
  have hcong : Work.BG.AlgIntModTwo (χ (C.t : G)) (χ 1) := by
    have h1 : ((1 : ↥C.P.H0) : G) ∈ C.P.U := by simpa using C.P.U.one_mem
    have hres := s02_char16_t_mul C h1 χ (IsPmIrr.mem_ZIrr hχ)
    simpa using hres
  obtain ⟨c, hcint, hc⟩ := hcong
  -- `χ(1) = (d : ℂ)` for some integer `d`
  have hχint : ∃ d : ℤ, χ 1 = (d : ℂ) := by
    rcases hχ with h | h
    · obtain ⟨n, _, hval, -⟩ := h.exists_natDegree_charValue_one_dvd_card
      exact ⟨n, by rw [hval]; norm_num⟩
    · obtain ⟨n, _, hval, -⟩ := h.exists_natDegree_charValue_one_dvd_card
      refine ⟨-(n : ℤ), ?_⟩
      have hval' : -χ 1 = (n : ℂ) := by simpa [ClassFunction.neg_apply] using hval
      have hneg : χ 1 = -(n : ℂ) := by rw [← neg_neg (χ 1), hval']
      rw [hneg]; norm_num
  obtain ⟨d, hd⟩ := hχint
  have hc' : (k : ℂ) - (d : ℂ) = 2 * c := by
    have hc0 := hc
    rw [hk, hd] at hc0
    exact hc0
  -- `c` is a rational algebraic integer, hence an integer
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_of_isIntegral_of_mem_range_rat hcint
    ⟨(((k - d : ℤ) : ℚ) / 2), by
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      have hcq : c = ((k : ℂ) - (d : ℂ)) / 2 := by
        rw [eq_div_iff h2]
        rw [mul_comm c 2]
        exact hc'.symm
      have hcast : ((((k - d : ℤ) : ℚ) / 2 : ℚ) : ℂ) = ((k : ℂ) - (d : ℂ)) / 2 := by
        push_cast
        ring
      rw [hcast, ← hcq]⟩
  have hkd : k - d = 2 * z := by
    have hkdz : (k : ℂ) - (d : ℂ) = 2 * (z : ℂ) := by rw [hc', ← hz]
    have hcast : ((k - d : ℤ) : ℂ) = ((2 * z : ℤ) : ℂ) := by push_cast; exact hkdz
    exact_mod_cast hcast
  refine ⟨d, hd, ?_⟩
  have hdz : d = k - 2 * z := by omega
  rw [hdz]
  exact hko.sub_even (even_two_mul z)


/-- **Lemma 3.4 (first assertion), specialised to `Λ = {1, λ₂}`.**  If `ξ ∈ 𝒮(χ)` is not
`s`-fixed then `𝒮(χ) = {ξ, ξ^s}`.  In this situation the exceptional configuration
`|Λξ| = 4` of the general Lemma 3.4 is impossible (`|Λξ| = 2`), so the only inputs are
Theorem 2.3 (vi), Theorem 3.2 and Lemma 2.4. -/
theorem s4L41_L34 (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (D : Work.GW2.BGData G) (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) :
    ∀ ξ ∈ Work.GW2.C16.bset C f χ,
      sconj C ξ ≠ ξ → Work.GW2.C16.bset C f χ = {ξ, sconj C ξ} := by
  classical
  have hOS := bset_orbit_struct C f hf χ hχ
  have hξ0 : ∀ ξ ∈ Work.GW2.C16.bset C f χ, sconj C ξ ∈ Work.GW2.C16.bset C f χ :=
    fun ξ hξ => (hOS.1 ξ hξ).1
  intro ξ hξ hξs
  by_contra hne'
  have hex : f ξ (C.t : G) = 2 * ξ C.t → Work.GW2.C16.bset C f χ = {ξ, sconj C ξ} := by
    intro hval
    have hξirr : IsIrreducibleCharacter ξ := hξ.1
    have hG := (hf.1 ξ hξirr) ξ (Or.inl (s02c_LamEquiv_refl C ξ)) ξ
      (Or.inl (s02c_LamEquiv_refl C ξ)) hξirr hξirr
    obtain ⟨hZIf, hsconjf, hnormf, -, -, -⟩ := hG
    have hnorm1 : ClassFunction.inner (f ξ) (f ξ) = 1 := by rw [hnormf]; simp [hξs]
    have hpmf : IsPmIrr (f ξ) := s4L41_pmIrr_of_norm_one hZIf hnorm1
    have hχeq : χ = f ξ ∨ χ = -f ξ := by
      rcases l34_eq_pm_of_inner_ne_zero hZIf hnorm1 hχ hξ.2 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    have hbseteq : Work.GW2.C16.bset C f (f ξ) = Work.GW2.C16.bset C f χ := by
      rcases hχeq with h | h
      · rw [h]
      · rw [h]
        ext η
        simp only [Work.GW2.C16.bset, Set.mem_ofPred_eq]
        rw [ClassFunction.inner_neg_left]; simp
    have hcard : (Work.GW2.C16.bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
    have hfin : (Work.GW2.C16.bset C f χ).Finite := s02_bset_finite C f χ
    ext η
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hη
      by_contra hnot
      have hην : η ≠ ξ := fun h => hnot (Or.inl h)
      have hηνs : η ≠ sconj C ξ := fun h => hnot (Or.inr h)
      obtain ⟨hηirr, hηne0⟩ := hη
      have hsub : ({ξ, sconj C ξ, η} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆
          Work.GW2.C16.bset C f χ := by
        intro ζ hζ
        rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
        rcases hζ with rfl | rfl | rfl
        · exact ⟨hξirr, hξ.2⟩
        · exact hξ0 ξ hξ
        · exact ⟨hηirr, hηne0⟩
      have hnot1 : ξ ∉ ({sconj C ξ, η} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
        intro hm
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with h | h
        · exact hξs h.symm
        · exact hην h.symm
      have hnot2 : sconj C ξ ∉ ({η} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
        intro hm
        rw [Set.mem_singleton_iff] at hm
        exact hηνs hm.symm
      have h3 : ({ξ, sconj C ξ, η} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem hnot1 (Set.toFinite _),
          Set.ncard_insert_of_notMem hnot2 (Set.toFinite _), Set.ncard_singleton]
      have heq : Work.GW2.C16.bset C f χ = {ξ, sconj C ξ, η} :=
        (Set.eq_of_subset_of_ncard_le hsub (by rw [h3]; exact hcard) hfin).symm
      have hbsetf : Work.GW2.C16.bset C f (f ξ) = {ξ, sconj C ξ, η} := by
        rw [hbseteq]; exact heq
      have hT := (lemma24 C f hf (f ξ) hpmf).2.1 C.t C.t_not_mem_U
      have hsum : (∑ᶠ ζ ∈ Work.GW2.C16.bset C f (f ξ),
            ClassFunction.inner (f ξ) (f ζ) * ζ C.t)
          = 2 * ξ C.t + ClassFunction.inner (f ξ) (f η) * η C.t := by
        rw [hbsetf,
          finsum_mem_insert (f := fun ζ => ClassFunction.inner (f ξ) (f ζ) * ζ C.t)
            (a := ξ) (s := ({sconj C ξ, η} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot1
            (Set.toFinite _),
          finsum_mem_insert (f := fun ζ => ClassFunction.inner (f ξ) (f ζ) * ζ C.t)
            (a := sconj C ξ) (s := ({η} : Set (ClassFunction ↥C.P.H0 ℂ))) hnot2
            (Set.toFinite _),
          finsum_mem_singleton, hsconjf, hnorm1, sconj_apply_t]
        ring
      rw [hsum] at hT
      rw [hval] at hT
      have hmem : η ∈ Work.GW2.C16.bset C f (f ξ) := by
        rw [hbsetf]
        exact Set.mem_insert_of_mem ξ (Set.mem_insert_of_mem (sconj C ξ) (Set.mem_singleton η))
      have hzero : ClassFunction.inner (f ξ) (f η) * η C.t = 0 := by
        have h1 : 2 * ξ C.t + ClassFunction.inner (f ξ) (f η) * η C.t = 2 * ξ C.t + 0 := by
          rw [add_zero]; exact hT.symm
        exact add_left_cancel h1
      exact mul_ne_zero hmem.2 (value_t_ne_zero C η hηirr) hzero
    · rintro (rfl | rfl)
      · exact ⟨hξirr, hξ.2⟩
      · exact hξ0 ξ hξ
  have hvalne : f ξ (C.t : G) ≠ 2 * ξ C.t := fun hval => hne' (hex hval)
  have hbad : (lamOrbit C ξ).ncard = 4 ∧ sconj C '' lamOrbit C ξ = lamOrbit C ξ := by
    by_contra hb
    have hG := (hf.1 ξ hξ.1) ξ (Or.inl (s02c_LamEquiv_refl C ξ)) ξ
      (Or.inl (s02c_LamEquiv_refl C ξ)) hξ.1 hξ.1
    exact hvalne (hG.2.2.2.2.2 hξs hb)
  rw [lamOrbit_ncard_eq_two C h2 hβ hξ.1] at hbad
  exact absurd hbad.1 (by norm_num)



/-! ## 4. The first case of Lemma 3.3 in the situation `|S| = 4` -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **BG Lemma 3.3, first case, in the form needed here.**  If `𝒮(χ) = bset C f χ` consists of
exactly two characters `ξ₁ ≠ ξ₂`, both `s`-fixed with `|Λξᵢ| = D.n`, then we get a
contradiction.  (This is the special case `|Λ| = 2` of the paper's argument p. 209: the
congruence of Lemma 2.4 on `U`, the triviality of `χ` on `C_U(S)` obtained from Gorenstein
4.2.10 and an odd index, and the injectivity of Glauberman's correspondence.) -/
theorem s4L41_L33 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    {ξ₁ ξ₂ : ClassFunction ↥C.P.H0 ℂ}
    (h₁ : ξ₁ ∈ Work.GW2.C16.bset C f χ) (h₂ : ξ₂ ∈ Work.GW2.C16.bset C f χ) (hne : ξ₁ ≠ ξ₂)
    (hs₁ : Work.BG.sconj C ξ₁ = ξ₁) (hs₂ : Work.BG.sconj C ξ₂ = ξ₂)
    (ho₁ : (Work.BG.lamOrbit C ξ₁).ncard = D.n) (ho₂ : (Work.BG.lamOrbit C ξ₂).ncard = D.n)
    (hT2 : (Work.GW2.C16.bset C f χ).ncard = 2) : False := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(Work.GW2.C16.Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥(fixedSubgroupS (L33D.phiS D C hDC)) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroupS (L33D.phiS D C hDC)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hfin : (Work.GW2.C16.bset C f χ).Finite := s02_bset_finite C f χ
  -- `𝒮(χ) = {ξ₁, ξ₂}`
  have hTset : Work.GW2.C16.bset C f χ = {ξ₁, ξ₂} := by
    have hsub : ({ξ₁, ξ₂} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ Work.GW2.C16.bset C f χ := by
      intro ν hν
      rcases (by simpa using hν : ν = ξ₁ ∨ ν = ξ₂) with rfl | rfl
      · exact h₁
      · exact h₂
    have hcard2 : ({ξ₁, ξ₂} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 := Set.ncard_pair hne
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2, hT2]) hfin).symm
  -- the sum over `𝒮(χ)`
  have hsum : ∀ u : ↥C.P.H0, (∑ᶠ ν ∈ Work.GW2.C16.bset C f χ, ν u) = ξ₁ u + ξ₂ u := by
    intro u
    rw [hTset]
    rw [finsum_mem_insert (f := fun ν : ClassFunction ↥C.P.H0 ℂ => ν u) (a := ξ₁)
      (s := ({ξ₂} : Set (ClassFunction ↥C.P.H0 ℂ)))
      (by simp only [Set.mem_singleton_iff]; exact hne) (Set.toFinite _)]
    rw [finsum_mem_singleton]
  have hcong : ∀ u : ↥C.P.H0, (u : G) ∈ C.P.U →
      AlgIntModTwo (χ (u : G)) (∑ᶠ ν ∈ Work.GW2.C16.bset C f χ, ν u) :=
    (lemma24 C f hf χ hχ).2.2
  -- degrees of the two members are odd
  have hαirr : ∀ {ν : ClassFunction ↥C.P.H0 ℂ}, IsIrreducibleCharacter ν →
      (Work.BG.lamOrbit C ν).ncard = D.n →
      IsIrreducibleCharacter (ClassFunction.restrict (Work.GW2.C16.Uin C) ν) := by
    intro ν hν hn
    obtain ⟨a, hairr, hcase⟩ := rem31ShapeLeaf D C hDC hS3 ν hν
    rcases hcase with h | h
    · rw [h.1]; exact hairr
    · obtain ⟨a₂, -, -, -, -, h2n⟩ := h
      rw [hn] at h2n
      exact absurd h2n (by have := D.two_le; omega)
  have hdegodd : ∀ {ν : ClassFunction ↥C.P.H0 ℂ}, IsIrreducibleCharacter ν →
      (Work.BG.lamOrbit C ν).ncard = D.n → ∃ d : ℤ, ν 1 = (d : ℂ) ∧ Odd d := by
    intro ν hν hn
    obtain ⟨a, hairr, hcase⟩ := rem31ShapeLeaf D C hDC hS3 ν hν
    have hva : ClassFunction.restrict (Work.GW2.C16.Uin C) ν = a := by
      rcases hcase with h | h
      · exact h.1
      · obtain ⟨a₂, -, -, -, -, h2n⟩ := h
        rw [hn] at h2n
        exact absurd h2n (by have := D.two_le; omega)
    obtain ⟨n, -, hna, hndvd⟩ := hairr.exists_natDegree_charValue_one_dvd_card
    have hnodd : Odd n := Odd.of_dvd_nat (L33D.odd_card_Uin D C hDC) hndvd
    refine ⟨(n : ℤ), ?_, by exact_mod_cast hnodd⟩
    have h1 : ClassFunction.restrict (Work.GW2.C16.Uin C) ν (1 : ↥(Work.GW2.C16.Uin C)) = ν 1 := by
      rw [ClassFunction.restrict_apply]; rfl
    rw [← h1, hva, hna]
    exact (Int.cast_natCast n).symm
  obtain ⟨d₁, hd₁, hdo₁⟩ := hdegodd h₁.1 ho₁
  obtain ⟨d₂, hd₂, hdo₂⟩ := hdegodd h₂.1 ho₂
  -- `χ(1)` is even
  have heven : AlgIntModTwo (χ 1) 0 := by
    have hstep := hcong (1 : ↥C.P.H0) C.P.U.one_mem
    simp only [Subgroup.coe_one] at hstep
    rw [hsum 1] at hstep
    obtain ⟨k₁, hk₁⟩ := hdo₁
    obtain ⟨k₂, hk₂⟩ := hdo₂
    have h0 : AlgIntModTwo (ξ₁ 1 + ξ₂ 1) 0 := by
      refine ⟨((k₁ + k₂ + 1 : ℤ) : ℂ), isIntegral_intCast _, ?_⟩
      rw [hd₁, hd₂, hk₁, hk₂]; push_cast; ring
    simpa using hstep.trans h0
  -- on `C_U(S)`, the two members agree modulo `2`
  have honC : ∀ u : ↥(Work.GW2.C16.Uin C), u ∈ fixedSubgroupS (L33D.phiS D C hDC) →
      AlgIntModTwo (ξ₁ (u : ↥C.P.H0)) (ξ₂ (u : ↥C.P.H0)) := by
    intro u hu
    have hcomm := (L33D.mem_fixedSubgroupS_phiS' D C hDC u).mp hu
    have hArith := lemma33Arith D C hDC hχ heven (Subgroup.mem_subgroupOf.mp u.2) hcomm
    have hS := hcong (u : ↥C.P.H0) (Subgroup.mem_subgroupOf.mp u.2)
    rw [hsum (u : ↥C.P.H0)] at hS
    have hz : AlgIntModTwo (ξ₁ (u : ↥C.P.H0) + ξ₂ (u : ↥C.P.H0)) 0 := hS.symm.trans hArith
    have hmid : AlgIntModTwo (ξ₁ (u : ↥C.P.H0) + ξ₂ (u : ↥C.P.H0))
        (ξ₁ (u : ↥C.P.H0) - ξ₂ (u : ↥C.P.H0)) :=
      ⟨ξ₂ (u : ↥C.P.H0), isIntegral_apply_of_isIrreducibleCharacter' h₂.1 (u : ↥C.P.H0),
        by ring⟩
    have hz0 : AlgIntModTwo (ξ₁ (u : ↥C.P.H0) - ξ₂ (u : ↥C.P.H0)) 0 := hmid.symm.trans hz
    simpa [AlgIntModTwo] using hz0
  -- the restrictions are distinct: otherwise `ξ₁ ~ ξ₂` and then `ξ₂ = ξ₁^s = ξ₁`
  have hαne : ClassFunction.restrict (Work.GW2.C16.Uin C) ξ₁ ≠
      ClassFunction.restrict (Work.GW2.C16.Uin C) ξ₂ := by
    intro hres
    obtain ⟨β, hβU, hβeq⟩ := exists_linearClassFunction_mul_of_restrict_eq_restrict
      (H := Work.GW2.C16.Uin C) h₁.1 h₂.1 hres (hαirr h₁.1 ho₁)
    have hker : (Work.GW2.C16.Uin C) ≤ β.ker := fun x hx => MonoidHom.mem_ker.mpr (hβU ⟨x, hx⟩)
    have hfac : linearClassFunction β =
        lamCF C (QuotientGroup.lift (Work.GW2.C16.Uin C) β hker) := by
      ext x
      simp only [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
      exact congrArg (fun y : ℂˣ => (y : ℂ))
        (QuotientGroup.lift_mk' (Work.GW2.C16.Uin C) (φ := β) hker x).symm
    have hlam : LamEquiv C ξ₁ ξ₂ := by
      refine ⟨QuotientGroup.lift (Work.GW2.C16.Uin C) β hker, ?_⟩
      rw [hβeq, hfac]
      ext x
      rw [ClassFunction.mul_apply, ClassFunction.mul_apply]
      ring
    have hconj : ξ₂ = sconj C ξ₁ :=
      (bset_orbit_struct C f hf χ hχ).2 ξ₁ h₁ ξ₂ h₂ hlam (Ne.symm hne)
    exact hne (hconj.trans hs₁).symm
  -- `S`-invariance of the two restrictions
  have hinv : ∀ ν : ClassFunction ↥C.P.H0 ℂ, sconj C ν = ν →
      ∀ (s : ↥(D.S)) (u : ↥(Work.GW2.C16.Uin C)),
        ClassFunction.restrict (Work.GW2.C16.Uin C) ν (L33D.phiS D C hDC s u) =
          ClassFunction.restrict (Work.GW2.C16.Uin C) ν u := by
    intro ν hs
    refine L33D.invariant_phiS D C hDC (ClassFunction.restrict (Work.GW2.C16.Uin C) ν) ?_ ?_
    · intro s hs0 u
      have hsH0 : (s : G) ∈ C.P.H0 := by
        rw [hDC.H0_eq]
        exact Subgroup.mem_sup_right hs0
      have hkey : ((L33D.phiS D C hDC s u : ↥(Work.GW2.C16.Uin C)) : ↥C.P.H0) =
          (⟨(s : G), hsH0⟩ : ↥C.P.H0) * (u : ↥C.P.H0) * (⟨(s : G), hsH0⟩ : ↥C.P.H0)⁻¹ :=
        Subtype.ext (L33D.phiS_apply D C hDC s u)
      rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, hkey,
        ClassFunction.conj_eq]
    · intro u
      have hkey : ((L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩ u : ↥(Work.GW2.C16.Uin C)) : ↥C.P.H0) =
          conjMulEquiv C.P C.s (u : ↥C.P.H0) := by
        refine Subtype.ext ?_
        rw [conjMulEquiv_apply, hDC.s_eq]
        exact L33D.phiS_apply D C hDC ⟨D.t1, D.t1_mem⟩ u
      have hval : ν (conjMulEquiv C.P C.s (u : ↥C.P.H0)) = ν (u : ↥C.P.H0) := by
        have hfun : sconj C ν (u : ↥C.P.H0) = ν (u : ↥C.P.H0) :=
          congrFun (congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => (φ : ↥C.P.H0 → ℂ)) hs)
            (u : ↥C.P.H0)
        rw [sconj, conjByH, ClassFunction.compHom_apply] at hfun
        exact hfun
      rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, hkey]
      exact hval
  -- Glauberman's correspondence is injective
  obtain ⟨u₀, hu₀⟩ := glaubCorrDistinct (S := ↥(D.S)) (U := ↥(Work.GW2.C16.Uin C))
    (L33D.isPGroup_S D) (L33D.odd_card_Uin D C hDC) (L33D.phiS D C hDC)
    (ClassFunction.restrict (Work.GW2.C16.Uin C) ξ₁)
    (ClassFunction.restrict (Work.GW2.C16.Uin C) ξ₂)
    (hαirr h₁.1 ho₁) (hαirr h₂.1 ho₂)
    (hinv ξ₁ hs₁) (hinv ξ₂ hs₂) hαne
  exact hu₀ (by simpa using honC (u₀ : ↥(Work.GW2.C16.Uin C)) u₀.2)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem s4L41 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Lemma41Prop D C := by
  intro hDC hn β₂ hβ χ hχ hne
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- 0. `|H₀/U| = 2` and the §3 hypothesis
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hDC hn
  have hS3 : Sec3Hyp D := s4L41_sec3Hyp D hn
  -- 1. the coherent map
  have hOrb : OrbitCoherenceProp C := fun ν hν => by
    by_cases hfix : sconj C ν = ν
    · exact s4L41_goodOn_of_sfixed C h2 hβ hν hfix
    · exact s4L41_goodOn_of_ne C h2 hβ hν hfix
  obtain ⟨f, hf⟩ := (coherence23_iff C).mp
    (s02_assemblyFull C (s02_gram C) (s02_bsValueT C) (s02_assemblyCore C (sconjLam C) hOrb))
  -- 2. Lemma 2.4, and the orbit structure of `𝒮(χ) = bset C f χ`
  obtain ⟨hSfin, hSval, hScong⟩ := lemma24 C f hf χ hχ
  obtain ⟨hOS1, hOS2⟩ := bset_orbit_struct C f hf χ hχ
  -- 3. `δ_ν = f ν - f (λ₂ν)`
  have hP1 : ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
      ind C (ν - lamCF C β₂ * ν) = f ν - f (lamCF C β₂ * ν) := by
    intro ν hν
    exact ((hf.1 ν hν) ν (Or.inl (s02c_LamEquiv_refl C ν)) (lamCF C β₂ * ν)
      (Or.inl ⟨β₂, rfl⟩) hν (lam_two_mul_irr C hν)).2.2.2.1 ⟨β₂, rfl⟩
  have hdel : ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
      delta C β₂ ν = f ν - f (lamCF C β₂ * ν) := fun ν hν => hP1 ν hν
  -- 4. `(χ, δ_ν) ≠ 0` forces `ν ∈ 𝒮(χ)` or `λ₂ν ∈ 𝒮(χ)`
  have hmemd : ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
      ClassFunction.inner χ (delta C β₂ ν) ≠ 0 →
      ν ∈ bset C f χ ∨ lamCF C β₂ * ν ∈ bset C f χ := by
    intro ν hν hδ
    have hne' : ClassFunction.inner χ (f ν) -
        ClassFunction.inner χ (f (lamCF C β₂ * ν)) ≠ 0 := by
      rw [← ClassFunction.inner_sub_right, ← hdel ν hν]
      exact hδ
    by_contra hc
    push_neg at hc
    have hc1 : ClassFunction.inner χ (f ν) = 0 := by
      by_contra h
      exact hc.1 ⟨hν, h⟩
    have hc2 : ClassFunction.inner χ (f (lamCF C β₂ * ν)) = 0 := by
      by_contra h
      exact hc.2 ⟨lam_two_mul_irr C hν, h⟩
    exact hne' (by rw [hc1, hc2, sub_zero])
  -- 5. `𝒮(χ) ≠ ∅`
  have hTne : (bset C f χ).Nonempty := by
    obtain ⟨ν, hν⟩ := hne
    rcases hmemd ν hν.1.1 hν.2 with h | h
    · exact ⟨ν, h⟩
    · exact ⟨lamCF C β₂ * ν, h⟩
  -- 6. not both `ξ` and `λ₂ξ` in `𝒮(χ)`
  have hP6a : ∀ ξ : ClassFunction ↥C.P.H0 ℂ,
      ¬ (ξ ∈ bset C f χ ∧ lamCF C β₂ * ξ ∈ bset C f χ) := by
    rintro ξ ⟨h1, hT2⟩
    have hξirr : IsIrreducibleCharacter ξ := h1.1
    have hne' : lamCF C β₂ * ξ ≠ ξ := lam_two_mul_ne_self C h2 hβ hξirr
    exact sconj_ne_lam_two_mul C h2 hβ hξirr
      (hOS2 ξ h1 (lamCF C β₂ * ξ) hT2 ⟨β₂, rfl⟩ hne').symm
  -- 7. a two-element `𝒮(χ) = {ξ, ξ^s}` is impossible
  have hempty : ∀ ξ : ClassFunction ↥C.P.H0 ℂ,
      bset C f χ = {ξ, sconj C ξ} → sconj C ξ ≠ ξ → False := by
    intro ξ hS hξs
    obtain ⟨ν, hν⟩ := hne
    rcases hmemd ν hν.1.1 hν.2 with h | h
    · rw [hS] at h
      rcases h with h | h
      · exact hξs (by rw [← h]; exact hν.1.2.1)
      · have hconj : sconj C ν = ν := hν.1.2.1
        rw [h, sconj_sconj C ξ] at hconj
        exact hξs hconj.symm
    · rw [hS] at h
      rcases h with h | h
      · have hconj : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν := by
          rw [sconj_lam_two_mul C h2 hβ, hν.1.2.1]
        rw [h] at hconj
        exact hξs hconj
      · have hconj : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν := by
          rw [sconj_lam_two_mul C h2 hβ, hν.1.2.1]
        rw [h, sconj_sconj C ξ] at hconj
        exact hξs hconj.symm
  -- 8. every member of `𝒮(χ)` is `s`-fixed
  have hsfixed : ∀ ξ ∈ bset C f χ, sconj C ξ = ξ := by
    intro ξ hξ
    by_contra hξs
    have h34 := s4L41_L34 C h2 hβ D hDC hS3 f hf χ hχ ξ hξ hξs
    exact hempty ξ h34 hξs
  -- 9. `ν ∈ 𝒮'(χ)` forces `ν` to be `s`-fixed
  have hPsi : ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν → ν C.t = ν 1 →
      ClassFunction.inner χ (delta C β₂ ν) ≠ 0 → sconj C ν = ν := by
    intro ν hν hε hδ
    by_contra hfix
    rcases hmemd ν hν hδ with h | h
    · have h34 := s4L41_L34 C h2 hβ D hDC hS3 f hf χ hχ ν h hfix
      exact hempty ν h34 hfix
    · have hlamνirr : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hν
      have hlamfix : sconj C (lamCF C β₂ * ν) ≠ lamCF C β₂ * ν :=
        fun hh => hfix ((sconj_lam_two_mul_eq_iff C h2 hβ ν).mp hh)
      have h34 := s4L41_L34 C h2 hβ D hDC hS3 f hf χ hχ (lamCF C β₂ * ν) h hlamfix
      exact hempty (lamCF C β₂ * ν) h34 hlamfix
  -- 10. `ε(λ₂ξ) ↔ ¬ ε(ξ)`
  have hεlam : ∀ ξ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ξ →
      (((lamCF C β₂ * ξ) C.t = (lamCF C β₂ * ξ) 1) ↔ ¬ (ξ C.t = ξ 1)) := by
    intro ξ hξ
    have h1 : (lamCF C β₂ * ξ) 1 = ξ 1 := by
      rw [ClassFunction.mul_apply, lamCF, ClassFunction.compHom_apply,
        linearClassFunction_apply, map_one]
      simp
    rw [lam_two_mul_apply_t C h2 hβ ξ, h1]
    constructor
    · intro hh hξt
      have hz : ξ C.t = 0 := by linear_combination (-1 / 2) * hh + (1 / 2) * hξt
      exact t_val_ne_zero C hξ hz
    · intro hh
      rcases t_val_or C hξ with h | h
      · exact absurd h hh
      · rw [h]; ring
  -- 11. Lemma 1.7 at `t` gives `χ(t) = Σ_{ν ∈ 𝒮'(χ)} (χ, δ_ν) ν(1)`
  let rep : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ := fun ξ =>
    if ξ C.t = ξ 1 then lamCF C β₂ * ξ else ξ
  have hrep1 : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      IsIrreducibleCharacter (rep (ν : ClassFunction ↥C.P.H0 ℂ)) ∧
        LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (rep (ν : ClassFunction ↥C.P.H0 ℂ)) := by
    intro ν
    by_cases h : (ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1
    · have hr : rep (ν : ClassFunction ↥C.P.H0 ℂ) =
          lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ) := by
        dsimp only [rep]; rw [if_pos h]
      rw [hr]
      exact ⟨lam_two_mul_irr C ν.2, ⟨β₂, rfl⟩⟩
    · have hr : rep (ν : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ) := by
        dsimp only [rep]; rw [if_neg h]
      rw [hr]
      exact ⟨ν.2, s02c_LamEquiv_refl C _⟩
  have hrep2 : ∀ ν ν' : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ) (ν' : ClassFunction ↥C.P.H0 ℂ) →
        rep (ν : ClassFunction ↥C.P.H0 ℂ) = rep (ν' : ClassFunction ↥C.P.H0 ℂ) := by
    intro ν ν' hL
    rcases (LamEquiv_iff C h2 hβ (ν : ClassFunction ↥C.P.H0 ℂ)
      (ν' : ClassFunction ↥C.P.H0 ℂ)).mp hL with h | h
    · rw [h]
    · rw [h]
      by_cases hε : (ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1
      · have hA : rep (ν : ClassFunction ↥C.P.H0 ℂ) =
            lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ) := by
          dsimp only [rep]; rw [if_pos hε]
        have hB : rep (lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ)) =
            lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ) := by
          dsimp only [rep]
          rw [if_neg (fun hh => ((hεlam (ν : ClassFunction ↥C.P.H0 ℂ) ν.2).mp hh) hε)]
        rw [hA, hB]
      · have hA : rep (ν : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ) := by
          dsimp only [rep]; rw [if_neg hε]
        have hB : rep (lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ)) =
            lamCF C β₂ * (lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ)) := by
          dsimp only [rep]
          rw [if_pos ((hεlam (ν : ClassFunction ↥C.P.H0 ℂ) ν.2).mpr hε)]
        rw [hA, hB, ← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
  have h17 := s02_lemma17T C χ rep hrep1 hrep2 C.t C.t_not_mem_U
  have hterm : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner χ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) -
        rep (ν : ClassFunction ↥C.P.H0 ℂ))) * (ν : ClassFunction ↥C.P.H0 ℂ) C.t =
      (if (ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1 then
        ClassFunction.inner χ (delta C β₂ (ν : ClassFunction ↥C.P.H0 ℂ)) *
          (ν : ClassFunction ↥C.P.H0 ℂ) 1 else 0) := by
    intro ν
    by_cases hε : (ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1
    · have hr : rep (ν : ClassFunction ↥C.P.H0 ℂ) =
          lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ) := by
        dsimp only [rep]; rw [if_pos hε]
      rw [if_pos hε, hr, hε]
      have hbridge : ind C ((ν : ClassFunction ↥C.P.H0 ℂ) -
          lamCF C β₂ * (ν : ClassFunction ↥C.P.H0 ℂ)) =
          delta C β₂ (ν : ClassFunction ↥C.P.H0 ℂ) := rfl
      rw [hbridge]
    · have hr : rep (ν : ClassFunction ↥C.P.H0 ℂ) = (ν : ClassFunction ↥C.P.H0 ℂ) := by
        dsimp only [rep]; rw [if_neg hε]
      rw [if_neg hε, hr, sub_self]
      simp only [ind, ClassFunction.induce_zero, ClassFunction.inner_zero_right, zero_mul]
  have hT'sub : bset' C β₂ χ ⊆ bset C f χ ∪ (fun ξ => lamCF C β₂ * ξ) '' (bset C f χ) := by
    intro ν hν
    rcases hmemd ν hν.1.1 hν.2 with h | h
    · exact Or.inl h
    · refine Or.inr ⟨lamCF C β₂ * ν, h, ?_⟩
      exact (show lamCF C β₂ * (lamCF C β₂ * ν) = ν from by
        rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf])
  have hT'fin : (bset' C β₂ χ).Finite :=
    (hSfin.union (hSfin.image _)).subset hT'sub
  haveI : Fintype ↥(bset' C β₂ χ) := hT'fin.fintype
  haveI : Fintype ↥(bset C f χ) := hSfin.fintype
  have hii : χ (C.t : G) =
      ∑ᶠ ν ∈ bset' C β₂ χ, ClassFunction.inner χ (delta C β₂ ν) * ν 1 := by
    have hG : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        (if (ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1 then
          ClassFunction.inner χ (delta C β₂ (ν : ClassFunction ↥C.P.H0 ℂ)) *
            (ν : ClassFunction ↥C.P.H0 ℂ) 1 else 0)) =
        ∑ᶠ ξ ∈ bset' C β₂ χ,
          (if ξ C.t = ξ 1 then ClassFunction.inner χ (delta C β₂ ξ) * ξ 1 else 0) := by
      refine s4L41_sum_irr_eq_finsum C (bset' C β₂ χ) (fun ξ hξ => hξ.1.1)
        (fun ν => if ν C.t = ν 1 then ClassFunction.inner χ (delta C β₂ ν) * ν 1 else 0) ?_
      intro ν hν
      by_cases hε : (ν : ClassFunction ↥C.P.H0 ℂ) C.t = (ν : ClassFunction ↥C.P.H0 ℂ) 1
      · rw [if_pos hε]
        have hδ0 : ClassFunction.inner χ (delta C β₂ (ν : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
          by_contra hδ
          exact hν ⟨⟨ν.2, hPsi _ ν.2 hε hδ, hε⟩, hδ⟩
        rw [hδ0, zero_mul]
      · rw [if_neg hε]
    rw [h17, Finset.sum_congr rfl (fun ν _ => hterm ν), hG]
    rw [finsum_mem_eq_finite_toFinset_sum _ hT'fin,
      finsum_mem_eq_finite_toFinset_sum _ hT'fin]
    refine Finset.sum_congr rfl (fun ξ hξ => ?_)
    have hm : ξ ∈ bset' C β₂ χ := (Set.Finite.mem_toFinset hT'fin).mp hξ
    rw [if_pos hm.1.2.2]
  -- 12. `|𝒮'(χ)| ∈ {1,3}`
  let ψ : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ := fun ξ =>
    if ξ C.t = ξ 1 then ξ else lamCF C β₂ * ξ
  have hψcases : ∀ ξ : ClassFunction ↥C.P.H0 ℂ, ψ ξ = ξ ∨ ψ ξ = lamCF C β₂ * ξ := by
    intro ξ
    by_cases h : ξ C.t = ξ 1
    · exact Or.inl (by dsimp only [ψ]; rw [if_pos h])
    · exact Or.inr (by dsimp only [ψ]; rw [if_neg h])
  have hψmem : ∀ ξ ∈ bset C f χ, ψ ξ ∈ bset' C β₂ χ := by
    intro ξ hξ
    have hξs : sconj C ξ = ξ := hsfixed ξ hξ
    have hξirr : IsIrreducibleCharacter ξ := hξ.1
    have hzer : ClassFunction.inner χ (f (lamCF C β₂ * ξ)) = 0 := by
      by_contra hc
      exact hP6a ξ ⟨hξ, ⟨lam_two_mul_irr C hξirr, hc⟩⟩
    by_cases hε : ξ C.t = ξ 1
    · have hψ : ψ ξ = ξ := by dsimp only [ψ]; rw [if_pos hε]
      rw [hψ]
      refine ⟨⟨hξirr, hξs, hε⟩, ?_⟩
      rw [hdel ξ hξirr, ClassFunction.inner_sub_right, hzer, sub_zero]
      exact hξ.2
    · have hψ : ψ ξ = lamCF C β₂ * ξ := by dsimp only [ψ]; rw [if_neg hε]
      rw [hψ]
      have hlamξirr : IsIrreducibleCharacter (lamCF C β₂ * ξ) := lam_two_mul_irr C hξirr
      refine ⟨⟨hlamξirr, ?_, ?_⟩, ?_⟩
      · rw [sconj_lam_two_mul C h2 hβ, hξs]
      · exact (hεlam ξ hξirr).mpr hε
      · have hlam2' : lamCF C β₂ * (lamCF C β₂ * ξ) = ξ := by
          rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
        rw [hdel (lamCF C β₂ * ξ) hlamξirr, hlam2', ClassFunction.inner_sub_right, hzer,
          zero_sub]
        exact neg_ne_zero.mpr hξ.2
  have hψinj : Set.InjOn ψ (bset C f χ) := by
    intro ξ hξ ξ' hξ' heq
    by_contra hne'
    rcases hψcases ξ with k1 | k1 <;> rcases hψcases ξ' with k2 | k2
    · exact hne' (by rw [← k1, heq, k2])
    · have hmem : lamCF C β₂ * ξ' ∈ bset C f χ := by
        rw [← k2, ← heq, k1]; exact hξ
      exact hP6a ξ' ⟨hξ', hmem⟩
    · have hmem : lamCF C β₂ * ξ ∈ bset C f χ := by
        rw [← k1, heq, k2]; exact hξ'
      exact hP6a ξ ⟨hξ, hmem⟩
    · have h3 : ξ = ξ' := by
        calc ξ = lamCF C β₂ * (lamCF C β₂ * ξ) := by
              rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
          _ = lamCF C β₂ * ψ ξ := by rw [k1]
          _ = lamCF C β₂ * ψ ξ' := by rw [heq]
          _ = lamCF C β₂ * (lamCF C β₂ * ξ') := by rw [k2]
          _ = ξ' := by rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
      exact hne' h3
  have hψsurj : ∀ ν ∈ bset' C β₂ χ, ∃ ξ ∈ bset C f χ, ψ ξ = ν := by
    intro ν hν
    rcases hmemd ν hν.1.1 hν.2 with h | h
    · refine ⟨ν, h, ?_⟩
      dsimp only [ψ]; rw [if_pos hν.1.2.2]
    · refine ⟨lamCF C β₂ * ν, h, ?_⟩
      have hε' : ¬ ((lamCF C β₂ * ν) C.t = (lamCF C β₂ * ν) 1) :=
        fun hh => ((hεlam ν hν.1.1).mp hh) hν.1.2.2
      dsimp only [ψ]
      rw [if_neg hε']
      exact (show lamCF C β₂ * (lamCF C β₂ * ν) = ν from by
        rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf])
  have hcard_eq : (bset C f χ).ncard = (bset' C β₂ χ).ncard :=
    Set.ncard_congr (fun ξ (_ : ξ ∈ bset C f χ) => ψ ξ)
      (fun ξ hξ => hψmem ξ hξ)
      (fun ξ ξ' hξ hξ' heq => hψinj hξ hξ' heq)
      (fun ν hν => by obtain ⟨ξ, hξ, hψ⟩ := hψsurj ν hν; exact ⟨ξ, hξ, hψ⟩)
  have hle3 : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hpos : 0 < (bset C f χ).ncard := (Set.ncard_pos hSfin).mpr hTne
  have hne2 : (bset C f χ).ncard ≠ 2 := by
    intro h2'
    have hlt : 1 < (bset C f χ).ncard := by omega
    obtain ⟨a, ha⟩ := hTne
    obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard hlt a
    exact s4L41_L33 D C hDC hS3 f hf χ hχ ha hb hba.symm
      (hsfixed a ha) (hsfixed b hb)
      (by rw [hn]; exact lamOrbit_ncard_eq_two C h2 hβ ha.1)
      (by rw [hn]; exact lamOrbit_ncard_eq_two C h2 hβ hb.1) h2'
  have hcardT : (bset C f χ).ncard = 1 ∨ (bset C f χ).ncard = 3 := by omega
  have hcardT' : (bset' C β₂ χ).ncard = 1 ∨ (bset' C β₂ χ).ncard = 3 := by
    rw [← hcard_eq]; exact hcardT
  -- 13. `χ(1)` is odd
  have hK : ∀ ν ∈ bset' C β₂ χ,
      ∃ k : ℤ, ClassFunction.inner χ (delta C β₂ ν) = (k : ℂ) ∧ Odd k := by
    intro ν hν
    rcases hmemd ν hν.1.1 hν.2 with h | h
    · obtain ⟨-, -, hcoef⟩ := hOS1 ν h
      have hzer0 : ClassFunction.inner χ (f (lamCF C β₂ * ν)) = 0 := by
        by_contra hc
        exact hP6a ν ⟨h, ⟨lam_two_mul_irr C hν.1.1, hc⟩⟩
      rw [hdel ν hν.1.1, ClassFunction.inner_sub_right, hzer0, sub_zero]
      rcases hcoef with hcoef | hcoef
      · exact ⟨1, by rw [hcoef]; norm_num, by norm_num⟩
      · exact ⟨-1, by rw [hcoef]; norm_num, by norm_num⟩
    · obtain ⟨-, -, hcoef⟩ := hOS1 (lamCF C β₂ * ν) h
      have hν0 : ClassFunction.inner χ (f ν) = 0 := by
        by_contra hc
        exact hP6a ν ⟨⟨hν.1.1, hc⟩, h⟩
      rw [hdel ν hν.1.1, ClassFunction.inner_sub_right, hν0, zero_sub]
      rcases hcoef with hcoef | hcoef
      · exact ⟨-1, by rw [hcoef]; norm_num, by norm_num⟩
      · exact ⟨1, by rw [hcoef]; norm_num, by norm_num⟩
  have hDg : ∀ ν ∈ bset' C β₂ χ, ∃ d : ℤ, ν 1 = (d : ℂ) ∧ Odd d := by
    intro ν hν
    obtain ⟨d, hdo, hdv⟩ := l41_s4Index_one_odd D C hDC hn hν.1
    exact ⟨d, hdv, hdo⟩
  let K : ClassFunction ↥C.P.H0 ℂ → ℤ := fun ν =>
    if h : ν ∈ bset' C β₂ χ then Classical.choose (hK ν h) else 0
  have hKspec : ∀ ν (h : ν ∈ bset' C β₂ χ),
      ClassFunction.inner χ (delta C β₂ ν) = (K ν : ℂ) ∧ Odd (K ν) := by
    intro ν h
    have hK' : K ν = Classical.choose (hK ν h) := by dsimp only [K]; rw [dif_pos h]
    rw [hK']
    exact Classical.choose_spec (hK ν h)
  let Dg : ClassFunction ↥C.P.H0 ℂ → ℤ := fun ν =>
    if h : ν ∈ bset' C β₂ χ then Classical.choose (hDg ν h) else 0
  have hDspec : ∀ ν (h : ν ∈ bset' C β₂ χ), ν 1 = (Dg ν : ℂ) ∧ Odd (Dg ν) := by
    intro ν h
    have hD' : Dg ν = Classical.choose (hDg ν h) := by dsimp only [Dg]; rw [dif_pos h]
    rw [hD']
    exact Classical.choose_spec (hDg ν h)
  have hsum_int : χ (C.t : G) =
      ((∑ ν ∈ hT'fin.toFinset, K ν * Dg ν : ℤ) : ℂ) := by
    rw [hii, finsum_mem_eq_finite_toFinset_sum _ hT'fin]
    rw [show (∑ ν ∈ hT'fin.toFinset,
          ClassFunction.inner χ (delta C β₂ ν) * ν 1) =
        ((∑ ν ∈ hT'fin.toFinset, K ν * Dg ν : ℤ) : ℂ) from by
      push_cast
      refine Finset.sum_congr rfl (fun ν hν => ?_)
      have hm : ν ∈ bset' C β₂ χ := (Set.Finite.mem_toFinset hT'fin).mp hν
      obtain ⟨hk, -⟩ := hKspec ν hm
      obtain ⟨hd, -⟩ := hDspec ν hm
      rw [hk, hd]]
  have hodd_sum : Odd (∑ ν ∈ hT'fin.toFinset, K ν * Dg ν) := by
    refine s4L41_odd_finset_sum _ _ (fun ν hν => ?_) ?_
    · have hm : ν ∈ bset' C β₂ χ := (Set.Finite.mem_toFinset hT'fin).mp hν
      exact (hKspec ν hm).2.mul (hDspec ν hm).2
    · have hc : hT'fin.toFinset.card = 1 ∨ hT'fin.toFinset.card = 3 := by
        have hthis := hcardT'
        rw [Set.ncard_eq_toFinset_card (bset' C β₂ χ) hT'fin] at hthis
        exact hthis
      rcases hc with h | h <;> rw [h] <;> norm_num
  obtain ⟨d, hd, hdo⟩ := s4L41_odd_of_odd_t C hχ ⟨_, hsum_int, hodd_sum⟩
  exact ⟨hcardT', hii, d, hdo, hd⟩

end Work.BG
