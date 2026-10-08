import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Lambda
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralValue
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible

/-!
# Area BG: the `Λ`-orbit of the `s`-conjugate inside `𝒮(χ)`

Bender–Glauberman 1981, p. 210, fact (2): if `𝒮(χ) = bset C f χ` contains an `s`-fixed
character, then every `ν ∈ 𝒮(χ)` has `ν^s ∈ Λν`.

Route (the paper cites Lemmas 3.3/3.4; here we run Lemma 3.4's argument directly, avoiding the
exceptional-configuration leaf):

* if `ν^s ∉ Λν` then `(Λν)^s ≠ Λν`, so clause (vi) of the coherence theorem applies and
  `f ν (t) = 2 ν(t)`;
* `f ν ∈ ℤ[Irr G]` has norm `1`, so `f ν = ±χ` and hence `𝒮(χ) = 𝒮(f ν)`;
* if `𝒮(f ν)` contained a third character `ξ` besides `ν, ν^s`, then Theorem 3.2 would give
  `𝒮(f ν) = {ν, ν^s, ξ}` and Lemma 2.4 for `f ν` at `t` would read
  `f ν(t) = ν(t) + ν^s(t) + (f ν, f ξ)·ξ(t) = 2ν(t) + (f ν, f ξ)·ξ(t)`, contradicting `(vi)`
  since `(f ν, f ξ) ≠ 0` and `ξ(t) ≠ 0`.  So `𝒮(f ν) = {ν, ν^s}` — contradicting the given
  `s`-fixed member of `𝒮(χ)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- Norm-one `ℤ[Irr G]` elements are signed irreducibles (local copy of
`Work.BG.l34_eq_pm_of_inner_ne_zero`, kept here so that this file does not depend on
`lemma34Leaf.lean`). -/
theorem l34eqpm {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ χ : ClassFunction G ℂ}
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


/-- **BG 1981, p. 210, (2).**  If `𝒮(χ)` contains an `s`-fixed character `ν₀`, then the
`s`-conjugate of every member of `𝒮(χ)` lies in its own `Λ`-orbit. -/
theorem sconj_mem_lamOrbit_of_fixed (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (hC : Compat D C) (hS3 : Sec3Hyp D) (hf : IsCoherent C f) (hχ : IsPmIrr χ)
    {ν₀ : ClassFunction ↥C.P.H0 ℂ} (hν₀mem : ν₀ ∈ bset C f χ) (hν₀fix : sconj C ν₀ = ν₀)
    {η : ClassFunction ↥C.P.H0 ℂ} (hηmem : η ∈ bset C f χ) :
    sconj C η ∈ lamOrbit C η := by
  classical
  by_contra hconj
  have hηirr : IsIrreducibleCharacter η := hηmem.1
  have hfix : sconj C η ≠ η := by
    intro h
    refine hconj ?_
    rw [h]
    exact s02c_LamEquiv_refl C η
  -- coherence at `η`
  have hkey : η ∈ orbitKey C η := Or.inl (s02c_LamEquiv_refl C η)
  have hG := (hf.1 η hηirr) η hkey η hkey hηirr hηirr
  have hnorm : ClassFunction.inner (f η) (f η) = 1 := by
    have h := hG.2.2.1
    rw [if_neg hfix] at h
    exact h
  have hexc : ¬ ((lamOrbit C η).ncard = 4 ∧ sconj C '' lamOrbit C η = lamOrbit C η) := by
    rintro ⟨-, himg⟩
    refine hconj ?_
    rw [← himg]
    exact Set.mem_image_of_mem (sconj C) (s02c_LamEquiv_refl C η)
  have hv : f η (C.t : G) = 2 * η C.t := hG.2.2.2.2.2 hfix hexc
  -- `f η ∈ ±Irr(G)`
  have hpm : IsPmIrr (f η) := by
    rcases l34eqpm hG.1 hnorm hχ hηmem.2 with h | h
    · rw [h]; exact hχ
    · rw [h]
      rcases hχ with h1 | h1
      · exact Or.inr (by rwa [neg_neg])
      · exact Or.inl h1
  have hbset : bset C f (f η) = bset C f χ := by
    rcases l34eqpm hG.1 hnorm hχ hηmem.2 with h | h
    · rw [h]
    · ext μ
      simp only [bset, Set.mem_setOf_eq]
      rw [h]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro h0
        exact h2 (by rw [ClassFunction.inner_neg_left, h0, neg_zero])
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [ClassFunction.inner_neg_left]
        exact neg_ne_zero.mpr h2
  -- the three characters `η`, `η^s`, `ν₀`
  have hη' : η ∈ bset C f (f η) := by rw [hbset]; exact hηmem
  have hsη' : sconj C η ∈ bset C f (f η) := by
    rw [hbset]
    exact ((bset_orbit_struct C f hf χ hχ).1 η hηmem).1
  have hν₀' : ν₀ ∈ bset C f (f η) := by rw [hbset]; exact hν₀mem
  have hν₀ne1 : ν₀ ≠ η := by
    intro h
    apply hfix
    rw [← h, hν₀fix]
  have hν₀ne2 : ν₀ ≠ sconj C η := by
    intro h
    apply hν₀ne1
    calc ν₀ = sconj C ν₀ := hν₀fix.symm
      _ = sconj C (sconj C η) := by rw [h]
      _ = η := sconj_sconj C η
  have hsub : ({η, sconj C η, ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f (f η) := by
    intro μ hμ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl | rfl
    · exact hη'
    · exact hsη'
    · exact hν₀'
  have hcard3 : ({η, sconj C η, ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm hfix, Ne.symm hν₀ne1⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]
          exact fun h => hν₀ne2 h.symm),
        Set.ncard_singleton]
  have hb3 : (bset C f (f η)).ncard ≤ 3 :=
    thm32 D C hC hS3 f hf (f η) hpm
  have hle : (bset C f (f η)).ncard ≤
      ({η, sconj C η, ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := by
    rw [hcard3]; exact hb3
  have hseteq : bset C f (f η) = ({η, sconj C η, ν₀} : Set (ClassFunction ↥C.P.H0 ℂ)) :=
    (Set.eq_of_subset_of_ncard_le hsub hle (s02_bset_finite C f (f η))).symm
  -- Lemma 2.4 for `f η`
  obtain ⟨hbfin, hvalform, -⟩ := lemma24 C f hf (f η) hpm
  have hvalt : f η (C.t : G) =
      ∑ᶠ μ ∈ bset C f (f η), ClassFunction.inner (f η) (f μ) * μ C.t :=
    hvalform C.t C.t_not_mem_U
  have hftriple : hbfin.toFinset = ({η, sconj C η, ν₀} : Finset (ClassFunction ↥C.P.H0 ℂ)) := by
    ext μ
    rw [Set.Finite.mem_toFinset, hseteq]
    simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hsplit : (∑ᶠ μ ∈ bset C f (f η), ClassFunction.inner (f η) (f μ) * μ C.t)
      = ClassFunction.inner (f η) (f η) * η C.t
        + ClassFunction.inner (f η) (f (sconj C η)) * (sconj C η) C.t
        + ClassFunction.inner (f η) (f ν₀) * ν₀ C.t := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hbfin, hftriple,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hfix, Ne.symm hν₀ne1⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact fun h => hν₀ne2 h.symm),
      Finset.sum_singleton]
    ring_nf
  -- the contradiction
  have hcoef : ClassFunction.inner (f η) (f ν₀) * ν₀ C.t ≠ 0 := by
    refine mul_ne_zero hν₀'.2 ?_
    rcases (centralValue C ν₀ hν₀'.1).1 with h | h
    · rw [h]; exact (centralValue C ν₀ hν₀'.1).2
    · rw [h]; exact neg_ne_zero.mpr (centralValue C ν₀ hν₀'.1).2
  have hzero : ClassFunction.inner (f η) (f ν₀) * ν₀ C.t = 0 := by
    have h := hvalt
    rw [hsplit, hG.2.1, hnorm, sconj_apply_t C η, hv] at h
    ring_nf at h
    have h2 : η C.t * 2 - η C.t * 2 = (f η).inner (f ν₀) * ν₀ C.t := by
      nth_rewrite 1 [h]
      ring
    rw [sub_self] at h2
    exact h2.symm
  exact hcoef hzero

end Work.BG
