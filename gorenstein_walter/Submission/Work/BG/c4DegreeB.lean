import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.s02_bset_finite
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.thmCSec3
-- Theorem A / Theorem B in the case `D.n = 2` and BG Remark 3.5
import Submission.Work.BG.s4Decomp
import Submission.Work.BG.keySmallAsm
import Submission.Work.BG.constituentSum
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_bsValueT
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_assemblyFull
import Submission.Work.BG.s02_orbitCoherence
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lemma22Kappa
import Submission.Work.BG.kEqSmall
import Submission.Work.BG.tDerived
import Submission.Work.BG.indexOdd
import Submission.Work.BG.arithSmall
import Submission.Work.BG.bridge
import Submission.Work.BG.strongEmbed
import Submission.Work.BG.subBGDataN
import Submission.Work.BG.splitglue.Split
import Submission.Work.LEAD.Core26
-- the two character-theoretic pieces of the assembly
import Submission.Work.BG.existsMovedConstituentB
import Submission.Work.BG.degreeBoundOfMovedB

/-
# `Work.BG.c4DegreeB` — BG 1981, Lemma 3.6 with `m = 2` (`C4DegreeProp`)

`Work.GW2.C16.C4DegreeProp D C K1 K2` is the degree bound of BG 1981, p. 215 ("By Lemma 3.6,
`|χ₁(1)| > 5`"): for a simple `G` whose dihedral Sylow `2`-subgroup has order `4` (`D.n = 2`),
a signed irreducible `χ ⊥ 1_G` whose `𝒮(χ)` contains an `s`-fixed member has `|χ(1)| ≥ 5`.

The proof follows the "repaired" argument of `NOTES_c4Degree.md` §2 and is assembled from:

* `Work.BG.kNeOne_n2` (below) — BG Remark 3.5 in the case `D.n = 2`: `K = K₁ ⊓ K₂ ≠ ⊥`;
* `Work.BG.existsNotKerOfSimple` (proved in the area; reproduced below as
  `exists_mem_apply_ne_one_l`) — hence `K ⊄ ker χ`;
* `Work.BG.existsMovedConstituentB` — such a witness yields a constituent `μ` of `χ|_{H₀}`
  moved by `s` (`μ^s ∉ Λμ`);
* `bset_sconj_mem_lamOrbit_n2` (below) — Piece C: an `s`-fixed member of `𝒮(χ)` forces
  `sconj η ∈ Λη` for every `η ∈ 𝒮(χ)`;
* `Work.BG.degreeBoundOfMovedB` — the five-constituent count giving `5 ≤ |χ(1)|`.

The two self-contained helpers `l34set_of_n_two` and `bset_sconj_mem_lamOrbit_n2` are the
`D.n = 2` case of BG Lemma 3.4 and of Piece C: for `D.n = 2` the exceptional configuration
`|Λν| = 4` of the paper's proof is impossible (`Rem31ShapeProp` gives
`|Λν| ∈ {D.n, D.n/2} = {2,1}`), so clause (vi) of the Coherence Theorem 2.3 gives the value of
`f ν` at `t` directly and the rest is the argument of the paper.  (They are proved here rather
than taken from `Work.BG.lemma34Leaf`, whose proof goes through the still open exceptional
analysis `Work.BG.lemma34Exc`.)

## Theorem A and Theorem B for `D.n = 2`

The Remark 3.5 argument of the lead's design 26 (`NOTES_LEAD_gw_design26.md`,
`_design_gw/Core26.lean`) needs Theorem B for the data `D` and for its restriction to
`N_G(U)`.  Both have `n = 2` here, and for `n = 2` Theorem A uses only KEY-SMALL (the `n = 2`
key identity) and AR-SMALL — never KEY-BIG, hence never DEC-BIG — so that the derivation below
does not depend on the exceptional analysis of Lemma 3.4 at all.  `Work.GW2.C26` supplies the
group-theoretic steps (`oneClass_normalizer`, `false_of_normalizer_index_five`, …).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## The character-kernel step -/

/-- An irreducible character has nonzero degree. -/
private theorem irr_apply_one_ne_zero_l {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) : φ 1 ≠ 0 := by
  obtain ⟨n, hpos, hval, _⟩ := hφ.exists_natDegree_charValue_one_dvd_card (G := G)
  rw [hval]
  exact_mod_cast hpos.ne'

/-- A signed irreducible character has nonzero value at `1`. -/
private theorem pmIrr_apply_one_ne_zero_l {χ : ClassFunction G ℂ} (h : IsPmIrr χ) :
    χ 1 ≠ 0 := by
  rcases h with h | h
  · exact irr_apply_one_ne_zero_l h
  · have hh := irr_apply_one_ne_zero_l h
    have : -χ 1 ≠ 0 := hh
    exact neg_ne_zero.mp this

/-- A class function constant with value `χ 1` has inner product `χ 1` with the trivial
character. -/
private theorem inner_trivialClassFunction_of_const_l (χ : ClassFunction G ℂ)
    (h : ∀ g, χ g = χ 1) :
    ClassFunction.inner χ (trivialClassFunction G) = χ 1 := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum]
  have hsum : ClassFunction.innerSum χ (trivialClassFunction G) = (Nat.card G : ℂ) * χ 1 := by
    simp only [ClassFunction.innerSum, trivialClassFunction_apply, star_one, mul_one]
    rw [Finset.sum_congr rfl (fun g _ => h g)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hsum, ← mul_assoc, invOf_mul_self, one_mul]

/-- An irreducible character of a finite simple group that is constant `= φ 1` on a nontrivial
subgroup is constant on all of `G`. -/
private theorem irr_const_of_const_on_subgroup_l (K : Subgroup G) (φ : ClassFunction G ℂ)
    (hφ : IsIrreducibleCharacter φ) (hKconst : ∀ k ∈ K, φ k = φ 1) (hKne : K ≠ ⊥)
    (hsimple : IsSimpleGroup G) : ∀ g : G, φ g = φ 1 := by
  obtain ⟨V, _, _, _, ρ, hirr, hchar⟩ := hφ
  -- `K` lies in the kernel of the witnessing representation.
  have hNle : K ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hc : ρ.character k = ρ.character 1 := by
      rw [← congrFun hchar k, ← congrFun hchar 1, hKconst k hk]
    have hid : ρ k = LinearMap.id := rep_eq_id_of_character_eq_one ρ hc
    rw [hid]
    rfl
  -- simplicity: the (normal) kernel is `⊥` or `⊤`; `K ≠ ⊥` rules out `⊥`.
  have hNtop : (ρ.ker : Subgroup G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker) with h | h
    · exact absurd (le_bot_iff.mp (h ▸ hNle)) hKne
    · exact h
  intro g
  have hg : g ∈ ρ.ker := by rw [hNtop]; trivial
  have hg' : ρ g = (1 : V →ₗ[ℂ] V) := MonoidHom.mem_ker.mp hg
  have hchar_eq : ρ.character g = ρ.character 1 := by
    simp only [Representation.character]
    rw [hg', show ρ (1 : G) = (1 : V →ₗ[ℂ] V) from map_one ρ]
  rw [congrFun hchar g, congrFun hchar 1, hchar_eq]

/-- **`χ` is not constant on `K`.**  If `K ≠ ⊥` in a simple group and `χ ∈ ±Irr(G)` is
orthogonal to the trivial character, then `χ x ≠ χ 1` for some `x ∈ K`. -/
private theorem exists_mem_apply_ne_one_l (K : Subgroup G) (χ : ClassFunction G ℂ)
    (hKne : K ≠ ⊥) (hsimple : IsSimpleGroup G) (hpm : IsPmIrr χ)
    (horth : ClassFunction.inner χ (trivialClassFunction G) = 0) :
    ∃ k ∈ K, χ k ≠ χ 1 := by
  by_contra hcon
  push Not at hcon
  have hdeg : χ 1 ≠ 0 := pmIrr_apply_one_ne_zero_l hpm
  have hconstχ : ∀ g : G, χ g = χ 1 := by
    rcases hpm with hirr | hirr
    · exact irr_const_of_const_on_subgroup_l K χ hirr hcon hKne hsimple
    · have hc : ∀ k ∈ K, (-χ) k = (-χ) 1 := by
        intro k hk
        rw [ClassFunction.neg_apply, ClassFunction.neg_apply, hcon k hk]
      intro g
      have h := irr_const_of_const_on_subgroup_l K (-χ) hirr hc hKne hsimple g
      simpa using h
  have hinner_eq : ClassFunction.inner χ (trivialClassFunction G) = χ 1 :=
    inner_trivialClassFunction_of_const_l χ hconstχ
  rw [hinner_eq] at horth
  exact hdeg horth

/-! ## BG Lemma 3.4 and Piece C for `D.n = 2` -/

/-- **Norm-one `ℤ[Irr G]` elements are signed irreducibles.**  If `φ ∈ ℤ[Irr G]` has norm one
and a signed irreducible `χ` is not orthogonal to `φ`, then `φ = ±χ`. -/
private theorem l34n2_eq_pm_of_inner_ne_zero {φ χ : ClassFunction G ℂ}
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

/-- **BG Lemma 3.4 for `D.n = 2`.**  In the case `|S| = 4` the exceptional configuration
`|Λν| = 4` is impossible, so clause (vi) of the Coherence Theorem 2.3 gives the value of `f ν`
at `t` and the argument of the paper's Lemma 3.4 yields `𝒮(χ) = {ν, ν^s}`. -/
theorem l34set_of_n_two (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Compat D C) (hn2 : D.n = 2) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hdisj : sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n) :
    bset C f χ = {ν, sconj C ν} ∧ f ν (C.t : G) = 2 * ν C.t := by
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
    rcases l34n2_eq_pm_of_inner_ne_zero hZIfν hnormf1 hχ hνne0 with h | h
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
  -- the value at `t`: the exceptional configuration is impossible for `D.n = 2`
  have hval : f ν (C.t : G) = 2 * ν C.t := by
    refine hvi hne ?_
    rintro ⟨h4, -⟩
    obtain ⟨a, -, hcase⟩ := rem31Shape D C hC hS3 ν hνirr
    rcases hcase with ⟨-, hnc⟩ | ⟨a₂, -, -, -, hnc⟩ <;> omega
  -- `𝒮(χ) = {ν, ν^s}`
  have hcard : (bset C f χ).ncard ≤ 3 := thm32 D C hC hS3 f hf χ hχ
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

/-- **Piece C for `D.n = 2`.**  If `𝒮(χ)` contains an `s`-fixed member, then every member
`η ∈ 𝒮(χ)` is `Λ`-conjugate to its `s`-conjugate: otherwise the `D.n = 2` case of Lemma 3.4
(`l34set_of_n_two`) forces `𝒮(χ) = {η, η^s}`, a set containing no `s`-fixed character. -/
theorem bset_sconj_mem_lamOrbit_n2 (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Compat D C) (hn2 : D.n = 2) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hfix : ∃ ν₀ ∈ bset C f χ, sconj C ν₀ = ν₀) :
    ∀ η ∈ bset C f χ, sconj C η ∈ lamOrbit C η := by
  intro η hη
  by_contra hconj
  by_cases hfixη : sconj C η = η
  · exact hconj (by rw [hfixη]; exact mem_lamOrbit_self C η)
  · obtain ⟨hset, -⟩ := l34set_of_n_two D C hC hn2 hS3 f hf χ hχ η hη hfixη (Or.inl hconj)
    obtain ⟨ν₀, hν₀, hν₀fix⟩ := hfix
    have hmem : ν₀ ∈ ({η, sconj C η} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
      rw [← hset]; exact hν₀
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hfixη (by rw [← h]; exact hν₀fix)
    · have h2 : sconj C (sconj C η) = sconj C η := by rw [← h]; exact hν₀fix
      rw [sconj_sconj] at h2
      exact hfixη h2.symm

/-! ## Theorem A, Theorem B and Remark 3.5 for `D.n = 2` -/

/-- **BG Coherence Theorem 2.3** for every §2 context (A-1 composed with A-2), as in
`Work.BG.Final.coherenceAll`. -/
theorem coherence23Prop_c4 (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Coherence23Prop C :=
  s02_assemblyFull C (s02_gram C) (s02_bsValueT C)
    (s02_assemblyCore C (sconjLam C) (s02_orbitCoherence C))

/-- **KEY-SMALL** (BG §4, `|S| = 4`), as in `Work.BG.Final.keySmall_of`. -/
theorem keySmallProp_c4 : KeySmallProp :=
  keySmallAsm (bridge SplitGlue.centralizerSplitProp) constituentSum
    (fun (G : Type) [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
      [Fintype (IrreducibleCharacter G)] (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] =>
        ⟨coherence23Prop_c4 C, s02_indDiff C, s4Decomp D C, lemma22Kappa D C⟩)
    kEqSmall tDerived

/-- **Theorem A in the case `D.n = 2`.**  Only KEY-SMALL and AR-SMALL are needed (the `n = 2`
branch of `thmA_of_leaves`); KEY-BIG, and hence DEC-BIG and the exceptional analysis of
Lemma 3.4, are not used. -/
theorem thmA_n2 : ∀ (G : Type) [Group G] [Finite G] (D : BGData G), D.n = 2 →
    D.H.index < 3 * (2 * D.k ^ 2) ∧ 2 * D.k ^ 2 < 3 * D.H.index := by
  intro G _ _ D hn
  obtain ⟨hodd, -⟩ := indexOdd G D
  obtain ⟨a, b, c, ha, hb, hc, ha', hb', hc', hsum, hid⟩ := keySmallProp_c4 G D hn
  exact arithSmall D.H.index D.k a b c hodd ha hb hc ha' hb' hc' hsum hid

/-- **Theorem B in the case `D.n = 2`** (BG p. 201, "Theorem B is an easy consequence of
Theorem A"): a proper `G₁ ⊇ H` with one class of involutions has index `5`.  Theorem A applied
to `G` and to the restricted data on `G₁` gives `|G : G₁| < 9`, and strong embedding gives
`4 ∣ |G : G₁| - 1`. -/
theorem thmB_n2 {G : Type} [Group G] [Finite G] (D : BGData G) (hn : D.n = 2)
    (G1 : Subgroup G) (hne : G1 ≠ ⊤) (hle : D.H ≤ G1)
    (hcl : ∀ x y : G, x ∈ G1 → y ∈ G1 → orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ G1, g * x * g⁻¹ = y) :
    G1.index = 5 := by
  obtain ⟨D', hD'n, hidx, hk⟩ := subBGDataN D G1 hle hcl
  have h1 : D.H.index < 3 * (2 * D.k ^ 2) := (thmA_n2 G D hn).1
  have h2 : 2 * D'.k ^ 2 < 3 * D'.H.index := (thmA_n2 ↥G1 D' (hD'n.trans hn)).2
  rw [hidx, hk] at h2
  have hmul : D.H.relIndex G1 * G1.index = D.H.index := Subgroup.relIndex_mul_index hle
  have hHidx : D.H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : 0 < D.H.relIndex G1 := by
    rcases Nat.eq_zero_or_pos (D.H.relIndex G1) with h | h
    · rw [h, zero_mul] at hmul; exact absurd hmul.symm hHidx
    · exact h
  have hlt : D.H.relIndex G1 * G1.index < D.H.relIndex G1 * 9 := by
    rw [hmul]; omega
  have h9 : G1.index < 9 := Nat.lt_of_mul_lt_mul_left hlt
  have h0 : G1.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1' : G1.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hd := strongEmbed G D G1 hne hle hcl
  omega

/-- **BG Remark 3.5 in the case `D.n = 2`**: under the hypotheses of Theorem C with `G` simple,
`K = K₁ ⊓ K₂ ≠ ⊥`.  This is the argument of the lead's design 26 (G8), with Theorem B used only
in its `n = 2` form `thmB_n2`; the group-theoretic steps are `Work.GW2.C26`. -/
theorem kNeOne_n2 : ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G),
    D.n = 2 → ThmCHyps D K1 K2 → IsSimpleGroup G → K1 ⊓ K2 ≠ ⊥ := by
  intro G _instG _instFin D K1 K2 hn hHyps hsimple
  obtain ⟨-, -, -, -, hBne, hfrob⟩ := hHyps
  by_contra hK
  have hKbot : K1 ⊓ K2 = ⊥ := by simpa using hK
  -- the Frobenius clause forces `U = B`
  have hUB : D.U = D.B := by
    by_contra hne
    have hne' : D.U ≠ D.B ⊔ (K1 ⊓ K2) := by rw [hKbot]; simpa using hne
    have hF := hfrob hne'
    rw [hKbot] at hF
    exact hF.2.2.2.2.1 rfl
  have hBne_bot : D.B ≠ ⊥ := by
    intro h
    exact hBne (by rw [h]; simp)
  have hUne : D.U ≠ ⊥ := hUB ▸ hBne_bot
  have hUpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
    rw [show D.U = Work.GW2.oddCoreIn D.H from rfl, oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
  have hUodd : Odd (Nat.card ↥D.U) := (odd_card_iff_isPiSubgroup_ne_two D.U).mpr hUpi
  -- `S` centralizes `U`
  have hcent : D.U ≤ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
    rw [hUB, B_eq_inf_centralizer_S D]; exact inf_le_left
  -- `H = U ⊔ S` (`CentralizerSplitProp`)
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (S_le_H D hx) D.t (Set.mem_singleton D.t)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem)
      D.t_order hcentr
  set N := Subgroup.normalizer (D.U : Set G) with hN
  have hSN : (D.S : Subgroup G) ≤ N := Work.GW2.C26.le_normalizer_of_le_centralizer hcent
  have hHN : D.H ≤ N := hUS ▸ sup_le Subgroup.le_normalizer hSN
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hnorm : D.U.Normal := ⟨fun u hu g => by
      have hg : g ∈ N := htop ▸ Subgroup.mem_top g
      exact (mem_normalizer_iff.mp hg u).mp hu⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D.U with h | h
    · exact hUne h
    · have hGodd : Odd (Nat.card G) := by
        rw [← Subgroup.card_top (G := G), ← h]; exact hUodd
      have hcard : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
        obtain ⟨e⟩ := D.dih
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hdvd : 2 ∣ Nat.card G :=
        (Dvd.intro _ hcard.symm).trans (Subgroup.card_subgroup_dvd_card _)
      exact (Nat.not_even_iff_odd.mpr hGodd) (even_iff_two_dvd.mpr hdvd)
  have h5 : N.index = 5 :=
    thmB_n2 D hn N hNtop hHN (Work.GW2.C26.oneClass_normalizer D hUS hcent hUodd)
  exact Work.GW2.C26.false_of_normalizer_index_five hsimple D.U hUodd hUne h5

/- **`C4DegreeProp`** (BG 1981, Lemma 3.6 with `m = 2`, p. 215): in a simple group whose
dihedral Sylow `2`-subgroup has order `4`, every `χ ∈ ±Irr(G)` with `χ ⊥ 1_G` whose `𝒮(χ)`
contains an `s`-fixed member has `|χ(1)| ≥ 5`. -/
open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c4DegreeB {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.C4DegreeProp D C K1 K2 := by
  intro hComp hHyps hSimp hn2 f hf χ hχ hbot hsfixed
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- §3 holds, by G6 (`ThmCSec3Prop` applied to the hypotheses of Theorem C)
  have hS3 : Sec3Hyp D :=
    (thmCSec3 G D K1 K2 hHyps.1 hHyps.2.1 hHyps.2.2.1 hHyps.2.2.2.2.1).1
  -- `K = K₁ ⊓ K₂ ≠ ⊥` (BG Remark 3.5, in the case `D.n = 2`)
  have hKne : K1 ⊓ K2 ≠ ⊥ := kNeOne_n2 G D K1 K2 hn2 hHyps hSimp
  -- `χ` is not constant on `K`, so `χ|_{H₀}` has a constituent moved by `s`
  have hKker : ∃ x ∈ K1 ⊓ K2, χ x ≠ χ 1 :=
    exists_mem_apply_ne_one_l (K1 ⊓ K2) χ hKne hSimp hχ hbot
  have hmoved : ∃ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ ∧
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) μ ≠ 0 ∧
      sconj C μ ∉ lamOrbit C μ :=
    existsMovedConstituentB D C K1 K2 f χ hComp hHyps hSimp hn2 hf hχ hbot hKker
  -- Piece C: every member of `𝒮(χ)` is `Λ`-conjugate to its `s`-conjugate
  have hcoll : ∀ η ∈ bset C f χ, sconj C η ∈ lamOrbit C η :=
    bset_sconj_mem_lamOrbit_n2 D C hComp hn2 hS3 f hf χ hχ hsfixed
  -- the five-constituent count
  exact degreeBoundOfMovedB D C f χ hComp hn2 hS3 hf hχ hbot hsfixed hcoll hmoved

end Work.BG
