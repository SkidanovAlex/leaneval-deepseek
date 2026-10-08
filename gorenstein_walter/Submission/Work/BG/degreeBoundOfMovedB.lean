/-
# Area BG: the degree bound for a moved character (Bender–Glauberman 1981, Lemma 3.6, `m = 2`)

Bender–Glauberman 1981, §3/§4.  Let `C` be the §2 context attached to a `BGData D` with
`D.n = 2` (so the Sylow `2`-subgroup has order `4` and `Λ = {1, λ₂}`), `f` a coherent map
(Theorem 2.3) and `χ ∈ ±Irr(G)` orthogonal to the trivial character.

**Claim.**  If `𝒮(χ) = bset C f χ` contains an `s`-fixed character `ν₀`, *every* member of
`𝒮(χ)` is `Λ`-conjugate to its `s`-conjugate (this is BG Lemma 3.4 / "Piece C"; here it is
supplied as a hypothesis), and `χ|_{H₀}` has a constituent `μ` which is *moved* by `s`
(`μ^s ∉ Λμ`), then `5 ≤ |χ(1)|`.

The proof exhibits five distinct irreducible constituents of `χ|_{H₀}`, each with multiplicity
`≥ 1`:

* `μ`, `λ₂μ`, `μ^s`, `λ₂μ^s`: all four have multiplicity `(χ|_{H₀}, μ) = e_μ ≥ 1` — the two
  `s`-conjugates by `s`-invariance of `χ|_{H₀}`, and `λ₂μ` because `μ ∉ 𝒮(χ)` (the hypothesis
  on `𝒮(χ)` forbids a moved member next to `ν₀`), so that coherence + Frobenius reciprocity
  turn `⟨χ, f μ - f λ₂μ⟩ = 0` into `e_μ = e_{λ₂μ}`.
* one of `ν₀`, `λ₂ν₀`:  `λ₂ν₀ ∉ 𝒮(χ)` (Lemma 2.1 / `bset_orbit_struct`), so coherence gives
  `e_{ν₀} - e_{λ₂ν₀} = ±1`, and one of the two has multiplicity `≥ 1`.

The counting `χ(1) ≥ 5` is then the pure lemma `card_le_re_of_constituents`.

The supporting steps are proved in sibling modules: `Work.BG.inner_restrict_sconj`
(`s`-invariance of the restriction multiplicities), `Work.BG.inner_coherence_coeff`
(coherence + Frobenius reciprocity), `Work.BG.card_le_re_of_constituents` (the counting) and
`Work.BG.fourBlock_distinct` (`λ₂`-orbit bookkeeping).
-/
import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.card_le_re_of_constituents
import Submission.Work.BG.inner_restrict_sconj
import Submission.Work.BG.inner_coherence_coeff
import Submission.Work.BG.fourBlock_distinct
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.L41Aux

namespace Work.BG

set_option maxHeartbeats 1000000

open OddOrder.RepresentationTheory

/-! ## Preliminaries -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- `lamCF C 1` is the trivial class function of `H₀`. -/
private theorem lamCF_one_eq_trivial_local {G : Type} [Group G] [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) :
    lamCF C (1 : quotGroup C.P →* ℂˣ) = trivialClassFunction ↥C.P.H0 := by
  rw [lamCF_one]
  ext h
  simp [linearClassFunction_apply, trivialClassFunction_apply]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- The restriction of a genuine character is a genuine character. -/
private theorem isCharacter_restrict_local {K : Type} [Group K] [Finite K]
    {φ : ClassFunction K ℂ} (hφ : IsCharacter φ) (H : Subgroup K) :
    IsCharacter (ClassFunction.restrict H φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  have hφeq : φ = repCharacterClassFunction ρ :=
    ClassFunction.ext fun g => by rw [repCharacterClassFunction_apply]; exact congrFun hρ g
  rw [hφeq, ClassFunction.restrict_repCharacterClassFunction H ρ]
  exact repCharacterClassFunction_isCharacter (ρ.comp H.subtype)

/-! ## The main case: `χ` irreducible -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
private theorem degreeBoundOfMovedB_irr {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (hC : Compat D C) (hn : D.n = 2) (hS3 : Sec3Hyp D) (hf : IsCoherent C f)
    (hχ : IsIrreducibleCharacter χ)
    (h1 : ClassFunction.inner χ (trivialClassFunction G) = 0)
    (hA : ∃ ν : ClassFunction ↥C.P.H0 ℂ, ν ∈ bset C f χ ∧ sconj C ν = ν)
    (hcoll : ∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν)
    (hB : ∃ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ ∧
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) μ ≠ 0 ∧
        sconj C μ ∉ lamOrbit C μ) :
    ∃ d : ℤ, χ 1 = d ∧ 5 ≤ |d| := by
  classical
  -- ## the `λ₂`-data
  have hq2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hC hn
  obtain ⟨β₂, hβ₂t⟩ := s02_exists_lamCF_apply_t_eq_neg_one C
  have hβ₂ : β₂ ≠ 1 := by
    intro h
    rw [h, lamCF_one_eq_trivial_local, trivialClassFunction_apply] at hβ₂t
    norm_num at hβ₂t
  have hsq : lamCF C β₂ * lamCF C β₂ = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) :=
    lamCF_two_mul_self C hq2
  have hcancel : ∀ x : ClassFunction ↥C.P.H0 ℂ, lamCF C β₂ * (lamCF C β₂ * x) = x :=
    fun x => by rw [← mul_assoc_cf, hsq, one_mul_cf]
  -- ## the hypotheses
  obtain ⟨ν₀, hν₀mem₀, hν₀fix⟩ := hA
  have hν₀mem : ν₀ ∈ bset C f χ := hν₀mem₀
  obtain ⟨hν₀irr, -⟩ := hν₀mem₀
  obtain ⟨μ, hμirr, hμmult, hμmoved⟩ := hB
  -- ## Piece C, supplied as a hypothesis
  have hpiece : ∀ η : ClassFunction ↥C.P.H0 ℂ, η ∈ bset C f χ → sconj C η ∈ lamOrbit C η :=
    hcoll
  have hbs := bset_orbit_struct C f hf χ (Or.inl hχ)
  -- ## `λ₂`-orbit bookkeeping
  have hdist := fourBlock_distinct C hq2 (β₂ := β₂) (ν₀ := ν₀) (μ := μ)
    hβ₂ hν₀irr hν₀fix hμirr hμmoved
  obtain ⟨hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9, hD10, hD11, hD12, hD13, hD14,
    hD15, hD16, hD17, hD18, hD19⟩ := hdist
  -- ## non-membership in `𝒮(χ)`
  have hμnot : μ ∉ bset C f χ := fun h => hμmoved (hpiece μ h)
  have hμval : ClassFunction.inner χ (f μ) = 0 := by
    by_contra hne
    apply hμnot
    show IsIrreducibleCharacter μ ∧ ClassFunction.inner χ (f μ) ≠ 0
    exact ⟨hμirr, hne⟩
  have h2μnot : lamCF C β₂ * μ ∉ bset C f χ := by
    intro hmem
    apply hμmoved
    have h1' := hpiece (lamCF C β₂ * μ) hmem
    rw [sconj_lam_two_mul C hq2 hβ₂ μ,
      lamOrbit_eq C hq2 hβ₂ (lamCF C β₂ * μ), Set.mem_ofPred_eq] at h1'
    rcases h1' with h' | h'
    · have h'' : sconj C μ = μ := by
        have h2' := congrArg (fun z => lamCF C β₂ * z) h'
        rw [hcancel] at h2'
        rw [hcancel] at h2'
        exact h2'
      rw [h'']
      exact mem_lamOrbit_self C μ
    · have h'' : sconj C μ = lamCF C β₂ * μ := by
        have h2' := congrArg (fun z => lamCF C β₂ * z) h'
        rw [hcancel] at h2'
        rw [hcancel] at h2'
        exact h2'
      exact ⟨β₂, h''⟩
  have h2μval : ClassFunction.inner χ (f (lamCF C β₂ * μ)) = 0 := by
    by_contra hne
    apply h2μnot
    show IsIrreducibleCharacter (lamCF C β₂ * μ) ∧
      ClassFunction.inner χ (f (lamCF C β₂ * μ)) ≠ 0
    exact ⟨hD16, hne⟩
  have h2ν₀not : lamCF C β₂ * ν₀ ∉ bset C f χ := by
    intro hmem
    have h' := hbs.2 ν₀ hν₀mem (lamCF C β₂ * ν₀) hmem
      (⟨β₂, rfl⟩ : LamEquiv C ν₀ (lamCF C β₂ * ν₀))
      (lam_two_mul_ne_self C hq2 hβ₂ hν₀irr)
    rw [hν₀fix] at h'
    exact lam_two_mul_ne_self C hq2 hβ₂ hν₀irr h'
  have h2ν₀val : ClassFunction.inner χ (f (lamCF C β₂ * ν₀)) = 0 := by
    by_contra hne
    apply h2ν₀not
    show IsIrreducibleCharacter (lamCF C β₂ * ν₀) ∧
      ClassFunction.inner χ (f (lamCF C β₂ * ν₀)) ≠ 0
    exact ⟨hD19, hne⟩
  have hν₀val : ClassFunction.inner χ (f ν₀) = 1 ∨ ClassFunction.inner χ (f ν₀) = -1 :=
    (hbs.1 ν₀ hν₀mem).2.2
  -- ## restriction multiplicities are natural numbers
  have hμnat : ∃ k : ℕ,
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) μ = (k : ℂ) :=
    ClassFunction.restrictionMultiplicity_natCast (H := C.P.H0) hχ hμirr
  obtain ⟨kμ, hkμ⟩ := hμnat
  have hkμ1 : 1 ≤ kμ := by
    by_contra hlt
    have h0 : kμ = 0 := by omega
    exact hμmult (by rw [hkμ, h0]; norm_num)
  -- ## the multiplicity of `λ₂μ`
  have hinner2 : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (lamCF C β₂ * μ) =
      (kμ : ℂ) := by
    have hcc := inner_coherence_coeff (ν := μ) (η := lamCF C β₂ * μ) C f hf χ hμirr hD16
      (⟨β₂, rfl⟩ : LamEquiv C μ (lamCF C β₂ * μ))
    have hzero : ClassFunction.inner χ (f μ - f (lamCF C β₂ * μ)) = 0 := by
      rw [ClassFunction.inner_sub_right, hμval, h2μval, sub_zero]
    rw [hzero, ClassFunction.inner_sub_right, hkμ] at hcc
    exact (sub_eq_zero.mp hcc.symm).symm
  have hμs : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (sconj C μ) = (kμ : ℂ) := by
    rw [inner_restrict_sconj C χ μ, hkμ]
  have h2μs : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
      (sconj C (lamCF C β₂ * μ)) = (kμ : ℂ) := by
    rw [inner_restrict_sconj C χ (lamCF C β₂ * μ), hinner2]
  have h4val : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
      (lamCF C β₂ * sconj C μ) = (kμ : ℂ) := by
    rw [← sconj_lam_two_mul C hq2 hβ₂ μ]
    exact h2μs
  -- ## the fifth character
  have hν₀nat : ∃ k : ℕ, ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν₀ = (k : ℂ) :=
    ClassFunction.restrictionMultiplicity_natCast (H := C.P.H0) hχ hν₀irr
  obtain ⟨k₀, hk₀⟩ := hν₀nat
  have h2ν₀nat : ∃ k : ℕ,
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (lamCF C β₂ * ν₀) = (k : ℂ) :=
    ClassFunction.restrictionMultiplicity_natCast (H := C.P.H0) hχ hD19
  obtain ⟨k₁, hk₁⟩ := h2ν₀nat
  have hval5 : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (ν₀ - lamCF C β₂ * ν₀) = 1 ∨
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (ν₀ - lamCF C β₂ * ν₀) = -1 := by
    have hL : ClassFunction.inner χ (f ν₀ - f (lamCF C β₂ * ν₀)) = 1 ∨
        ClassFunction.inner χ (f ν₀ - f (lamCF C β₂ * ν₀)) = -1 := by
      rw [ClassFunction.inner_sub_right, h2ν₀val, sub_zero]
      exact hν₀val
    have hcc := inner_coherence_coeff (ν := ν₀) (η := lamCF C β₂ * ν₀) C f hf χ hν₀irr hD19
      (⟨β₂, rfl⟩ : LamEquiv C ν₀ (lamCF C β₂ * ν₀))
    rwa [hcc] at hL
  have hdiff : ((k₀ : ℤ) - (k₁ : ℤ) = 1 ∨ (k₀ : ℤ) - (k₁ : ℤ) = -1) := by
    have h2 : (k₀ : ℂ) - (k₁ : ℂ) = 1 ∨ (k₀ : ℂ) - (k₁ : ℂ) = -1 := by
      rw [← hk₀, ← hk₁, ← ClassFunction.inner_sub_right]
      exact hval5
    rcases h2 with h | h
    · left
      have h3 : ((k₀ : ℤ) - (k₁ : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; exact h
      exact_mod_cast h3
    · right
      have h3 : ((k₀ : ℤ) - (k₁ : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) := by push_cast; exact h
      exact_mod_cast h3
  have hfive : 1 ≤ k₀ ∨ 1 ≤ k₁ := by
    rcases hdiff with h | h
    · left; omega
    · right; omega
  -- ## the five-element set of constituents
  set S4 : Finset (ClassFunction ↥C.P.H0 ℂ) :=
    {μ, lamCF C β₂ * μ, sconj C μ, lamCF C β₂ * sconj C μ} with hS4
  have hcard4 : S4.card = 4 := by
    rw [hS4,
      Finset.card_insert_of_notMem
        (s := ({lamCF C β₂ * μ, sconj C μ, lamCF C β₂ * sconj C μ} : Finset _))
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hD1, hD2, hD3⟩),
      Finset.card_insert_of_notMem
        (s := ({sconj C μ, lamCF C β₂ * sconj C μ} : Finset _))
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hD4, hD5⟩),
      Finset.card_insert_of_notMem
        (s := ({lamCF C β₂ * sconj C μ} : Finset _))
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact hD6),
      Finset.card_singleton]
  have hζexists : ∃ ζ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ζ ∧
      1 ≤ (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ζ).re ∧ ζ ∉ S4 := by
    rcases hfive with h5 | h5
    · refine ⟨ν₀, hν₀irr, ?_, ?_⟩
      · rw [hk₀, Complex.natCast_re]; exact_mod_cast h5
      · rw [hS4]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hD7, hD8, hD9, hD10⟩
    · refine ⟨lamCF C β₂ * ν₀, hD19, ?_, ?_⟩
      · rw [hk₁, Complex.natCast_re]; exact_mod_cast h5
      · rw [hS4]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hD11, hD12, hD13, hD14⟩
  obtain ⟨ζ, hζirr, hζval, hζnot⟩ := hζexists
  have hcard5 : (insert ζ S4).card = 5 := by
    rw [Finset.card_insert_of_notMem hζnot, hcard4]
  -- ## counting the five constituents
  have hres : IsCharacter (ClassFunction.restrict C.P.H0 χ) :=
    isCharacter_restrict_local hχ.isCharacter C.P.H0
  have hs : ∀ a ∈ insert ζ S4, IsIrreducibleCharacter a := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha4
    · exact hζirr
    · rw [hS4] at ha4
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha4
      rcases ha4 with rfl | rfl | rfl | rfl
      · exact hμirr
      · exact hD16
      · exact hD17
      · exact hD18
  have hmul : ∀ a ∈ insert ζ S4,
      1 ≤ (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) a).re := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha4
    · exact hζval
    · rw [hS4] at ha4
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha4
      rcases ha4 with rfl | rfl | rfl | rfl
      · rw [hkμ, Complex.natCast_re]; exact_mod_cast hkμ1
      · rw [hinner2, Complex.natCast_re]; exact_mod_cast hkμ1
      · rw [hμs, Complex.natCast_re]; exact_mod_cast hkμ1
      · rw [h4val, Complex.natCast_re]; exact_mod_cast hkμ1
  have hcount := card_le_re_of_constituents (ClassFunction.restrict C.P.H0 χ) hres
    (insert ζ S4) hs hmul
  rw [hcard5] at hcount
  norm_num at hcount
  -- ## degree conversion
  have hres1 : (ClassFunction.restrict C.P.H0 χ) 1 = χ 1 := rfl
  obtain ⟨m, -, hm⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hχ⟩ : IrreducibleCharacter G)
  have hm' : χ 1 = (m : ℂ) := by simpa using hm
  have h5m : 5 ≤ m := by
    have h : (5 : ℝ) ≤ (χ 1).re := hcount
    rw [hm', Complex.natCast_re] at h
    exact_mod_cast h
  refine ⟨(m : ℤ), ?_, ?_⟩
  · push_cast; exact hm'
  · rw [abs_of_nonneg (by positivity)]
    exact_mod_cast h5m

/-! ## The target -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem degreeBoundOfMovedB {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) :
    Work.GW2.C16.Compat D C → D.n = 2 → Work.GW2.C16.Sec3Hyp D →
    Work.GW2.C16.IsCoherent C f → Work.BG.IsPmIrr χ →
    OddOrder.RepresentationTheory.ClassFunction.inner χ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 0 →
    (∃ ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ,
      ν ∈ Work.GW2.C16.bset C f χ ∧ Work.BG.sconj C ν = ν) →
    (∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν) →
    (∃ μ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter μ ∧
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) μ ≠ 0 ∧
      Work.BG.sconj C μ ∉ Work.BG.lamOrbit C μ) →
    ∃ d : ℤ, χ 1 = d ∧ 5 ≤ |d| := by
  intro hC hn hS3 hf hχ h1 hA hcoll hB
  rcases hχ with hχ | hχ
  · exact degreeBoundOfMovedB_irr D C f χ hC hn hS3 hf hχ h1 hA hcoll hB
  · -- `χ = -ψ` with `ψ ∈ Irr G`: apply the irreducible case to `-χ`
    have hA' : ∃ ν : ClassFunction ↥C.P.H0 ℂ, ν ∈ bset C f (-χ) ∧ sconj C ν = ν := by
      obtain ⟨ν, hνmem, hνfix⟩ := hA
      obtain ⟨hνirr, hνne⟩ := hνmem
      exact ⟨ν, ⟨hνirr, by rw [ClassFunction.inner_neg_left]; exact neg_ne_zero.mpr hνne⟩, hνfix⟩
    have hcoll' : ∀ ν ∈ bset C f (-χ), sconj C ν ∈ lamOrbit C ν := by
      intro ν hν
      obtain ⟨hνirr, hνne⟩ := hν
      refine hcoll ν ⟨hνirr, ?_⟩
      intro h0
      exact hνne (by rw [ClassFunction.inner_neg_left, h0]; simp)
    have hB' : ∃ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ ∧
        ClassFunction.inner (ClassFunction.restrict C.P.H0 (-χ)) μ ≠ 0 ∧
        sconj C μ ∉ lamOrbit C μ := by
      obtain ⟨μ, hμirr, hμmult, hμmoved⟩ := hB
      exact ⟨μ, hμirr, by
        rw [ClassFunction.restrict_neg, ClassFunction.inner_neg_left]
        exact neg_ne_zero.mpr hμmult, hμmoved⟩
    have h1' : ClassFunction.inner (-χ) (trivialClassFunction G) = 0 := by
      rw [ClassFunction.inner_neg_left, h1, neg_zero]
    obtain ⟨d, hd, hd5⟩ := degreeBoundOfMovedB_irr D C f (-χ) hC hn hS3 hf hχ h1' hA' hcoll' hB'
    refine ⟨-d, ?_, by rw [abs_neg]; exact hd5⟩
    have h : χ 1 = -(d : ℂ) := by
      have h' : -χ 1 = (d : ℂ) := by rw [← ClassFunction.neg_apply]; exact hd
      rw [← h']
      ring
    rw [h, Int.cast_neg]

end Work.BG
