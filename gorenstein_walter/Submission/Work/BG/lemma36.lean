import Mathlib
import Submission.Work.BG.Core24
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thmCSec3
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma24
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.degreeGeSOrbit
import Submission.Work.BG.degree_ge_sOrbitCount
import Submission.Work.BG.isCharacterRestrict
import Submission.Work.BG.existsConstituentNontrivial
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_pair_contra
import Submission.Work.BG.lamOrbit_subset_bset_of_badCase
import Submission.Work.BG.centralValue
import Submission.Work.BG.orbitCardMul
import Submission.Work.BG.mult_ge_lamOrbitCard
import Submission.Work.BG.lamOrbitOfU_disjoint_bset
import Submission.Work.BG.badCase_structure
import Submission.Work.BG.lamOrbit_ncard_eq_two_of_n_eq_two

/-
# BG Lemma 3.6, corrected form (`Work.GW2.C24.Lemma36InvProp`)

The proof plan is written up in `Submission/Work/BG/NOTES_lemma36_plan.md`.  In short:

* the printed proof (BG p. 210) only gives `χ(1) ≥ 2m·a(1)` with `m = D.n`, and its strictness
  step is the gap recorded in `NOTES_c4Degree.md`; the formal conclusion only asks for *some*
  `a ∈ Irr(U)` with `K ⊄ ker a` and `2 * D.n * a(1) < χ(1)`, so one takes `a` of **minimal
  degree** `d_min` among the irreducibles of `U` not trivial on `K`;
* step 1: for every `K`-nontrivial constituent `a` of `χ|_U`, the pieces
  `Work.BG.kerLeOfMulAutInv` (a `S∖S₀`-fixed `a` has `K ≤ ker a`) and `Work.BG.rem31Shape`
  give `c_a ≥ |Λ(a)|` and `|Σ_S(a)| · |Λ(a)| = 2m`, hence `χ(1) ≥ 2m·a(1)`
  (`c_a ≥ 1` is the multiplicity in `χ|_U`);
* step 2: if some `K`-nontrivial constituent has degree `> d_min` we are done;
* step 3: otherwise `χ(1) = 2m·d_min` would force `χ|H₀ = Σ_{ν ∈ Ω ∪ Ω^{t₁}} ν` with
  multiplicity one (`χ` vanishes on `T`) and `Ω ∩ 𝒮(χ) = ∅`; then `Work.BG.thm32`,
  `Work.BG.bset_orbit_struct` and `Work.BG.lemma24` (value at `t`, which is central in `H₀`)
  give a contradiction, as detailed in the plan.
-/

namespace Work.BG

/-! ## Step 1: the counting bound `2 * D.n * a(1) ≤ χ(1)` -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

section Step1

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (D : BGData G) (C : Sec2Ctx G)

/-- Pure arithmetic core of Step 1: from `|S·a| · |Λ(a)| = 2·D.n`, `|Λ(a)| ≤ c` and
`|S·a| · c · a(1) ≤ dχ` follows `2·D.n·a(1) ≤ dχ`. -/
theorem two_mul_mul_le_of (N S Λ c a d : ℕ) (h1 : S * Λ = 2 * N) (h2 : Λ ≤ c)
    (h3 : S * c * a ≤ d) : 2 * N * a ≤ d := by
  calc 2 * N * a = (S * Λ) * a := by rw [h1]
    _ = S * (Λ * a) := by ring
    _ ≤ S * (c * a) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = S * c * a := by ring
    _ ≤ d := h3

/-- Arithmetic core of Step 2: if some `K`-nontrivial constituent `a` of `χ|_U` has degree
`> dmin = irrDeg aMin`, then Step 1 applied to `a` gives the *strict* bound
`2·D.n·dmin < χ(1)` — that is, the conclusion with `a := aMin`. -/
theorem two_mul_mul_lt_of (N da dmin d : ℕ) (hN : 1 ≤ N) (h : dmin < da)
    (h1 : 2 * N * da ≤ d) : 2 * N * dmin < d := by
  have hpos : 0 < 2 * N := by omega
  have h2 : 2 * N * dmin < 2 * N * da := Nat.mul_lt_mul_of_pos_left h hpos
  exact lt_of_lt_of_le h2 h1

end Step1

section Step1Assembly

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (D : BGData G) (C : Sec2Ctx G)

/-- **Step 1 of the repaired route to BG Lemma 3.6.**  For an irreducible `a` of `U` nontrivial
on `K` and occurring in `χ|_U`, the three claims
`|S·a|·|Λ(a)| = 2·D.n` (`Work.BG.orbitCardMul`), `|Λ(a)| ≤ c` (`Work.BG.mult_ge_lamOrbitCard`)
and `|S·a|·c·a(1) ≤ χ(1)` (`Work.BG.degree_ge_sOrbitCount`) combine to `2·D.n·a(1) ≤ χ(1)`. -/
theorem degree_ge_two_n_mul (hDC : Compat D C)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (χ : ClassFunction G ℂ) (a : IrreducibleCharacter ↥(Uin C))
    (hOrbit : (sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ)).ncard *
        (lamOrbitOfU C (a : ClassFunction ↥(Uin C) ℂ)).ncard = 2 * D.n)
    (hMult : ∃ c : ℕ, (c : ℂ) = ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (a : ClassFunction ↥(Uin C) ℂ) ∧
      (lamOrbitOfU C (a : ClassFunction ↥(Uin C) ℂ)).ncard ≤ c)
    (hCount : ∃ c dχ : ℕ, (c : ℂ) = ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (a : ClassFunction ↥(Uin C) ℂ) ∧ χ 1 = (dχ : ℂ) ∧
      (sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ)).ncard * c * irrDeg a ≤ dχ) :
    ∃ dχ : ℕ, χ 1 = (dχ : ℂ) ∧ 2 * D.n * irrDeg a ≤ dχ := by
  obtain ⟨c₁, hc₁, hΛc⟩ := hMult
  obtain ⟨c₂, dχ, hc₂, hχd, hcnt⟩ := hCount
  have hc12 : c₁ = c₂ := Nat.cast_injective (R := ℂ) (by rw [hc₁, hc₂])
  rw [hc12] at hΛc
  exact ⟨dχ, hχd, two_mul_mul_le_of D.n _ _ c₂ (irrDeg a) dχ hOrbit hΛc hcnt⟩

/-- Step 1's count claim, discharged by `Work.BG.degree_ge_sOrbitCount`. -/
theorem hCount_of_degreeGeSOrbit (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    (a : IrreducibleCharacter ↥(Uin C))
    (hca : ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (a : ClassFunction ↥(Uin C) ℂ) ≠ 0) :
    ∃ c dχ : ℕ, (c : ℂ) = ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (a : ClassFunction ↥(Uin C) ℂ) ∧ χ 1 = (dχ : ℂ) ∧
      (sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ)).ncard * c * irrDeg a ≤ dχ :=
  degree_ge_sOrbitCount D C hDC χ hχ a hca

end Step1Assembly

/-! ## Step 1, first move: the `K`-nontrivial constituent of `χ|_U` -/

section Constituent

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **The constituent extraction.**  If `χ ∈ Irr(G)` is nontrivial on `K ≤ D.U = C.P.U`, then
`χ|_U = Res_U (Res_{H₀} χ)` is a genuine character of `U` (`isCharacterRestrict`) which is
nontrivial at (the image of) an element of `K`, so `existsConstituentNontrivial` produces an
irreducible constituent `a` of `χ|_U` that is nontrivial on `K` — the `a` on which Step 1 is run
and whose minimal-degree companion `aMin` is the answer to Lemma 3.6. -/
theorem exists_constituent_nontrivialOn (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (K : Subgroup G) (hKU : K ≤ D.U)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    (hK : ∃ x ∈ K, χ x ≠ χ 1) :
    ∃ a : IrreducibleCharacter ↥(Uin C), nontrivialOn C K a ∧
      ClassFunction.inner (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (a : ClassFunction ↥(Uin C) ℂ) ≠ 0 := by
  classical
  obtain ⟨x, hxK, hxne⟩ := hK
  have hxU : x ∈ C.P.U := by rw [hDC.U_eq]; exact hKU hxK
  -- lift `x` to `↥(Uin C)`
  let u₀ : ↥(Uin C) :=
    ⟨⟨x, C.P.U_le_H0 hxU⟩, L33D.mem_Uin_of_mem_CPU C hxU⟩
  have hcoe : ((u₀ : ↥C.P.H0) : G) = x := rfl
  have hone : ((1 : ↥(Uin C)) : ↥C.P.H0) = 1 := rfl
  -- `χ|_U` is a genuine character, nontrivial at `u₀`
  have hchar : IsCharacter
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) :=
    isCharacterRestrict (isCharacterRestrict hχ.isCharacter C.P.H0) (Uin C)
  have hune : (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) u₀ ≠
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) 1 := by
    simp only [ClassFunction.restrict_apply]
    rw [show ((u₀ : ↥C.P.H0) : G) = x from rfl]
    exact hxne
  obtain ⟨a, hairr, hainner, hane⟩ := existsConstituentNontrivial _ hchar u₀ hune
  exact ⟨⟨a, hairr⟩, ⟨u₀, by rw [hcoe]; exact hxK, hane⟩, hainner⟩

end Constituent

/-! ## Step 2 and the case split -/

section CaseSplit

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Strict branch of the case split.**  If the extracted constituent `a` of `χ|_U` has degree
*above* the minimum `irrDeg aMin`, then Step 1's bound `2·D.n·irrDeg a ≤ χ(1)` upgrades to the
*strict* bound `2·D.n·irrDeg aMin < χ(1)` — that is, the conclusion with `a := aMin`. -/
theorem strict_branch (D : BGData G) (C : Sec2Ctx G) (K : Subgroup G)
    [Fintype ↥(Uin C)] (χ : ClassFunction G ℂ) (a : IrreducibleCharacter ↥(Uin C))
    (hne : (nontrivialIrr C K).Nonempty)
    (hStep1 : ∃ dχ : ℕ, χ 1 = (dχ : ℂ) ∧ 2 * D.n * irrDeg a ≤ dχ)
    (hgt : irrDeg (aMin C K hne) < irrDeg a) :
    ∃ dχ : ℕ, χ 1 = (dχ : ℂ) ∧ 2 * D.n * irrDeg (aMin C K hne) < dχ := by
  obtain ⟨dχ, hdχ, hle⟩ := hStep1
  exact ⟨dχ, hdχ, two_mul_mul_lt_of D.n (irrDeg a) (irrDeg (aMin C K hne)) dχ
    (by have := D.two_le; omega) hgt hle⟩

/-- **Packaging.**  The strict bound for `aMin` is exactly the conclusion of BG Lemma 3.6, with
`a := aMin` (which is nontrivial on `K` by `aMin_nontrivial`). -/
theorem conclusion_of_aMin (D : BGData G) (C : Sec2Ctx G) (K : Subgroup G)
    [Fintype ↥(Uin C)] (χ : ClassFunction G ℂ)
    (hne : (nontrivialIrr C K).Nonempty)
    (h : ∃ dχ : ℕ, χ 1 = (dχ : ℂ) ∧ 2 * D.n * irrDeg (aMin C K hne) < dχ) :
    ∃ a : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a ∧
      (∃ u : ↥(Uin C), ((u : ↥C.P.H0) : G) ∈ K ∧ a u ≠ a 1) ∧
      ∃ dχ da : ℕ, χ 1 = dχ ∧ a 1 = da ∧ 2 * D.n * da < dχ := by
  obtain ⟨dχ, hdχ, hlt⟩ := h
  exact ⟨(aMin C K hne : ClassFunction ↥(Uin C) ℂ), (aMin C K hne).isIrreducible,
    aMin_nontrivial C K hne, dχ, irrDeg (aMin C K hne), hdχ,
    irrDeg_spec (aMin C K hne), hlt⟩

end CaseSplit

/-! ## The equality case -/

section Equality

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **The equality case of the case split.**  If the conclusion *fails* for `aMin`
(`hfail`), while Step 1 holds for the extracted constituent `a` (`hStep1`), then the chain

  `2·D.n·irrDeg a ≤ irrDeg χ ≤ 2·D.n·irrDeg aMin ≤ 2·D.n·irrDeg a`

collapses: `irrDeg a = irrDeg aMin` and `irrDeg χ = 2·D.n·irrDeg a` (`heq` of the plan).  This is
the input of `Work.BG.badCase_structure`. -/
theorem equality_case (D : BGData G) (C : Sec2Ctx G) (K : Subgroup G)
    [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    (a : IrreducibleCharacter ↥(Uin C)) (ha : nontrivialOn C K a)
    (hne : (nontrivialIrr C K).Nonempty)
    (hStep1 : ∃ dχ : ℕ, χ 1 = (dχ : ℂ) ∧ 2 * D.n * irrDeg a ≤ dχ)
    (hfail : ¬ (2 * D.n * irrDeg (aMin C K hne) < irrDeg ⟨χ, hχ⟩)) :
    irrDeg a = irrDeg (aMin C K hne) ∧ irrDeg ⟨χ, hχ⟩ = 2 * D.n * irrDeg a := by
  obtain ⟨dχ, hdχ, hle⟩ := hStep1
  have hχd : irrDeg ⟨χ, hχ⟩ = dχ := by
    apply Nat.cast_injective (R := ℂ)
    rw [← irrDeg_spec ⟨χ, hχ⟩, hdχ]
  have hmin : irrDeg (aMin C K hne) ≤ irrDeg a := aMin_min C K hne ha
  have h3 : 2 * D.n * irrDeg a ≤ irrDeg ⟨χ, hχ⟩ := by rw [hχd]; exact hle
  have h1 : irrDeg ⟨χ, hχ⟩ ≤ 2 * D.n * irrDeg (aMin C K hne) := le_of_not_gt hfail
  have h2 : 2 * D.n * irrDeg (aMin C K hne) ≤ 2 * D.n * irrDeg a :=
    Nat.mul_le_mul_left _ hmin
  have hchain : 2 * D.n * irrDeg (aMin C K hne) = 2 * D.n * irrDeg a :=
    le_antisymm h2 (le_trans h3 h1)
  have hpos : 0 < 2 * D.n := by have := D.two_le; omega
  exact ⟨(Nat.mul_left_cancel hpos hchain).symm, le_antisymm (hchain ▸ h1) h3⟩

/-- **The equality branch of BG Lemma 3.6 is impossible.**  Feed the extraction
`badCase_structure` (a `Λ`-orbit-closed, `𝒮(χ)`-free `Ξ` containing the support of `χ|H₀`, with all
`𝒮(χ)`-multiplicities `0` and `χ(t) = 0`) through the landed lemmas:
`Work.BG.lamOrbit_subset_bset_of_badCase` gives `hsub`, `Work.BG.thm32` gives `|𝒮(χ)| ≤ 3`, and
`Work.BG.bset_pair_contra` then closes the case — no member of `𝒮(χ)` vanishes at the central `t`
(`htval`, Schur) and every member is moved by `s` (`hfix`, the `D.n = 2` dichotomy) force
`𝒮(χ) = {ν₀, ν₀^s}`, so `0 = χ(t) = 2·⟨χ, fν₀⟩·ν₀(t) ≠ 0`. -/
theorem equality_branch_false (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (hS3 : Sec3Hyp D) [Fintype ↥C.P.H0]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    (hne : (bset C f χ).Nonempty)
    (hsl : ∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν)
    (hstruct : ∃ Ξ : Set (ClassFunction ↥C.P.H0 ℂ),
      (∀ ν ∈ Ξ, lamOrbit C ν ⊆ Ξ) ∧ (∀ ν ∈ Ξ, ν ∉ bset C f χ) ∧
      (∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν ≠ 0 → ν ∈ Ξ) ∧
      (∀ ν ∈ bset C f χ, ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν = 0) ∧
      χ (C.t : G) = 0)
    (htval : ∀ ν ∈ bset C f χ, ν C.t ≠ 0)
    (hfix : ∀ ν ∈ bset C f χ, sconj C ν ≠ ν) : False := by
  obtain ⟨Ξ, hΞorb, hΞfree, hsupp, hzero, ht⟩ := hstruct
  have hsub := lamOrbit_subset_bset_of_badCase C f hf χ Ξ hΞorb hΞfree hsupp hzero
  exact bset_pair_contra C f hf χ hχ hne
    (thm32 D C hDC hS3 f hf χ (Or.inl hχ)) hsl hsub hfix htval ht

/-- **`htval` of the equality case.**  No member of `𝒮(χ)` vanishes at the central involution
`t`: for `ν ∈ Irr(H₀)` one has `ν C.t = ±ν 1 ≠ 0` (`Work.BG.centralValue`, Schur's lemma applied
to the central element `t`), and `𝒮(χ)` consists of irreducible characters. -/
theorem bset_apply_t_ne_zero (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ) :
    ∀ ν ∈ bset C f χ, ν C.t ≠ 0 := by
  intro ν hν
  obtain ⟨hνirr, -⟩ := hν
  obtain ⟨hcase, hne⟩ := centralValue C ν hνirr
  rcases hcase with h | h
  · rw [h]; exact hne
  · rw [h]; exact neg_ne_zero.mpr hne

/-- **Every `Λ`-orbit in `Irr(H₀)` has at least two elements.**  By `Work.BG.rem31Shape` an
irreducible `ν` of `H₀` either has `ν|_U` irreducible and `|Λν| = D.n ≥ 2`, or `ν|_U = a + a₂` and
`2|Λν| = D.n`; in the latter case `D.n ≥ 2` and `D.n ≠ 2` (for `D.n = 2`,
`Work.BG.lamOrbit_ncard_eq_two_of_n_eq_two` gives `|Λν| = 2` instead) force `|Λν| ≥ 2`. -/
theorem lamOrbit_ncard_ge_two (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (hS3 : Sec3Hyp D) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    2 ≤ (lamOrbit C ν).ncard := by
  by_cases hn : D.n = 2
  · rw [lamOrbit_ncard_eq_two_of_n_eq_two D C hDC hν hn]; exact D.two_le
  · obtain ⟨a, _hairr, hcase⟩ := rem31Shape D C hDC hS3 ν hν
    rcases hcase with ⟨_hres, hcard⟩ | ⟨a₂, _ha₂irr, _hne, _hdeg, _hres, hcard⟩
    · rw [hcard]; exact D.two_le
    · by_contra h
      have h1 : (lamOrbit C ν).ncard ≤ 1 := by omega
      have h2 : D.n ≤ 2 := by
        calc D.n = 2 * (lamOrbit C ν).ncard := hcard.symm
          _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 h1
          _ = 2 := by norm_num
      exact hn (le_antisymm h2 D.two_le)

/-- **`hfix` of the equality case.**  If every member of `𝒮(χ)` has its `Λ`-orbit inside `𝒮(χ)`
(`hsub`), then no member of `𝒮(χ)` is fixed by `s`: for `ν ∈ 𝒮(χ)` with `ν^s = ν`, coherence
(`Work.BG.bset_orbit_struct` part 2) makes `Λν ⊆ {ν}`, contradicting `|Λν| ≥ 2`
(`Work.BG.lamOrbit_ncard_ge_two`). -/
theorem sconj_ne_self_of_mem_bset (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (hS3 : Sec3Hyp D) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    (hsl : ∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν)
    (hsub : ∀ ν ∈ bset C f χ, lamOrbit C ν ⊆ bset C f χ) :
    ∀ ν ∈ bset C f χ, sconj C ν ≠ ν := by
  intro ν hν hsν
  have hsingle : lamOrbit C ν ⊆ ({ν} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    intro μ hμ
    have hμbset : μ ∈ bset C f χ := hsub ν hν hμ
    by_cases hμν : μ = ν
    · rw [Set.mem_singleton_iff]; exact hμν
    · have hpair := (bset_orbit_struct C f hf χ (Or.inl hχ)).2 ν hν μ hμbset hμ hμν
      rw [Set.mem_singleton_iff, hpair, hsν]
  have heq : lamOrbit C ν = {ν} := Set.Subset.antisymm hsingle (by
    intro μ hμ
    rw [Set.mem_singleton_iff] at hμ
    rw [hμ]
    exact s02c_LamEquiv_refl C ν)
  have h2 := lamOrbit_ncard_ge_two D C hDC hS3 hν.1
  rw [heq, Set.ncard_singleton] at h2
  omega

end Equality

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C24 in
/-- `Lemma36InvProp`'s two `Invertible (Nat.card _)` arguments are irrelevant (`Invertible` is a
subsingleton), so they can be replaced by any other instance.  In a *proof* of `Lemma36InvProp` the
instances coming from the statement are local variables, while the supporting lemmas
(`Work.GW2.C16.IsCoherent`, `Work.BG.bset`, …) are stated in terms of the *global*
`invertibleOfPos` instances; this transport changes the goal once and for all. -/
theorem Lemma36InvProp_inst_irrel {G : Type} [Group G] [Finite G] [Fintype G]
    (D : BGData G) (C : Sec2Ctx G) (K : Subgroup G)
    (i j : Invertible (Nat.card G : ℂ)) (k l : Invertible (Nat.card ↥C.P.H0 : ℂ)) :
    @Work.GW2.C24.Lemma36InvProp G _ _ _ i D C k K →
      @Work.GW2.C24.Lemma36InvProp G _ _ _ j D C l K :=
  Eq.mp (congrArg (fun p : Invertible (Nat.card G : ℂ) × Invertible (Nat.card ↥C.P.H0 : ℂ) =>
      @Work.GW2.C24.Lemma36InvProp G _ _ _ p.1 D C p.2 K)
    (show (i, k) = (j, l) from Prod.ext (Subsingleton.elim i j) (Subsingleton.elim k l)))

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C24 in
/-- **The main body of `Work.BG.lemma36`, with the *global* `Invertible`/`Fintype` instances.**
The statement `Work.GW2.C24.Lemma36InvProp D C K` needs an `Invertible (Nat.card G : ℂ)` and an
`Invertible (Nat.card ↥C.P.H0 : ℂ)`; here these are *not* local instance binders, so every
type-class search inside the proof produces the same global `invertibleOfPos` instances that the
supporting lemmas (`Work.GW2.C16.IsCoherent`, `Work.BG.bset`, …) use at the positions where their
own telescopes leave them to type-class search.  `Work.BG.lemma36` recovers the requested
statement by `Work.BG.Lemma36InvProp_inst_irrel`. -/
theorem lemma36_aux {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K : Subgroup G) :
    Work.GW2.C24.Lemma36InvProp D C K := by
  intro hDC hS3 hKU hKnorm ht1inv ht2inv f hf χ hχ hbset hKx hsl
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- the `K`-nontrivial constituent `a` of `χ|_U` (`Work.BG.exists_constituent_nontrivialOn`)
  obtain ⟨a, ha, hca⟩ := exists_constituent_nontrivialOn D C hDC K hKU χ hχ hKx
  have hne : (nontrivialIrr C K).Nonempty := ⟨a, ha⟩
  -- Step 1: the three orbit/multiplicity/counting inputs, combined by
  -- `Work.BG.degree_ge_two_n_mul` into `2 * D.n * a(1) ≤ χ(1)`
  have hOrbit := orbitCardMul D C hDC hS3 K hKU hKnorm ht1inv ht2inv ha
  have hMultA := mult_ge_lamOrbitCard D C hDC hS3 K hKU hKnorm ht1inv ht2inv
    f hf χ hχ hsl a ha hca
  have hCount := hCount_of_degreeGeSOrbit D C hDC χ hχ a hca
  have hStep1 := degree_ge_two_n_mul D C hDC χ a hOrbit hMultA hCount
  -- Step 2: the case split on whether the minimal degree is attained by `a`
  by_cases hlt : 2 * D.n * irrDeg (aMin C K hne) < irrDeg ⟨χ, hχ⟩
  · -- strict branch: the conclusion already holds with `a := aMin`
    exact conclusion_of_aMin D C K χ hne ⟨irrDeg ⟨χ, hχ⟩, irrDeg_spec ⟨χ, hχ⟩, hlt⟩
  · -- equality branch: extract the `Ξ`-structure and contradict it
    obtain ⟨_haeq, hχeq⟩ := equality_case D C K χ hχ a ha hne hStep1 hlt
    have hΩfree := lamOrbitOfU_disjoint_bset D C hDC hS3 K hKU hKnorm ht1inv ht2inv f χ hsl a ha
    obtain ⟨Ξ, hΞorb, hΞfree, hsupp, hzero, ht⟩ :=
      badCase_structure D C hDC f hf χ hχ hsl a hca hOrbit hMultA hΩfree hχeq
    have hsub := lamOrbit_subset_bset_of_badCase C f hf χ Ξ hΞorb hΞfree hsupp hzero
    exact (equality_branch_false D C hDC hS3 f hf χ hχ hbset hsl
      ⟨Ξ, hΞorb, hΞfree, hsupp, hzero, ht⟩ (bset_apply_t_ne_zero C f χ)
      (sconj_ne_self_of_mem_bset D C hDC hS3 f hf χ hχ hsl hsub)).elim

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C24 in
/-- **BG Lemma 3.6 (BG 1981, p. 210), corrected form.**  See `Work.BG.lemma36_aux` for the body;
here the `Invertible` instances of the statement are the caller's, and
`Work.BG.Lemma36InvProp_inst_irrel` transports the global-instance version to it. -/
theorem lemma36 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K : Subgroup G) :
    Work.GW2.C24.Lemma36InvProp D C K :=
  Lemma36InvProp_inst_irrel D C K (invertibleOfPos (Nat.card G))
    (inferInstance : Invertible (Nat.card G : ℂ)) (invertibleOfPos (Nat.card ↥C.P.H0))
    (inferInstance : Invertible (Nat.card ↥C.P.H0 : ℂ)) (lemma36_aux D C K)

end Work.BG
