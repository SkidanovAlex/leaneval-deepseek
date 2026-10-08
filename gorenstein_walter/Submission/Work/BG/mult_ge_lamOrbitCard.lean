import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.degreeGeSOrbit
import Submission.Work.BG.kerLeOfMulAutInv
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.inner_coherence_coeff
import Submission.Work.BG.inner_restrict_eq_sum_irr
import Submission.Work.BG.isCharacterRestrict
import Submission.Work.BG.lamOrbitOfU_inner_eq_zero_or_one
import Submission.Work.BG.lamOrbitOfU_lamEquiv
import Submission.Work.BG.lamOrbitOfU_disjoint_bset
import Submission.Work.BG.lamOrbitOfU_mult_eq

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- **Step 1b of BG Lemma 3.6: the multiplicity gain.**  If `a ∈ Irr(U)` is nontrivial on `K`
and a constituent of `χ|_U` for an irreducible `χ`, and every member `ν` of `𝒮(χ)` satisfies
`ν^s ∈ Λν` (the standing hypothesis of Lemma 3.6), then the multiplicity `c = ⟨χ|_U, a⟩` is at
least the size of the `Λ`-orbit `Λ(a)` of `a`.

Route: `Λ(a) ∩ 𝒮(χ) = ∅` (if `ν ∈ Λ(a) ∩ 𝒮(χ)` then `ν^s ∈ Λν = Λ(a)`, giving
`(ν|_U)^{t₁} = ν|_U`, and the `U`-constituents of `ν|_U` are `S`-conjugates of `a` by Remark 3.1,
so some element of `S ∖ S₀` fixes `a`; `kerLeOfMulAutInv` — every element of `S ∖ S₀ = t₁S₀`
inverts `K` — then forces `K ≤ ker a`, contradicting `ha`).  Coherence
(`ind C (ν - ν') = fν - fν'` plus Frobenius reciprocity, packaged as
`Work.BG.inner_coherence_coeff`) makes `⟨χ|H₀,ν⟩ - ⟨χ,fν⟩` constant on `Λ(a)`; that constant is
`0` because `Λ(a)` is `𝒮(χ)`-free, so the multiplicities agree on `Λ(a)`, each equal to
`c/|Λ(a)|` with `c = ∑_{ν∈Λ(a)} e_ν ≥ 1`, whence `c ≥ |Λ(a)|`. -/
theorem mult_ge_lamOrbitCard {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (hS3 : Work.GW2.C16.Sec3Hyp D) (K : Subgroup G) (hKU : K ≤ D.U)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    [Fintype ↥(Work.GW2.C16.Uin C)] [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ)
    (hsl : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C))
    (ha : Work.BG.nontrivialOn C K a)
    (hca : OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ≠ 0) :
    ∃ c : ℕ, (c : ℂ) = OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ∧
      (Work.BG.lamOrbitOfU C (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard ≤ c := by
  classical
  haveI hH0fin : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI hIrrfin : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  set ac : ClassFunction ↥(Uin C) ℂ := (a : ClassFunction ↥(Uin C) ℂ) with hac
  set χH : ClassFunction ↥C.P.H0 ℂ := ClassFunction.restrict C.P.H0 χ with hχH
  -- `hca`, with the abbreviations
  have hcane : ClassFunction.inner (ClassFunction.restrict (Uin C)
      (ClassFunction.restrict C.P.H0 χ)) ac ≠ 0 := hca
  have hac_irr : IsIrreducibleCharacter ac := a.isIrreducible
  -- **Step 1**: expand `⟨χ|_U, a⟩` over `Irr(H₀)`.
  have hHchar : IsCharacter χH := isCharacterRestrict hχ.isCharacter C.P.H0
  have hexp : ClassFunction.inner (ClassFunction.restrict (Uin C) χH) ac =
      ∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χH (ν : ClassFunction ↥C.P.H0 ℂ) *
          ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac :=
    inner_restrict_eq_sum_irr (A := Uin C) hHchar ac
  -- hence some irreducible `ν₀` of `H₀` has `a` as a constituent of `ν₀|_U`
  have hsumne : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χH (ν : ClassFunction ↥C.P.H0 ℂ) *
          ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac) ≠ 0 := by
    rw [← hexp]
    exact hcane
  obtain ⟨ν₀, _, hν₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hν₀in : ClassFunction.inner (ClassFunction.restrict (Uin C)
      (ν₀ : ClassFunction ↥C.P.H0 ℂ)) ac ≠ 0 := (mul_ne_zero_iff.mp hν₀ne).2
  -- **Step 2**: the common multiplicity `κ = ⟨χ|H₀, ν₀⟩`
  obtain ⟨κnat, hκ⟩ := hHchar.exists_natCast_inner_irreducible
    (ψ := (ν₀ : ClassFunction ↥C.P.H0 ℂ)) ν₀.isIrreducible
  -- the members of `Λ(a)` among the irreducibles of `H₀`
  set S : Finset (IrreducibleCharacter ↥C.P.H0) :=
    Finset.univ.filter (fun ν : IrreducibleCharacter ↥C.P.H0 =>
      ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac ≠ 0)
    with hS
  have hmemS : ∀ ν : IrreducibleCharacter ↥C.P.H0, ν ∈ S ↔
      ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac ≠ 0 := by
    intro ν
    rw [hS, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ ν, h⟩⟩
  have hmemLam : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      (ν : ClassFunction ↥C.P.H0 ℂ) ∈ lamOrbitOfU C ac ↔
        ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac ≠ 0 := by
    intro ν
    exact ⟨fun h => h.2, fun h => ⟨ν.isIrreducible, h⟩⟩
  -- on `S` the second factor is `1` (Remark 3.1) and the first is `κ` (coherence)
  have hval : ∀ ν ∈ S, ClassFunction.inner (ClassFunction.restrict (Uin C)
      (ν : ClassFunction ↥C.P.H0 ℂ)) ac = 1 := by
    intro ν hνS
    have hne := (hmemS ν).mp hνS
    rcases lamOrbitOfU_inner_eq_zero_or_one D C hDC hS3 (ν := (ν : ClassFunction ↥C.P.H0 ℂ))
      ν.isIrreducible (a := ac) hac_irr with h | h
    · exact absurd h hne
    · exact h
  have hvalχ : ∀ ν ∈ S, ClassFunction.inner χH (ν : ClassFunction ↥C.P.H0 ℂ) = (κnat : ℂ) := by
    intro ν hνS
    have hνmem : (ν : ClassFunction ↥C.P.H0 ℂ) ∈ lamOrbitOfU C ac :=
      (hmemLam ν).mpr ((hmemS ν).mp hνS)
    have hν₀mem : (ν₀ : ClassFunction ↥C.P.H0 ℂ) ∈ lamOrbitOfU C ac :=
      ⟨ν₀.isIrreducible, hν₀in⟩
    exact (lamOrbitOfU_mult_eq D C hDC hS3 K hKU Knorm h1 h2 f hf χ hχ hsl a ha hνmem hν₀mem).trans hκ
  -- **Step 3**: the expanded sum is `|Λ(a)| · κ`
  have hsumS : (∑ ν ∈ S,
        ClassFunction.inner χH (ν : ClassFunction ↥C.P.H0 ℂ) *
          ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac)
      = (S.card : ℂ) * (κnat : ℂ) := by
    have hterm : ∀ ν ∈ S, ClassFunction.inner χH (ν : ClassFunction ↥C.P.H0 ℂ) *
        ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac
        = (κnat : ℂ) := fun ν hνS => by rw [hval ν hνS, hvalχ ν hνS, mul_one]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hsumAll : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner χH (ν : ClassFunction ↥C.P.H0 ℂ) *
          ClassFunction.inner (ClassFunction.restrict (Uin C) (ν : ClassFunction ↥C.P.H0 ℂ)) ac)
      = (S.card : ℂ) * (κnat : ℂ) := by
    rw [← hsumS]
    refine (Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) ?_ ?_).symm
    · intro x _; exact Finset.mem_univ x
    · intro x _ hx
      have hx0 : ClassFunction.inner (ClassFunction.restrict (Uin C)
          (x : ClassFunction ↥C.P.H0 ℂ)) ac = 0 := by
        by_contra h
        exact hx (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
      rw [hx0, mul_zero]
  -- the cardinality of `Λ(a)`
  have hcardS : (lamOrbitOfU C ac).ncard = S.card := by
    have hSet : lamOrbitOfU C ac = ((S.image
        (fun ν : IrreducibleCharacter ↥C.P.H0 => (ν : ClassFunction ↥C.P.H0 ℂ))) :
          Set (ClassFunction ↥C.P.H0 ℂ)) := by
      ext ν
      constructor
      · intro h
        obtain ⟨hirr, hne⟩ := h
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨⟨ν, hirr⟩, (hmemS ⟨ν, hirr⟩).mpr hne, rfl⟩)
      · intro h
        rw [Finset.mem_coe, Finset.mem_image] at h
        obtain ⟨b, hb, rfl⟩ := h
        exact ⟨b.isIrreducible, (hmemS b).mp hb⟩
    rw [hSet, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ (fun x y hxy => Subtype.ext hxy)]
  -- **Step 4**: assemble
  have hkey : ((S.card * κnat : ℕ) : ℂ) = ClassFunction.inner
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (a : ClassFunction ↥(Uin C) ℂ) := by
    rw [Nat.cast_mul]
    show (S.card : ℂ) * (κnat : ℂ) = ClassFunction.inner
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (a : ClassFunction ↥(Uin C) ℂ)
    rw [← hsumAll, ← hexp]
  refine ⟨S.card * κnat, hkey, ?_⟩
  have hkpos : 0 < κnat := by
    by_contra h
    have h0 : κnat = 0 := Nat.eq_zero_of_not_pos h
    have hzero : ((S.card * κnat : ℕ) : ℂ) = 0 := by rw [h0]; simp
    rw [hzero] at hkey
    exact hca hkey.symm
  calc (lamOrbitOfU C (a : ClassFunction ↥(Uin C) ℂ)).ncard
      = (lamOrbitOfU C ac).ncard := rfl
    _ = S.card := hcardS
    _ ≤ S.card * κnat := Nat.le_mul_of_pos_right S.card hkpos

end Work.BG
