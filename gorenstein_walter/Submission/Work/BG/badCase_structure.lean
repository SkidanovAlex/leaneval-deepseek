import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.L33DDefs
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_lamSign
import Submission.Work.BG.inner_coherence_coeff
import Submission.Work.BG.s02_orbitSumVanish
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.degree_ge_sOrbitCount
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_lamDualCyclic
import Submission.Work.BG.supp_restrictU_phiS_invariant
import Submission.Work.BG.sconj_image_lamOrbitOfU
import Submission.Work.BG.eqCase_kill

set_option maxHeartbeats 1600000

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary `Λ`-calculus -/

/-- Every `λ_β` is trivial on `U`. -/
theorem badCase_lamCF_apply_mem_U (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (x : ↥(Uin C)) :
    lamCF C β (x : ↥C.P.H0) = 1 := by
  rw [lamCF_apply]
  have hx : (x : ↥C.P.H0) ∈ C.P.U.subgroupOf C.P.H0 := x.2
  have hq : quotMk C.P (x : ↥C.P.H0) = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  rw [hq, map_one]
  rfl

/-- Twisting by `λ_β` does not change the restriction to `U`. -/
theorem badCase_restrict_lamCF_mul (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.restrict (Uin C) (lamCF C β * ν) = ClassFunction.restrict (Uin C) ν := by
  ext u
  rw [ClassFunction.restrict_apply, ClassFunction.mul_apply, ClassFunction.restrict_apply,
    badCase_lamCF_apply_mem_U, one_mul]

/-- `λ_{β⁻¹} * (λ_β * ν) = ν`. -/
theorem badCase_lamCF_mul_cancel' (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β⁻¹ * (lamCF C β * ν) = ν := by
  ext x
  rw [ClassFunction.mul_apply, ClassFunction.mul_apply, lamCF_apply, lamCF_apply,
    MonoidHom.inv_apply]
  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- `λ_β * (λ_{β⁻¹} * ν) = ν`. -/
theorem badCase_lamCF_mul_cancel (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    lamCF C β * (lamCF C β⁻¹ * ν) = ν := by
  ext x
  rw [ClassFunction.mul_apply, ClassFunction.mul_apply, lamCF_apply, lamCF_apply,
    MonoidHom.inv_apply]
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- Evaluation of a finite sum of class functions. -/
theorem badCase_sum_apply {H : Type} [Group H] {ι : Type} (s : Finset ι)
    (g : ι → ClassFunction H ℂ) (x : H) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.add_apply, ih]

/-- Restriction of a finite sum of class functions is the sum of the restrictions. -/
theorem badCase_restrict_finset_sum {H : Type} [Group H] (A : Subgroup H) {ι : Type}
    (s : Finset ι) (g : ι → ClassFunction H ℂ) :
    ClassFunction.restrict A (∑ i ∈ s, g i) = ∑ i ∈ s, ClassFunction.restrict A (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.restrict_add, ih]

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `χ|H₀` is `s`-invariant, because `χ` is a class function of `G`. -/
theorem badCase_chiH0_sconj_invariant (C : Sec2Ctx G) (χ : ClassFunction G ℂ) :
    ClassFunction.compHom (conjMulEquiv C.P C.s).toMonoidHom
        (ClassFunction.restrict C.P.H0 χ) = ClassFunction.restrict C.P.H0 χ := by
  ext h
  simp only [ClassFunction.compHom_apply, ClassFunction.restrict_apply]
  exact χ.conj_eq _ _

/-- The inner product of a genuine character with an irreducible is a natural number. -/
theorem badCase_inner_isNat {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ : ClassFunction K ℂ} (hφ : IsCharacter φ)
    {ψ : ClassFunction K ℂ} (hψ : IsIrreducibleCharacter ψ) :
    ∃ n : ℕ, ClassFunction.inner φ ψ = (n : ℂ) := by
  obtain ⟨m, -, -, hmc⟩ := hφ.exists_natFinsupp_eq_sum
  exact ⟨m ψ, (hmc ψ hψ).symm⟩

/-- `lamOrbitOfU C a` is closed under the `Λ`-action: twisting by a linear character does not
change the restriction to `U`. -/
theorem badCase_lamOrbitOfU_closed (C : Sec2Ctx G)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (a : ClassFunction ↥(Uin C) ℂ) :
    ∀ ν ∈ lamOrbitOfU C a, lamOrbit C ν ⊆ lamOrbitOfU C a := by
  intro ν hν μ hμ
  obtain ⟨hνirr, hνa⟩ := hν
  obtain ⟨β, hβ⟩ := hμ
  refine ⟨?_, ?_⟩
  · rw [hβ]
    exact lambda_mul_irreducible C.P ⟨β, rfl⟩ hνirr
  · rw [hβ, badCase_restrict_lamCF_mul]
    exact hνa


/-- If `ν ∈ Irr(H₀)` occurs in `χ|H₀` with nonzero multiplicity, then `⟨χ|_U, ν|_U⟩ ≠ 0`.

Route: the Fourier expansion `χ|H₀ = ∑_μ ⟨χ|H₀,μ⟩·μ` restricts to `χ|_U = ∑_μ ⟨χ|H₀,μ⟩·(μ|_U)`,
so `⟨χ|_U, ν|_U⟩ = ∑_μ ⟨χ|H₀,μ⟩·⟨μ|_U, ν|_U⟩`; by `Work.BG.rem31Orth` the term vanishes unless
`μ ~ ν` (and then equals `D.n/|Λν|`), so the sum is `(D.n/|Λν|)·∑_{μ~ν}⟨χ|H₀,μ⟩`, which is
nonzero because the multiplicities `⟨χ|H₀,μ⟩` are natural numbers and `⟨χ|H₀,ν⟩ ≠ 0`. -/
theorem badCase_inner_restrictU_ne_zero {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(Work.GW2.C16.Uin C)] [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν)
    (he : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν ≠ 0) :
    ClassFunction.inner
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (ClassFunction.restrict (Uin C) ν) ≠ 0 := by
  classical
  have hχH0 : IsCharacter (ClassFunction.restrict C.P.H0 χ) :=
    isCharacterRestrict hχ.isCharacter C.P.H0
  have hnat : ∀ μ : IrreducibleCharacter ↥C.P.H0,
      ∃ n : ℕ, ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
        (μ : ClassFunction ↥C.P.H0 ℂ) = (n : ℂ) :=
    fun μ => badCase_inner_isNat hχH0 μ.isIrreducible
  choose n hn using hnat
  -- restriction of the Fourier expansion of `χ|H₀`
  have hres : ClassFunction.restrict (Uin C)
      (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) •
          (μ : ClassFunction ↥C.P.H0 ℂ))
      = ∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) •
          ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ) := by
    rw [badCase_restrict_finset_sum]
    exact Finset.sum_congr rfl fun μ _ => ClassFunction.restrict_smul (Uin C) _ _
  have hdec : ClassFunction.inner
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (ClassFunction.restrict (Uin C) ν) =
      ∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (μ : ClassFunction ↥C.P.H0 ℂ) *
          ClassFunction.inner (ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ))
            (ClassFunction.restrict (Uin C) ν) := by
    conv_lhs =>
      rw [← sum_inner_irreducibleCharacter_smul (ClassFunction.restrict C.P.H0 χ)]
    rw [hres, inner_sum_left]
    exact Finset.sum_congr rfl fun μ _ => by rw [ClassFunction.inner_smul_left]
  -- rewriting the terms
  have h2 : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (μ : ClassFunction ↥C.P.H0 ℂ) *
          ClassFunction.inner (ClassFunction.restrict (Uin C) (μ : ClassFunction ↥C.P.H0 ℂ))
            (ClassFunction.restrict (Uin C) ν)) =
      ∑ μ : IrreducibleCharacter ↥C.P.H0,
        (n μ : ℂ) * (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then
          (D.n : ℂ) / ((lamOrbit C ν).ncard : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    have horth := ((rem31Orth D C) hDC) (μ : ClassFunction ↥C.P.H0 ℂ) ν μ.isIrreducible hν
    rw [hn μ]
    by_cases hL : LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν
    · rw [if_pos hL, horth.1 hL]
    · rw [if_neg hL, horth.2 hL, mul_zero]
  have h3 : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        (n μ : ℂ) * (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then
          (D.n : ℂ) / ((lamOrbit C ν).ncard : ℂ) else 0)) =
      ((D.n : ℂ) / ((lamOrbit C ν).ncard : ℂ)) *
        (∑ μ : IrreducibleCharacter ↥C.P.H0,
          (n μ : ℂ) * (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hL : LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν
    · simp only [if_pos hL]; ring
    · simp only [if_neg hL]; ring
  have h4 : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        (n μ : ℂ) * (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0)) =
      ((∑ μ : IrreducibleCharacter ↥C.P.H0,
          (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0) * n μ : ℕ) : ℂ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Nat.cast_mul]
    by_cases hL : LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν
    · simp only [if_pos hL]; ring
    · simp only [if_neg hL]; ring
  have hval : ClassFunction.inner
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (ClassFunction.restrict (Uin C) ν) =
      ((D.n : ℂ) / ((lamOrbit C ν).ncard : ℂ)) *
        ((∑ μ : IrreducibleCharacter ↥C.P.H0,
            (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0) * n μ : ℕ) : ℂ) := by
    rw [hdec, h2, h3, h4]
  -- positivity
  have hNpos : 0 < ∑ μ : IrreducibleCharacter ↥C.P.H0,
      (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0) * n μ := by
    have hle := Finset.single_le_sum
      (f := fun μ : IrreducibleCharacter ↥C.P.H0 =>
        (if LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0) * n μ)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0))
    have hνI : (if LamEquiv C ((⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0) :
            ClassFunction ↥C.P.H0 ℂ) ν then 1 else 0)
        * n (⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0)
          = n (⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0) := by
      rw [IrreducibleCharacter.coe_mk, if_pos (s02c_LamEquiv_refl C ν), one_mul]
    rw [hνI] at hle
    have hnν : 0 < n (⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0) := by
      rcases Nat.eq_zero_or_pos (n (⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0)) with h | h
      · exact absurd (by rw [hn (⟨ν, hν⟩ : IrreducibleCharacter ↥C.P.H0), h]; norm_num) he
      · exact h
    exact lt_of_lt_of_le hnν hle
  -- conclude
  intro hzero
  rw [hval] at hzero
  rcases mul_eq_zero.mp hzero with hc | hc
  · rcases div_eq_zero_iff.mp hc with hc | hc
    · exact absurd (Nat.cast_eq_zero.mp hc) (by have := D.two_le; omega)
    · have hfin : (lamOrbit C ν).Finite := by
        obtain ⟨hfinD, -⟩ := s02_lamDualCyclic C
        haveI : Finite (lamDual C) := hfinD
        have hr : lamOrbit C ν = Set.range (fun β : lamDual C => lamCF C β * ν) := by
          ext χ
          exact ⟨fun ⟨β, hβ⟩ => ⟨β, hβ.symm⟩, fun ⟨β, hβ⟩ => ⟨β, hβ.symm⟩⟩
        rw [hr]
        exact Set.finite_range _
      have hpos : 0 < (lamOrbit C ν).ncard :=
        (Set.ncard_pos hfin).mpr ⟨ν, s02c_LamEquiv_refl C ν⟩
      exact absurd (Nat.cast_eq_zero.mp hc) (Nat.pos_iff_ne_zero.mp hpos)
  · exact Nat.pos_iff_ne_zero.mp hNpos (Nat.cast_eq_zero.mp hc)

/-- **Step 3 of BG Lemma 3.6 (equality case, extraction).**  Let `a` be a constituent of `χ|_U`
(`hca`) for which the Step-1 chain is an *equality*: `|S·a|·|Λ(a)| = 2·D.n` (`hOrbit`),
`|Λ(a)| ≤ c_a = ⟨χ|_U, a⟩` (`hMultA`), `Λ(a)` is `𝒮(χ)`-free (`hΩfree`), and
`irrDeg χ = 2·D.n·irrDeg a` (`heq`).  Then the support of `χ|H₀` is a `Λ`-orbit-closed,
`𝒮(χ)`-free set `Ξ`, every member of `𝒮(χ)` has multiplicity `0` in `χ|H₀`, and `χ` vanishes at
the central involution `t`.

These are exactly the hypotheses of `Work.BG.lamOrbit_subset_bset_of_badCase` and
`Work.BG.bset_pair_contra`, so the equality case is contradicted.

Route: `c_a ≥ |Λ(a)|` and `|S·a|·|Λ(a)| = 2·D.n` give
`|S·a|·c_a·a(1) ≥ 2·D.n·a(1) = χ(1)`, while the `S`-orbit of `a` contributes exactly
`|S·a|·c_a·a(1)` to `χ(1)` (multiplicities and degrees are `S`-invariant, `degree_ge_sOrbitCount`);
so `c_a = |Λ(a)|` and `χ|_U` has no constituent outside `S·a`.  By Remark 3.1 the support of
`χ|H₀` is then `Ω ∪ Ω^{t₁}` with `Ω := Λ(a)`, with multiplicity one on `Ω` (`c_a = |Λ(a)|` and the
multiplicities are equal on the `𝒮(χ)`-free orbits) and on `Ω^{t₁}` (`s`-invariance); take
`Ξ := Ω ∪ Ω^{t₁}`, which is `Λ`-orbit-closed, `𝒮(χ)`-free (`hΩfree`, plus `hsl` for `Ω^{t₁}`) and
contains the support, and no member of `𝒮(χ)` is a constituent (any such member lies in `Ξ`).
Finally `χ|H₀ = ∑_{ν∈Ξ} ν` with each `Λ`-orbit sum vanishing off `U`, so `χ(t) = 0` as `t ∉ U`. -/
theorem badCase_structure {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ)
    (hsl : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C))
    (hca : OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ≠ 0)
    (hOrbit : (Work.BG.sOrbitU D C hDC
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard *
      (Work.BG.lamOrbitOfU C
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard = 2 * D.n)
    (hMultA : ∃ c : ℕ, (c : ℂ) = OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ∧
      (Work.BG.lamOrbitOfU C
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard ≤ c)
    (hΩfree : ∀ ν ∈ Work.BG.lamOrbitOfU C
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ),
      ν ∉ Work.GW2.C16.bset C f χ)
    (heq : Work.BG.irrDeg ⟨χ, hχ⟩ = 2 * D.n * Work.BG.irrDeg a) :
    ∃ Ξ : Set (OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ),
      (∀ ν ∈ Ξ, Work.BG.lamOrbit C ν ⊆ Ξ) ∧
      (∀ ν ∈ Ξ, ν ∉ Work.GW2.C16.bset C f χ) ∧
      (∀ ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ,
        OddOrder.RepresentationTheory.IsIrreducibleCharacter ν →
        OddOrder.RepresentationTheory.ClassFunction.inner
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) ν ≠ 0 → ν ∈ Ξ) ∧
      (∀ ν ∈ Work.GW2.C16.bset C f χ,
        OddOrder.RepresentationTheory.ClassFunction.inner
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) ν = 0) ∧
      χ (C.t : G) = 0 := by
  classical
  haveI hIrrH0 : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  haveI hIrrU : Fintype (IrreducibleCharacter ↥(Uin C)) := Fintype.ofFinite _
  let aU : ClassFunction ↥(Uin C) ℂ := (a : ClassFunction ↥(Uin C) ℂ)
  let s1 : ↥(D.S) := ⟨D.t1, D.t1_mem⟩
  let aT : ClassFunction ↥(Uin C) ℂ :=
    ClassFunction.compHom (L33D.phiS D C hDC s1).toMonoidHom aU
  let Ω : Set (ClassFunction ↥C.P.H0 ℂ) := lamOrbitOfU C aU
  let Ω' : Set (ClassFunction ↥C.P.H0 ℂ) := lamOrbitOfU C aT
  have hsconjΩ : sconj C '' Ω = Ω' := by
    have h := sconj_image_lamOrbitOfU D C hDC aU
    simpa only [Ω, Ω', aT, s1] using h
  obtain ⟨hkc, hsuppU⟩ := eqCase_kill D C hDC χ hχ a hca hOrbit hMultA heq
  -- multiplicity constancy on a `bset`-free `Λ`-orbit
  have hconst : ∀ ν ν' : ClassFunction ↥C.P.H0 ℂ,
      IsIrreducibleCharacter ν → IsIrreducibleCharacter ν' → LamEquiv C ν ν' →
      (∀ ξ ∈ lamOrbit C ν, ξ ∉ bset C f χ) →
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν =
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν' := by
    intro ν ν' hν hν' hlam hfree
    have h1 : ClassFunction.inner χ (f ν) = 0 := by
      by_contra h
      exact hfree ν (s02c_LamEquiv_refl C ν) ⟨hν, h⟩
    have h2 : ClassFunction.inner χ (f ν') = 0 := by
      by_contra h
      exact hfree ν' hlam ⟨hν', h⟩
    have hco := inner_coherence_coeff C f hf χ hν hν' hlam
    rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_right, h1, h2, sub_zero] at hco
    exact sub_eq_zero.mp hco.symm
  -- `Λ`-orbit-closure
  have hΞorb : ∀ ν ∈ Ω ∪ Ω', lamOrbit C ν ⊆ Ω ∪ Ω' := by
    intro ν hν
    rcases hν with hν | hν
    · exact fun μ hμ => Or.inl (badCase_lamOrbitOfU_closed C aU ν hν hμ)
    · exact fun μ hμ => Or.inr (badCase_lamOrbitOfU_closed C aT ν hν hμ)
  -- `bset`-freeness
  have hΞfree : ∀ ν ∈ Ω ∪ Ω', ν ∉ bset C f χ := by
    intro ν hν
    rcases hν with hν | hν
    · exact hΩfree ν hν
    · intro hbset
      have hνmem : ν ∈ sconj C '' Ω := by rw [hsconjΩ]; exact hν
      obtain ⟨ν'', hν''Ω, hν''eq⟩ := hνmem
      have hsν : sconj C ν ∈ lamOrbit C ν := hsl ν hbset
      have he1 : sconj C ν = ν'' := by rw [← hν''eq, sconj_sconj]
      rw [he1] at hsν
      exact hΩfree ν
        (badCase_lamOrbitOfU_closed C aU ν'' hν''Ω (s02c_LamEquiv_symm C hsν)) hbset
  -- the support of `χ|H₀`
  have hsupp : ∀ ν : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter ν →
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν ≠ 0 → ν ∈ Ω ∪ Ω' := by
    intro ν hνirr he
    have hne := badCase_inner_restrictU_ne_zero D C hDC χ hχ hνirr he
    -- second Fourier expansion, over `Irr(U)`
    have hdec2 : ClassFunction.inner
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (ClassFunction.restrict (Uin C) ν) =
        ∑ b : IrreducibleCharacter ↥(Uin C),
          ClassFunction.inner (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
            (b : ClassFunction ↥(Uin C) ℂ) *
          ClassFunction.inner (b : ClassFunction ↥(Uin C) ℂ)
            (ClassFunction.restrict (Uin C) ν) := by
      conv_lhs => rw [← sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))]
      rw [inner_sum_left]
      exact Finset.sum_congr rfl fun b _ => by rw [ClassFunction.inner_smul_left]
    have hex : ∃ b : IrreducibleCharacter ↥(Uin C),
        ClassFunction.inner (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
          (b : ClassFunction ↥(Uin C) ℂ) ≠ 0 ∧
        ClassFunction.inner (b : ClassFunction ↥(Uin C) ℂ)
          (ClassFunction.restrict (Uin C) ν) ≠ 0 := by
      by_contra hno
      push_neg at hno
      refine hne ?_
      rw [hdec2]
      exact Finset.sum_eq_zero fun b _ => by
        by_cases hb : ClassFunction.inner
            (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
            (b : ClassFunction ↥(Uin C) ℂ) = 0
        · rw [hb, zero_mul]
        · rw [hno b hb, mul_zero]
    obtain ⟨b, hχb, hbν⟩ := hex
    -- `b` lies in the `S`-orbit of `a`
    have hbT : (b : ClassFunction ↥(Uin C) ℂ) ∈ sOrbitU D C hDC aU := hsuppU b hχb
    obtain ⟨s, hs⟩ := hbT
    -- the coset decomposition of `s`
    have hS0idx : (D.S0.subgroupOf (D.S : Subgroup G)).index = 2 := D.S0_index
    haveI hNnorm : (D.S0.subgroupOf (D.S : Subgroup G)).Normal :=
      Subgroup.normal_of_index_eq_two hS0idx
    have hsup := L33D.S0_subgroupOf_sup_zpowers_t1 D C hDC
    have hs_top : s ∈ D.S0.subgroupOf (D.S : Subgroup G) ⊔ Subgroup.zpowers s1 := by
      rw [hsup]; exact Subgroup.mem_top s
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hs_top
    -- `σ = z⁻¹ y⁻¹ z ∈ S₀` and `(phiS σ) b = (phiS z) aU`
    have hσmem : z⁻¹ * y⁻¹ * z ∈ D.S0.subgroupOf (D.S : Subgroup G) := by
      have h := hNnorm.conj_mem y⁻¹ (Subgroup.inv_mem _ hy) z⁻¹
      simpa [mul_assoc] using h
    have hσG : ((z⁻¹ * y⁻¹ * z : ↥(D.S)) : G) ∈ D.S0 := hσmem
    have hstep : ClassFunction.compHom (L33D.phiS D C hDC (z⁻¹ * y⁻¹ * z)).toMonoidHom
        (b : ClassFunction ↥(Uin C) ℂ) =
        ClassFunction.compHom (L33D.phiS D C hDC z).toMonoidHom aU := by
      rw [hs]
      ext u
      simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
      rw [← MulAut.mul_apply, ← map_mul,
        show s * (z⁻¹ * y⁻¹ * z) = z by rw [← hyz]; group]
    -- `z` is `1` or `s1`
    have ht1 : (D.t1 : G) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one D.t1
      rw [D.t1_order] at h
      exact h
    have hs1sq : s1 ^ (2 : ℤ) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, Subgroup.coe_one]
      show (D.t1 : G) ^ (2 : ℤ) = 1
      rw [zpow_ofNat]
      exact ht1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzcase : z = 1 ∨ z = s1 := by
      have h2 : s1 ^ k = s1 ^ (k % 2) := zpow_eq_zpow_emod k hs1sq
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left; rw [← hk, h2, h]; simp
      · right; rw [← hk, h2, h]; norm_num
    have hbν' : ClassFunction.inner (ClassFunction.restrict (Uin C) ν)
        (b : ClassFunction ↥(Uin C) ℂ) ≠ 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm]
      exact fun h => hbν (by simpa using congrArg (starRingEnd ℂ) h)
    have hclos := supp_restrictU_phiS_invariant D C hDC hνirr hbν' (z⁻¹ * y⁻¹ * z) hσG
    rw [hstep] at hclos
    rcases hzcase with hz1 | hzs1
    · refine Or.inl ⟨hνirr, ?_⟩
      rw [hz1] at hclos
      have hone : ClassFunction.compHom (L33D.phiS D C hDC (1 : ↥(D.S))).toMonoidHom aU = aU := by
        ext u
        simp
      rwa [hone] at hclos
    · exact Or.inr ⟨hνirr, by rw [hzs1] at hclos; exact hclos⟩
  -- `bset` multiplicities vanish
  have hbset0 : ∀ ν ∈ bset C f χ,
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν = 0 := by
    intro ν hbset
    by_contra he
    exact hΞfree ν (hsupp ν hbset.1 he) hbset
  -- `χ(t) = 0`
  have hχt0 : χ (C.t : G) = 0 := by
    obtain ⟨β, hβ⟩ := s02_lamSign C
    have hβt : lamCF C β C.t = -1 := by
      rw [lamCF_apply_t, hβ]; norm_num
    let τ : IrreducibleCharacter ↥C.P.H0 ≃ IrreducibleCharacter ↥C.P.H0 :=
      { toFun := fun μ => ⟨lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ),
          lambda_mul_irreducible C.P ⟨β, rfl⟩ μ.isIrreducible⟩
        invFun := fun μ => ⟨lamCF C β⁻¹ * (μ : ClassFunction ↥C.P.H0 ℂ),
          lambda_mul_irreducible C.P ⟨β⁻¹, rfl⟩ μ.isIrreducible⟩
        left_inv := fun μ => by
          apply IrreducibleCharacter.ext
          simp only [IrreducibleCharacter.coe_mk]
          exact badCase_lamCF_mul_cancel' C β (μ : ClassFunction ↥C.P.H0 ℂ)
        right_inv := fun μ => by
          apply IrreducibleCharacter.ext
          simp only [IrreducibleCharacter.coe_mk]
          exact badCase_lamCF_mul_cancel C β (μ : ClassFunction ↥C.P.H0 ℂ) }
    have hχt : χ (C.t : G) = ∑ μ : IrreducibleCharacter ↥C.P.H0,
        (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (μ : ClassFunction ↥C.P.H0 ℂ)) *
          ((μ : ClassFunction ↥C.P.H0 ℂ) C.t) := by
      have key : χ (C.t : G) = (∑ μ : IrreducibleCharacter ↥C.P.H0,
            (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
              (μ : ClassFunction ↥C.P.H0 ℂ)) •
              (μ : ClassFunction ↥C.P.H0 ℂ)) C.t := by
        rw [sum_inner_irreducibleCharacter_smul, ClassFunction.restrict_apply]
      conv_lhs => rw [key, badCase_sum_apply]
      exact Finset.sum_congr rfl fun μ _ => by rw [ClassFunction.smul_apply]
    have hΛinv : ∀ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ)) =
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) := by
      intro μ
      by_cases hμΞ : (μ : ClassFunction ↥C.P.H0 ℂ) ∈ Ω ∪ Ω'
      · have hlam : LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ)
            (lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ)) := ⟨β, rfl⟩
        have hfree : ∀ ξ ∈ lamOrbit C (lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ)),
            ξ ∉ bset C f χ := by
          intro ξ hξ
          refine hΞfree ξ (hΞorb _ hμΞ ?_)
          rwa [← s02c_lamOrbit_eq_of_lamEquiv C hlam] at hξ
        exact hconst _ _ (lambda_mul_irreducible C.P ⟨β, rfl⟩ μ.isIrreducible)
          μ.isIrreducible (s02c_LamEquiv_symm C hlam) hfree
      · have h0 : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (μ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
          by_contra hc
          exact hμΞ (hsupp _ μ.isIrreducible hc)
        have h0' : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
          by_contra hc
          have hmem : lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ) ∈ Ω ∪ Ω' :=
            hsupp _ (lambda_mul_irreducible C.P ⟨β, rfl⟩ μ.isIrreducible) hc
          have hback : (μ : ClassFunction ↥C.P.H0 ℂ) ∈ Ω ∪ Ω' :=
            hΞorb _ hmem ⟨β⁻¹, (badCase_lamCF_mul_cancel' C β
              (μ : ClassFunction ↥C.P.H0 ℂ)).symm⟩
          exact hμΞ hback
        rw [h0, h0']
    have hS : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
            (μ : ClassFunction ↥C.P.H0 ℂ)) *
          ((μ : ClassFunction ↥C.P.H0 ℂ) C.t)) = 0 := by
      have h1 : (∑ μ : IrreducibleCharacter ↥C.P.H0,
            (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
                (μ : ClassFunction ↥C.P.H0 ℂ)) *
              ((μ : ClassFunction ↥C.P.H0 ℂ) C.t)) =
          ∑ μ : IrreducibleCharacter ↥C.P.H0,
            (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
                ((τ μ) : ClassFunction ↥C.P.H0 ℂ)) *
              (((τ μ) : ClassFunction ↥C.P.H0 ℂ) C.t) :=
        (Equiv.sum_comp τ (fun μ : IrreducibleCharacter ↥C.P.H0 =>
          (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
              (μ : ClassFunction ↥C.P.H0 ℂ)) *
            ((μ : ClassFunction ↥C.P.H0 ℂ) C.t))).symm
      have h2 : ∀ μ : IrreducibleCharacter ↥C.P.H0,
          (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
              ((τ μ) : ClassFunction ↥C.P.H0 ℂ)) *
            (((τ μ) : ClassFunction ↥C.P.H0 ℂ) C.t) =
          -((ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
              (μ : ClassFunction ↥C.P.H0 ℂ)) *
            ((μ : ClassFunction ↥C.P.H0 ℂ) C.t)) := by
        intro μ
        have hcoe : ((τ μ) : ClassFunction ↥C.P.H0 ℂ)
            = lamCF C β * (μ : ClassFunction ↥C.P.H0 ℂ) := rfl
        rw [hcoe, hΛinv μ, ClassFunction.mul_apply, hβt]
        ring_nf
      rw [Finset.sum_congr rfl fun μ _ => h2 μ] at h1
      rw [Finset.sum_neg_distrib] at h1
      have h2S : (2 : ℂ) * (∑ μ : IrreducibleCharacter ↥C.P.H0,
          (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
              (μ : ClassFunction ↥C.P.H0 ℂ)) *
            ((μ : ClassFunction ↥C.P.H0 ℂ) C.t)) = 0 := by
        linear_combination h1
      exact (mul_eq_zero.mp h2S).resolve_left (by norm_num)
    rw [hχt, hS]
  exact ⟨Ω ∪ Ω', hΞorb, hΞfree, hsupp, hbset0, hχt0⟩

end Work.BG
