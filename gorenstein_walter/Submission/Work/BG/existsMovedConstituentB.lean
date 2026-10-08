import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.pieceAInv
import Submission.Work.BG.restrictU_single
import Submission.Work.BG.infKNormalInU
import Submission.Work.BG.rem31Shape

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

/-!
# `Work.BG.existsMovedConstituentB`

Variant of `Work.BG.existsMovedConstituent` in which the witness of the constancy hypothesis is
given directly (`∃ x ∈ K₁ ⊓ K₂, χ x ≠ χ 1`) instead of being extracted from `K₁ ⊓ K₂ ≠ ⊥` by
the character-kernel argument of `Work.BG.existsNotKerOfSimple`.

The mathematical content is the same.  The auxiliary lemma `irr_eq_one_on_infK_b` (the `D.n = 2`
case of BG 1981, Lemma 3.4's "moved constituent" step) is recorded here rather than imported from
`Work.BG.existsMovedConstituent`, whose module currently cannot be built (its import
`Work.BG.existsNotKerOfSimple` clashes with `Work.BG.L41Aux` on the name
`Work.BG.irr_apply_one_ne_zero`).
-/

/-- **Key step.**  If `μ ∈ Irr(H₀)` is `Λ`-equivalent to its `s`-conjugate
(`sconj C μ ∈ lamOrbit C μ`), then `μ` is constant `= μ 1` on `K = K₁ ⊓ K₂ ≤ U`.

Indeed `(μ^s)|_U = μ|_U` because the members of a `Λ`-orbit have the same restriction to `U`,
so `restrictU C μ` is invariant under `sigmaU C` (conjugation by `s` on `U`).  By
`restrictU_single`, `restrictU C μ = e • a` with `a ∈ Irr(U)`, `e ≠ 0`, so `a` is
`sigmaU C`-invariant; `infKNormalInU` gives that `K ◁ U` and that `sigmaU C` inverts `K`;
`pieceAInv` then gives `a k = a 1` for `k ∈ K`, whence `μ k = e * a k = e * a 1 = μ 1`. -/
private theorem irr_eq_one_on_infK_b {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Compat D C) (hHyps : ThmCHyps D K1 K2) (hn : D.n = 2)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : IsIrreducibleCharacter μ)
    (hm : sconj C μ ∈ lamOrbit C μ) :
    ∀ u : ↥C.P.U, (u : G) ∈ K1 ⊓ K2 → μ ⟨(u : G), C.P.U_le_H0 u.2⟩ = μ 1 := by
  haveI : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hle, hnorm, hσinv⟩ := infKNormalInU D C K1 K2 hComp hHyps hn
  obtain ⟨a, e, he, ha, hres⟩ := restrictU_single D C hComp hn μ hμ
  have hm' : ∃ β : quotGroup C.P →* ℂˣ, sconj C μ = lamCF C β * μ := hm
  obtain ⟨β, hβ⟩ := hm'
  have hlamU : ∀ u : ↥C.P.U, lamCF C β ⟨(u : G), C.P.U_le_H0 u.2⟩ = 1 := by
    intro u
    have hq : quotMk C.P ⟨(u : G), C.P.U_le_H0 u.2⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)).mpr (by
        rw [Subgroup.mem_subgroupOf]; exact u.2)
    rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply, hq, map_one]
    rfl
  have hpoint : ∀ u : ↥C.P.U, (restrictU C μ) u = e * a u := by
    intro u
    rw [hres, ClassFunction.smul_apply]
  have hsconj_apply : ∀ u : ↥C.P.U, (restrictU C μ) (sigmaU C u) = (restrictU C μ) u := by
    intro u
    have hkey : conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
        = (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) :=
      Subtype.ext (by rw [conjMulEquiv_apply, sigmaU_apply_coe])
    calc (restrictU C μ) (sigmaU C u)
        = μ (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) := rfl
      _ = μ (conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)) := by rw [hkey]
      _ = conjByH C.P C.s μ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := rfl
      _ = sconj C μ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := rfl
      _ = (lamCF C β * μ) (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by rw [hβ]
      _ = 1 * μ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by
            rw [ClassFunction.mul_apply, hlamU u]
      _ = μ (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) := by rw [one_mul]
      _ = (restrictU C μ) u := rfl
  have hfix : ∀ u : ↥C.P.U, a (sigmaU C u) = a u := by
    intro u
    have hEq : e * a (sigmaU C u) = e * a u := by
      rw [← hpoint (sigmaU C u), ← hpoint u]
      exact hsconj_apply u
    exact mul_left_cancel₀ he hEq
  have hσ : ∀ k ∈ (K1 ⊓ K2).subgroupOf C.P.U, sigmaU C k = k⁻¹ := by
    intro k hk
    exact hσinv k (by rwa [Subgroup.mem_subgroupOf] at hk)
  haveI : ((K1 ⊓ K2).subgroupOf C.P.U).Normal := hnorm
  have hPA := pieceAInv ((K1 ⊓ K2).subgroupOf C.P.U) (odd_card_U_of_compat hComp)
    (sigmaU C) hσ a ha hfix
  intro u hu
  have hu' : u ∈ (K1 ⊓ K2).subgroupOf C.P.U := by
    rw [Subgroup.mem_subgroupOf]; exact hu
  have hkey := hPA u hu'
  calc μ ⟨(u : G), C.P.U_le_H0 u.2⟩
      = (restrictU C μ) u := by rw [restrictU_apply]
    _ = e * a u := hpoint u
    _ = e * a 1 := by rw [hkey]
    _ = (restrictU C μ) 1 := (hpoint 1).symm
    _ = μ 1 := by rw [restrictU_apply]; rfl

theorem existsMovedConstituentB {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) :
    Work.GW2.C16.Compat D C → Work.GW2.C16.ThmCHyps D K1 K2 → IsSimpleGroup G → D.n = 2 →
    Work.GW2.C16.IsCoherent C f → Work.BG.IsPmIrr χ →
    OddOrder.RepresentationTheory.ClassFunction.inner χ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 0 →
    (∃ x ∈ K1 ⊓ K2, χ x ≠ χ 1) →
    ∃ μ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter μ ∧
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) μ ≠ 0 ∧
      Work.BG.sconj C μ ∉ Work.BG.lamOrbit C μ := by
  intro hComp hHyps hSimple hn hf hχ horth hx
  -- Suppose every irreducible constituent of `χ|_{H₀}` is `Λ`-conjugate to its `s`-conjugate.
  -- Then (by `irr_eq_one_on_infK_b`) each such constituent is constant `= μ 1` on `K = K₁ ⊓ K₂`,
  -- so the Fourier expansion `χ|_{H₀} = ∑ μ (χ|_{H₀}, μ) μ` gives `χ k = χ 1` for all
  -- `k ∈ K₁ ⊓ K₂`, contradicting the hypothesis.
  by_contra hcon
  have hcon' : ∀ μ : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter μ →
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) μ ≠ 0 →
      sconj C μ ∈ lamOrbit C μ := by
    intro μ hμ hinner
    by_contra hnot
    exact hcon ⟨μ, hμ, hinner, hnot⟩
  obtain ⟨k, hkK, hkne⟩ := hx
  obtain ⟨hle, -, -⟩ := infKNormalInU D C K1 K2 hComp hHyps hn
  have hkU : k ∈ C.P.U := hle hkK
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := by
    haveI := finite_irreducibleCharacter (G := ↥C.P.H0)
    exact Fintype.ofFinite _
  have hexp := sum_inner_irreducibleCharacter_smul (ClassFunction.restrict C.P.H0 χ)
  have hsum_k : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) •
          (μ : ClassFunction ↥C.P.H0 ℂ)) (⟨k, C.P.U_le_H0 hkU⟩ : ↥C.P.H0)
      = ∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) *
          (μ : ClassFunction ↥C.P.H0 ℂ) (⟨k, C.P.U_le_H0 hkU⟩ : ↥C.P.H0) := by
    rw [ClassFunction.sum_apply]
    exact Finset.sum_congr rfl (fun μ _ => by rw [ClassFunction.smul_apply])
  have hsum_1 : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) •
          (μ : ClassFunction ↥C.P.H0 ℂ)) (1 : ↥C.P.H0)
      = ∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) *
          (μ : ClassFunction ↥C.P.H0 ℂ) (1 : ↥C.P.H0) := by
    rw [ClassFunction.sum_apply]
    exact Finset.sum_congr rfl (fun μ _ => by rw [ClassFunction.smul_apply])
  have hterms : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) *
          (μ : ClassFunction ↥C.P.H0 ℂ) (⟨k, C.P.U_le_H0 hkU⟩ : ↥C.P.H0))
      = ∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) *
          (μ : ClassFunction ↥C.P.H0 ℂ) (1 : ↥C.P.H0) := by
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    by_cases hc : ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
        (μ : ClassFunction ↥C.P.H0 ℂ) = 0
    · rw [hc, zero_mul, zero_mul]
    · have hm : sconj C (μ : ClassFunction ↥C.P.H0 ℂ) ∈
          lamOrbit C (μ : ClassFunction ↥C.P.H0 ℂ) :=
        hcon' (μ : ClassFunction ↥C.P.H0 ℂ) μ.isIrreducible hc
      have hval := irr_eq_one_on_infK_b D C K1 K2 hComp hHyps hn μ.isIrreducible hm
        (⟨k, hkU⟩ : ↥C.P.U) hkK
      rw [hval]
  have hk_eval : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) •
          (μ : ClassFunction ↥C.P.H0 ℂ)) (⟨k, C.P.U_le_H0 hkU⟩ : ↥C.P.H0) = χ k := by
    rw [hexp, ClassFunction.restrict_apply]
  have h1_eval : (∑ μ : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (μ : ClassFunction ↥C.P.H0 ℂ) •
          (μ : ClassFunction ↥C.P.H0 ℂ)) (1 : ↥C.P.H0) = χ 1 := by
    rw [hexp, ClassFunction.restrict_apply]
    rfl
  have hχk : χ k = χ 1 := by
    rw [← hk_eval, ← h1_eval, hsum_k, hsum_1, hterms]
  exact hkne hχk

end Work.BG
