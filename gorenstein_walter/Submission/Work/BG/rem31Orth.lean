import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_lemma21Ext
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_orbitSumVanish
import Submission.Work.BG.s02_quot_data
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.rem31Gallagher
import Submission.Work.BG.rem31CardFiber
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31IndexUin

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem rem31Orth {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)] :
    Work.GW2.C16.Rem31OrthProp D C := by
  classical
  intro hDC μ ν hμ hν
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Nonempty ↥C.P.H0 := ⟨1⟩
  haveI : Invertible (Nat.card ↥C.P.H0 : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (lamDual C) := Fintype.ofFinite _
  -- `|Λ| = [H₀ : U]`, the dual of the finite (cyclic) group `H₀/U`
  have hcard_dual : Nat.card (lamDual C) = (Uin C).index := rem31LamDualCard C
  -- **Gallagher**: `Ind_U^{H₀}(ν|_U) = ∑_{λ ∈ Λ} λν`
  have hInd : ClassFunction.induce (Uin C) (ClassFunction.restrict (Uin C) ν)
      = ∑ β : lamDual C, lamCF C β * ν := by
    have hone : ClassFunction.restrict (Uin C) ν * trivialClassFunction ↥(Uin C)
        = ClassFunction.restrict (Uin C) ν := by
      ext g
      simp [ClassFunction.mul_apply]
    rw [← hone, ClassFunction.induce_restrict_mul, rem31Gallagher C hcard_dual, lambdaSum]
    ext g
    simp only [ClassFunction.mul_apply, ClassFunction.sum_apply, lamCF,
      ClassFunction.compHom_apply, linearClassFunction_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => mul_comm _ _
  -- **orthonormality**: `(μ, ∑_β λ_βν) = #{β : λ_βν = μ}`
  have htwist : ClassFunction.inner μ (∑ β : lamDual C, lamCF C β * ν)
      = (Fintype.card {β : lamDual C // lamCF C β * ν = μ} : ℂ) := by
    rw [inner_sum_right]
    have hterm : ∀ β : lamDual C, ClassFunction.inner μ (lamCF C β * ν)
        = if lamCF C β * ν = μ then (1 : ℂ) else 0 := by
      intro β
      have hβirr : lamCF C β * ν ∈ irreducibleCharacters ↥C.P.H0 :=
        lambda_mul_irreducible C.P ⟨β, rfl⟩ hν
      rw [irr_cf_inner hμ hβirr]
      by_cases hb : lamCF C β * ν = μ
      · rw [ite_eq_left hb.symm, ite_eq_left hb]
      · rw [ite_eq_right (fun h => hb h.symm), ite_eq_right hb]
    rw [Finset.sum_congr rfl fun β _ => hterm β]
    rw [Finset.sum_boole, Fintype.card_subtype]
  -- Frobenius reciprocity + star-symmetry
  have hfib : ClassFunction.inner (ClassFunction.restrict (Uin C) μ)
        (ClassFunction.restrict (Uin C) ν)
      = (Fintype.card {β : lamDual C // lamCF C β * ν = μ} : ℂ) := by
    rw [ClassFunction.inner_star_comm]
    rw [← ClassFunction.inner_induce_eq_inner_restrict (Uin C)
      (ClassFunction.restrict (Uin C) ν) μ, hInd]
    rw [ClassFunction.inner_star_comm, star_star, htwist]
  -- the orbit of `ν` is nonempty, hence `|Λν| ≠ 0`
  have hfin : (lamOrbit C ν).Finite := by
    rw [← orbit_eq_lamOrbit C ν]
    exact Set.finite_range fun β : lamDual C => β • ν
  have hm : ((lamOrbit C ν).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Set.ncard_ne_zero_of_mem (s02c_LamEquiv_refl C ν) hfin)
  constructor
  · intro hμν
    have hmul : Fintype.card {β : lamDual C // lamCF C β * ν = μ} * (lamOrbit C ν).ncard
        = D.n := by
      rw [← Nat.card_eq_fintype_card, rem31CardFiber C hμν, rem31StabCard C ν,
        rem31IndexUin D C hDC]
    rw [hfib, eq_div_iff hm, ← Nat.cast_mul, hmul]
  · intro hμν
    have hzero : Fintype.card {β : lamDual C // lamCF C β * ν = μ} = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun β => hμν (s02c_LamEquiv_symm C ⟨β.1, β.2.symm⟩)⟩
    rw [hfib, hzero, Nat.cast_zero]

end Work.BG
