import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Torus.conj_eq_inv_of_mem_cent
import Submission.Work.L2F.Props.oddsub.NoUnipotentDefs
import Submission.Work.L2F.Props.oddsub.trace_det_eq_zero_of_mul_self_eq_zero
import Submission.Work.L2F.Props.oddsub.sq_eq_one_of_unipotent_of_two_eq_zero
import Submission.Work.L2F.Props.oddsub.unipotent_sq_eq_one_add_nilpotent
import Submission.Work.L2F.Props.oddsub.det_ne_zero_of_mem_matCent
import Submission.Work.L2F.Props.oddsub.eq_or_trace_sub_of_commute_of_mem_matCent

/-!
# A normal abelian irreducible subgroup of odd order rules out unipotent elements

Let `F` be a field, `A ≤ L ≤ SL(2,F)` with `A` normal in `L`, `A` abelian and *irreducible*
(`A` has no common eigenvector in `F²`, i.e. `F²` is a simple `F[A]`-module), and suppose that
every element of `L` has odd order.  Then `L` contains no unipotent element.

## Proof

Let `g ∈ L` be unipotent, say `g = λ·1 + N` with `N ≠ 0`, `N² = 0`.  Since `g ∈ SL(2,F)` and
`(λ·1+N).det = λ²` (the nilpotent part has vanishing trace and determinant), we get `λ² = 1`.

* In characteristic `2`, `λ = 1` and `g² = 1` with `g ≠ 1`, so `g` has order `2`, contradicting
  the oddness hypothesis.

* Otherwise `λ = ±1`, so `g² = 1 + 2λ·N` is again unipotent, and it suffices to show that `g²`
  commutes with `A`: then the nonzero nilpotent `N' = g² - 1` lies in the commutant of `A` and has
  vanishing determinant, contradicting the fact (`hirr`) that every nonzero matrix commuting with
  `A` is invertible.

  For `a ∈ A`, the conjugate `b = g a g⁻¹` again lies in `A` (normality) and commutes with `a`
  (`A` abelian), and has the same trace and determinant as `a`.  As `A` is irreducible, the
  differences `b - a` and `b - (tr a·1 - a)` are elements of the commutant, so that Cayley–Hamilton
  together with the trace and determinant conditions yields the dichotomy
  `b = a` or `b = tr(a)·1 - a`.  In either case `g² a g⁻² = (g b g⁻¹) = a`.
-/

set_option linter.unusedVariables false

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

theorem no_unipotent_of_normal_abelian_irreducible (F : Type*) [Field F]
    (L A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hAL : A ≤ L)
    (hAnorm : (A.subgroupOf L).Normal)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAne : A ≠ ⊥)
    (hirr : ¬ ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ a ∈ A,
        ∃ c : F, Matrix.mulVec ((a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v = c • v)
    (hoddL : ∀ l ∈ L, Odd (orderOf l)) :
    ¬ ∃ g ∈ L, Work.L2F.Props.UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have hnoce : ¬ HasCommonEigenvector A := hirr
  have hinv : ∀ M : Matrix (Fin 2) (Fin 2) F, MatCent A M → M ≠ 0 → M.det ≠ 0 :=
    fun M hM hM0 => det_ne_zero_of_mem_matCent F A hnoce hM hM0
  -- elements of `A` commute with `A`
  have hcentA : ∀ a ∈ A,
      MatCent A ((a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro a ha b hb
    have h := hAab a ha b hb
    have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
      (z : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.SpecialLinearGroup.coe_mul] using h'
  rintro ⟨g, hgL, hunip⟩
  set gm : Matrix (Fin 2) (Fin 2) F :=
    ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hgm
  have hdetg : gm.det = 1 := by rw [hgm]; exact Matrix.SpecialLinearGroup.det_coe g
  have hunipD : Work.L2F.Props.UnipotentMatrix gm := by rw [hgm]; exact hunip
  obtain ⟨lam, hNne, hNsq⟩ := hunipD
  have hunit : IsUnit gm := by
    rw [Matrix.isUnit_iff_isUnit_det, hdetg]; exact isUnit_one
  have hginv : gm⁻¹ * gm = 1 := Matrix.nonsing_inv_mul gm (by rw [hdetg]; exact isUnit_one)
  -- the "eigenvalue" `lam` of a unipotent element of `SL(2,F)` satisfies `lam ^ 2 = 1`
  have hlam2 : lam ^ 2 = 1 := by
    have h := Work.L2F.Mat2.det_smul_one_add_smul F (gm - lam • 1) lam 1
    rw [one_smul] at h
    obtain ⟨htrN, hdetN⟩ := trace_det_eq_zero_of_mul_self_eq_zero F (gm - lam • 1) hNsq
    rw [show lam • (1 : Matrix (Fin 2) (Fin 2) F) + (gm - lam • 1) = gm from by abel,
      hdetg] at h
    simp only [htrN, hdetN] at h
    simpa using h.symm
  by_cases h2 : (2 : F) = 0
  · -- characteristic two: `g * g = 1` and `g ≠ 1`, so `g` has order `2`
    obtain ⟨hgg, hgne⟩ := sq_eq_one_of_unipotent_of_two_eq_zero F h2 gm hunip hdetg
    have hg2 : g ^ 2 = 1 := by
      rw [pow_two]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hgm, hgg, Matrix.SpecialLinearGroup.coe_one]
    have hg1 : g ≠ 1 := by
      intro h
      refine hgne ?_
      rw [hgm, h, Matrix.SpecialLinearGroup.coe_one]
    have hord : orderOf g = 2 :=
      orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) hg2 hg1
    have hodd := hoddL g hgL
    rw [hord] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  · -- odd characteristic: `g ^ 2` is unipotent and commutes with `A`
    obtain ⟨N, hN0, hNsq', hgg⟩ := unipotent_sq_eq_one_add_nilpotent F h2 gm hunip hdetg
    have hggcent : MatCent A (gm * gm) := by
      intro a ha
      set aM : Matrix (Fin 2) (Fin 2) F :=
        ((a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with haM
      set b : Matrix.SpecialLinearGroup (Fin 2) F := g * a * g⁻¹ with hbdef
      have hbA : b ∈ A := (Subgroup.normal_subgroupOf_iff hAL).mp hAnorm a g ha hgL
      set bM : Matrix (Fin 2) (Fin 2) F :=
        ((b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hbM
      have hbmat : bM = gm * aM * gm⁻¹ := by
        rw [hbM, hbdef, haM, hgm, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_mul, Work.L2F.Torus.coe_inv_sl]
      have hcomm : bM * aM = aM * bM := by
        have h := hAab b hbA a ha
        have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
          (z : Matrix (Fin 2) (Fin 2) F)) h
        simpa [hbM, haM, Matrix.SpecialLinearGroup.coe_mul] using h'
      have htr : aM.trace = bM.trace := by rw [hbmat, Matrix.trace_conj hunit]
      have hdet : aM.det = bM.det := by rw [hbmat, Matrix.det_conj hunit]
      have hD := eq_or_trace_sub_of_commute_of_mem_matCent F A (hcentA a ha)
        (hcentA b hbA) hcomm htr hdet hinv
      have hD' : bM = aM ∨ bM = aM.trace • (1 : Matrix (Fin 2) (Fin 2) F) - aM := hD
      have hgm_aM : gm * aM = bM * gm := by
        rw [hbmat, mul_assoc, hginv, mul_one]
      have hgm_bM : gm * bM = aM * gm := by
        rcases hD' with hD | hD
        · rw [hD]
          exact hgm_aM.trans (congrArg (fun X => X * gm) hD)
        · have h1 : gm * bM = aM.trace • gm - gm * aM := by
            rw [hD, mul_sub, Matrix.mul_smul, mul_one]
          have h2 : bM * gm = aM.trace • gm - aM * gm := by
            rw [hD, sub_mul, Matrix.smul_mul, one_mul]
          rw [h1, hgm_aM, h2]
          abel
      calc gm * gm * aM = gm * (gm * aM) := by rw [mul_assoc]
        _ = gm * (bM * gm) := by rw [hgm_aM]
        _ = (gm * bM) * gm := by rw [mul_assoc]
        _ = (aM * gm) * gm := by rw [hgm_bM]
        _ = aM * (gm * gm) := by rw [mul_assoc]
    have hNcent : MatCent A N := by
      have hNeq : N = gm * gm - 1 := by rw [hgg]; abel
      rw [hNeq]
      intro a ha
      rw [sub_mul, mul_sub, hggcent a ha]
      simp
    have hNdet : N.det = 0 := (trace_det_eq_zero_of_mul_self_eq_zero F N hNsq').2
    exact hinv N hNcent hN0 hNdet

end Work.L2F.Props.oddsub
