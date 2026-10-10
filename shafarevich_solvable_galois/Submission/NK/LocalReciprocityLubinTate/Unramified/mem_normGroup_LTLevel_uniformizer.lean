import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RingTheory.Valuation.eq_of_comap_eq_of_isAlgebraic
import Submission.Commons.RingTheory.Valuation.val_eq_of_algEquiv_of_comap_eq
import Submission.NK.LocalReciprocityLubinTate.LubinTate.norm_root_LTpolyEis
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

/-! ### Plan for the prover

**A uniformiser is a norm from every Lubin–Tate level**, i.e. the `⟨π⟩` half of Honda's reciprocity
law `N_{K_n/F}K_nˣ = ⟨π⟩·U^n` at every level `n ≥ 1`.

The proof is the direct generalisation of the level-one argument of
`Submission/Work/LocalReciprocityLubinTate/Unramified/normGroup_LTLevel_one_adicCompletion.lean`:
a root `y` of the Eisenstein factor `f^{[n-1]}(T) = f^{(n-1)}(T)^{q-1} + π` is a `π^n`-division
point (`LTpolyIter_succ_eq_mul`), its minimal polynomial is `f^{[n-1]}` of degree `(q-1)q^{n-1}`
(`irreducible_LTpolyEis`, `finrank_adjoin_root_LTpolyEis`), so `F(y)` has the same degree as the
level `K_n = F(Λ_n) = F(π_n)` (`finrank_LTLevel_eq_of_isUniformizer`) and hence `F(y) = K_n`.
Transporting `Nm(y) = (-1)^{(q-1)q^{n-1}} π` (`norm_root_LTpolyEis`) along the resulting
`F`-algebra isomorphism, the element `-y` has norm exactly `π`: the sign is a norm because
`Nm(-1) = (-1)^{[K_n:F]} = (-1)^{(q-1)q^{n-1}}`. -/

open Polynomial

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-- **A uniformiser is a norm from every Lubin–Tate level** (Honda's reciprocity law, the `⟨π⟩`
half): for `q = residueCard F` and every `n ≥ 1`,

  `π ∈ N_{K_n/F} K_nˣ`,  `K_n = F(Λ_n)`.

Stated in the shifted form `K_{m+1} = F(π_{m+1})` so that the Eisenstein factor involved is
`f^{[m]}`. -/
theorem mem_normGroup_LTLevel_succ_of_isUniformizer (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : IsUniformizer F (πu : F)) (m : ℕ) :
    πu ∈ NK.LocalReciprocity.normGroup F
      ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) := by
  classical
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  have hq1 : 1 ≤ residueCard F := by omega
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F πu hπ
  have hirr : Irreducible (LTpolyEis (πu : F) (residueCard F) m) := by
    rw [← hPcoe]
    exact irreducible_LTpolyEis F P hPirr (residueCard F) m hq2
  obtain ⟨hmon, hnat, -⟩ :=
    LubinTate.LTpolyEis_monic_natDegree_coeff_zero (πu : F) (residueCard F) m hq2
  have hdeg : (LTpolyEis (πu : F) (residueCard F) m).degree ≠ 0 := by
    have hpos : 0 < (LTpolyEis (πu : F) (residueCard F) m).natDegree := by
      rw [hnat]
      exact Nat.mul_pos (by omega) (pow_pos (by omega) m)
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨y, hy⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F)
      (LTpolyEis (πu : F) (residueCard F) m) hdeg
  -- `y` is a `π^{m+1}`-division point
  have hymem : y ∈ LTdivisionSet F (πu : F) (residueCard F) (m + 1) := by
    rw [mem_LTdivisionSet_iff (πu : F) (residueCard F) (m + 1) hq2,
      LTpolyIter_succ_eq_mul (πu : F) (residueCard F) m hq1, Polynomial.aeval_mul, hy, zero_mul]
  -- its minimal polynomial is the Eisenstein factor
  have hmin : minpoly F y = LTpolyEis (πu : F) (residueCard F) m :=
    (minpoly.eq_of_irreducible_of_monic hirr hy hmon).symm
  -- hence `F(y) = K_{m+1}`
  haveI : FiniteDimensional F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) :=
    LubinTate.finiteDimensional_LTLevel F (πu : F) (residueCard F) (m + 1) hq2
  have hspan : IntermediateField.adjoin F ({y} : Set (AlgebraicClosure F)) =
      LTLevel F (πu : F) (residueCard F) (m + 1) := by
    refine IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr
        (LTdivisionSet_subset_LTLevel F (πu : F) (residueCard F) (m + 1) hymem)) ?_
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y), hmin, hnat,
      finrank_LTLevel_eq_of_isUniformizer F πu hπ (m + 1) (by omega)]
    simp
  obtain ⟨e⟩ : Nonempty (AdjoinRoot (LTpolyEis (πu : F) (residueCard F) m) ≃ₐ[F]
      ↥(LTLevel F (πu : F) (residueCard F) (m + 1))) :=
    ⟨(hmin ▸ IntermediateField.adjoinRootEquivAdjoin F (Algebra.IsIntegral.isIntegral y)).trans
      (IntermediateField.equivOfEq hspan)⟩
  haveI hfree : Module.Free F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) :=
    Module.Free.of_divisionRing F ↥(LTLevel F (πu : F) (residueCard F) (m + 1))
  -- the norm of the root, transported to the level
  have hnormroot : Algebra.norm F
      (e (AdjoinRoot.root (LTpolyEis (πu : F) (residueCard F) m))) =
      (-1) ^ ((residueCard F - 1) * residueCard F ^ m) * (πu : F) := by
    rw [Algebra.norm_eq_of_algEquiv e, ← hPcoe]
    simpa using LubinTate.norm_root_LTpolyEis F P hPirr (residueCard F) m hq2
  have hfd : Module.finrank F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) =
      (residueCard F - 1) * residueCard F ^ m := by
    rw [finrank_LTLevel_eq_of_isUniformizer F πu hπ (m + 1) (by omega)]
    simp
  have hnormneg : Algebra.norm F
      (algebraMap F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) (-1)) =
      (-1 : F) ^ ((residueCard F - 1) * residueCard F ^ m) := by
    rw [Algebra.norm_algebraMap, hfd]
  have hprod : Algebra.norm F
      (algebraMap F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) (-1) *
        e (AdjoinRoot.root (LTpolyEis (πu : F) (residueCard F) m))) = (πu : F) := by
    rw [map_mul, hnormneg, hnormroot]
    have h2 : (-1 : F) ^ ((residueCard F - 1) * residueCard F ^ m) *
        (-1 : F) ^ ((residueCard F - 1) * residueCard F ^ m) = 1 := by
      rw [← pow_add]
      have hcast : (residueCard F - 1) * residueCard F ^ m +
          (residueCard F - 1) * residueCard F ^ m =
          2 * ((residueCard F - 1) * residueCard F ^ m) := by ring
      rw [hcast, pow_mul, neg_one_sq, one_pow]
    rw [← mul_assoc, h2, one_mul]
  have hne : algebraMap F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) (-1) *
      e (AdjoinRoot.root (LTpolyEis (πu : F) (residueCard F) m)) ≠ 0 := by
    intro h0
    have hzero : Algebra.norm F
        (algebraMap F ↥(LTLevel F (πu : F) (residueCard F) (m + 1)) (-1) *
          e (AdjoinRoot.root (LTpolyEis (πu : F) (residueCard F) m))) = 0 := by
      rw [h0, Algebra.norm_zero]
    rw [hprod] at hzero
    exact Units.ne_zero πu hzero
  refine (NK.LocalReciprocity.mem_normGroup_iff πu).mpr ⟨Units.mk0 _ hne, ?_⟩
  exact hprod

theorem mem_normGroup_LTLevel_uniformizer (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (n : ℕ) (hn : 1 ≤ n) :
    πu ∈ NK.LocalReciprocity.normGroup F
      ↥(NK.LocalReciprocityLubinTate.LTLevel F (πu : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n) := by
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← hn']
  exact mem_normGroup_LTLevel_succ_of_isUniformizer F πu hπ (n - 1)

end

end NK.LocalReciprocityLubinTate.Unramified
