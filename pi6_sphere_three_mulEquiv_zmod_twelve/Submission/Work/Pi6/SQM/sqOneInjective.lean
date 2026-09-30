import Mathlib
import Submission.Work.Pi6.SQM.SqOneDefs
import Submission.Work.Pi6.SQM.SqOnePointwise
import Submission.Work.Pi6.SQM.cochainClassEqZero
import Submission.Work.Pi6.SQM.deltaHalf_spec
import Submission.Work.Pi6.SQM.redChain_d
import Submission.Work.Pi6.SQM.redChain_surjective
import Submission.Work.Pi6.SQM.redChain_eq_zero
import Submission.Work.Pi6.SQM.redChainKernel
import Submission.Work.SSS.E2Zero.homologypi_eq_zero_iff
import Submission.Work.RatHurewicz.Bridge.HomologyAux
import Submission.Work.Cohomology.kronH_bijective_field
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Sq¹` is injective on `H²` when `H₁(X;ℤ) = 0` and `2 · H₂(X;ℤ) = 0`

For a space `X` with `H₁(X;ℤ) = 0` (so that mod-2 cycles lift to integral cycles and the mod-2
reduction on `H₂` is onto) and `2 · H₂(X;ℤ) = 0`, the mod-2 Steenrod square
`Sq¹ : H²(X;𝔽₂) → H³(X;𝔽₂)`, which on a `2`-cocycle `x` is the cup-1 square `x ∪₁ x`, is
injective.

The argument (Toda, *Composition methods*, §2 of `REFS/NOTES_LEAD_SQM.md`): let `x` be a mod-2
`2`-cocycle with `[x ∪₁ x] = 0`, say `x ∪₁ x = δw`.  Let `x̃ = liftZ X 2 x` be the `0/1` lift of
`x`.  The pointwise identity `(x ∪₁ x)(σ) ≡ ((δx̃)(σ))/2` (`pointwiseSqOne`) says that the
half-coboundary cochain `deltaHalf X x` of `SqOneDefs` has the same reduction mod `2` as
`δ(liftZ X 2 w)`; since `δ(liftZ X 2 w) = δw̃` and `δw = x ∪₁ x`, the two cochains are the halves
of `δx̃` and of `δw̃` (`deltaHalf_spec`).

Now let `z` be a mod-2 `2`-cycle and lift it to an integral chain `C₀`
(`redChain_surjective`) with `∂C₀ = 2t` (`redChain_d`, `redChain_eq_zero`).  Since `t` is an
integral `1`-cycle and `H₁(X;ℤ) = 0`, `t = ∂s`, so `C := C₀ - 2s` is an integral `2`-cycle reducing
to `z` (`redChain_d` again).  Since `2 · H₂(X;ℤ) = 0`, `2C` is a boundary, `2C = ∂e`.  Pairing:
`x z = (x̃ C mod 2)` (`pairingRedC`), and
`2 (x̃ C) = x̃ (2C) = x̃ (∂e) = (δx̃) e = 2 (deltaHalf x)(e)`, so `x̃ C = (deltaHalf x)(e)`; finally
`(deltaHalf x)(e) ≡ (δw̃)(e) = w̃ (∂e) = 2 (w̃ C) ≡ 0 mod 2`.  Hence `x` pairs to zero with every
mod-2 `2`-cycle, and field duality (`kronH_bijective_field`) gives `[x] = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf cocycleOf genElt chainC
  genEval_ext)

/-- In a module over `ZMod 2`, the integer `2` acts by zero. -/
theorem two_zsmul_eq_zero' {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (y : M) :
    (2 : ℤ) • y = 0 := by
  have h : (((2 : ℤ)) : ZMod 2) = 0 := by decide
  rw [← Int.cast_smul_eq_zsmul (ZMod 2) 2 y, h, zero_smul]

/-- **`Sq¹` is injective on `H²`** when `H₁(X;ℤ) = 0` and `2 · H₂(X;ℤ) = 0`. -/
theorem sqOneInjective : Work.Pi6.SQM.SqOneInjective := by
  intro X _ hH1 hH2 x hx hxx hcls
  obtain ⟨w, hw⟩ := exists_cochainDiff_eq_of_class_eq_zero
    (y := Work.Pi6.SQ.cup1m (SX X) 2 2 x x) hxx hcls
  -- `deltaHalf x` and `δ(liftZ X 2 w)` have the same reduction mod `2`
  have hred : redC (SX X) 3 (deltaHalf (SX X) x)
      = redC (SX X) 3 (cochainDiff ℤ (SX X) (liftZ (SX X) 2 w)) := by
    apply genEval_ext
    intro σ
    simp only [genEval_redC]
    rw [pointwiseSqOne (SX X) x σ, ← genEval_redC, redC_cochainDiff, redC_liftZ, hw]
  -- the key chain-level statement
  have key : ∀ z : ↥((chainC F2 (SX X)).X 2), ((chainC F2 (SX X)).d 2 1).hom z = 0 → x z = 0 := by
    intro z hz
    obtain ⟨C₀, hC₀⟩ := redChain_surjective (SX X) 2 z
    have h1 : redChain (SX X) 1 (((chainC ℤ (SX X)).d 2 1).hom C₀) = 0 := by
      rw [redChain_d, hC₀, hz]
    obtain ⟨t, ht⟩ := redChain_eq_zero (SX X) 1 _ h1
    -- `t` is an integral `1`-cycle
    have htcyc : ((chainC ℤ (SX X)).d 1 0).hom t = 0 := by
      have hdd : ((chainC ℤ (SX X)).d 1 0).hom (((chainC ℤ (SX X)).d 2 1).hom C₀) = 0 := by
        have h := HomologicalComplex.d_comp_d (C := chainC ℤ (SX X)) 2 1 0
        exact congrArg (fun (g : (chainC ℤ (SX X)).X 2 ⟶ (chainC ℤ (SX X)).X 0) => g.hom C₀) h
      rw [ht, map_zsmul] at hdd
      exact (redChainKernel (Y := SX X) 0).2 (((chainC ℤ (SX X)).d 1 0).hom t) hdd
    -- `t` is a boundary, since `H₁(X;ℤ) = 0`
    have hzt0 : ((chainC ℤ (SX X)).homologyπ 1)
        (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 1 (by norm_num) t htcyc) = 0 :=
      @Subsingleton.elim _ hH1
        (((chainC ℤ (SX X)).homologyπ 1)
          (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 1 (by norm_num) t htcyc)) 0
    obtain ⟨s, hs⟩ := (Work.SSS.E2Zero.homologypi_eq_zero_iff 1
      (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 1 (by norm_num) t htcyc)).mp hzt0
    have hs' : ((chainC ℤ (SX X)).d 2 1).hom s = t := by
      rw [hs, Work.RatHurewicz.Bridge.iCycles_cycleOf]
    -- `C = C₀ - 2s` is an integral cycle reducing to `z`
    let C : ↥((chainC ℤ (SX X)).X 2) := C₀ - (2 : ℤ) • s
    have hCcyc : ((chainC ℤ (SX X)).d 2 1).hom C = 0 := by
      simp only [C, map_sub, map_zsmul, ht, hs', sub_self]
    have hCred : redChain (SX X) 2 C = z := by
      have h2 : redChain (SX X) 2 ((2 : ℤ) • s) = 0 := by
        rw [map_zsmul]
        exact two_zsmul_eq_zero' _
      simp only [C, map_sub, h2, hC₀, sub_zero]
    -- `2C` is a boundary, since `2 · H₂(X;ℤ) = 0`
    have hcyc2 : ((chainC ℤ (SX X)).d 2 1).hom ((2 : ℤ) • C) = 0 := by
      rw [map_zsmul, hCcyc, two_zsmul, add_zero]
    have h2cl : (2 : ℤ) • ((chainC ℤ (SX X)).homologyπ 2
        (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 2 (by norm_num) C hCcyc)) = 0 :=
      hH2 _
    have hzeq : Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 2 (by norm_num) ((2 : ℤ) • C) hcyc2
        = (2 : ℤ) • (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 2 (by norm_num) C hCcyc) := by
      apply (ModuleCat.mono_iff_injective ((chainC ℤ (SX X)).iCycles 2)).mp inferInstance
      rw [Work.RatHurewicz.Bridge.iCycles_cycleOf (chainC ℤ (SX X)) 2 (by norm_num) ((2 : ℤ) • C)
          hcyc2,
        map_zsmul,
        Work.RatHurewicz.Bridge.iCycles_cycleOf (chainC ℤ (SX X)) 2 (by norm_num) C hCcyc]
    have h2C : ((chainC ℤ (SX X)).homologyπ 2)
        (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 2 (by norm_num) ((2 : ℤ) • C) hcyc2)
        = 0 := by
      rw [hzeq, map_zsmul, h2cl]
    obtain ⟨e, he⟩ := (Work.SSS.E2Zero.homologypi_eq_zero_iff 2
      (Work.RatHurewicz.Bridge.cycleOf (chainC ℤ (SX X)) 2 (by norm_num) ((2 : ℤ) • C)
        hcyc2)).mp h2C
    rw [Work.RatHurewicz.Bridge.iCycles_cycleOf] at he
    -- `he : ∂e = 2C`
    have hpair1 : x z = (((liftZ (SX X) 2 x) C : ℤ) : F2) := by
      have h := pairingRedC (SX X) 2 (liftZ (SX X) 2 x) C
      rw [redC_liftZ, hCred] at h
      exact h.symm
    have hpair2 : ((liftZ (SX X) 2 x) C : ℤ) = ((deltaHalf (SX X) x) e : ℤ) := by
      have h1 : (2 : ℤ) • ((liftZ (SX X) 2 x) C)
          = (2 : ℤ) • ((deltaHalf (SX X) x) e) := by
        calc (2 : ℤ) • ((liftZ (SX X) 2 x) C)
            = (liftZ (SX X) 2 x) ((2 : ℤ) • C) := by rw [map_zsmul]
          _ = (liftZ (SX X) 2 x) (((chainC ℤ (SX X)).d 3 2).hom e) := by rw [he]
          _ = (cochainDiff ℤ (SX X) (liftZ (SX X) 2 x)) e := rfl
          _ = ((2 : ℤ) • deltaHalf (SX X) x) e := by rw [deltaHalf_spec (SX X) x hx]
          _ = (2 : ℤ) • ((deltaHalf (SX X) x) e) := by rw [LinearMap.smul_apply]
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (by simpa [zsmul_eq_mul] using h1)
    have hpair3 : (((deltaHalf (SX X) x) e : ℤ) : F2) = 0 := by
      have hδ : ((cochainDiff ℤ (SX X) (liftZ (SX X) 2 w)) e : ℤ)
          = 2 * ((liftZ (SX X) 2 w) C) := by
        calc ((cochainDiff ℤ (SX X) (liftZ (SX X) 2 w)) e : ℤ)
            = (liftZ (SX X) 2 w) (((chainC ℤ (SX X)).d 3 2).hom e) := rfl
          _ = (liftZ (SX X) 2 w) ((2 : ℤ) • C) := by rw [he]
          _ = 2 * ((liftZ (SX X) 2 w) C) := by rw [map_zsmul, zsmul_eq_mul]; ring
      rw [pairingRedC (SX X) 3 (deltaHalf (SX X) x) e, hred,
        ← pairingRedC (SX X) 3 (cochainDiff ℤ (SX X) (liftZ (SX X) 2 w)) e, hδ]
      rw [Int.cast_mul, show (((2 : ℤ)) : F2) = 0 from by decide, zero_mul]
    calc x z = (((liftZ (SX X) 2 x) C : ℤ) : F2) := hpair1
      _ = (((deltaHalf (SX X) x) e : ℤ) : F2) := by rw [hpair2]
      _ = 0 := hpair3
  -- field duality
  apply (Work.Cohomology.kronH_bijective_field F2 (SX X) 2).1
  rw [map_zero]
  ext c
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((chainC F2 (SX X)).homologyπ 2)).mp inferInstance c
  rw [Work.Cohomology.kronH_apply]
  refine key _ ?_
  have h2 := congrArg (fun (g : (chainC F2 (SX X)).cycles 2 ⟶ (chainC F2 (SX X)).X 1) =>
    g.hom z) (HomologicalComplex.iCycles_d (chainC F2 (SX X)) 2 1)
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  exact h2

end

end Work.Pi6.SQM
