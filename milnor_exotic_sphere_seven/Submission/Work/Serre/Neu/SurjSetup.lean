-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/Setup.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.SurjDefs
import Submission.Work.Serre.Neu.RatHyp
import Submission.Work.StemsB.WangCohRat
import Submission.Work.Serre.crossProduct_coker_rat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## Cycles of a rational chain complex -/

/-- The cycle of a `ℚ`-chain complex with a prescribed underlying chain. -/
noncomputable def cycleOfQ (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (x : ↥(K.X n))
    (h : (ModuleCat.Hom.hom (K.d n (n - 1))) x = 0) : ↥(K.cycles n) :=
  (K.cyclesIsoSc' (n + 1) n (n - 1) (Work.Kunneth.down_prev n) (Work.Kunneth.down_next n)).inv
    (((K.sc' (n + 1) n (n - 1)).moduleCatCyclesIso).inv ⟨x, LinearMap.mem_ker.mpr h⟩)

/-- The underlying chain of `cycleOfQ` is the prescribed one. -/
theorem iCycles_cycleOfQ (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (x : ↥(K.X n))
    (h : (ModuleCat.Hom.hom (K.d n (n - 1))) x = 0) :
    (ModuleCat.Hom.hom (K.iCycles n)) (cycleOfQ K n x h) = x := by
  set y : ↥((K.sc' (n + 1) n (n - 1)).cycles) :=
    ((K.sc' (n + 1) n (n - 1)).moduleCatCyclesIso).inv ⟨x, LinearMap.mem_ker.mpr h⟩ with hy
  have h2 : (ModuleCat.Hom.hom (K.iCycles n))
        ((ModuleCat.Hom.hom ((K.cyclesIsoSc' (n + 1) n (n - 1) (Work.Kunneth.down_prev n)
          (Work.Kunneth.down_next n)).inv)) y)
      = (ModuleCat.Hom.hom ((K.sc' (n + 1) n (n - 1)).iCycles)) y := by
    have hh := congrArg (fun (g : (K.sc' (n + 1) n (n - 1)).cycles ⟶ K.X n) =>
        (ModuleCat.Hom.hom g) y)
      (HomologicalComplex.cyclesIsoSc'_inv_iCycles (K := K) (i := n + 1) (j := n) (k := n - 1)
        (Work.Kunneth.down_prev n) (Work.Kunneth.down_next n))
    exact hh
  have h1 : (ModuleCat.Hom.hom ((K.sc' (n + 1) n (n - 1)).iCycles)) y = x := by
    rw [hy, ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
    rfl
  have h3 := h2.trans h1
  simpa only [cycleOfQ, hy] using h3

private theorem rat_smul_tmul_one_nat {H : Type} [AddCommGroup H] [Module ℤ H] (n : ℕ) (w : H) :
    (n : ℚ) • (TensorProduct.tmul ℤ (1 : ℚ) w) = TensorProduct.tmul ℤ (1 : ℚ) (n • w) := by
  rw [Nat.cast_smul_eq_nsmul (R := ℚ) n (TensorProduct.tmul ℤ (1 : ℚ) w),
    ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) w]

/-- `(m : ℚ) • (1 ⊗ w) = 1 ⊗ (m • w)` for an integer `m`. -/
private theorem rat_smul_tmul_one_int {H : Type} [AddCommGroup H] [Module ℤ H] (m : ℤ) (w : H) :
    (m : ℚ) • (TensorProduct.tmul ℤ (1 : ℚ) w) = TensorProduct.tmul ℤ (1 : ℚ) (m • w) := by
  rcases Int.eq_nat_or_neg m with ⟨n, h | h⟩
  · rw [h, Int.cast_natCast,
      Nat.cast_smul_eq_nsmul (R := ℚ) n (TensorProduct.tmul ℤ (1 : ℚ) w),
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) w, natCast_zsmul]
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_smul, neg_zsmul, TensorProduct.tmul_neg,
      Nat.cast_smul_eq_nsmul (R := ℚ) n (TensorProduct.tmul ℤ (1 : ℚ) w),
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) w, natCast_zsmul]

/-- `q ⊗ w = q • (1 ⊗ w)`. -/
private theorem rat_tmul_eq_smul_tmul_one {H : Type} [AddCommGroup H] [Module ℤ H] (q : ℚ)
    (w : H) : TensorProduct.tmul ℤ q w = q • (TensorProduct.tmul ℤ (1 : ℚ) w) := by
  rw [TensorProduct.smul_tmul' (R := ℤ) q (1 : ℚ) w, smul_eq_mul, mul_one]

/-- **The generating relation propagates to the whole tensor product.**  If every element `w` of a
`ℤ`-module `H` has a positive multiple which is an integral multiple of `x` after rationalisation,
then every element of `ℚ ⊗[ℤ] H` is a rational multiple of `1 ⊗ x`. -/
theorem exists_rat_smul_tmul_one {H : Type} [AddCommGroup H] [Module ℤ H] {x : H}
    (hgen : ∀ w : H, ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      TensorProduct.tmul ℤ (n • w) (1 : ℚ) = TensorProduct.tmul ℤ (m • x) (1 : ℚ))
    (y : ℚ ⊗[ℤ] H) : ∃ c : ℚ, y = c • TensorProduct.tmul ℤ (1 : ℚ) x := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [zero_smul]⟩
  | tmul q w =>
      obtain ⟨n, hn, m, hm⟩ := hgen w
      have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      have hm' : TensorProduct.tmul ℤ (1 : ℚ) (n • w)
          = TensorProduct.tmul ℤ (1 : ℚ) (m • x) := by
        have h := congrArg (TensorProduct.comm ℤ H ℚ) hm
        simpa only [map_nsmul, map_zsmul, TensorProduct.comm_tmul] using h
      have hn' : (n : ℚ) • (TensorProduct.tmul ℤ (1 : ℚ) w)
          = (m : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) x := by
        rw [rat_smul_tmul_one_nat n w, hm', ← rat_smul_tmul_one_int m x]
      have hw : TensorProduct.tmul ℤ (1 : ℚ) w
          = ((m : ℚ) / n) • TensorProduct.tmul ℤ (1 : ℚ) x := by
        calc TensorProduct.tmul ℤ (1 : ℚ) w
            = (n : ℚ)⁻¹ • ((n : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) w) :=
                (inv_smul_smul₀ hnq _).symm
          _ = (n : ℚ)⁻¹ • ((m : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) x) := by rw [hn']
          _ = ((n : ℚ)⁻¹ * (m : ℚ)) • TensorProduct.tmul ℤ (1 : ℚ) x := smul_smul _ _ _
          _ = ((m : ℚ) / n) • TensorProduct.tmul ℤ (1 : ℚ) x := by rw [div_eq_inv_mul]
      refine ⟨q * ((m : ℚ) / n), ?_⟩
      rw [rat_tmul_eq_smul_tmul_one q w, hw, smul_smul]
  | add a b ha hb =>
      obtain ⟨c₁, h₁⟩ := ha
      obtain ⟨c₂, h₂⟩ := hb
      exact ⟨c₁ + c₂, by rw [h₁, h₂, add_smul]⟩

end

end Work.Serre.Surj

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## The value of `homologyMapIso` on classes of cycles -/

/-- The value of `homologyMapIso` on the class of a cycle. -/
theorem homologyMapIso_homologyπ (K L : ChainComplex (ModuleCat ℤ) ℕ) (e : K ≅ L) (n : ℕ)
    (x : ↥(K.cycles n)) :
    (ModuleCat.Hom.hom ((HomologicalComplex.homologyMapIso e n).hom))
        ((ModuleCat.Hom.hom (K.homologyπ n)) x)
      = (ModuleCat.Hom.hom (L.homologyπ n)) ((HomologicalComplex.cyclesMap e.hom n) x) := by
  rw [HomologicalComplex.homologyMapIso_hom]
  exact homologyMap_homologyπ K L e.hom n x

