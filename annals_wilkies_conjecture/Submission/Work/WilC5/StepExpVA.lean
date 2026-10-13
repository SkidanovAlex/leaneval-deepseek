import Mathlib
import Submission.Work.WilC5.S4Exp.hynew_exp
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC4.dcl_inv

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG

/-! ## Auxiliary: the value relation read off an integer relation

This is the (small) algebraic step that converts Wilkie's integer relation
`c · u · y ^ n ∈ U(K)` into a statement about archimedean classes:
`v(u) = -v(c) - n·v(y)`.  It is a self-contained restatement of the corresponding
helper in `Submission.Work.WilC5.S4Exp.va_exp`, reproduced here because that module and
`Submission.Work.WilC5.S4Exp.hynew_exp` both declare `Work.WilC5.S4Exp.mem_dcl_iff_definableElt`
and therefore cannot be imported together. -/

/-- **The value relation read off an integer relation.**  If `c · u · y ^ n` is a unit of the
standard real valuation (`c ≠ 0`, `y ≠ 0`), then `u` and `c⁻¹ · y ^ (-n)` have the same value:
in value-group notation `v(u) + v(c) + n · v(y) = 0`, i.e. `v(u) = -v(c) - n · v(y)`. -/
theorem stepVA_sameArch_zpow_of_unitVal {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {c y u : K} (hc : c ≠ 0) (hy : y ≠ 0) {n : ℤ}
    (h : WilkiesDesign.CG.IsUnitVal (c * u * y ^ n)) :
    Work.WilC5.SameArch u (c⁻¹ * y ^ (-n)) := by
  have hz : c⁻¹ * y ^ (-n) ≠ 0 := mul_ne_zero (inv_ne_zero hc) (zpow_ne_zero _ hy)
  rw [Work.WilC5.SameArch_iff_IsUnitVal_div hz]
  have key : u / (c⁻¹ * y ^ (-n)) = c * u * y ^ n := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_zpow, inv_zpow', neg_neg]
    ring
  rw [key]
  exact h

theorem StepExpVA {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (A : Set K) (hAdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) A ⊆ A)
    (hAlog : ∀ x ∈ A, Work.WilC5.logFun x ∈ A)
    (a : K) (ha : a ∈ A) (hx : Work.WilC5.expE a ∉ A) :
    ∀ w ∈ @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (A ∪ {Work.WilC5.expE a}),
      w ≠ 0 → ∃ Q : ℤ, 0 < Q ∧ ∃ N : ℤ, ∃ z ∈ A, z ≠ 0 ∧ ∃ ε : K,
        Work.WilC5.IsInfinitesimal ε ∧ w ^ Q = z * (Work.WilC5.expE a) ^ N * (1 + ε) := by
  classical
  -- ## The value of `expE a` is new over `A` (vdDMM's `hynew`): the analytic input `hynew_exp`.
  have hynew : ∀ c ∈ A, c ≠ 0 →
      ¬ WilkiesDesign.CG.IsUnitVal (c * Work.WilC5.expE a) :=
    Work.WilC5.S4Exp.hynew_exp (K := K) hTE hrexp hadd hmul hone hleneg A hAdcl hAlog a ha hx
  -- ## `0 ∈ A`, hence `expE a ≠ 0`.
  have h0A : (0 : K) ∈ A := by
    have h := Work.WilC5.S4Exp.mem_realConst (K := K) A hAdcl 0
    rwa [Work.WilC5.realConst_zero] at h
  have hy0 : Work.WilC5.expE a ≠ 0 := fun h => hx (h ▸ h0A)
  -- ## `A` is the carrier of an elementary substructure of `K`.
  obtain ⟨S, hS⟩ := Work.WilC5.dclClosed_substructure (M := K) hAdcl
  have helem : S.IsElementary := by
    have hSdcl : Work.WilC2.Dcl (S : Set K) ⊆ (S : Set K) := by rw [hS]; exact hAdcl
    have hmeet : FirstOrder.Language.MeetsDefinable (L := WilkiesDesign.CG.LRc) (S : Set K) :=
      Work.WilC5.meetsDefinable_of_dclClosed (M := K) hOM hSdcl
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := WilkiesDesign.CG.LRc)
      (M := K) (A := (S : Set K)) hmeet
    rwa [FirstOrder.Language.Substructure.closure_eq] at h
  let S' : WilkiesDesign.CG.LRc.ElementarySubstructure K := ⟨S, helem⟩
  have hS' : (S' : Set K) = A := hS
  -- ## The value containment for `w ∈ Dcl (A ∪ {expE a})`.
  intro w hw hw0
  -- `w` is definable from the parameters `S' ∪ {expE a}`.
  have hbdef : ((S' : Set K) ∪ {Work.WilC5.expE a}).Definable WilkiesDesign.CG.LRc
      {fun _ : Fin 1 => w} := by
    have h1 : Work.WilC4.DefinableElt (A ∪ {Work.WilC5.expE a}) ∅ w :=
      (Work.WilC5.S4Exp.mem_dcl_iff_definableElt_hy (A ∪ {Work.WilC5.expE a}) w).mp hw
    have h2 : (A ∪ {Work.WilC5.expE a}).Definable WilkiesDesign.CG.LRc
        {fun _ : Fin 1 => w} := by
      simpa [Work.WilC4.DefinableElt, Set.union_empty] using h1
    rwa [hS']
  -- the value of `expE a` is new over `S'`
  have hynew' : ∀ c ∈ (S' : Set K), c ≠ 0 →
      ¬ WilkiesDesign.CG.IsUnitVal (c * Work.WilC5.expE a) := by
    rw [hS']; exact hynew
  -- Wilkie's inequality: an integer relation between `v w` and `v (expE a)` over `v(A^×)`.
  obtain ⟨q, hqne, n, c, hcS, hc0, hunit⟩ :=
    Work.WilC5.valIneq_span (M := K) hVI S' hy0 hw0 hbdef hynew'
  have hcA : c ∈ A := by rw [← hS']; exact hcS
  have hSA : Work.WilC5.SameArch (w ^ q) (c⁻¹ * (Work.WilC5.expE a) ^ (-n)) :=
    stepVA_sameArch_zpow_of_unitVal (K := K) hc0 hy0 hunit
  rcases lt_trichotomy q 0 with hqlt | hqeq | hqgt
  · -- `q < 0`: invert the relation, `Q := -q`, `N := n`, `z := realConst r · c`.
    have h1 : (w ^ q)⁻¹ = w ^ (-q) := by rw [← inv_zpow, inv_zpow']
    have h2 : (c⁻¹ * (Work.WilC5.expE a) ^ (-n))⁻¹ = c * (Work.WilC5.expE a) ^ n := by
      rw [mul_inv_rev, inv_inv, ← inv_zpow, inv_zpow', neg_neg]
      exact mul_comm _ _
    have hSA' : Work.WilC5.SameArch (w ^ (-q)) (c * (Work.WilC5.expE a) ^ n) := by
      have h := Work.WilC5.SameArch_inv hSA
      rwa [h1, h2] at h
    have hz0 : c * (Work.WilC5.expE a) ^ n ≠ 0 := mul_ne_zero hc0 (zpow_ne_zero _ hy0)
    obtain ⟨r, hrne, ε, hε, heq⟩ :=
      Work.WilC5.decomposition_of_same_value (M := K) hz0 hSA'
    refine ⟨-q, by omega, n, Work.WilC5.realConst K r * c, ?_, ?_, ε, hε, ?_⟩
    · exact Work.WilC5.S4Exp.mem_mul A hAdcl (Work.WilC5.S4Exp.mem_realConst A hAdcl r) hcA
    · exact mul_ne_zero (Work.WilC5.realConst_ne_zero hrne) hc0
    · rw [heq]; ring
  · exact absurd hqeq hqne
  · -- `q > 0`: the relation itself, `Q := q`, `N := -n`, `z := realConst r · c⁻¹`.
    have hz0 : c⁻¹ * (Work.WilC5.expE a) ^ (-n) ≠ 0 :=
      mul_ne_zero (inv_ne_zero hc0) (zpow_ne_zero _ hy0)
    obtain ⟨r, hrne, ε, hε, heq⟩ :=
      Work.WilC5.decomposition_of_same_value (M := K) hz0 hSA
    refine ⟨q, hqgt, -n, Work.WilC5.realConst K r * c⁻¹, ?_, ?_, ε, hε, ?_⟩
    · exact Work.WilC5.S4Exp.mem_mul A hAdcl (Work.WilC5.S4Exp.mem_realConst A hAdcl r)
        (Work.WilC5.S4Exp.dcl_mem_inv A hAdcl hcA hc0)
    · exact mul_ne_zero (Work.WilC5.realConst_ne_zero hrne) (inv_ne_zero hc0)
    · rw [heq]; ring

end Work.WilC5
