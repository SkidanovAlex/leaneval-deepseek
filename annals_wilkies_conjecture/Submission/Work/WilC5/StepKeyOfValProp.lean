import Mathlib
import Submission.Work.WilC5.ValProp
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.Values
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.StepKey
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.S4ExpF.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open Classical
open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

namespace Work.WilC5

/-! ## 0. The syntactic `LRc`-structure attached to an `LEc`-structure

`Work.WilC5.ValProp` is stated for the `LRc`-structure synthesised by Mathlib from the
typeclass arguments `Ring.CompatibleRing M`, `rexpL.Structure M` and `(constantsOn ℝ).Structure M`,
whereas the §4 layer works with the *reduct* `Work.WilC5.reductStruct M` of the `LEc`-structure.
The two structures are equal, but not definitionally, so we need the pieces below.

`canonSyn K` is the syntactic structure as an explicit term, written in terms of the reducts
`lrcRingReduct`, `lrcRexpReduct`, `lrcConstReduct` of the **reduct** structure; it is exactly the
right-hand side of `Work.WilC5.reductStruct_eq_withConstants`. -/

/-- The syntactic `LRc`-structure built from the reducts of `Work.WilC5.reductStruct K`. -/
@[instance_reducible] noncomputable def canonSyn (K : Type) [LEc.Structure K] : LRc.Structure K :=
  @Language.withConstantsStructure LR K
    (@Language.sumStructure ring rexpL K
      (@Work.WilC5.lrcRingReduct K (@Work.WilC5.reductStruct K inferInstance))
      (@Work.WilC5.lrcRexpReduct K (@Work.WilC5.reductStruct K inferInstance)))
    ℝ (@Work.WilC5.lrcConstReduct K (@Work.WilC5.reductStruct K inferInstance))

/-- The reduct structure and the syntactic structure agree. -/
theorem reductStruct_eq_canonSyn {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] [rexpL.Structure K]
    [(constantsOn ℝ).Structure K] :
    (reductStruct K : LRc.Structure K) = canonSyn K :=
  reductStruct_eq_withConstants

/-- The `funMap`s of the two equal `LRc`-structures agree, symbol by symbol. -/
theorem funMap_canonSyn {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] [rexpL.Structure K]
    [(constantsOn ℝ).Structure K] {n : ℕ} (f : LRc.Functions n) (x : Fin n → K) :
    @Structure.funMap LRc K (canonSyn K) n f x =
      @Structure.funMap LRc K (reductStruct K) n f x :=
  congrArg (fun i => @Structure.funMap LRc K i n f x)
    (reductStruct_eq_canonSyn (K := K)).symm

/-- **A `Ring.CompatibleRing K` whose ring structure is the `LRc`-reduct of the `LEc`-structure.**

This is the instance with which `ValProp`'s syntactic structure coincides with the reduct
`Work.WilC5.reductStruct K`.  The proofs of the compatibility axioms transfer the `LEc`-sentences
`x + y = z`, `x · y = z`, `-x = y`, `0 = z`, `1 = z` from `ℝ` (`Work.WilC5.S4ExpF.Bridge`). -/
@[instance_reducible] noncomputable def lrcCompatRing {K : Type} [LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [Ring.CompatibleRing K] [rexpL.Structure K]
    [(constantsOn ℝ).Structure K] [K ⊨ TE]
    (hadd : ∀ x y : K, addE x y = x + y) (hmul : ∀ x y : K, mulE x y = x * y)
    (hone : (oneE : K) = 1) : Ring.CompatibleRing K where
  toStructure := lrcRingReduct K
  funMap_add := by
    intro x
    show @Structure.funMap Language.ring K (lrcRingReduct K) 2 Ring.addFunc x = x 0 + x 1
    rw [lrcRingReduct_funMap]
    have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hx]
    exact hadd (x 0) (x 1)
  funMap_mul := by
    intro x
    show @Structure.funMap Language.ring K (lrcRingReduct K) 2 Ring.mulFunc x = x 0 * x 1
    rw [lrcRingReduct_funMap]
    have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hx]
    exact hmul (x 0) (x 1)
  funMap_neg := by
    intro x
    show @Structure.funMap Language.ring K (lrcRingReduct K) 1 Ring.negFunc x = -x 0
    rw [lrcRingReduct_funMap]
    have hx : x = ![x 0] := by funext i; fin_cases i <;> rfl
    rw [hx]
    exact S4ExpF.negE_eq_neg inferInstance hadd (x 0)
  funMap_zero := by
    intro x
    show @Structure.funMap Language.ring K (lrcRingReduct K) 0 Ring.zeroFunc x = 0
    rw [lrcRingReduct_funMap]
    have hx : x = (default : Fin 0 → K) := Subsingleton.elim x default
    rw [hx]
    exact S4ExpF.zeroE_eq_zero inferInstance hadd
  funMap_one := by
    intro x
    show @Structure.funMap Language.ring K (lrcRingReduct K) 0 Ring.oneFunc x = 1
    rw [lrcRingReduct_funMap]
    have hx : x = (default : Fin 0 → K) := Subsingleton.elim x default
    rw [hx]
    exact hone

/-- The closure condition of an `LRc`-substructure at an explicitly given `LRc`-structure
(the projection `Substructure.fun_mem` with its instance argument pinned down). -/
theorem substructure_funMem {M : Type} (i : LRc.Structure M) (S : @LRc.Substructure M i)
    {n : ℕ} (f : LRc.Functions n) (x : Fin n → M) (hx : ∀ k, x k ∈ (S : Set M)) :
    @Structure.funMap LRc M i n f x ∈ (S : Set M) := by
  letI : LRc.Structure M := i
  exact S.fun_mem f x hx

/-! ## 1. Transporting `LRc`-statements along an equality of structures -/

/-- Membership in the definable closure transports along an equality of `LRc`-structures. -/
theorem mem_dcl_struct_congr {M : Type} (i i' : LRc.Structure M) (h : i = i') (A : Set M)
    (x : M) : x ∈ @Work.WilC2.Dcl M i A ↔ x ∈ @Work.WilC2.Dcl M i' A := by
  cases h
  exact Iff.rfl

/-- `LRc`-definability transports along an equality of `LRc`-structures. -/
theorem definable_struct_congr {M : Type} {α : Type} (i i' : LRc.Structure M) (h : i = i')
    (A : Set M) (s : Set (α → M)) :
    @Set.Definable M A LRc i α s ↔ @Set.Definable M A LRc i' α s := by
  cases h
  exact Iff.rfl

/-- `Set.Definable₁` transports along an equality of `LRc`-structures. -/
theorem definable₁_struct_congr {M : Type} (i i' : LRc.Structure M) (h : i = i') (A : Set M)
    (s : Set M) : @Set.Definable₁ M A LRc i s ↔ @Set.Definable₁ M A LRc i' s := by
  cases h
  exact Iff.rfl

/-- Being a model of a theory transports along an equality of `LRc`-structures. -/
theorem theoryModel_struct_congr {M : Type} (i i' : LRc.Structure M) (h : i = i')
    (T : LRc.Theory) : @Theory.Model LRc M i T ↔ @Theory.Model LRc M i' T := by
  cases h
  exact Iff.rfl

/-! ## 2. The bridge between `Work.WilC2.Dcl` and `Work.WilC4.Dcl` -/

/-- `Work.WilC2.Dcl A` is `Work.WilC4.Dcl A ∅`, at the syntactic structure. -/
theorem dcl_iff_definableElt {M : Type} [Field M] [Ring.CompatibleRing M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M] (A : Set M) (x : M) :
    x ∈ @Work.WilC2.Dcl M (LR.withConstantsStructure ℝ) A ↔
      Work.WilC4.DefinableElt A ∅ x := by
  rw [Work.WilC2.mem_dcl]
  unfold Set.Definable₁ Work.WilC4.DefinableElt
  rw [Set.union_empty, Work.WilC4.singleton_setOf_eq x]

/-! ## 3. `SameArch` versus `IsUnitVal (c * ·)` -/

/-- `SameArch 0 x` forces `x = 0` (the `LRc`-free form of `Work.WilC5.eq_zero_of_sameArch_zero`). -/
theorem eq_zero_of_sameArch_zero' {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (h : SameArch (0 : K) x) : x = 0 := by
  obtain ⟨N, -, h2⟩ := h
  exact abs_eq_zero.mp (le_antisymm (by simpa using h2) (abs_nonneg x))

/-- `IsUnitVal 0` fails. -/
theorem not_isUnitVal_zero {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ¬ IsUnitVal (0 : K) := by
  rintro ⟨N, h1, -⟩
  have hpos : (0 : K) < ((N : K) + 1)⁻¹ := inv_pos.mpr (by positivity)
  rw [abs_zero] at h1
  linarith

/-- **`v(x) ∉ v(S^×)` in the two forms used by the §4 layer.**  For a set `S` of nonzero elements
closed under inverses and `y ≠ 0`, "no element of `S` has the value of `y`" (`SameArch`) is the
same as "no `c ∈ S` makes `c * y` a unit" (`IsUnitVal`), the form in which the frozen `ValIneq`
and the `ValProp` hypothesis are written. -/
theorem notSameArch_iff_notIsUnitVal_mul {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {S : Set K} (hSinv : ∀ c ∈ S, c ≠ 0 → c⁻¹ ∈ S) {y : K}
    (hy : y ≠ 0) :
    (∀ b : ↥S, ¬ SameArch (b : K) y) ↔ (∀ c ∈ S, ¬ IsUnitVal (c * y)) := by
  constructor
  · intro h c hc hcu
    have hc0 : c ≠ 0 := by
      intro hcc
      have hcu' := hcu
      rw [hcc, zero_mul] at hcu'
      exact not_isUnitVal_zero hcu'
    have hcinv : c⁻¹ ∈ S := hSinv c hc hc0
    have h1 : IsUnitVal (c⁻¹ * y⁻¹) := by
      have h2 : IsUnitVal ((c * y)⁻¹) := IsUnitVal_inv hcu
      rw [mul_inv_rev, mul_comm] at h2
      exact h2
    exact h ⟨c⁻¹, hcinv⟩ ((SameArch_iff_IsUnitVal_mul_inv (K := K) hy).mpr h1)
  · intro h b hsa
    by_cases hb0 : (b : K) = 0
    · rw [hb0] at hsa
      exact hy (eq_zero_of_sameArch_zero' hsa)
    · have hbinv : (b : K)⁻¹ ∈ S := hSinv (b : K) b.2 hb0
      have h1 : IsUnitVal ((b : K)⁻¹ * y) := by
        have h2 : IsUnitVal ((b : K) * y⁻¹) :=
          (SameArch_iff_IsUnitVal_mul_inv (K := K) hy).mp hsa
        have h3 : IsUnitVal (((b : K) * y⁻¹)⁻¹) := IsUnitVal_inv h2
        rw [mul_inv_rev, inv_inv, mul_comm] at h3
        exact h3
      exact h ((b : K)⁻¹) hbinv h1

theorem StepKeyOfValProp
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    (hVP : Work.WilC5.ValProp)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    {z : K}
    (hnew : ∃ w : K, w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {z}) ∧
        ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) w) :
    ∃ a ∈ (B : Set K), ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) (z - a) := by
  classical
  obtain ⟨w, hwD, hw⟩ := hnew
  -- `0 ∈ B`, hence `w ≠ 0` (as `SameArch 0 0`).
  have hz0 : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero ‹K ⊨ WilkiesDesign.CG.TE› hadd
  have h0B : (0 : K) ∈ (B : Set K) := by
    rw [← hz0]
    exact mem_B_zero (K := K) hadd B
  have hw0 : w ≠ 0 := by
    intro hz
    refine hw ⟨0, h0B⟩ ?_
    rw [hz]
    exact sameArch_zero_zero
  -- ------------------------------------------------------------------ #
  -- the syntactic `LRc`-structure, made the local structure
  -- ------------------------------------------------------------------ #
  letI : Ring.CompatibleRing K := lrcCompatRing hadd hmul hone
  letI : rexpL.Structure K := lrcRexpReduct K
  letI : (constantsOn ℝ).Structure K := lrcConstReduct K
  have hstruct : (reductStruct K : LRc.Structure K) = canonSyn K :=
    reductStruct_eq_canonSyn
  letI : LRc.Structure K := canonSyn K
  -- ------------------------------------------------------------------ #
  -- transporting the hypotheses to the syntactic structure
  -- ------------------------------------------------------------------ #
  have hBdcl' : @Work.WilC2.Dcl K (canonSyn K) (B : Set K) ⊆ (B : Set K) := fun x hx =>
    hBdcl ((mem_dcl_struct_congr (reductStruct K) (canonSyn K) hstruct (B : Set K) x).mpr hx)
  have hKTR : @Theory.Model LRc K (canonSyn K) TR :=
    (theoryModel_struct_congr (reductStruct K) (canonSyn K) hstruct TR).mp (reductTR inferInstance)
  have hwD' : w ∈ @Work.WilC2.Dcl K (canonSyn K) ((B : Set K) ∪ {z}) :=
    (mem_dcl_struct_congr (reductStruct K) (canonSyn K) hstruct ((B : Set K) ∪ {z}) w).mp hwD
  have hdef : @Set.Definable K ((B : Set K) ∪ {z}) LRc (canonSyn K) (Fin 1)
      {fun _ : Fin 1 => w} := by
    have h1 : @Set.Definable₁ K ((B : Set K) ∪ {z}) LRc (canonSyn K) ({w} : Set K) := hwD'
    unfold Set.Definable₁ at h1
    rwa [Work.WilC4.singleton_setOf_eq w] at h1
  -- ------------------------------------------------------------------ #
  -- the elementary substructure with carrier `B`
  -- ------------------------------------------------------------------ #
  let Ssub : @LRc.Substructure K (canonSyn K) :=
    mkSubAt K (canonSyn K) (B : Set K) (fun {n} f x hx => by
      rw [funMap_canonSyn (K := K) f x]
      exact substructure_funMem (reductStruct K) B f x hx)
  have hSsub : (Ssub : Set K) = (B : Set K) := rfl
  have hBdcl'' : @Work.WilC2.Dcl K (canonSyn K) (Ssub : Set K) ⊆ (Ssub : Set K) := hBdcl'
  have helem : Ssub.IsElementary := by
    have hmeet : @FirstOrder.Language.MeetsDefinable LRc K (canonSyn K) (Ssub : Set K) :=
      @meetsDefinable_of_dclClosed K (inferInstance : Field K)
        (inferInstance : LinearOrder K) (inferInstance : IsStrictOrderedRing K)
        (inferInstance : Ring.CompatibleRing K) (inferInstance : rexpL.Structure K)
        (inferInstance : (constantsOn ℝ).Structure K) hOM (Ssub : Set K) hKTR hBdcl''
    have h := @FirstOrder.Language.MeetsDefinable.isElementary_closure LRc K (canonSyn K)
      (Ssub : Set K) hmeet
    rwa [FirstOrder.Language.Substructure.closure_eq] at h
  let Ssyn : @LRc.ElementarySubstructure K (canonSyn K) := ⟨Ssub, helem⟩
  -- ------------------------------------------------------------------ #
  -- `B` is closed under inversion (a `Dcl`-closed substructure of a field is a subfield)
  -- ------------------------------------------------------------------ #
  have hBinv : ∀ c ∈ (B : Set K), c ≠ 0 → c⁻¹ ∈ (B : Set K) := by
    intro c hc hc0
    have h1 : Work.WilC4.DefinableElt (B : Set K) ∅ c := by
      show @Set.Definable K ((B : Set K) ∪ ∅) LRc (LR.withConstantsStructure ℝ) (Fin 1)
        {fun _ : Fin 1 => c}
      rw [Set.union_empty, ← Work.WilC4.singleton_setOf_eq c]
      exact Set.Definable.singleton_of_mem LRc hc
    have h2 : c⁻¹ ∈ Work.WilC4.Dcl (B : Set K) ∅ := Work.WilC4.dcl_inv h1 hc0
    exact hBdcl' ((dcl_iff_definableElt (B : Set K) c⁻¹).mpr h2)
  -- ------------------------------------------------------------------ #
  -- the valuation hypothesis in `IsUnitVal` form, and `ValProp`
  -- ------------------------------------------------------------------ #
  have hunit : ∀ c ∈ (B : Set K), ¬ IsUnitVal (c * w) :=
    (notSameArch_iff_notIsUnitVal_mul (S := (B : Set K)) hBinv (y := w) hw0).mp
      (fun b => hw b)
  haveI : @Theory.Model LRc K (canonSyn K) TR := hKTR
  obtain ⟨a, ha, hane, hval⟩ := hVP K Ssyn z w hw0 hdef hunit
  exact ⟨a, ha, fun b => (notSameArch_iff_notIsUnitVal_mul (S := (B : Set K)) hBinv
    (y := z - a) hane).mpr (fun c hc => hval c hc) b⟩

end Work.WilC5
