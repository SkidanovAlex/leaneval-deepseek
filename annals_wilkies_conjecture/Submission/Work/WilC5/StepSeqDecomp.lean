/-
  WilC5 — **the value decomposition of an element of a definable closure** (the "step sequence"
  decomposition of van den Dries–Macintyre–Marker §4).

  `B` is a `Dcl`-closed `LRc`-substructure of the `rexp`-reduct of a model `K ⊨ TE`, `a : Fin n → K`
  is a family whose values are `ℤ`-independent modulo `v(B^×)` (`hind`), and `w ≠ 0` lies in the
  definable closure of `B ∪ range a`.  The conclusion is that, up to a *power* `w ^ Q` (`Q > 0`,
  the denominators being unavoidable because `v(Dcl …)` lies in the divisible hull of the values of
  the generators), `w ^ Q` is a `B`-multiple of a monomial `∏ aᵢ ^ Nᵢ` times a unit `1 + ε` with
  `ε` infinitesimal.

  The two inputs are
  * `Work.WilC5.SpanContain` (vdDMM (3.9), the value containment from Wilkie's valuation inequality
    `hVI`): `c · w ^ q · ∏ aᵢ ^ Nᵢ` is a unit for some `q ≠ 0`, `c ∈ B \ {0}` — i.e.
    `v(w) ∈ divhull (v(B^×) ∪ ℚ span {v(aᵢ)})`;
  * `Work.WilC5.decomposition_of_same_value` (vdDMM Lemma 4.2's `w = z(1+ε)`): two nonzero elements
    of the same archimedean class differ by a real constant times an infinitesimal unit.

  ## The instance bookkeeping

  `SpanContain` and the whole `§4` layer are stated at the `LRc`-structure *synthesised* from an
  ordered-field instance bundle (`LR.withConstantsStructure ℝ`: ring operations from the field,
  the constant symbols from a `constantsOn ℝ`-structure, the `rexp` symbol from a `rexpL`-structure),
  whereas the hypotheses of the statement are given at the `rexp`-*reduct* `reductStruct K` of an
  opaque `LEc`-structure.  The bridge is the (proved) equality of `LRc`-structures
  `Work.WilC5.reductStruct_eq_withConstants`; it applies once the instance bundle is chosen to be
  the one *derived* from `reductStruct K`:

  * the `rexpL`-structure is `lrcRexpReduct K` and the `constantsOn ℝ`-structure is
    `lrcConstReduct K` (both derived from the reduct — the *given* instances are irrelevant, and
    in particular the given constant symbols need not be the ones of the model `K ⊨ TE`);
  * the `Ring.CompatibleRing` structure is replaced (by `letI`, with the same underlying ring
    operations) by one whose `Language.ring.Structure` is `lrcRingReduct K`, i.e. the ring of the
    reduct, which agrees with the field operations by `hadd`, `hmul`, `hone` and the two transfer
    lemmas `S4Exp.zeroE_eq_zero`, `S4Exp.negE_eq_neg`.

  With that choice `LR.withConstantsStructure ℝ` is literally `reductStruct K` (up to definitional
  equality), so `B` is a substructure and `Dcl`-closed at the canonical structure, hence (via
  `hOM`, `dclClosed_substructure`, `MeetsDefinable.isElementary_closure`) the carrier of an
  elementary substructure; the hypotheses `hBdcl`, `hw` transfer along the structure equality by
  `congrArg`.
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.SpanContain
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.ValArith
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.S4Exp.hynew_exp

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem StepSeqDecomp
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
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    {n : ℕ} (a : Fin n → K) (ha0 : ∀ i, a i ≠ 0)
    (hind : ∀ q : Fin n → ℤ,
      (∃ c ∈ (B : Set K), c ≠ 0 ∧ WilkiesDesign.CG.IsUnitVal (c * ∏ i, a i ^ (q i))) → q = 0)
    {w : K} (hw : w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K)
        ((B : Set K) ∪ Set.range a)) (hw0 : w ≠ 0) :
    ∃ Q : ℤ, 0 < Q ∧ ∃ N : Fin n → ℤ, ∃ z ∈ (B : Set K), z ≠ 0 ∧ ∃ ε : K,
      Work.WilC5.IsInfinitesimal ε ∧ w ^ Q = z * (∏ i, a i ^ (N i)) * (1 + ε) := by
  classical
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  -- ## Facts about `B` at the `rexp`-reduct (before any instance is shadowed)
  have hclosRed : ∀ {m : ℕ} (f : LRc.Functions m) (x : Fin m → K),
      (∀ k, x k ∈ (B : Set K)) → @Structure.funMap LRc K (Work.WilC5.reductStruct K) m f x
        ∈ (B : Set K) := fun f x hx => B.fun_mem f x hx
  have hTRRed : @Theory.Model LRc K (Work.WilC5.reductStruct K) TR :=
    Work.WilC5.reduct_model_TR K hTE
  have hzero : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4Exp.zeroE_eq_zero hTE hadd
  have hneg : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4Exp.negE_eq_neg hTE hadd x
  -- ## A `CompatibleRing` structure whose ring is that of the reduct
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hadd _ _
      funMap_mul := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hmul _ _
      funMap_neg := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hneg _
      funMap_zero := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show x = default from Subsingleton.elim _ _]
        exact hzero
      funMap_one := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show x = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : rexpL.Structure K := Work.WilC5.lrcRexpReduct K
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K := Work.WilC5.lrcConstReduct K
  letI hLR : LRc.Structure K := LR.withConstantsStructure ℝ
  -- ## The canonical structure is the reduct (vdDMM: the two instance bundles agree)
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = (inferInstance : LRc.Structure K) :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hTR : @Theory.Model LRc K (inferInstance) TR := hstruct ▸ hTRRed
  haveI : @Theory.Model LRc K (inferInstance) TR := hTR
  -- ## `B` is the carrier of an elementary substructure of the canonical structure
  have hfun : ∀ (m : ℕ) (f : LRc.Functions m) (x : Fin m → K),
      @Structure.funMap LRc K (inferInstance) m f x =
        @Structure.funMap LRc K (Work.WilC5.reductStruct K) m f x :=
    fun m f x => (congrArg (fun i => @Structure.funMap LRc K i m f x) hstruct).symm
  have hclos : ∀ {m : ℕ} (f : LRc.Functions m) (x : Fin m → K),
      (∀ k, x k ∈ (B : Set K)) → @Structure.funMap LRc K (inferInstance) m f x
        ∈ (B : Set K) := by
    intro m f x hx
    rw [hfun m f x]
    exact hclosRed f x hx
  let S₁ : LRc.Substructure K := ⟨(B : Set K), hclos⟩
  have hS₁ : (S₁ : Set K) = (B : Set K) := rfl
  have hdclEq : @Work.WilC2.Dcl K (inferInstance) (B : Set K)
      = @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) :=
    congrArg (fun i => @Work.WilC2.Dcl K i (B : Set K)) hstruct.symm
  have hS₁dcl : @Work.WilC2.Dcl K (inferInstance) (S₁ : Set K) ⊆ (S₁ : Set K) := by
    intro y hy
    rw [hS₁] at hy ⊢
    rw [hdclEq] at hy
    exact hBdcl hy
  have hmeet : FirstOrder.Language.MeetsDefinable (L := LRc) (S₁ : Set K) :=
    Work.WilC5.meetsDefinable_of_dclClosed (M := K) hOM hS₁dcl
  have helem : S₁.IsElementary := by
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := LRc) (M := K)
      (A := (S₁ : Set K)) hmeet
    rwa [FirstOrder.Language.Substructure.closure_eq S₁] at h
  let ES : LRc.ElementarySubstructure K := ⟨S₁, helem⟩
  -- ## `w` is definable from `B ∪ range a` at the canonical structure
  have hdclEq' : @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ Set.range a)
      = @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ Set.range a) :=
    congrArg (fun i => @Work.WilC2.Dcl K i ((B : Set K) ∪ Set.range a)) hstruct.symm
  have hw₁ : w ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ Set.range a) := by
    rw [hdclEq']; exact hw
  have hbdef : ((ES : Set K) ∪ Set.range a).Definable LRc {fun _ : Fin 1 => w} := by
    have h1 : Work.WilC4.DefinableElt ((B : Set K) ∪ Set.range a) ∅ w :=
      (Work.WilC5.S4Exp.mem_dcl_iff_definableElt_hy ((B : Set K) ∪ Set.range a) w).mp hw₁
    have h2 : ((B : Set K) ∪ Set.range a).Definable LRc {fun _ : Fin 1 => w} := by
      simpa [Work.WilC4.DefinableElt, Set.union_empty] using h1
    have h3 : (ES : Set K) = (B : Set K) := rfl
    simpa [h3] using h2
  -- ## vdDMM (3.9): an integer relation between `v w` and the values of the generators
  obtain ⟨q, nn, hnne, c, hcES, hc0, hunit⟩ :=
    Work.WilC5.SpanContain (M := K) hVI ES a hw0 hbdef hind
  -- ## The algebraic part: `v (w ^ nn) = v (c⁻¹ ∏ aᵢ ^ (-qᵢ))`
  have hcS₁ : c ∈ (S₁ : Set K) := hcES
  have hPne : ∀ (N : Fin n → ℤ), (∏ i, a i ^ (N i)) ≠ 0 :=
    fun N => Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (ha0 i))
  have hPinv : (∏ i, a i ^ (-(q i)))⁻¹ = ∏ i, a i ^ (q i) := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [zpow_neg, inv_inv])
  have hz0a : c⁻¹ * (∏ i, a i ^ (-(q i))) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hc0) (hPne _)
  have hSAa : Work.WilC5.SameArch (w ^ nn) (c⁻¹ * (∏ i, a i ^ (-(q i)))) := by
    refine (Work.WilC5.SameArch_iff_IsUnitVal_div hz0a).mpr ?_
    have hq : w ^ nn / (c⁻¹ * (∏ i, a i ^ (-(q i)))) = c * w ^ nn * (∏ i, a i ^ (q i)) := by
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hPinv]
      ring
    rw [hq]
    exact hunit
  have hrcB : ∀ r : ℝ, Work.WilC5.realConst K r ∈ (B : Set K) :=
    fun r => Work.WilC5.S4Exp.mem_realConst (K := K) (S₁ : Set K) hS₁dcl r
  have hcinvB : c⁻¹ ∈ (B : Set K) :=
    Work.WilC5.S4Exp.dcl_mem_inv (K := K) (S₁ : Set K) hS₁dcl hcS₁ hc0
  -- ## vdDMM Lemma 4.2: `w ^ nn = z ∏ aᵢ ^ Nᵢ (1 + ε)`
  rcases lt_trichotomy nn 0 with hlt | heq | hgt
  · -- `nn < 0`: invert the relation, `Q := -nn`
    have hSA' : Work.WilC5.SameArch (w ^ (-nn)) (c * (∏ i, a i ^ (q i))) := by
      have h := Work.WilC5.SameArch_inv hSAa
      have h1 : (w ^ nn)⁻¹ = w ^ (-nn) := by rw [zpow_neg]
      have h2 : (c⁻¹ * (∏ i, a i ^ (-(q i))))⁻¹ = c * (∏ i, a i ^ (q i)) := by
        rw [mul_inv_rev, inv_inv, hPinv, mul_comm]
      rwa [h1, h2] at h
    have hz0' : c * (∏ i, a i ^ (q i)) ≠ 0 := mul_ne_zero hc0 (hPne _)
    obtain ⟨r, hrne, ε, hε, heqε⟩ := Work.WilC5.decomposition_of_same_value (M := K) hz0' hSA'
    refine ⟨-nn, by omega, q, Work.WilC5.realConst K r * c, ?_, ?_, ε, hε, ?_⟩
    · exact Work.WilC5.S4Exp.mem_mul (K := K) (S₁ : Set K) hS₁dcl (hrcB r) hcS₁
    · exact mul_ne_zero (Work.WilC5.realConst_ne_zero hrne) hc0
    · rw [heqε]; ring
  · exact absurd heq hnne
  · -- `nn > 0`: the relation itself, `Q := nn`
    obtain ⟨r, hrne, ε, hε, heqε⟩ :=
      Work.WilC5.decomposition_of_same_value (M := K) hz0a hSAa
    refine ⟨nn, hgt, fun i => -(q i), Work.WilC5.realConst K r * c⁻¹, ?_, ?_, ε, hε, ?_⟩
    · exact Work.WilC5.S4Exp.mem_mul (K := K) (S₁ : Set K) hS₁dcl (hrcB r) hcinvB
    · exact mul_ne_zero (Work.WilC5.realConst_ne_zero hrne) (inv_ne_zero hc0)
    · rw [heqε]; ring

end Work.WilC5
