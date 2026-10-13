import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.definableElt_of_mem_left
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.stdPart

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5.S4Exp

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. Bridge facts between the `LEc`/`LRc` symbols and the field operations

`hynew_exp` assumes the componentwise compatibility of the `LEc`-structure of `K` with the
field operations (`hadd`, `hmul`, `hone`, `hleneg`) and that its restricted exponential is
`rexpFromExp` (`hrexp`).  The lemmas below put the *other* ring operations of `LEc` (which are not
among the hypotheses) in the same normal form, by transferring the corresponding `TE`-sentences,
and record the resulting description of `absLeOne`. -/

section Bridge

variable {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]

/-- The `LEc`-formula `0 + x = x`. -/
private def zeroAddForm : LEc.BoundedFormula Empty 1 :=
  Term.bdEqual (eAdd (eZero) (v1 0)) (v1 0)

private theorem zeroAddForm_realize {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    (zeroAddForm).Realize (emptyVar : Empty → M) xs ↔ addE (zeroE : M) (xs 0) = xs 0 := by
  rw [zeroAddForm, BoundedFormula.realize_bdEqual]
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eZero]

private theorem zeroAddForm_real (xs : Fin 1 → ℝ) :
    (zeroAddForm).Realize (emptyVar : Empty → ℝ) xs := by
  rw [zeroAddForm_realize, addE_real, zeroE_real, zero_add]

/-- **`0` is the additive identity of a model of `TE`** (transferred from `ℝ`). -/
theorem addE_zeroE_of_model {M : Type} [LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M TE) (x : M) :
    addE (zeroE : M) x = x := by
  have h := transfer hM zeroAddForm zeroAddForm_real ![x]
  rwa [zeroAddForm_realize] at h

/-- The `LEc`-formula `x + (-x) = 0`. -/
private def negAddForm : LEc.BoundedFormula Empty 1 :=
  Term.bdEqual (eAdd (v1 0) (eNeg (v1 0))) (eZero)

private theorem negAddForm_realize {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    (negAddForm).Realize (emptyVar : Empty → M) xs ↔ addE (xs 0) (negE (xs 0)) = zeroE := by
  rw [negAddForm, BoundedFormula.realize_bdEqual]
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eNeg, realize_eZero]

private theorem negAddForm_real (xs : Fin 1 → ℝ) :
    (negAddForm).Realize (emptyVar : Empty → ℝ) xs := by
  rw [negAddForm_realize, addE_real, negE_real, zeroE_real, add_neg_cancel]

/-- **`x + (-x) = 0` in a model of `TE`** (transferred from `ℝ`). -/
theorem addE_negE_of_model {M : Type} [LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M TE) (x : M) :
    addE x (negE x) = zeroE := by
  have h := transfer hM negAddForm negAddForm_real ![x]
  rwa [negAddForm_realize] at h

end Bridge

section BridgeK

variable {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K TE)
    (hadd : ∀ x y : K, addE x y = x + y)

include hTE hadd

/-- The `LEc`-zero of `K` is the field zero (using `K ⊨ TE` and `hadd`). -/
theorem zeroE_eq_zero : (zeroE : K) = 0 := by
  have h := addE_zeroE_of_model hTE (0 : K)
  rw [hadd] at h
  simpa using h

/-- The `LEc`-negation of `K` is the field negation. -/
theorem negE_eq_neg (x : K) : negE x = -x := by
  have h := addE_negE_of_model hTE x
  rw [hadd, zeroE_eq_zero hTE hadd] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The `LEc`-subtraction of `K` is the field subtraction. -/
theorem subE_eq_sub (x y : K) : subE x y = x - y := by
  rw [subE, hadd, negE_eq_neg hTE hadd]
  ring

end BridgeK

section AbsLe

variable {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K TE)
    (hadd : ∀ x y : K, addE x y = x + y)
    (hone : (oneE : K) = 1)
    (hleneg : ∀ x y : K, leE x y ↔ x ≤ y)

include hTE hadd hone hleneg

/-- `absLeOne` (the ring formula `|x| ≤ 1`) is the field condition `|x| ≤ 1`. -/
theorem absLeOne_iff_abs (x : K) : absLeOne x ↔ |x| ≤ 1 := by
  have hn : ∀ y : K, negE y = -y := negE_eq_neg hTE hadd
  have hs : ∀ y z : K, subE y z = y - z := subE_eq_sub hTE hadd
  have hinv1 : (x ≤ oneE) ↔ (x ≤ 1) := by rw [hone]
  have hinv2 : (negE oneE ≤ x) ↔ (-1 ≤ x) := by rw [hn oneE, hone]
  have h1 : isSquare (subE oneE x) ↔ x ≤ oneE := by rw [← hleneg x oneE, leE]
  have h2 : isSquare (addE oneE x) ↔ negE oneE ≤ x := by
    have hkey : subE x (negE oneE) = addE oneE x := by
      rw [hs, hn, hadd]; ring
    rw [← hkey, ← hleneg (negE oneE) x, leE]
  rw [absLeOne, h1, h2, hinv1, hinv2, abs_le]
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hB, hA⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hB, hA⟩

end AbsLe

/-! ## 2. Closure of a `Dcl`-closed parameter set under the field operations -/

section Closure

variable {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K TR]

/-- The `rexp`-symbol of `LR = ring ⊕ rexpL`. -/
def rexpSymR : LR.Functions 1 := Sum.inr rexpFunc.rexp
/-- The `rexp`-symbol of `LRc`. -/
def rexpSymL : LRc.Functions 1 := Sum.inl rexpSymR

/-- The `rexp`-symbol of `LRc` is interpreted by `rexpFromExp`. -/
theorem rexpSymL_funMap
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap rexpL K _ 1
        rexpFunc.rexp ![x] = rexpFromExp x) (x : K) :
    @FirstOrder.Language.Structure.funMap LRc K _ 1 rexpSymL ![x] = rexpFromExp x := by
  simp only [rexpSymL, rexpSymR]
  exact hrexp x

/-- Realization of the `LRc`-term `rexp x`. -/
theorem realize_rexpSymL {M : Type} [LRc.Structure M] (x : M) :
    Term.realize ![x] (Term.func rexpSymL ![Term.var 0]) =
      @FirstOrder.Language.Structure.funMap LRc M _ 1 rexpSymL ![x] := by
  rw [Term.realize_func]
  congr 1
  funext i
  fin_cases i
  simp

variable (A : Set K)
    (hAdcl : @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A ⊆ A)

/-- Every element of `A` is definable from `A` (its singleton is named by itself). -/
theorem subset_dcl : A ⊆ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A :=
  fun _ hx => by
    rw [Work.WilC2.mem_dcl]
    exact Set.Definable.singleton_of_mem LRc hx

include A hAdcl

/-- Under `hAdcl` the parameter set `A` *is* its definable closure. -/
theorem dcl_eq : @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A = A :=
  le_antisymm hAdcl (subset_dcl A)

/-- An `LRc`-term evaluated at a tuple of elements of `A` lies in `A`. -/
theorem mem_term {n : ℕ} (t : LRc.Term (Fin n)) (x : Fin n → K) (hx : ∀ i, x i ∈ A) :
    Term.realize x t ∈ A :=
  hAdcl (Work.WilC5.term_realize_mem_dcl t x hx)

/-- `A` is closed under multiplication. -/
theorem mem_mul {x y : K} (hx : x ∈ A) (hy : y ∈ A) : x * y ∈ A := by
  have h := mem_term A hAdcl (tMulL (Term.var 0) (Term.var 1)) ![x, y]
    (by intro i; fin_cases i <;> assumption)
  rw [Work.WilC5.realize_tMulL] at h
  simp only [Term.realize_var] at h
  rwa [Work.WilC5.mulEL_eq_mul] at h

/-- `A` is closed under subtraction. -/
theorem mem_sub {x y : K} (hx : x ∈ A) (hy : y ∈ A) : x - y ∈ A := by
  have h := mem_term A hAdcl (tSubL (Term.var 0) (Term.var 1)) ![x, y]
    (by intro i; fin_cases i <;> assumption)
  rw [tSubL, Work.WilC5.realize_tAddL, Work.WilC5.realize_tNegL] at h
  simp only [Term.realize_var] at h
  rw [Work.WilC5.addEL_eq_add, Work.WilC5.negEL_eq_neg] at h
  simpa [sub_eq_add_neg] using h

/-- The real constants of `K` lie in `A`. -/
theorem mem_realConst (r : ℝ) : realConst K r ∈ A := by
  have h := mem_term A hAdcl (Work.WilC5.constTermL (α := Fin 0) r) (fun i => i.elim0)
    (fun i => i.elim0)
  rwa [Work.WilC5.realize_constTermL] at h

/-- `A` is closed under the restricted exponential. -/
theorem mem_rexp
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap rexpL K _ 1
        rexpFunc.rexp ![x] = rexpFromExp x) {x : K} (hx : x ∈ A) :
    rexpFromExp x ∈ A := by
  have h := mem_term A hAdcl (Term.func rexpSymL ![Term.var 0]) ![x]
    (by intro i; fin_cases i; exact hx)
  rw [realize_rexpSymL] at h
  rwa [rexpSymL_funMap (K := K) hrexp x] at h

end Closure

/-! ## 3. Closure of `A` under inversion -/

section Aux

variable {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]

/-- `Work.WilC2.Dcl` (singletons through `Set.Definable₁`) and `Work.WilC4.DefinableElt`
(singletons as constant `Fin 1`-tuples) describe the same definable closure. -/
theorem mem_dcl_iff_definableElt_hy (A : Set K) (x : K) :
    x ∈ (@Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A) ↔
      Work.WilC4.DefinableElt A ∅ x := by
  have hset : {v : Fin 1 → K | v 0 ∈ ({x} : Set K)} = {fun _ : Fin 1 => x} := by
    ext v; simp [funext_iff]
  rw [Work.WilC2.mem_dcl, Work.WilC4.DefinableElt, Set.union_empty, Set.Definable₁, hset]

/-- **Inversion preserves `A`.**  If `x ∈ A` and `x ≠ 0` then the singleton `{x⁻¹}` is definable
from the parameter `x ∈ A`, hence `x⁻¹ ∈ Dcl A ⊆ A`. -/
theorem dcl_mem_inv (A : Set K)
    (hAdcl : @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) A ⊆ A)
    {c : K} (hc : c ∈ A) (hc0 : c ≠ 0) : c⁻¹ ∈ A := by
  have h1 : Work.WilC4.DefinableElt A (∅ : Set K) c :=
    Work.WilC4.definableElt_of_mem_left A ∅ hc
  exact hAdcl ((mem_dcl_iff_definableElt_hy (K := K) A c⁻¹).mpr
    (Work.WilC4.dcl_inv h1 hc0))

end Aux

/-! ## 4. The logarithm of an element of `[1/2, 3/2]` lies in `[-1,1]` -/

section LogBound

/-- The `LEc`-formula `logDefSet (1+δ) y → |2δ| ≤ 1 → |y| ≤ 1`. -/
def absLeBoundForm : LEc.BoundedFormula Empty 2 :=
  Work.WilC5.logPairForm.imp (Work.WilC5.absLeTwoForm.imp
    (Work.WilC5.absLeOneForm (Work.WilC5.v2 1)))

theorem absLeBoundForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    (absLeBoundForm).Realize (emptyVar : Empty → M) xs ↔
      (logDefSet (addE oneE (xs 0)) (xs 1) →
        absLeOne (mulE (addE oneE oneE) (xs 0)) → absLeOne (xs 1)) := by
  simp only [absLeBoundForm, BoundedFormula.realize_imp, Work.WilC5.logPairForm_realize,
    Work.WilC5.absLeTwoForm_realize, Work.WilC5.absLeOneForm_realize, Work.WilC5.v2,
    Term.realize_var, Sum.elim_inr]

theorem absLeBoundForm_real (xs : Fin 2 → ℝ) :
    (absLeBoundForm).Realize (emptyVar : Empty → ℝ) xs := by
  rw [absLeBoundForm_realize]
  intro hy hx
  by_contra hcon
  have hrexp := real_logDefSet_one_add_rexp hy hx
  rw [rexpFromExp_of_not_absLeOne hcon, zeroE_real, addE_real, oneE_real] at hrexp
  rw [absLeOne_real] at hx
  have h1 : |2 * xs 0| ≤ 1 := by
    have h : mulE (addE oneE oneE) (xs 0) = 2 * xs 0 := by
      rw [mulE_real, addE_real, oneE_real]; norm_num
    rwa [h] at hx
  have h2 : (0 : ℝ) < 1 + xs 0 := by
    have := (abs_le.mp h1).1
    linarith
  linarith

/-- **The logarithm of an element of `[1/2, 3/2]` lies in `[-1,1]`.**  This is the real statement
`|2δ| ≤ 1 → y = log (1+δ) → |y| ≤ 1`, transferred to a model of `TE`. -/
theorem absLeOne_of_logDefSet {M : Type} [LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M TE) {ε y : M}
    (hε : absLeOne (mulE (addE oneE oneE) ε))
    (h : logDefSet (addE oneE ε) y) : absLeOne y := by
  have hm := transfer hM absLeBoundForm absLeBoundForm_real ![ε, y]
  rw [absLeBoundForm_realize] at hm
  exact hm h hε

end LogBound

theorem hynew_exp {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (A : Set K)
    (hAdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) A ⊆ A)
    (hAlog : ∀ x ∈ A, Work.WilC5.logFun x ∈ A) (a : K) (ha : a ∈ A)
    (hx : Work.WilC5.expE a ∉ A) :
    ∀ c ∈ A, c ≠ 0 → ¬ WilkiesDesign.CG.IsUnitVal (c * Work.WilC5.expE a) := by
  intro c hc hc0 hunit
  -- ## bridge facts
  have hz0 : (zeroE : K) = 0 := zeroE_eq_zero hTE hadd
  have hle : ∀ x y : K, leE x y ↔ x ≤ y := hleneg
  have hza : ∀ x : K, absLeOne x ↔ |x| ≤ 1 := fun x => absLeOne_iff_abs hTE hadd hone hleneg x
  -- ## `c⁻¹ ∈ A`, so `expE a` has the value of an element of `A`
  have hcinv : c⁻¹ ∈ A := dcl_mem_inv A hAdcl hc hc0
  have hcne : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hSA : SameArch (expE a) c⁻¹ := by
    rw [SameArch_iff_IsUnitVal_div hcne]
    simpa [div_inv_eq_mul, mul_comm] using hunit
  -- ## the vdDMM 4.2 decomposition `exp a = z (1 + ε)` with `z ∈ A` and `ε` infinitesimal
  obtain ⟨r, hr0, ε, hε, hdec⟩ := decomposition_of_same_value hcne hSA
  set z : K := realConst K r * c⁻¹ with hzdef
  have hzA : z ∈ A := by
    rw [hzdef]
    exact mem_mul A hAdcl (mem_realConst A hAdcl r) hcinv
  have hexpz : expE a = z * (1 + ε) := by
    rw [hzdef]; exact hdec
  -- ## `1 + ε` is positive, hence `z` is positive
  have hεhalf : |ε| ≤ (2 : K)⁻¹ := by
    have h := hε 1
    have h2 : (((1 : ℕ) : K) + 1) = (2 : K) := by norm_num
    rwa [h2] at h
  have hε1 : |ε| < 1 := by
    have h3 : (2 : K)⁻¹ < 1 := by
      have h := (inv_lt_inv₀ (show (0 : K) < 2 by norm_num)
        (show (0 : K) < 1 by norm_num)).mpr (show (1 : K) < 2 by norm_num)
      simpa using h
    exact lt_of_le_of_lt hεhalf h3
  have h1e_pos : 0 < 1 + ε := by
    have h := (abs_lt.mp hε1).1
    linarith
  have hea_pos : 0 < expE a := by
    have h := expE_pos_of_model hTE a
    rw [hle zeroE (expE a), hle (expE a) zeroE, hz0] at h
    linarith [h.1, h.2]
  have hzpos : 0 < z := by
    have h := hea_pos
    rw [hexpz] at h
    exact pos_of_mul_pos_left h (le_of_lt h1e_pos)
  have hzle : leE zeroE z ∧ ¬ leE z zeroE := by
    rw [hle zeroE z, hle z zeroE, hz0]
    exact ⟨le_of_lt hzpos, not_le_of_gt hzpos⟩
  have h1e_pos' : leE zeroE (1 + ε) ∧ ¬ leE (1 + ε) zeroE := by
    rw [hle zeroE (1 + ε), hle (1 + ε) zeroE, hz0]
    exact ⟨le_of_lt h1e_pos, not_le_of_gt h1e_pos⟩
  -- ## `t := a - log z` is the logarithm of `1 + ε`, hence `|t| ≤ 1`
  have hzlog : logFun z ∈ A := hAlog z hzA
  have htA : a - logFun z ∈ A := mem_sub A hAdcl ha hzlog
  have ht_eq : a - logFun z = logFun (1 + ε) := by
    have hlm := logFun_mul hTE hzle h1e_pos'
    have hmulz : mulE z (1 + ε) = expE a := by rw [hmul]; exact hexpz.symm
    rw [hmulz, logFun_expE hTE a, hadd] at hlm
    linarith
  have hlog : logDefSet (addE oneE ε) (a - logFun z) := by
    have h1e : addE oneE ε = 1 + ε := by rw [hadd, hone]
    rw [h1e]
    have h := logFun_spec_of_model hTE (1 + ε)
    rwa [← ht_eq] at h
  have h2ε : absLeOne (mulE (addE oneE oneE) ε) := by
    rw [hza, hmul, hadd, hone, abs_mul]
    have h2 : |(1 : K) + 1| = 2 := by
      rw [abs_of_nonneg (by norm_num : (0 : K) ≤ 1 + 1)]; norm_num
    rw [h2]
    have h2inv : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ (by norm_num)
    linarith [hεhalf]
  have habs : absLeOne (a - logFun z) := absLeOne_of_logDefSet hTE h2ε hlog
  have hexptA : expE (a - logFun z) ∈ A := by
    have h := mem_rexp A hAdcl hrexp htA
    rwa [rexpFromExp_of_absLeOne habs] at h
  -- ## conclude `exp a ∈ A`
  have hexpa : expE a ∈ A := by
    have hm : expE a = z * expE (a - logFun z) := by
      rw [hexpz, ht_eq, expE_logFun_of_pos hTE h1e_pos']
    rw [hm]
    exact mem_mul A hAdcl hzA hexptA
  exact hx hexpa

end Work.WilC5.S4Exp
