import Mathlib
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.model_TR_of_dcl_closed

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## Auxiliary ingredients

`StepExpCut` compares the cut that `exp a` defines in a `dcl`-closed substructure `B` of a model
`K ⊨ T_e` with the cut that `exp (τ a)` defines in a model `L ⊨ T_r`, where `τ : B ↪[LRc] L`
preserves the definable logarithm.  The proof uses:

* `B` is an *elementary* `LRc`-substructure of `K` (from `dcl`-closure and o-minimality), and
  `τ` is elementary because `T_r` is model complete — so `τ` is an order embedding on `B`;
* `t < exp u ↔ log t < u` for positive `t`, from the strict monotonicity of `exp` and
  `exp (log t) = t` on positive `t`. -/

/-- The two-variable `LRc`-formula whose realization is `leEL`. -/
def seLeForm2 : LRc.Formula (Fin 2) :=
  leFormL (Term.var (Sum.inl (0 : Fin 2))) (Term.var (Sum.inl (1 : Fin 2)))

theorem seLeForm2_realize {M : Type} [LRc.Structure M] (v : Fin 2 → M) :
    seLeForm2.Realize v ↔ leEL (v 0) (v 1) := by
  have h := leFormL_realize (t₁ := Term.var (Sum.inl (0 : Fin 2)))
    (t₂ := Term.var (Sum.inl (1 : Fin 2))) (v := v) (xs := (default : Fin 0 → M))
  simpa [seLeForm2, Formula.Realize, Term.realize_var] using h

/-- The `LRc`-zero of a ring-like structure is the field zero. -/
theorem seZeroEL_eq_zero {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] :
    (Work.WilC5.zeroEL : M) = 0 := by
  have hb : ∀ (n : ℕ) (f : Language.ring.Functions n) (xs : Fin n → M),
      @Structure.funMap LRc M _ n (Sum.inl (Sum.inl f)) xs =
      @Structure.funMap Language.ring M _ n f xs :=
    fun n f xs => (Work.WilC2.instRingToLRcIsExpansionOn M).map_onFunction f xs
  rw [Work.WilC5.zeroEL, Work.WilC5.ringSymL, hb 0 Ring.zeroFunc (default : Fin 0 → M)]
  simp [Ring.CompatibleRing.funMap_zero]

/-- The zero of an `LRc`-substructure `B ≤ K`, seen in `K`, is the field zero of `K`. -/
theorem seZeroEL_coe {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [WilkiesDesign.CG.rexpL.Structure K]
    [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (B : WilkiesDesign.CG.LRc.Substructure K) :
    ((Work.WilC5.zeroEL : ↥B) : K) = (0 : K) := by
  have h := (Substructure.subtype B).map_fun (Work.WilC5.ringSymL Ring.zeroFunc)
    (default : Fin 0 → ↥B)
  have ht : (⇑(Substructure.subtype B) ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → K) :=
    Subsingleton.elim _ _
  rw [ht] at h
  have h2 : @Structure.funMap LRc K _ 0 (Work.WilC5.ringSymL Ring.zeroFunc)
      (default : Fin 0 → K) = (Work.WilC5.zeroEL : K) := rfl
  rw [h2] at h
  exact h.trans (seZeroEL_eq_zero)

/-- An `LRc`-embedding of the `rexp`-reducts sends the zero of the substructure to the zero. -/
theorem seTauZeroEL {K L : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [WilkiesDesign.CG.rexpL.Structure K]
    [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (B : WilkiesDesign.CG.LRc.Substructure K) (τ : WilkiesDesign.CG.LRc.Embedding B L) :
    τ (Work.WilC5.zeroEL : ↥B) = (0 : L) := by
  have h := τ.map_fun (Work.WilC5.ringSymL Ring.zeroFunc) (default : Fin 0 → ↥B)
  have ht : (τ ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → L) := Subsingleton.elim _ _
  rw [ht] at h
  have h2 : @Structure.funMap LRc L _ 0 (Work.WilC5.ringSymL Ring.zeroFunc)
      (default : Fin 0 → L) = (Work.WilC5.zeroEL : L) := rfl
  rw [h2] at h
  exact h.trans (seZeroEL_eq_zero)

/-- **Strict monotonicity of `exp`, in the field order**, for a model of `T_e` in which the
definable order `leE` is the field order. -/
theorem seExpLt {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LEc M]
    [LinearOrder M] (hTE : M ⊨ WilkiesDesign.CG.TE)
    (hleneg : ∀ x y : M, Work.WilC5.leE x y ↔ x ≤ y) (x y : M) :
    Work.WilC5.expE x < Work.WilC5.expE y ↔ x < y := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge (a := x) (b := y),
    ← hleneg (Work.WilC5.expE x) (Work.WilC5.expE y),
    ← hleneg (Work.WilC5.expE y) (Work.WilC5.expE x),
    ← hleneg x y, ← hleneg y x]
  exact Work.WilC5.expE_lt_expE_iff_of_model hTE x y

theorem StepExpCut {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (hTEK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hTEL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (a : ↥B) (τ : WilkiesDesign.CG.LRc.Embedding B L)
    (hτlog : ∀ x : B, τ ⟨Work.WilC5.logFun (x : K), hBlog (x : K) x.2⟩ = Work.WilC5.logFun (τ x)) :
    (∀ f : B, ((f : K) < Work.WilC5.expE (a : K) ↔ (τ f : L) < Work.WilC5.expE (τ a))) ∧
      (∀ f : B, (Work.WilC5.expE (a : K) < (f : K) ↔ Work.WilC5.expE (τ a) < τ f)) := by
  classical
  -- ## 0. `B` is an elementary `LRc`-substructure of `K`, hence a model of `T_r`
  have hBie : B.IsElementary := by
    have hmeet : FirstOrder.Language.MeetsDefinable (L := LRc) (B : Set K) :=
      Work.WilC5.meetsDefinable_of_dclClosed hOM hBdcl
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := LRc) (M := K)
      (A := (B : Set K)) hmeet
    rwa [Substructure.closure_eq] at h
  have hBTR : (↥B) ⊨ WilkiesDesign.CG.TR :=
    Work.WilC5.model_TR_of_dcl_closed hOM B hBdcl
  -- ## 1. `τ` is an order embedding of `B` into `L`
  have hτle : ∀ x y : ↥B, (x : K) ≤ (y : K) ↔ τ x ≤ τ y := by
    intro x y
    have h1 : leEL (x : K) (y : K) ↔ leEL x y := by
      have hh := hBie seLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [seLeForm2_realize, seLeForm2_realize] at hh
      simpa using hh
    have h2 : leEL (τ x) (τ y) ↔ leEL x y := by
      haveI := hBTR
      have hh := hMCr (↥B) L τ seLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [seLeForm2_realize, seLeForm2_realize] at hh
      simpa using hh
    calc (x : K) ≤ (y : K)
        ↔ leEL (x : K) (y : K) := (Work.WilC5.leEL_iff_le (M := K)
            (inferInstance : K ⊨ WilkiesDesign.CG.TR) (x : K) (y : K)).symm
      _ ↔ leEL x y := h1
      _ ↔ leEL (τ x) (τ y) := h2.symm
      _ ↔ τ x ≤ τ y := Work.WilC5.leEL_iff_le (M := L)
            (inferInstance : L ⊨ WilkiesDesign.CG.TR) (τ x) (τ y)
  have hτlt : ∀ x y : ↥B, (x : K) < (y : K) ↔ τ x < τ y := by
    intro x y
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge (a := τ x) (b := τ y), hτle x y, hτle y x]
  -- ## 2. The zero of `B` is `0` in both `K` and `L`
  have hzB : ((Work.WilC5.zeroEL : ↥B) : K) = 0 := seZeroEL_coe B
  have hτzB : τ (Work.WilC5.zeroEL : ↥B) = 0 := seTauZeroEL B τ
  have hτle0 : ∀ f : ↥B, (f : K) ≤ 0 ↔ τ f ≤ 0 := by
    intro f
    have h := hτle f (Work.WilC5.zeroEL : ↥B)
    rwa [hzB, hτzB] at h
  -- ## 3. `exp` is strictly increasing, and inverse to `logFun` on positives
  have hexpK : ∀ x y : K, Work.WilC5.expE x < Work.WilC5.expE y ↔ x < y :=
    fun x y => seExpLt (M := K) hTEK hlenegK x y
  have hexpL : ∀ x y : L, Work.WilC5.expE x < Work.WilC5.expE y ↔ x < y :=
    fun x y => seExpLt (M := L) hTEL hlenegL x y
  have hposK : (0 : K) < Work.WilC5.expE (a : K) :=
    (Work.WilC5.S4ExpF.leE_zero_iff hTEK haddK hlenegK (Work.WilC5.expE (a : K))).mp
      (Work.WilC5.expE_pos_of_model hTEK (a : K))
  have hposL : (0 : L) < Work.WilC5.expE (τ a) :=
    (Work.WilC5.S4ExpF.leE_zero_iff hTEL haddL hlenegL (Work.WilC5.expE (τ a))).mp
      (Work.WilC5.expE_pos_of_model hTEL (τ a))
  have hlogK : ∀ w : K, 0 < w → Work.WilC5.expE (Work.WilC5.logFun w) = w := fun w hw =>
    Work.WilC5.expE_logFun_of_pos_of_model hTEK
      ((Work.WilC5.S4ExpF.leE_zero_iff hTEK haddK hlenegK w).mpr hw)
  have hlogL : ∀ w : L, 0 < w → Work.WilC5.expE (Work.WilC5.logFun w) = w := fun w hw =>
    Work.WilC5.expE_logFun_of_pos_of_model hTEL
      ((Work.WilC5.S4ExpF.leE_zero_iff hTEL haddL hlenegL w).mpr hw)
  constructor
  · -- ## 4. First conjunct: the cut `· < exp a`
    intro f
    by_cases hf : (f : K) ≤ 0
    · -- below `exp a`: both statements hold
      exact iff_of_true (lt_of_le_of_lt hf hposK)
        (lt_of_le_of_lt ((hτle0 f).mp hf) hposL)
    · -- `f > 0`: reduce to the comparison of `log f` with `a`
      have hfpos : (0 : K) < (f : K) := lt_of_not_ge hf
      have hτfpos : (0 : L) < τ f := lt_of_not_ge (fun hle => hf ((hτle0 f).mpr hle))
      have hflog : (f : K) = Work.WilC5.expE (Work.WilC5.logFun (f : K)) :=
        (hlogK (f : K) hfpos).symm
      have hτflog : τ f = Work.WilC5.expE (Work.WilC5.logFun (τ f)) :=
        (hlogL (τ f) hτfpos).symm
      let hx : ↥B := ⟨Work.WilC5.logFun (f : K), hBlog (f : K) f.2⟩
      have hxτ : τ hx = Work.WilC5.logFun (τ f) := hτlog f
      have hA : (f : K) < Work.WilC5.expE (a : K) ↔
          Work.WilC5.logFun (f : K) < (a : K) := by
        conv_lhs => rw [hflog]
        exact hexpK (Work.WilC5.logFun (f : K)) (a : K)
      have hB : τ f < Work.WilC5.expE (τ a) ↔ Work.WilC5.logFun (τ f) < τ a := by
        conv_lhs => rw [hτflog]
        exact hexpL (Work.WilC5.logFun (τ f)) (τ a)
      have hC : Work.WilC5.logFun (f : K) < (a : K) ↔
          Work.WilC5.logFun (τ f) < τ a := by
        rw [← hxτ]
        exact hτlt hx a
      exact hA.trans (hC.trans hB.symm)
  · -- ## 5. Second conjunct: the cut `exp a < ·`
    intro f
    by_cases hf : (f : K) ≤ 0
    · -- below `exp a`: both statements fail
      refine iff_of_false ?_ ?_
      · exact not_lt.mpr (le_trans hf (le_of_lt hposK))
      · exact not_lt.mpr (le_trans ((hτle0 f).mp hf) (le_of_lt hposL))
    · have hfpos : (0 : K) < (f : K) := lt_of_not_ge hf
      have hτfpos : (0 : L) < τ f := lt_of_not_ge (fun hle => hf ((hτle0 f).mpr hle))
      have hflog : (f : K) = Work.WilC5.expE (Work.WilC5.logFun (f : K)) :=
        (hlogK (f : K) hfpos).symm
      have hτflog : τ f = Work.WilC5.expE (Work.WilC5.logFun (τ f)) :=
        (hlogL (τ f) hτfpos).symm
      let hx : ↥B := ⟨Work.WilC5.logFun (f : K), hBlog (f : K) f.2⟩
      have hxτ : τ hx = Work.WilC5.logFun (τ f) := hτlog f
      have hA : Work.WilC5.expE (a : K) < (f : K) ↔
          (a : K) < Work.WilC5.logFun (f : K) := by
        conv_lhs => rw [hflog]
        exact hexpK (a : K) (Work.WilC5.logFun (f : K))
      have hB : Work.WilC5.expE (τ a) < τ f ↔ τ a < Work.WilC5.logFun (τ f) := by
        conv_lhs => rw [hτflog]
        exact hexpL (τ a) (Work.WilC5.logFun (τ f))
      have hC : (a : K) < Work.WilC5.logFun (f : K) ↔
          τ a < Work.WilC5.logFun (τ f) := by
        rw [← hxτ]
        exact hτlt a hx
      exact hA.trans (hC.trans hB.symm)

end Work.WilC5
