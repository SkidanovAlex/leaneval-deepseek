import Mathlib
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC2.Dcl

namespace Work.WilC5.S4ExpG

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

noncomputable section

/-! ## Auxiliary ingredients

`LRc` has no relation symbols: the order of a model of `TR` is the definable order
`leEL x y := ∃ z, z * z = y - x` (`LRcOps.lean`), and it agrees with the field order
(`leEL_iff_le.lean`).  The elementarity of the two embeddings

* `B ↪ K` (a `Dcl`-closed substructure of a model of `TR` is elementary, by o-minimality), and
* `B ↪ L` (`τ`, between two models of `TR`, elementary by model completeness),

is then applied to the two-variable `LRc`-formula defining `leEL`, giving the first two claims.
The comparison with `0` additionally needs the *`LRc`-zero* of `B`, which is the field zero of
both `K` and `L`. -/

/-- The two-variable `LRc`-formula whose realization is `leEL`. -/
def ocaLeForm2 : LRc.Formula (Fin 2) :=
  Work.WilC5.leFormL (Term.var (Sum.inl (0 : Fin 2))) (Term.var (Sum.inl (1 : Fin 2)))

theorem ocaLeForm2_realize {M : Type} [LRc.Structure M] (v : Fin 2 → M) :
    ocaLeForm2.Realize v ↔ Work.WilC5.leEL (v 0) (v 1) := by
  have h := Work.WilC5.leFormL_realize (t₁ := Term.var (Sum.inl (0 : Fin 2)))
    (t₂ := Term.var (Sum.inl (1 : Fin 2))) (v := v) (xs := (default : Fin 0 → M))
  simpa [ocaLeForm2, Formula.Realize, Term.realize_var] using h

/-- The `LRc`-zero of a ring-like structure is the field zero. -/
theorem ocaZeroEL_eq_zero {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
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
theorem ocaZeroEL_coe {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [WilkiesDesign.CG.rexpL.Structure K]
    [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (B : WilkiesDesign.CG.LRc.Substructure K) :
    ((Work.WilC5.zeroEL : ↥B) : K) = (0 : K) := by
  have hb : ∀ (n : ℕ) (f : Language.ring.Functions n) (xs : Fin n → K),
      @Structure.funMap LRc K _ n (Sum.inl (Sum.inl f)) xs =
      @Structure.funMap Language.ring K _ n f xs :=
    fun n f xs => (Work.WilC2.instRingToLRcIsExpansionOn K).map_onFunction f xs
  have hzK : (Work.WilC5.zeroEL : K) = 0 := by
    rw [Work.WilC5.zeroEL, Work.WilC5.ringSymL, hb 0 Ring.zeroFunc (default : Fin 0 → K)]
    simp [Ring.CompatibleRing.funMap_zero]
  have h := (Substructure.subtype B).map_fun (Work.WilC5.ringSymL Ring.zeroFunc)
    (default : Fin 0 → ↥B)
  have ht : (⇑(Substructure.subtype B) ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → K) :=
    Subsingleton.elim _ _
  rw [ht] at h
  have h2 : @Structure.funMap LRc K _ 0 (Work.WilC5.ringSymL Ring.zeroFunc)
      (default : Fin 0 → K) = (Work.WilC5.zeroEL : K) := rfl
  rw [h2] at h
  exact h.trans hzK

/-- An `LRc`-embedding of the `rexp`-reducts sends the zero of the substructure to the zero. -/
theorem ocaTauZeroEL {K L : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [WilkiesDesign.CG.rexpL.Structure K]
    [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (B : WilkiesDesign.CG.LRc.Substructure K) (τ : WilkiesDesign.CG.LRc.Embedding B L) :
    τ (Work.WilC5.zeroEL : ↥B) = (0 : L) := by
  have hb : ∀ (n : ℕ) (f : Language.ring.Functions n) (xs : Fin n → L),
      @Structure.funMap LRc L _ n (Sum.inl (Sum.inl f)) xs =
      @Structure.funMap Language.ring L _ n f xs :=
    fun n f xs => (Work.WilC2.instRingToLRcIsExpansionOn L).map_onFunction f xs
  have hzL : (Work.WilC5.zeroEL : L) = 0 := by
    rw [Work.WilC5.zeroEL, Work.WilC5.ringSymL, hb 0 Ring.zeroFunc (default : Fin 0 → L)]
    simp [Ring.CompatibleRing.funMap_zero]
  have h := τ.map_fun (Work.WilC5.ringSymL Ring.zeroFunc) (default : Fin 0 → ↥B)
  have ht : (τ ∘ (default : Fin 0 → ↥B)) = (default : Fin 0 → L) := Subsingleton.elim _ _
  rw [ht] at h
  have h2 : @Structure.funMap LRc L _ 0 (Work.WilC5.ringSymL Ring.zeroFunc)
      (default : Fin 0 → L) = (Work.WilC5.zeroEL : L) := rfl
  rw [h2] at h
  exact h.trans hzL

/-- **`τ` preserves and reflects the order on the `dcl`-closed substructure `B`** (to be proved in
namespace `Work.WilC5.S4ExpG`).

`K, L ⊨ TR` (each with a field structure, an `LRc`-structure via the canonical instances), `hMCr`
is model completeness of `TR`, `hOM` o-minimality of its models, `B ≤ K` is an `LRc`-substructure
which is `Dcl`-closed (`hBdcl`), and `τ : B ↪ L` is an `LRc`-embedding.  Then for all `x y : B`,

  `x ≤ y ↔ τ x ≤ τ y`,  `x < y ↔ τ x < τ y`,  `0 < x ↔ 0 < τ x`.

Proof idea: `B` is elementary in `K` (`hOM` + `hBdcl` via `MeetsDefinable.isElementary_closure`),
and `τ` is elementary because `TR` is model complete and `B ⊨ TR` by `model_TR_of_dcl_closed`.
The order of a model of `TR` is the `LRc`-definable order `leEL x y := ∃z, z*z = y - x`
(`leEL_iff_le`), so elementarity applied to the two-variable `LRc`-formula for `leEL` — computed in
`B` — gives both directions of the first two statements.  For the comparison with `0`, apply the
same elementarity to the one-variable formula `leEL c₀ v` (and `leEL v c₀`), where `c₀` is the
`LRc`-term for the ring zero constant, so that the corresponding element of `B` is produced by
`Term.realize`; then use that the `LRc`-zero of `K`, resp. `L`, is the field zero and that `leEL`
is `≤`. -/
theorem ord_cut_aux {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (B : Set K) ⊆ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding B L) :
    (∀ x y : ↥B, (((x : K) ≤ (y : K)) ↔ ((τ x : L) ≤ (τ y : L)))) ∧
      (∀ x y : ↥B, (((x : K) < (y : K)) ↔ ((τ x : L) < (τ y : L)))) ∧
      (∀ x : ↥B, (0 < (x : K) ↔ 0 < (τ x : L))) := by
  classical
  -- ## 0. `B` is an elementary `LRc`-substructure of `K`, hence a model of `TR`
  have hBie : B.IsElementary := by
    have hmeet : FirstOrder.Language.MeetsDefinable (L := LRc) (B : Set K) :=
      Work.WilC5.meetsDefinable_of_dclClosed hOM hBdcl
    have h := FirstOrder.Language.MeetsDefinable.isElementary_closure (L := LRc) (M := K)
      (A := (B : Set K)) hmeet
    rwa [Substructure.closure_eq] at h
  have hBTR : (↥B) ⊨ WilkiesDesign.CG.TR :=
    Work.WilC5.model_TR_of_dcl_closed hOM B hBdcl
  -- ## 1. `τ` preserves and reflects `≤`
  have hτle : ∀ x y : ↥B, (x : K) ≤ (y : K) ↔ τ x ≤ τ y := by
    intro x y
    -- elementarity of `B ⊆ K`
    have h1 : Work.WilC5.leEL (x : K) (y : K) ↔ Work.WilC5.leEL x y := by
      have hh := hBie ocaLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [ocaLeForm2_realize, ocaLeForm2_realize] at hh
      simpa using hh
    -- elementarity of `τ : B ↪ L`
    have h2 : Work.WilC5.leEL (τ x) (τ y) ↔ Work.WilC5.leEL x y := by
      haveI := hBTR
      have hh := hMCr (↥B) L τ ocaLeForm2 (fun i : Fin 2 => ![x, y] i)
      rw [ocaLeForm2_realize, ocaLeForm2_realize] at hh
      simpa using hh
    calc (x : K) ≤ (y : K)
        ↔ Work.WilC5.leEL (x : K) (y : K) := (Work.WilC5.leEL_iff_le (M := K)
            (inferInstance : K ⊨ WilkiesDesign.CG.TR) (x : K) (y : K)).symm
      _ ↔ Work.WilC5.leEL x y := h1
      _ ↔ Work.WilC5.leEL (τ x) (τ y) := h2.symm
      _ ↔ τ x ≤ τ y := Work.WilC5.leEL_iff_le (M := L)
            (inferInstance : L ⊨ WilkiesDesign.CG.TR) (τ x) (τ y)
  -- ## 2. `τ` preserves and reflects `<`
  have hτlt : ∀ x y : ↥B, (x : K) < (y : K) ↔ τ x < τ y := by
    intro x y
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge (a := τ x) (b := τ y), hτle x y, hτle y x]
  refine ⟨hτle, hτlt, ?_⟩
  -- ## 3. Comparison with `0`, applied to the `LRc`-zero of `B`
  intro x
  have h := hτlt (Work.WilC5.zeroEL : ↥B) x
  rwa [ocaZeroEL_coe B, ocaTauZeroEL B τ] at h

end

end Work.WilC5.S4ExpG
