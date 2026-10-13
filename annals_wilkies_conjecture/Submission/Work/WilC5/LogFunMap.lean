/-
  WilC5 — the definable logarithm is preserved by `LEc`-embeddings of models of `TE`.

  The definable logarithm `logFun` (`ExpLog.lean`) is the function whose graph is

      `logDefSet x y  =  ((0 < x) ∧ exp y = x) ∨ (¬ (0 < x) ∧ exp y = 1)`,

  i.e. `logDefSet` is the graph of the *unique* logarithm of a model of `TE`.  Since `logDefSet`
  is built from the function symbols of `LEc` (`addE`, `mulE`, `negE`, `zeroE`, `oneE`, `expE`) it is
  preserved by every `LEc`-embedding, and since in a model of `TE` it really is the graph of a
  function, its `Classical.choose`-value is preserved as well: this module proves

  `Work.WilC5.LogFunMap  :  f (logFun x) = logFun (f x)`.

  The two facts about models of `TE` that this needs — `exp` is injective and surjective onto the
  positive elements — are transferred from `ℝ` with `Work.WilC5.transfer` (`ReductEmb.lean`), the
  same way the order facts used there are obtained.  This is the input of
  `Work.WilC5.LogStructEmbedding`.
-/
import Mathlib
import Submission.Work.WilC5.ExpLog

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. Transfer of `exp`-facts from `ℝ` to models of `TE` -/

/-- Injectivity of the exponential, as an `LEc`-formula: `exp x = exp y → x = y`. -/
def injForm : LEc.BoundedFormula Empty 2 :=
  (Term.bdEqual (eExp (v2 0)) (eExp (v2 1))).imp (Term.bdEqual (v2 0) (v2 1))

theorem injForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    injForm.Realize (emptyVar : Empty → M) xs ↔
      (expE (xs 0) = expE (xs 1) → xs 0 = xs 1) := by
  rw [injForm, BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_bdEqual]
  simp only [v2, Term.realize_var, Sum.elim_inr, realize_eExp]

theorem inj_real : ∀ xs : Fin 2 → ℝ, injForm.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [injForm_realize]
  intro h
  rw [expE_real, expE_real] at h
  exact Real.exp_injective h

/-- **The exponential is injective in every model of `TE`.** -/
theorem expE_injective_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (a b : M)
    (h : expE a = expE b) : a = b := by
  have hh := transfer hM injForm inj_real ![a, b]
  rw [injForm_realize] at hh
  exact hh (by simpa using h)

/-- The strict positivity predicate of an `LEc`-structure, as an `LEc`-formula:
`0 ≤ x ∧ ¬ (x ≤ 0)`, i.e. `0 < x` in a model of `TE`. -/
def posForm : LEc.BoundedFormula Empty 1 :=
  leForm (eZero : LEc.Term (Empty ⊕ Fin 1)) (v1 0) ⊓
    (leForm (v1 0) (eZero : LEc.Term (Empty ⊕ Fin 1))).not

/-- Surjectivity of the exponential onto the positive elements:
`0 < x → ∃ y, exp y = x`. -/
def surjForm : LEc.BoundedFormula Empty 1 :=
  posForm.imp ((Term.bdEqual (eExp (witTerm (l := 1))) (pushTerm (v1 0))).ex)

theorem posForm_realize {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    posForm.Realize (emptyVar : Empty → M) xs ↔
      (leE zeroE (xs 0) ∧ ¬ leE (xs 0) zeroE) := by
  rw [posForm, BoundedFormula.realize_inf, BoundedFormula.realize_not, leForm_realize,
    leForm_realize]
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eZero, leE]

theorem surjForm_realize {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    surjForm.Realize (emptyVar : Empty → M) xs ↔
      ((leE zeroE (xs 0) ∧ ¬ leE (xs 0) zeroE) → ∃ y : M, expE y = xs 0) := by
  rw [surjForm, BoundedFormula.realize_imp, posForm_realize, BoundedFormula.realize_ex]
  constructor
  · intro h hpos
    obtain ⟨a, ha⟩ := h hpos
    refine ⟨a, ?_⟩
    rw [BoundedFormula.realize_bdEqual] at ha
    simpa only [witTerm, Term.realize_var, Sum.elim_inr, Fin.snoc_last, realize_eExp,
      realize_pushTerm, snoc_comp_castSucc, v1, Sum.elim_inl, expE_def] using ha
  · intro h hpos
    obtain ⟨a, ha⟩ := h hpos
    refine ⟨a, ?_⟩
    rw [BoundedFormula.realize_bdEqual]
    simpa only [witTerm, Term.realize_var, Sum.elim_inr, Fin.snoc_last, realize_eExp,
      realize_pushTerm, snoc_comp_castSucc, v1, Sum.elim_inl, expE_def] using ha

theorem surj_real : ∀ xs : Fin 1 → ℝ, surjForm.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [surjForm_realize]
  intro hpos
  rw [leE, leE, isSquare_real, isSquare_real, subE_real, subE_real, zeroE_real] at hpos
  have h1 : 0 ≤ xs 0 := by linarith [hpos.1]
  have h2 : xs 0 ≤ 0 → False := fun h => hpos.2 (by linarith)
  have h3 : 0 < xs 0 := lt_of_not_ge h2
  exact ⟨Real.log (xs 0), by rw [expE_real, Real.exp_log h3]⟩

/-- **The exponential of a model of `TE` is surjective onto the positive elements.** -/
theorem expE_surj_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M)
    (hpos : leE zeroE x ∧ ¬ leE x zeroE) : ∃ y : M, expE y = x := by
  have h := transfer hM surjForm surj_real ![x]
  rw [surjForm_realize] at h
  exact h (by simpa using hpos)

/-- The equation `exp 0 = 1`. -/
def expZeroForm : LEc.BoundedFormula Empty 0 :=
  Term.bdEqual (eExp (eZero : LEc.Term (Empty ⊕ Fin 0))) (eOne : LEc.Term (Empty ⊕ Fin 0))

theorem expZeroForm_realize {M : Type} [LEc.Structure M] (xs : Fin 0 → M) :
    expZeroForm.Realize (emptyVar : Empty → M) xs ↔ expE (zeroE : M) = (oneE : M) := by
  rw [expZeroForm, BoundedFormula.realize_bdEqual]
  simp only [realize_eExp, realize_eZero, realize_eOne]

theorem expZero_real : ∀ xs : Fin 0 → ℝ, expZeroForm.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [expZeroForm_realize]
  rw [expE_real, zeroE_real, oneE_real, Real.exp_zero]

/-- **`exp 0 = 1` in every model of `TE`.** -/
theorem expE_zero_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) :
    expE (zeroE : M) = (oneE : M) := by
  have h := transfer hM expZeroForm expZero_real
  exact (expZeroForm_realize emptyBnd).mp (h emptyBnd)

/-! ## 2. The graph `logDefSet` is preserved by an `LEc`-embedding of models of `TE` -/

/-- The definable order is preserved *and* reflected by an `LEc`-embedding between models of
`TE` (`leE_map` is the forward direction, `leE_reflect` the backward one). -/
theorem leE_map_iff {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (hM : M ⊨ TE) (hN : N ⊨ TE) (f : M ↪[LEc] N) (x y : M) :
    leE (f x) (f y) ↔ leE x y :=
  ⟨leE_reflect f (le_total_of_model hM) (le_antisymm_of_model hN), leE_map f⟩

/-- The strict positivity predicate `0 < x` is preserved by an `LEc`-embedding of models of
`TE`. -/
theorem pos_map_iff {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (hM : M ⊨ TE) (hN : N ⊨ TE) (f : M ↪[LEc] N) (x : M) :
    (leE zeroE (f x) ∧ ¬ leE (f x) zeroE) ↔ (leE zeroE x ∧ ¬ leE x zeroE) := by
  have h0 : (zeroE : N) = f (zeroE : M) := (map_zeroE f).symm
  rw [h0, leE_map_iff hM hN f, leE_map_iff hM hN f]

/-- **The graph of the definable logarithm is preserved by an `LEc`-embedding of models of
`TE`.** -/
theorem logDefSet_map_iff {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (hM : M ⊨ TE) (hN : N ⊨ TE) (f : M ↪[LEc] N) (x y : M) :
    logDefSet (f x) (f y) ↔ logDefSet x y := by
  have hpos := pos_map_iff hM hN f x
  have h1 : expE (f y) = f x ↔ expE y = x := by
    rw [← map_expE f y]; exact f.injective.eq_iff
  have h2 : expE (f y) = (oneE : N) ↔ expE y = (oneE : M) := by
    rw [← map_expE f y, ← map_oneE f]; exact f.injective.eq_iff
  simp only [logDefSet]
  rw [hpos, h1, h2]

/-! ## 3. `logDefSet` is the graph of a total function in a model of `TE` -/

/-- **Existence**: every element of a model of `TE` has a logarithm. -/
theorem logDefSet_exists_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M) :
    ∃ y, logDefSet x y := by
  by_cases hpos : leE zeroE x ∧ ¬ leE x zeroE
  · obtain ⟨y, hy⟩ := expE_surj_of_model hM x hpos
    exact ⟨y, Or.inl ⟨hpos, hy⟩⟩
  · exact ⟨zeroE, Or.inr ⟨hpos, expE_zero_of_model hM⟩⟩

/-- **Uniqueness**: the logarithm of an element of a model of `TE` is unique. -/
theorem logDefSet_unique_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {x y₁ y₂ : M}
    (h₁ : logDefSet x y₁) (h₂ : logDefSet x y₂) : y₁ = y₂ := by
  rw [logDefSet] at h₁ h₂
  by_cases hpos : leE zeroE x ∧ ¬ leE x zeroE
  · rcases h₁ with ⟨_, h₁e⟩ | ⟨h₁n, _⟩
    · rcases h₂ with ⟨_, h₂e⟩ | ⟨h₂n, _⟩
      · exact expE_injective_of_model hM _ _ (by rw [h₁e, h₂e])
      · exact absurd hpos h₂n
    · exact absurd hpos h₁n
  · rcases h₁ with ⟨h₁p, _⟩ | ⟨_, h₁e⟩
    · exact absurd h₁p hpos
    · rcases h₂ with ⟨h₂p, _⟩ | ⟨_, h₂e⟩
      · exact absurd h₂p hpos
      · exact expE_injective_of_model hM _ _ (by rw [h₁e, h₂e])

/-- The chosen value of `logFun` in a model of `TE` really is a logarithm. -/
theorem logFun_spec_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M) :
    logDefSet x (logFun x) := by
  have h : ∃ y, logDefSet x y := logDefSet_exists_of_model hM x
  unfold logFun
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-! ## 4. The logarithm is preserved by `LEc`-embeddings -/

theorem LogFunMap {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE)
    (hN : FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE)
    (f : FirstOrder.Language.Embedding WilkiesDesign.CG.LEc M N) (x : M) :
    f (Work.WilC5.logFun x) = Work.WilC5.logFun (f x) := by
  have hMspec : logDefSet x (logFun x) := logFun_spec_of_model hM x
  have hkey : logDefSet (f x) (f (logFun x)) :=
    (logDefSet_map_iff hM hN f x (logFun x)).mpr hMspec
  have hNspec : logDefSet (f x) (logFun (f x)) := logFun_spec_of_model hN (f x)
  exact (logDefSet_unique_of_model hN hNspec hkey).symm

end Work.WilC5
