/-
  WilC5 — every `LEc`-embedding between models of `TE` is an `LElog`-embedding.

  The expanded language `LElog = LEc ⊕ {log, ≤}` (`ExpLog.lean`) has, on every `LEc`-structure,
  the canonical structure `logStruct` in which `log` is the *definable* logarithm

      `logDefSet x y  :=  (0 < x ∧ exp y = x) ∨ (¬ 0 < x ∧ exp y = 1)`

  (the vdDMM convention: `log x` for `x > 0`, and `0` otherwise) and `≤` is the definable order
  `leE x y := ∃ z, z * z = y - x` of `Bridge.lean`.

  The content of this module is that these two extra symbols are *absolute* for embeddings of
  models of `TE`: given `f : M ↪[LEc] N` with `M, N ⊨ TE`, the same underlying function `f` is an
  `LElog`-embedding.  For `≤` this is `leE_map` / `leE_reflect` (`ReductEmb.lean`, using the
  linearity of the definable order, transferred from `ℝ`).  For `log` one has to show

      `f (logFun x) = logFun (f x)`,

  which needs two facts about the exponential of a model of `TE` — that `exp` is injective and
  that it is surjective onto the positive elements — so that `logDefSet x ·` has a *unique*
  solution and `logFun` is the function it defines.  Both facts are transferred from `ℝ`, where
  they are `Real.exp_injective` and `Real.exp_log`; the transfer machinery is `Work.WilC5.transfer`
  of `ReductEmb.lean` (universally quantified `LEc`-formulas holding in `ℝ` hold in every model of
  `TE`).

  This is the "`f` is an `LElog`-embedding" step of the synthesis in `Synthesis.lean`, where it
  combines with quantifier elimination in `LElog` (`DMM45_QE`) to give model completeness of `TE`.
-/
import Mathlib
import Submission.Work.WilC5.ExpLog

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder
open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language

/-! ## 1. The three `LEc`-sentences transferred from `ℝ`

`exp` injective, `exp` surjective onto the positive elements, and `exp 0 = 1`.  Each is written as
a bounded `LEc`-formula (over `β = Empty`) and then transferred from `ℝ` to an arbitrary model of
`TE` with `Work.WilC5.transfer`. -/

/-- `0 < t`, i.e. `t` is positive for the definable order: `0 ≤ t` and not `t ≤ 0`. -/
private def posF {n : ℕ} (t : LEc.Term (Empty ⊕ Fin n)) : LEc.BoundedFormula Empty n :=
  leForm (eZero : LEc.Term (Empty ⊕ Fin n)) t ⊓
    (leForm t (eZero : LEc.Term (Empty ⊕ Fin n))).not

/-- The formula `exp x = exp y → x = y`: injectivity of the exponential. -/
private def expInjForm : LEc.BoundedFormula Empty 2 :=
  (Term.bdEqual (eExp (v2 0)) (eExp (v2 1))).imp (Term.bdEqual (v2 0) (v2 1))

/-- The formula `0 < x → ∃ y, exp y = x`: surjectivity of the exponential onto the positive
elements. -/
private def expSurjForm : LEc.BoundedFormula Empty 1 :=
  (posF (v1 0)).imp ((Term.bdEqual (eExp (v2 1)) (v2 0)).ex)

/-- The sentence `exp 0 = 1`. -/
private def expZeroForm : LEc.BoundedFormula Empty 0 :=
  Term.bdEqual (eExp (eZero : LEc.Term (Empty ⊕ Fin 0))) (eOne : LEc.Term (Empty ⊕ Fin 0))

/-! ## 2. Realization of the formulas -/

private theorem expInjForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    expInjForm.Realize (emptyVar (M := M)) xs ↔ (expE (xs 0) = expE (xs 1) → xs 0 = xs 1) := by
  rw [expInjForm, BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_bdEqual]
  simp only [v2, Term.realize_var, Sum.elim_inr, realize_eExp]

private theorem expSurjForm_realize {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    expSurjForm.Realize (emptyVar (M := M)) xs ↔
      (leE (zeroE : M) (xs 0) ∧ ¬ leE (xs 0) (zeroE : M) → ∃ y : M, expE y = xs 0) := by
  rw [expSurjForm, BoundedFormula.realize_imp, posF, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, leForm_realize, leForm_realize, BoundedFormula.realize_ex]
  simp only [BoundedFormula.realize_bdEqual, realize_eExp, Term.realize_var, Sum.elim_inr,
    realize_eZero, v1, v2]
  constructor
  · rintro h ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := h ⟨by simpa [leE] using h1, by simpa [leE] using h2⟩
    refine ⟨a, ?_⟩
    have h1' : (Fin.snoc xs a : Fin 2 → M) 1 = a := by
      simpa using Fin.snoc_last (α := fun _ : Fin 2 => M) (p := xs) (x := a)
    have h0' : (Fin.snoc xs a : Fin 2 → M) 0 = xs 0 := by simp
    rw [h1', h0'] at ha
    exact ha
  · rintro h ⟨h1, h2⟩
    obtain ⟨y, hy⟩ := h ⟨by simpa [leE] using h1, by simpa [leE] using h2⟩
    refine ⟨y, ?_⟩
    have h1' : (Fin.snoc xs y : Fin 2 → M) 1 = y := by
      simpa using Fin.snoc_last (α := fun _ : Fin 2 => M) (p := xs) (x := y)
    have h0' : (Fin.snoc xs y : Fin 2 → M) 0 = xs 0 := by simp
    rw [h1', h0']
    exact hy

private theorem expZeroForm_realize {M : Type} [LEc.Structure M] :
    expZeroForm.Realize (emptyVar (M := M)) (emptyBnd (M := M)) ↔ expE (zeroE : M) = oneE := by
  rw [expZeroForm, BoundedFormula.realize_bdEqual]
  simp only [realize_eExp, realize_eZero, realize_eOne]

/-! ## 3. The formulas hold in `ℝ` -/

private theorem expInj_real : ∀ xs : Fin 2 → ℝ, expInjForm.Realize (emptyVar (M := ℝ)) xs := by
  intro xs
  rw [expInjForm_realize]
  intro h
  rw [expE_real, expE_real] at h
  exact Real.exp_injective h

private theorem expSurj_real : ∀ xs : Fin 1 → ℝ, expSurjForm.Realize (emptyVar (M := ℝ)) xs := by
  intro xs
  rw [expSurjForm_realize]
  intro h
  have h1 : 0 ≤ xs 0 := by
    have h1' := h.1
    rw [leE, subE_real, zeroE_real, sub_zero, isSquare_real] at h1'
    exact h1'
  have h2 : ¬ (xs 0 ≤ 0) := by
    intro hc
    refine h.2 ?_
    rw [leE, subE_real, zeroE_real, isSquare_real]
    linarith
  exact ⟨Real.log (xs 0), by rw [expE_real, Real.exp_log (by linarith)]⟩

private theorem expZero_real : expZeroForm.Realize (emptyVar (M := ℝ)) (emptyBnd (M := ℝ)) := by
  rw [expZeroForm_realize]
  rw [expE_real, zeroE_real, oneE_real, Real.exp_zero]

/-! ## 4. The same facts in an arbitrary model of `TE`, by transfer -/

private theorem expE_inj_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (a b : M)
    (h : expE a = expE b) : a = b := by
  have h' := transfer hM expInjForm expInj_real ![a, b]
  rw [expInjForm_realize] at h'
  simpa using h' h

private theorem expE_surj_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M)
    (hx : leE (zeroE : M) x ∧ ¬ leE x (zeroE : M)) : ∃ y : M, expE y = x := by
  have h' := transfer hM expSurjForm expSurj_real ![x]
  rw [expSurjForm_realize] at h'
  simpa using h' (by simpa using hx)

private theorem expE_zero_of_model {M : Type} [LEc.Structure M] (hM : M ⊨ TE) :
    expE (zeroE : M) = oneE := by
  have h' := transfer hM expZeroForm (fun _ => expZero_real) (emptyBnd (M := M))
  rw [expZeroForm_realize] at h'
  exact h'

/-! ## 5. `logDefSet` is the graph of a total function -/

private theorem logDefSet_exists {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M) :
    ∃ y : M, logDefSet x y := by
  by_cases h : leE (zeroE : M) x ∧ ¬ leE x (zeroE : M)
  · obtain ⟨y, hy⟩ := expE_surj_of_model hM x h
    exact ⟨y, Or.inl ⟨h, hy⟩⟩
  · exact ⟨zeroE, Or.inr ⟨h, expE_zero_of_model hM⟩⟩

private theorem logDefSet_unique {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {x y₁ y₂ : M}
    (h₁ : logDefSet x y₁) (h₂ : logDefSet x y₂) : y₁ = y₂ := by
  rcases h₁ with ⟨h1, h1e⟩ | ⟨h1, h1e⟩ <;> rcases h₂ with ⟨h2, h2e⟩ | ⟨h2, h2e⟩
  · exact expE_inj_of_model hM _ _ (by rw [h1e, h2e])
  · exact absurd h1 h2
  · exact absurd h2 h1
  · exact expE_inj_of_model hM _ _ (by rw [h1e, h2e])

private theorem logFun_spec {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x : M) :
    logDefSet x (logFun x) := by
  have hex := logDefSet_exists hM x
  rw [logFun, dite_eq_left hex]
  exact Classical.choose_spec hex

private theorem logFun_eq_of_logDefSet {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {x y : M}
    (h : logDefSet x y) : logFun x = y :=
  logDefSet_unique hM (logFun_spec hM x) h

/-! ## 6. The definable logarithm is absolute for `LEc`-embeddings of models of `TE` -/

private theorem logDefSet_map {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (hM : M ⊨ TE) (hN : N ⊨ TE) (f : M ↪[LEc] N) {x y : M} (h : logDefSet x y) :
    logDefSet (f x) (f y) := by
  have htot := le_total_of_model hM
  have hanti := le_antisymm_of_model hN
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h3⟩
  · refine Or.inl ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [map_zeroE f] using leE_map f h1
    · intro hc
      exact h2 (leE_reflect f htot hanti (by simpa [map_zeroE f] using hc))
    · rw [← map_expE f y, h3]
  · refine Or.inr ⟨?_, ?_⟩
    · intro hc
      obtain ⟨hc1, hc2⟩ := hc
      refine h1 ⟨leE_reflect f htot hanti (by simpa [map_zeroE f] using hc1), ?_⟩
      intro hx0
      exact hc2 (by simpa [map_zeroE f] using leE_map f hx0)
    · rw [← map_expE f y, h3, map_oneE f]

private theorem logFun_map {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (hM : M ⊨ TE) (hN : N ⊨ TE) (f : M ↪[LEc] N) (x : M) :
    f (logFun x) = logFun (f x) := by
  have hx := logFun_spec hM x
  have hfx := logDefSet_map hM hN f hx
  exact (logFun_eq_of_logDefSet hN hfx).symm

/-! ## 7. The main theorem -/

theorem LogStructEmbedding {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE)
    (hN : FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE)
    (f : FirstOrder.Language.Embedding WilkiesDesign.CG.LEc M N) :
    ∃ g : FirstOrder.Language.Embedding Work.WilC5.LElog M N, ∀ x : M, g x = f x := by
  refine ⟨{ toEmbedding := (f.toEmbedding : M ↪ N), map_fun' := ?_, map_rel' := ?_ },
    fun x => rfl⟩
  · intro n g x
    rcases g with g | r
    · rw [logStruct_funMap_inl, logStruct_funMap_inl]
      exact f.map_fun g x
    · rcases r with ⟨⟩
      show f (logFun (x 0)) = logFun ((f ∘ x) 0)
      exact logFun_map hM hN f (x 0)
  · intro n r x
    rcases r with r | r
    · exact nomatch r
    · rcases r with ⟨⟩
      show leE ((f ∘ x) 0) ((f ∘ x) 1) ↔ leE (x 0) (x 1)
      exact ⟨fun h => leE_reflect f (le_total_of_model hM) (le_antisymm_of_model hN) h,
        fun h => leE_map f h⟩

end Work.WilC5
