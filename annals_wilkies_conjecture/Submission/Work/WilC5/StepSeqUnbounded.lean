/-
  WilC5 — **each remainder of the vdDMM §4 sequence is unbounded.**

  This is Claim 1 of the iteration underlying van den Dries–Macintyre–Marker's Lemma 4.4
  (notation as fixed in `Submission/Work/WilC5/StepSeq.lean`).

  Situation.  `K ⊨ TE`, `B ≤ K` is an `LRc`-substructure of the `rexp`-reduct which is closed
  under the exponential, `x > 0` is *value-new* over `B` (`¬ SameArch b x` for every `b ∈ B`),
  `β ∈ B`, `x' > 0` and `log x = β + x'` (with `β + x'` the `LEc`-addition, which agrees with the
  field addition by `hadd`; likewise `hmul`, `hone`, `hleneg`).

  Claim.  `x'` is not finite, `¬ IsFiniteVal x'`.

  Proof.  Since `0 < x`, the definable logarithm inverts the exponential
  (`expE_logFun_of_pos`) and, by additivity of `expE` in a model of `TE` (`expE_add_of_model`),

      `x = expE (log x) = expE (β + x') = expE β · expE x'`,

  with `expE β ∈ B` by closure under `expE`.  If `x'` were finite, say `|x'| ≤ (N : K) + 1`, then
  `0 < x' ≤ (N : K) + 1 = ((N+1) : K)`, and monotonicity of `expE` (`expE_le_of_le`) together with
  the elementarity of the model — the exponential of a standard natural is bounded by a standard
  natural, `expNat_le` — bounds `1 ≤ expE x' ≤ (M : K)`.  So `expE x'` is a *unit* of the standard
  real valuation, whence also

      `x / expE β = expE x'`

  is a unit, giving `SameArch x (expE β)` (`SameArch_iff_IsUnitVal_div`) — contradicting the
  value-newness of `x` at the element `expE β ∈ B`.

  The model-theoretic inputs are the transfers `expE_le_of_le` (monotonicity), `expE_oneE_le`
  (`exp 1 < 3`) and the induction `expNat_le`, together with the `LEc`/field bridges
  `zeroE_eq_zero` and `leE_zero_iff` from `S4ExpF/Bridge.lean`.
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.ValArith
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.S4ExpF.Bridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. Monotonicity of the exponential in a model of `TE` -/

/-- The `LEc`-sentence `∀ x y, x ≤ y → exp x ≤ exp y`. -/
def expMonoForm : LEc.BoundedFormula Empty 2 :=
  (Work.WilC5.leForm (Work.WilC5.v2 0) (Work.WilC5.v2 1)).imp
    (Work.WilC5.leForm (Work.WilC5.eExp (Work.WilC5.v2 0)) (Work.WilC5.eExp (Work.WilC5.v2 1)))

theorem expMonoForm_realize {M : Type} [LEc.Structure M] (xs : Fin 2 → M) :
    (expMonoForm).Realize (@Work.WilC5.emptyVar M) xs ↔
      (Work.WilC5.leE (xs 0) (xs 1) →
        Work.WilC5.leE (Work.WilC5.expE (xs 0)) (Work.WilC5.expE (xs 1))) := by
  rw [expMonoForm, BoundedFormula.realize_imp, Work.WilC5.leForm_realize, Work.WilC5.leForm_realize,
    Work.WilC5.realize_eExp, Work.WilC5.realize_eExp]
  simp only [Work.WilC5.v2, Term.realize_var, Sum.elim_inr]
  rfl

theorem expMonoForm_real :
    ∀ xs : Fin 2 → ℝ, (expMonoForm).Realize (@Work.WilC5.emptyVar ℝ) xs := by
  intro xs
  rw [expMonoForm_realize]
  intro h
  rw [Work.WilC5.leE_real] at h ⊢
  rw [Work.WilC5.expE_real, Work.WilC5.expE_real]
  exact Real.exp_le_exp.mpr h

/-- **`exp` is increasing in every model of `TE`.** -/
theorem expE_le_of_le {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {a b : M}
    (h : Work.WilC5.leE a b) :
    Work.WilC5.leE (Work.WilC5.expE a) (Work.WilC5.expE b) := by
  have h' := Work.WilC5.transfer hM expMonoForm expMonoForm_real ![a, b]
  rw [expMonoForm_realize] at h'
  exact h' h

/-! ## 2. `exp 1 ≤ 3`, and `exp` of a standard natural is standard -/

/-- The `LEc`-sentence `exp 1 ≤ 1 + (1 + 1)`. -/
def expOneBoundForm : LEc.BoundedFormula Empty 0 :=
  Work.WilC5.leForm (Work.WilC5.eExp Work.WilC5.eOne)
    (Work.WilC5.eAdd Work.WilC5.eOne (Work.WilC5.eAdd Work.WilC5.eOne Work.WilC5.eOne))

theorem expOneBoundForm_realize {M : Type} [LEc.Structure M] (xs : Fin 0 → M) :
    (expOneBoundForm).Realize (@Work.WilC5.emptyVar M) xs ↔
      Work.WilC5.leE (M := M) (Work.WilC5.expE (M := M) (Work.WilC5.oneE (M := M)))
        (Work.WilC5.addE (M := M) (Work.WilC5.oneE (M := M))
          (Work.WilC5.addE (M := M) (Work.WilC5.oneE (M := M)) (Work.WilC5.oneE (M := M)))) := by
  rw [expOneBoundForm, Work.WilC5.leForm_realize, Work.WilC5.realize_eExp, Work.WilC5.realize_eAdd,
    Work.WilC5.realize_eAdd, Work.WilC5.realize_eOne]
  rfl

theorem expOneBoundForm_real :
    ∀ xs : Fin 0 → ℝ, (expOneBoundForm).Realize (@Work.WilC5.emptyVar ℝ) xs := by
  intro xs
  rw [expOneBoundForm_realize, Work.WilC5.leE_real, Work.WilC5.expE_real, Work.WilC5.oneE_real,
    Work.WilC5.addE_real, Work.WilC5.addE_real]
  linarith [Real.exp_one_lt_three]

/-- **`exp 1 ≤ 1 + (1 + 1)` in every model of `TE`** (the transfer of `e < 3`). -/
theorem expE_oneE_le {M : Type} [LEc.Structure M] (hM : M ⊨ TE) :
    Work.WilC5.leE (M := M) (Work.WilC5.expE (M := M) (Work.WilC5.oneE (M := M)))
      (Work.WilC5.addE (M := M) (Work.WilC5.oneE (M := M))
        (Work.WilC5.addE (M := M) (Work.WilC5.oneE (M := M)) (Work.WilC5.oneE (M := M)))) :=
  (expOneBoundForm_realize (M := M) Fin.elim0).mp
    (Work.WilC5.transfer hM expOneBoundForm expOneBoundForm_real Fin.elim0)

/-- **The exponential of a standard natural is bounded by a standard natural.**  By induction:
`exp 0 = 1`, and `exp (n+1) = exp n · exp 1 ≤ exp n · 3`. -/
theorem expNat_le {K : Type} [LEc.Structure K] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] (hM : K ⊨ TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y) :
    ∀ n : ℕ, ∃ M : ℕ, Work.WilC5.expE ((n : K)) ≤ (M : K) := by
  intro n
  induction n with
  | zero =>
      refine ⟨1, ?_⟩
      rw [Nat.cast_zero, ← Work.WilC5.S4ExpF.zeroE_eq_zero hM hadd,
        Work.WilC5.expE_zero_of_model hM, hone]
      norm_num
  | succ n ih =>
      obtain ⟨A, hA⟩ := ih
      refine ⟨3 * A, ?_⟩
      have hsucc : ((n + 1 : ℕ) : K) = Work.WilC5.addE ((n : K)) (Work.WilC5.oneE : K) := by
        rw [Nat.cast_succ, ← hone]
        exact (hadd (n : K) (Work.WilC5.oneE : K)).symm
      rw [hsucc, Work.WilC5.expE_add_of_model hM, hmul]
      have h3 : Work.WilC5.expE (Work.WilC5.oneE : K) ≤ 3 := by
        have h := (hleneg (Work.WilC5.expE (Work.WilC5.oneE : K))
          (Work.WilC5.addE (Work.WilC5.oneE : K)
            (Work.WilC5.addE (Work.WilC5.oneE : K) (Work.WilC5.oneE : K)))).mp
          (expE_oneE_le (M := K) hM)
        rw [hadd, hadd, hone] at h
        norm_num at h
        rw [hone]
        exact h
      have hpos : 0 ≤ Work.WilC5.expE (Work.WilC5.oneE : K) := by
        have h := (Work.WilC5.expE_pos_of_model hM (Work.WilC5.oneE : K)).1
        rw [hleneg, Work.WilC5.S4ExpF.zeroE_eq_zero hM hadd] at h
        exact h
      have hcast : ((3 * A : ℕ) : K) = 3 * (A : K) := by push_cast; ring
      rw [hcast]
      calc Work.WilC5.expE ((n : K)) * Work.WilC5.expE (Work.WilC5.oneE : K)
          ≤ (A : K) * 3 := mul_le_mul hA h3 hpos (Nat.cast_nonneg A)
        _ = 3 * (A : K) := by ring

/-! ## 3. The unboundedness of the remainder -/

theorem StepSeqUnbounded
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
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBexp : ∀ b ∈ (B : Set K), Work.WilC5.expE b ∈ (B : Set K))
    {x x' : K} (hxpos : 0 < x)
    (hxnew : ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) x)
    {β : ↥B} (hβ : Work.WilC5.logFun x = Work.WilC5.addE (β : K) x')
    (hx'pos : 0 < x') :
    ¬ Work.WilC5.IsFiniteVal x' := by
  intro hx'fin
  -- `0 < x` is the `LEc`-strict-positivity of `x`
  have hxle : Work.WilC5.leE Work.WilC5.zeroE x ∧ ¬ Work.WilC5.leE x Work.WilC5.zeroE :=
    (Work.WilC5.S4ExpF.leE_zero_iff (K := K) (inferInstance) hadd hleneg x).mpr hxpos
  -- `x = exp (log x) = exp β · exp x'`
  have hx_eq : Work.WilC5.expE (Work.WilC5.logFun x) = x :=
    Work.WilC5.expE_logFun_of_pos (M := K) (inferInstance) hxle
  have hsplit : x = Work.WilC5.expE (β : K) * Work.WilC5.expE x' := by
    rw [← hx_eq, hβ, Work.WilC5.expE_add_of_model (M := K) (inferInstance), hmul]
  have hexpβ_mem : Work.WilC5.expE (β : K) ∈ (B : Set K) := hBexp (β : K) β.2
  have hexpβ_pos : 0 < Work.WilC5.expE (β : K) :=
    (Work.WilC5.S4ExpF.leE_zero_iff (K := K) (inferInstance) hadd hleneg
      (Work.WilC5.expE (β : K))).mp
      (Work.WilC5.expE_pos_of_model (M := K) (inferInstance) (β : K))
  have hexpβ_ne : Work.WilC5.expE (β : K) ≠ 0 := ne_of_gt hexpβ_pos
  -- `expE x'` is bounded by a standard natural
  obtain ⟨N, hN⟩ := hx'fin
  have hx'le : x' ≤ (N : K) + 1 := le_trans (le_abs_self x') hN
  have hx'leE : Work.WilC5.leE x' ((N : K) + 1) := (hleneg x' _).mpr hx'le
  have hexpmono : Work.WilC5.expE x' ≤ Work.WilC5.expE ((N : K) + 1) :=
    (hleneg _ _).mp (expE_le_of_le (M := K) (inferInstance) hx'leE)
  obtain ⟨M, hM⟩ := expNat_le (K := K) (inferInstance) hadd hmul hone hleneg (N + 1)
  have hN1 : (N : K) + 1 = ((N + 1 : ℕ) : K) := (Nat.cast_succ N).symm
  have hub : Work.WilC5.expE x' ≤ (M : K) := by
    calc Work.WilC5.expE x' ≤ Work.WilC5.expE ((N : K) + 1) := hexpmono
      _ = Work.WilC5.expE (((N + 1 : ℕ) : K)) := by rw [hN1]
      _ ≤ (M : K) := hM
  -- `1 ≤ expE x'`
  have hx'nn_leE : Work.WilC5.leE Work.WilC5.zeroE x' :=
    (Work.WilC5.S4ExpF.leE_zero_iff (K := K) (inferInstance) hadd hleneg x').mpr hx'pos |>.1
  have hmono0 : Work.WilC5.leE (Work.WilC5.expE Work.WilC5.zeroE) (Work.WilC5.expE x') :=
    expE_le_of_le (M := K) (inferInstance) hx'nn_leE
  have hge1 : (1 : K) ≤ Work.WilC5.expE x' := by
    have h1 : Work.WilC5.oneE ≤ Work.WilC5.expE x' := by
      rw [← Work.WilC5.expE_zero_of_model (M := K) (inferInstance)]
      exact (hleneg _ _).mp hmono0
    rwa [hone] at h1
  have hexp'pos : 0 < Work.WilC5.expE x' := lt_of_lt_of_le zero_lt_one hge1
  -- `expE x'` is a unit of the standard real valuation
  have hunit : WilkiesDesign.CG.IsUnitVal (Work.WilC5.expE x') := by
    refine ⟨M, ?_, ?_⟩
    · rw [abs_of_pos hexp'pos]
      calc ((M : K) + 1)⁻¹ ≤ (1 : K) :=
            inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg M))
        _ ≤ Work.WilC5.expE x' := hge1
    · rw [abs_of_pos hexp'pos]
      exact le_trans hub (le_add_of_nonneg_right zero_le_one)
  -- `x` and `expE β` have the same value
  have hdiv : x / Work.WilC5.expE (β : K) = Work.WilC5.expE x' := by
    rw [hsplit]
    exact mul_div_cancel_left₀ (Work.WilC5.expE x') hexpβ_ne
  have hSameArch : Work.WilC5.SameArch x (Work.WilC5.expE (β : K)) := by
    rw [Work.WilC5.SameArch_iff_IsUnitVal_div hexpβ_ne, hdiv]
    exact hunit
  -- contradicting the value-newness of `x` at `expE β ∈ B`
  exact hxnew ⟨Work.WilC5.expE (β : K), hexpβ_mem⟩ (Work.WilC5.SameArch_equiv.symm hSameArch)

end Work.WilC5
