import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVariationDefs

/-!
# A.e. measurability of the `ρ`-variation of a continuous family

For a family `h : ℕ → ℝ → ℂ` of continuous functions, the assignment

`x ↦ V^ρ_{[lo,hi]}(h_n(x) : n ∈ ℕ)`

(`Work.BourgainPlan.Maximal.varRho`) is a.e. measurable with respect to Lebesgue measure.

The `ρ`-variation is by definition a supremum over *all* monotone chains `t : ℕ → ℕ` with values in
the window `[lo, hi]`, i.e. over an uncountable index set, so measurability is not immediate.  The
observation that makes it work is that the `ℓ^ρ`-length `chainLp ρ J a t` of a chain depends only on
the first `J+1` values of `t`; hence the supremum may be taken over nondecreasing tuples
`u : Fin (J+1) → ℕ` with values in the window, an index set which is countable (a finite power of
`ℕ`).  Each tuple contributes the measurable function
`x ↦ ofReal (chainLp ρ J (h_·(x)) û)` — a finite sum of compositions of the (measurable) maps
`y ↦ y ^ q` with `x ↦ ‖h_{t(j+1)}(x) − h_{t(j)}(x)‖` — and a countable supremum of measurable
functions is measurable.

The auxiliary fact `measurable_rpow_const_real` is the (only) place where real exponentiation
enters: `y ↦ y ^ q` is Borel measurable on `ℝ` for *every* real `q` (for `q ≥ 0` it is even
continuous, cf. `Real.continuous_rpow_const`); the definition `Real.rpow x y =
((x : ℂ) ^ (y : ℂ)).re` gives an explicit case distinction for the remaining cases.
-/

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **`y ↦ y ^ q` is Borel measurable on `ℝ`** for every real exponent `q`. -/
lemma measurable_rpow_const_real (q : ℝ) : Measurable fun y : ℝ => y ^ q := by
  have hpos : Measurable fun y : ℝ => Real.exp (Real.log y * q) :=
    Real.measurable_exp.comp (Real.measurable_log.mul_const q)
  have hneg : Measurable fun y : ℝ => Real.exp (Real.log y * q) * Real.cos (q * Real.pi) :=
    hpos.mul (Real.measurable_cos.comp measurable_const)
  have hmain : Measurable fun y : ℝ =>
      if 0 < y then Real.exp (Real.log y * q)
      else if y = 0 then (if q = 0 then (1 : ℝ) else 0)
      else Real.exp (Real.log y * q) * Real.cos (q * Real.pi) := by
    refine Measurable.ite measurableSet_Ioi hpos ?_
    refine Measurable.ite (measurableSet_singleton 0) measurable_const hneg
  have key : (fun y : ℝ => y ^ q) = fun y : ℝ =>
      if 0 < y then Real.exp (Real.log y * q)
      else if y = 0 then (if q = 0 then (1 : ℝ) else 0)
      else Real.exp (Real.log y * q) * Real.cos (q * Real.pi) := by
    funext y
    rcases lt_trichotomy y 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le), if_neg (ne_of_lt h), Real.rpow_def_of_nonpos h.le,
        if_neg (ne_of_lt h)]
    · subst h
      rw [if_neg (lt_irrefl 0), if_pos rfl, Real.rpow_def_of_nonpos le_rfl, if_pos rfl]
    · rw [if_pos h, Real.rpow_def_of_pos h]
  rw [key]
  exact hmain

/-- **The chain length of a continuous family is measurable.** -/
lemma measurable_chainLp_family {h : ℕ → ℝ → ℂ} (hcont : ∀ n, Continuous (h n))
    (ρ : ℝ) (J : ℕ) (t : ℕ → ℕ) :
    Measurable fun x : ℝ =>
      Work.BourgainPlan.Maximal.chainLp ρ J (fun n => h n x) t := by
  unfold Work.BourgainPlan.Maximal.chainLp
  refine (measurable_rpow_const_real (1 / ρ)).comp ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  refine (measurable_rpow_const_real ρ).comp ?_
  exact (((hcont (t (j + 1))).sub (hcont (t j))).norm).measurable

/-- **The `ρ`-variation is a countable supremum.**  Since `chainLp ρ J a t` depends only on the
first `J + 1` values of the chain `t`, the defining supremum over all monotone chains may be
replaced by the supremum over the (countably many) nondecreasing tuples `u : Fin (J+1) → ℕ` with
values in the window `[lo, hi]`, each extended to a chain by `j ↦ u (min j J)`. -/
lemma varRho_eq_iSup_fin (ρ : ℝ) (lo hi : ℕ) (a : ℕ → E) :
    Work.BourgainPlan.Maximal.varRho ρ lo hi a =
      ⨆ (J : ℕ) (u : {u : Fin (J + 1) → ℕ // (∀ j, lo ≤ u j ∧ u j ≤ hi) ∧ Monotone u}),
        ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp ρ J a
          (fun j => u.1 ⟨min j J, Nat.lt_succ_of_le (Nat.min_le_right j J)⟩)) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hw => ?_
    have hcl : Work.BourgainPlan.Maximal.chainLp ρ J a
        (fun j => (fun i : Fin (J + 1) => t i.1)
          ⟨min j J, Nat.lt_succ_of_le (Nat.min_le_right j J)⟩)
        = Work.BourgainPlan.Maximal.chainLp ρ J a t := by
      unfold Work.BourgainPlan.Maximal.chainLp
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have e1 : min (j + 1) J = j + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hj')
      have e2 : min j J = j := Nat.min_eq_left hj'.le
      simp only [e1, e2]
    rw [← hcl]
    refine le_iSup_of_le J ?_
    refine le_iSup_of_le
      (⟨fun i : Fin (J + 1) => t i.1, fun i => hw i.1 (Nat.lt_succ_iff.mp i.2), fun i j hij => ht hij⟩ :
        {u : Fin (J + 1) → ℕ // (∀ j, lo ≤ u j ∧ u j ≤ hi) ∧ Monotone u}) ?_
    exact le_rfl
  · refine iSup_le fun J => iSup_le fun u => ?_
    refine le_iSup_of_le J ?_
    refine le_iSup_of_le
      (fun j => u.1 ⟨min j J, Nat.lt_succ_of_le (Nat.min_le_right j J)⟩) ?_
    refine le_iSup_of_le (fun i j hij => u.2.2 (min_le_min hij le_rfl)) ?_
    refine le_iSup_of_le (fun j hj => ?_) le_rfl
    have e : min j J = j := Nat.min_eq_left hj
    have h := u.2.1 ⟨j, Nat.lt_succ_of_le hj⟩
    simpa only [e] using h

/-- **A.e. measurability of `x ↦ V^ρ_{[lo,hi]}(h_n(x))`** for a continuous family
`h : ℕ → ℝ → ℂ`. -/
theorem aemeasurable_varRho_family (ρ : ℝ) (lo hi : ℕ) {h : ℕ → ℝ → ℂ}
    (hcont : ∀ n, Continuous (h n)) :
    AEMeasurable (fun x : ℝ => Work.BourgainPlan.Maximal.varRho ρ lo hi (fun n => h n x))
      MeasureTheory.volume := by
  have hfun : (fun x : ℝ => Work.BourgainPlan.Maximal.varRho ρ lo hi (fun n => h n x)) =
      fun x : ℝ => ⨆ (J : ℕ)
        (u : {u : Fin (J + 1) → ℕ // (∀ j, lo ≤ u j ∧ u j ≤ hi) ∧ Monotone u}),
          ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp ρ J (fun n => h n x)
            (fun j => u.1 ⟨min j J, Nat.lt_succ_of_le (Nat.min_le_right j J)⟩)) := by
    funext x
    exact varRho_eq_iSup_fin ρ lo hi (fun n => h n x)
  rw [hfun]
  refine Measurable.aemeasurable ?_
  refine Measurable.iSup fun J => Measurable.iSup fun u => ?_
  exact ENNReal.measurable_ofReal.comp (measurable_chainLp_family hcont ρ J _)

end

end Work.BourgainPlan.IonescuWainger
