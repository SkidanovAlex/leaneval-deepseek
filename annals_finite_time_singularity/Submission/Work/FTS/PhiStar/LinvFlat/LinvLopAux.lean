import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.LinvFlat.Lop_iter_sin_cos_bound
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.PhiStar.LinvFlat

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The coefficient function `L₂` -/

/-- `L₂ θ = 5 cos 2θ − 1 = 2(2cos²θ − 3sin²θ)`. -/
def LI_L2fun (θ : ℝ) : ℝ := 5 * Real.cos (2 * θ) - 1

lemma LI_L2fun_eq (θ : ℝ) : LI_L2fun θ = 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2) := by
  rw [show LI_L2fun θ = 5 * Real.cos (2 * θ) - 1 from rfl, Real.cos_two_mul, Real.sin_sq]
  ring

lemma contDiffOn_LI_L2fun (k : ℕ) {U : Set ℝ} :
    ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) LI_L2fun U := by
  show ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (fun θ : ℝ => 5 * Real.cos (2 * θ) - 1) U
  fun_prop

/-- The `Lop`-iterates of `L₂` are uniformly bounded up to order `7`. -/
lemma LI_L2fun_lop_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℕ, a ≤ 7 → ∀ θ : ℝ,
      |(Work.Spaces.Lop^[a]) LI_L2fun θ| ≤ M := by
  have hbase : LopTrig.TP (fun θ : ℝ => 5 * Real.cos (2 * θ) + (-1) *
      (Real.sin (2 * θ) * Real.sin (2 * θ) + Real.cos (2 * θ) * Real.cos (2 * θ))) :=
    LopTrig.TP.add (LopTrig.TP.smul 5 LopTrig.TP.cos2)
      (LopTrig.TP.smul (-1) (LopTrig.TP.add (LopTrig.TP.mul LopTrig.TP.sin2 LopTrig.TP.sin2)
        (LopTrig.TP.mul LopTrig.TP.cos2 LopTrig.TP.cos2)))
  have hTP : LopTrig.TP LI_L2fun := by
    have heq : (fun θ : ℝ => 5 * Real.cos (2 * θ) + (-1) *
        (Real.sin (2 * θ) * Real.sin (2 * θ)
          + Real.cos (2 * θ) * Real.cos (2 * θ))) = LI_L2fun := by
      funext θ
      rw [show LI_L2fun θ = 5 * Real.cos (2 * θ) - 1 from rfl]
      have hs : Real.sin (2 * θ) * Real.sin (2 * θ)
          + Real.cos (2 * θ) * Real.cos (2 * θ) = 1 := by
        have h1 := Real.sin_sq_add_cos_sq (2 * θ)
        rw [pow_two, pow_two] at h1
        exact h1
      rw [hs]
      ring
    rw [heq] at hbase
    exact hbase
  have hTPa : ∀ a : ℕ, LopTrig.TP ((Work.Spaces.Lop^[a]) LI_L2fun) := by
    intro a
    induction a with
    | zero => simpa [Function.iterate_zero_apply] using hTP
    | succ a ih => rw [Function.iterate_succ_apply']; exact LopTrig.TP_lop ih
  choose B hB using fun a => LopTrig.TP_bdd (hTPa a)
  refine ⟨∑ a ∈ Finset.range 8, B a, Finset.sum_nonneg (fun a _ => (hB a).1), ?_⟩
  intro a ha θ
  have hmem : a ∈ Finset.range 8 := Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
  exact le_trans ((hB a).2 θ) (Finset.single_le_sum (fun i _ => (hB i).1) hmem)

/-! ## Smoothness bookkeeping for `Lop` -/

/-- `Lop` costs one order of smoothness on an open set. -/
lemma LI_contDiffOn_Lop {m : ℕ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) f U) :
    ContDiffOn ℝ (m : ℕ∞ω) (Work.Spaces.Lop f) U := by
  have hd : ContDiffOn ℝ (m : ℕ∞ω) (deriv f) U := hf.deriv_of_isOpen hU (le_refl _)
  have hs : ContDiffOn ℝ (m : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
  have h := hs.mul hd
  change ContDiffOn ℝ (m : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ) * deriv f θ) U
  exact h

/-- `Lop^[a]` costs `a` orders of smoothness. -/
lemma LI_LI_contDiffOn_Lop_iter {N : ℕ} {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (N : ℕ∞ω) u U) :
    ∀ a ≤ N, ContDiffOn ℝ ((N - a : ℕ) : ℕ∞ω) (Work.Spaces.Lop^[a] u) U := by
  intro a
  induction a with
  | zero => intro _; simpa [Function.iterate_zero_apply, Nat.sub_zero] using hu
  | succ a ih =>
      intro ha
      have ha' : a ≤ N := Nat.le_of_succ_le ha
      have hih : ContDiffOn ℝ ((N - a : ℕ) : ℕ∞ω) (Work.Spaces.Lop^[a] u) U := ih ha'
      have hsub : N - (a + 1) + 1 = N - a := by omega
      have hstep := LI_contDiffOn_Lop (m := N - (a + 1)) hU
        (f := Work.Spaces.Lop^[a] u) (by rw [hsub]; exact hih)
      rw [Function.iterate_succ_apply']
      exact hstep

lemma LI_diffAt_of_contDiffOn_one {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : ContDiffOn ℝ (1 : ℕ∞ω) f U) {θ : ℝ} (hθ : θ ∈ U) :
    DifferentiableAt ℝ f θ :=
  (h.differentiableOn_one).differentiableAt (hU.mem_nhds hθ)

/-- Any iterate `Lop^[a] u` with `a < N` is differentiable at interior points of the open set
where `u` is `C^N`. -/
lemma LI_diffAt_lop_iter {N : ℕ} {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (N : ℕ∞ω) u U) (a : ℕ) (ha : a < N) {θ : ℝ} (hθ : θ ∈ U) :
    DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := by
  have h := LI_LI_contDiffOn_Lop_iter hU hu a (le_of_lt ha)
  have h1 : ContDiffOn ℝ (1 : ℕ∞ω) (Work.Spaces.Lop^[a] u) U :=
    h.of_le (by exact_mod_cast (by omega : 1 ≤ N - a))
  exact LI_diffAt_of_contDiffOn_one hU h1 hθ

/-! ## Congruence and linearity of the iterates -/

lemma LI_Lop_congr_eqOn {A B : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : Set.EqOn A B U) : Set.EqOn (Work.Spaces.Lop A) (Work.Spaces.Lop B) U := by
  intro θ hθ
  show Real.sin (2 * θ) * deriv A θ = Real.sin (2 * θ) * deriv B θ
  rw [Set.EqOn.deriv h hU hθ]

lemma LI_Lop_iter_congr_eqOn {U : Set ℝ} (hU : IsOpen U) :
    ∀ (k : ℕ) {A B : ℝ → ℝ}, Set.EqOn A B U →
      Set.EqOn (Work.Spaces.Lop^[k] A) (Work.Spaces.Lop^[k] B) U := by
  intro k
  induction k with
  | zero => intro A B h; simpa [Function.iterate_zero_apply] using h
  | succ k ih =>
      intro A B h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact LI_Lop_congr_eqOn hU (ih h)

lemma LI_Lop_iter_neg_eqOn {U : Set ℝ} (hU : IsOpen U) :
    ∀ (k : ℕ) {A : ℝ → ℝ}, ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) A U →
      Set.EqOn (Work.Spaces.Lop^[k] (fun θ => -A θ))
        (fun θ => -(Work.Spaces.Lop^[k] A θ)) U := by
  intro k
  induction k with
  | zero =>
      intro A hA θ hθ
      show -A θ = -(A θ)
      rfl
  | succ k ih =>
      intro A hA
      show Set.EqOn (Work.Spaces.Lop^[k] (Work.Spaces.Lop (fun θ => -A θ)))
        (fun θ => -(Work.Spaces.Lop^[k] (Work.Spaces.Lop A) θ)) U
      have hbase : Set.EqOn (Work.Spaces.Lop (fun θ => -A θ))
          (fun θ => -(Work.Spaces.Lop A θ)) U := by
        intro θ hθ
        show Real.sin (2 * θ) * deriv (fun θ' : ℝ => -A θ') θ
          = -(Real.sin (2 * θ) * deriv A θ)
        have hd : DifferentiableAt ℝ A θ :=
          (((hA.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1)))).differentiableOn_one).differentiableAt
            (hU.mem_nhds hθ)
        have hdn : HasDerivAt (fun θ' : ℝ => -A θ') (-(deriv A θ)) θ :=
          hd.hasDerivAt.neg
        rw [hdn.deriv]
        ring
      have hLopA : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.Spaces.Lop A) U :=
        LI_contDiffOn_Lop (m := k) hU hA
      exact (LI_Lop_iter_congr_eqOn hU k hbase).trans (ih hLopA)

lemma LI_Lop_iter_add_eqOn {U : Set ℝ} (hU : IsOpen U) :
    ∀ (k : ℕ) {A B : ℝ → ℝ}, ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) A U →
      ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) B U →
      Set.EqOn (Work.Spaces.Lop^[k] (A + B))
        (fun θ => Work.Spaces.Lop^[k] A θ + Work.Spaces.Lop^[k] B θ) U := by
  intro k
  induction k with
  | zero =>
      intro A B hA hB θ hθ
      rfl
  | succ k ih =>
      intro A B hA hB
      show Set.EqOn (Work.Spaces.Lop^[k] (Work.Spaces.Lop (A + B)))
        (fun θ => Work.Spaces.Lop^[k] (Work.Spaces.Lop A) θ
          + Work.Spaces.Lop^[k] (Work.Spaces.Lop B) θ) U
      have hbase : Set.EqOn (Work.Spaces.Lop (A + B))
          (fun θ => Work.Spaces.Lop A θ + Work.Spaces.Lop B θ) U := by
        intro θ hθ
        show Real.sin (2 * θ) * deriv (A + B) θ
          = Real.sin (2 * θ) * deriv A θ + Real.sin (2 * θ) * deriv B θ
        have hdA : DifferentiableAt ℝ A θ :=
          (((hA.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1)))).differentiableOn_one).differentiableAt
            (hU.mem_nhds hθ)
        have hdB : DifferentiableAt ℝ B θ :=
          (((hB.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1)))).differentiableOn_one).differentiableAt
            (hU.mem_nhds hθ)
        have h := hdA.hasDerivAt.add hdB.hasDerivAt
        rw [h.deriv]
        ring
      have hLopA : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.Spaces.Lop A) U :=
        LI_contDiffOn_Lop (m := k) hU hA
      have hLopB : ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (Work.Spaces.Lop B) U :=
        LI_contDiffOn_Lop (m := k) hU hB
      exact (LI_Lop_iter_congr_eqOn hU k hbase).trans (ih hLopA hLopB)

/-! ## The iterated Leibniz rule at fixed order `9` -/

lemma LI_Lop_iter_mul_eqOn_9 {u v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 9 u U) (hv : ContDiffOn ℝ 9 v U) :
    ∀ j : ℕ, j ≤ 8 → Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ : ℝ => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
        (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  intro j
  induction j with
  | zero =>
      intro _ θ _
      simp [Function.iterate_zero_apply, Finset.sum_range_one]
  | succ j ih =>
      intro hj θ hθ
      show Work.Spaces.Lop^[j + 1] (u * v) θ
        = ∑ a ∈ Finset.range (j + 1 + 1), ((j + 1).choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j + 1 - a] v θ)
      have hj' : j ≤ 8 := by omega
      rw [Function.iterate_succ_apply']
      have hih := ih hj'
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' : ℝ => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
              (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        hih.deriv hU hθ
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' : ℝ => (j.choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact (((LI_diffAt_lop_iter (N := 9) hU hu a (by omega) hθ).mul
          (LI_diffAt_lop_iter (N := 9) hU hv (j - a) (by omega) hθ)).const_mul _)
      have hfun : (fun θ' : ℝ => ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1), (fun θ' : ℝ => (j.choose a : ℝ) *
            (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ) * deriv
              (fun θ' : ℝ => (j.choose a : ℝ) *
                (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ = _
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      have hstep : (∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ) * deriv
              (fun θ' : ℝ => (j.choose a : ℝ) *
                (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ)
          = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
              (Work.Spaces.Lop^[a + 1] u θ * Work.Spaces.Lop^[j - a] v θ
                + Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a + 1] v θ) := by
        apply Finset.sum_congr rfl
        intro a ha
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact Work.Spaces.sin_deriv_term u v θ j a
          (LI_diffAt_lop_iter (N := 9) hU hu a (by omega) hθ)
          (LI_diffAt_lop_iter (N := 9) hU hv (j - a) (by omega) hθ)
      rw [hstep]
      exact Work.Spaces.leibniz_step j (fun i => Work.Spaces.Lop^[i] u θ)
        (fun i => Work.Spaces.Lop^[i] v θ)


end Work.FTS.PhiStar.LinvFlat
