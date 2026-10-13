/-
# `Transfer/HkIntegrand_Dz_le_succ_Q0Sm.lean` — the `D_z`-index shift at finite order

The transfer of the level-4 coercivity of the clean operator `𝓛̂` to the paper's operator
`𝓛_Γ^T = 𝓛̂ + Corr` runs through the weakened additivity package `Assembly.Comm2w`, whose
hypotheses are *finite order* smoothness of the blocks on the open quadrant `Qd` (the class
`Transfer.Q0Sm k X` of `Transfer/Q0Sm.lean`) rather than the analytic `SmoothQuad`/`SmoothNbhd`
classes used by `QuadPorts.HkIntegrand_Dz_le_succ` and `EllipticEst.UopHk.HkIntegrand_Dz_le_succ`.

This file supplies the corresponding pointwise domination of the `ℋ^k`-integrands, i.e. the
finite-order instance of

  `HkIntegrand α k (D_z f) ≤ HkIntegrand α (k+1) f`   on the open quadrant,

for `f ∈ C^{k+1}` on `Qd` (the honest hypothesis order: the index shift
`mixed b a (D_z f) = mixed (b+1) a f` costs `a + 1` derivatives, exactly the differentiability of
`f` that makes the statement meaningful).

Every summand of `HkIntegrand α k (D_z f)` is a summand of `HkIntegrand α (k+1) f` with the same
weight:

* the pure summands by the *definitional* index shift `D_z^i (D_z f) = D_z^{i+1} f`
  (`DzIter_Dz_eq`, from `DzIter_add_right`);
* the mixed summands by the index shift `mixed b a (D_z f) = mixed (b+1) a f`, which needs
  Clairaut's theorem for the two curvilinear operators.  On the open quadrant this is
  `D_θ^a (D_z f) = mixed 1 a f`, proved here by induction on `a`, each step exchanging *one*
  inner `D_θ` with `D_z` by `Work.Spaces.Dz_Dth_comm` (which asks only `C²` at that point) and
  comparing the two `D_θ`-iterates on the open set `Qd` (`Work.Spaces.pth_congr_of_isOpen`).

The combinatorial content of the mixed half is `Work.Coercivity.SumShiftZ_le`
(the shift `(i,j) ↦ (i,j+1)` of the slot square), already available.

Everything here is proved and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.Coercivity.SumShiftZ_le
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Congruence of `D_θ` and of the iterated `D_z` on the open quadrant

Both operators are local; on the open set `Qd` two functions that agree there have equal
`D_θ`- and equal `D_z^j`-profiles, by `Work.Spaces.pth_congr_of_isOpen` respectively
`Work.Spaces.pz_congr_of_isOpen`. -/

/-- `D_θ` is congruent on the open quadrant. -/
theorem Dth_congr_Qd {X Y : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Qd → X z θ = Y z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd → Work.Spaces.Dth X z θ = Work.Spaces.Dth Y z θ := by
  intro z θ hzθ
  have hEq : Set.EqOn (Function.uncurry X) (Function.uncurry Y) Qd :=
    fun p hp => h p.1 p.2 hp
  simp only [Work.Spaces.Dth]
  rw [Work.Spaces.pth_congr_of_isOpen isOpen_Qd hEq hzθ]

/-- The iterated `D_z` is congruent on the open quadrant. -/
theorem DzIter_congr_Qd {X Y : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Qd → X z θ = Y z θ) (j : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.DzIter j X z θ = Work.Spaces.DzIter j Y z θ := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro z θ hzθ
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DzIter j X))
          (Function.uncurry (Work.Spaces.DzIter j Y)) Qd :=
        fun p hp => ih p.1 p.2 hp
      show z * Work.Spaces.pz (Work.Spaces.DzIter j X) z θ
          = z * Work.Spaces.pz (Work.Spaces.DzIter j Y) z θ
      rw [Work.Spaces.pz_congr_of_isOpen isOpen_Qd hEq hzθ]

/-- `D_z^i (D_z X) = D_z^{i+1} X`, definitionally from `D_z^{i+b} = D_z^i ∘ D_z^b`. -/
theorem DzIter_Dz_eq (i : ℕ) (X : Fn) :
    Work.Spaces.DzIter i (Work.Spaces.Dz X) = Work.Spaces.DzIter (i + 1) X := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-! ## The finite-order index shift `D_θ^a (D_z u) = mixed 1 a u`

The honest hypothesis is `u ∈ C^{a+1}` on `Qd`: the identity is `∂_θ`-`∂_z` commutation of total
order `a + 1`.  It is proved by induction on `a`; the step applies Clairaut
(`Work.Spaces.Dz_Dth_comm`) to the `C²` profile `D_θ^a u` (which needs `u ∈ C^{a+2}`, one order
more, exactly as the induction hypothesis for level `a` supplies it). -/

theorem DthIter_Dz_eq_mixed_one {u : Fn} {N : ℕ} (h : Q0Sm N u) {a : ℕ} (ha : a + 1 ≤ N) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.DthIter a (Work.Spaces.Dz u) z θ = Work.Spaces.mixed 1 a u z θ := by
  induction a with
  | zero => intro z θ _; rfl
  | succ a ih =>
      intro z θ hzθ
      have ha' : a + 1 ≤ N := by omega
      -- `D_θ^a u` is `C²` on `Qd`, because `u` is `C^{a+2}` there.
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter a u)) (z, θ) :=
        (contDiffOn_DthIter_nat isOpen_Qd (G := u) a 2
          (h.mono (l := a + 2) (by omega))).contDiffAt (isOpen_Qd.mem_nhds hzθ)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter a u)) z θ
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter a u)) z θ :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter a u) hcd
      show Work.Spaces.Dth (Work.Spaces.DthIter a (Work.Spaces.Dz u)) z θ
          = Work.Spaces.mixed 1 (a + 1) u z θ
      rw [Dth_congr_Qd (X := Work.Spaces.DthIter a (Work.Spaces.Dz u))
            (Y := Work.Spaces.Dz (Work.Spaces.DthIter a u)) (ih ha') z θ hzθ, ← hcomm]
      rfl

/-- **The index shift on the open quadrant**: `D_z^b D_θ^a (D_z u) = D_z^{b+1} D_θ^a u`. -/
theorem mixed_Dz_shift_Q0Sm {u : Fn} {N : ℕ} (h : Q0Sm N u) {a : ℕ} (ha : a + 1 ≤ N) (b : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.mixed b a (Work.Spaces.Dz u) z θ
        = Work.Spaces.mixed (b + 1) a u z θ := by
  intro z θ hzθ
  have hX := DzIter_congr_Qd (X := Work.Spaces.DthIter a (Work.Spaces.Dz u))
    (Y := Work.Spaces.Dz (Work.Spaces.DthIter a u)) (DthIter_Dz_eq_mixed_one h ha) b z θ hzθ
  have hfun : Work.Spaces.DzIter b (Work.Spaces.Dz (Work.Spaces.DthIter a u))
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) :=
    (Work.Spaces.DzIter_add_right b 1 (Work.Spaces.DthIter a u)).symm
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Spaces.Dz u)) z θ
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a u) z θ
  rw [hX, hfun]

/-! ## The pointwise domination of the `ℋ^k`-integrands -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`. -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- **Every summand of `HkIntegrand α m (D_z X)` is a summand of `HkIntegrand α (m+1) X`**, with
the same weight: the pure summands by `D_z^i (D_z X) = D_z^{i+1} X`, the mixed summands by the
index shift `mixed_Dz_shift_Q0Sm`.  Hence the pointwise domination of the integrands.  This is
the finite-order (`Q0Sm`) companion of `QuadPorts.HkIntegrand_Dz_le_succ` (`SmoothQuad`) and of
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ` (`SmoothOpen`). -/
theorem HkIntegrand_Dz_le_succ_Q0Sm (α : ℝ) (m : ℕ) {X : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.Q0Sm (m + 1) X) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) X z θ := by
  intro z θ hzθ
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
      = (∑ i ∈ Finset.range (m + 1),
            (Work.Spaces.DzIter i (Work.Spaces.Dz X) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j ≤ m
              then (Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (m + 1) X z θ
      = (∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (m + 2), ∑ b ∈ Finset.range (m + 2),
            (if 1 ≤ a ∧ a + b ≤ m + 1
              then (Work.Spaces.mixed b a X z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (m + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz X) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le m
      (fun a => (Work.Spaces.DzIter a X z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq i X])
  have h2 : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ * W) ^ 2 else 0))
      = (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed (j + 1) i X z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [ite_eq_left hc, ite_eq_left hc,
        mixed_Dz_shift_Q0Sm h (a := i) (by omega) j z θ hzθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hkey : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed (j + 1) i X z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (m + 2), ∑ b ∈ Finset.range (m + 2),
            (if 1 ≤ a ∧ a + b ≤ m + 1
              then (Work.Spaces.mixed b a X z θ * W) ^ 2 else 0)) :=
    Work.Coercivity.SumShiftZ_le m
      (fun a b => (Work.Spaces.mixed b a X z θ * W) ^ 2) (fun a b => sq_nonneg _)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

end Work.FTS.CoercivityFix.Transfer
