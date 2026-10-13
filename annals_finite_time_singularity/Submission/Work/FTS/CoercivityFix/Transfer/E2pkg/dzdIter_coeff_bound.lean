/-
# `Transfer/E2pkg/dzdIter_coeff_bound.lean` — the coefficient bounds on the transfer defect

The transfer `𝓛_Γ^T = 𝓛̂ + Corr` has the defect `E2 α f = Ê₂ f + Γ(θ)·radS α f z`, whose
`z`-part is built from the two elementary radial profiles

* `ampA α z = 2z/(c(α)(1+z)²)` (the nonlocal term of `𝓛_Γ`, feeding `radA`), and
* `ampB α z = 2z²/(1+z)³` (the projector correction, feeding `radS`);

see `Transfer/Profiles.lean`.  Bounding `E2` in the weighted `ℋᵏ`-norms needs two soft facts
about these profiles, which this file proves:

* every `(z ∂_z)`-iterate of `ampA α` up to order `4` is bounded on `(0,∞)` — so that the
  multiplier has a *uniform* jet bound `K`;
* the `w²`-weighted square of every `(z ∂_z)`-iterate of `ampB α` up to order `4` is integrable
  on `Iz = [0,∞)` — so that the projector correction contributes finitely to the `ℋ⁴`-norm.

## The proofs

**The boundedness half.**  `ampA α = (2/c(α))·φ` with `φ(z) = z/(1+z)²`, as *functions* (the
identity `(2z)/(c(1+z)²) = (2/c)(z/(1+z)²)` holds unconditionally because Lean's totalised `/`
sends both sides to `0` when `c = 0`).  Writing `Zop u = z·∂_z u` (`Work.Spaces.Zop`, which is
definitionally `Work.Elliptic.Dzd`), we have `DzdIter j = Zop^[j]`, the iterates of a constant
multiple are the constant multiple of the iterates (`Zop_iter_const_mul`, from the unconditional
`deriv_const_mul_field`), and `zop_phi_bound`
(`E2Bound/zop_phi_bound.lean`, the Möbius-chart argument of `ZopPhiDefs.lean`) bounds
`Zop^[b] φ` uniformly for `b ≤ 4`.  Since `1/10 ≤ c(α) ≤ 10` (`Spaces.c_bounds`) gives
`2/c(α) ≤ 20`, the constant `K = 20·K₀` works.

**The integrability half.**  `ampB α = 2·(z²/(1+z)³)`, whose `(z∂_z)`-iterates have the closed
forms `z²N_j(z)/(1+z)^{j+3}` (`E2pkg/dzdIter_defs.lean`).  Since `w(z)² = (1+z)⁴/z⁴`, the
weighted square is `N_j(z)²/(1+z)^{2+2j}`, and `|N_j(z)| ≤ C(1+z)^j` gives the bound
`C²/(1+z)²`, integrable on `Iz`.  The two inputs are the delegated lemmas `E2pkg.rB_iter` (the
closed forms, on `z > 0`) and `E2pkg.rB_sq_w_integrable` (the integrability of the weighted
square of the closed form); the passage from `Ioi 0` (where `rB` is identified) to `Iz = Ici 0`
is the null-set identity `Ioi 0 =ᵐ Ici 0`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_defs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_iter
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_sq_w_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

/-! ## `DzdIter` is the iterate of `Zop` -/

/-- `Work.Elliptic.Dzd` and `Work.Spaces.Zop` are the same operator `z ↦ z·u'(z)`, hence so are
their iterates. -/
theorem DzdIter_eq_Zop_iter (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j u = Work.Spaces.Zop^[j] u := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Work.Elliptic.DzdIter_succ, ih, Function.iterate_succ_apply']
      rfl

/-- Iterating `Zop` commutes with multiplication by a constant.  (Mathlib's
`deriv_const_mul_field` is unconditional.) -/
theorem Zop_iter_const_mul (j : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[j] (fun z => c * u z) = fun z => c * Work.Spaces.Zop^[j] u z := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext z
      simp only [Work.Spaces.Zop]
      rw [deriv_const_mul_field]
      ring

/-! ## The boundedness half: `ampA` -/

/-- `ampA α = (2/c(α))·φ` **as functions**; the identity holds for every `z` because both sides
vanish when `c(α) = 0` (`mul_inv` handles the totalised inverse). -/
theorem ampA_eq_const_mul_fA (α : ℝ) :
    Work.FTS.CoercivityFix.Transfer.ampA α
      = fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2) := by
  funext z
  simp only [Work.FTS.CoercivityFix.Transfer.ampA, div_eq_mul_inv]
  rw [mul_inv]
  ring

/-- **The boundedness half.**  All `(z∂_z)`-iterates of `ampA α` up to order `4` are bounded on
`(0,∞)` by `20·K₀`, where `K₀` is the chart bound of `E2Bound.zop_phi_bound`. -/
theorem ampA_dzdIter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K := by
  obtain ⟨K₀, hK₀, hbd⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 4
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h2c : 2 / Work.Spaces.c α ≤ 20 := by
    rw [div_le_iff₀ hcpos]
    linarith
  refine ⟨20 * K₀, by positivity, ?_⟩
  intro j hj z hz
  have hb : |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ := hbd j hj z hz
  calc |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z|
      = |Work.Spaces.Zop^[j] (Work.FTS.CoercivityFix.Transfer.ampA α) z| := by
        rw [DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[j] (fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2)) z| := by
        rw [ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c α) * Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Zop_iter_const_mul]
    _ = |2 / Work.Spaces.c α|
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := abs_mul _ _
    _ = (2 / Work.Spaces.c α)
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c α) * K₀ := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 20 * K₀ := mul_le_mul_of_nonneg_right h2c hK₀

/-! ## The integrability half: `ampB` -/

/-- `ampB α = 2·fB` as functions. -/
theorem ampB_eq_two_mul_fB (α : ℝ) :
    Work.FTS.CoercivityFix.Transfer.ampB α = fun z => 2 * (z ^ 2 / (1 + z) ^ 3) := by
  funext z
  simp only [Work.FTS.CoercivityFix.Transfer.ampB, div_eq_mul_inv]
  ring

/-- The `(z∂_z)`-iterates of `ampB α` are twice the iterates of `z²/(1+z)³`, as functions. -/
theorem dzdIter_ampB_eq (α : ℝ) (j : ℕ) :
    Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α)
      = fun z => 2 * Work.Elliptic.DzdIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z := by
  rw [DzdIter_eq_Zop_iter, ampB_eq_two_mul_fB, Zop_iter_const_mul]
  rw [← DzdIter_eq_Zop_iter]

/-- **The integrability half**, given the two closed-form inputs. -/
theorem ampB_sq_w_integrable_of
    (hA : ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = rB j z)
    (hB : ∀ j ≤ 4, MeasureTheory.IntegrableOn
      (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (α : ℝ) :
    ∀ j ≤ 4, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  intro j hj
  have hG : MeasureTheory.IntegrableOn
      (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := hB j hj
  -- the two integrands agree pointwise on `Ioi 0`
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = 4 * ((rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro z hz
    rw [congrFun (dzdIter_ampB_eq α j) z, hA j hj z hz]
    ring
  have hG' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hG.mono_set Set.Ioi_subset_Ici_self
  have hae : (fun z : ℝ => (Work.Elliptic.DzdIter j
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z : ℝ => 4 * ((rB j z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact hpoint z hz
  have hF' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (hG'.const_mul 4).congr hae.symm
  have hmeas : volume.restrict (Set.Ioi (0 : ℝ))
      = volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  show MeasureTheory.Integrable
    (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2) (volume.restrict Work.Spaces.Iz)
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, ← hmeas]
  exact hF'

/-! ## The main theorem -/

theorem dzdIter_coeff_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) ∧
    (∀ j ≤ 4, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :=
  ⟨ampA_dzdIter_bound α hα hα1,
    ampB_sq_w_integrable_of (fun j hj z hz => rB_iter j hj z hz)
      (fun j hj => rB_sq_w_integrable j hj) α⟩

end Work.FTS.CoercivityFix.Transfer.E2pkg
