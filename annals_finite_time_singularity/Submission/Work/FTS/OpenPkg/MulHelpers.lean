/-
# `OpenPkg/MulHelpers` — the pointwise machinery for the two remaining `N4Norm'` field lemmas

The field lemmas `wrad_field` (multiplication by a function of `z` alone) and `wang_field`
(multiplication by a function of `θ` alone) in the `D`-sup norms are Leibniz computations.  This
module collects the two ingredients they share:

* `mixed_le_WDp` — the pointwise bound `|D_z^bD_θ^j f z θ| ≤ WDp 4 f` on the open quadrant, for
  `f` with honest `D`-sup norm (`WDMem 4 f`) and `b + j ≤ 4`;
* `DthIter_const_theta` and `DzIter_const_z` — the vanishing of the iterated operators on the
  functions which are constant in `θ` resp. in `z` (which is what collapses the double Leibniz
  sum of `Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed` to a single sum).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **A pointwise bound for every mixed derivative of an honest function** by its `D`-sup norm. -/
theorem mixed_le_WDp {f : Fn} (hf : WDMem 4 f) {b j : ℕ} (hbj : b + j ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.mixed b j f z θ| ≤ WDp 4 f := by
  classical
  obtain ⟨K, hK⟩ := hf b j hbj
  have hbdd : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2
      ∧ y = |Work.Spaces.mixed b j f z θ|} :=
    ⟨K, by rintro y ⟨z', hz', θ', hθ', hθ'', rfl⟩; exact hK z' θ' hz' hθ' hθ''⟩
  have h1 : |Work.Spaces.mixed b j f z θ| ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) :=
    le_csSup hbdd ⟨z, hz, θ, hθ0, hθ1, rfl⟩
  have h2 : Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) ≤ WDp 4 f := by
    have hb' : b ∈ Finset.range (4 + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
    have hj' : j ∈ Finset.range (4 + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
    have hnn : ∀ a c : ℕ, 0 ≤ (if a + c ≤ 4 then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed a c f) else 0) := fun a c => by
      split_ifs with h
      · exact supAbsO_nonneg _
      · exact le_rfl
    have hinner : (if b + j ≤ 4 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0)
        ≤ ∑ j' ∈ Finset.range (4 + 1),
            (if b + j' ≤ 4 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0) :=
      Finset.single_le_sum (f := fun j' => if b + j' ≤ 4 then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0) (fun j' _ => hnn b j') hj'
    have houter : (∑ j' ∈ Finset.range (4 + 1),
          (if b + j' ≤ 4 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0))
        ≤ ∑ b' ∈ Finset.range (4 + 1), ∑ j' ∈ Finset.range (4 + 1),
            (if b' + j' ≤ 4 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' j' f) else 0) :=
      Finset.single_le_sum (f := fun b' => ∑ j' ∈ Finset.range (4 + 1),
          (if b' + j' ≤ 4 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' j' f) else 0))
        (fun b' _ => Finset.sum_nonneg fun j' _ => hnn b' j') hb'
    have h := le_trans hinner houter
    rw [ite_eq_left hbj] at h
    simpa only [WDp] using h
  linarith

/-- The iterated angular operator applied to a function which is constant in `θ` vanishes
(from the first application on). -/
theorem DthIter_const_theta (φ : ℝ → ℝ) : ∀ a : ℕ, 1 ≤ a →
    Work.Spaces.DthIter a (fun z _ => φ z) = fun _ _ => 0 := by
  intro a ha
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  induction m with
  | zero =>
    funext z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
      Work.Spaces.pth]
    rw [deriv_const]
    ring
  | succ m ih =>
    funext z θ
    change Work.Spaces.Dth (Work.Spaces.DthIter (m + 1) (fun z _ => φ z)) z θ = 0
    rw [ih (by omega)]
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [show (fun θ' => (0 : ℝ)) = fun _ => 0 from rfl, deriv_const]
    ring

/-- The iterated radial operator applied to a function which is constant in `z` vanishes
(from the first application on). -/
theorem DzIter_const_z (a : ℝ → ℝ) : ∀ c : ℕ, 1 ≤ c →
    Work.Spaces.DzIter c (fun _ θ => a θ) = fun _ _ => 0 := by
  intro c hc
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  induction m with
  | zero =>
    funext z θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.Spaces.pz]
    rw [deriv_const]
    ring
  | succ m ih =>
    funext z θ
    change Work.Spaces.Dz (Work.Spaces.DzIter (m + 1) (fun _ θ => a θ)) z θ = 0
    rw [ih (by omega)]
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => (0 : ℝ)) = fun _ => 0 from rfl, deriv_const]
    ring

/-- The iterated angular operator kills every function which is constant in `θ` (derivatives of
pointwise-constant functions vanish, and the class is preserved). -/
theorem DthIter_eq_zero_of_theta_const {F : Fn} (hF : ∀ z θ, F z θ = F z 0) :
    ∀ i : ℕ, 1 ≤ i → Work.Spaces.DthIter i F = fun _ _ => 0 := by
  intro i hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  induction m with
  | zero =>
    funext z θ
    change Work.Spaces.Dth F z θ = 0
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    have hcongr : (fun θ' => F z θ') =ᶠ[𝓝 θ] fun _ => F z 0 :=
      Filter.Eventually.of_forall fun θ' => hF z θ'
    rw [hcongr.deriv_eq, deriv_const]
    ring
  | succ m ih =>
    funext z θ
    change Work.Spaces.Dth (Work.Spaces.DthIter (m + 1) F) z θ = 0
    rw [ih (by omega)]
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    have hcongr : (fun θ' => (0 : ℝ)) =ᶠ[𝓝 θ] fun _ => (0 : ℝ) :=
      Filter.Eventually.of_forall fun θ' => rfl
    rw [hcongr.deriv_eq, deriv_const]
    ring

/-- The iterated radial operator kills every function which is constant in `z`. -/
theorem DzIter_eq_zero_of_z_const {F : Fn} (hF : ∀ z θ, F z θ = F 0 θ) :
    ∀ c : ℕ, 1 ≤ c → Work.Spaces.DzIter c F = fun _ _ => 0 := by
  intro c hc
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  induction m with
  | zero =>
    funext z θ
    change Work.Spaces.Dz F z θ = 0
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    have hcongr : (fun z' => F z' θ) =ᶠ[𝓝 z] fun _ => F 0 θ :=
      Filter.Eventually.of_forall fun z' => hF z' θ
    rw [hcongr.deriv_eq, deriv_const]
    ring
  | succ m ih =>
    funext z θ
    change Work.Spaces.Dz (Work.Spaces.DzIter (m + 1) F) z θ = 0
    rw [ih (by omega)]
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    have hcongr : (fun z' => (0 : ℝ)) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      Filter.Eventually.of_forall fun z' => rfl
    rw [hcongr.deriv_eq, deriv_const]
    ring

/-- The iterated radial operator kills the zero function. -/
theorem DzIter_zero_fun (c : ℕ) :
    Work.Spaces.DzIter c (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    funext z θ
    change Work.Spaces.Dz (Work.Spaces.DzIter c (fun _ _ => (0 : ℝ))) z θ = 0
    rw [ih]
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => (0 : ℝ)) = fun _ => 0 from rfl, deriv_const]
    ring

end Work.FTS.OpenPkg
