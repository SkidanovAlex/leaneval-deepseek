import Mathlib
import Submission.Work.Lattice.ActiveBlockEuclid
import Submission.Work.Lattice.FlagMemberCriterion
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank

/-!
# The per-member supply of the §3 extraction

At a flag member `V ≤ Λ_t` (a saturated subgroup of the flowed lattice, of rank `j = subDim V`),
the §3 extraction (de Saxcé, Prop. 5) needs an orthonormal family **inside** `V` whose wedge
carries `π₊`-mass: this module produces it from the *active block* data, with an explicit uniform
constant `cStar d := (2^{3d})⁻¹`.

Module `Submission.Work.Extraction.Supply`, namespace `Submission.Supply`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.Supply

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowDataMax
open Submission.FlowRateAsymptotic
open Submission.FlagMemberCriterion
open Submission.GraysonLattice
open Submission.PlaneFinrank
open Submission.ActiveBlock
open Submission.ActiveBlockEuclid
open Submission.LatticePolygon
open Commons.Analysis.InnerProductSpace

variable {d : ℕ}

/-- The uniform lower bound for the `π₊`-mass of the supply of a flag member. -/
noncomputable def cStar (d : ℕ) : ℝ := ((2 : ℝ) ^ (3 * d))⁻¹

lemma cStar_pos (d : ℕ) : 0 < cStar d := by
  unfold cStar; positivity

/-- The explicit Lemma-5 mass constant dominates `cStar`. -/
lemma cStar_le_massConst {j u : ℕ} (hud : u ≤ j) (hjd : j ≤ d) :
    cStar d ≤ (Real.sqrt ((Nat.choose d j : ℕ) : ℝ))⁻¹ / (Nat.choose j (j - u) : ℝ) := by
  have hcpos : 0 < ((Nat.choose d j : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hjd
  have hCpos : 0 < ((Nat.choose j (j - u) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.sub_le j u)
  have hc : ((Nat.choose d j : ℕ) : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast Nat.choose_le_two_pow d j
  have hC : ((Nat.choose j (j - u) : ℕ) : ℝ) ≤ (2 : ℝ) ^ d := by
    have h1 : ((Nat.choose j (j - u) : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_two_pow j (j - u)
    have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hjd
    linarith
  have hsqrt : Real.sqrt ((Nat.choose d j : ℕ) : ℝ) ≤ (2 : ℝ) ^ d := by
    have h2 : ((Nat.choose d j : ℕ) : ℝ) ≤ ((2 : ℝ) ^ d) ^ 2 := by
      have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
      nlinarith [hc, h3]
    calc Real.sqrt ((Nat.choose d j : ℕ) : ℝ) ≤ Real.sqrt (((2 : ℝ) ^ d) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = (2 : ℝ) ^ d := Real.sqrt_sq (by positivity)
  have hkey : Real.sqrt ((Nat.choose d j : ℕ) : ℝ) * ((Nat.choose j (j - u) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (3 * d) := by
    have h4 : (2 : ℝ) ^ d * (2 : ℝ) ^ d = (2 : ℝ) ^ (2 * d) := by rw [← pow_add]; ring_nf
    have h5 : (2 : ℝ) ^ (2 * d) ≤ (2 : ℝ) ^ (3 * d) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc Real.sqrt ((Nat.choose d j : ℕ) : ℝ) * ((Nat.choose j (j - u) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ d :=
          mul_le_mul hsqrt hC hCpos.le (by positivity)
      _ = (2 : ℝ) ^ (2 * d) := h4
      _ ≤ (2 : ℝ) ^ (3 * d) := h5
  have hpos : 0 < Real.sqrt ((Nat.choose d j : ℕ) : ℝ) * ((Nat.choose j (j - u) : ℕ) : ℝ) :=
    mul_pos (Real.sqrt_pos.mpr hcpos) hCpos
  have h1 : ((2 : ℝ) ^ (3 * d))⁻¹ ≤
      (Real.sqrt ((Nat.choose d j : ℕ) : ℝ) * ((Nat.choose j (j - u) : ℕ) : ℝ))⁻¹ :=
    (inv_le_inv₀ (by positivity) hpos).mpr hkey
  rw [cStar]
  calc ((2 : ℝ) ^ (3 * d))⁻¹
      ≤ (Real.sqrt ((Nat.choose d j : ℕ) : ℝ) * ((Nat.choose j (j - u) : ℕ) : ℝ))⁻¹ := h1
    _ = (Real.sqrt ((Nat.choose d j : ℕ) : ℝ))⁻¹ / ((Nat.choose j (j - u) : ℕ) : ℝ) := by
        rw [mul_inv, div_eq_mul_inv]

/-- **The per-member supply.** -/
theorem exists_supply {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ)
    {V : Submodule ℤ (RD d)} (hV1 : 1 ≤ subDim V)
    {w : Fin (subDim V) → RD d} (hwli : LinearIndependent ℝ w)
    {u : ℕ} (hact : IsFirstActiveBlock (d := d) ℓ (subDim_le_ambient V) t
      (exteriorPower.ιMulti ℝ (subDim V) w) u)
    (hspan : Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (w i))) = realSpan V) :
    ∃ a : Fin (subDim V - u) → RD d, Orthonormal ℝ a ∧
      Submodule.span ℝ (Set.range a) ≤ realSpan V ∧
      cStar d ≤ ‖blockElem (d := d) (k := subDim V - u) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ (subDim V - u) a) 0‖ := by
  classical
  have hjd : subDim V ≤ d := subDim_le_ambient V
  have hj0 : 0 < subDim V := lt_of_lt_of_le Nat.zero_lt_one hV1
  have hli : LinearIndependent ℝ (fun i => eFlow (d := d) ℓ t (w i)) := by
    have heq : (fun i => eFlow (d := d) ℓ t (w i)) =
        (fun i => (eEquiv (d := d) ℓ t : RD d →ₗ[ℝ] RD d) (w i)) := by
      funext i; rw [eEquiv_coe]
    rw [heq]
    exact hwli.map' _ (LinearMap.ker_eq_bot.mpr (eEquiv (d := d) ℓ t).injective)
  obtain ⟨aa, haaON, haamem, haaspan⟩ :=
    Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank
      (Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (w i))))
      (finrank_span_range (fun i => eFlow (d := d) ℓ t (w i)) hli)
  have hu_le : u ≤ subDim V := hact.1.1
  obtain ⟨b, hbON, hbspan, hbmass⟩ :=
    exists_orthonormal_dominated_of_activeBlock (d := d) hℓ0 hℓd (k := subDim V)
      (hk := subDim_le_ambient V) hj0 (t := t) (v := w) hwli (a := aa) haaON haaspan
      (u := u) hu_le hact.1.2.2
  refine ⟨b, hbON, ?_, ?_⟩
  · refine le_trans hbspan ?_
    rw [haaspan, hspan]
  · exact le_trans (cStar_le_massConst (d := d) hu_le hjd) hbmass

end Submission.Supply

end
