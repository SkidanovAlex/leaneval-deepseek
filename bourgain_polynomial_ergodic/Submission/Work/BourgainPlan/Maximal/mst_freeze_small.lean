import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.Maximal.poly_dyadic_of_model

/-!
# Smallness of the lifted one-arc error symbol on the bump of the arc

`mst_lvl_approx_pointwise` says that at level `s`, on the support of the level-`s` bump around an
arc `β ∈ 𝒰(s+1)`, the density symbol `mstWeyl P J` (`J = ⌊exp √(s+1)⌋`) is within
`C exp(−√(s+1)/2)` of the complete sum `mstG P β`.  This module puts that estimate into the two
forms the freezing estimate consumes:

* `mstTht_small`: the same bound for the *lifted* symbol
  `mstTht P J β (iwRep β) u = star (mstG P β) − star (polyWeylKernel P J (iwRep β + u))`, at every
  offset `u` with `|u| < 1/2` such that `η (c_s u) ≠ 0`;
* `mstTht_small_on_closure`: the same bound on the *closure* of that set.  This is the form needed
  when the error symbol is multiplied by a derivative of the bump: `η'` and `η''` may be non-zero
  at points where `η` vanishes, but their support still lies in the closure of the support of `η`,
  and the lifted symbol is continuous.
-/

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The lifted error symbol is continuous in the offset. -/
theorem continuous_mstTht (P : Polynomial ℤ) (J : ℕ) (β : Circ) (r : ℝ) :
    Continuous (fun u : ℝ => mstTht P J β r u) := by
  have h : Continuous (fun u : ℝ => polyWeylKernel P J (r + u)) :=
    (continuous_polyWeylKernel P J).comp (continuous_const.add continuous_id)
  have h2 : Continuous (fun u : ℝ => star (polyWeylKernel P J (r + u))) :=
    continuous_star.comp h
  exact continuous_const.sub h2

/-- **Smallness of the lifted error symbol on the bump of the arc.**  For `β ∈ 𝒰(s+1)`,
`J = ⌊exp √(s+1)⌋`, and every offset `u` with `|u| < 1/2` and `η (c_s u) ≠ 0` (`c_s = mstScale`),

`‖mstTht P J β (iwRep β) u‖ ≤ C exp(−√(s+1)/2)`.

This is `mst_lvl_approx_pointwise` read at the circle point `ξ = β + (u : 𝕋)` (where
`iwRep (u : 𝕋) = u` because `|u| < 1/2`, and `mstWeyl P J ξ = polyWeylKernel P J (iwRep β + u)` by
`1`-periodicity). -/
theorem mstTht_small (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (l : ℕ) (hl : 1 ≤ l) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ (β : Circ), β ∈ mstU l (s + 1) →
      ∀ u : ℝ, |u| < 1 / 2 → η (mstScale P.natDegree χ s * u) ≠ 0 →
      ‖mstTht P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ β (iwRep β) u‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  obtain ⟨C₁, hC₁pos, N₁, happrox⟩ := mst_lvl_approx_pointwise P hd hc hχ0 hχ1 η hη0 l hl
  refine ⟨C₁, hC₁pos, N₁, fun s hs β hβ u hu hηcu => ?_⟩
  have hu' := abs_lt.mp hu
  have hmem : u ∈ Set.Ioc (-(1 / 2) : ℝ) (1 / 2) :=
    ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
  have hiw : iwRep ((u : ℝ) : Circ) = u := by
    have h := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := (-(1 / 2) : ℝ))
      (f := fun y : ℝ => y) (x := u)
      (by rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hmem)
    simpa only [iwRep, AddCircle.liftIoc, Function.comp_apply, Set.domRestrict_apply] using h
  have heta : mstEta P.natDegree χ η s ((u : ℝ) : Circ) = η (mstScale P.natDegree χ s * u) := by
    rw [mstEta_eq_mstScale, hiw]
  have hne : mstEta P.natDegree χ η s ((β + ((u : ℝ) : Circ)) - β) ≠ 0 := by
    rw [add_sub_cancel_left, heta]; exact hηcu
  have happ := happrox s hs β (β + ((u : ℝ) : Circ)) hβ hne
  rw [mstTht_eq_mstWeyl P _ β u, ← star_sub, norm_star]
  exact (norm_sub_rev _ _).trans_le happ

/-- **The sup bound on the closure of the bump.**  With `c_s = mstScale P.natDegree χ s > 1` and
`J = ⌊exp √(s+1)⌋`, the lifted error symbol is bounded by `C exp(−√(s+1)/2)` on the closure of
`{u | η (c_s u) ≠ 0}`.  (On the open set this is `mstTht_small`; the bound extends to the closure
because the symbol is continuous.  The hypothesis `η x = 0` for `1/2 < |x|` and `c_s > 1` put the
open set inside `|u| < 1/2`, which is where `mstTht_small` applies.) -/
theorem mstTht_small_on_closure (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (l : ℕ) (hl : 1 ≤ l) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ (β : Circ), β ∈ mstU l (s + 1) →
      ∀ u : ℝ, u ∈ closure {u : ℝ | η (mstScale P.natDegree χ s * u) ≠ 0} →
      ‖mstTht P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ β (iwRep β) u‖
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  obtain ⟨C₁, hC₁pos, N₁, hsmall⟩ := mstTht_small P hd hc hχ0 hχ1 η hη0 l hl
  refine ⟨C₁, hC₁pos, max N₁ 1, fun s hs β hβ u hu => ?_⟩
  have hsN : N₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  set c : ℝ := mstScale P.natDegree χ s with hcdef
  have hcpos : 0 < c := mstScale_pos P.natDegree χ s
  have hc1 : 1 < c := by
    rw [hcdef, mstScale_apply]
    refine Real.one_lt_rpow (by norm_num) ?_
    have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have : (0 : ℝ) < (P.natDegree : ℝ) - χ := by linarith
    positivity
  -- the open bump lies in `|u| < 1/2`
  have hsub : {u : ℝ | η (c * u) ≠ 0} ⊆ {u : ℝ | |u| < 1 / 2} := by
    intro v hv
    have hle : |c * v| ≤ 1 / 2 := le_of_not_gt (fun hcon => hv (hη0 (c * v) hcon))
    rw [abs_mul, abs_of_pos hcpos] at hle
    have h2 : (1 : ℝ) / 2 < c * (1 / 2) := by linarith
    have h3 : c * |v| < c * (1 / 2) := lt_of_le_of_lt hle h2
    exact (mul_lt_mul_iff_of_pos_left hcpos).mp h3
  -- the sublevel set of the (continuous) symbol is closed
  have hclosed : IsClosed {u : ℝ | ‖mstTht P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ β
      (iwRep β) u‖ ≤ C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))} :=
    isClosed_le (continuous_norm.comp (continuous_mstTht P _ β (iwRep β))) continuous_const
  exact closure_minimal (fun v hv => hsmall s hsN β hβ v (hsub hv) hv) hclosed hu

end

end Work.BourgainPlan.Maximal
