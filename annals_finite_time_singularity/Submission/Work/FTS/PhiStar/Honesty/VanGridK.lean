/-
Copyright: work module for the Elgindi finite-time singularity project.

# `vanGridK` — the general-level grid majorant of the vanishing-family honesty transfer

The level-`7` transfer `Work.FTS.ClassC.HkMem_seven_slots_of_vanishing_family` proves
`HkMem α 7` of the three derivatives `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ` from two families of
*integrable* angular slots of `Ψ`:

* `hσ`: `HkMem α 0 (D_z^l ∂_θ^m Ψ)` for `l ≤ 9`, `m ≤ 2` (the singular `η`-weight), and
* `hV`: integrability of `(D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t-4-γ}` for `3 ≤ t ≤ 9`, `l ≤ 9`
  (the *vanishing* weights).

The target of the present node is the same statement at an **arbitrary** level `K`, with the
two families supplied up to `K + 2` (`hσ`: `l ≤ K + 2`, `m ≤ 2`; `hV`: `3 ≤ t ≤ K + 2`,
`l ≤ K + 2`).  This module fixes the corresponding *grid majorant* and its elementary
membership lemmas; they are the level-`K` analogues of the `vanGrid`
(`Work.FTS.ClassC.VanishFamilyDefs`) membership lemmas of the level-`7` development, and the
proofs are verbatim relabellings of those (the arithmetic of the two induction ranges is the
only change).

* `vanGridK α Ψ K` is the sum of **all** the integrands whose integrability the hypotheses
  `hσ`/`hV` provide;
* `vanGridK_nonneg`, and the single-slot membership lemmas
  `hkDze_zero_DzIter_le_vanGridK` (pure radial slot),
  `hkIntegrand_le_vanGridK` (angular slot of order `≤ 2`, singular weight),
  `hVint_le_vanGridK` (angular slot of order `≥ 3`, vanishing weight),
  `vig_slot_le_vanGridK` (a plain angular slot `D_z^l ∂_θ^r Ψ` against the vanishing weight
  `sin(2θ)^{2r-γ}` — the form in which the reduction `HkMem_of_pure_and_vanishing` consumes
  them).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.VanishFamilyDefs
import Submission.Work.FTS.ClassC.VanishWeightDom
import Submission.Work.FTS.ClassC.HkMem_seven_slots_of_plain_family

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The level-`K` grid majorant.**  The sum of all the integrands of the two families whose
integrability the hypotheses of the honesty transfer supply: the singular-weight `ℋ⁰`-slots
`HkIntegrand α 0 (D_z^l ∂_θ^m Ψ)` (`l ≤ K + 2`, `m ≤ 2`) and the vanishing-weight slots
`hVint α Ψ t l` (`3 ≤ t ≤ K + 2`, `l ≤ K + 2`). -/
def vanGridK (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (K : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (∑ l ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      + ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l ∈ Finset.range (K + 3),
          Work.FTS.ClassC.hVint α Ψ t l z θ

/-- The grid majorant is nonnegative on the angular interval. -/
theorem vanGridK_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (K : ℕ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ vanGridK α Ψ K z θ := by
  rw [vanGridK]
  refine add_nonneg
    (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
    (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ => ?_)
  simp only [Work.FTS.ClassC.hVint]
  exact mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Work.FTS.ClassC.sin_two_nonneg_of_mem_Iθ' hθ) _)

/-! ## Membership of the single slots in the grid majorant -/

/-- Every pure radial slot `HkIntegrand α 0 (D_z^l Ψ)` with `l ≤ K + 2` is a summand of the
grid majorant. -/
theorem hkDze_zero_DzIter_le_vanGridK {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {K l : ℕ}
    (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l Ψ) z θ ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ
  have hmem_l : l ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have hmem_m : (0 : ℕ) ∈ Finset.range 3 := Finset.mem_range.mpr (by norm_num)
  -- the slot with `m = 0` is the `m = 0` term of the inner sum
  have hinner : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l Ψ) z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ := by
    simpa only [Work.Spaces.pthIter_zero] using
      (Finset.single_le_sum
        (f := fun m => Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
        (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_m)
  have houter : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l' ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun l' => ∑ m ∈ Finset.range 3, Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ)
      (fun l' _ => Finset.sum_nonneg fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_l
  have htail : 0 ≤ ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l' ∈ Finset.range (K + 3),
      Work.FTS.ClassC.hVint α Ψ t l' z θ :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l' _ => by
      simp only [Work.FTS.ClassC.hVint]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  rw [vanGridK]
  linarith

/-- The `HkIntegrand α 0`-slot of angular order `r ≤ 2` and radial order `l ≤ K + 2` is a
summand of the grid majorant. -/
theorem hkIntegrand_le_vanGridK {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {K r l : ℕ}
    (hr : r ≤ 2) (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ)) z θ
        ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ
  have hmem_l : l ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have hmem_r : r ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
  have hinner : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ))
        z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun m => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_r
  have hmid : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l' ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun l' => ∑ m ∈ Finset.range 3, Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ)
      (fun l' _ => Finset.sum_nonneg fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_l
  have htail : 0 ≤ ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l' ∈ Finset.range (K + 3),
      Work.FTS.ClassC.hVint α Ψ t l' z θ :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l' _ => by
      simp only [Work.FTS.ClassC.hVint]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  rw [vanGridK]
  linarith

/-- The `hVint`-slot of angular order `3 ≤ t ≤ K + 2` and radial order `l ≤ K + 2` is a summand
of the grid majorant. -/
theorem hVint_le_vanGridK {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {K t l : ℕ}
    (ht3 : 3 ≤ t) (ht : t ≤ K + 2) (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.hVint α Ψ t l z θ ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ
  have hmem_t : t ∈ Finset.Icc 3 (K + 2) := Finset.mem_Icc.mpr ⟨ht3, ht⟩
  have hmem_l : l ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ t' l' : ℕ, 0 ≤ Work.FTS.ClassC.hVint α Ψ t' l' z θ := fun t' l' => by
    simp only [Work.FTS.ClassC.hVint]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  have hinner : Work.FTS.ClassC.hVint α Ψ t l z θ
      ≤ ∑ l' ∈ Finset.range (K + 3), Work.FTS.ClassC.hVint α Ψ t l' z θ :=
    Finset.single_le_sum (f := fun l' => Work.FTS.ClassC.hVint α Ψ t l' z θ)
      (fun l' _ => hnonneg t l') hmem_l
  have hmid : (∑ l' ∈ Finset.range (K + 3), Work.FTS.ClassC.hVint α Ψ t l' z θ)
      ≤ ∑ t' ∈ Finset.Icc 3 (K + 2), ∑ l' ∈ Finset.range (K + 3),
          Work.FTS.ClassC.hVint α Ψ t' l' z θ :=
    Finset.single_le_sum
      (f := fun t' => ∑ l' ∈ Finset.range (K + 3), Work.FTS.ClassC.hVint α Ψ t' l' z θ)
      (fun t' _ => Finset.sum_nonneg fun l' _ => hnonneg t' l') hmem_t
  have hhead : 0 ≤ ∑ l' ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.sum_nonneg fun l' _ => Finset.sum_nonneg fun m _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  rw [vanGridK]
  linarith

/-- **A single plain angular slot against the grid.**  For `1 ≤ r ≤ K + 2` and `l ≤ K + 2`, the
vanishing-weight slot `(D_z^l ∂_θ^r Ψ · w)² · sin(2θ)^{2r-γ}` is dominated by the grid
majorant: for `r ≤ 2` the singular `ℋ⁰`-slot dominates it (because `2r - γ ≥ 2 - 3/2 ≥ -η`),
and for `r ≥ 3` the grid's own `hVint`-slot has the smaller exponent `2r - 4 - γ`. -/
theorem vig_slot_le_vanGridK {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2) (Ψ : ℝ → ℝ → ℝ)
    (K r l : ℕ) (hr : 1 ≤ r) (hrK : r ≤ K + 2) (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ) z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)
        ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  by_cases hr2 : r ≤ 2
  · -- `r ≤ 2`: the singular `ℋ⁰`-integrand dominates the vanishing weight
    refine le_trans (Work.FTS.ClassC.sq_mul_sin_le_HkIntegrand_zero α _ hθ ?_)
      (hkIntegrand_le_vanGridK hr2 hl z θ hθ)
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have heta : Work.Spaces.eta = 99 / 100 := rfl
    have hgam := hγ
    rw [Work.Spaces.gam] at hgam
    rw [heta]
    linarith
  · -- `r ≥ 3`: the grid's own vanishing slot has the smaller exponent `2r - 4 - γ`
    have hr3 : 3 ≤ r := by omega
    refine le_trans (Work.FTS.ClassC.sq_mul_sin_le_sq_mul_sin hθ ?_ ?_)
      (hVint_le_vanGridK hr3 hrK hl z θ hθ)
    · -- `0 ≤ 2r - 4 - γ`
      have hr3' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
      have hgam := hγ
      rw [Work.Spaces.gam] at hgam
      linarith
    · -- `2r - 4 - γ ≤ 2r - γ`
      linarith

end Work.FTS.PhiStar.Honesty
