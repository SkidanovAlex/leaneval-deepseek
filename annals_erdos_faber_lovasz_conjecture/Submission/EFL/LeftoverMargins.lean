import Submission.EFL.DeepInputs
import Submission.EFL.HugeStep
import Submission.EFL.S12Setup
import Submission.Commons.Analysis.Real.exists_mul_exp_neg_lt_one

/-!
# The numerical margin bundle of the Leftover Lemma

This module isolates the *numerical* content of the Leftover Lemma
(`lem:leftover`, §7 of Kang--Kelly--Kühn--Methuku--Osthus): Kahn's theorem
instantiated at `α = 1/2`, the two parameters `t = ⌈4/γ⌉` and `m = ⌈γ²D/10⌉`
of the partition of the colour set, and the bundled hypotheses
`LeftoverMargins` together with the theorem `exists_leftoverMargins` saying
that they hold for all sufficiently large `n`.

It is placed below `S12Step7` in the import order so that the §12 chain can
carry `LeftoverMargins` as a single hypothesis instead of the (unprovable)
`LeftoverStatement`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Kahn's theorem with `α = 1/2`, in the form needed here -/

/-- The instantiated body of Kahn's theorem for `α = 1/2`: a linear hypergraph
of maximum degree at most `D ≥ D₀` and edge sizes at most `r` is
list-edge-colourable with `(3/2)D` colours, provided every list has size at
most `D/4`. -/
def KahnListBody (r : ℕ) (D₀ : ℝ) : Prop :=
  ∀ D : ℝ, D₀ ≤ D → ∀ m : ℕ, ∀ 𝓖 : Hypergraph (Fin m), 𝓖.IsLinear →
    ((hypergraphMaxDegree 𝓖 : ℕ) : ℝ) ≤ D →
    (∀ e : 𝓖, (edgeSize (e : Set (Fin m)) : ℝ) ≤ (r : ℝ)) →
    ∀ c : ℕ, (3 / 2) * D ≤ (c : ℝ) → ∀ L : 𝓖 → Finset (Fin c),
      (∀ e : 𝓖, ((L e).card : ℝ) ≤ D / 4) →
      ∃ φ : 𝓖.Coloring (Fin c), ∀ e : 𝓖, φ.labels e ∉ L e

/-- The canonical threshold of Kahn's theorem at `α = 1/2` and edge size `r`. -/
noncomputable def kahnD₀ (hK : KahnStatement) (r : ℕ) (hr : 2 ≤ r) : ℝ :=
  Classical.choose (hK (1 / 2) (by norm_num) r hr)

theorem kahnD₀_pos (hK : KahnStatement) (r : ℕ) (hr : 2 ≤ r) : 0 < kahnD₀ hK r hr :=
  (Classical.choose_spec (hK (1 / 2) (by norm_num) r hr)).1

theorem kahnD₀_body (hK : KahnStatement) (r : ℕ) (hr : 2 ≤ r) :
    KahnListBody r (kahnD₀ hK r hr) := by
  intro D hD m 𝓖 hlin hdeg hsize c hc L hL
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hbody := (Classical.choose_spec (hK (1 / 2) hα r hr)).2
  exact hbody D hD m 𝓖 hlin hdeg hsize c (by linarith [hc]) L (by intro e; linarith [hL e])


/-! ## The two numerical parameters of the partition -/

/-- The number of parts into which the colour set is split: `t = max 2 ⌈4/γ⌉`. -/
noncomputable def leftoverT (γ : ℝ) : ℕ := max 2 ⌈4 / γ⌉₊

/-- The minimum size of a part: `m = ⌈γ²D/10⌉`. -/
noncomputable def leftoverM (γ : ℝ) (D : ℕ) : ℕ := ⌈γ ^ 2 * (D : ℝ) / 10⌉₊

theorem leftoverT_pos (γ : ℝ) : 0 < leftoverT γ :=
  lt_of_lt_of_le (by norm_num) (le_max_left 2 ⌈4 / γ⌉₊)

theorem leftoverT_one_le (γ : ℝ) : 1 ≤ leftoverT γ :=
  le_trans (by norm_num) (le_max_left 2 ⌈4 / γ⌉₊)

theorem leftoverT_two_le (γ : ℝ) : 2 ≤ leftoverT γ := le_max_left 2 ⌈4 / γ⌉₊

/-- `4 ≤ γ·t` for the number of parts `t = leftoverT γ`. -/
theorem four_le_mul_leftoverT {γ : ℝ} (hγ : 0 < γ) :
    4 ≤ γ * (leftoverT γ : ℝ) := by
  have h1 : 4 / γ ≤ (leftoverT γ : ℝ) :=
    le_trans (Nat.le_ceil (4 / γ)) (by exact_mod_cast le_max_right 2 ⌈4 / γ⌉₊)
  have h2 : γ * (4 / γ) ≤ γ * (leftoverT γ : ℝ) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hγ)
  rwa [mul_div_cancel₀ 4 (ne_of_gt hγ)] at h2

/-- `n/t ≤ γn/4` for the number of parts `t = leftoverT γ`. -/
theorem div_leftoverT_le {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    ((n : ℝ) / (leftoverT γ : ℝ)) ≤ γ * (n : ℝ) / 4 := by
  have ht : (0 : ℝ) < (leftoverT γ : ℝ) := by exact_mod_cast leftoverT_pos γ
  rw [div_le_iff₀ ht]
  have h1 : (4 : ℝ) * (n : ℝ) ≤ (γ * (leftoverT γ : ℝ)) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (four_le_mul_leftoverT hγ) (Nat.cast_nonneg n)
  have h2 : (γ * (n : ℝ) / 4) * (leftoverT γ : ℝ) = (γ * (leftoverT γ : ℝ)) * (n : ℝ) / 4 := by
    ring
  rw [h2, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- `n/t + γn/4 ≤ γn/2` for the number of parts `t = leftoverT γ`. -/
theorem div_leftoverT_add_le {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    ((n : ℝ) / (leftoverT γ : ℝ)) + γ * (n : ℝ) / 4 ≤ γ * (n : ℝ) / 2 := by
  have := div_leftoverT_le hγ n
  linarith


/-! ## The numerical margin bundle for the Leftover Lemma -/

/-- Kahn's threshold `D₀(1/2, r)` at the edge-size bound `max r 2`. -/
noncomputable def kahnD₀' (hK : KahnStatement) (r : ℕ) : ℝ :=
  kahnD₀ hK (max r 2) (le_max_right r 2)

/-- **The numerical hypotheses of the Leftover Lemma**, bundled.  All of them
except `hn4` and `hDn` are "`n` is large enough" conditions (with respect to
the constants `γ, ρ, ε, ξ, r₁`), so for every admissible constant hierarchy
they hold for all sufficiently large `n` (`exists_leftoverMargins`). -/
structure LeftoverMargins (n r₁ : ℕ) (γ ρ ρ_abs ε ξ : ℝ) : Prop where
  /-- Kahn's theorem at the relevant edge-size bound. -/
  hK : KahnStatement
  hn4 : 4 ≤ n
  hDn : (Dparam n ρ : ℝ) ≤ (n : ℝ)
  hkanthr : 20 * kahnD₀' hK r₁ ≤ (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ)
  hTm : leftoverT (10 * Real.sqrt γ) * leftoverM (10 * Real.sqrt γ) (Dparam n ρ)
      ≤ D'param (Dparam n ρ) γ
  hcher : ((D'param (Dparam n ρ) γ : ℕ) : ℝ) *
      (2 * Real.exp (-(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2) /
        (2 * (((max r₁ 2 : ℕ) : ℝ) * ((n : ℝ) / (leftoverT (10 * Real.sqrt γ) : ℝ) +
          (10 * Real.sqrt γ) * (n : ℝ) / 4 / 3))))) < 1
  hm : HugeMargins n ρ_abs ε (10 * Real.sqrt γ) (1 / 2) ξ

theorem eventually_le_natCast (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, c ≤ (n : ℝ) := by
  have h : ∀ᶠ n : ℕ in Filter.atTop, ⌈c⌉₊ ≤ n := Filter.eventually_ge_atTop _
  filter_upwards [h] with n hn
  exact le_trans (Nat.le_ceil c) (by exact_mod_cast hn)

theorem eventually_Dparam_ge_quarter {ρ : ℝ} (hρ4 : ρ ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) / 4 ≤ (Dparam n ρ : ℝ) := by
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, 8 ≤ n := Filter.eventually_ge_atTop 8
  filter_upwards [h1] with n hn
  have h2 : (1 - ρ) * ((n : ℝ) - 1) - 1 ≤ (Dparam n ρ : ℝ) := by
    rw [Dparam]
    have h3 := Nat.lt_floor_add_one ((1 - ρ) * ((n : ℝ) - 1))
    linarith only [h3]
  have hn' : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith only [h2, hn', hρ4]

theorem eventually_Dparam_le_self {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop, (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
  have h0 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  filter_upwards [h0] with n hn
  rw [Dparam]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (0 : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by nlinarith only [hρ4, hn1]
  have h3 : (⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
    Nat.floor_le h2
  nlinarith only [h3, hρ0, hρ4, hn1]

/-- **The numerical hypotheses of the Leftover Lemma hold for all large `n`.**

For a constant hierarchy `0 < γ ≤ 1/100`, `0 < ρ ≤ 1/4`, `0 < ε ≤ 1`, `0 < ξ`
with `10⁴√γ ≤ ρε` and `4000ξ ≤ √γ ρ`, all the margin conditions of
`LeftoverMargins` hold for every sufficiently large `n`. -/
theorem exists_leftoverMargins (hK : KahnStatement) {r₁ : ℕ} {γ ρ ρ_abs ε ξ : ℝ}
    (hγ0 : 0 < γ) (hγ100 : γ ≤ 1 / 100) (hρ0 : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hρabs0 : 0 < ρ_abs) (hρabs1 : ρ_abs ≤ 1)
    (hε0 : 0 < ε) (hε1000 : 1000 * ε ≤ 1) (hξ0 : 0 < ξ)
    (hsmall : 10 ^ 4 * Real.sqrt γ ≤ ρ_abs * ε)
    (hξsmall : 4000 * ξ ≤ Real.sqrt γ * ρ_abs) :
    ∃ N : ℕ, ∀ n ≥ N, LeftoverMargins n r₁ γ ρ ρ_abs ε ξ := by
  classical
  have hsqrt0 : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ0
  have hg0 : 0 < 10 * Real.sqrt γ := by linarith
  have hg1 : 10 * Real.sqrt γ ≤ 1 := by
    have h1 : Real.sqrt γ ≤ 1 / 10 := by
      have h2 : (1 / 10 : ℝ) ^ 2 = 1 / 100 := by norm_num
      rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 10), h2]
      exact hγ100
    linarith
  have hgsq : (10 * Real.sqrt γ) ^ 2 = 100 * γ := by
    have h := Real.sq_sqrt (le_of_lt hγ0)
    nlinarith only [h]
  -- ## `n` is large
  have hF1 : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ n := Filter.eventually_ge_atTop 4
  have hF2 : ∀ᶠ n : ℕ in Filter.atTop, (Dparam n ρ : ℝ) ≤ (n : ℝ) :=
    eventually_Dparam_le_self (le_of_lt hρ0) hρ4
  have hDq : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) / 4 ≤ (Dparam n ρ : ℝ) :=
    eventually_Dparam_ge_quarter hρ4
  have hDbig : ∀ c : ℝ, ∀ᶠ n : ℕ in Filter.atTop, c ≤ (Dparam n ρ : ℝ) := by
    intro c
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, c ≤ (n : ℝ) / 4 := by
      have h2 := eventually_le_natCast (4 * c)
      filter_upwards [h2] with n hn
      linarith only [hn]
    filter_upwards [h1, hDq] with n hn1 hn2
    linarith only [hn1, hn2]
  -- ## The Kahn threshold
  have hF3 : ∀ᶠ n : ℕ in Filter.atTop,
      20 * kahnD₀' hK r₁ ≤ (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ) := by
    have h100 : (0 : ℝ) < 100 * γ := by linarith
    filter_upwards [hDbig (20 * kahnD₀' hK r₁ / (100 * γ))] with n hn
    rw [hgsq]
    have h2 : (20 * kahnD₀' hK r₁ / (100 * γ)) * (100 * γ) = 20 * kahnD₀' hK r₁ :=
      div_mul_cancel₀ _ (ne_of_gt h100)
    have h3 := mul_le_mul_of_nonneg_right hn (le_of_lt h100)
    rw [h2] at h3
    linarith only [h3]
  -- ## The size of the parts
  have hF4 : ∀ᶠ n : ℕ in Filter.atTop,
      leftoverT (10 * Real.sqrt γ) * leftoverM (10 * Real.sqrt γ) (Dparam n ρ)
          ≤ D'param (Dparam n ρ) γ := by
    have hgsq' : 0 < (10 * Real.sqrt γ) ^ 2 := by positivity
    filter_upwards [hDbig ((10 + 2 * (10 * Real.sqrt γ)) / (10 * Real.sqrt γ) ^ 2)] with n hn
    have hD' : 10 + 2 * (10 * Real.sqrt γ) ≤ (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ) := by
      have h2 : ((10 + 2 * (10 * Real.sqrt γ)) / (10 * Real.sqrt γ) ^ 2) * (10 * Real.sqrt γ) ^ 2
          = 10 + 2 * (10 * Real.sqrt γ) := div_mul_cancel₀ _ (ne_of_gt hgsq')
      have h3 := mul_le_mul_of_nonneg_right hn (le_of_lt hgsq')
      rw [h2] at h3
      linarith only [h3]
    have hT : (leftoverT (10 * Real.sqrt γ) : ℝ) * (10 * Real.sqrt γ) ≤ 5 := by
      have h1 : (leftoverT (10 * Real.sqrt γ) : ℝ) ≤ 4 / (10 * Real.sqrt γ) + 1 := by
        rw [leftoverT, Nat.cast_max]
        refine max_le ?_ ?_
        · have h4 : (1 : ℝ) ≤ 4 / (10 * Real.sqrt γ) := by
            rw [le_div_iff₀ hg0]
            linarith only [hg1]
          linarith only [h4]
        · exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
      have h2 : 4 / (10 * Real.sqrt γ) + 1 ≤ 5 / (10 * Real.sqrt γ) := by
        have h3 : (1 : ℝ) ≤ 1 / (10 * Real.sqrt γ) := by
          rw [le_div_iff₀ hg0]
          linarith only [hg1]
        have h4 : 4 / (10 * Real.sqrt γ) + 1 / (10 * Real.sqrt γ)
            = 5 / (10 * Real.sqrt γ) := by
          rw [← add_div]; norm_num
        linarith only [h3, h4]
      calc (leftoverT (10 * Real.sqrt γ) : ℝ) * (10 * Real.sqrt γ)
          ≤ (5 / (10 * Real.sqrt γ)) * (10 * Real.sqrt γ) :=
            mul_le_mul_of_nonneg_right (le_trans h1 h2) (le_of_lt hg0)
        _ = 5 := by field_simp
    have hM : (leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℝ)
        ≤ (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ) / 10 + 1 := by
      rw [leftoverM]
      have h := Nat.ceil_lt_add_one
        (show (0 : ℝ) ≤ (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ) / 10 by positivity)
      linarith only [h]
    have hDp : (10 * Real.sqrt γ) * (Dparam n ρ : ℝ) - 1
        ≤ (D'param (Dparam n ρ) γ : ℝ) := by
      rw [D'param]
      have h := Nat.lt_floor_add_one (10 * Real.sqrt γ * (Dparam n ρ : ℝ))
      linarith only [h]
    have hkey : (leftoverT (10 * Real.sqrt γ) : ℝ)
          * (leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℝ) * (10 * Real.sqrt γ)
        ≤ ((10 * Real.sqrt γ) * (Dparam n ρ : ℝ) - 1) * (10 * Real.sqrt γ) := by
      have hstep1 : (leftoverT (10 * Real.sqrt γ) : ℝ)
            * (leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℝ) * (10 * Real.sqrt γ)
          ≤ 5 * (leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hT
          (Nat.cast_nonneg (leftoverM (10 * Real.sqrt γ) (Dparam n ρ)))
        nlinarith only [h]
      have hstep2 : 5 * (leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℝ)
          ≤ (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ) / 2 + 5 := by
        nlinarith only [hM]
      have hstep3 : (10 * Real.sqrt γ) ^ 2 * (Dparam n ρ : ℝ) / 2 + 5
          ≤ ((10 * Real.sqrt γ) * (Dparam n ρ : ℝ) - 1) * (10 * Real.sqrt γ) := by
        nlinarith only [hD', hgsq]
      linarith only [hstep1, hstep2, hstep3]
    have hfinal : (leftoverT (10 * Real.sqrt γ) : ℝ)
        * (leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℝ)
        ≤ (10 * Real.sqrt γ) * (Dparam n ρ : ℝ) - 1 :=
      le_of_mul_le_mul_right hkey hg0
    have hreal : ((leftoverT (10 * Real.sqrt γ)
        * leftoverM (10 * Real.sqrt γ) (Dparam n ρ) : ℕ) : ℝ)
        ≤ ((D'param (Dparam n ρ) γ : ℕ) : ℝ) := by
      push_cast
      linarith only [hfinal, hDp]
    exact_mod_cast hreal
  -- ## The Chernoff condition
  have hF5 : ∀ᶠ n : ℕ in Filter.atTop,
      ((D'param (Dparam n ρ) γ : ℕ) : ℝ) *
        (2 * Real.exp (-(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2) /
          (2 * (((max r₁ 2 : ℕ) : ℝ) * ((n : ℝ) / (leftoverT (10 * Real.sqrt γ) : ℝ) +
            (10 * Real.sqrt γ) * (n : ℝ) / 4 / 3))))) < 1 := by
    obtain ⟨Nexp, hNexp⟩ := Commons.Analysis.Real.exists_mul_exp_neg_lt_one
      (a := 2 * (10 * Real.sqrt γ)) (b := 0) (by positivity) le_rfl
      (c := 3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ))) (by positivity)
    have hexp : ∀ᶠ n : ℕ in Filter.atTop,
        (2 * (10 * Real.sqrt γ) * (n : ℝ) + 0) *
          Real.exp (-(3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ))) < 1 := by
      filter_upwards [Filter.eventually_ge_atTop Nexp] with n hn
      exact hNexp n hn
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
    filter_upwards [hexp, hF2, hDq, h1] with n hexpn hDn hDq h1n
    have hr0 : (0 : ℝ) < ((max r₁ 2 : ℕ) : ℝ) := by positivity
    have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h1n
    set X : ℝ := (n : ℝ) / (leftoverT (10 * Real.sqrt γ) : ℝ)
      + (10 * Real.sqrt γ) * (n : ℝ) / 4 / 3 with hX
    have hXle : X ≤ (10 * Real.sqrt γ) * (n : ℝ) / 3 := by
      have h := div_leftoverT_le hg0 n
      rw [hX]
      linarith only [h]
    have hX0 : 0 < X := by
      rw [hX]
      have h : (0 : ℝ) < (n : ℝ) / (leftoverT (10 * Real.sqrt γ) : ℝ) :=
        div_pos hn1 (by exact_mod_cast leftoverT_pos _)
      have h2 : 0 ≤ (10 * Real.sqrt γ) * (n : ℝ) / 4 / 3 := by positivity
      linarith only [h, h2]
    have hk : ((D'param (Dparam n ρ) γ : ℕ) : ℝ) ≤ (10 * Real.sqrt γ) * (n : ℝ) := by
      have h2 : ((D'param (Dparam n ρ) γ : ℕ) : ℝ) ≤ 10 * Real.sqrt γ * (Dparam n ρ : ℝ) := by
        rw [D'param]
        exact Nat.floor_le (by positivity)
      nlinarith only [h2, hDn, hg0]
    have hexp_le : Real.exp (-(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2) / (2 * (((max r₁ 2 : ℕ) : ℝ) * X)))
        ≤ Real.exp (-(3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hkey : 3 * X ≤ (10 * Real.sqrt γ) * (n : ℝ) := by linarith only [hXle]
      have hmain : 3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ)
          ≤ ((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2 / (2 * (((max r₁ 2 : ℕ) : ℝ) * X)) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (((max r₁ 2 : ℕ) : ℝ) * X))]
        have e1 : 3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ)
              * (2 * (((max r₁ 2 : ℕ) : ℝ) * X))
            = 3 * X * (10 * Real.sqrt γ) * (n : ℝ) / 16 := by
          field_simp
          ring
        rw [e1, div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
        have h6 : ((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2 * 16
            = ((10 * Real.sqrt γ) * (n : ℝ)) ^ 2 := by ring
        rw [h6]
        have h7 : 3 * X * (10 * Real.sqrt γ) * (n : ℝ)
            ≤ ((10 * Real.sqrt γ) * (n : ℝ)) ^ 2 := by
          have h8 := mul_le_mul_of_nonneg_right hkey
            (by positivity : (0 : ℝ) ≤ (10 * Real.sqrt γ) * (n : ℝ))
          nlinarith only [h8]
        exact h7
      have h1 : -(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2)
            / (2 * (((max r₁ 2 : ℕ) : ℝ) * X))
          = -(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2
            / (2 * (((max r₁ 2 : ℕ) : ℝ) * X))) := by
        rw [neg_div]
      rw [h1]
      exact neg_le_neg hmain
    have h2exp : 2 * Real.exp (-(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2) /
          (2 * (((max r₁ 2 : ℕ) : ℝ) * X)))
        ≤ 2 * Real.exp (-(3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    have hstep := mul_le_mul hk h2exp (by positivity)
      (by positivity : (0 : ℝ) ≤ (10 * Real.sqrt γ) * (n : ℝ))
    have hstep' : ((D'param (Dparam n ρ) γ : ℕ) : ℝ) *
        (2 * Real.exp (-(((10 * Real.sqrt γ) * (n : ℝ) / 4) ^ 2) /
          (2 * (((max r₁ 2 : ℕ) : ℝ) * X))))
        ≤ (2 * (10 * Real.sqrt γ) * (n : ℝ) + 0) *
          Real.exp (-(3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ))) := by
      have h2 : ((10 * Real.sqrt γ) * (n : ℝ))
          * (2 * Real.exp (-(3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ))))
          = (2 * (10 * Real.sqrt γ) * (n : ℝ) + 0)
            * Real.exp (-(3 * (10 * Real.sqrt γ) / (32 * ((max r₁ 2 : ℕ) : ℝ)) * (n : ℝ))) := by
        ring
      rw [h2] at hstep
      exact hstep
    exact lt_of_le_of_lt hstep' hexpn
  -- ## The `HugeMargins` bundle
  have hF6 : ∀ᶠ n : ℕ in Filter.atTop, HugeMargins n ρ_abs ε (10 * Real.sqrt γ) (1 / 2) ξ := by
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, 2000 ≤ (10 * Real.sqrt γ) * ρ_abs * (n : ℝ) := by
      have h2 := eventually_le_natCast (2000 / ((10 * Real.sqrt γ) * ρ_abs))
      filter_upwards [h2] with n hn
      have h3 : (0 : ℝ) < (10 * Real.sqrt γ) * ρ_abs := by positivity
      have h4 := mul_le_mul_of_nonneg_right hn (le_of_lt h3)
      rw [div_mul_cancel₀ _ (ne_of_gt h3)] at h4
      linarith only [h4]
    filter_upwards [h1] with n hn
    have hγε : 1000 * (10 * Real.sqrt γ) ≤ ρ_abs * ε := by
      have h2 : 1000 * (10 * Real.sqrt γ) = 10 ^ 4 * Real.sqrt γ := by ring
      rw [h2]; exact hsmall
    have hξle : 4000 * ξ ≤ 10 * Real.sqrt γ * ρ_abs := by
      have h2 : Real.sqrt γ * ρ_abs ≤ 10 * Real.sqrt γ * ρ_abs := by
        nlinarith only [hρabs0, hsqrt0]
      linarith only [hξsmall, h2]
    exact ⟨hρabs0, hρabs1, hε0, hg0, by norm_num, hξ0,
      by linarith only [hε1000], hγε, hn, hξle⟩
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hF1, hF2, hF3, hF4, hF5, hF6] with n hn4 hDn hkan hTm hcher hm
  exact ⟨hK, hn4, hDn, hkan, hTm, hcher, hm⟩

end

end ErdosFaberLovaszConjecture
