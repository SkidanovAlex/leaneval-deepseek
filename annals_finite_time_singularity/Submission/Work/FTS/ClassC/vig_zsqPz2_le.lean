/-
Copyright: work module for the Elgindi finite-time singularity project.

# `vig_zsqPz2_le` — the vanishing-weight slot of the smoothing family `z²∂_z²Ψ`

The reduction `HkMem_of_pure_and_vanishing` needs, for the smoothing family
`f = fun z θ => z ^ 2 * pzIter 2 Ψ z θ` of a `C^∞` datum `Ψ` on the open quadrant, the
pointwise domination

```
vig α f r j z θ ≤ 4 * vanGrid α Ψ z θ      (1 ≤ r, r + j ≤ 7, z > 0, θ ∈ (0,π/2))
```

of every *vanishing-weight* slot of `f` by the grid majorant `vanGrid` built from the plain
family of `Ψ` (the singular `HkIntegrand α 0`-slots of angular order `≤ 2` and the vanishing
slots `hVint` of angular order `3 ≤ t ≤ 9`).

The mathematics is the operator identity

```
D_z^j ∂_θ^r (z²∂_z²Ψ) = z²∂_z² (D_z^j ∂_θ^r Ψ) = D_z^{j+2}(∂_θ^r Ψ) − D_z^{j+1}(∂_θ^r Ψ)
```

on the open quadrant (`∂_θ` commutes with the `z`-only factor `z²` and with `z²∂_z²` by
Clairaut; `z²∂_z² = D_z² − D_z`), together with the elementary AM–GM
`((x − y)·w)² ≤ 2(xw)² + 2(yw)²`.  The two slots `D_z^{j+1}(∂_θ^rΨ)`, `D_z^{j+2}(∂_θ^rΨ)`
have radial order `≤ 9`, so each is a summand of `vanGrid`: for `r ≤ 2` through
`HkIntegrand α 0` (the singular weight `σ = sin(2θ)^{-η}` dominates the vanishing weight
`sin(2θ)^{2r-γ}`, since `2r - γ ≥ 2 - 3/2 > -η`), and for `r ≥ 3` through `hVint` (whose
weight `sin(2θ)^{2r-4-γ}` dominates `sin(2θ)^{2r-γ}` because `sin(2θ) ≤ 1` and the exponents
are non-negative).  The constant `4 = 2·2` is exactly the AM–GM loss.

Everything here is `sorry`-free.
-/
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

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Membership of the single slots in the grid majorant -/

/-- The `HkIntegrand α 0`-slot of angular order `r ≤ 2` and radial order `l ≤ 9` is a summand
of `vanGrid`. -/
theorem hkIntegrand_le_vanGrid {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {r l : ℕ}
    (hr : r ≤ 2) (hl : l ≤ 9) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ)) z θ
        ≤ vanGrid α Ψ z θ := by
  intro z θ hθ
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hmem_l : l ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hmem_r : r ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
  have hinner : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ)) z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0
        (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ) hmem_r
  have hmid : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l' ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (fun l' _ => Finset.sum_nonneg fun m _ => Work.Spaces.HkIntegrand_nonneg α 0
        (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ) hmem_l
  have htail : 0 ≤ ∑ t ∈ Finset.Icc 3 9, ∑ l' ∈ Finset.range 10, hVint α Ψ t l' z θ :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l' _ => by
      simp only [hVint]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  rw [vanGrid]
  linarith

/-- The `hVint`-slot of angular order `3 ≤ r ≤ 9` and radial order `l ≤ 9` is a summand of
`vanGrid`. -/
theorem hVint_le_vanGrid {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {r l : ℕ}
    (hr3 : 3 ≤ r) (hr9 : r ≤ 9) (hl : l ≤ 9) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      hVint α Ψ r l z θ ≤ vanGrid α Ψ z θ := by
  intro z θ hθ
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hmem_t : r ∈ Finset.Icc 3 9 := Finset.mem_Icc.mpr ⟨hr3, hr9⟩
  have hmem_l : l ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have hinner : hVint α Ψ r l z θ ≤ ∑ l' ∈ Finset.range 10, hVint α Ψ r l' z θ :=
    Finset.single_le_sum (f := fun l' => hVint α Ψ r l' z θ)
      (fun l' _ => by
        simp only [hVint]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)) hmem_l
  have hmid : (∑ l' ∈ Finset.range 10, hVint α Ψ r l' z θ)
      ≤ ∑ t ∈ Finset.Icc 3 9, ∑ l' ∈ Finset.range 10, hVint α Ψ t l' z θ :=
    Finset.single_le_sum
      (f := fun t => ∑ l' ∈ Finset.range 10, hVint α Ψ t l' z θ)
      (fun t _ => Finset.sum_nonneg fun l' _ => by
        simp only [hVint]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)) hmem_t
  have hhead : 0 ≤ ∑ l' ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.sum_nonneg fun l' _ => Finset.sum_nonneg fun m _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ
  rw [vanGrid]
  linarith

/-! ## The domination of a single plain angular slot -/

/-- **A single plain slot of the smoothing family is dominated by the grid.** For `1 ≤ r ≤ 7`
and radial order `l ≤ 9`, the vanishing-weight slot `(D_z^l ∂_θ^r Ψ · w)² · sin(2θ)^{2r-γ}`
is at most `vanGrid α Ψ`. -/
theorem vig_slot_le_vanGrid {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2) (Ψ : ℝ → ℝ → ℝ) :
    ∀ r l : ℕ, 1 ≤ r → r ≤ 7 → l ≤ 9 → ∀ z θ : ℝ,
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ) z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)
        ≤ vanGrid α Ψ z θ := by
  intro r l hr hr7 hl z θ hθ
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  by_cases hr2 : r ≤ 2
  · -- `r ≤ 2`: the singular `ℋ^0`-integrand dominates the vanishing weight
    refine le_trans (sq_mul_sin_le_HkIntegrand_zero α _ hθ ?_)
      (hkIntegrand_le_vanGrid hr2 hl z θ hθ)
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have heta : Work.Spaces.eta = 99 / 100 := rfl
    rw [heta]
    linarith
  · -- `r ≥ 3`: the grid's own vanishing slot has the smaller exponent `2r - 4 - γ`
    have hr3 : 3 ≤ r := by omega
    refine le_trans (sq_mul_sin_le_sq_mul_sin hθ ?_ ?_)
      (hVint_le_vanGrid hr3 (by omega) hl z θ hθ)
    · have hr3' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
      linarith
    · linarith

/-! ## The operator identity -/

/-- **The operator identity.** On the open quadrant, the `D_z^j ∂_θ^r`-slot of the smoothing
family `z²∂_z²Ψ` is the difference of the two shifted radial slots of `∂_θ^rΨ`:
`D_z^j∂_θ^r(z²∂_z²Ψ) = D_z^{j+2}(∂_θ^rΨ) − D_z^{j+1}(∂_θ^rΨ)`. -/
theorem vig_DzIter_pthIter_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (r j : ℕ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DzIter j
          (Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        = Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
          - Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ := by
  intro z θ hz hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hH : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter r Ψ) :=
    SmoothOpen_pthIter_classC hΨ r
  have hC : Work.Spaces.DzIter j
        (Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ) z θ :=
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (G := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ)
      (fun z' θ' hz' hθ' hπ' => by
        rw [congrFun (congrFun (seven_pthIter_zsq_mul r (Work.Spaces.pzIter 2 Ψ)) z') θ',
          seven_pzIter_two_pthIter_eqOn_Q0 hΨ r z' θ' hz' hθ' hπ'])
      j z θ hz hθ0 hθ1
  have hD : Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ :=
    NormPiecesAux.zsqPz2_DzIter_eqOn (Work.Spaces.pthIter r Ψ) hH j z θ hz hθ0 hθ1
  have hE : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ :=
    seven_zsq_pzIter_two_eq (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) (hH.DzIter j)
      z θ hz hθ0 hθ1
  have e2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ))
      = Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) := by
    rw [← seven_DzIter_add 2 j (Work.Spaces.pthIter r Ψ)]
    exact congrArg (fun n => Work.Spaces.DzIter n (Work.Spaces.pthIter r Ψ)) (by omega)
  have e1 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ))
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) := by
    rw [← seven_DzIter_add 1 j (Work.Spaces.pthIter r Ψ)]
    exact congrArg (fun n => Work.Spaces.DzIter n (Work.Spaces.pthIter r Ψ)) (by omega)
  rw [hC, hD, hE, e2, e1]

/-! ## The target -/

theorem vig_zsqPz2_le {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ 7 → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r j z θ
        ≤ 4 * Work.FTS.ClassC.vanGrid α Ψ z θ := by
  intro j r hr hrj z hz θ hθ
  have hj2 : j + 2 ≤ 9 := by omega
  have hj1 : j + 1 ≤ 9 := by omega
  have hid := vig_DzIter_pthIter_eq hΨ r j z θ hz hθ
  have hsq := seven_sq_sub_mul_sq_le
    (Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ)
    (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ) (Work.Spaces.w z)
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
    Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) _
  have hA := vig_slot_le_vanGrid hγ Ψ r (j + 2) hr (by omega) hj2 z θ hθ
  have hB := vig_slot_le_vanGrid hγ Ψ r (j + 1) hr (by omega) hj1 z θ hθ
  rw [vig, hid]
  calc ((Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
          - Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ)
        * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)
      ≤ (2 * (Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
          + 2 * (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_right hsq hsnn
    _ = 2 * ((Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)) := by ring
    _ ≤ 4 * vanGrid α Ψ z θ := by linarith

end Work.FTS.ClassC
