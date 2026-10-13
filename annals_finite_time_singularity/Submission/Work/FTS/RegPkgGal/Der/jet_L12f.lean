/-
# `Work.FTS.RegPkgGal.Der.jet_L12f` — `L₁₂^K` preserves the regularity jet of the profile

The operator of the fundamental model

  `L12f f z = FM.L12 f z = ∫_z^∞ ∫_0^{π/2} K(θ)·f(s,θ)/s dθ ds`   (`K(θ) = 3 sin θ cos²θ`)

is *radial* in its argument, so the family

  `(z, θ, τ) ↦ L12f (gSlice F τ) z`

only depends on `(z, τ)`.  The lemma says that this family again belongs to the regularity
jet `Jet α S N'` — a uniform bound and a joint `α`-Hölder modulus on `z ≥ 0`, `θ ∈ Iθ`,
`τ ∈ [0,S]` — whenever `F` does and, in addition:

* `|F z θ τ| ≤ Kl·z` near the axis (`hlin`), which kills the `1/s` singularity of the density
  at `s = 0⁺` (a bare `Jet` bound would only give `|dens| ≲ N/s`, which is not integrable);
* `F z θ τ = 0` for `s ≥ Lf` (`hsupp`), which kills the `1/s` tail at `s → ∞`;
* a *uniform in `z`* `τ`-modulus `|F z θ τ - F z θ τ'| ≤ Nt·z·|τ-τ'|^α` (`htau`), under which
  the factor `s` cancels in the density.

## The proof

Write `v τ s = L12dens K (gSlice F τ) s` and `u τ z = L12f (gSlice F τ) z = ∫_{s > z} v τ s`.

1. **The three density facts** — the pointwise bound `|v τ s| ≤ 6·max Kl N` for `s > 0` together
   with the support `v τ s = 0` for `s ≥ Lf` (`L12fDensBound`), the `τ`-modulus
   `|v τ s - v τ' s| ≤ 6·Nt·|τ - τ'|^α` (`L12fDensDiff`) and the continuity/integrability of the
   density on `(0,∞)` (`L12fDensContInt`).

2. **The tail integral collapses onto `(z, Lf]`**: since `v τ` vanishes beyond `Lf`,
   `u τ z = ∫_{(z, Lf]} v τ` (`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`; no
   integrability needed — unlike a comparison of *two* integrals).

3. **The three moduli**, all obtained from that identity with
   `norm_setIntegral_le_of_norm_le_const` and `volume.real (Ioc a b) = max (b - a) 0`:
   * `|u τ z| ≤ 6·max Kl N·Lf`;
   * `|u τ z - u τ z'| ≤ 6·max Kl N·|z - z'|` (via
     `setIntegral_union`, `Ioi z = Ioi z' ∪ Ioc z z'` for `z ≤ z'`, which is where the
     integrability of the density from step 1 is used);
   * `|u τ z - u τ' z| ≤ 6·Nt·Lf·|τ - τ'|^α` (`integral_sub`, then the same compact-support
     reduction).

4. **Assembly**: the Lipschitz bound together with the bound gives the `α`-modulus in `z`
   (`Lib.holder_of_lipschitz_of_bounded`), and the two moduli are amalgamated against the
   metric `|Δz| + |Δθ| + |Δτ|` by monotonicity of `t ↦ t^α`.  The constant is
   `N' = max 0 (max Cden (2·Cden·Lf) + 6·Nt·Lf)` with `Cden = 6·max Kl N`.

The hypothesis `hS : 0 < S` is not used (it only records that the time strip is nonempty).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic
import Submission.Work.FTS.RegPkgGal.Der.L12fDensBound
import Submission.Work.FTS.RegPkgGal.Der.L12fDensDiff
import Submission.Work.FTS.RegPkgGal.Der.L12fDensContInt
import Submission.Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The assembly -/

theorem jet_L12f {α S : ℝ} {F : ℝ → ℝ → ℝ → ℝ} {N Kl Lf Nt : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0)
    (htau : 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ici (0:ℝ), |F z θ τ - F z θ τ'| ≤ Nt * z * |τ - τ'| ^ α) :
    ∃ N' : ℝ, Work.FTS.Regularity.Jet α S N'
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z) := by
  have hN0 : 0 ≤ N := hJ.1
  have hKl0 : 0 ≤ Kl := hlin.1
  have hLfpos : 0 < Lf := hsupp.1
  have hNt0 : 0 ≤ Nt := htau.1
  let v : ℝ → ℝ → ℝ :=
    fun τ s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s
  obtain ⟨hDensLe, hDensZero⟩ :=
    L12fDensBound (α := α) (S := S) (N := N) (Kl := Kl) (Lf := Lf) hJ hlin hsupp
  have hDensDif : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
      |v τ s - v τ' s| ≤ 6 * Nt * |τ - τ'| ^ α :=
    L12fDensDiff (α := α) (S := S) (N := N) (Nt := Nt) hα hJ htau
  have hInt0 : ∀ τ ∈ Set.Icc 0 S, MeasureTheory.IntegrableOn (v τ) (Set.Ioi 0) :=
    fun τ hτ => (L12fDensContInt (α := α) (S := S) (N := N) (Kl := Kl) (Lf := Lf)
      hα hJ hlin hsupp τ hτ).2
  have hCden0 : 0 ≤ 6 * max Kl N := by
    have h1 : (0:ℝ) ≤ max Kl N := le_trans hN0 (le_max_right Kl N)
    linarith
  have hM0 : 0 ≤ (6 * max Kl N) * Lf := mul_nonneg hCden0 hLfpos.le
  have hCt0 : 0 ≤ (6 * Nt) * Lf := mul_nonneg (by linarith) hLfpos.le
  -- the tail integral is supported in `(z, Lf]`
  have htail : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ,
      Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        = ∫ s in Set.Ioc z Lf, v τ s := by
    intro τ hτ z
    have h1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        = ∫ s in Set.Ioi z, v τ s := rfl
    rw [h1]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self (fun x hx => ?_)
    have hxgt : Lf < x := by
      by_contra hcon
      exact hx.2 ⟨hx.1, le_of_not_gt hcon⟩
    exact hDensZero τ hτ x hxgt.le
  -- the `z`-Lipschitz bound (monotone case)
  have hzlip_le : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → z ≤ z' →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'|
      ≤ (6 * max Kl N) * |z' - z| := by
    intro τ hτ z z' hz hzz
    have hI1 : MeasureTheory.IntegrableOn (v τ) (Set.Ioi z') :=
      (hInt0 τ hτ).mono_set (Set.Ioi_subset_Ioi (le_trans hz hzz))
    have hI2 : MeasureTheory.IntegrableOn (v τ) (Set.Ioc z z') :=
      (hInt0 τ hτ).mono_set (fun x hx => lt_of_le_of_lt hz hx.1)
    have hU : Set.Ioi z = Set.Ioi z' ∪ Set.Ioc z z' := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hx
        rcases lt_or_ge z' x with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h)
        · exact lt_of_le_of_lt hzz h
        · exact h.1
    have hsplit : (∫ s in Set.Ioi z, v τ s)
        = (∫ s in Set.Ioi z', v τ s) + ∫ s in Set.Ioc z z', v τ s := by
      rw [hU]
      exact MeasureTheory.setIntegral_union
        (Set.disjoint_left.mpr (fun a ha ha' => absurd ha (not_lt.mpr ha'.2)))
        measurableSet_Ioc hI1 hI2
    have hdiff : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
        = ∫ s in Set.Ioc z z', v τ s := by
      have e1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          = ∫ s in Set.Ioi z, v τ s := rfl
      have e2 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
          = ∫ s in Set.Ioi z', v τ s := rfl
      rw [e1, e2, hsplit]
      ring
    rw [hdiff]
    have hb : |∫ s in Set.Ioc z z', v τ s| ≤ (6 * max Kl N) * |z' - z| := by
      rw [show (∫ s in Set.Ioc z z', v τ s) = ∫ s in z..z', v τ s from
        (intervalIntegral.integral_of_le hzz).symm]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s : ℝ => v τ s)
        (a := z) (b := z') (C := 6 * max Kl N) (by
          intro x hx
          rw [uIoc_of_le hzz] at hx
          have hxpos : 0 < x := lt_of_le_of_lt hz hx.1
          exact hDensLe τ hτ x hxpos)
    exact hb
  -- the `z`-Lipschitz bound (general case)
  have hzlip : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'|
      ≤ (6 * max Kl N) * |z - z'| := by
    intro τ hτ z z' hz hz'
    rcases le_total z z' with h | h
    · have hthis := hzlip_le τ hτ z z' hz h
      rw [abs_sub_comm z' z] at hthis
      exact hthis
    · have hthis := hzlip_le τ hτ z' z hz' h
      rw [abs_sub_comm (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z')
        (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z)] at hthis
      exact hthis
  -- the `τ`-Hölder bound
  have hthold : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
        - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z|
      ≤ (6 * Nt * Lf) * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ' z hz
    have h1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z
        = ∫ s in Set.Ioi z, (v τ s - v τ' s) := by
      have e1 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          = ∫ s in Set.Ioi z, v τ s := rfl
      have e2 : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z
          = ∫ s in Set.Ioi z, v τ' s := rfl
      rw [e1, e2]
      exact (MeasureTheory.integral_sub
        ((hInt0 τ hτ).mono_set (Set.Ioi_subset_Ioi hz))
        ((hInt0 τ' hτ').mono_set (Set.Ioi_subset_Ioi hz))).symm
    rw [h1]
    have h2 : (∫ s in Set.Ioi z, (v τ s - v τ' s))
        = ∫ s in Set.Ioc z Lf, (v τ s - v τ' s) := by
      refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Set.Ioc_subset_Ioi_self (fun x hx => ?_)
      have hxgt : Lf < x := by
        by_contra hcon
        exact hx.2 ⟨hx.1, le_of_not_gt hcon⟩
      have e1 : v τ x = 0 := hDensZero τ hτ x hxgt.le
      have e2 : v τ' x = 0 := hDensZero τ' hτ' x hxgt.le
      rw [e1, e2, sub_zero]
    rw [h2]
    have hb : |∫ s in Set.Ioc z Lf, (v τ s - v τ' s)|
        ≤ (6 * Nt * |τ - τ'| ^ α) * MeasureTheory.volume.real (Set.Ioc z Lf) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (s := Set.Ioc z Lf) (f := fun s : ℝ => v τ s - v τ' s)
        (C := 6 * Nt * |τ - τ'| ^ α)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        (fun x hx => by
          have hxpos : 0 < x := lt_of_le_of_lt hz hx.1
          exact hDensDif τ hτ τ' hτ' x hxpos)
    have hLfm : MeasureTheory.volume.real (Set.Ioc z Lf) ≤ Lf := by
      rw [Real.volume_real_Ioc]
      exact max_le (by linarith) hLfpos.le
    have hnn : (0:ℝ) ≤ 6 * Nt * |τ - τ'| ^ α :=
      mul_nonneg (mul_nonneg (by norm_num) hNt0) (Real.rpow_nonneg (abs_nonneg _) α)
    calc |∫ s in Set.Ioc z Lf, (v τ s - v τ' s)|
        ≤ (6 * Nt * |τ - τ'| ^ α) * MeasureTheory.volume.real (Set.Ioc z Lf) := hb
      _ ≤ (6 * Nt * |τ - τ'| ^ α) * Lf := mul_le_mul_of_nonneg_left hLfm hnn
      _ = (6 * Nt * Lf) * |τ - τ'| ^ α := by ring
  -- the pointwise bound
  have hbound : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z| ≤ (6 * max Kl N) * Lf := by
    intro τ hτ z hz
    rw [htail τ hτ z]
    have hb : |∫ s in Set.Ioc z Lf, v τ s|
        ≤ (6 * max Kl N) * MeasureTheory.volume.real (Set.Ioc z Lf) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (s := Set.Ioc z Lf) (f := fun s : ℝ => v τ s) (C := 6 * max Kl N)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        (fun x hx => by
          have hxpos : 0 < x := lt_of_le_of_lt hz hx.1
          exact hDensLe τ hτ x hxpos)
    have hLfm : MeasureTheory.volume.real (Set.Ioc z Lf) ≤ Lf := by
      rw [Real.volume_real_Ioc]
      exact max_le (by linarith) hLfpos.le
    calc |∫ s in Set.Ioc z Lf, v τ s|
        ≤ (6 * max Kl N) * MeasureTheory.volume.real (Set.Ioc z Lf) := hb
      _ ≤ (6 * max Kl N) * Lf := mul_le_mul_of_nonneg_left hLfm hCden0
  refine ⟨max 0 (max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf)), ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · intro z θ τ hz hθ hτ
    have h1 : (6 * max Kl N) * Lf ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) :=
      le_trans (le_mul_of_one_le_left hM0 (by norm_num)) (le_max_right _ _)
    have h2 : max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf))
        ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf) :=
      le_add_of_nonneg_right hCt0
    refine le_trans (hbound τ hτ z hz) ?_
    refine le_trans h1 ?_
    refine le_trans h2 ?_
    exact le_max_right _ _
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    set D := |z - z'| + |θ - θ'| + |τ - τ'| with hDdef
    have hD0 : 0 ≤ D := by rw [hDdef]; positivity
    have hzD : |z - z'| ^ α ≤ D ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by rw [hDdef]; linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
    have htD : |τ - τ'| ^ α ≤ D ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by rw [hDdef]; linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
    have h1 : |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'|
        ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * |z - z'| ^ α :=
      Lib.holder_of_lipschitz_of_bounded hα hα1 hCden0 hM0 (hzlip τ hτ) (hbound τ hτ) z z' hz hz'
    have h2 : |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z'|
        ≤ (6 * Nt * Lf) * |τ - τ'| ^ α := hthold τ hτ τ' hτ' z' hz'
    have hsplit : Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
          - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z'
        = (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z
            - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z')
          + (Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ) z'
            - Work.Coercivity.L12f (Work.FTS.Regularity.gSlice F τ') z') := by ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add h1 h2) ?_
    have hA0 : 0 ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) :=
      le_trans hCden0 (le_max_left _ _)
    have hsum : max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * |z - z'| ^ α
          + (6 * Nt * Lf) * |τ - τ'| ^ α
        ≤ (max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf)) * D ^ α := by
      have h3 : max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * |z - z'| ^ α
          ≤ max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * D ^ α :=
        mul_le_mul_of_nonneg_left hzD hA0
      have h4 : (6 * Nt * Lf) * |τ - τ'| ^ α ≤ (6 * Nt * Lf) * D ^ α :=
        mul_le_mul_of_nonneg_left htD hCt0
      have h5 : (max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) + (6 * Nt * Lf)) * D ^ α
          = max (6 * max Kl N) (2 * ((6 * max Kl N) * Lf)) * D ^ α
            + (6 * Nt * Lf) * D ^ α := by ring
      linarith [h3, h4, h5]
    refine le_trans hsum ?_
    refine mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hD0 α)

end Work.FTS.RegPkgGal.Der
