import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Cube.Loc.subsectorSupp_slice_snd
import Submission.Work.BoseFixB1B.tBamp_amplitude_box_fubini
import Submission.Work.BoseFixB1B.tBwordKinInd_eq_zero_of_boxQInd_ae_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibreSplit` — the **kinetic slot** of the Step-Loc
# fibre formula, with the `p`-integrability of the fibre slots supplied by `hint`

The target (statement frozen by the requester) is the fibre identity for the FS-faithful windowed
`p`-diagonal kinetic form `Work.UBBInputs8.tBdiagFormInd`:

    tBdiagFormInd a A V χ F Φ
      = ∫ y in Dloc m a A, tBdiagFormInd a A V χ F (fibre k m Φ y)      (T)

for a `(k+m)`-particle state `Φ` supported a.e. on the sub-sector in which the first `k`
coordinates lie in `A` and the last `m` coordinates avoid `A` (`SubsectorSupp`), with `A ⊆ acube a`
measurable, the window `χ` continuous, compactly supported and supported in `A`, and `F ≥ 0`
measurable.  The hypothesis `hint` is the `p`-integrability of the *whole* slot integrand
`F‖p‖·(a³)⁻¹∫_{abox N a}‖tBamp χ p (Q_{A,i}Ψ) i x‖²` for every `N` and every smooth `Ψ`; it is
exactly the input that makes the `p ↔ y` Fubini exchange honest (the `p`-integral of a non-integrable
nonnegative integrand is Mathlib's junk value `0`, so an *integrability* hypothesis is needed).

## The proof, in five steps

1. **Slot split.**  `tBdiagFormInd` is a sum over the `k+m` slots; `Fin.sum_univ_add` splits it
   into the `k` in-box slots (`Fin.castAdd`) and the `m` out-of-box slots (`Fin.natAdd`).
2. **The `m` out-of-box slots vanish.**  `SubsectorSupp` gives that `Φ` vanishes a.e. on the tube
   `{x | x i ∈ A}` for `i = Fin.natAdd k j`, whence `boxQInd V A i Φ =ᵐ 0` on the box
   (`boxQInd_ae_eq_zero_of_tube`, whose core is the a.e.-slice lemma
   `Work.FibreWord.ae_eq_slice_set`, so no measurability of the slice map is needed), whence the
   slot integrand is `0` a.e. (`Work.BoseFixB1B.tBamp_integral_sq_eq_zero_of_ae_eq_zero`).
3. **The `k` in-box slots become the fibre slots.**  For each `j : Fin k` the pointwise-in-`p`
   block Fubini `Work.BoseFixB1B.tBamp_amplitude_box_fubini` (whose `IntegrableOn` hypothesis is
   `ampSqIntegrableOn_aux`, a boundedness bound for the box projection and its amplitude) writes the
   slot-`x` integral as `∫_w ∫_u ‖tBamp χ p (Q_{A,j}(fibre w Φ)) j u‖²`.  The exchange of the `p`-
   and `w`-integrals is then `MeasureTheory.integral_integral_swap`, with joint integrability from
   `MeasureTheory.integrable_prod_iff`: the `w`-integrability of the slices from the uniform
   amplitude bound (again `ampSqIntegrableOn_aux`'s ingredients) and the `p`-integrability of the
   `w`-integrated slot from `hint` applied to `Φ` (this is where the block Fubini is used a second
   time, in the reverse direction).
4. **Sum over the fibered slots.**  `MeasureTheory.integral_finsetSum` moves the finite sum over
   `j : Fin k` inside the `w`-integral, which is definitionally the RHS at the fibre state
   (`fibreSlot`, `sum_fibreSlot_eq_tBdiagFormInd`).
5. **The domain reduction `abox m a → Dloc m a A`.**  For a.e. `w ∈ abox m a` with some slot
   `w ℓ ∈ A`, `SubsectorSupp` makes the fibre state vanish a.e. on `abox k a`, so
   `tBdiagFormInd … (fibre k m Φ w) = 0` (`tBdiagFormInd_eq_zero_of_ae_eq_zero`); the two set
   integrals therefore agree (indicator argument).

## Status of the two side lemmas

`ampSqIntegrableOn_aux` and `fibreAmpAEMeasurable_aux` are the local copies of the two statements
delegated this session to `Submission/Work/BoseFixB1/Cube/Loc/ampSqIntegrableOn.lean` and
`…/fibreAmpAEMeasurable.lean` (same statements, same namespace).  This file is **self-contained**:
it does not import those modules, so it is insensitive to their state.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1.Cube.Loc

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-! ## 1. The amplitude bound -/

theorem norm_tBamp_le_of_boundedOn {N : ℕ} {a : ℝ} {A : Set E3}
    (hAc : A ⊆ acube a) {χ : E3 → ℝ} (hχint : Integrable (fun z : E3 => |χ z|))
    (hχA : ∀ z, z ∉ A → χ z = 0)
    {Ψ : X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y ∈ abox N a, |Ψ y| ≤ B)
    (i : Fin N) (p : E3) {x : X N} (hx : x ∈ abox N a) :
    ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ≤ B * ∫ z : E3, |χ z| := by
  have hint : Integrable (fun z : E3 => |χ z| * B) := hχint.mul_const B
  have hexp : ∀ z : E3, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    intro z
    rw [Complex.norm_exp]
    simp
  have hpt : ∀ z : E3,
      ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Ψ (Function.update x i z) : ℂ)‖ ≤ |χ z| * B := by
    intro z
    simp only [norm_mul, hexp z, mul_one, Complex.norm_real, Real.norm_eq_abs]
    by_cases hz : χ z = 0
    · rw [hz]; simp
    · have hzA : z ∈ acube a := hAc (by_contra fun h => hz (hχA z h))
      have hmem : Function.update x i z ∈ abox N a := by
        rw [mem_abox_iff] at hx ⊢
        intro j
        rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj]; exact hzA
        · rw [if_neg hj]; exact hx j
      exact mul_le_mul_of_nonneg_left (hb _ hmem) (abs_nonneg _)
  calc ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
      = ‖∫ z, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)‖ := by simp only [Work.SmallBoxTBWord.tBamp]
    _ ≤ ∫ z, ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, |χ z| * B :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = B * ∫ z, |χ z| := by rw [integral_mul_const]; ring

/-! ## 2. The projected state of a fibre is bounded on the box -/

theorem abs_boxQInd_fibre_le {k m : ℕ} {a V : ℝ} {A : Set E3}
    (hAc : A ⊆ acube a) {Φ : X (k + m) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hfin : (volume : Measure E3) A < ⊤)
    (hΦb : ∀ x ∈ abox (k + m) a, |Φ x| ≤ C)
    {w : X m} (hw : w ∈ abox m a) (j : Fin k) {u : X k} (hu : u ∈ abox k a) :
    |Work.UBBInputs8.boxQInd V A j (fibre k m Φ w) u|
      ≤ C + |V|⁻¹ * (C * (volume : Measure E3).real A) := by
  have hmem : ∀ z ∈ A, Function.update u j z ∈ abox k a := by
    intro z hz
    rw [mem_abox_iff] at hu ⊢
    intro i
    rw [Function.update_apply]
    by_cases hi : i = j
    · rw [if_pos hi]; exact hAc hz
    · rw [if_neg hi]; exact hu i
  have hmerge : ∀ z ∈ A, mergeBlock k m (Function.update u j z, w) ∈ abox (k + m) a :=
    fun z hz => Work.BoseFixB1B.cns_split_mergeBlock_mem_abox (hmem z hz) hw
  have hfib : ∀ z ∈ A, |fibre k m Φ w (Function.update u j z)| ≤ C := by
    intro z hz
    have h := hΦb _ (hmerge z hz)
    simpa only [fibre, mkSlot_eq_mergeBlock] using h
  have hInt : |∫ z in A, (fibre k m Φ w) (Function.update u j z)|
      ≤ C * (volume : Measure E3).real A := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3))
      (f := fun z : E3 => (fibre k m Φ w) (Function.update u j z)) (C := C) hfin
      (fun z hz => by simpa only [Real.norm_eq_abs] using hfib z hz)
    simpa only [Real.norm_eq_abs] using h
  have hreal : 0 ≤ (volume : Measure E3).real A := measureReal_nonneg
  have hRHS : 0 ≤ C + |V|⁻¹ * (C * (volume : Measure E3).real A) :=
    add_nonneg hC (mul_nonneg (inv_nonneg.mpr (abs_nonneg V)) (mul_nonneg hC hreal))
  have huA : u ∈ abox k a := hu
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases huj : u j ∈ A
  · have h1 : A.indicator (fun _ => (1 : ℝ)) (u j) = 1 := Set.indicator_of_mem huj _
    rw [h1, one_mul, mul_one]
    have h2 : |fibre k m Φ w u| ≤ C := by
      have h := hΦb _ (Work.BoseFixB1B.cns_split_mergeBlock_mem_abox huA hw)
      simpa only [fibre, mkSlot_eq_mergeBlock] using h
    have h3 : |(1 : ℝ) / V| = |V|⁻¹ := by rw [one_div, abs_inv]
    calc |fibre k m Φ w u - 1 / V * (∫ z in A, (fibre k m Φ w) (Function.update u j z))|
        ≤ |fibre k m Φ w u|
          + |1 / V * (∫ z in A, (fibre k m Φ w) (Function.update u j z))| := by
          simpa [sub_eq_add_neg] using abs_add_le (fibre k m Φ w u)
            (-(1 / V * (∫ z in A, (fibre k m Φ w) (Function.update u j z))))
      _ = |fibre k m Φ w u|
          + |V|⁻¹ * |∫ z in A, (fibre k m Φ w) (Function.update u j z)| := by
          rw [abs_mul, h3]
      _ ≤ C + |V|⁻¹ * (C * (volume : Measure E3).real A) :=
          add_le_add h2 (mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr (abs_nonneg V)))
  · have h1 : A.indicator (fun _ => (1 : ℝ)) (u j) = 0 := Set.indicator_of_notMem huj _
    rw [h1, zero_mul, mul_zero, sub_zero, abs_zero]
    exact hRHS

/-! ## 3. The a.e. vanishing of the box projection on a tube -/

theorem boxQInd_ae_eq_zero_of_tube {N : ℕ} {a V : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube a) (i : Fin N) {Ψ : X N → ℝ}
    (hΨ : ∀ᵐ x ∂((volume : Measure (X N)).restrict (abox N a)), x i ∈ A → Ψ x = 0) :
    Work.UBBInputs8.boxQInd V A i Ψ
      =ᵐ[((volume : Measure (X N)).restrict (abox N a))] 0 := by
  classical
  set μB : Measure (X N) := (volume : Measure (X N)).restrict (abox N a) with hμB
  have hnull : μB {x : X N | x i ∈ A ∧ Ψ x ≠ 0} = 0 := by
    refine measure_mono_null (fun x hx => ?_) ((MeasureTheory.ae_iff).mp hΨ)
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro h
    exact hx.2 (h hx.1)
  have hnull' : (volume : Measure (X N)) ({x : X N | x i ∈ A ∧ Ψ x ≠ 0} ∩ abox N a) = 0 := by
    rw [← Measure.restrict_apply' (abox_measurable N a)]
    exact hnull
  -- the indicator term
  have h1 : (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) =ᵐ[μB] 0 := by
    refine (MeasureTheory.ae_iff).mpr ?_
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at hx ⊢
    by_cases hxin : x i ∈ A
    · refine ⟨hxin, fun hΨ0 => hx ?_⟩
      rw [Set.indicator_of_mem hxin, one_mul, hΨ0]
    · rw [Set.indicator_of_notMem hxin, zero_mul] at hx
      exact absurd rfl hx
  -- the mean term
  set Q : X N → ℝ :=
    (abox N a).indicator (fun y => A.indicator (fun _ => (1 : ℝ)) (y i) * Ψ y) with hQ
  have hQae : Q =ᵐ[(volume : Measure (X N))] 0 := by
    refine (MeasureTheory.ae_iff).mpr ?_
    refine measure_mono_null (fun x hx => ?_) hnull'
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at hx ⊢
    have hxab : x ∈ abox N a := by
      by_contra h
      rw [hQ, Set.indicator_of_notMem h] at hx
      exact hx rfl
    refine ⟨?_, hxab⟩
    rw [hQ, Set.indicator_of_mem hxab] at hx
    by_cases hxin : x i ∈ A
    · refine ⟨hxin, fun hΨ0 => hx ?_⟩
      rw [Set.indicator_of_mem hxin, one_mul, hΨ0]
    · rw [Set.indicator_of_notMem hxin, zero_mul] at hx
      exact absurd rfl hx
  have hslice : (fun x : X N => ∫ z in A, Q (Function.update x i z)) =ᵐ[μB] 0 := by
    have h0 := Work.FibreWord.ae_eq_slice_set (n := N) i A hQae
    have h0' : (fun x : X N => ∫ z in A, Q (Function.update x i z)) =ᵐ[volume] (0 : X N → ℝ) := by
      refine h0.trans ?_
      filter_upwards with x
      simp only [Pi.zero_apply]
      rw [MeasureTheory.integral_zero]
    exact h0'.filter_mono (MeasureTheory.ae_mono (Measure.restrict_le_self))
  have hident : ∀ x ∈ abox N a,
      (∫ z in A, Q (Function.update x i z)) = ∫ z in A, Ψ (Function.update x i z) := by
    intro x hx
    refine MeasureTheory.setIntegral_congr_fun hA (fun z hz => ?_)
    rw [hQ, Set.indicator_of_mem (by
      rw [mem_abox_iff] at hx ⊢
      intro j
      rw [Function.update_apply]
      by_cases hj : j = i
      · rw [if_pos hj]; exact hAc hz
      · rw [if_neg hj]; exact hx j)]
    rw [Function.update_self]
    by_cases hzA : z ∈ A
    · rw [Set.indicator_of_mem hzA, one_mul]
    · exact absurd hz hzA
  have h2 : (fun x : X N => (1 / V) * (∫ z in A, Ψ (Function.update x i z))
      * A.indicator (fun _ => (1 : ℝ)) (x i)) =ᵐ[μB] 0 := by
    have hslice' : (fun x : X N => (∫ z in A, Ψ (Function.update x i z))) =ᵐ[μB] 0 := by
      filter_upwards [hslice, self_mem_ae_restrict (abox_measurable N a)] with x hx hxab
      rw [← hident x hxab]
      exact hx
    filter_upwards [hslice'] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    simp [hx]
  have hbox : Work.UBBInputs8.boxQInd V A i Ψ
      = (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x)
        - (fun x : X N => (1 / V) * (∫ z in A, Ψ (Function.update x i z))
            * A.indicator (fun _ => (1 : ℝ)) (x i)) := by
    funext x
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Pi.sub_apply]
  rw [hbox]
  simpa using h1.sub h2

/-! ## 4. `tBdiagFormInd` of an a.e.-vanishing projected state -/

theorem tBdiagFormInd_eq_zero_of_boxQInd_ae_eq_zero {N : ℕ} {a V : ℝ} {A : Set E3}
    {χ : E3 → ℝ} {F : ℝ → ℝ} {Ψ : X N → ℝ}
    (hAc : A ⊆ acube a) (hχA : ∀ z, z ∉ A → χ z = 0)
    (hbox : ∀ i : Fin N, Work.UBBInputs8.boxQInd V A i Ψ
      =ᵐ[((volume : Measure (X N)).restrict (abox N a))] 0) :
    Work.UBBInputs8.tBdiagFormInd a A V χ F Ψ = 0 := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hinner : (fun p : E3 => F ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in abox N a, ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2))
      = fun _ => 0 := by
    funext p
    rw [Work.BoseFixB1B.tBamp_integral_sq_eq_zero_of_ae_eq_zero (i := i) p hAc hχA (hbox i)]
    ring
  rw [hinner]
  simp

theorem tBdiagFormInd_eq_zero_of_ae_eq_zero {N : ℕ} {a V : ℝ} {A : Set E3}
    {χ : E3 → ℝ} {F : ℝ → ℝ} {Ψ : X N → ℝ}
    (hA : MeasurableSet A) (hAc : A ⊆ acube a) (hχA : ∀ z, z ∉ A → χ z = 0)
    (hΨ : Ψ =ᵐ[((volume : Measure (X N)).restrict (abox N a))] 0) :
    Work.UBBInputs8.tBdiagFormInd a A V χ F Ψ = 0 :=
  tBdiagFormInd_eq_zero_of_boxQInd_ae_eq_zero (N := N) (a := a) (V := V) (A := A)
    (χ := χ) (F := F) hAc hχA
    (fun i => boxQInd_ae_eq_zero_of_tube (N := N) (a := a) (V := V) (A := A) hA hAc i
      (hΨ.mono (fun x hx _ => hx)))



/-! ## 5. Local copies of the two delegated side lemmas -/

theorem ampSqIntegrableOn_aux {N : ℕ} {a V : ℝ} (ha : 0 < a) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube a)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχA : ∀ z, z ∉ A → χ z = 0) {Ψ : X N → ℝ} (hΨm : Measurable Ψ) {C : ℝ} (hC : 0 ≤ C)
    (hΨb : ∀ x ∈ abox N a, |Ψ x| ≤ C) (i : Fin N) (p : E3) :
    IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2) (abox N a) := by
  have hAfin : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)
  have hχint : Integrable (fun z : E3 => |χ z|) :=
    (hχc.integrable_of_hasCompactSupport hχs).abs
  have hK : ∀ x : X N, (∀ j : Fin N, x j ∈ acube a) →
      |Work.UBBInputs8.boxQInd V A i Ψ x| ≤ C + |V|⁻¹ * (C * (volume : Measure E3).real A) :=
    Work.SlotWord.abs_boxQInd_le_of_bound a hAc hC hAfin (fun x hx => hΨb x hx) i
  have hK0 : 0 ≤ C + |V|⁻¹ * (C * (volume : Measure E3).real A) :=
    add_nonneg hC (mul_nonneg (inv_nonneg.mpr (abs_nonneg V)) (mul_nonneg hC measureReal_nonneg))
  have hbamp : ∀ x ∈ abox N a, ‖Work.SmallBoxTBWord.tBamp χ p
      (Work.UBBInputs8.boxQInd V A i Ψ) i x‖
      ≤ (C + |V|⁻¹ * (C * (volume : Measure E3).real A)) * ∫ z : E3, |χ z| :=
    fun x hx => norm_tBamp_le_of_boundedOn (a := a) hAc hχint hχA hK0
      (fun y hy => hK y ((mem_abox_iff N a y).mp hy)) i p hx
  have hmeas : Measurable (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2) := by
    have hpair : Measurable (fun x : X N => ((p, x) : E3 × X N)) :=
      Measurable.prodMk (measurable_const (a := p)) (measurable_id (α := X N))
    simpa only [Function.comp_def] using
      (Work.BoseFixB1.measurable_tBamp_boxQInd_pair (n := N) (A := A) (volA := V)
        (Ψ := Ψ) hA hχc hΨm i).comp hpair
  refine IntegrableOn.of_bound (abox_lt_top N a ha.le) hmeas.aestronglyMeasurable
    (((C + |V|⁻¹ * (C * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (abox_measurable N a)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbamp x hx) 2

theorem fibreAmpAEMeasurable_aux {k m : ℕ} {a V : ℝ} {A : Set E3} (hA : MeasurableSet A)
    {χ : E3 → ℝ} (hχc : Continuous χ) {Φ : X (k + m) → ℝ} (hΦm : Measurable Φ) (j : Fin k) :
    AEStronglyMeasurable
      (fun q : E3 × X m => ∫ z in abox k a,
        ‖Work.SmallBoxTBWord.tBamp χ q.1
          (Work.UBBInputs8.boxQInd V A j (fibre k m Φ q.2)) j z‖ ^ 2)
      ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) := by
  have hslot : Measurable (fun p : X m × X k => fibre k m Φ p.1 p.2) := by
    have h1 : Measurable (fun p : X m × X k => ((p.2, p.1) : X k × X m)) := by fun_prop
    have h2 : Measurable (fun p : X k × X m => Φ (mergeBlock k m p)) :=
      hΦm.comp (Work.KinPSuperadd.continuous_mergeBlock k m).measurable
    simpa only [Function.comp_def, fibre, mkSlot_eq_mergeBlock] using h2.comp h1
  have hQ : Measurable (fun p : X m × X k =>
      Work.UBBInputs8.boxQInd V A j (fibre k m Φ p.1) p.2) := by
    have hind : Measurable (fun p : X m × X k => A.indicator (fun _ => (1 : ℝ)) (p.2 j)) :=
      (measurable_const.indicator hA).comp ((measurable_pi_apply j).comp measurable_snd)
    have hjoint : Measurable (fun q : (X m × X k) × E3 =>
        A.indicator (fun z => fibre k m Φ q.1.1 (Function.update q.1.2 j z)) q.2) := by
      have hupd : Measurable (fun q : (X m × X k) × E3 => Function.update q.1.2 j q.2) := by
        have hq : Measurable (fun q : (X m × X k) × E3 => (q.1.2, q.2)) := by fun_prop
        simpa only [Function.comp_def] using
          (measurable_update' (X := fun _ : Fin k => E3) (a := j)).comp hq
      have h1 : Measurable (fun q : (X m × X k) × E3 =>
          fibre k m Φ q.1.1 (Function.update q.1.2 j q.2)) := by
        have hq : Measurable (fun q : (X m × X k) × E3 => (q.1.1, Function.update q.1.2 j q.2)) := by
          exact Measurable.prodMk (by fun_prop) hupd
        simpa only [Function.comp_def] using hslot.comp hq
      have h2 : Measurable (fun q : (X m × X k) × E3 =>
          A.indicator (fun z => fibre k m Φ q.1.1 (Function.update q.1.2 j z)) q.2) := by
        classical
        rw [show (fun q : (X m × X k) × E3 =>
              A.indicator (fun z => fibre k m Φ q.1.1 (Function.update q.1.2 j z)) q.2)
            = fun q : (X m × X k) × E3 =>
                if q.2 ∈ A then fibre k m Φ q.1.1 (Function.update q.1.2 j q.2) else 0 by
          funext q
          exact Set.indicator_apply _ _ _]
        exact Measurable.ite (hA.preimage measurable_snd) h1 measurable_const
      exact h2
    have hSM := hjoint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    have hint : Measurable (fun p : X m × X k =>
        ∫ z in A, fibre k m Φ p.1 (Function.update p.2 j z)) := by
      have h2 := hSM.measurable
      have heq : (fun p : X m × X k =>
            ∫ z, A.indicator (fun z => fibre k m Φ p.1 (Function.update p.2 j z)) z ∂volume)
          = fun p : X m × X k => ∫ z in A, fibre k m Φ p.1 (Function.update p.2 j z) := by
        funext p
        exact MeasureTheory.integral_indicator hA
      rw [heq] at h2
      exact h2
    have hboxP : Measurable (fun p : X m × X k =>
        Work.UBBInputs8.boxPInd V A j (fibre k m Φ p.1) p.2) := by
      have h : Measurable (fun p : X m × X k => (1 / V)
          * (∫ z in A, fibre k m Φ p.1 (Function.update p.2 j z))
          * A.indicator (fun _ => (1 : ℝ)) (p.2 j)) :=
        (measurable_const.mul hint).mul hind
      convert h using 1
      funext p
      rw [Work.UBBInputs8.boxPInd]
    have h : Measurable (fun p : X m × X k =>
        A.indicator (fun _ => (1 : ℝ)) (p.2 j) * fibre k m Φ p.1 p.2
          - Work.UBBInputs8.boxPInd V A j (fibre k m Φ p.1) p.2) :=
      (hind.mul hslot).sub hboxP
    convert h using 1
    funext p
    rw [Work.UBBInputs8.boxQInd]
  have hamp : Measurable (fun q : ((E3 × X m) × X k) × E3 =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ))) *
        ((Work.UBBInputs8.boxQInd V A j (fibre k m Φ q.1.1.2)
          (Function.update q.1.2 j q.2) : ℝ) : ℂ)) := by
    have hQw : Measurable (fun q : ((E3 × X m) × X k) × E3 =>
        Work.UBBInputs8.boxQInd V A j (fibre k m Φ q.1.1.2) (Function.update q.1.2 j q.2)) := by
      have hupd : Measurable (fun q : ((E3 × X m) × X k) × E3 =>
          Function.update q.1.2 j q.2) := by
        have hq : Measurable (fun q : ((E3 × X m) × X k) × E3 => (q.1.2, q.2)) := by fun_prop
        simpa only [Function.comp_def] using
          (measurable_update' (X := fun _ : Fin k => E3) (a := j)).comp hq
      have hq : Measurable (fun q : ((E3 × X m) × X k) × E3 =>
          (q.1.1.2, Function.update q.1.2 j q.2)) := by
        exact Measurable.prodMk (by fun_prop) hupd
      simpa only [Function.comp_def] using hQ.comp hq
    have h1 : Measurable (fun q : ((E3 × X m) × X k) × E3 => (χ q.2 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχc.measurable.comp measurable_snd)
    have h2 : Measurable (fun q : ((E3 × X m) × X k) × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ q.1.1.1 q.2 : ℂ)))) := by
      have hpair : Continuous (fun q : ((E3 × X m) × X k) × E3 => (q.1.1.1, q.2)) := by fun_prop
      have hinner : Continuous (fun q : ((E3 × X m) × X k) × E3 =>
          (inner ℝ q.1.1.1 q.2 : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_inner.comp hpair)
      exact (Complex.continuous_exp.comp ((continuous_const.mul hinner).neg)).measurable
    have h3 : Measurable (fun q : ((E3 × X m) × X k) × E3 =>
        ((Work.UBBInputs8.boxQInd V A j (fibre k m Φ q.1.1.2)
          (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hQw
    exact (h1.mul h2).mul h3
  have hnorm : Measurable (fun p : (E3 × X m) × X k =>
      ‖Work.SmallBoxTBWord.tBamp χ p.1.1 (Work.UBBInputs8.boxQInd V A j (fibre k m Φ p.1.2))
        j p.2‖ ^ 2) := by
    have hSM := hamp.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable.norm.pow_const 2
  have hfin : Measurable (fun q : E3 × X m => ∫ z in abox k a,
      ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd V A j (fibre k m Φ q.2))
        j z‖ ^ 2) := by
    have hSM := hnorm.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (X k)).restrict (abox k a))
    exact hSM.measurable
  exact hfin.aestronglyMeasurable



/-! ## 6. The `j`-th fibre slot summand -/

/-- The `j`-th summand of `tBdiagFormInd` at the fibre state of the out-of-box configuration `w`. -/
def fibreSlot (k m : ℕ) (a V : ℝ) (A : Set E3) (χ : E3 → ℝ) (F : ℝ → ℝ)
    (Φ : X (k + m) → ℝ) (j : Fin k) (w : X m) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
    ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
      (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)

theorem sum_fibreSlot_eq_tBdiagFormInd (k m : ℕ) (a V : ℝ) (A : Set E3) (χ : E3 → ℝ)
    (F : ℝ → ℝ) (Φ : X (k + m) → ℝ) (w : X m) :
    (∑ j : Fin k, fibreSlot k m a V A χ F Φ j w)
      = Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w) := rfl

/-! ## 7. The fibre split of the kinetic slot -/

theorem tBdiagFormInd_fibreSplit {k m : ℕ} {a V : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχA : ∀ z, z ∉ A → χ z = 0)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFnn : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ENat) Ψ → ∀ i : Fin N,
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ *
        ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2)))
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦc : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ) :
    Work.UBBInputs8.tBdiagFormInd a A V χ F Φ
      = ∫ y in Work.BoseFixB1.Cube.Loc.Dloc m a A,
          Work.UBBInputs8.tBdiagFormInd a A V χ F (Work.BoseFixB1.Cube.Loc.fibre k m Φ y) := by
  classical
  -- ## 0. elementary facts
  have hΦm : Measurable Φ := hΦc.continuous.measurable
  have hχint : Integrable (fun z : E3 => |χ z|) :=
    (hχc.integrable_of_hasCompactSupport hχs).abs
  have hAfin : (volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (acube_lt_top a ha.le)
  obtain ⟨CΦ, hCΦ⟩ := (abox_compact (k + m) ha).exists_bound_of_continuousOn
    (f := Φ) hΦc.continuous.continuousOn
  have hCΦ0 : 0 ≤ CΦ := le_trans (norm_nonneg (Φ 0)) (hCΦ _ (zero_mem_abox ha.le))
  have hΦb : ∀ x ∈ abox (k + m) a, |Φ x| ≤ CΦ :=
    fun x hx => by simpa [Real.norm_eq_abs] using hCΦ x hx
  haveI hνfin : IsFiniteMeasure ((volume : Measure (X m)).restrict (abox m a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top m a ha.le⟩
  -- ## 1. the `natAdd` slots vanish
  have hboxQnat : ∀ j : Fin m, Work.UBBInputs8.boxQInd V A (Fin.natAdd k j) Φ
      =ᵐ[((volume : Measure (X (k + m))).restrict (abox (k + m) a))] 0 := by
    intro j
    refine boxQInd_ae_eq_zero_of_tube (N := k + m) (a := a) (V := V) (A := A) hA hAc
      (Fin.natAdd k j) ?_
    filter_upwards [hsupp] with x hx hxA
    by_contra hne
    exact (hx hne).2 j hxA
  have hnat : (∑ j : Fin m, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A (Fin.natAdd k j) Φ) (Fin.natAdd k j) x‖ ^ 2)) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hz : (fun p : E3 => F ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A (Fin.natAdd k j) Φ) (Fin.natAdd k j) x‖ ^ 2))
        = fun _ => 0 := by
      funext p
      rw [Work.BoseFixB1B.tBamp_integral_sq_eq_zero_of_ae_eq_zero
        (N := k + m) (a := a) (A := A) (χ := χ)
        (F := Work.UBBInputs8.boxQInd V A (Fin.natAdd k j) Φ) (Fin.natAdd k j) p hAc hχA
        (hboxQnat j)]
      ring
    rw [hz]
    simp
  -- ## 2. the `castAdd` slots
  have hfib : ∀ w : X m, (fun y : X k => Φ (mergeBlock k m (y, w))) = fibre k m Φ w := by
    intro w
    funext y
    simp only [fibre, mkSlot_eq_mergeBlock]
  have hkey : ∀ j : Fin k,
      ((((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ) (Fin.castAdd m j) x‖ ^ 2))
        = ∫ w in abox m a, fibreSlot k m a V A χ F Φ j w) ∧
      Integrable (fibreSlot k m a V A χ F Φ j)
        ((volume : Measure (X m)).restrict (abox m a)) := by
    intro j
    -- (a) the per-`p` box Fubini
    have hIntOn : ∀ p : E3, IntegrableOn (fun x : X (k + m) =>
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ)
          (Fin.castAdd m j) x‖ ^ 2) (abox (k + m) a) := fun p =>
      ampSqIntegrableOn_aux (N := k + m) (a := a) (V := V) (A := A) ha hA hAc hχc hχs hχA
        hΦm hCΦ0 hΦb (Fin.castAdd m j) p
    have hboxFub : ∀ p : E3,
        (∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ) (Fin.castAdd m j) x‖ ^ 2)
        = ∫ w in abox m a, ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2 := by
      intro p
      have h1 := (Work.BoseFixB1B.tBamp_amplitude_box_fubini (N1 := k) (N2 := m) (a := a)
        (V := V) (A := A) (χ := χ) (Φ := Φ) p).1 j (hIntOn p)
      rw [h1]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only []
      rw [hfib w]
    -- (b) the uniform bound on the fibre amplitudes
    have hKq : ∀ (w : X m), w ∈ abox m a → ∀ u : X k, u ∈ abox k a →
        |Work.UBBInputs8.boxQInd V A j (fibre k m Φ w) u|
          ≤ CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A) :=
      fun w hw u hu => abs_boxQInd_fibre_le (a := a) (V := V) (A := A) hAc hCΦ0 hAfin hΦb hw j hu
    have hKq0 : 0 ≤ CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A) :=
      add_nonneg hCΦ0
        (mul_nonneg (inv_nonneg.mpr (abs_nonneg V)) (mul_nonneg hCΦ0 measureReal_nonneg))
    have hamp_bd : ∀ (p : E3) (w : X m), w ∈ abox m a → ∀ u : X k, u ∈ abox k a →
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖
          ≤ (CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z| :=
      fun p w hw u hu =>
        norm_tBamp_le_of_boundedOn (a := a) hAc hχint hχA hKq0 (hKq w hw) j p hu
    have hInnerBd : ∀ (p : E3) (w : X m), w ∈ abox m a →
        (∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)
          ≤ (volume (abox k a)).toReal
            * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2 := by
      intro p w hw
      haveI : IsFiniteMeasure ((volume : Measure (X k)).restrict (abox k a)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top k a ha.le⟩
      have hg : Integrable (fun _ : X k =>
          ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2)
          ((volume : Measure (X k)).restrict (abox k a)) := integrable_const _
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (μ := (volume : Measure (X k)).restrict (abox k a))
        (f := fun u : X k => ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)
        (g := fun _ : X k =>
          ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2)
        (Filter.Eventually.of_forall fun u => sq_nonneg _) hg
        (by
          filter_upwards [MeasureTheory.ae_restrict_mem (abox_measurable k a)] with u hu
          exact pow_le_pow_left₀ (norm_nonneg _) (hamp_bd p w hw u hu) 2)
      have hconst : (∫ u : X k,
          ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2
          ∂((volume : Measure (X k)).restrict (abox k a)))
          = (volume (abox k a)).toReal
            * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2 := by
        rw [MeasureTheory.integral_const, Measure.real_def, Measure.restrict_apply_univ,
          smul_eq_mul]
      rwa [hconst] at hmono
    -- (c) the joint integrand
    set φ : E3 → X m → ℝ := fun p w => F ‖p‖ * ((a ^ 3)⁻¹ *
      ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
        (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2) with hφdef
    have haesm : AEStronglyMeasurable (Function.uncurry φ)
        ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) := by
      have hE := fibreAmpAEMeasurable_aux (k := k) (m := m) (a := a) (V := V) (A := A) hA hχc hΦm j
      have hFaes : AEStronglyMeasurable (fun q : E3 × X m => F ‖q.1‖)
          ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) :=
        (hFm.comp (continuous_norm.measurable.comp measurable_fst)).aestronglyMeasurable
      have h := hFaes.mul (hE.const_mul ((a ^ 3)⁻¹))
      refine h.congr ?_
      filter_upwards with q
      rw [hφdef]
      rfl
    have hIntW : ∀ᵐ p ∂(volume : Measure E3), Integrable (fun w : X m => φ p w)
        ((volume : Measure (X m)).restrict (abox m a)) := by
      filter_upwards [haesm.prodMk_left] with p hp
      refine Integrable.of_bound hp (|F ‖p‖| * (|(a ^ 3)⁻¹| * ((volume (abox k a)).toReal
        * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2))) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (abox_measurable m a)] with w hw
      have hI0 : 0 ≤ ∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2 :=
        integral_nonneg (fun u => sq_nonneg _)
      rw [hφdef]
      calc ‖F ‖p‖ * ((a ^ 3)⁻¹ * (∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2))‖
          = |F ‖p‖| * (|(a ^ 3)⁻¹| * (∫ u in abox k a, ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd V A j (fibre k m Φ w)) j u‖ ^ 2)) := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg hI0]
        _ ≤ |F ‖p‖| * (|(a ^ 3)⁻¹| * ((volume (abox k a)).toReal
              * ((CΦ + |V|⁻¹ * (CΦ * (volume : Measure E3).real A)) * ∫ z : E3, |χ z|) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hInnerBd p w hw) ?_) ?_
            · positivity
            · positivity
    have hIntP : Integrable (fun p : E3 => ∫ w, ‖φ p w‖
        ∂((volume : Measure (X m)).restrict (abox m a))) (volume : Measure E3) := by
      have heq : (fun p : E3 => ∫ w, ‖φ p w‖
            ∂((volume : Measure (X m)).restrict (abox m a)))
          = (fun p : E3 => F ‖p‖ * ((a ^ 3)⁻¹ *
              ∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ)
                (Fin.castAdd m j) x‖ ^ 2)) := by
        funext p
        have hnn : ∀ w : X m, 0 ≤ φ p w := by
          intro w
          rw [hφdef]
          exact mul_nonneg (hFnn _) (mul_nonneg (by positivity)
            (integral_nonneg (fun u => sq_nonneg _)))
        rw [show (fun w : X m => ‖φ p w‖) = fun w : X m => φ p w from
          funext fun w => Real.norm_of_nonneg (hnn w)]
        simp only [hφdef]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        rw [← hboxFub p]
      rw [heq]
      exact hint (k + m) Φ hΦc (Fin.castAdd m j)
    have hJoint : Integrable (Function.uncurry φ)
        ((volume : Measure E3).prod ((volume : Measure (X m)).restrict (abox m a))) :=
      (integrable_prod_iff haesm).mpr ⟨hIntW, hIntP⟩
    have hswap := MeasureTheory.integral_integral_swap hJoint
    have hwint : Integrable (fibreSlot k m a V A χ F Φ j)
        ((volume : Measure (X m)).restrict (abox m a)) := by
      have h1 : Integrable (fun w : X m => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, φ p w
          ∂(volume : Measure E3)) ((volume : Measure (X m)).restrict (abox m a)) :=
        hJoint.integral_prod_right.const_mul _
      refine h1.congr ?_
      filter_upwards with w
      simp only [fibreSlot, hφdef]
    refine ⟨?_, hwint⟩
    calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in abox (k + m) a, ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd V A (Fin.castAdd m j) Φ) (Fin.castAdd m j) x‖ ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ∫ w, φ p w
            ∂((volume : Measure (X m)).restrict (abox m a)) := by
          congr 1
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only []
          rw [hboxFub p]
          simp only [hφdef]
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ w, (∫ p, φ p w ∂(volume : Measure E3))
            ∂((volume : Measure (X m)).restrict (abox m a)) := by
          rw [hswap]
      _ = ∫ w in abox m a, fibreSlot k m a V A χ F Φ j w := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only [fibreSlot, hφdef]
  -- ## 3. assemble
  have hLHS : Work.UBBInputs8.tBdiagFormInd a A V χ F Φ
      = ∫ w in abox m a, Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w) := by
    simp only [Work.UBBInputs8.tBdiagFormInd]
    rw [Fin.sum_univ_add]
    rw [hnat, add_zero]
    refine (Finset.sum_congr rfl (fun j _ => (hkey j).1)).trans ?_
    rw [(MeasureTheory.integral_finsetSum (μ := (volume : Measure (X m)).restrict (abox m a))
      Finset.univ (f := fun j w => fibreSlot k m a V A χ F Φ j w)
      (fun j _ => (hkey j).2)).symm]
    simp only [fibreSlot]
  rw [hLHS]
  -- ## 4. the domain reduction
  have hmeasD : MeasurableSet (Dloc m a A) := measurableSet_Dloc m hA
  have hmeasDiff : MeasurableSet (abox m a \ Dloc m a A) := (abox_measurable m a).diff hmeasD
  have hzero : (fun w : X m => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w))
      =ᵐ[((volume : Measure (X m)).restrict (abox m a \ Dloc m a A))] 0 := by
    have hslice := (subsectorSupp_slice_snd hsupp).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_le_self (s := abox m a \ Dloc m a A)))
    rw [Measure.restrict_restrict_of_subset (s := abox m a \ Dloc m a A) (t := abox m a)
      Set.sdiff_subset] at hslice
    filter_upwards [hslice, MeasureTheory.ae_restrict_mem hmeasDiff] with w hw hwmem
    obtain ⟨jj, hj⟩ := exists_mem_A_of_mem_abox_not_mem_Dloc hwmem.1 hwmem.2
    refine tBdiagFormInd_eq_zero_of_ae_eq_zero (N := k) (a := a) (V := V) (A := A)
      (χ := χ) (F := F) hA hAc hχA ?_
    filter_upwards [hw] with z hz
    simp only [fibre, mkSlot_eq_mergeBlock]
    by_contra hne
    exact (hz hne).2 jj hj
  have hS : (volume : Measure (X m))
      {x : X m | (abox m a).indicator
          (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x
        ≠ (Dloc m a A).indicator
          (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x} = 0 := by
    have hsub : {x : X m | (abox m a).indicator
          (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x
        ≠ (Dloc m a A).indicator
          (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x}
        ⊆ {x : X m | Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ x) ≠ 0}
          ∩ (abox m a \ Dloc m a A) := by
      intro x hx
      by_cases hxa : x ∈ abox m a
      · have h1 : (abox m a).indicator
            (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x
            = Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ x) :=
          Set.indicator_of_mem hxa _
        by_cases hxd : x ∈ Dloc m a A
        · exact absurd (by rw [h1, Set.indicator_of_mem hxd]) hx
        · refine ⟨?_, ⟨hxa, hxd⟩⟩
          intro hF
          exact hx (by rw [h1, Set.indicator_of_notMem hxd, hF])
      · have h1 : (abox m a).indicator
            (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x = 0 :=
          Set.indicator_of_notMem hxa _
        have h2 : (Dloc m a A).indicator
            (fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)) x = 0 :=
          Set.indicator_of_notMem (fun hxd => hxa (Dloc_subset_abox m a A hxd)) _
        exact absurd (by rw [h1, h2]) hx
    have hae : (volume : Measure (X m))
        ({x : X m | Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ x) ≠ 0}
          ∩ (abox m a \ Dloc m a A)) = 0 := by
      rw [← Measure.restrict_apply' hmeasDiff]
      exact (MeasureTheory.ae_iff).mp hzero
    exact measure_mono_null hsub hae
  rw [← MeasureTheory.integral_indicator (μ := (volume : Measure (X m)))
        (abox_measurable m a)
        (f := fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w)),
      ← MeasureTheory.integral_indicator (μ := (volume : Measure (X m)))
        (measurableSet_Dloc m hA)
        (f := fun w => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ w))]
  exact MeasureTheory.integral_congr_ae hS


end Work.BoseFixB1.Cube.Loc
