import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.Q0Value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — the Q0-value identities for a.e.-measurable kernels

The `Q0Value` family (`pair_value`, `one_value`, `sumPair_value`,
`sumOne_value`, `q0_expect`) is stated for **measurable** kernels
`w1 w2 : kcE3 × kcE3 → ℝ` integrable on `acube ℓ ×ˢ acube ℓ`.  In every
genuine instantiation of the Fournais–Solovej box analysis, however, the
kernels are the χ-renormalized `wPairU ℓ h` with numerators `h = g₀`, `g₂`
(`ScatKernelChosen`), built from the potential `v : MemLp v 1` and the
scattering solution `w₀` (only `LocallyIntegrable`): these kernels are
**integrable but not literally measurable** (only a.e.-strongly-measurable,
which integrability already entails).

Since `IntegrableOn f s volume` already gives
`AEStronglyMeasurable f (volume.restrict s)`, the measurability hypothesis
in `Q0Value` is an *artifact* of the proof route: all the identities hold for
**any integrable kernel**.  This module re-proves the whole family with the
`Measurable` hypothesis removed:

    pair_value_ae      ∫(P_iP_jΦ)²·w₂(xᵢ,xⱼ) = ℓ⁻⁶·(∬w₂)·∫(P_iP_jΦ)²
    one_value_ae       ∫(P_iΦ)²·(∫_y w₁(xᵢ,y)) = ℓ⁻³·(∬w₁)·∫(P_iΦ)²
    sumPair_value_ae   Σ_{i≠j}-version of pair_value_ae
    sumOne_value_ae    Σ_i-version of one_value_ae
    q0_expect_ae       ⟨Φ,Q₀Φ⟩ = ½ℓ⁻⁶(∬w₂)S₂ − μℓ⁻³(∬w₁)S₁

## Route notes (for the child)

The proofs mirror `Q0Value.pair_value_aux` / `one_value_aux` verbatim, with
the measurability hypothesis on the kernel replaced by mere `IntegrableOn`
on the product cube.  The only places measurability entered were:

  * `Q0Value.integrableOn_pair_LHS` / `integrableOn_one_LHS` (integrability of
    `G·w₂(xᵢ,xⱼ)` / `G·(∫_y w₁(xᵢ,y))` over `abox`): here re-proved as
    `integrableOn_pair_LHS_ae` / `integrableOn_one_LHS_ae` using only
    `IntegrableOn`.  The pair case reduces to the measurable version through
    the a.e.-representative `w2.mk`
    (`AEStronglyMeasurable.mk`: `stronglyMeasurable_mk`, `ae_eq_mk`,
    `StronglyMeasurable.measurable`) plus the pullback a.e.-transfer
    `ae_eq_pair_pullback`; the one-body case uses Fubini for integrable
    kernels (`Integrable.integral_prod_left`,
    `AEStronglyMeasurable.integral_prod_right'`) in place of the measurable
    `w1_fibre`/`w1_fibre_aem`, giving `w1_fibre_ae`/`w1_fibre_aem_ae`.
  * `prod_setIntegral_eq_iter1/2` (Fubini rewriting the double integral over
    `acube ℓ ×ˢ acube ℓ` as iterated): re-proved as
    `prod_setIntegral_eq_iter1_ae`/`prod_setIntegral_eq_iter2_ae` using
    `MeasureTheory.integral_prod` / `integral_prod_symm` (which require only
    `Integrable`).

## Correction of the original draft's a.e.-transfer facts

The draft anticipated two "missing a.e.-transfer facts":

  * `ae_eq_pair_pullback` (pair pullback): kept here (in the version with
    `hℓ : 0 < ℓ`, needed for the measure-preserving peel
    `Q0Value.ins2_flat_mp`; all actual uses have `0 < ℓ` anyway).
  * `ae_eq_coord_pullback` (kernel slices `w₁(xᵢ,y)` at a **fixed** `y`):
    this statement is **false** — a.e.-equality on the product cube does not
    force equality of a single fibre: e.g. `N = 1`, `w₁(z,y') :=
    if y' = 0 then 1 else 0`, `w₁' := 0` differ on the null set
    `acube × {0}`, but the pulls `x ↦ w₁(x₀, 0) ≡ 1` and `x ↦ 0` differ on
    a set of full measure.  No lemma in this module needs slice-level
    transfers: the one-body integrand is handled through Fubini
    (`w1_fibre_ae`, `w1_fibre_aem_ae`) and the box peels of
    `one_value_aux_ae`, so the false statement is omitted.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
/-- Pullback a.e.-equality: a.e.-equal pair kernels give a.e.-equal
pullbacks to the full box (coordinates `i`, `j`). -/
lemma ae_eq_pair_pullback {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w2 w2' : kcE3 × kcE3 → ℝ}
    (hw : w2 =ᵐ[volume.restrict (acube ℓ ×ˢ acube ℓ)] w2') :
    (fun x : X N => w2 (x i, x j)) =ᵐ[volume.restrict (abox N ℓ)]
      fun x : X N => w2' (x i, x j) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          exfalso
          have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
          have hj0 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
          exact hij (Fin.ext (hi0.trans hj0.symm))
      | succ p =>
          rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
          let F : Set (kcE3 × kcE3) := {q | w2 q ≠ w2' q}
          have hF0 : (volume.restrict (acube ℓ ×ˢ acube ℓ)) F = 0 := by
            simpa [F] using (ae_iff.mp hw)
          rcases exists_measurable_superset_of_null (μ := volume.restrict (acube ℓ ×ˢ acube ℓ)) hF0 with ⟨G0, hFG0, hG0m, hG00⟩
          let E0 : Set (X (p + 2)) := {x | (x i, x j) ∈ G0}
          have hEsub : {x : X (p + 2) | w2 (x i, x j) ≠ w2' (x i, x j)} ⊆ E0 := by
            intro x hx
            exact hFG0 (by simpa [F] using hx)
          have hπm : Measurable (fun x : X (p + 2) => (x i, x j)) := by
            fun_prop
          have hE0m : MeasurableSet E0 := hπm hG0m
          let μ' : Measure kcE3 := (volume : Measure kcE3).restrict (acube ℓ)
          let ν_p : Measure (X p) := (volume : Measure (X p)).restrict (abox p ℓ)
          let T : (kcE3 × kcE3) × X p → X (p + 2) := fun q =>
            kcInsN (p + 1) i (q.1.1, kcInsN p j' (q.1.2, q.2))
          have hmp : MeasurePreserving T ((μ'.prod μ').prod ν_p)
              (volume.restrict (abox (p + 2) ℓ)) := by
            simpa [T, μ', ν_p] using (ins2_flat_mp (p := p) hℓ i j')
          have hTm : Measurable T := hmp.measurable
          have hpre : T ⁻¹' E0 = G0 ×ˢ (Set.univ : Set (X p)) := by
            ext q
            rcases q with ⟨⟨y, z⟩, r2⟩
            simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
            change ((kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i,
                    (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) j) ∈ G0 ↔ (y, z) ∈ G0
            rw [show (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i = y by
                  exact kc_insN_apply_same (p + 1) i y (kcInsN p j' (z, r2))]
            rw [show (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) j = z by
                  rw [← hj']
                  exact (kc_insN_apply_succ (p + 1) i y (kcInsN p j' (z, r2)) j').trans
                    (kc_insN_apply_same p j' z r2)]
          have hG0prod : (μ'.prod μ') G0 = 0 := by
            simpa [μ', prod_measure_eq] using hG00
          have hE00 : (volume.restrict (abox (p + 2) ℓ)) E0 = 0 := by
            calc
              (volume.restrict (abox (p + 2) ℓ)) E0
                  = ((μ'.prod μ').prod ν_p) (T ⁻¹' E0) := by
                    rw [← hmp.map_eq]
                    rw [Measure.map_apply hTm hE0m]
              _ = ((μ'.prod μ').prod ν_p) (G0 ×ˢ (Set.univ : Set (X p))) := by rw [hpre]
              _ = (μ'.prod μ') G0 * ν_p Set.univ := by
                    exact Measure.prod_prod G0 (Set.univ : Set (X p))
              _ = 0 := by rw [hG0prod, zero_mul]
          change ∀ᵐ x ∂(volume.restrict (abox (p + 2) ℓ)), w2 (x i, x j) = w2' (x i, x j)
          rw [ae_iff]
          exact measure_mono_null hEsub hE00

/-! ### Fubini/representative helpers without measurability -/

/-- the product-set integral equals the iterated integral (y outer, z inner),
for an *integrable* (not necessarily measurable) kernel -/
lemma prod_setIntegral_eq_iter1_ae {ℓ : ℝ} {w : kcE3 × kcE3 → ℝ}
    (hwi : IntegrableOn w (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, w (y, z)) = ∫ p in acube ℓ ×ˢ acube ℓ, w p := by
  have hInt : Integrable w ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hwi
  have hF := MeasureTheory.integral_prod (μ := (volume : Measure kcE3).restrict (acube ℓ))
    (ν := (volume : Measure kcE3).restrict (acube ℓ)) (f := fun p : kcE3 × kcE3 => w p) hInt
  rw [← hF]
  rw [← prod_measure_eq ℓ]

/-- the product-set integral equals the iterated integral (z outer, y inner),
for an *integrable* (not necessarily measurable) kernel -/
lemma prod_setIntegral_eq_iter2_ae {ℓ : ℝ} {w : kcE3 × kcE3 → ℝ}
    (hwi : IntegrableOn w (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ z in acube ℓ, ∫ y in acube ℓ, w (y, z)) = ∫ p in acube ℓ ×ˢ acube ℓ, w p := by
  have hInt : Integrable w ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hwi
  have hF := MeasureTheory.integral_prod_symm (μ := (volume : Measure kcE3).restrict (acube ℓ))
    (ν := (volume : Measure kcE3).restrict (acube ℓ)) (f := fun p : kcE3 × kcE3 => w p) hInt
  rw [← hF]
  rw [← prod_measure_eq ℓ]

/-- integrability of the one-particle fibre mean `z ↦ ∫_y w1 (z, y)` over the cube
(no measurability: Fubini for integrable kernels) -/
lemma w1_fibre_ae {ℓ : ℝ} {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    Integrable (fun z : kcE3 => ∫ y in acube ℓ, w1 (z, y))
      (volume.restrict (acube ℓ)) := by
  have hInt : Integrable w1 ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hw1i
  have hmain := MeasureTheory.Integrable.integral_prod_left (μ := (volume : Measure kcE3).restrict (acube ℓ))
    (ν := (volume : Measure kcE3).restrict (acube ℓ)) hInt
  simpa using hmain

/-- a.e.-strong measurability of the one-particle fibre mean `z ↦ ∫_y w1 (z, y)`
over the cube (from integrability, no measurability) -/
lemma w1_fibre_aem_ae {ℓ : ℝ} {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    AEStronglyMeasurable (fun z : kcE3 => ∫ y in acube ℓ, w1 (z, y))
      (volume.restrict (acube ℓ)) := by
  have hInt : AEStronglyMeasurable w1
      ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) := by
    exact (integrable_prod_of_IntegrableOn hw1i).aestronglyMeasurable
  have h1 : AEStronglyMeasurable (fun z : kcE3 => ∫ y : kcE3, w1 (z, y)
        ∂(volume.restrict (acube ℓ))) (volume.restrict (acube ℓ)) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure kcE3).restrict (acube ℓ))
      (ν := (volume : Measure kcE3).restrict (acube ℓ)) hInt
  simpa using h1


/-! ### Integrability of the ae integrands -/

/-- `w2 (x i, x j)` is integrable over the centred `(p+2)`-box for distinct
`i j`, for an *integrable* (not necessarily measurable) kernel -/
lemma integrableOn_pair_comp_ae {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {w2 : kcE3 × kcE3 → ℝ}
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X (p + 2) => w2 (x i, x j)) (abox (p + 2) ℓ) volume := by
  have hw2aem : AEStronglyMeasurable w2 (volume.restrict (acube ℓ ×ˢ acube ℓ)) :=
    hw2i.aestronglyMeasurable
  let w2' : kcE3 × kcE3 → ℝ := hw2aem.mk
  have hw2'm : Measurable w2' := hw2aem.stronglyMeasurable_mk.measurable
  have hw2'ae : w2 =ᵐ[volume.restrict (acube ℓ ×ˢ acube ℓ)] w2' := hw2aem.ae_eq_mk
  have hw2'i : IntegrableOn w2' (acube ℓ ×ˢ acube ℓ) volume := by
    change Integrable w2' (volume.restrict (acube ℓ ×ˢ acube ℓ))
    exact Integrable.congr (show Integrable w2 (volume.restrict (acube ℓ ×ˢ acube ℓ)) from hw2i) hw2'ae
  have hw2'comp : IntegrableOn (fun x : X (p + 2) => w2' (x i, x j)) (abox (p + 2) ℓ) volume :=
    integrableOn_pair_comp hℓ i j hij hw2'm hw2'i
  have hpull : (fun x : X (p + 2) => w2 (x i, x j)) =ᵐ[volume.restrict (abox (p + 2) ℓ)]
      fun x : X (p + 2) => w2' (x i, x j) := ae_eq_pair_pullback (N := p + 2) hℓ hij hw2'ae
  change Integrable (fun x : X (p + 2) => w2 (x i, x j)) (volume.restrict (abox (p + 2) ℓ))
  exact Integrable.congr (show Integrable (fun x : X (p + 2) => w2' (x i, x j))
      (volume.restrict (abox (p + 2) ℓ)) from hw2'comp) hpull.symm

/-- the pair-value integrand is integrable over the centred box (no
measurability: `G` continuous, `w2` integrable on the product cube) -/
lemma integrableOn_pair_LHS_ae_core {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2))
    (hij : i ≠ j) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ}
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      (abox (p + 2) ℓ) volume := by
  have hcG : Continuous (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2) :=
    aP_pair_sq_continuous hℓ i j hΦc
  obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn (s := abox (p + 2) ℓ)
    (f := fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2) hcG.continuousOn
  have hwcomp : IntegrableOn (fun x : X (p + 2) => w2 (x i, x j)) (abox (p + 2) ℓ) volume :=
    integrableOn_pair_comp_ae hℓ i j hij hw2i
  have hwabs : Integrable (fun x : X (p + 2) => |w2 (x i, x j)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    have hwabs' := hwcomp.abs
    simpa [Real.norm_eq_abs] using hwabs'
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (p + 2) ℓ)),
      ‖(aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j)‖ ≤ B * |w2 (x i, x j)| := by
    rw [ae_restrict_iff' (abox_measurable (p + 2) ℓ)]
    apply ae_of_all
    intro x hx
    have hle : |(aP ℓ i (aP ℓ j Φ) x) ^ 2| ≤ B := by
      have hb' := hB x hx
      simpa [Real.norm_eq_abs] using hb'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      (volume.restrict (abox (p + 2) ℓ)) := by
    have h1 : Measurable (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2) := hcG.measurable
    exact (h1.aestronglyMeasurable.mul hwcomp.aestronglyMeasurable)
  have hdomin : Integrable (fun x : X (p + 2) => B * |w2 (x i, x j)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hwabs.const_mul B
  exact Integrable.mono' hdomin hmeas hbnd

/-- the pair-value integrand is integrable (general-N statement of the
`AeValue` family) -/
lemma integrableOn_pair_LHS_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ}
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X N => (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      (abox N ℓ) volume := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          exfalso
          have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
          have hj0 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
          exact hij (Fin.ext (hi0.trans hj0.symm))
      | succ p =>
          exact integrableOn_pair_LHS_ae_core (p := p) hℓ i j hij hΦc hw2i

/-- the one-body value integrand is integrable over the centred box (no
measurability) -/
lemma integrableOn_one_LHS_ae_core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      (abox (n + 1) ℓ) volume := by
  let g : kcE3 → ℝ := fun z => ∫ y in acube ℓ, w1 (z, y)
  have hgc : AEStronglyMeasurable (fun x : X (n + 1) => g (x i))
      (volume.restrict (abox (n + 1) ℓ)) := by
    exact aem_comp_coord i (w1_fibre_aem_ae (w1 := w1) hw1i)
  have hgi : IntegrableOn (fun x : X (n + 1) => g (x i)) (abox (n + 1) ℓ) volume := by
    exact integrableOn_comp_coord hℓ i (w1_fibre_aem_ae (w1 := w1) hw1i) (w1_fibre_ae hw1i)
  have hgabs : Integrable (fun x : X (n + 1) => |g (x i)|)
      (volume.restrict (abox (n + 1) ℓ)) := by
    have h := hgi.abs
    simpa [Real.norm_eq_abs] using h
  have hcG : Continuous (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2) := aP_sq_continuous hℓ i hΦc
  obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn (s := abox (n + 1) ℓ)
    (f := fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2) hcG.continuousOn
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (n + 1) ℓ)),
      ‖(aP ℓ i Φ x) ^ 2 * g (x i)‖ ≤ B * |g (x i)| := by
    rw [ae_restrict_iff' (abox_measurable (n + 1) ℓ)]
    apply ae_of_all
    intro x hx
    have hb' := hB x hx
    have hle : |(aP ℓ i Φ x) ^ 2| ≤ B := by simpa [Real.norm_eq_abs] using hb'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2 * g (x i))
      (volume.restrict (abox (n + 1) ℓ)) := by
    have h1 : Measurable (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2) := hcG.measurable
    exact (h1.aestronglyMeasurable.mul hgc)
  have hdomin : Integrable (fun x : X (n + 1) => B * |g (x i)|)
      (volume.restrict (abox (n + 1) ℓ)) := by
    exact hgabs.const_mul B
  have hres : Integrable (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2 * g (x i))
      (volume.restrict (abox (n + 1) ℓ)) := Integrable.mono' hdomin hmeas hbnd
  exact hres


/-! ### The value identities without measurability -/

/-- **pair_value_ae at dimension `p + 2`** -/
lemma pair_value_aux_ae {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ}
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∫ x in abox (p + 2) ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
  rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
  let G : X (p + 2) → ℝ := fun x => (aP ℓ i (aP ℓ j Φ) x) ^ 2
  let T2 : ℝ := ∫ r2 in abox p ℓ, G (rest2 i j' r2)
  have hF1 : IntegrableOn (fun x : X (p + 2) => G x * w2 (x i, x j)) (abox (p + 2) ℓ) volume := by
    simpa [G] using integrableOn_pair_LHS_ae_core hℓ i j hij hΦc hw2i
  have hG : IntegrableOn G (abox (p + 2) ℓ) volume := by
    exact integrableOn_abox_of_continuous hℓ (aP_pair_sq_continuous hℓ i j hΦc)
  have hpeel1 := abox_integral_peel2 (p := p) (i := i) (j' := j')
    (F := fun x : X (p + 2) => G x * w2 (x i, x j)) hF1
  have hmain : (∫ x in abox (p + 2) ℓ, G x * w2 (x i, x j)) = (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) * T2 := by
    calc
      (∫ x in abox (p + 2) ℓ, G x * w2 (x i, x j))
          = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
              G (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) * w2 (y, z) := by
            rw [hpeel1]
            apply integral_congr_ae
            filter_upwards with r2
            apply integral_congr_ae
            filter_upwards with z
            apply integral_congr_ae
            filter_upwards with y
            have hY : (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i = y :=
              kc_insN_apply_same (p + 1) i y (kcInsN p j' (z, r2))
            have hZ : (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) j = z := by
              rw [← hj']
              exact (kc_insN_apply_succ (p + 1) i y (kcInsN p j' (z, r2)) j').trans
                (kc_insN_apply_same p j' z r2)
            rw [hY, hZ]
      _ = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, G (rest2 i j' r2) * w2 (y, z) := by
            apply integral_congr_ae
            filter_upwards with r2
            apply integral_congr_ae
            filter_upwards with z
            apply integral_congr_ae
            filter_upwards with y
            have hGfib : G (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) = G (rest2 i j' r2) := by
              dsimp [G]
              exact congrArg (fun t : ℝ => t ^ 2) (aP_pair_fiber_const hℓ i j hij j' hj' hΦc y z r2)
            rw [hGfib]
      _ = T2 * (∫ z in acube ℓ, ∫ y in acube ℓ, w2 (y, z)) := by
            dsimp [T2]
            calc
              (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, G (rest2 i j' r2) * w2 (y, z))
                  = ∫ r2 in abox p ℓ, G (rest2 i j' r2) * (∫ z in acube ℓ, ∫ y in acube ℓ, w2 (y, z)) := by
                    apply integral_congr_ae
                    filter_upwards with r2
                    calc
                      (∫ z in acube ℓ, ∫ y in acube ℓ, G (rest2 i j' r2) * w2 (y, z))
                          = ∫ z in acube ℓ, (G (rest2 i j' r2) * ∫ y in acube ℓ, w2 (y, z)) := by
                            apply integral_congr_ae
                            filter_upwards with z
                            rw [MeasureTheory.integral_const_mul]
                      _ = G (rest2 i j' r2) * (∫ z in acube ℓ, ∫ y in acube ℓ, w2 (y, z)) := by
                            rw [MeasureTheory.integral_const_mul]
              _ = (∫ r2 in abox p ℓ, G (rest2 i j' r2)) * (∫ z in acube ℓ, ∫ y in acube ℓ, w2 (y, z)) := by
                    rw [MeasureTheory.integral_mul_const]
      _ = (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) * T2 := by
            rw [prod_setIntegral_eq_iter2_ae hw2i]
            ac_rfl
  have hpeel2 := abox_integral_peel2 (p := p) (i := i) (j' := j') (F := G) hG
  have hGvol : (∫ x in abox (p + 2) ℓ, G x) = (ℓ ^ 3) * (ℓ ^ 3) * T2 := by
    calc
      (∫ x in abox (p + 2) ℓ, G x)
          = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, G (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) := hpeel2
      _ = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, G (rest2 i j' r2) := by
            apply integral_congr_ae
            filter_upwards with r2
            apply integral_congr_ae
            filter_upwards with z
            apply integral_congr_ae
            filter_upwards with y
            have hGfib : G (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) = G (rest2 i j' r2) := by
              dsimp [G]
              exact congrArg (fun t : ℝ => t ^ 2) (aP_pair_fiber_const hℓ i j hij j' hj' hΦc y z r2)
            rw [hGfib]
      _ = (ℓ ^ 3) * (ℓ ^ 3) * T2 := by
            dsimp [T2]
            calc
              (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, G (rest2 i j' r2))
                  = ∫ r2 in abox p ℓ, (ℓ ^ 3) * (ℓ ^ 3) * G (rest2 i j' r2) := by
                    apply integral_congr_ae
                    filter_upwards with r2
                    calc
                      (∫ z in acube ℓ, ∫ y in acube ℓ, G (rest2 i j' r2))
                          = ∫ z in acube ℓ, (G (rest2 i j' r2) * ℓ ^ 3) := by
                            apply integral_congr_ae
                            filter_upwards with z
                            rw [integral_const_acube ℓ hℓ]
                      _ = (G (rest2 i j' r2) * ℓ ^ 3) * ℓ ^ 3 := by
                            rw [integral_const_acube ℓ hℓ]
                      _ = (ℓ ^ 3) * (ℓ ^ 3) * G (rest2 i j' r2) := by ring
              _ = (ℓ ^ 3) * (ℓ ^ 3) * (∫ r2 in abox p ℓ, G (rest2 i j' r2)) := by
                    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ x in abox (p + 2) ℓ, G x * w2 (x i, x j))
        = (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) * T2 := hmain
    _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∫ x in abox (p + 2) ℓ, G x) := by
          rw [hGvol]
          have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
          field_simp [hℓ3]
          try ring
    _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∫ x in abox (p + 2) ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
          rfl


/-- **pair_value without measurability** (general `N`): for an integrable
(hence a.e.-strongly-measurable) kernel `w₂`,
`∫(P_iP_jΦ)²·w₂(xᵢ,xⱼ) = ℓ⁻⁶·(∬_{acube²}w₂)·∫(P_iP_jΦ)²`. -/
lemma pair_value_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ}
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          exfalso
          have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
          have hj0 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
          exact hij (Fin.ext (hi0.trans hj0.symm))
      | succ p =>
          exact pair_value_aux_ae (p := p) hℓ i j hij hΦc hw2i

/-- **one_value without measurability at dimension `n + 1`** -/
lemma one_value_aux_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
  let G : X (n + 1) → ℝ := fun x => (aP ℓ i Φ x) ^ 2
  let T1 : ℝ := ∫ r in abox n ℓ, G (kcInsN n i (0, r))
  have hF0 : IntegrableOn (fun x : X (n + 1) => G x * (∫ y in acube ℓ, w1 (x i, y)))
      (abox (n + 1) ℓ) volume := by
    simpa [G] using integrableOn_one_LHS_ae_core hℓ i hΦc hw1i
  have hG : IntegrableOn G (abox (n + 1) ℓ) volume := by
    simpa [G] using integrableOn_sq_aP hℓ i hΦc
  have hpeel1 := abox_integral_peel (n := n) (i := i)
    (F := fun x : X (n + 1) => G x * (∫ y in acube ℓ, w1 (x i, y))) hF0
  have hmain : (∫ x in abox (n + 1) ℓ, G x * (∫ y in acube ℓ, w1 (x i, y)))
      = (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) * T1 := by
    calc
      (∫ x in abox (n + 1) ℓ, G x * (∫ y in acube ℓ, w1 (x i, y)))
          = ∫ r in abox n ℓ, ∫ t in acube ℓ,
              G (kcInsN n i (t, r)) * (∫ y in acube ℓ, w1 (t, y)) := by
            rw [hpeel1]
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have hT : (kcInsN n i (t, r)) i = t := kc_insN_apply_same n i t r
            rw [hT]
      _ = ∫ r in abox n ℓ, ∫ t in acube ℓ,
              G (kcInsN n i (0, r)) * (∫ y in acube ℓ, w1 (t, y)) := by
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have hGfib : G (kcInsN n i (t, r)) = G (kcInsN n i (0, r)) := by
              dsimp [G]
              exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΦc t r)
            rw [hGfib]
      _ = (∫ t in acube ℓ, ∫ y in acube ℓ, w1 (t, y)) * T1 := by
            dsimp [T1]
            calc
              (∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)) * (∫ y in acube ℓ, w1 (t, y)))
                  = ∫ r in abox n ℓ, G (kcInsN n i (0, r)) * (∫ t in acube ℓ, ∫ y in acube ℓ, w1 (t, y)) := by
                    apply integral_congr_ae
                    filter_upwards with r
                    rw [MeasureTheory.integral_const_mul]
              _ = (∫ t in acube ℓ, ∫ y in acube ℓ, w1 (t, y)) * (∫ r in abox n ℓ, G (kcInsN n i (0, r))) := by
                    rw [MeasureTheory.integral_mul_const]
                    ring
      _ = (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) * T1 := by
            rw [prod_setIntegral_eq_iter1_ae hw1i]
  have hpeel2 := abox_integral_peel (n := n) (i := i) (F := G) hG
  have hGvol : (∫ x in abox (n + 1) ℓ, G x) = (ℓ ^ 3) * T1 := by
    calc
      (∫ x in abox (n + 1) ℓ, G x)
          = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (t, r)) := hpeel2
      _ = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)) := by
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have hGfib : G (kcInsN n i (t, r)) = G (kcInsN n i (0, r)) := by
              dsimp [G]
              exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΦc t r)
            rw [hGfib]
      _ = (ℓ ^ 3) * T1 := by
            dsimp [T1]
            calc
              (∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)))
                  = ∫ r in abox n ℓ, (ℓ ^ 3) * G (kcInsN n i (0, r)) := by
                    apply integral_congr_ae
                    filter_upwards with r
                    rw [integral_const_acube ℓ hℓ]
                    ring
              _ = (ℓ ^ 3) * (∫ r in abox n ℓ, G (kcInsN n i (0, r))) := by
                    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ x in abox (n + 1) ℓ, G x * (∫ y in acube ℓ, w1 (x i, y)))
        = (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) * T1 := hmain
    _ = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) * (∫ x in abox (n + 1) ℓ, G x) := by
          rw [hGvol]
          have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
          field_simp [hℓ3]
          try ring
    _ = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
          rfl

/-- **one_value without measurability** (general `N`) -/
lemma one_value_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      exact one_value_aux_ae (n := n) hℓ i hΦc hw1i

/-- **sumPair_value without measurability** -/
lemma sumPair_value_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {w2 : kcE3 × kcE3 → ℝ}
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1, x p.2))
      = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
  let c : ℝ := (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p)
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1, x p.2))
        = ∑ p ∈ pairSet N, c * (∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          have hp12 : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
          have hk := pair_value_ae (N := N) hℓ (i := p.1) (j := p.2) hp12 hΦc hw2i
          simpa [c, mul_assoc] using hk
    _ = c * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          dsimp [c]

/-- **sumOne_value without measurability** -/
lemma sumOne_value_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  let c : ℝ := (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p)
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
        = ∑ i : Fin N, c * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk := one_value_ae (N := N) hℓ (i := i) hΦc hw1i
          simpa [c, mul_assoc] using hk
    _ = c * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          dsimp [c]

/-- **q0_expect without measurability** -/
lemma q0_expect_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {w1 w2 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume)
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
            (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
        - μ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
            (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  rw [sumPair_value_ae hℓ hΦc hw2i, sumOne_value_ae hℓ hΦc hw1i]
  ring


/-- the one-body integrand is integrable over the centred box (general-`N`
statement of the `AeValue` family; no measurability) -/
lemma integrableOn_one_LHS_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ}
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X N => (aP ℓ i Φ x) ^ 2 *
      (∫ y in acube ℓ, w1 (x i, y))) (abox N ℓ) volume := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      exact integrableOn_one_LHS_ae_core (n := n) hℓ i hΦc hw1i


end BoseGases
end Submission