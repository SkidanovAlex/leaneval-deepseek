import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.KernelIds
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — the Q0-sector value identities (lem:QDecompSimpler eq:Q0n0)

The first (all-condensate) piece of the Fournais--Solovej potential
decomposition is (FS `eq:DefQ0`, `lem:QDecompSimpler` `eq:Q0n0`)

    Q₀^ren = ½ Σ_{i≠j} P_iP_j w₂(xᵢ,xⱼ) P_jP_i − μ Σ_i P_i (∫_y w₁(xᵢ,y) dy) P_i

with `P_i` the mean over the centred box (`Q0Sector.aP`) and `w₁,w₂` the
χ-renormalized kernels supported in `acube ℓ ×ˢ acube ℓ`.  Since `P_iP_jΦ`
is constant in the pair coordinates `(xᵢ,xⱼ)` and `P_iΦ` in `xᵢ`
(`Q0Sector.aP_pair_const_in_i/j`, `aP_const_in_coord`), the expectation value
factors into the pair double integrals:

    ∫_{abox N ℓ} (P_iP_jΦ)²·w₂(xᵢ,xⱼ) = ℓ⁻⁶·(∬w₂)·∫_{abox} (P_iP_jΦ)²        (pair_value)
    ∫_{abox N ℓ} (P_iΦ)²·(∫_y w₁(xᵢ,y)) = ℓ⁻³·(∬w₁)·∫_{abox} (P_iΦ)²          (one_value)

so that, writing `n₀Φ = Σ_i P_iΦ` and `S₂ = Σ_{i≠j}∫(P_iP_jΦ)²`,
`S₁ = Σ_i∫(P_iΦ)²` (all box-integrals over `abox N ℓ`),

    ⟨Φ, Q₀Φ⟩ = ½ℓ⁻⁶(∬w₂)S₂ − μℓ⁻³(∬w₁)S₁ .                                  (q0_expect)

This module proves these identities for any measurable kernels with
`w₂` integrable on `acube ℓ ×ˢ acube ℓ` and any continuous Φ (functions are
total; box integrals over the compact centred box).  It also proves the
support-transfer lemma (kernels built from `χ_ℓ := chiScale ℓ` vanish off
`acube ℓ ×ˢ acube ℓ`, so `∬_{acube²} = ∬_{ℝ⁶}`).

## Route notes (for the child)

* `pair_value`: G := aP ℓ i (aP ℓ j Φ) is constant in slots i and j
  (Q0Sector.aP_pair_const_in_i/j).  Peel the box integral twice with
  `abox_integral_peel` (isolate slot i, then slot j' = the image of j in the
  remaining `Fin (N−1)`); in the (y,z)-fiber the integrand is
  `G(rest)²·w₂(y,z)`; the (y,z)-integral is `(∬_{acube²} w₂)·G(rest)²`, and
  the integral of `G²` over the rest relates to the full box integral by the
  factor `ℓ⁶` (each remaining slot has volume `ℓ³`, `integral_const_acube` /
  `real_volume_acube`).  For `i`-peel: use `kcInsN` conventions of
  `Q0Sector.abox_integral_peel`; for the second peel use the `n = N−1` case
  at the correct index.
* `one_value`: same with a single peel and Fubini
  `∫_{xᵢ∈acube}(∫_{y∈acube} w₁(xᵢ,y) dy) dxᵢ = ∬ w₁`.
* sums: `Finset.sum_congr` with the per-pair / per-i lemmas (no analytic
  content); `q0_expect` is linear algebra from `sumPair_value`,
  `sumOne_value`.
* `prod_integral_eq_full` and `chiScale_mul_support_acube`: kernel support
  bookkeeping (χ_ℓ ≠ 0 ⟹ ‖·‖ ≤ ℓ/2 ⟹ ∈ acube via `KernelIds.chiScale_support_le`
  and `CentreBox.mem_acube_of_norm_le`; `tsupport`-style vanishing).  The
  product-set integral over `acube ℓ ×ˢ acube ℓ` equals the full ℝ³×ℝ³
  integral once the kernel vanishes outside.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Infrastructure: continuity of the mean, double peel, two-slot fibre -/

/-- The projection `Pᵢ` of a continuous function is continuous (for `0 < ℓ`). -/
lemma aP_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    Continuous (aP ℓ i Φ) := by
  have hcont : Continuous (fun x : X N => ∫ y : ℝ³ in acube ℓ, Φ (Function.update x i y)) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (x : X N) (y : ℝ³) => Φ (Function.update x i y)) ?_ ?_
    · fun_prop
    · exact acube_compact hℓ
  convert hcont.const_mul (1 / ℓ ^ 3) using 1
  ext x
  rfl

/-- the peeled fibre of an integrable function is integrable in the rest (centred-box
version of `SectorProj.box_peel_inner_integrable`) -/
lemma abox_peel_inner_integrable {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) (F : X (n + 1) → ℝ)
    (hF : IntegrableOn F (abox (n + 1) ℓ) volume) :
    Integrable (fun r : X n => ∫ y in acube ℓ, F (kcInsN n i (y, r)))
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ)
  have hmp : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (abox_peel_mp (n := n) ℓ i)
    simpa [kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : ℝ³ × X n => F (kcInsN n i p)) (μ'.prod ν) := by
    exact (hmp.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  have hsw : MeasurePreserving (fun p : X n × ℝ³ => (p.2, p.1)) (ν.prod μ') (μ'.prod ν) := by
    refine MeasurePreserving.mk (by measurability) ?_
    exact (MeasureTheory.Measure.prod_swap (μ := ν) (ν := μ'))
  have hswap : Integrable (fun p : X n × ℝ³ => F (kcInsN n i (p.2, p.1))) (ν.prod μ') := by
    exact (hsw.integrable_comp (hg := hpeel.aestronglyMeasurable)).mpr hpeel
  exact (hswap.integral_prod_left (μ := ν) (ν := μ'))

/-- Double peel of the centred box: first isolates slot `i : Fin (p + 2)`, then, inside the
remaining `p + 1` coordinates, the slot `j' : Fin (p + 1)`. -/
lemma abox_integral_peel2 {p : ℕ} {ℓ : ℝ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    (F : X (p + 2) → ℝ) (hF : IntegrableOn F (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, F x) =
      ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
          F (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) := by
  have h1 := abox_integral_peel (i := i) (n := p + 1) (F := F) hF
  have hHint : IntegrableOn (fun r : X (p + 1) => ∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r)))
      (abox (p + 1) ℓ) volume := by
    exact abox_peel_inner_integrable (n := p + 1) (i := i) F hF
  have h2 := abox_integral_peel (i := j') (n := p)
    (F := fun r : X (p + 1) => ∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r))) hHint
  rw [h1]
  simpa using h2

/-- zero lies in the centred cube -/
lemma zero_mem_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : (0 : ℝ³) ∈ acube ℓ := by
  intro m
  have h1 : (-ℓ / 2 : ℝ) ≤ (0 : ℝ) := by linarith
  have h2 : (0 : ℝ) ≤ ℓ / 2 := by linarith
  simpa using (Set.mem_Icc.mpr ⟨h1, h2⟩ : (0 : ℝ) ∈ Set.Icc (-ℓ / 2) (ℓ / 2))

/-- insert `y` at `i` and `z` at `i.succAbove j'`, with rest `r2` on the other slots -/
def ins2 {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (y : kcE3) (z : kcE3) (r2 : X p) : X (p + 2) :=
  kcInsN (p + 1) i (y, kcInsN p j' (z, r2))

/-- the two-slot fibre with both distinguished slots zeroed -/
def rest2 {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) : X (p + 2) :=
  ins2 i j' 0 0 r2

lemma ins2_apply_i {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (y z : kcE3) (r2 : X p) :
    ins2 i j' y z r2 i = y := by
  dsimp [ins2]
  exact kc_insN_apply_same (p + 1) i y (kcInsN p j' (z, r2))

lemma ins2_apply_succ {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (y z : kcE3) (r2 : X p) :
    ins2 i j' y z r2 (i.succAbove j') = z := by
  dsimp [ins2]
  rw [kc_insN_apply_succ]
  exact kc_insN_apply_same p j' z r2

/-- updating slot `i` of a double insertion just re-inserts with the new value -/
lemma ins2_update_i {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (y y' z : kcE3) (r2 : X p) :
    Function.update (ins2 i j' y z r2) i y' = ins2 i j' y' z r2 := by
  dsimp [ins2]
  exact update_kcInsN (n := p + 1) (i := i) y y' (kcInsN p j' (z, r2))

/-- updating the `i.succAbove j'` slot of a double insertion just re-inserts with the new value -/
lemma ins2_update_succ {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (y z z' : kcE3) (r2 : X p) :
    Function.update (ins2 i j' y z r2) (i.succAbove j') z' = ins2 i j' y z' r2 := by
  funext k
  by_cases hk : k = i
  · subst k
    rw [ins2_apply_i]
    dsimp [ins2]
    simp [Function.update_apply, kc_insN_apply_same]
  · by_cases hkj : k = i.succAbove j'
    · subst k
      rw [ins2_apply_succ]
      dsimp [ins2]
      simp [Function.update_apply]
    · rw [Function.update_apply, if_neg hkj]
      rcases Fin.exists_succAbove_eq hk with ⟨l, hl⟩
      rw [← hl]
      have hlne : l ≠ j' := by
        intro hlj
        apply hkj
        rw [← hl, hlj]
      have hA : (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) (i.succAbove l) = (kcInsN p j' (z, r2)) l := by
        exact kc_insN_apply_succ (p + 1) i y (kcInsN p j' (z, r2)) l
      have hC : (kcInsN (p + 1) i (y, kcInsN p j' (z', r2))) (i.succAbove l) = (kcInsN p j' (z', r2)) l := by
        exact kc_insN_apply_succ (p + 1) i y (kcInsN p j' (z', r2)) l
      dsimp [ins2]
      rw [hA, hC]
      rcases Fin.exists_succAbove_eq hlne with ⟨m, hm⟩
      rw [← hm]
      rw [kc_insN_apply_succ, kc_insN_apply_succ]

/-- configurations in the centred box stay in the centred box after two zero insertions -/
lemma rest2_mem_abox {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {r2 : X p} (hr2 : r2 ∈ abox p ℓ) (i : Fin (p + 2))
    (j' : Fin (p + 1)) : rest2 i j' r2 ∈ abox (p + 2) ℓ := by
  intro k
  dsimp [rest2, ins2]
  by_cases hk : k = i
  · subst k
    simpa [kc_insN_apply_same] using (zero_mem_acube hℓ.le : (0 : ℝ³) ∈ acube ℓ)
  · by_cases hkj : k = i.succAbove j'
    · subst k
      rw [kc_insN_apply_succ]
      simpa [kc_insN_apply_same] using (zero_mem_acube hℓ.le : (0 : ℝ³) ∈ acube ℓ)
    · rcases Fin.exists_succAbove_eq hk with ⟨l, hl⟩
      rw [← hl]
      have hlne : l ≠ j' := by
        intro hlj
        apply hkj
        rw [← hl, hlj]
      rw [kc_insN_apply_succ]
      rcases Fin.exists_succAbove_eq hlne with ⟨m, hm⟩
      rw [← hm]
      rw [kc_insN_apply_succ]
      exact hr2 m

/-- The set of ordered pairs `(i,j)` of distinct particle indices. -/
def pairSet (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ : Finset (Fin N × Fin N)).filter (fun p : Fin N × Fin N => p.1 ≠ p.2)

/-! ## Bridge between the product-set integrals and the product of cube measures -/

/-- product-space volume restricted to the product cube equals the product of the two cube
restrictions (measure identity bridging `IntegrableOn` statements over the product set) -/
lemma prod_measure_eq (ℓ : ℝ) :
    (volume : Measure (kcE3 × kcE3)).restrict (acube ℓ ×ˢ acube ℓ) =
      ((volume : Measure kcE3).restrict (acube ℓ)).prod ((volume : Measure kcE3).restrict (acube ℓ)) := by
  rw [MeasureTheory.Measure.volume_eq_prod (kcE3) (kcE3)]
  exact (Measure.prod_restrict (μ := (volume : Measure kcE3)) (ν := (volume : Measure kcE3))
    (s := acube ℓ) (t := acube ℓ)).symm

/-- a function integrable over the product cube is integrable for the product of the cube measures -/
lemma integrable_prod_of_IntegrableOn {ℓ : ℝ} {w : kcE3 × kcE3 → ℝ}
    (hwi : IntegrableOn w (acube ℓ ×ˢ acube ℓ) volume) :
    Integrable w ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) := by
  rw [← prod_measure_eq ℓ]
  simpa [IntegrableOn] using hwi

/-- the product-set integral equals the iterated integral (y outer, z inner) -/
lemma prod_setIntegral_eq_iter1 {ℓ : ℝ} {w : kcE3 × kcE3 → ℝ} (hwm : Measurable w)
    (hwi : IntegrableOn w (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, w (y, z)) = ∫ p in acube ℓ ×ˢ acube ℓ, w p := by
  have hInt : Integrable w ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hwi
  have hF := MeasureTheory.integral_prod (μ := (volume : Measure kcE3).restrict (acube ℓ))
    (ν := (volume : Measure kcE3).restrict (acube ℓ)) (f := fun p : kcE3 × kcE3 => w p) hInt
  rw [← hF]
  rw [← prod_measure_eq ℓ]

/-- the product-set integral equals the iterated integral (z outer, y inner) -/
lemma prod_setIntegral_eq_iter2 {ℓ : ℝ} {w : kcE3 × kcE3 → ℝ} (hwm : Measurable w)
    (hwi : IntegrableOn w (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ z in acube ℓ, ∫ y in acube ℓ, w (y, z)) = ∫ p in acube ℓ ×ˢ acube ℓ, w p := by
  have hInt : Integrable w ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hwi
  have hF := MeasureTheory.integral_prod_symm (μ := (volume : Measure kcE3).restrict (acube ℓ))
    (ν := (volume : Measure kcE3).restrict (acube ℓ)) (f := fun p : kcE3 × kcE3 => w p) hInt
  rw [← hF]
  rw [← prod_measure_eq ℓ]

/-- ae-strong measurability of the one-particle fibre mean `z ↦ ∫_y w1 (z, y)` -/
lemma w1_fibre_aem {ℓ : ℝ} {w1 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1) :
    AEStronglyMeasurable (fun z : kcE3 => ∫ y in acube ℓ, w1 (z, y))
      (volume.restrict (acube ℓ)) := by
  have hInt : AEStronglyMeasurable w1
      ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    hw1m.aestronglyMeasurable
  have h1 : AEStronglyMeasurable (fun z : kcE3 => ∫ y : kcE3, w1 (z, y)
        ∂(volume.restrict (acube ℓ))) (volume.restrict (acube ℓ)) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure kcE3).restrict (acube ℓ))
      (ν := (volume : Measure kcE3).restrict (acube ℓ)) hInt
  simpa using h1

/-- integrability of the one-particle fibre mean `z ↦ ∫_y w1 (z, y)` over the cube -/
lemma w1_fibre {ℓ : ℝ} {w1 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1)
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    Integrable (fun z : kcE3 => ∫ y in acube ℓ, w1 (z, y))
      (volume.restrict (acube ℓ)) := by
  have hInt : Integrable w1 ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) :=
    integrable_prod_of_IntegrableOn hw1i
  have hmain := MeasureTheory.Integrable.integral_prod_left (μ := (volume : Measure kcE3).restrict (acube ℓ))
    (ν := (volume : Measure kcE3).restrict (acube ℓ)) hInt
  simpa using hmain

/-- ae-strong measurability of `g ∘ πᵢ` over the centred `(n+1)`-box -/
lemma aem_comp_coord {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {g : kcE3 → ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict (acube ℓ))) :
    AEStronglyMeasurable (fun x : X (n + 1) => g (x i)) (volume.restrict (abox (n + 1) ℓ)) := by
  let μ' : Measure kcE3 := (volume : Measure kcE3).restrict (acube ℓ)
  let m := AEStronglyMeasurable.mk g hgm
  have hsm : StronglyMeasurable m := hgm.stronglyMeasurable_mk
  have hwitness : StronglyMeasurable (fun x : X (n + 1) => m (x i)) := by
    refine MeasureTheory.StronglyMeasurable.comp_measurable hsm ?_
    fun_prop
  refine ⟨fun x : X (n + 1) => m (x i), hwitness, ?_⟩
  change ∀ᵐ x ∂(volume.restrict (abox (n + 1) ℓ)), g (x i) = m (x i)
  rw [ae_iff]
  have hA0 : μ' {z : kcE3 | g z ≠ m z} = 0 := by
    dsimp [μ', m]
    simpa using (ae_iff.mp hgm.ae_eq_mk)
  have hpi : (Measure.pi (fun _ : Fin (n + 1) => μ')) {x : X (n + 1) | g (x i) ≠ m (x i)} = 0 := by
    rw [show {x : X (n + 1) | g (x i) ≠ m (x i)} =
        (Set.univ : Set (Fin (n + 1))).pi (fun j : Fin (n + 1) =>
          if j = i then {z : kcE3 | g z ≠ m z} else Set.univ) by
      ext x
      simp]
    rw [Measure.pi_pi (μ := fun _ : Fin (n + 1) => μ')]
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simpa using hA0
  simpa [μ', restrict_abox_eq_pi] using hpi

/-- `g ∘ πᵢ` is integrable over the centred `(n+1)`-box when `g` is integrable over the cube -/
lemma integrableOn_comp_coord {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {g : kcE3 → ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict (acube ℓ)))
    (hg : Integrable g (volume.restrict (acube ℓ))) :
    IntegrableOn (fun x : X (n + 1) => g (x i)) (abox (n + 1) ℓ) volume := by
  let μ' : Measure kcE3 := (volume : Measure kcE3).restrict (acube ℓ)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ)
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    dsimp [ν]
    rw [Measure.restrict_apply_univ]
    exact abox_lt_top n ℓ hℓ.le
  letI : IsFiniteMeasure ν := hνfin
  have hg' : Integrable g μ' := by simpa [μ'] using hg
  have hprod : Integrable (fun p : kcE3 × X n => g p.1) (μ'.prod ν) := by
    exact MeasureTheory.Integrable.comp_fst hg' ν
  have hmp : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (abox_peel_mp (n := n) ℓ i)
    simpa [kcInsN, μ', ν] using h
  have hFcomp : Integrable (fun p : kcE3 × X n => g ((kcInsN n i p) i)) (μ'.prod ν) := by
    refine hprod.congr ?_
    apply ae_of_all
    intro p
    exact congrArg g (by simpa using (kc_insN_apply_same n i p.1 p.2).symm)
  have haem : AEStronglyMeasurable (fun x : X (n + 1) => g (x i))
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) :=
    aem_comp_coord i hgm
  exact (hmp.integrable_comp (hg := haem)).mp hFcomp

/-- `PᵢΦ` is constant in the `i`-slot of an inserted configuration -/
lemma aP_fiber_const_one {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) (y : kcE3) (r : X n) :
    aP ℓ i Φ (kcInsN n i (y, r)) = aP ℓ i Φ (kcInsN n i (0, r)) := by
  rw [kcInsN_update_zero i y r]
  exact aP_const_in_coord hℓ i hΦc (kcInsN n i (0, r)) y

/-- `PᵢPⱼΦ` is constant in both distinguished slots of the two-slot fibre -/
lemma aP_pair_fiber_const {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    (j' : Fin (p + 1)) (hj' : i.succAbove j' = j) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) (y z : kcE3) (r2 : X p) :
    aP ℓ i (aP ℓ j Φ) (ins2 i j' y z r2) = aP ℓ i (aP ℓ j Φ) (rest2 i j' r2) := by
  -- constancy in the `i`-slot
  have hupd1 : Function.update (ins2 i j' y z r2) i 0 = ins2 i j' 0 z r2 := by
    exact ins2_update_i i j' y 0 z r2
  have hconst1 := aP_pair_const_in_i hℓ hij hΦc (x := ins2 i j' y z r2) (z := 0)
  rw [hupd1] at hconst1
  -- constancy in the `j = i.succAbove j'`-slot
  have hupd2 : Function.update (ins2 i j' 0 z r2) j 0 = rest2 i j' r2 := by
    rw [← hj']
    exact ins2_update_succ i j' (0 : kcE3) z 0 r2
  have hconst2 := aP_pair_const_in_j hℓ hij hΦc (x := ins2 i j' 0 z r2) (z := 0)
  rw [hupd2] at hconst2
  exact hconst1.symm.trans hconst2.symm

/-- the double-insertion map is measure-preserving from the product of cube measures to the box -/
lemma ins2_flat_mp {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    MeasurePreserving (fun q : (kcE3 × kcE3) × X p =>
        kcInsN (p + 1) i (q.1.1, kcInsN p j' (q.1.2, q.2)))
      (((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))).prod (volume.restrict (abox p ℓ)))
      (volume.restrict (abox (p + 2) ℓ)) := by
  let μ' : Measure kcE3 := (volume : Measure kcE3).restrict (acube ℓ)
  let ν_p : Measure (X p) := (volume : Measure (X p)).restrict (abox p ℓ)
  let ν_p1 : Measure (X (p + 1)) := (volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)
  let ν_p2 : Measure (X (p + 2)) := (volume : Measure (X (p + 2))).restrict (abox (p + 2) ℓ)
  have mp1 : MeasurePreserving (⇑(kcInsN (p + 1) i)) (μ'.prod ν_p1) ν_p2 := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 2) => kcE3) i))
      (abox_peel_mp (n := p + 1) ℓ i)
    simpa [kcInsN, μ', ν_p1, ν_p2] using h
  have mp2 : MeasurePreserving (⇑(kcInsN p j')) (μ'.prod ν_p) ν_p1 := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => kcE3) j'))
      (abox_peel_mp (n := p) ℓ j')
    simpa [kcInsN, μ', ν_p, ν_p1] using h
  have hmid : MeasurePreserving (Prod.map id (⇑(kcInsN p j'))) (μ'.prod (μ'.prod ν_p)) (μ'.prod ν_p1) := by
    exact MeasurePreserving.prod (MeasurePreserving.id μ') mp2
  have hassoc : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc : (kcE3 × kcE3) × X p ≃ᵐ kcE3 × (kcE3 × X p)))
      ((μ'.prod μ').prod ν_p) (μ'.prod (μ'.prod ν_p)) := by
    exact measurePreserving_prodAssoc μ' μ' ν_p
  have htot : MeasurePreserving (fun q : (kcE3 × kcE3) × X p =>
        kcInsN (p + 1) i (q.1.1, kcInsN p j' (q.1.2, q.2)))
      ((μ'.prod μ').prod ν_p) ν_p2 := by
    have hfunext : (fun q : (kcE3 × kcE3) × X p =>
          kcInsN (p + 1) i (q.1.1, kcInsN p j' (q.1.2, q.2))) =
        (⇑(kcInsN (p + 1) i)) ∘ (Prod.map id (⇑(kcInsN p j'))) ∘
          ⇑(MeasurableEquiv.prodAssoc : (kcE3 × kcE3) × X p ≃ᵐ kcE3 × (kcE3 × X p)) := by
      funext q
      rcases q with ⟨⟨y, z⟩, r2⟩
      rfl
    rw [hfunext]
    exact MeasurePreserving.comp mp1 (MeasurePreserving.comp hmid hassoc)
  simpa [μ', ν_p, ν_p1, ν_p2] using htot

/-- `w2 (x i, x j)` is integrable over the centred `(p+2)`-box for distinct `i j` -/
lemma integrableOn_pair_comp {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {w2 : kcE3 × kcE3 → ℝ} (hw2m : Measurable w2)
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X (p + 2) => w2 (x i, x j)) (abox (p + 2) ℓ) volume := by
  rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
  let μ' : Measure kcE3 := (volume : Measure kcE3).restrict (acube ℓ)
  let ν_p : Measure (X p) := (volume : Measure (X p)).restrict (abox p ℓ)
  have hνfin : IsFiniteMeasure ν_p := by
    refine ⟨?_⟩
    dsimp [ν_p]
    rw [Measure.restrict_apply_univ]
    exact abox_lt_top p ℓ hℓ.le
  letI : IsFiniteMeasure ν_p := hνfin
  have hw : Integrable w2 (μ'.prod μ') := by
    dsimp [μ']
    exact integrable_prod_of_IntegrableOn hw2i
  have hflat : Integrable (fun t : (kcE3 × kcE3) × X p => w2 t.1) ((μ'.prod μ').prod ν_p) := by
    exact MeasureTheory.Integrable.comp_fst hw ν_p
  have hmp := ins2_flat_mp (p := p) hℓ i j'
  have hF : Integrable (fun x : X (p + 2) => w2 (x i, x j))
      ((volume : Measure (X (p + 2))).restrict (abox (p + 2) ℓ)) := by
    have hFcomp : Integrable (fun t : (kcE3 × kcE3) × X p =>
        w2 ((kcInsN (p + 1) i (t.1.1, kcInsN p j' (t.1.2, t.2))) i,
            (kcInsN (p + 1) i (t.1.1, kcInsN p j' (t.1.2, t.2))) j)) ((μ'.prod μ').prod ν_p) := by
      refine hflat.congr ?_
      apply ae_of_all
      intro t
      rcases t with ⟨⟨y, z⟩, r2⟩
      change w2 (y, z) = w2 ((kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i,
          (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) j)
      rw [show (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i = y by
            exact kc_insN_apply_same (p + 1) i y (kcInsN p j' (z, r2))]
      rw [show (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) j = z by
            rw [← hj']
            exact (kc_insN_apply_succ (p + 1) i y (kcInsN p j' (z, r2)) j').trans
              (kc_insN_apply_same p j' z r2)]
    have hmeas : Measurable (fun x : X (p + 2) => w2 (x i, x j)) := by
      exact hw2m.comp (by fun_prop : Measurable (fun x : X (p + 2) => (x i, x j)))
    exact (hmp.integrable_comp (hg := hmeas.aestronglyMeasurable)).mp hFcomp
  exact hF

/-- square of the two-particle mean is continuous -/
lemma aP_pair_sq_continuous {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2))
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
  have h1 : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  exact h1.pow 2

/-- square of the one-particle mean is continuous -/
lemma aP_sq_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : Continuous (fun x : X N => (aP ℓ i Φ x) ^ 2) := by
  exact (aP_continuous hℓ i hΦc).pow 2

/-- the pair-value integrand is integrable over the centred box -/
lemma integrableOn_pair_LHS {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ} (hw2m : Measurable w2)
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      (abox (p + 2) ℓ) volume := by
  have hcG : Continuous (fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2) :=
    aP_pair_sq_continuous hℓ i j hΦc
  obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn (s := abox (p + 2) ℓ)
    (f := fun x : X (p + 2) => (aP ℓ i (aP ℓ j Φ) x) ^ 2) hcG.continuousOn
  have hwcomp : IntegrableOn (fun x : X (p + 2) => w2 (x i, x j)) (abox (p + 2) ℓ) volume :=
    integrableOn_pair_comp hℓ i j hij hw2m hw2i
  have hwabs : Integrable (fun x : X (p + 2) => |w2 (x i, x j)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    have hwabs' := hwcomp.abs
    simpa [Real.norm_eq_abs] using hwabs'
  let dom : Set (X (p + 2)) := abox (p + 2) ℓ
  have hdom_m : MeasurableSet dom := abox_measurable (p + 2) ℓ
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (p + 2) ℓ)),
      ‖(aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j)‖ ≤ B * |w2 (x i, x j)| := by
    rw [ae_restrict_iff' hdom_m]
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
    have h2 : Measurable (fun x : X (p + 2) => w2 (x i, x j)) :=
      hw2m.comp (by fun_prop : Measurable (fun x : X (p + 2) => (x i, x j)))
    exact (h1.mul h2).aestronglyMeasurable
  have hdomin : Integrable (fun x : X (p + 2) => B * |w2 (x i, x j)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hwabs.const_mul B
  exact Integrable.mono' hdomin hmeas hbnd

lemma integrableOn_one_LHS {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1)
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    IntegrableOn (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      (abox (n + 1) ℓ) volume := by
  let g : kcE3 → ℝ := fun z => ∫ y in acube ℓ, w1 (z, y)
  have hgc : AEStronglyMeasurable (fun x : X (n + 1) => g (x i))
      (volume.restrict (abox (n + 1) ℓ)) := by
    exact aem_comp_coord i (w1_fibre_aem (w1 := w1) hw1m)
  have hgi : IntegrableOn (fun x : X (n + 1) => g (x i)) (abox (n + 1) ℓ) volume := by
    exact integrableOn_comp_coord hℓ i (w1_fibre_aem (w1 := w1) hw1m) (w1_fibre hw1m hw1i)
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
lemma pair_value_aux {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ} (hw2m : Measurable w2)
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i, x j))
      = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∫ x in abox (p + 2) ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
  rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
  let G : X (p + 2) → ℝ := fun x => (aP ℓ i (aP ℓ j Φ) x) ^ 2
  let T2 : ℝ := ∫ r2 in abox p ℓ, G (rest2 i j' r2)
  have hF1 : IntegrableOn (fun x : X (p + 2) => G x * w2 (x i, x j)) (abox (p + 2) ℓ) volume := by
    simpa [G] using integrableOn_pair_LHS hℓ i j hij hΦc hw2m hw2i
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
            rw [prod_setIntegral_eq_iter2 hw2m hw2i]
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

lemma pair_value {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) {w2 : kcE3 × kcE3 → ℝ} (hw2m : Measurable w2)
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
          exact pair_value_aux (p := p) hℓ i j hij hΦc hw2m hw2i

/-- The Q0 one-body value identity at dimension `n + 1`. -/
lemma one_value_aux {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1)
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
  let G : X (n + 1) → ℝ := fun x => (aP ℓ i Φ x) ^ 2
  let T1 : ℝ := ∫ r in abox n ℓ, G (kcInsN n i (0, r))
  have hF0 : IntegrableOn (fun x : X (n + 1) => G x * (∫ y in acube ℓ, w1 (x i, y)))
      (abox (n + 1) ℓ) volume := by
    simpa [G] using integrableOn_one_LHS hℓ i hΦc hw1m hw1i
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
            rw [prod_setIntegral_eq_iter1 hw1m hw1i]
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

lemma one_value {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {w1 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1)
    (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume) :
    (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      exact one_value_aux (n := n) hℓ i hΦc hw1m hw1i

/-- The summed pair identity: `Σ_{i≠j} ∫ (P_iP_jΦ)²·w₂(xᵢ,xⱼ)`. -/
lemma sumPair_value {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {w2 : kcE3 × kcE3 → ℝ} (hw2m : Measurable w2)
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
          have hk := pair_value (N := N) hℓ (i := p.1) (j := p.2) hp12 hΦc hw2m hw2i
          simpa [c, mul_assoc] using hk
    _ = c * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          dsimp [c]

lemma sumOne_value {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {w1 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1)
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
          have hk := one_value (N := N) hℓ (i := i) hΦc hw1m hw1i
          simpa [c, mul_assoc] using hk
    _ = c * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
          dsimp [c]

lemma q0_expect {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {w1 w2 : kcE3 × kcE3 → ℝ} (hw1m : Measurable w1)
    (hw2m : Measurable w2) (hw1i : IntegrableOn w1 (acube ℓ ×ˢ acube ℓ) volume)
    (hw2i : IntegrableOn w2 (acube ℓ ×ˢ acube ℓ) volume) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1, x p.2))
        - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, w1 (x i, y)))
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) *
            (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
        - μ * (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, w1 p) *
            (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  rw [sumPair_value hℓ hΦc hw2m hw2i, sumOne_value hℓ hΦc hw1m hw1i]
  ring

/-- Support transfer: a function supported in `acube ℓ ×ˢ acube ℓ` has the
same integral over the product cube as over the whole space. -/
lemma prod_integral_eq_full {ℓ : ℝ} {w2 : kcE3 × kcE3 → ℝ} (hw2m : Measurable w2)
    (hw2i : Integrable w2) (hsupp : ∀ p : kcE3 × kcE3, w2 p ≠ 0 → p.1 ∈ acube ℓ ∧ p.2 ∈ acube ℓ) :
    (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) = ∫ p : kcE3 × kcE3, w2 p := by
  have hs : MeasurableSet (acube ℓ ×ˢ acube ℓ) :=
    (acube_measurable ℓ).prod (acube_measurable ℓ)
  have hind : (fun p : kcE3 × kcE3 => (acube ℓ ×ˢ acube ℓ).indicator w2 p) = w2 := by
    rw [Set.indicator_eq_self]
    intro p hp
    exact hsupp p hp
  calc
    (∫ p in acube ℓ ×ˢ acube ℓ, w2 p) = ∫ p : kcE3 × kcE3, (acube ℓ ×ˢ acube ℓ).indicator w2 p := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ p : kcE3 × kcE3, w2 p := by rw [hind]

/-- Support in one coordinate: `f` supported in `acube ℓ` integrates to the
full integral over `acube ℓ`. -/
lemma integral_eq_full_on_acube {ℓ : ℝ} {f : kcE3 → ℝ} (hfm : Measurable f)
    (hfi : Integrable f) (hsupp : ∀ x : kcE3, f x ≠ 0 → x ∈ acube ℓ) :
    (∫ x in acube ℓ, f x) = ∫ x : kcE3, f x := by
  have hind : (fun x : kcE3 => (acube ℓ).indicator f x) = f := by
    rw [Set.indicator_eq_self]
    intro x hx
    exact hsupp x hx
  calc
    (∫ x in acube ℓ, f x) = ∫ x : kcE3, (acube ℓ).indicator f x := by
      rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
    _ = ∫ x : kcE3, f x := by rw [hind]

/-- `χ_ℓ(x) ≠ 0` implies `x ∈ acube ℓ` (support of the scaled bump inside
the centred box). -/
lemma chiScale_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {x : kcE3} (hx : chiScale ℓ x ≠ 0) :
    x ∈ acube ℓ := by
  exact mem_acube_of_norm_le hℓ.le (chiScale_support_le hℓ hx)

/-- The product of two scaled bumps at different points is supported in the
product cube. -/
lemma chiScale_pair_support {ℓ : ℝ} (hℓ : 0 < ℓ) {x y : kcE3}
    (hx : chiScale ℓ x ≠ 0) (hy : chiScale ℓ y ≠ 0) : x ∈ acube ℓ ∧ y ∈ acube ℓ := by
  exact ⟨chiScale_mem_acube hℓ hx, chiScale_mem_acube hℓ hy⟩


end BoseGases
end Submission
