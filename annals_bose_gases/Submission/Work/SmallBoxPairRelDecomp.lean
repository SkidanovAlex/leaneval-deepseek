import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.QDecompSimpler
import Submission.Work.SmallBoxPairDecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-275 — the relative-coordinate (`z = x_i − x_j`) decomposition of the
two-body pairing word `q4PairWord` (D1 step (ii))

D1 (`lm:appbogolubov`) needs the corpus's *position-space* pairing word

    q4PairWord = Σ_{i≠j} ∫_{abox} (P_iP_jΦ)(Q_jQ_iΦ)·w₁(x_i,x_j)

rewritten in the **relative coordinate** `z = x_i − x_j`, so that the Fourier
transform `𝓕W₁` of the renormalised kernel `W₁ = wScaled ℓ (g₀ v h)` can be
inserted (`pairWord_relDecomp` of `SmallBoxPairDecomp`).  This module proves
the exact identity

    q4PairWord = ∫_z W₁(z)·RelDens(z) dz

with `RelDens` the peeled two-body "pair density" (see `q4Fibre`/`relDens`
below).  The chain is:

  * `abox_double_peel_flat` — the two-slot peel with the *rest* coordinate
    INNERMOST (via the measure-preserving `ins2_flat_mp`), i.e.

        ∫_{abox (p+2) ℓ} F = ∫_{acube ℓ}∫_{acube ℓ}∫_{abox p ℓ} F(ins2 i j' y z r2)

    (the order `∫y∫z∫r2` is what makes the pull-out of the `r2`-independent
    kernel factor algebraic);
  * `pairWord_relDecomp` — the general bilinear kernel decomposition
    (`SmallBoxPairDecomp.pairForm_relComp` with an arbitrary two-variable
    density);
  * `q4_pair_fibre` / `sum_q4_fibre` / `q4PairWord_eq_relDens` — the assembly.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The general bilinear relative-coordinate decomposition -/

/-- **The bilinear relative-coordinate decomposition of the pair kernel** for
an arbitrary two-variable density `G` (the `SmallBoxPairDecomp.pairForm_relComp`
identity with `ψ x·φ y` replaced by `G x y`):

    ∫∫ w₁(x,y)·G(x,y) dx dy = ∫_z W₁(z)·(∫_x χ(x)χ(x−z)·G(x,x−z) dx) dz .

This is the position-space form of the Plancherel pairing
`∫_p 𝓕W₁(p)·\overline{𝓕(χ·)}·𝓕(χ·)`: the relative coordinate `z` carries the
renormalised kernel `W₁`, while the `x`-fibre is the pair amplitude. -/
theorem pairWord_relDecomp {ℓ R : ℝ} (_hℓ : 0 < ℓ) (_hR : 0 ≤ R) (_hRℓ : R ≤ ℓ * chiR0)
    {h : ℝ³ → ℝ} {G : ℝ³ → ℝ³ → ℝ}
    (hInt : Integrable (Function.uncurry (fun x y : ℝ³ =>
      chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * G x (x - y)))
      (volume.prod volume)) :
    (∫ x, ∫ y, wPairC ℓ h x y * G x y)
      = ∫ y, wScaled ℓ h y *
          (∫ x, chiScale ℓ x * chiScale ℓ (x - y) * G x (x - y)) := by
  have hA : ∀ x : ℝ³,
      (∫ y, wPairC ℓ h x y * G x y)
        = ∫ y, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * G x (x - y) := by
    intro x
    have hG := integral_sub_left_eq_self
      (fun w : ℝ³ => chiScale ℓ x * wScaled ℓ h w * chiScale ℓ (x - w) * G x (x - w))
      volume x
    have hcongr : (∫ y, chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y * G x y)
        = ∫ y, chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ (x - (x - y)) * G x (x - (x - y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [show x - (x - y) = y from by abel]
    simp only [wPairC, wPair]
    exact hcongr.trans hG
  have hstep1 : (∫ x, ∫ y, wPairC ℓ h x y * G x y)
      = ∫ x, ∫ y, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * G x (x - y) :=
    integral_congr_ae (Filter.Eventually.of_forall hA)
  have hD : ∀ y : ℝ³,
      (∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * G x (x - y))
        = wScaled ℓ h y * (∫ x, chiScale ℓ x * chiScale ℓ (x - y) * G x (x - y)) := by
    intro y
    have h1 : (∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * G x (x - y))
        = ∫ x, wScaled ℓ h y
            * (chiScale ℓ x * chiScale ℓ (x - y) * G x (x - y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h1, integral_const_mul]
  rw [hstep1, integral_integral_swap hInt]
  exact integral_congr_ae (Filter.Eventually.of_forall hD)

/-! ## 2. The two-slot peel with the rest-coordinate innermost -/

/-- **The two-slot peel of the centred box, flat form.**  Isolating the two
distinguished slots `i` and `i.succAbove j'` and writing the remaining `p`
coordinates as the innermost integral:

    ∫_{abox (p+2) ℓ} F = ∫_{acube ℓ}∫_{acube ℓ}∫_{abox p ℓ}
        F (x_{i ↦ y, (i.succAbove j') ↦ z, rest ↦ r2}) .

Derived from the measure-preserving double insertion `ins2_flat_mp` plus
Fubini (the order `∫y∫z∫r2` is the one in which the `r2`-independent kernel
factors pull out algebraically). -/
lemma abox_double_peel_flat {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {F : X (p + 2) → ℝ} (hF : IntegrableOn F (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, F x)
      = ∫ y in acube ℓ, ∫ z in acube ℓ, ∫ r2 in abox p ℓ, F (ins2 i j' y z r2) := by
  let μ' : Measure kcE3 := (volume : Measure kcE3).restrict (acube ℓ)
  let ν : Measure (X p) := (volume : Measure (X p)).restrict (abox p ℓ)
  let ν2 : Measure (X (p + 2)) := (volume : Measure (X (p + 2))).restrict (abox (p + 2) ℓ)
  have hmp : MeasurePreserving (fun q : (kcE3 × kcE3) × X p => ins2 i j' q.1.1 q.1.2 q.2)
      ((μ'.prod μ').prod ν) ν2 := by
    simpa [ins2, μ', ν, ν2] using ins2_flat_mp (p := p) hℓ i j'
  have hF' : Integrable F ν2 := hF
  have hcomp : Integrable (fun q : (kcE3 × kcE3) × X p => F (ins2 i j' q.1.1 q.1.2 q.2))
      ((μ'.prod μ').prod ν) := (hmp.integrable_comp (hg := hF'.aestronglyMeasurable)).mpr hF'
  have h1 : (∫ x in abox (p + 2) ℓ, F x)
      = ∫ q, F (ins2 i j' q.1.1 q.1.2 q.2) ∂((μ'.prod μ').prod ν) := by
    change (∫ x, F x ∂ν2) = _
    rw [← hmp.map_eq]
    exact (MeasureTheory.integral_map hmp.aemeasurable
      (by rw [hmp.map_eq]; exact hF'.aestronglyMeasurable))
  have h2 : (∫ q, F (ins2 i j' q.1.1 q.1.2 q.2) ∂((μ'.prod μ').prod ν))
      = ∫ yz, (∫ r2, F (ins2 i j' yz.1 yz.2 r2) ∂ν) ∂(μ'.prod μ') :=
    MeasureTheory.integral_prod _ hcomp
  have hint2 : Integrable (fun yz : kcE3 × kcE3 => ∫ r2, F (ins2 i j' yz.1 yz.2 r2) ∂ν)
      (μ'.prod μ') :=
    MeasureTheory.Integrable.integral_prod_left (μ := μ'.prod μ') (ν := ν) hcomp
  have h3 : (∫ yz, (∫ r2, F (ins2 i j' yz.1 yz.2 r2) ∂ν) ∂(μ'.prod μ'))
      = ∫ y, (∫ z, (∫ r2, F (ins2 i j' y z r2) ∂ν) ∂μ') ∂μ' :=
    MeasureTheory.integral_prod _ hint2
  rw [h1, h2, h3]


/-! ## 3. The peel with the `r2`-independent kernel pulled out -/

/-- **The two-slot peel with the kernel factor pulled out.**  For a two-variable
kernel `w` and any `G`, isolating the slots `i` and `i.succAbove j'` gives

    ∫_{abox (p+2) ℓ} G x·w (x i) (x (i.succAbove j'))
      = ∫_{acube ℓ}∫_{acube ℓ} w y z·(∫_{abox p ℓ} G (x_{i↦y, (i.succAbove j')↦z}))

(the kernel `w y z` is independent of the innermost rest-coordinate `r2`, so it
pulls out of the peeled fibre with no further Fubini). -/
lemma peel_pair_kernel {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {G : X (p + 2) → ℝ} {w : ℝ³ → ℝ³ → ℝ}
    (hF : IntegrableOn (fun x : X (p + 2) => G x * w (x i) (x (i.succAbove j')))
      (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, G x * w (x i) (x (i.succAbove j')))
      = ∫ y in acube ℓ, ∫ z in acube ℓ, w y z * (∫ r2 in abox p ℓ, G (ins2 i j' y z r2)) := by
  rw [abox_double_peel_flat (p := p) hℓ i j' hF]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with z
  have h1 : (∫ r2 in abox p ℓ, G (ins2 i j' y z r2) * w ((ins2 i j' y z r2) i)
        ((ins2 i j' y z r2) (i.succAbove j')))
      = ∫ r2 in abox p ℓ, G (ins2 i j' y z r2) * w y z := by
    apply integral_congr_ae
    filter_upwards with r2
    rw [ins2_apply_i, ins2_apply_succ]
  rw [h1]
  have h2 : (∫ r2 in abox p ℓ, G (ins2 i j' y z r2) * w y z)
      = ∫ r2 in abox p ℓ, w y z * G (ins2 i j' y z r2) := by
    apply integral_congr_ae
    filter_upwards with r2
    ring
  rw [h2, MeasureTheory.integral_const_mul]

/-- **The per-pair peel of `q4PairWord`'s summand** (with the `PᵢPⱼΦ` factor
made slot-independent by `aP_pair_fiber_const`). -/
lemma q4_pair_peel {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {w : ℝ³ → ℝ³ → ℝ}
    (hF : IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ i (aP ℓ (i.succAbove j') Φ) x) * (aQ ℓ (i.succAbove j') (aQ ℓ i Φ) x)
          * w (x i) (x (i.succAbove j'))) (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ, (aP ℓ i (aP ℓ (i.succAbove j') Φ) x)
        * (aQ ℓ (i.succAbove j') (aQ ℓ i Φ) x) * w (x i) (x (i.succAbove j')))
      = ∫ y in acube ℓ, ∫ z in acube ℓ, w y z *
          (∫ r2 in abox p ℓ, (aP ℓ i (aP ℓ (i.succAbove j') Φ) (rest2 i j' r2))
            * (aQ ℓ (i.succAbove j') (aQ ℓ i Φ) (ins2 i j' y z r2))) := by
  rw [peel_pair_kernel (p := p) hℓ i j'
    (G := fun x => (aP ℓ i (aP ℓ (i.succAbove j') Φ) x) * (aQ ℓ (i.succAbove j') (aQ ℓ i Φ) x)) hF]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  apply integral_congr_ae
  filter_upwards with r2
  rw [aP_pair_fiber_const hℓ i (i.succAbove j') (Fin.ne_succAbove i j') j' rfl hΦc y z r2]

/-! ## 4. The relative-coordinate substitution -/

/-- **The relative-coordinate substitution.**  With a kernel of the form
`χ(y)W(y−z)χ(z)`,

    ∫_{acube ℓ}∫_{acube ℓ} χ(y)W(y−z)χ(z)Q(y,z)
      = ∫_u W(u)·(∫_z χ(z+u)χ(z)Q(z+u,z)) .

This is the passage from the position-space pairing density `Q` to the
relative-coordinate picture in which the Fourier transform `Ŵ` acts.  The
derivation uses only translation invariance (`integral_sub_left_eq_self`,
`integral_add_left_eq_self`), the support of `χ` (`chiScale_mem_acube`), the
pointwise extension of a set integral (no integrability), and ONE Fubini
(whose integrability is the single hypothesis `hInt`). -/
lemma pairWord_subst {ℓ : ℝ} (hℓ : 0 < ℓ) {W : ℝ³ → ℝ} {Q : ℝ³ → ℝ³ → ℝ}
    (hInt : Integrable (Function.uncurry (fun y u : ℝ³ =>
      chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))) (volume.prod volume)) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, chiScale ℓ y * W (y - z) * chiScale ℓ z * Q y z)
      = ∫ u, W u * (∫ z, chiScale ℓ (z + u) * chiScale ℓ z * Q (z + u) z) := by
  have hzero : ∀ z : ℝ³, z ∉ acube ℓ → chiScale ℓ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (chiScale_mem_acube hℓ hne)
  have hb : ∀ y : ℝ³, (∫ z in acube ℓ, chiScale ℓ y * W (y - z) * chiScale ℓ z * Q y z)
      = ∫ z, chiScale ℓ y * W (y - z) * chiScale ℓ z * Q y z := by
    intro y
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
    rw [hzero z hz]
    ring
  have hc : ∀ y : ℝ³, (∫ z, chiScale ℓ y * W (y - z) * chiScale ℓ z * Q y z)
      = ∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u) := by
    intro y
    refine (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)).trans
      (integral_sub_left_eq_self
        (fun w : ℝ³ => chiScale ℓ y * W w * chiScale ℓ (y - w) * Q y (y - w)) volume y)
    simp only [show y - (y - z) = z from by abel]
  have hd : ∀ y : ℝ³, (∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))
      = chiScale ℓ y * ∫ u, W u * chiScale ℓ (y - u) * Q y (y - u) := by
    intro y
    rw [show (∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))
        = ∫ u, chiScale ℓ y * (W u * chiScale ℓ (y - u) * Q y (y - u)) from by
      apply integral_congr_ae
      filter_upwards with u
      ring]
    rw [MeasureTheory.integral_const_mul]
  have he : (∫ y in acube ℓ, chiScale ℓ y * ∫ u, W u * chiScale ℓ (y - u) * Q y (y - u))
      = ∫ y, chiScale ℓ y * ∫ u, W u * chiScale ℓ (y - u) * Q y (y - u) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    rw [hzero y hy, zero_mul]
  have hf : (∫ y, chiScale ℓ y * ∫ u, W u * chiScale ℓ (y - u) * Q y (y - u))
      = ∫ y, ∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [show (∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))
        = ∫ u, chiScale ℓ y * (W u * chiScale ℓ (y - u) * Q y (y - u)) from by
      apply integral_congr_ae
      filter_upwards with u
      ring]
    rw [MeasureTheory.integral_const_mul]
  have hg : (∫ y, ∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))
      = ∫ u, ∫ y, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u) :=
    integral_integral_swap (f := fun y u : ℝ³ =>
      chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u)) hInt
  have hh : (∫ u, ∫ y, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))
      = ∫ u, W u * ∫ z, chiScale ℓ (z + u) * chiScale ℓ z * Q (z + u) z := by
    apply integral_congr_ae
    filter_upwards with u
    rw [show (∫ y, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u))
        = ∫ y, W u * (chiScale ℓ y * chiScale ℓ (y - u) * Q y (y - u)) from by
      apply integral_congr_ae
      filter_upwards with y
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- translation: `y = z + u`
    have hshift := MeasureTheory.integral_add_left_eq_self (μ := (volume : Measure ℝ³))
      (fun w : ℝ³ => chiScale ℓ w * chiScale ℓ (w - u) * Q w (w - u)) u
    have h1 : (∫ z, chiScale ℓ (u + z) * chiScale ℓ (u + z - u) * Q (u + z) (u + z - u))
        = ∫ z, chiScale ℓ z * chiScale ℓ (z - u) * Q z (z - u) := hshift
    have h2 : (∫ z, chiScale ℓ (u + z) * chiScale ℓ (u + z - u) * Q (u + z) (u + z - u))
        = ∫ z, chiScale ℓ (z + u) * chiScale ℓ z * Q (z + u) z := by
      apply integral_congr_ae
      filter_upwards with z
      rw [show u + z = z + u from by abel]
      rw [show z + u - u = z from by abel]
    rw [← h2, h1]
  calc (∫ y in acube ℓ, ∫ z in acube ℓ, chiScale ℓ y * W (y - z) * chiScale ℓ z * Q y z)
      = ∫ y in acube ℓ, ∫ z, chiScale ℓ y * W (y - z) * chiScale ℓ z * Q y z :=
        integral_congr_ae (Filter.Eventually.of_forall hb)
    _ = ∫ y in acube ℓ, chiScale ℓ y * ∫ u, W u * chiScale ℓ (y - u) * Q y (y - u) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun y => (hc y).trans (hd y)))
    _ = ∫ y, chiScale ℓ y * ∫ u, W u * chiScale ℓ (y - u) * Q y (y - u) := he
    _ = ∫ y, ∫ u, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u) := hf
    _ = ∫ u, ∫ y, chiScale ℓ y * W u * chiScale ℓ (y - u) * Q y (y - u) := hg
    _ = ∫ u, W u * ∫ z, chiScale ℓ (z + u) * chiScale ℓ z * Q (z + u) z := hh


/-! ## 5. Sup bounds for the slot operators and the pair fibre -/

/-- A sup bound for a continuous function on the centred box. -/
lemma exists_abox_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ abox N ℓ, |Φ x| ≤ B := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (Real.norm_eq_abs _).symm.trans_le ((hC x hx).trans (le_max_left _ _))⟩

/-- `|QᵢΦ| ≤ 2B` on the box when `|Φ| ≤ B`. -/
lemma aQ_abs_le_two {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B) (hΦB : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) :
    ∀ x ∈ abox N ℓ, |aQ ℓ i Φ x| ≤ 2 * B := by
  intro x hx
  have h1 := aP_abs_le hℓ i hΦc hB hΦB x hx
  have h2 := hΦB x hx
  have h3 : aQ ℓ i Φ x = Φ x - aP ℓ i Φ x := rfl
  rw [h3]
  calc |Φ x - aP ℓ i Φ x| ≤ |Φ x| + |aP ℓ i Φ x| := abs_sub _ _
    _ ≤ B + B := add_le_add h2 h1
    _ = 2 * B := by ring

/-- `|QⱼQᵢΦ| ≤ 4B` on the box when `|Φ| ≤ B`. -/
lemma aQ_pair_abs_le {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) {Φ : X (p + 2) → ℝ}
    (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B)
    (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) :
    ∀ x ∈ abox (p + 2) ℓ, |aQ ℓ j (aQ ℓ i Φ) x| ≤ 4 * B := by
  have h1 : ∀ x ∈ abox (p + 2) ℓ, |aQ ℓ i Φ x| ≤ 2 * B :=
    aQ_abs_le_two hℓ i hΦc hB hΦB
  have h2 : ∀ x ∈ abox (p + 2) ℓ, |aQ ℓ j (aQ ℓ i Φ) x| ≤ 2 * (2 * B) :=
    aQ_abs_le_two hℓ j (aQ_continuous hℓ i hΦc) (by linarith) h1
  intro x hx
  have h3 := h2 x hx
  linarith

/-- Real measure of the centred `N`-box: `(ℓ³)^N`. -/
lemma real_volume_abox (N : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ((volume : Measure (X N)).restrict (abox N ℓ)).real Set.univ = (ℓ ^ 3) ^ N := by
  rw [MeasureTheory.measureReal_def]
  rw [Measure.restrict_apply_univ, abox_volume N ℓ hℓ]
  exact ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hℓ 3) N)

/-- A double insertion of cube points lies in the box. -/
lemma ins2_mem_abox {p : ℕ} {ℓ : ℝ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    {y z : ℝ³} (hy : y ∈ acube ℓ) (hz : z ∈ acube ℓ) {r2 : X p} (hr2 : r2 ∈ abox p ℓ) :
    ins2 i j' y z r2 ∈ abox (p + 2) ℓ := by
  intro k
  dsimp [ins2]
  by_cases hk : k = i
  · subst k
    simpa [kc_insN_apply_same] using hy
  · by_cases hkj : k = i.succAbove j'
    · subst k
      rw [kc_insN_apply_succ]
      simpa [kc_insN_apply_same] using hz
    · rcases Fin.exists_succAbove_eq hk with ⟨l, hl⟩
      rw [← hl]
      have hlne : l ≠ j' := by
        intro hlj
        exact hkj (by rw [← hl, hlj])
      rw [kc_insN_apply_succ]
      rcases Fin.exists_succAbove_eq hlne with ⟨m, hm⟩
      rw [← hm]
      rw [kc_insN_apply_succ]
      exact hr2 m

/-- The inverse of `Fin.succAbove`: the unique `j'` with `i.succAbove j' = j`. -/
noncomputable def sucAboveInv {n : ℕ} (i j : Fin (n + 1)) (h : i ≠ j) : Fin n :=
  Classical.choose (Fin.exists_succAbove_eq (x := j) (y := i) h.symm)

/-- The defining property of `sucAboveInv`. -/
lemma succAbove_sucAboveInv {n : ℕ} (i j : Fin (n + 1)) (h : i ≠ j) :
    i.succAbove (sucAboveInv i j h) = j :=
  Classical.choose_spec (Fin.exists_succAbove_eq (x := j) (y := i) h.symm)

/-- **The peeled pair fibre** `Q_{ij}(y,z)`: for distinct slots `i ≠ j`, the
integral over the remaining `p` coordinates of `PᵢPⱼΦ·QⱼQᵢΦ` with the two
distinguished slots set to `y` and `z`; `0` for `i = j`. -/
noncomputable def pairFibreFun {p : ℕ} (ℓ : ℝ) (Φ : X (p + 2) → ℝ) (i j : Fin (p + 2))
    (y z : ℝ³) : ℝ :=
  if hij : i ≠ j then
    ∫ r2 in abox p ℓ, (aP ℓ i (aP ℓ j Φ) (rest2 i (sucAboveInv i j hij) r2))
      * (aQ ℓ j (aQ ℓ i Φ) (ins2 i (sucAboveInv i j hij) y z r2))
  else 0

/-- **The pair fibre is bounded** on the cube: for `y, z ∈ acube ℓ` the peeled
pair integral is bounded by `4B²ℓ^{3p}`. -/
lemma pairFibreFun_abs_le {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B)
    (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) {y z : ℝ³} (hy : y ∈ acube ℓ)
    (hz : z ∈ acube ℓ) :
    |pairFibreFun ℓ Φ i j y z| ≤ 4 * B ^ 2 * ℓ ^ (3 * p) := by
  rw [pairFibreFun, dif_pos hij]
  set j' := sucAboveInv i j hij with hj'def
  have hPi : ∀ x ∈ abox (p + 2) ℓ, |aP ℓ j Φ x| ≤ B :=
    fun x hx => aP_abs_le hℓ j hΦc hB hΦB x hx
  have hAb : ∀ r2 ∈ abox p ℓ, |aP ℓ i (aP ℓ j Φ) (rest2 i j' r2)| ≤ B :=
    fun r2 hr2 => aP_abs_le hℓ i (aP_continuous hℓ j hΦc) hB hPi _
      (rest2_mem_abox hℓ hr2 i j')
  have hCb : ∀ r2 ∈ abox p ℓ,
      |aQ ℓ j (aQ ℓ i Φ) (ins2 i j' y z r2)| ≤ 4 * B :=
    fun r2 hr2 => aQ_pair_abs_le hℓ i j hΦc hB hΦB _
      (ins2_mem_abox i j' hy hz hr2)
  have hpt : ∀ᵐ r2 ∂((volume : Measure (X p)).restrict (abox p ℓ)),
      ‖(aP ℓ i (aP ℓ j Φ) (rest2 i j' r2))
        * (aQ ℓ j (aQ ℓ i Φ) (ins2 i j' y z r2))‖ ≤ 4 * B ^ 2 := by
    filter_upwards [ae_restrict_mem (abox_measurable p ℓ)] with r2 hr2
    rw [Real.norm_eq_abs, abs_mul]
    calc |aP ℓ i (aP ℓ j Φ) (rest2 i j' r2)|
          * |aQ ℓ j (aQ ℓ i Φ) (ins2 i j' y z r2)|
        ≤ B * (4 * B) := mul_le_mul (hAb r2 hr2) (hCb r2 hr2) (abs_nonneg _) hB
      _ = 4 * B ^ 2 := by ring
  have _ : IsFiniteMeasure ((volume : Measure (X p)).restrict (abox p ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top p ℓ hℓ.le⟩
  calc |∫ r2 in abox p ℓ, (aP ℓ i (aP ℓ j Φ) (rest2 i j' r2))
        * (aQ ℓ j (aQ ℓ i Φ) (ins2 i j' y z r2))|
      = ‖∫ r2 in abox p ℓ, (aP ℓ i (aP ℓ j Φ) (rest2 i j' r2))
        * (aQ ℓ j (aQ ℓ i Φ) (ins2 i j' y z r2))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ (4 * B ^ 2) * ((volume : Measure (X p)).restrict (abox p ℓ)).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hpt
    _ = 4 * B ^ 2 * ℓ ^ (3 * p) := by
        rw [real_volume_abox p ℓ hℓ.le, pow_mul]

/-! ## 6. The assembly: `q4PairWord` in relative coordinates -/

/-- **The per-pair contribution to `q4PairWord` in relative coordinates.**  For
distinct slots `i ≠ j` this is `∫_u W(u)·(∫_z χ(z+u)χ(z)·Q(z+u,z))` with `Q`
the peeled pair fibre, and `0` for `i = j` (never a member of `pairSet`). -/
noncomputable def pairRelTerm {p : ℕ} (ℓ : ℝ) (Φ : X (p + 2) → ℝ) (W : ℝ³ → ℝ)
    (i j : Fin (p + 2)) : ℝ :=
  if _hij : i ≠ j then
    ∫ u, W u * (∫ z, chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z)
  else 0

/-- **The relative-coordinate decomposition of `q4PairWord`** (D1 step (ii)).

    q4PairWord = Σ_{i≠j} ∫_u W₁(u)·(∫_z χ(z+u)χ(z)·Q(z+u,z)) ,

with `W₁ = wScaled ℓ (g₀ v h)` the χ-renormalised scattering kernel and `Q`
the peeled pair fibre (`pairFibreFun`).  The relative coordinate `u = x_i − x_j`
is now the variable carrying the kernel, which is exactly the form in which the
Fourier transform `Ŵ₁` (and hence the anti-diagonal Bogoliubov pairing
`b_u†b_{−u}†`) can be inserted.

The hypotheses `hFint`/`hInt` are integrability side conditions (the pair
integrand on the box, resp. the relative-coordinate integrand on `ℝ⁶`); they
are discharged in `q4PairWord_eq_relDens_auto`. -/
theorem q4PairWord_eq_relDens {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (_hR : 0 < R)
    (_hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (_hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    (hFint : ∀ (i j : Fin (p + 2)) (_ : i ≠ j), IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPairC ℓ (g0 v h) (x i) (x j))
      (abox (p + 2) ℓ) volume)
    (hInt : ∀ (i j : Fin (p + 2)) (_ : i ≠ j), Integrable (Function.uncurry (fun y u : ℝ³ =>
        chiScale ℓ y * wScaled ℓ (g0 v h) u * chiScale ℓ (y - u)
          * pairFibreFun ℓ Φ i j y (y - u)))
      (volume.prod volume)) :
    q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = ∑ q ∈ pairSet (p + 2), pairRelTerm ℓ Φ (wScaled ℓ (g0 v h)) q.1 q.2 := by
  rw [q4PairWord]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
  have hj' : q.1.succAbove (sucAboveInv q.1 q.2 hqne) = q.2 :=
    succAbove_sucAboveInv q.1 q.2 hqne
  have hprt : pairRelTerm ℓ Φ (wScaled ℓ (g0 v h)) q.1 q.2
      = ∫ u, wScaled ℓ (g0 v h) u
          * (∫ z, chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ q.1 q.2 (z + u) z) := by
    unfold pairRelTerm
    rw [dif_pos hqne]
  rw [hprt]
  have hpeel := q4_pair_peel (p := p) hℓ q.1 (sucAboveInv q.1 q.2 hqne) hΦc
    (w := wPairC ℓ (g0 v h)) (by rw [hj']; exact hFint q.1 q.2 hqne)
  rw [hj'] at hpeel
  have hsub := pairWord_subst (ℓ := ℓ) hℓ (W := wScaled ℓ (g0 v h))
    (Q := pairFibreFun ℓ Φ q.1 q.2) (hInt q.1 q.2 hqne)
  have hsub' : (∫ y in acube ℓ, ∫ z in acube ℓ, wPairC ℓ (g0 v h) y z
        * (∫ r2 in abox p ℓ, (aP ℓ q.1 (aP ℓ q.2 Φ) (rest2 q.1 (sucAboveInv q.1 q.2 hqne) r2))
          * (aQ ℓ q.2 (aQ ℓ q.1 Φ) (ins2 q.1 (sucAboveInv q.1 q.2 hqne) y z r2))))
      = ∫ u, wScaled ℓ (g0 v h) u
          * (∫ z, chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ q.1 q.2 (z + u) z) := by
    simpa only [wPairC, wPair, pairFibreFun, dif_pos hqne] using hsub
  rw [hpeel]
  exact hsub'

/-! ## 7. Discharge of the integrability side conditions -/

/-- **Integrability of the box pair integrand** (`hFint` of
`q4PairWord_eq_relDens`).  Domination by `4B²·chiSup·2(∫χ²)^{-1/2}·|g₀(xᵢ−xⱼ)|`
with `|g₀(xᵢ−xⱼ)|` integrable over the box (`integrableOn_abs_sub_abox`). -/
lemma q4_pair_integrable {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ * chiR0)
    {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (i j : Fin (p + 2)) (hij : i ≠ j) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    {B : ℝ} (hB : 0 ≤ B) (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPairC ℓ (g0 v h) (x i) (x j))
      (abox (p + 2) ℓ) volume := by
  have hg0 : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hP : ∀ x ∈ abox (p + 2) ℓ, |aP ℓ i (aP ℓ j Φ) x| ≤ B :=
    fun x hx => aP_abs_le hℓ i (aP_continuous hℓ j hΦc) hB
      (fun y hy => aP_abs_le hℓ j hΦc hB hΦB y hy) x hx
  have hQ : ∀ x ∈ abox (p + 2) ℓ, |aQ ℓ j (aQ ℓ i Φ) x| ≤ 4 * B :=
    aQ_pair_abs_le hℓ i j hΦc hB hΦB
  have hC0 : (0 : ℝ) ≤ chiSup * (2 * (Real.sqrt chiNormSq)⁻¹) :=
    mul_nonneg (le_of_lt chiSup_pos)
      (mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hWb : ∀ x : X (p + 2), |wPairC ℓ (g0 v h) (x i) (x j)|
      ≤ chiSup * (2 * (Real.sqrt chiNormSq)⁻¹) * |g0 v h (x i - x j)| :=
    fun x => wPair_abs_bound_le hℓ hgsupp hRℓ (x i) (x j)
  have hbase : IntegrableOn (fun x : X (p + 2) => |g0 v h (x i - x j)|)
      (abox (p + 2) ℓ) volume :=
    integrableOn_abs_sub_abox hℓ hg0 i j hij
  have hmaj : Integrable (fun x : X (p + 2) =>
      ((4 * B ^ 2) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹))) * |g0 v h (x i - x j)|)
      (volume.restrict (abox (p + 2) ℓ)) :=
    hbase.integrable.const_mul _
  have haesm : AEStronglyMeasurable (fun x : X (p + 2) =>
      (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPairC ℓ (g0 v h) (x i) (x j))
      (volume.restrict (abox (p + 2) ℓ)) := by
    have h1 : AEStronglyMeasurable (fun x : X (p + 2) => aP ℓ i (aP ℓ j Φ) x)
        (volume.restrict (abox (p + 2) ℓ)) :=
      (aP_continuous hℓ i (aP_continuous hℓ j hΦc)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : X (p + 2) => aQ ℓ j (aQ ℓ i Φ) x)
        (volume.restrict (abox (p + 2) ℓ)) :=
      (aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun x : X (p + 2) => wPair ℓ (g0 v h) (x i) (x j))
        (volume.restrict (abox (p + 2) ℓ)) := aesm_wPair_pair hℓ hg0 i j hij
    exact (h1.mul h2).mul (by simpa [wPairC] using h3)
  refine Integrable.mono' hmaj haesm ?_
  filter_upwards [ae_restrict_mem (abox_measurable (p + 2) ℓ)] with x hx
  have h1 : ‖(aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPairC ℓ (g0 v h) (x i) (x j)‖
      = |aP ℓ i (aP ℓ j Φ) x| * |aQ ℓ j (aQ ℓ i Φ) x|
        * |wPairC ℓ (g0 v h) (x i) (x j)| := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
  rw [h1]
  calc |aP ℓ i (aP ℓ j Φ) x| * |aQ ℓ j (aQ ℓ i Φ) x| * |wPairC ℓ (g0 v h) (x i) (x j)|
      ≤ B * (4 * B) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹) * |g0 v h (x i - x j)|) :=
        mul_le_mul (mul_le_mul (hP x hx) (hQ x hx) (abs_nonneg _) hB) (hWb x) (abs_nonneg _)
          (mul_nonneg hB (by linarith : (0 : ℝ) ≤ 4 * B))
    _ = ((4 * B ^ 2) * (chiSup * (2 * (Real.sqrt chiNormSq)⁻¹))) * |g0 v h (x i - x j)| := by ring

/-- **Integrability of the relative-coordinate integrand** (`hInt` of
`q4PairWord_eq_relDens`).  The `χ`-factors confine `y` and `y−u` to the cube,
where the peeled pair fibre is bounded by `4B²ℓ^{3p}` (`pairFibreFun_abs_le`);
the majorant `C·1_{acube}⊗|g₀|` is a product of `L¹` functions. -/
lemma q4_subst_integrable {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ * chiR0)
    {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (i j : Fin (p + 2)) (hij : i ≠ j) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    {B : ℝ} (hB : 0 ≤ B) (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) :
    Integrable (Function.uncurry (fun y u : ℝ³ =>
      chiScale ℓ y * wScaled ℓ (g0 v h) u * chiScale ℓ (y - u)
        * pairFibreFun ℓ Φ i j y (y - u)))
      (volume.prod volume) := by
  have hg0 : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hWb : ∀ u : ℝ³, |wScaled ℓ (g0 v h) u| ≤ 2 * |g0 v h u| :=
    fun u => wScaled_abs_le_two hℓ hR.le hRℓ hgsupp u
  have hchi : ∀ y : ℝ³, |chiScale ℓ y| ≤ chiSup := fun y => abs_chiScale_le_chiSup ℓ y
  have hχnn : ∀ y : ℝ³, 0 ≤ chiScale ℓ y := fun y => chiScale_nonneg ℓ y
  have hchiSup0 : (0 : ℝ) ≤ chiSup := le_of_lt chiSup_pos
  have hB2 : (0 : ℝ) ≤ 4 * B ^ 2 * ℓ ^ (3 * p) :=
    mul_nonneg (by positivity) (pow_nonneg hℓ.le _)
  have hR2 : Measurable (fun q : (ℝ³ × ℝ³) × X p => rest2 i (sucAboveInv i j hij) q.2) := by
    have hj : Continuous (fun q : (ℝ³ × ℝ³) × X p =>
        kcInsN p (sucAboveInv i j hij) ((0 : ℝ³), q.2)) :=
      (kcInsN_cont (sucAboveInv i j hij)).comp (by fun_prop)
    exact ((kcInsN_cont (i : Fin (p + 2))).comp
      (continuous_const.prodMk hj)).measurable
  have hIns : Measurable (fun q : (ℝ³ × ℝ³) × X p =>
      ins2 i (sucAboveInv i j hij) q.1.1 (q.1.1 - q.1.2) q.2) := by
    have h1 : Continuous (fun q : (ℝ³ × ℝ³) × X p =>
        kcInsN p (sucAboveInv i j hij) (q.1.1 - q.1.2, q.2)) :=
      (kcInsN_cont (sucAboveInv i j hij)).comp (by fun_prop)
    exact ((kcInsN_cont (i : Fin (p + 2))).comp (by fun_prop)).measurable
  have hmeasm : Measurable (fun q : (ℝ³ × ℝ³) × X p =>
      (aP ℓ i (aP ℓ j Φ) (rest2 i (sucAboveInv i j hij) q.2)
        * aQ ℓ j (aQ ℓ i Φ)
            (ins2 i (sucAboveInv i j hij) q.1.1 (q.1.1 - q.1.2) q.2) : ℝ)) :=
    ((aP_continuous hℓ i (aP_continuous hℓ j hΦc)).measurable.comp hR2).mul
      ((aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)).measurable.comp hIns)
  have hQaesm : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      pairFibreFun ℓ Φ i j q.1 (q.1 - q.2)) (volume.prod volume) := by
    have := hmeasm.aestronglyMeasurable.integral_prod_right'
      (μ := volume.prod volume) (ν := (volume : Measure (X p)).restrict (abox p ℓ))
    simpa only [pairFibreFun, dif_pos hij] using this
  have hInd : Integrable (Set.indicator (acube ℓ) (fun _ : ℝ³ => (1 : ℝ)))
      (volume : Measure ℝ³) :=
    (integrableOn_const (μ := (volume : Measure ℝ³)) (s := acube ℓ) (C := (1 : ℝ))
      (hs := ne_of_lt (acube_lt_top ℓ hℓ.le)) (hC := by simp)).integrable_indicator
      (acube_measurable ℓ)
  have hmaj : Integrable (Function.uncurry (fun y u : ℝ³ =>
      (2 * chiSup * (chiSup * (4 * B ^ 2 * ℓ ^ (3 * p))))
        * Set.indicator (acube ℓ) (fun _ : ℝ³ => (1 : ℝ)) y * |g0 v h u|))
      (volume.prod volume) :=
    (hInd.const_mul _).mul_prod hg0.abs
  have hmeas : AEStronglyMeasurable (Function.uncurry (fun y u : ℝ³ =>
      chiScale ℓ y * wScaled ℓ (g0 v h) u * chiScale ℓ (y - u)
        * pairFibreFun ℓ Φ i j y (y - u))) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => chiScale ℓ q.1)
        (volume.prod volume) :=
      ((chiScale_continuous ℓ).comp continuous_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => wScaled ℓ (g0 v h) q.2)
        (volume.prod volume) :=
      (hg0.aemeasurable.div (convScale_continuous ℓ).aemeasurable).aestronglyMeasurable.comp_snd
    have h3 : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => chiScale ℓ (q.1 - q.2))
        (volume.prod volume) :=
      ((chiScale_continuous ℓ).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    exact ((h1.mul h2).mul h3).mul (by simpa only [Function.uncurry] using hQaesm)
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards with q
  simp only [Function.uncurry]
  have hmajnn : (0 : ℝ) ≤ (2 * chiSup * (chiSup * (4 * B ^ 2 * ℓ ^ (3 * p))))
      * Set.indicator (acube ℓ) (fun _ : ℝ³ => (1 : ℝ)) q.1 * |g0 v h q.2| :=
    mul_nonneg (mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) q.1)) (abs_nonneg _)
  by_cases hy : chiScale ℓ q.1 = 0
  · have hf0 : chiScale ℓ q.1 * wScaled ℓ (g0 v h) q.2 * chiScale ℓ (q.1 - q.2)
        * pairFibreFun ℓ Φ i j q.1 (q.1 - q.2) = 0 := by
      rw [hy]; ring
    rw [hf0, norm_zero]
    exact hmajnn
  · by_cases hz : chiScale ℓ (q.1 - q.2) = 0
    · have hf0 : chiScale ℓ q.1 * wScaled ℓ (g0 v h) q.2 * chiScale ℓ (q.1 - q.2)
          * pairFibreFun ℓ Φ i j q.1 (q.1 - q.2) = 0 := by
        rw [hz]; ring
      rw [hf0, norm_zero]
      exact hmajnn
    · have hb1 : q.1 ∈ acube ℓ := chiScale_mem_acube hℓ hy
      have hb2 : q.1 - q.2 ∈ acube ℓ := chiScale_mem_acube hℓ hz
      have hind : Set.indicator (acube ℓ) (fun _ : ℝ³ => (1 : ℝ)) q.1 = 1 :=
        Set.indicator_of_mem hb1 _
      have hQb : |pairFibreFun ℓ Φ i j q.1 (q.1 - q.2)| ≤ 4 * B ^ 2 * ℓ ^ (3 * p) :=
        pairFibreFun_abs_le (p := p) hℓ i j hij hΦc hB hΦB hb1 hb2
      have hcy : chiScale ℓ q.1 ≤ chiSup := by
        rw [← abs_of_nonneg (hχnn q.1)]; exact hchi q.1
      have hcz : chiScale ℓ (q.1 - q.2) ≤ chiSup := by
        rw [← abs_of_nonneg (hχnn (q.1 - q.2))]; exact hchi (q.1 - q.2)
      rw [hind, mul_one, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (hχnn q.1), abs_of_nonneg (hχnn (q.1 - q.2))]
      have hstep : chiScale ℓ q.1 * |wScaled ℓ (g0 v h) q.2| * chiScale ℓ (q.1 - q.2)
          * |pairFibreFun ℓ Φ i j q.1 (q.1 - q.2)|
          ≤ chiSup * (2 * |g0 v h q.2|) * chiSup * (4 * B ^ 2 * ℓ ^ (3 * p)) :=
        mul_le_mul (mul_le_mul (mul_le_mul hcy (hWb q.2) (abs_nonneg _) hchiSup0)
          hcz (hχnn (q.1 - q.2))
          (mul_nonneg hchiSup0 (mul_nonneg (by norm_num) (abs_nonneg _)))) hQb
          (abs_nonneg _)
          (mul_nonneg (mul_nonneg hchiSup0 (mul_nonneg (by norm_num) (abs_nonneg _))) hchiSup0)
      have hstep2 : chiSup * (2 * |g0 v h q.2|) * chiSup * (4 * B ^ 2 * ℓ ^ (3 * p))
          = (2 * chiSup * (chiSup * (4 * B ^ 2 * ℓ ^ (3 * p)))) * |g0 v h q.2| := by ring
      exact hstep.trans (le_of_eq hstep2)

/-- **The relative-coordinate decomposition of `q4PairWord`** with the
integrability side conditions discharged from continuity of `Φ` alone. -/
theorem q4PairWord_eq_relDens_auto {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = ∑ q ∈ pairSet (p + 2), pairRelTerm ℓ Φ (wScaled ℓ (g0 v h)) q.1 q.2 := by
  obtain ⟨B, hB, hΦB⟩ := exists_abox_bound hℓ hΦc
  exact q4PairWord_eq_relDens hℓ hR hRℓ hv_supp h hΦc
    (fun i j hij => q4_pair_integrable hℓ hR hRℓ hv_supp h i j hij hΦc hB hΦB)
    (fun i j hij => q4_subst_integrable hℓ hR hRℓ hv_supp h i j hij hΦc hB hΦB)

/-! ## 8. The slot fibre of `Qᵢ` has zero mean (the `Q_B`-cancellation seed) -/

/-- **`aQ ℓ i Φ` has zero fibre mean in the slot it projects out.**  For any
configuration `r` of the remaining slots, `∫_{acube ℓ} (aQ ℓ i Φ)(x_{i↦y}) dy = 0`.

This is the analytic content of FS's `Q_B` (box-mean-free) structure: the `k = 0`
Neumann mode of a `Q`-projected function vanishes, which is what makes the
`b_p` corrections cancel in the momentum resolution of `A₂` (D1 item (c2)). -/
lemma aQ_slot_fibre_mean_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ) (r : X n) :
    (∫ y in acube ℓ, aQ ℓ i Φ (kcInsN n i (y, r))) = 0 := by
  have hconst : ∀ y : ℝ³,
      aP ℓ i Φ (kcInsN n i (y, r)) = aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r)) := by
    intro y
    have h := aP_const_in_coord hℓ i hΦc (kcInsN n i ((0 : ℝ³), r)) y
    rwa [← kcInsN_update_zero i y r] at h
  have h1 : ∀ y : ℝ³, aQ ℓ i Φ (kcInsN n i (y, r))
      = Φ (kcInsN n i (y, r)) - aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r)) := by
    intro y
    unfold aQ
    rw [hconst y]
  have hUcont : Continuous (fun y : ℝ³ => kcInsN n i (y, r)) :=
    (kcInsN_cont i).comp (continuous_id.prodMk continuous_const)
  have hci : Continuous (fun y : ℝ³ => Φ (kcInsN n i (y, r))) := hΦc.comp hUcont
  have hfib : (∫ y in acube ℓ, Φ (kcInsN n i (y, r)))
      = ℓ ^ 3 * aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r)) := by
    have hdef : aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r))
        = (1 / ℓ ^ 3) * ∫ y in acube ℓ, Φ (kcInsN n i (y, r)) := by
      dsimp only [aP]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      rw [← kcInsN_update_zero i y r]
    rw [hdef]
    field_simp
  have hint1 : IntegrableOn (fun y : ℝ³ => Φ (kcInsN n i (y, r))) (acube ℓ) volume :=
    hci.continuousOn.integrableOn_compact (acube_compact hℓ)
  have hint2 : IntegrableOn (fun _ : ℝ³ => aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r)))
      (acube ℓ) volume :=
    integrableOn_const (μ := (volume : Measure ℝ³)) (s := acube ℓ)
      (C := aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r)))
      (hs := ne_of_lt (acube_lt_top ℓ hℓ.le)) (hC := by simp)
  calc (∫ y in acube ℓ, aQ ℓ i Φ (kcInsN n i (y, r)))
      = ∫ y in acube ℓ, (Φ (kcInsN n i (y, r)) - aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r))) :=
        integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = (∫ y in acube ℓ, Φ (kcInsN n i (y, r)))
          - ∫ _y in acube ℓ, aP ℓ i Φ (kcInsN n i ((0 : ℝ³), r)) :=
        MeasureTheory.integral_sub hint1 hint2
    _ = 0 := by
        rw [hfib, integral_const_acube ℓ hℓ]
        ring

end BoseGases
end Submission
