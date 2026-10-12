import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.CrudePlanAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.rpsi_ge_affine`

FS `thm:aprioriHLambda`, step 4, *first half*: the a-priori remainder `R_Ψ` dominates
the affine function of the state-averaged density `wbSig` and of the localised mass total
`wbW`,

  `(μ/3)·(‖Φ‖²·wbSig) − μ²·(‖Φ‖²·wbW) ≤ R_Ψ`.

**FS's argument.**  Write `g = wbMass`, `t = wbDens` (the `χ_B`-weighted local density),
`F = psiWeight 1 μ`, and recall

* `R_Ψ = ∫_{I₋} g u · ∫_{abox} Φ² · F(t(u,x)) du` where `t(u,x) = nCountB u x / chiMass u`,
* `wbW = ∫_{I₋} g`, `wbSig = ∫_{I₋} g·t` with `t u = (∫ Φ²·nCountB u)/(‖Φ‖²·chiMass u)`.

Two ingredients:

1. **(Jensen in `x`, FS step 4)**  `‖Φ‖²·F(t u) ≤ ∫_{abox} Φ²·F(t(u,x))` —
   `Work.BoseFixB1.WB.jensen_integrated`, obtained from the weighted Cauchy–Schwarz
   inequality for the probability density `Φ²/‖Φ‖²`.
2. **(The affine lower bound on `F`)**  for `t ≥ 0`, `μ > 0`,
   `(μ/3)·t − μ² ≤ F(t)`  (`psiWeight_ge_affine` below).  Substituting the two forms
   `F(t) = (t−μ)²/(1+t/μ) = μ(t−μ)²/(t+μ)` this is
   `((μ/3)t−μ²)(1+t/μ) ≤ (t−μ)²`, i.e. `t²/3 − 2μt/3 − μ² ≤ (t−μ)²`, whose difference is
   `(2/3)((t−μ)² + 2μ²) ≥ 0`.

Multiplying (2) by `g ≥ 0`, integrating in `u` against `g` and combining with (1) gives the
claim.  The integration is legitimate because `g`, `g·t` and `g·F(t)` are all integrable on
`I₋` (`integrableOn_wbMass_mul_wbDens`, `integrableOn_wbMass_mul_psiDens`, using the
domination `g ≤ C₁·(a v)·χ_B` of `hmassU`); they are the three integrability inputs of the
Cauchy–Schwarz window `Work.BoseFixB1.WB.cs_apply` and are extracted here as standalone
lemmas.

The abstract assembly is `affine_le_of_psiWeight`; `rpsi_ge_affine` is its instantiation at
`g = wbMass`, `t = wbDens`, `G = I₋`, `N = ‖Φ‖²`, `P = R_Ψ`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.BoseFixB1 Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. The affine lower bound on FS's weight `F` -/

/-- **FS's `F` dominates the affine function `(μ/3)t − μ²` on the physical half-line.**
With `F = psiWeight 1 μ`, `F(t) = (t−μ)²/(1+t/μ)`, and the claimed inequality is
equivalent (after multiplying by the positive denominator `1+t/μ`) to
`t²/3 − 2μt/3 − μ² ≤ (t−μ)²`, i.e. `0 ≤ (2/3)((t−μ)² + 2μ²)`. -/
theorem psiWeight_ge_affine {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    (μ / 3) * t - μ ^ 2 ≤ Work.SmallBoxSliding.psiWeight 1 μ t := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have h : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
    linarith
  rw [le_div_iff₀ hden]
  have hkey : ((μ / 3) * t - μ ^ 2) * (1 + t * μ⁻¹)
      = t ^ 2 / 3 - 2 * μ * t / 3 - μ ^ 2 := by
    field_simp
    ring
  rw [hkey]
  nlinarith [sq_nonneg (t - μ), sq_nonneg μ]

/-! ## 2. The abstract assembly -/

/-- **The affine lower bound for an abstract `u`-integral.**

Let `G` be a measurable set, `t, g ≥ 0` on `G`, with `g`, `g·t` and `g·F(t)` integrable on
`G`, where `F = psiWeight 1 μ`, `μ > 0`.  If `N > 0` and `N·∫_G g·F(t) ≤ P`, then

  `(μ/3)·(N·∫_G g·t) − μ²·(N·∫_G g) ≤ P`.

This is `rpsi_ge_affine` with the state-specific objects abstracted away: the pointwise
bound `F(t) ≥ (μ/3)t − μ²` (`psiWeight_ge_affine`), multiplied by `g ≥ 0` and integrated. -/
theorem affine_le_of_psiWeight {G : Set E3} {t g : E3 → ℝ} {μ N P : ℝ}
    (hGmeas : MeasurableSet G) (hμ : 0 < μ) (hN : 0 < N)
    (ht : ∀ u ∈ G, 0 ≤ t u) (hg : ∀ u ∈ G, 0 ≤ g u)
    (hIg : IntegrableOn g G) (hIgt : IntegrableOn (fun u => g u * t u) G)
    (hIpsi : IntegrableOn (fun u => g u * Work.SmallBoxSliding.psiWeight 1 μ (t u)) G)
    (hJ : N * (∫ u in G, g u * Work.SmallBoxSliding.psiWeight 1 μ (t u)) ≤ P) :
    (μ / 3) * (N * (∫ u in G, g u * t u)) - μ ^ 2 * (N * (∫ u in G, g u)) ≤ P := by
  have hAint : IntegrableOn (fun u => g u * ((μ / 3) * t u - μ ^ 2)) G := by
    have h : IntegrableOn (fun u => (μ / 3) * (g u * t u) - μ ^ 2 * g u) G :=
      (hIgt.const_mul (μ / 3)).sub (hIg.const_mul (μ ^ 2))
    refine h.congr ?_
    filter_upwards with u
    ring
  have hpt : ∀ u ∈ G, g u * ((μ / 3) * t u - μ ^ 2)
      ≤ g u * Work.SmallBoxSliding.psiWeight 1 μ (t u) := by
    intro u hu
    exact mul_le_mul_of_nonneg_left (psiWeight_ge_affine hμ (ht u hu)) (hg u hu)
  have hAB : (∫ u in G, g u * ((μ / 3) * t u - μ ^ 2))
      ≤ ∫ u in G, g u * Work.SmallBoxSliding.psiWeight 1 μ (t u) :=
    integral_mono_ae hAint hIpsi (ae_restrict_of_forall_mem hGmeas hpt)
  have hlin : (∫ u in G, g u * ((μ / 3) * t u - μ ^ 2))
      = (μ / 3) * (∫ u in G, g u * t u) - μ ^ 2 * (∫ u in G, g u) := by
    have h1 : (∫ u in G, g u * ((μ / 3) * t u - μ ^ 2))
        = ∫ u in G, ((μ / 3) * (g u * t u) - μ ^ 2 * g u) :=
      setIntegral_congr_fun hGmeas (fun u _ => by ring)
    have h2 : (∫ u in G, ((μ / 3) * (g u * t u) - μ ^ 2 * g u))
        = (μ / 3) * (∫ u in G, g u * t u) - μ ^ 2 * (∫ u in G, g u) := by
      rw [MeasureTheory.integral_sub (hIgt.const_mul (μ / 3)) (hIg.const_mul (μ ^ 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact h1.trans h2
  calc (μ / 3) * (N * (∫ u in G, g u * t u)) - μ ^ 2 * (N * (∫ u in G, g u))
      = N * ((μ / 3) * (∫ u in G, g u * t u) - μ ^ 2 * (∫ u in G, g u)) := by ring
    _ = N * (∫ u in G, g u * ((μ / 3) * t u - μ ^ 2)) := by rw [hlin]
    _ ≤ N * (∫ u in G, g u * Work.SmallBoxSliding.psiWeight 1 μ (t u)) :=
        mul_le_mul_of_nonneg_left hAB hN.le
    _ ≤ P := hJ

/-! ## 3. The two integrability inputs of the Cauchy–Schwarz window -/

/-- **Integrability of `wbMass · wbDens` on `I₋`.**

The product is dominated by the constant `max(C₁·(a v))0 · n·(chiSupAbs·chiSmallDecay M)²`
on the ball in which the small box meets the big box, and vanishes outside it
(`chiMass = 0` there); this is `Work.BoseFixB1.WB.integrable_w1MassB_mul_dens` at FS's
parameters. -/
theorem integrableOn_wbMass_mul_wbDens {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (paramsAt μ (_root_.BoseGases.a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : E3, wbMass v h μ u
      ≤ C₁ * _root_.BoseGases.a v
        * chiMass (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v)))
    (hN : 0 < normB v μ n (Φ : X n → ℝ)) :
    IntegrableOn (fun u : E3 => wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u)
      (interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ) := by
  have hmassL : ∀ u : E3, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg (h := h) hv hvrad hv_supp hR hM hℓ hd u
  have haesm_g : AEStronglyMeasurable (fun u : E3 => wbMass v h μ u) volume :=
    Work.BoseFixB1.WB.w1MassB_aeStronglyMeasurable_local (h := h) hR hv_supp _ hM _ _
  have haesm_t : AEStronglyMeasurable (fun u : E3 => wbDens v h μ n (Φ : X n → ℝ) u) volume :=
    Work.BoseFixB1.WB.wbDens_aeStronglyMeasurable_gen (h := h) hM hℓ hd (Φ.contDiff.continuous)
  exact (Work.BoseFixB1.WB.integrable_w1MassB_mul_dens (Φ := (Φ : X n → ℝ))
    (haesm_g.mul haesm_t) hM hℓ hd hC₁ hmassL hmassU hN).integrableOn

/-- **Integrability of `wbMass · F(wbDens)` on `I₋`**, `F = psiWeight 1 μ`.

Domination by `μ²·wbMass + μ·(wbMass·wbDens)` through the affine *upper* bound
`F(t) ≤ μ² + μt` (`Work.BoseFixB1.WB.psiWeight_one_le`), both summands being integrable by
`IntegrableOn_wbMass_interior` and `integrableOn_wbMass_mul_wbDens`. -/
theorem integrableOn_wbMass_mul_psiDens {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (paramsAt μ (_root_.BoseGases.a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : E3, wbMass v h μ u
      ≤ C₁ * _root_.BoseGases.a v
        * chiMass (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (_root_.BoseGases.a v)))
    (hN : 0 < normB v μ n (Φ : X n → ℝ)) :
    IntegrableOn (fun u : E3 => wbMass v h μ u
        * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u))
      (interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ) := by
  have hmassL : ∀ u : E3, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg (h := h) hv hvrad hv_supp hR hM hℓ hd u
  have haesm_g : AEStronglyMeasurable (fun u : E3 => wbMass v h μ u) volume :=
    Work.BoseFixB1.WB.w1MassB_aeStronglyMeasurable_local (h := h) hR hv_supp _ hM _ _
  have haesm_t : AEStronglyMeasurable (fun u : E3 => wbDens v h μ n (Φ : X n → ℝ) u) volume :=
    Work.BoseFixB1.WB.wbDens_aeStronglyMeasurable_gen (h := h) hM hℓ hd (Φ.contDiff.continuous)
  have hIg : IntegrableOn (fun u : E3 => wbMass v h μ u)
      (interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ) :=
    (Work.BoseFixB1.WB.integrable_w1MassB (v := v) (h := h) haesm_g hM hℓ hd hmassL
      hmassU).integrableOn
  have hIgt := integrableOn_wbMass_mul_wbDens (h := h) hv hvrad hv_supp hR hμ hav hM hℓ hd
    hC₁ hmassU Φ hN
  have haesm_psi : AEStronglyMeasurable (fun u : E3 => wbMass v h μ u
      * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)) volume :=
    haesm_g.mul (((Work.BoseFixB1.WB.measurable_psiWeight_cs 1 μ).comp_aemeasurable
      haesm_t.aemeasurable)).aestronglyMeasurable
  have hdom : IntegrableOn (fun u : E3 => μ ^ 2 * wbMass v h μ u
      + μ * (wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u))
      (interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ) :=
    (hIg.const_mul (μ ^ 2)).add (hIgt.const_mul μ)
  refine hdom.mono' (haesm_psi.mono_measure Measure.restrict_le_self) ?_
  filter_upwards with u
  have ht0 : 0 ≤ wbDens v h μ n (Φ : X n → ℝ) u := wbDens_nonneg (Φ : X n → ℝ) u
  have hpsi0 : 0 ≤ psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u) :=
    Work.BoseFixB1.WB.psiWeight_one_nonneg hμ ht0
  have hpsile : psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)
      ≤ μ ^ 2 + μ * wbDens v h μ n (Φ : X n → ℝ) u :=
    Work.BoseFixB1.WB.psiWeight_one_le hμ ht0
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hmassL u) hpsi0)]
  calc wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)
      ≤ wbMass v h μ u * (μ ^ 2 + μ * wbDens v h μ n (Φ : X n → ℝ) u) :=
        mul_le_mul_of_nonneg_left hpsile (hmassL u)
    _ = μ ^ 2 * wbMass v h μ u
        + μ * (wbMass v h μ u * wbDens v h μ n (Φ : X n → ℝ) u) := by ring

/-! ## 4. The target -/

theorem rpsi_ge_affine {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u
      ≤ C₁ * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hN : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :
    (μ / 3) * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          * Work.BoseFixB1.wbSig v h μ n (Φ : Submission.BoseGases.X n → ℝ))
      - μ ^ 2 * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          * Work.BoseFixB1.wbW v h μ)
      ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) := by
  have hIg : IntegrableOn (fun u : E3 => wbMass v h μ u)
      (interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ) :=
    Work.BoseFixB1.WB.integrableOn_wbMass_interior (h := h) hv hvrad hv_supp hR hμ hav hM hℓ hd
  have hIgt := integrableOn_wbMass_mul_wbDens (h := h) hv hvrad hv_supp hR hμ hav hM hℓ hd
    hC₁ hmassU Φ hN
  have hIpsi := integrableOn_wbMass_mul_psiDens (h := h) hv hvrad hv_supp hR hμ hav hM hℓ hd
    hC₁ hmassU Φ hN
  have hJ := Work.BoseFixB1.WB.jensen_integrated (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR
    hμ hav hM hℓ hd Φ
  have hmain := affine_le_of_psiWeight
    (G := interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ)
    (t := fun u => wbDens v h μ n (Φ : X n → ℝ) u) (g := fun u => wbMass v h μ u)
    (μ := μ) (N := normB v μ n (Φ : X n → ℝ)) (P := RPsi v h μ (Φ : X n → ℝ))
    (measurableSet_interiorSet _ _ _) hμ hN
    (fun u _ => wbDens_nonneg (Φ : X n → ℝ) u)
    (fun u _ => wbMass_nonneg (h := h) hv hvrad hv_supp hR hM hℓ hd u)
    hIg hIgt hIpsi hJ
  simpa only [wbSig, wbW] using hmain

end Work.BoseB1Cube
