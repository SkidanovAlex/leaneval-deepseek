import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C²` regularity of the profile `Φ` from the `C²` regularity of `merPsi`

The meridian stream function of the reconstruction is

  `merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ), θ(r,z), τ)`,  `τ = clockInv C t`,

where `Φ̂ = PhiOdd Φ` is the odd extension in `θ`, `ρ(r,z) = √(r²+z²)` and `θ(r,z) = arctan(z/r)`.

On the branch `θ > 0` the odd extension is the identity, so *off* the degenerate set
`{r = 0} ∪ {z = 0}` the function `H(r,z) := Φ̂(ρ(r,z)^p/B(τ), θ(r,z), τ)` differs from `merPsi` only
by the explicit `C²` factor `ρ²·A(τ)⁻¹`, which is *nonzero* at a point with `ρ > 0` as soon as
`A(τ) ≠ 0`.  Hence the hypothesis that `merPsi` is `C²` off the degenerate set transfers to `H`.

The second ingredient is the *explicit local inverse* of the polar dictionary: the map

  `Q(w,θ) = ((w·B(τ))^{1/p}·cos θ, (w·B(τ))^{1/p}·sin θ)`

is `C^∞` at `(w,θ)` for `w > 0`, it maps `(w,θ)` to the point `(r₀,z₀)` with
`ρ(r₀,z₀) = (w·B(τ))^{1/p}` and `θ(r₀,z₀) = θ`, and near `(w,θ)` it satisfies
`ρ(Q(w,θ))^p/B(τ) = w`, `θ(Q(w,θ)) = θ`.  Composing `H` with `Q` therefore gives the `C²`-ness of
`(w,θ) ↦ Φ̂(w,θ,τ)` at `(w,θ)`, and on a neighbourhood of `(w,θ)` (where the second coordinate stays
in `(0, π/2)`) the odd extension agrees with `Φ`.  This is the inverse-function-theorem-free form of
the statement; the only hypothesis needed about `A` is `A(τ) ≠ 0` (without it `merPsi` is
identically zero, since `(0:ℝ)⁻¹ = 0` — see `NOTES_contDiffAt_Phi_of_contDiffAt_merPsi.md`).
-/

namespace Work.FTS.BSIdent.Defs

open scoped Topology

/-- Polar reconstruction: the meridian point with coordinates `(R cos Θ, R sin Θ)` has `ρ = R`
whenever `R > 0`. -/
private lemma rhoP_mul_cos_sin {R Θ : ℝ} (hR : 0 < R) :
    Work.Cyl.rhoP (R * Real.cos Θ) (R * Real.sin Θ) = R := by
  rw [Work.Cyl.rhoP]
  have h : (R * Real.cos Θ) ^ 2 + (R * Real.sin Θ) ^ 2 = R ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq Θ]
  rw [h, Real.sqrt_sq hR.le]

/-- Polar reconstruction: the meridian point with coordinates `(R cos Θ, R sin Θ)` has `θ = Θ`
whenever `R > 0` and `-(π/2) < Θ < π/2`. -/
private lemma thetaP_mul_cos_sin {R Θ : ℝ} (hR : 0 < R) (hΘ : -(Real.pi / 2) < Θ)
    (hΘ' : Θ < Real.pi / 2) :
    Work.Cyl.thetaP (R * Real.cos Θ) (R * Real.sin Θ) = Θ := by
  rw [Work.Cyl.thetaP]
  have htan : R * Real.sin Θ / (R * Real.cos Θ) = Real.tan Θ := by
    rw [Real.tan_eq_sin_div_cos, mul_div_mul_left _ _ hR.ne']
  rw [htan, Real.arctan_tan hΘ hΘ']

theorem contDiffAt_Phi_of_merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) (hα : 0 < α)
    (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hψ : ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Work.FTS.BSIdent.merPsi α A B Φ C p.1 p.2 t) (r, z))
    {w θ : ℝ} (hw : 0 < w) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hp_pos : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hwB : 0 < w * B (Physical.clockInv C t) := mul_pos hw hB
  -- ### The preimage point `(r₀, z₀)` of `(w, θ)` under the polar dictionary
  set ρ₀ : ℝ := (w * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; exact Real.rpow_pos_of_pos hwB _
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  set r₀ : ℝ := ρ₀ * Real.cos θ with hr₀def
  set z₀ : ℝ := ρ₀ * Real.sin θ with hz₀def
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; exact mul_pos hρ₀pos hcos
  have hz₀ne : z₀ ≠ 0 := by rw [hz₀def]; exact ne_of_gt (mul_pos hρ₀pos hsin)
  have hrhoP : Work.Cyl.rhoP r₀ z₀ = ρ₀ := by
    rw [hr₀def, hz₀def]; exact rhoP_mul_cos_sin hρ₀pos
  have hthetaP : Work.Cyl.thetaP r₀ z₀ = θ := by
    rw [hr₀def, hz₀def]
    exact thetaP_mul_cos_sin hρ₀pos (by linarith) hθ2
  -- ### Step 1: the `C²`-ness of the odd extension, read off `hψ` by removing the explicit factor
  have hH : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP q.1 q.2) (Physical.clockInv C t)) (r₀, z₀) := by
    have hmer := hψ r₀ z₀ hr₀pos hz₀ne
    have hρc : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r₀, z₀) := by
      have h2 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r₀, z₀) := by fun_prop
      have h3 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r₀, z₀) ≠ 0 := by
        show r₀ ^ 2 + z₀ ^ 2 ≠ 0
        positivity
      simpa [Work.Cyl.rhoP, Function.comp_def] using
        (Real.contDiffAt_sqrt (n := 2) h3).comp (r₀, z₀) h2
    have hfac : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Physical.clockInv C t))⁻¹)
        (r₀, z₀) :=
      (hρc.pow 2).mul contDiffAt_const
    have hne : Work.Cyl.rhoP r₀ z₀ ^ 2 * (A (Physical.clockInv C t))⁻¹ ≠ 0 := by
      rw [hrhoP]
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hρ₀pos)) (inv_ne_zero hA)
    refine (hmer.div hfac hne).congr_of_eventuallyEq ?_
    have hnb : ∀ᶠ q : ℝ × ℝ in 𝓝 (r₀, z₀),
        Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Physical.clockInv C t))⁻¹ ≠ 0 :=
      hfac.continuousAt.eventually_ne hne
    filter_upwards [hnb] with q hq
    simp only [Pi.div_apply]
    rw [Work.FTS.BSIdent.merPsi_apply]
    exact (mul_div_cancel_left₀ _ hq).symm
  -- ### Step 2: the explicit local inverse `Q` of the polar dictionary is `C²` at `(w, θ)`
  have hbase : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 * B (Physical.clockInv C t)) (w, θ) := by
    fun_prop
  have hpow : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α))
      (w, θ) :=
    hbase.rpow_const_of_ne (by simpa using hwB.ne')
  have hQ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.cos q.2,
       (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.sin q.2))
      (w, θ) := by
    have hc : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.cos q.2) (w, θ) := by fun_prop
    have hs : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.sin q.2) (w, θ) := by fun_prop
    exact (hpow.mul hc).prodMk (hpow.mul hs)
  have hcomp := hH.comp (w, θ) hQ
  -- ### Step 3: `Q` inverts the polar dictionary near `(w, θ)`, hence the composite is `Φ̂`
  have hPhiOdd : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ q.1 q.2 (Physical.clockInv C t)) (w, θ) := by
    refine hcomp.congr_of_eventuallyEq ?_
    have hpos_nb : ∀ᶠ q : ℝ × ℝ in 𝓝 (w, θ), 0 < q.1 * B (Physical.clockInv C t) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => q.1 * B (Physical.clockInv C t)) (w, θ) := by
        fun_prop
      exact hcont.eventually (isOpen_Ioi.mem_nhds hwB)
    have hth_nb : ∀ᶠ q : ℝ × ℝ in 𝓝 (w, θ),
        -(Real.pi / 2) < q.2 ∧ q.2 < Real.pi / 2 := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => q.2) (w, θ) := continuousAt_snd
      exact (hcont.eventually
          (isOpen_Ioi.mem_nhds (by change -(Real.pi / 2) < θ; linarith))).and
        (hcont.eventually (isOpen_Iio.mem_nhds hθ2))
    filter_upwards [hpos_nb, hth_nb] with q hq hqth
    simp only [Function.comp_apply]
    have hRpos : 0 < (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) :=
      Real.rpow_pos_of_pos hq _
    have h1 : Work.Cyl.rhoP
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.cos q.2)
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.sin q.2)
        = (q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) :=
      rhoP_mul_cos_sin hRpos
    have h2 : Work.Cyl.thetaP
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.cos q.2)
          ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α) * Real.sin q.2)
        = q.2 :=
      thetaP_mul_cos_sin hRpos hqth.1 hqth.2
    have h3 : ((q.1 * B (Physical.clockInv C t)) ^ (1 / Work.FTS.Regularity.pExp α))
          ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) = q.1 := by
      rw [← Real.rpow_mul (le_of_lt hq), one_div_mul_cancel hp_pos.ne', Real.rpow_one]
      exact mul_div_cancel_right₀ q.1 hB.ne'
    rw [h1, h3, h2]
  -- ### Step 4: near `(w, θ)` the second coordinate is positive, i.e. `Φ̂ = Φ`
  refine hPhiOdd.congr_of_eventuallyEq ?_
  have hth_nb : ∀ᶠ q : ℝ × ℝ in 𝓝 (w, θ), 0 < q.2 := by
    have hcont : ContinuousAt (fun q : ℝ × ℝ => q.2) (w, θ) := continuousAt_snd
    exact hcont.eventually (isOpen_Ioi.mem_nhds (by change 0 < θ; exact hθ))
  filter_upwards [hth_nb] with q hq
  exact (Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hq)).symm

end Work.FTS.BSIdent.Defs
