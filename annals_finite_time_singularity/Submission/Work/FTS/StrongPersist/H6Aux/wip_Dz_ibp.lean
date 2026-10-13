import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop
import Submission.Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_nearZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `z`-integration by parts in the `wip` normalisation, with the boundary terms derived

`Work.Coercivity.wip ρ (Dz h) h = ∫_z ∫_θ (Dz h) h ρ` is computed by integrating by parts in
the radial variable `z` on `(0,∞)`: with `ρ = Φ(z) σ(θ)` the derivative of the primitive
`z ↦ (z Φ z) h(z,θ)² σ θ` splits into `2 (Dz h) h Φ σ + h² ∂_z(zΦ) σ`, so

  `wip (Φ σ) (Dz h) h = -(1/2) ∫_z ∫_θ h² ∂_z(zΦ) σ`

*provided the boundary terms vanish*.  None of the boundary limits is a hypothesis here: the
three integrability assumptions (of `h²Φσ`, of `(Dz h) h Φσ` and of `h² ∂_z(zΦ) σ`) already
force them.  The primitive has an integrable derivative, so it has both limits
(`zibp_lim_atTop`, `zibp_lim_nearZero`), and each limit must be `0` because `z ↦ z g z` with
`g = h²Φσ ∈ L¹` cannot be bounded below by a positive constant on a half-line.

The proof is carried out slice by slice in `θ` (for a.e. angle, where the slice of a
`SmoothOpen` function is `C^∞` in `z`) and assembled with Fubini.

## Conventions

`Iz = [0,∞)`, `Iθ = [0,π/2]`, `dz dθ` measure, `Dz f = z ∂_z f`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `𝓝[≥] a` from `𝓝[>] a`: if `F → b` along `𝓝[>] a` and `F a = b`, then `F` tends to `F a`
along `𝓝[Ici a] a`.  (Local copy of the argument used in
`Work.FTS.StrongPersist.N6Trans.L6Flux.zibp_Ioi_of_integrable`.) -/
private theorem wip_Dz_tendsto_Ici_of_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds b)) (hb : F a = b) :
    Tendsto F (nhdsWithin a (Set.Ici a)) (nhds (F a)) := by
  rw [hb]
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`. -/
private theorem wip_Dz_Iz_ae_eq_Ioi :
    Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi (0 : ℝ) :=
  MeasureTheory.Ioi_ae_eq_Ici.symm

/-- The restricted measures of `Iz` and `(0,∞)` agree. -/
private theorem wip_Dz_restrict_Iz_eq_restrict_Ioi :
    (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi (0 : ℝ)) :=
  MeasureTheory.Measure.restrict_congr_set wip_Dz_Iz_ae_eq_Ioi

/-- Almost every angle of `Iθ` lies in the *open* interval. -/
private theorem wip_Dz_ae_restrict_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hset : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The `z`-derivative of the primitive `z ↦ (z Φ(z)) h(z,θ)² σ(θ)` -/

/-- The pointwise `z`-derivative of the primitive `z ↦ (z·Φ z)·(h z θ)²·σ θ` at `z > 0` and
`θ ∈ (0,π/2)`: it splits into `2` times the `wip`-integrand `Dz h · h · Φ · σ` plus the
"derived coefficient" term `h² · ∂_z(zΦ) · σ`. -/
private theorem wip_Dz_prim_hasDerivAt {h : ℝ → ℝ → ℝ} {Φ σ : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioi 0)) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hz : 0 < z) :
    HasDerivAt (fun z' => (z' * Φ z') * (h z' θ ^ 2 * σ θ))
      (h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ
        + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)) z := by
  have hΦd : DifferentiableAt ℝ Φ z :=
    (hΦ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hφ : HasDerivAt (fun z' : ℝ => z' * Φ z')
      (deriv (fun z' : ℝ => z' * Φ z') z) z :=
    (differentiableAt_id.mul hΦd).hasDerivAt
  have hV : HasDerivAt (fun z' : ℝ => h z' θ) (deriv (fun z' : ℝ => h z' θ) z) z :=
    hsm.hasDerivAt_slice hθ hz
  have hV2 : HasDerivAt (fun z' : ℝ => h z' θ ^ 2)
      (2 * h z θ * deriv (fun z' : ℝ => h z' θ) z) z := by
    have h' := hV.pow 2
    have hfun : (fun z' : ℝ => h z' θ ^ 2) = (fun z' : ℝ => h z' θ) ^ 2 := by
      funext z'; rfl
    rw [hfun]
    refine h'.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun z' : ℝ => h z' θ ^ 2 * σ θ)
      ((2 * h z θ * deriv (fun z' : ℝ => h z' θ) z) * σ θ) z := hV2.mul_const (σ θ)
  have h4 : HasDerivAt (fun z' : ℝ => (z' * Φ z') * (h z' θ ^ 2 * σ θ))
      (deriv (fun z' : ℝ => z' * Φ z') z * (h z θ ^ 2 * σ θ)
        + (z * Φ z) * ((2 * h z θ * deriv (fun z' : ℝ => h z' θ) z) * σ θ)) z :=
    hφ.mul h3
  refine h4.congr_deriv ?_
  ring

/-! ## The `z`-integration by parts on a single `θ`-slice -/

/-- **`z`-integration by parts on one `θ`-slice.**  For `θ ∈ (0,π/2)` and the two integrands
`(Dz h) h Φσ` and `h² ∂_z(zΦ) σ` integrable on `(0,∞)` (together with `h²Φσ ∈ L¹`, which is
what forces both boundary terms to vanish),
`∫_0^∞ (Dz h) h Φσ = -(1/2) ∫_0^∞ h² ∂_z(zΦ) σ`. -/
private theorem wip_Dz_slice_ibp {h : ℝ → ℝ → ℝ} {Φ σ : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioi 0)) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hA : IntegrableOn (fun z => Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ) (Set.Ioi 0))
    (hB : IntegrableOn (fun z => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
      (Set.Ioi 0))
    (hG : IntegrableOn (fun z => h z θ ^ 2 * Φ z * σ θ) (Set.Ioi 0)) :
    ∫ z in Set.Ioi 0, Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ
      = -(1 / 2) * ∫ z in Set.Ioi 0, h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ := by
  set ψ : ℝ → ℝ := fun z => (z * Φ z) * (h z θ ^ 2 * σ θ) with hψ
  have hψ0 : ψ 0 = 0 := by
    simp only [hψ]
    ring
  -- the derivative of the primitive is `deriv ψ`
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (deriv ψ z) z := by
    intro z hz
    have h := wip_Dz_prim_hasDerivAt (σ := σ) hsm hΦ hθ hz
    exact h.congr_deriv h.deriv.symm
  -- its explicit value
  have hderiv_eq : ∀ z ∈ Set.Ioi (0 : ℝ), deriv ψ z
      = h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ
        + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ) := by
    intro z hz
    exact (wip_Dz_prim_hasDerivAt (σ := σ) hsm hΦ hθ hz).deriv
  -- the `wip`-integrand, written with the plain partial derivative
  have hA' : IntegrableOn
      (fun z => z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ) (Set.Ioi 0) := hA
  have hB' : Integrable (fun z => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
      (volume.restrict (Set.Ioi 0)) := hB
  have h2A : IntegrableOn
      (fun z => 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ))
      (Set.Ioi 0) :=
    (show Integrable (fun z => z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)
      (volume.restrict (Set.Ioi 0)) from hA').const_mul 2
  have h2A' : Integrable
      (fun z => 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ))
      (volume.restrict (Set.Ioi 0)) := h2A
  -- the derivative is integrable
  have hint : IntegrableOn (deriv ψ) (Set.Ioi 0) := by
    have hsum : IntegrableOn (fun z => (h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
        + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)) (Set.Ioi 0) :=
      hB.add h2A
    refine hsum.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact (hderiv_eq z hz).symm
  -- the `L¹`-bound needed for the boundary vanishing
  have hG2 : IntegrableOn (fun z => (Real.sqrt |Φ z * h z θ ^ 2 * σ θ|) ^ 2) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun z => |h z θ ^ 2 * Φ z * σ θ|) (Set.Ioi 0) :=
      (show Integrable (fun z => h z θ ^ 2 * Φ z * σ θ) (volume.restrict (Set.Ioi 0))
        from hG).abs
    refine h1.congr_fun (fun z _ => ?_) measurableSet_Ioi
    rw [Real.sq_sqrt (abs_nonneg (Φ z * h z θ ^ 2 * σ θ))]
    exact congrArg abs (by ring)
  have hbd : ∀ z, 0 ≤ z →
      |ψ z| ≤ 1 * (z * (Real.sqrt |Φ z * h z θ ^ 2 * σ θ|) ^ 2) := by
    intro z hz
    have hsqrt : (Real.sqrt |Φ z * h z θ ^ 2 * σ θ|) ^ 2 = |Φ z * h z θ ^ 2 * σ θ| :=
      Real.sq_sqrt (abs_nonneg _)
    rw [hsqrt, one_mul]
    have hL : |ψ z| = z * |Φ z * h z θ ^ 2 * σ θ| := by
      simp only [hψ, abs_mul, abs_of_nonneg hz]
      ring
    rw [hL]
  -- the two boundary limits, derived (not assumed)
  have htop : Tendsto ψ atTop (nhds 0) :=
    Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop
      (ψ := ψ) (ψ' := deriv ψ) (G := fun z => Real.sqrt |Φ z * h z θ ^ 2 * σ θ|)
      (C := 1) one_pos hderiv hint hbd hG2
  have h0 : Tendsto ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_nearZero
      (ψ := ψ) (ψ' := deriv ψ) (G := fun z => Real.sqrt |Φ z * h z θ ^ 2 * σ θ|)
      (C := 1) one_pos hderiv hint hbd hG2
  have hcont : ContinuousWithinAt ψ (Set.Ici 0) 0 :=
    wip_Dz_tendsto_Ici_of_Ioi h0 hψ0
  -- the fundamental theorem of calculus on `(0,∞)`
  have hFTC : ∫ z in Set.Ioi 0, deriv ψ z = 0 := by
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop, hψ0,
      sub_zero]
  have hsplit : ∫ z in Set.Ioi 0, deriv ψ z
      = (∫ z in Set.Ioi 0, h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
        + 2 * (∫ z in Set.Ioi 0, z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ) := by
    rw [show (∫ z in Set.Ioi 0, deriv ψ z)
        = ∫ z in Set.Ioi 0, ((h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
            + 2 * (z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ)) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => hderiv_eq z hz)]
    rw [MeasureTheory.integral_add hB' h2A', MeasureTheory.integral_const_mul]
  have hgoal : ∫ z in Set.Ioi 0, z * deriv (fun z' => h z' θ) z * h z θ * Φ z * σ θ
      = -(1 / 2) * ∫ z in Set.Ioi 0,
          h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ := by
    linarith [hFTC, hsplit]
  exact hgoal

/-! ## The main theorem -/

theorem wip_Dz_ibp {h : ℝ → ℝ → ℝ} {Φ σ : ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioi 0))
    (hint1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Φ z * σ θ) (Work.Spaces.Dz h) h
      = -(1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ) := by
  set μ : MeasureTheory.Measure ℝ := volume.restrict Work.Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hmeas : μ.prod ν = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  -- the bundled integrands, viewed on the product
  set A : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.Dz h p.1 p.2 * h p.1 p.2 * Φ p.1 * σ p.2 with hAdef
  set B : ℝ × ℝ → ℝ :=
    fun p => h p.1 p.2 ^ 2 * deriv (fun z' => z' * Φ z') p.1 * σ p.2 with hBdef
  set Gg : ℝ × ℝ → ℝ := fun p => h p.1 p.2 ^ 2 * Φ p.1 * σ p.2 with hGdef
  have hAint : Integrable A (μ.prod ν) := by
    rw [hmeas]
    exact hint2
  have hBint : Integrable B (μ.prod ν) := by
    rw [hmeas]
    exact hint3
  have hGint : Integrable Gg (μ.prod ν) := by
    rw [hmeas]
    exact hint1
  -- the `wip` integral is the product-measure integral of `A`
  have hwip : Work.Coercivity.wip (fun z θ => Φ z * σ θ) (Work.Spaces.Dz h) h
      = ∫ z, ∫ θ, A (z, θ) ∂ν ∂μ := by
    simp only [Work.Coercivity.wip]
    rw [hμ, hν]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [A]
    ring
  -- the slice identity, for a.e. angle
  have hslice : ∀ᵐ θ ∂ν,
      (∫ z, A (z, θ) ∂μ) = -(1 / 2) * (∫ z, B (z, θ) ∂μ) := by
    filter_upwards [hAint.prod_left_ae, hBint.prod_left_ae, hGint.prod_left_ae,
      wip_Dz_ae_restrict_Iθ_mem_Ioo] with θ hIA hIB hIG hθIo
    have hIA' : IntegrableOn (fun z => Work.Spaces.Dz h z θ * h z θ * Φ z * σ θ)
        (Set.Ioi 0) := by
      rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi] at hIA
      exact hIA
    have hIB' : IntegrableOn (fun z => h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ)
        (Set.Ioi 0) := by
      rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi] at hIB
      exact hIB
    have hIG' : IntegrableOn (fun z => h z θ ^ 2 * Φ z * σ θ) (Set.Ioi 0) := by
      rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi] at hIG
      exact hIG
    have hgoal := wip_Dz_slice_ibp hsm hΦ hθIo hIA' hIB' hIG'
    rw [hμ, wip_Dz_restrict_Iz_eq_restrict_Ioi]
    exact hgoal
  calc Work.Coercivity.wip (fun z θ => Φ z * σ θ) (Work.Spaces.Dz h) h
      = ∫ z, ∫ θ, A (z, θ) ∂ν ∂μ := hwip
    _ = ∫ p, A p ∂(μ.prod ν) := (MeasureTheory.integral_prod A hAint).symm
    _ = ∫ θ, ∫ z, A (z, θ) ∂μ ∂ν := MeasureTheory.integral_prod_symm A hAint
    _ = ∫ θ, -(1 / 2) * (∫ z, B (z, θ) ∂μ) ∂ν :=
          MeasureTheory.integral_congr_ae hslice
    _ = -(1 / 2) * ∫ θ, ∫ z, B (z, θ) ∂μ ∂ν := by
          rw [MeasureTheory.integral_const_mul]
    _ = -(1 / 2) * ∫ p, B p ∂(μ.prod ν) := by
          rw [(MeasureTheory.integral_prod_symm B hBint).symm]
    _ = -(1 / 2) * (∫ z, ∫ θ, B (z, θ) ∂ν ∂μ) := by
          rw [MeasureTheory.integral_prod B hBint]
    _ = -(1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          h z θ ^ 2 * deriv (fun z' => z' * Φ z') z * σ θ) := by
          rw [hμ, hν]

end Work.FTS.StrongPersist.H6Aux
