import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.interpol_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false





/-- The four integrability hypotheses of the interpolation lemma, bundled. -/
def FourInt (G : ℝ → ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz

/-- The full hypothesis package of the interpolation statement: smoothness on a neighbourhood
of the closed quadrant, vanishing on the two angular boundaries, decay of `D_z²G` along
`z → ∞` at every angle, and the four integrability conditions. -/
def Hyp (G : ℝ → ℝ → ℝ) : Prop :=
  Work.Spaces.SmoothNbhd G ∧ (∀ z : ℝ, G z 0 = 0) ∧ (∀ z : ℝ, G z (Real.pi / 2) = 0) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ)
        Filter.atTop (nhds 0)) ∧
    FourInt G



end Work.FTS.EllipticEst

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The weight `ρ = w(z)²·sin(2θ)^{-η}` of the interpolation estimate. -/
def rho (z θ : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `SG = -(D²G + b DG)` with `b(z) = (z-3)/(1+z)`, i.e. `S G = D^*DG` for the adjoint
`D^* = -(D + b)` of `D = D_z` with respect to the weight `rho`. -/
def SG (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dz (Work.Spaces.Dz G) z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)


/-- The `L²(ρ)` pairing `⟨f, g⟩_ρ = ∫∫ f g ρ` over the quadrant. -/
def pairing (f g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ * g z θ * rho z θ

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.gC_orthogonal_half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The derivative of `gC n` at the origin -/

/-- The ladder relation `D_n` of `Gegenbauer/gC_ode`, evaluated at `x = 0`:
`deriv (gC n) 0 = (n + 2) · gC (n-1) 0` for `n ≥ 1`. -/
lemma deriv_gC_zero (n : ℕ) (hn : 1 ≤ n) :
    deriv (gC n) 0 = ((n : ℝ) + 2) * gC (n - 1) 0 := by
  have h := Erel_all (n - 1) 0
  have h1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp only [Erel, h1, Drel] at h
  ring_nf at h
  linarith

/-- For an even index the derivative of `gC` at the origin vanishes: `gC (2m)` is an even
polynomial.  (`n = 2m` is even and `n - 1 = 2(m-1) + 1` is odd, hence `gC (n-1) 0 = 0`.) -/
lemma deriv_gC_even_zero (m : ℕ) : deriv (gC (2 * m)) 0 = 0 := by
  cases m with
  | zero =>
    rw [show gC (2 * 0) = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  | succ k =>
    rw [deriv_gC_zero (2 * (k + 1)) (by omega)]
    have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h3, gC_odd_zero k]
    ring

/-! ## Integration by parts on the half interval -/

/-- Integration by parts for the Gegenbauer self-adjoint form on `[0,1]`, assuming that the
boundary term at the origin vanishes:

  `q(q+3) ∫_0^1 (1-x²) gC p gC q = ∫_0^1 (gC p)' (1-x²)² (gC q)' + gC p 0 · deriv (gC q) 0`,

and with `hbc : gC p 0 · deriv (gC q) 0 = 0` the boundary term is dropped.  The endpoint at
`x = 1` contributes nothing because `(1-x²)²` vanishes there. -/
lemma ibp_gC_half (p q : ℕ) (hbc : gC p 0 * deriv (gC q) 0 = 0) :
    ((q : ℝ) * ((q : ℝ) + 3)) *
        (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u)
      = ∫ u in (0 : ℝ)..1, deriv (gC p) u * ((1 - u ^ 2) ^ 2 * deriv (gC q) u) := by
  have hc : Continuous (fun u : ℝ => (1 - u ^ 2) * gC q u) :=
    (continuous_const.sub (continuous_id.pow 2)).mul (contDiff_gC q).continuous
  have hcont : Continuous (fun u : ℝ =>
      -(((q : ℝ) * ((q : ℝ) + 3)) * ((1 - u ^ 2) * gC q u))) :=
    (continuous_const.mul hc).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => gC p u) (u' := fun u : ℝ => deriv (gC p) u)
    (v := fun u : ℝ => (1 - u ^ 2) ^ 2 * deriv (gC q) u)
    (v' := fun u : ℝ => -(((q : ℝ) * ((q : ℝ) + 3)) * ((1 - u ^ 2) * gC q u)))
    (a := 0) (b := 1)
    (fun x _ => ((contDiff_gC p).differentiable (by norm_num)).differentiableAt.hasDerivAt)
    (fun x _ => hasDerivAt_gC_weight q x)
    (((contDiff_gC p).continuous_deriv (by norm_num)).intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1)
  have h1 : (1 - ((1 : ℝ)) ^ 2) ^ 2 * deriv (gC q) 1 = 0 := by norm_num
  have h0 : (1 - ((0 : ℝ)) ^ 2) ^ 2 * deriv (gC q) 0 = deriv (gC q) 0 := by norm_num
  rw [h1, h0, mul_zero, hbc] at h
  have hL : (∫ x in (0 : ℝ)..1, gC p x *
        (-(((q : ℝ) * ((q : ℝ) + 3)) * ((1 - x ^ 2) * gC q x))))
      = -(((q : ℝ) * ((q : ℝ) + 3))) *
        ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hL] at h
  linarith

/-! ## The eigenvalues `k(k+3)` are distinct -/

/-- `k ↦ k(k+3)` is strictly increasing, so `p ≠ q` implies `p(p+3) ≠ q(q+3)`: the eigenvalues
attached to `gC p` and `gC q` differ. -/
lemma eig_ne {p q : ℕ} (hpq : p ≠ q) :
    (p : ℝ) * ((p : ℝ) + 3) ≠ (q : ℝ) * ((q : ℝ) + 3) := by
  have hstep : ∀ k : ℕ, (k : ℝ) * ((k : ℝ) + 3)
      < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 3) := by
    intro k
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  exact fun h => hpq ((strictMono_nat_of_lt_succ hstep).injective h)

/-! ## The target -/

theorem gC_orthogonal_half (p q : ℕ) (hpq : p ≠ q) (hpar : Even (p + q)) :
    ∫ x in (0 : ℝ)..1,
        (1 - x ^ 2) * Work.FTS.PhiStar.Gegenbauer.gC p x
          * Work.FTS.PhiStar.Gegenbauer.gC q x = 0 := by
  -- `p` and `q` have the same parity
  have hsame : Even p ↔ Even q := Nat.even_add.mp hpar
  -- the boundary term of the integration by parts vanishes, in both orders
  have hbc1 : gC p 0 * deriv (gC q) 0 = 0 := by
    rcases Nat.even_or_odd q with hq | hq
    · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp hq
      rw [deriv_gC_even_zero n, mul_zero]
    · by_cases hp : Even p
      · exact absurd (hsame.mp hp) (Nat.not_even_iff_odd.mpr hq)
      · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hp
        rw [hk, gC_odd_zero k, zero_mul]
  have hbc2 : gC q 0 * deriv (gC p) 0 = 0 := by
    rcases Nat.even_or_odd p with hp | hp
    · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp hp
      rw [deriv_gC_even_zero n, mul_zero]
    · by_cases hq : Even q
      · exact absurd (hsame.mpr hq) (Nat.not_even_iff_odd.mpr hp)
      · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hq
        rw [hk, gC_odd_zero k, zero_mul]
  -- the two integration-by-parts identities
  have h1 := ibp_gC_half p q hbc1
  have h2 := ibp_gC_half q p hbc2
  -- symmetrise the two identities to a common integral
  have hU : (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC q u * gC p u)
      = ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u := by
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hJ : (∫ u in (0 : ℝ)..1, deriv (gC q) u * ((1 - u ^ 2) ^ 2 * deriv (gC p) u))
      = ∫ u in (0 : ℝ)..1, deriv (gC p) u * ((1 - u ^ 2) ^ 2 * deriv (gC q) u) := by
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have h2' : ((p : ℝ) * ((p : ℝ) + 3)) *
        (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u)
      = ∫ u in (0 : ℝ)..1, deriv (gC p) u * ((1 - u ^ 2) ^ 2 * deriv (gC q) u) := by
    rw [← hU, ← hJ]
    exact h2
  -- both eigenvalues multiply the same integral, so their difference does too
  have hkey : (((p : ℝ) * ((p : ℝ) + 3)) - ((q : ℝ) * ((q : ℝ) + 3))) *
      (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u) = 0 := by
    rw [sub_mul, h2', h1]
    ring
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h (sub_ne_zero.mpr (eig_ne hpq))
  · exact h

end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The angular domain

Everything is reduced to the *open* angular interval `Ioo 0 (π/2)`, which differs from
`Work.Spaces.Iθ = [0,π/2]` by the null set `{0, π/2}`; this is what makes the hypotheses of
the statement (which only control the open quadrant) enough for measurability and
integrability, since on the open interval all slices are continuous. -/

/-- The measure `volume.restrict (0,π/2)` is the one attached to `Work.Spaces.Iθ`. -/
theorem volume_restrict_Itheta_eq :
    (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict (Set.Ioo 0 (π / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

/-- `pz` of a `C¹` two-variable function is continuous on an open set. -/
theorem contDiffOn_zero_uncurry_pz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ 1 (Function.uncurry G) V) :
    ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pz G)) V := by
  rw [contDiffOn_zero]
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.continuousOn_fderiv_of_isOpen hV le_rfl
  have hcomp : ContinuousOn
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply continuousOn_const
  refine hcomp.congr fun p hp => ?_
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

/-- Taking `deriv` of two functions that agree on an open set. -/
theorem deriv_congr_of_isOpen {f₁ f₂ : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : EqOn f₁ f₂ s) : EqOn (deriv f₁) (deriv f₂) s := by
  intro z hz
  exact (Filter.EventuallyEq.deriv_eq
    (Filter.Eventually.mono (hs.mem_nhds hz) fun w hw => (h hw).symm)).symm

/-- **Smoothness of the angular parametric integral.**  If `F` is `C²` on the open quadrant
`(0,∞) × (0,π/2)`, `φ` is continuous on `Iθ = [0,π/2]`, and `F` together with its
`D_z = z ∂_z`-derivatives up to order `2` is bounded by `C` there, then
`z ↦ ∫_θ F z θ · φ θ` is `C²` on `(0,∞)`.

The point of the `D_z`-form of the bound: on a neighbourhood of a point `z₀ > 0` the
hypotheses give `|pz F z θ| ≤ 2C/z₀` and `|pzIter 2 F z θ| ≤ 8C/z₀²` (using
`DzIter 2 F = Dz F + z² · pzIter 2 F`, the product rule), so the dominated-differentiation
lemma `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`μ = volume.restrict Iθ`, x-neighbourhood
`Ioo (z₀/2) (2*z₀)`) applies with the integrable bound `θ ↦ C' · |φ θ|`; two applications give
the first two `HasDerivAt`s, and `MeasureTheory.continuousAt_of_dominated` gives the continuity
of the two derivatives needed for the `ContDiffOn`-by-`deriv` induction
(`contDiffOn_succ_iff_deriv_of_isOpen`). -/
theorem contDiffOn_two_integral_Itheta {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    ContDiffOn ℝ 2 (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ) (Set.Ioi 0) := by
  have hC : 0 ≤ C := by
    have h1 := (hb 1 (π / 4) (by norm_num) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).1
    linarith [abs_nonneg (F 1 (π / 4))]
  -- the reduced measure
  have hμ : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict (Set.Ioo 0 (π / 2)) :=
    volume_restrict_Itheta_eq
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- `φ` is integrable on the open interval
  have hφabs : Integrable (fun θ : ℝ => |φ θ|) (volume.restrict (Set.Ioo 0 (π / 2))) :=
    (hφ.abs.integrableOn_compact isCompact_Icc).mono_set hsub
  -- smoothness of the two partials on the open quadrant
  have hVopen : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmemV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      (z, θ) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) :=
    fun z θ hz hθ1 hθ2 => ⟨hz, hθ1, hθ2⟩
  have hsm_pz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz F))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.Spaces.uncurry_partial_c1 hVopen hF).1
  have hsm_pz2 : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz F)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contDiffOn_zero_uncurry_pz hVopen hsm_pz
  -- joint differentiability in the open quadrant, and the `z`-slice of `∂_z F`
  have hpz_slice_diff : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      DifferentiableAt ℝ (fun z' => Work.Spaces.pz F z' θ) z := fun z θ hz hθ1 hθ2 =>
    Work.Spaces.differentiableAt_curry_left
      ((hsm_pz.contDiffAt (hVopen.mem_nhds (hmemV z θ hz hθ1 hθ2))).differentiableAt
        (by norm_num))
  -- the pointwise bound on `∂_z F`
  have hpz_le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz F z θ| ≤ C / z := fun z θ hz hθ1 hθ2 => by
    have hDz : |Work.Spaces.Dz F z θ| ≤ C := (hb z θ hz hθ1 hθ2).2.1
    have hkey : |Work.Spaces.pz F z θ| = |Work.Spaces.Dz F z θ| / z := by
      rw [show Work.Spaces.Dz F z θ = z * Work.Spaces.pz F z θ from rfl, abs_mul,
        abs_of_pos hz, mul_div_cancel_left₀ _ (ne_of_gt hz)]
    rw [hkey, div_le_div_iff₀ hz hz]
    nlinarith [hDz]
  -- continuity of the slices of `F`, `pz F` and `pz (pz F)`
  have hsliceF : ∀ z : ℝ, 0 < z →
      ContinuousOn (fun θ : ℝ => Function.uncurry F (z, θ)) (Set.Ioo 0 (π / 2)) :=
    fun z hz => hF.continuousOn.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  have hslicePz : ∀ z : ℝ, 0 < z →
      ContinuousOn (fun θ : ℝ => Function.uncurry (Work.Spaces.pz F) (z, θ))
        (Set.Ioo 0 (π / 2)) :=
    fun z hz => hsm_pz.continuousOn.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  have hslicePz2 : ∀ z : ℝ, 0 < z →
      ContinuousOn (fun θ : ℝ => Function.uncurry (Work.Spaces.pz (Work.Spaces.pz F)) (z, θ))
        (Set.Ioo 0 (π / 2)) :=
    fun z hz => hsm_pz2.continuousOn.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  -- `pzIter 2 F` is definitionally `pz (pz F)`
  have hpzIter2_eq : ∀ z θ : ℝ,
      Work.Spaces.pzIter 2 F z θ = Function.uncurry (Work.Spaces.pz (Work.Spaces.pz F)) (z, θ) :=
    fun z θ => rfl
  -- the second derivative bound
  have hpz2_le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      ∀ z₀ : ℝ, 0 < z₀ → z₀ / 2 < z →
      |Work.Spaces.pzIter 2 F z θ| ≤ 8 * C / z₀ ^ 2 := fun z θ hz hθ1 hθ2 z₀ hz₀ hzge => by
    have hbd := hb z θ hz hθ1 hθ2
    exact pzIter_two_bound_of_DzIter_two hz₀ hzge hC
      (hpz_slice_diff z θ hz hθ1 hθ2) hbd.2.1 hbd.2.2
  ---------------------------------------------------------------------------------------
  -- The first derivative of the parametric integral.
  have h1 : ∀ z₀ ∈ Set.Ioi 0,
      HasDerivAt (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))
        (∫ θ, Work.Spaces.pz F z₀ θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))) z₀ := by
    intro z₀ hz₀
    have hz₀pos : 0 < z₀ := hz₀
    have hK : 0 ≤ 2 * C / z₀ := div_nonneg (by linarith) (le_of_lt hz₀pos)
    have hsmem : Set.Ioo (z₀ / 2) (2 * z₀) ∈ 𝓝 z₀ :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hzmem : ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), 0 < z := fun z hz => by
      linarith [hz.1, hz₀pos]
    refine hasDerivAt_integral_Itheta_of_bound hz₀pos hK hφ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hsmem] with z hz
      have hzpos : 0 < z := hzmem z hz
      have hcont : ContinuousOn (fun θ : ℝ => F z θ * φ θ) (Set.Ioo 0 (π / 2)) :=
        (hsliceF z hzpos).mul (hφ.mono hsub)
      simpa only [Function.uncurry] using hcont.aestronglyMeasurable measurableSet_Ioo
    · have hcont : ContinuousOn (fun θ : ℝ => F z₀ θ * φ θ) (Set.Ioo 0 (π / 2)) :=
        (hsliceF z₀ hz₀pos).mul (hφ.mono hsub)
      refine Integrable.mono (hφabs.const_mul C)
        (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hFb : |F z₀ θ| ≤ C := (hb z₀ θ hz₀pos hθ.1 hθ.2).1
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_abs]
      exact mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
    · have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pz F z₀ θ * φ θ)
          (Set.Ioo 0 (π / 2)) :=
        (hslicePz z₀ hz₀pos).mul (hφ.mono hsub)
      simpa only [Function.uncurry] using hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro z hz
      have hzpos : 0 < z := hzmem z hz
      have hbθ : |Work.Spaces.pz F z θ| ≤ C / z := hpz_le z θ hzpos hθ.1 hθ.2
      have hstep : C / z ≤ 2 * C / z₀ := by
        rw [div_le_div_iff₀ hzpos hz₀pos]
        nlinarith [le_of_lt hz.1, hz₀pos, hC]
      rw [Real.norm_eq_abs]
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro z hz
      have hzpos : 0 < z := hzmem z hz
      have hd : DifferentiableAt ℝ (fun z' => F z' θ) z :=
        Work.Spaces.differentiableAt_curry_left
          ((hF.contDiffAt (hVopen.mem_nhds (hmemV z θ hzpos hθ.1 hθ.2))).differentiableAt
            (by norm_num))
      exact hd.hasDerivAt.mul_const (φ θ)
  ---------------------------------------------------------------------------------------
  -- The second derivative of the parametric integral.
  have h2 : ∀ z₀ ∈ Set.Ioi 0,
      HasDerivAt (fun z => ∫ θ, Work.Spaces.pz F z θ * φ θ
          ∂(volume.restrict (Set.Ioo 0 (π / 2))))
        (∫ θ, Work.Spaces.pzIter 2 F z₀ θ * φ θ
          ∂(volume.restrict (Set.Ioo 0 (π / 2)))) z₀ := by
    intro z₀ hz₀
    have hz₀pos : 0 < z₀ := hz₀
    have hK : 0 ≤ 8 * C / z₀ ^ 2 := div_nonneg (by linarith) (by positivity)
    have hK2 : 0 ≤ 2 * C / z₀ := div_nonneg (by linarith) (le_of_lt hz₀pos)
    have hsmem : Set.Ioo (z₀ / 2) (2 * z₀) ∈ 𝓝 z₀ :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hzmem : ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), 0 < z := fun z hz => by
      linarith [hz.1, hz₀pos]
    refine hasDerivAt_integral_Itheta_of_bound hz₀pos hK hφ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hsmem] with z hz
      have hzpos : 0 < z := hzmem z hz
      have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pz F z θ * φ θ)
          (Set.Ioo 0 (π / 2)) :=
        (hslicePz z hzpos).mul (hφ.mono hsub)
      simpa only [Function.uncurry] using hcont.aestronglyMeasurable measurableSet_Ioo
    · have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pz F z₀ θ * φ θ)
          (Set.Ioo 0 (π / 2)) :=
        (hslicePz z₀ hz₀pos).mul (hφ.mono hsub)
      refine Integrable.mono (hφabs.const_mul (2 * C / z₀))
        (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hbθ : |Work.Spaces.pz F z₀ θ| ≤ 2 * C / z₀ := by
        have h := hpz_le z₀ θ hz₀pos hθ.1 hθ.2
        have hstep : C / z₀ ≤ 2 * C / z₀ := by
          rw [div_le_div_iff₀ hz₀pos hz₀pos]
          nlinarith [hC, hz₀pos]
        linarith
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK2, abs_abs]
      exact mul_le_mul_of_nonneg_right hbθ (abs_nonneg _)
    · have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 F z₀ θ * φ θ)
          (Set.Ioo 0 (π / 2)) :=
        (hslicePz2 z₀ hz₀pos).mul (hφ.mono hsub)
      simpa only [hpzIter2_eq, Function.uncurry] using
        hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro z hz
      have hzpos : 0 < z := hzmem z hz
      rw [Real.norm_eq_abs]
      exact hpz2_le z θ hzpos hθ.1 hθ.2 z₀ hz₀pos hz.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro z hz
      have hzpos : 0 < z := hzmem z hz
      exact (hpz_slice_diff z θ hzpos hθ.1 hθ.2).hasDerivAt.mul_const (φ θ)
  ---------------------------------------------------------------------------------------
  -- Continuity of the second derivative of the integral.
  have hcont_h : ContinuousOn
      (fun z => ∫ θ, Work.Spaces.pzIter 2 F z θ * φ θ
        ∂(volume.restrict (Set.Ioo 0 (π / 2)))) (Set.Ioi 0) := by
    intro z₀ hz₀
    have hz₀pos : 0 < z₀ := hz₀
    have hK : 0 ≤ 8 * C / z₀ ^ 2 := div_nonneg (by linarith) (by positivity)
    have hsmem : Set.Ioo (z₀ / 2) (2 * z₀) ∈ 𝓝 z₀ :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hzmem : ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), 0 < z := fun z hz => by
      linarith [hz.1, hz₀pos]
    refine (continuousAt_integral_Itheta_of_bound hK hφ ?_ ?_ ?_).continuousWithinAt
    · filter_upwards [hsmem] with z hz
      have hzpos : 0 < z := hzmem z hz
      have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 F z θ * φ θ)
          (Set.Ioo 0 (π / 2)) :=
        (hslicePz2 z hzpos).mul (hφ.mono hsub)
      simpa only [hpzIter2_eq, Function.uncurry] using
        hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [hsmem] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hzpos : 0 < z := hzmem z hz
      simpa only [Real.norm_eq_abs] using hpz2_le z θ hzpos hθ.1 hθ.2 z₀ hz₀pos hz.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hcont : ContinuousAt
          (fun z : ℝ => Function.uncurry (Work.Spaces.pz (Work.Spaces.pz F)) (z, θ)) z₀ := by
        have hca : ContinuousAt (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz F)))
            (z₀, θ) :=
          hsm_pz2.continuousOn.continuousAt (hVopen.mem_nhds (hmemV z₀ θ hz₀pos hθ.1 hθ.2))
        have hmap : ContinuousAt (fun z : ℝ => (z, θ)) z₀ :=
          continuousAt_id.prodMk continuousAt_const
        have hcomp : ContinuousAt
            ((Function.uncurry (Work.Spaces.pz (Work.Spaces.pz F))) ∘ (fun z : ℝ => (z, θ))) z₀ :=
          ContinuousAt.comp hca hmap
        simpa only [Function.comp_def] using hcomp
      simpa only [hpzIter2_eq, Function.uncurry] using hcont
  ---------------------------------------------------------------------------------------
  -- Assembly via the `ContDiffOn`-by-`deriv` induction.
  have hderiv_eq : EqOn
      (deriv (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))))
      (fun z => ∫ θ, Work.Spaces.pz F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))
      (Set.Ioi 0) := fun z hz => (h1 z hz).deriv
  have hderiv2_eq : EqOn
      (deriv (fun z => ∫ θ, Work.Spaces.pz F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))))
      (fun z => ∫ θ, Work.Spaces.pzIter 2 F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))
      (Set.Ioi 0) := fun z hz => (h2 z hz).deriv
  have hdiff_f : DifferentiableOn ℝ
      (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))) (Set.Ioi 0) :=
    fun z hz => (h1 z hz).differentiableAt.differentiableWithinAt
  have hdiff_g : DifferentiableOn ℝ
      (fun z => ∫ θ, Work.Spaces.pz F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))
      (Set.Ioi 0) :=
    fun z hz => (h2 z hz).differentiableAt.differentiableWithinAt
  have hcont_deriv_deriv : ContinuousOn
      (deriv (deriv (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))))
      (Set.Ioi 0) := by
    have hA : EqOn
        (deriv (deriv (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))))
        (deriv (fun z => ∫ θ, Work.Spaces.pz F z θ * φ θ
          ∂(volume.restrict (Set.Ioo 0 (π / 2))))) (Set.Ioi 0) :=
      deriv_congr_of_isOpen isOpen_Ioi hderiv_eq
    have hB : ContinuousOn
        (deriv (fun z => ∫ θ, Work.Spaces.pz F z θ * φ θ
          ∂(volume.restrict (Set.Ioo 0 (π / 2))))) (Set.Ioi 0) :=
      hcont_h.congr hderiv2_eq
    exact hB.congr hA
  have hdiff_deriv : DifferentiableOn ℝ
      (deriv (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))) (Set.Ioi 0) :=
    hdiff_g.congr fun z hz => hderiv_eq hz
  have hcont1 : ContDiffOn ℝ 1
      (deriv (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))))
      (Set.Ioi 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from by norm_num]
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (f := deriv (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))))
      (n := (0 : WithTop ℕ∞)) isOpen_Ioi).mpr ⟨hdiff_deriv, ?_, ?_⟩
    · intro h
      exact absurd h (by norm_num)
    · rw [contDiffOn_zero]
      exact hcont_deriv_deriv
  have hgoal : ContDiffOn ℝ 2
      (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))) (Set.Ioi 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from by norm_num]
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (f := fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))))
      (n := (1 : WithTop ℕ∞)) isOpen_Ioi).mpr ⟨hdiff_f, ?_, ?_⟩
    · intro h
      exact absurd h (by norm_num)
    · exact hcont1
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ)
      = (fun z => ∫ θ, F z θ * φ θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))) from by
    funext z
    rw [hμ]]
  exact hgoal

end Work.FTS_RegExport.RXT
end
end
