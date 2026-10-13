/-
# The time-Hölder regularity of `∂ₜω` from **second-order** profile/`λ̄` data

`Work.ConstructionInstance.SelfSimTimeHolderDeriv P` (the residual `hThDt` of finding (H) of
`NOTES.md` §3.5) is the statement that the time derivative of the constructed (cut) self-similar
vorticity `solVort P` is time-`α`-Hölder on every strip `[0,S]`, `S + 1 < T`.

`Tie.timeHolderOnBall_timeDeriv_of_secondDeriv` reduces it to a bound on the *second* time
derivative `∂ₜ²ω` (via the mean value theorem applied to `∂ₜω`,
`timeHolderOnBall_of_timeDeriv_le`), and `Tie.selfSimTimeHolderDeriv_of_secondDerivBound` records
that reduction with the bound as a hypothesis.  This file **produces** that bound from the
second-order data of the self-similar field:

* `hgdiff2`: the profile `F = profile p P.g` is twice differentiable in `z`, with second
  `z`-derivative `pz (pz F)`;
* `hg3`: `|z²·∂_z²F| ≤ Cg''` on the quadrant (the weighted second-derivative box);
* `hlamdif2`: `λ̄` is twice differentiable, with `deriv (deriv P.lam)` as the second derivative;
* `hlamd2`: `|λ̄''| ≤ K₂` on `preWindow T = (-2,T)`.

## The computation

The cut field is `selfSimVort p g L lam y t = χ(ρ(y)/L) · Φ(t) · e_θ(y)` with
`Φ(t) = λ̄(t)⁻¹·F(ρ(y)^p/λ̄(t), θ(y))`, so

  `∂ₜω(y,t) = a · Φ'(t) · e_θ(y)`,   `a = χ(ρ(y)/L)`,

and differentiating once more (`Φ''`, the second-order chain rule
`hasDerivAt_inv_mul_comp2`) gives the value

  `∂ₜ²ω(y,t) = a · X(t) · e_θ(y)`,

  `X(t) = -( λ̄''·G/λ̄² + λ̄'·(-(λ̄'/λ̄)·dd)/λ̄² - 2(λ̄')²·G/λ̄³ )`,

with `G = F(z) + z·∂_zF(z)` and `dd = z·(2∂_zF(z) + z·∂_z²F(z))` at `z = ρ(y)^p/λ̄(t)`.  The two
weighted boxes

  `|G| ≤ 20p + Cg + Cg'`  (`profile_add_z_pz_abs_le`),
  `|z·∂_zF| ≤ 5p + Cg'`   (`z_pz_profile_abs_le`),
  `|z²·∂_z²F| ≤ Cg''`     (`zsq_pz_pz_profile_abs_le`, transported to `|θ| ≤ π/2` by oddness),

together with `|λ̄'| ≤ K`, `|λ̄''| ≤ K₂` and `λ̄ ≥ m > 0` on the strip, bound
`|X| ≤ K₂(20p+Cg+Cg')/m² + K²(2(5p+Cg')+Cg'')/m³ + 2K²(20p+Cg+Cg')/m³`
(`abs_secondDeriv_rescale_le`), while `|a| ≤ 1` and `‖e_θ(y)‖ = 1` (off the axis; on the axis the
field vanishes identically).

## Contents

* `timeDeriv_timeDeriv_selfSimVort`: the slice lemma — `t ↦ ∂ₜω(y,t)` is differentiable with
  derivative `∂ₜ²ω(y,t)`, **and** `∂ₜ²ω(y,t)` obeys the box above (pointwise, for any `m` with
  `0 < m ≤ λ̄(t)`).
* `selfSimTimeHolderDeriv_of_secondOrderData`: the requested theorem, assembled from the slice
  lemma, `lam_pos_le_on_window` (the uniform positive lower bound of `λ̄` on a strip) and
  `timeHolderOnBall_timeDeriv_of_secondDeriv`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.solVort_timeHolder_Icc
import Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le
import Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le_Icc
import Submission.Work.ConstructionInstance.bddDt_selfSimVort
import Submission.Work.ConstructionInstance.lam_sq_timeDeriv_le_Ioo
import Submission.Work.ConstructionInstance.lam_pos_le_on_Icc
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le
import Submission.Work.ConstructionInstance.timeHolderOnBall_selfSimVort
import Submission.Work.ConstructionInstance.hasDerivAt_inv_mul_comp2
import Submission.Work.ConstructionInstance.abs_secondDeriv_rescale_le
import Submission.Work.ConstructionInstance.z_pz_profile_abs_le
import Submission.Work.ConstructionInstance.zsq_pz_pz_profile_abs_le
import Submission.Work.Construction.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Real Topology
open FiniteTimeSingularity

namespace Work.ConstructionInstance

/-! ## The slice lemma: `∂ₜ(∂ₜω)` on the self-similar ansatz -/

/-- **The second time derivative of the constructed (cut) self-similar vorticity.**

For the cut field `ω = selfSimVort p g L lam`, and at a time `t` of the half-window
`preWindow T = (-2,T)`:

* every time slice `s ↦ ∂ₜω(y,s)` is differentiable at `t`, with derivative `∂ₜ²ω(y,t)`
  (the second-order chain rule for `s ↦ λ̄(s)⁻¹·F(c/λ̄(s))`, `hasDerivAt_inv_mul_comp2`; on the
  symmetry axis `radial y = 0` the field vanishes identically);
* and the second derivative obeys the box

  `‖∂ₜ²ω(y,t)‖ ≤ K₂(20p+Cg+Cg')/m² + K²(2(5p+Cg')+Cg'')/m³ + 2K²(20p+Cg+Cg')/m³`

  for every `m` with `0 < m ≤ λ̄(t)` (the weighted boxes of the profile and of `λ̄`).

The hypotheses on `g` are exactly the `St1` data of `ProfileData`: the box `|g| ≤ Cg`, the weighted
first derivative box `|z∂_z g| ≤ Cg'`, the weighted second derivative box `|z²∂_z²F| ≤ Cg''` of
the *full* profile, and the two differentiability clauses. -/
theorem timeDeriv_timeDeriv_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ z : ℝ, g z 0 = 0) {L : ℝ} {lam : ℝ → ℝ} {T m : ℝ} {Cg Cg' Cg'' K K₂ : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ| ≤ Cg'')
    (hgdiff : ∀ z θ : ℝ, 0 < z → HasDerivAt (fun z' => profile p g z' θ)
      (Work.Spaces.pz (profile p g) z θ) z)
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz (profile p g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ) z)
    (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ preWindow T, HasDerivAt lam (deriv lam t) t)
    (hlamdif2 : ∀ t ∈ preWindow T, HasDerivAt (deriv lam) (deriv (deriv lam) t) t)
    (hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ K)
    (hlamd2 : ∀ t ∈ preWindow T, |deriv (deriv lam) t| ≤ K₂)
    (hK : 0 ≤ K) (hK₂ : 0 ≤ K₂)
    {t : ℝ} (ht : t ∈ preWindow T) (hm : 0 < m) (hmle : m ≤ lam t) (y : R3) :
    HasDerivAt (fun s => timeDeriv (selfSimVort p g L lam) y s)
      (timeDeriv (timeDeriv (selfSimVort p g L lam)) y t) t ∧
    ‖timeDeriv (timeDeriv (selfSimVort p g L lam)) y t‖
      ≤ K₂ * (20 * p + Cg + Cg') / m ^ 2 + K ^ 2 * (2 * (5 * p + Cg') + Cg'') / m ^ 3
        + 2 * K ^ 2 * (20 * p + Cg + Cg') / m ^ 3 := by
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgbdd 0 0 le_rfl hI0)
  have hCg' : 0 ≤ Cg' := by simpa using hg2 0 0 le_rfl hI0
  have hCg'' : 0 ≤ Cg'' := by simpa using hg3 0 0 le_rfl hI0
  have hK₂' : 0 ≤ K₂ := le_trans (abs_nonneg _) (hlamd2 t ht)
  have hpne : p ≠ 0 := ne_of_gt hp
  set Λ : ℝ := K₂ * (20 * p + Cg + Cg') / m ^ 2 + K ^ 2 * (2 * (5 * p + Cg') + Cg'') / m ^ 3
      + 2 * K ^ 2 * (20 * p + Cg + Cg') / m ^ 3 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : 0 ≤ K₂ * (20 * p + Cg + Cg') / m ^ 2 :=
      div_nonneg (mul_nonneg hK₂' (by linarith)) (by positivity)
    have h2 : 0 ≤ K ^ 2 * (2 * (5 * p + Cg') + Cg'') / m ^ 3 :=
      div_nonneg (mul_nonneg (sq_nonneg K) (by linarith)) (by positivity)
    have h3 : 0 ≤ 2 * K ^ 2 * (20 * p + Cg + Cg') / m ^ 3 := by positivity
    linarith
  by_cases hrad : Work.Cyl.radial y = 0
  · -- on the symmetry axis the field vanishes identically
    have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : selfSimVort p g L lam y = fun _ => (0 : R3) := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, he0, smul_zero, smul_zero, smul_zero]
    have htd : timeDeriv (selfSimVort p g L lam) y = fun _ => (0 : R3) := by
      funext s
      rw [FiniteTimeSingularity.timeDeriv, hω0]
      exact deriv_const s 0
    have h0 : timeDeriv (timeDeriv (selfSimVort p g L lam)) y t = 0 := by
      rw [FiniteTimeSingularity.timeDeriv, htd]
      simp
    refine ⟨?_, ?_⟩
    · rw [htd, h0]
      exact hasDerivAt_const t 0
    · rw [h0, norm_zero]
      exact hΛ
  · -- off the axis: `ω(y,·) = (a · Φ) • e` with `Φ(s) = λ̄(s)⁻¹ F(c/λ̄(s))`
    have hy : y ≠ 0 := by
      intro h0; exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    set a : ℝ := Work.Stability.chi (Work.Cyl.rho y / L) with ha
    have ha0 : 0 ≤ a := by rw [ha]; exact Work.Stability.chi_nonneg _
    have ha1 : |a| ≤ 1 := by rw [abs_of_nonneg ha0, ha]; exact Work.Stability.chi_le_one _
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hlt : 0 < lam t := hlam t ht
    have hne : lam t ≠ 0 := ne_of_gt hlt
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    have hθabs : |θ| ≤ Real.pi / 2 := by
      rw [hθdef, abs_le]
      exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    -- the three weighted boxes of the profile
    have hGbd : |profile p g (c / lam t) θ + c / lam t * Work.Spaces.pz (profile p g) (c / lam t) θ|
        ≤ 20 * p + Cg + Cg' :=
      profile_add_z_pz_abs_le hp hp1 hgbdd hg2 hgdiff hzpos hθabs
    have hd1 : |(c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ| ≤ 5 * p + Cg' :=
      z_pz_profile_abs_le hp hp1 hg2 hgdiff (c / lam t) θ hzpos hθabs
    have hd2 : |(c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ|
        ≤ Cg'' :=
      zsq_pz_pz_profile_abs_le hpne hg0 hgdiff2 hg3 (c / lam t) θ hzpos hθabs
    have hddbd : |(c / lam t) * (2 * Work.Spaces.pz (profile p g) (c / lam t) θ
        + (c / lam t) * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ)|
        ≤ 2 * (5 * p + Cg') + Cg'' := by
      have hkey : (c / lam t) * (2 * Work.Spaces.pz (profile p g) (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ)
          = 2 * ((c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)
            + (c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ := by
        ring
      rw [hkey]
      calc |2 * ((c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)
              + (c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ|
          ≤ |2 * ((c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)|
              + |(c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ| :=
            abs_add_le _ _
        _ = 2 * |(c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ|
              + |(c / lam t) ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        _ ≤ 2 * (5 * p + Cg') + Cg'' := by linarith
    -- the scalar factors of the ansatz, and their first derivatives
    set φ₀ : ℝ → ℝ := fun s => (lam s)⁻¹ * profile p g (c / lam s) θ with hφ0def
    set φ₁ : ℝ → ℝ := fun s => -(deriv lam s * (profile p g (c / lam s) θ
        + c / lam s * Work.Spaces.pz (profile p g) (c / lam s) θ) / (lam s) ^ 2) with hφ1def
    have hφ : ∀ s ∈ preWindow T, HasDerivAt φ₀ (φ₁ s) s := by
      intro s hs
      have hspos : 0 < c / lam s := div_pos hcpos (hlam s hs)
      have h := hasDerivAt_inv_mul_comp (F := fun z => profile p g z θ) (c := c)
        (hlamdif s hs) (ne_of_gt (hlam s hs)) (hgdiff (c / lam s) θ hspos)
      rw [hφ0def, hφ1def]
      exact h
    have hcut : selfSimVort p g L lam y = fun s => (a * φ₀ s) • e := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, ← ha, ← hc, ← hθdef, ← he, hφ0def]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    set X : ℝ := -(deriv (deriv lam) t * (profile p g (c / lam t) θ
          + c / lam t * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2
        + deriv lam t * (-(deriv lam t / lam t) * ((c / lam t)
            * (2 * Work.Spaces.pz (profile p g) (c / lam t) θ
              + (c / lam t) * Work.Spaces.pz (Work.Spaces.pz (profile p g)) (c / lam t) θ)))
            / (lam t) ^ 2
        - 2 * deriv lam t ^ 2 * (profile p g (c / lam t) θ
            + c / lam t * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 3) with hXdef
    have hX : HasDerivAt φ₁ X t := by
      rw [hφ1def, hXdef]
      exact hasDerivAt_inv_mul_comp2 (hlamdif t ht) (hlamdif2 t ht) hne
        (hgdiff (c / lam t) θ hzpos) (hgdiff2 (c / lam t) θ hzpos)
    have hXbd : |X| ≤ Λ := by
      rw [hXdef, hΛdef]
      exact abs_secondDeriv_rescale_le hm hmle hK hK₂ hGbd hddbd (hlamd t ht) (hlamd2 t ht)
    have hΦ : HasDerivAt (fun s => (a * φ₁ s) • e) ((a * X) • e) t :=
      (hX.const_mul a).smul_const e
    -- `∂ₜω(y,·)` agrees near `t` with `a · φ₁ · e`
    have hev : (fun s => timeDeriv (selfSimVort p g L lam) y s) =ᶠ[𝓝 t] (fun s => (a * φ₁ s) • e) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) ?_
      intro s hs
      have h1 : HasDerivAt (fun u => (a * φ₀ u) • e) ((a * φ₁ s) • e) s :=
        ((hφ s hs).const_mul a).smul_const e
      have h2 : timeDeriv (selfSimVort p g L lam) y s = deriv (fun u => (a * φ₀ u) • e) s := by
        rw [FiniteTimeSingularity.timeDeriv]
        exact congrArg (fun f => deriv f s) hcut
      change timeDeriv (selfSimVort p g L lam) y s = (a * φ₁ s) • e
      rw [h2, h1.deriv]
    have hfin : HasDerivAt (fun s => timeDeriv (selfSimVort p g L lam) y s) ((a * X) • e) t :=
      hΦ.congr_of_eventuallyEq hev
    have hderiv : timeDeriv (timeDeriv (selfSimVort p g L lam)) y t = (a * X) • e := by
      rw [FiniteTimeSingularity.timeDeriv]
      exact hfin.deriv
    refine ⟨?_, ?_⟩
    · rw [hderiv]; exact hfin
    · rw [hderiv]
      have hb : ‖(a * X) • e‖ ≤ Λ := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, he, Work.Cyl.norm_eTheta y hrad, mul_one]
        calc |a| * |X| ≤ 1 * |X| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
          _ = |X| := one_mul _
          _ ≤ Λ := hXbd
      exact hb

/-! ## The requested theorem -/

/-- **The time-Hölder regularity of `∂ₜω` from second-order data.**

The residual `SelfSimTimeHolderDeriv P` of finding (H) follows from the second-order profile and
modulation data: `F` twice differentiable in `z` with `|z²∂_z²F| ≤ Cg''` on the quadrant
(`hgdiff2`, `hg3`), and `λ̄` twice differentiable with `|λ̄''| ≤ K₂` on `preWindow T`
(`hlamdif2`, `hlamd2`).

The proof bounds `∂ₜ²ω` on each strip by the slice lemma `timeDeriv_timeDeriv_selfSimVort`
(with `m` the minimum of `λ̄` on the strip, `lam_pos_le_on_window`) and applies the mean value
theorem to `∂ₜω` (`timeHolderOnBall_timeDeriv_of_secondDeriv`). -/
theorem selfSimTimeHolderDeriv_of_secondOrderData {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)) z θ) z)
    {Cg'' K₂ : ℝ}
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz
        (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)) z θ| ≤ Cg'')
    (hlamdif2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      HasDerivAt (deriv P.lam) (deriv (deriv P.lam) t) t)
    (hlamd2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      |deriv (deriv P.lam) t| ≤ K₂) :
    Work.ConstructionInstance.SelfSimTimeHolderDeriv P := by
  intro S hS hST
  have hp : 0 < profExp α := profExp_pos P.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  have hα1 : (α : ℝ) ≤ 1 := by linarith [P.hα13]
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ P.Cg := le_trans (abs_nonneg _) (bdd_g P 0 0 le_rfl hI0)
  have hCg' : 0 ≤ P.Cg' := by simpa using P.hg2 0 0 le_rfl hI0
  have hCg'' : 0 ≤ Cg'' := by simpa using hg3 0 0 le_rfl hI0
  have hK₂ : 0 ≤ K₂ := le_trans (abs_nonneg _) (hlamd2 0 ⟨by norm_num, P.hT⟩)
  have hsub : Work.StabilityFar.window S ⊆ preWindow P.T := window_subset_preWindow hST
  -- the uniform lower bound of `λ̄` on the strip, and the resulting box `Λ`
  obtain ⟨m, hmpos, hmle⟩ := lam_pos_le_on_window hS hST P.hlam P.hlamdif
  set Λ : ℝ := K₂ * (20 * profExp α + P.Cg + P.Cg') / m ^ 2
      + P.K ^ 2 * (2 * (5 * profExp α + P.Cg') + Cg'') / m ^ 3
      + 2 * P.K ^ 2 * (20 * profExp α + P.Cg + P.Cg') / m ^ 3 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : 0 ≤ K₂ * (20 * profExp α + P.Cg + P.Cg') / m ^ 2 :=
      div_nonneg (mul_nonneg hK₂ (by linarith)) (by positivity)
    have h2 : 0 ≤ P.K ^ 2 * (2 * (5 * profExp α + P.Cg') + Cg'') / m ^ 3 :=
      div_nonneg (mul_nonneg (sq_nonneg P.K) (by linarith)) (by positivity)
    have h3 : 0 ≤ 2 * P.K ^ 2 * (20 * profExp α + P.Cg + P.Cg') / m ^ 3 := by positivity
    linarith
  have hdiff : ∀ z ∈ Metric.closedBall (0 : R3) P.R, ∀ s ∈ Work.StabilityFar.window S,
      HasDerivAt (fun t => timeDeriv (solVort P) z t)
        (timeDeriv (timeDeriv (solVort P)) z s) s := by
    intro z _ s hs
    exact (timeDeriv_timeDeriv_selfSimVort (p := profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) (m := m) (Cg := P.Cg) (Cg' := P.Cg') (Cg'' := Cg'') (K := P.K) (K₂ := K₂)
      hp hp1 P.hvt.1 (bdd_g P) P.hg2 hg3 P.hgdiff hgdiff2 P.hlam P.hlamdif hlamdif2 P.hlamd
      hlamd2 P.hK hK₂ (hsub hs) hmpos (hmle s hs) z).1
  have hbd : ∀ z ∈ Metric.closedBall (0 : R3) P.R, ∀ s ∈ Work.StabilityFar.window S,
      ‖timeDeriv (timeDeriv (solVort P)) z s‖ ≤ Λ := by
    intro z _ s hs
    rw [hΛdef]
    exact (timeDeriv_timeDeriv_selfSimVort (p := profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) (m := m) (Cg := P.Cg) (Cg' := P.Cg') (Cg'' := Cg'') (K := P.K) (K₂ := K₂)
      hp hp1 P.hvt.1 (bdd_g P) P.hg2 hg3 P.hgdiff hgdiff2 P.hlam P.hlamdif hlamdif2 P.hlamd
      hlamd2 P.hK hK₂ (hsub hs) hmpos (hmle s hs) z).2
  exact timeHolderOnBall_timeDeriv_of_secondDeriv (α := (α : ℝ)) (Λ := Λ) (R := P.R) (S := S)
    (ω := solVort P) P.hα hα1 hΛ hdiff hbd

end Work.ConstructionInstance
