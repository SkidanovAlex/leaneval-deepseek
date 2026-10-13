/-
# Time-Hölder continuity of the physical vorticity of a `RegPkg` profile

The physical vorticity of the route is

  `physVort α A B g x τ = A(τ)⁻¹ • F(ρ(x)^{3α}/B(τ), θ(x), τ) • e_θ(x)`,

with `F = F_* + g` the full self-similar profile, `A` the amplitude and `B` the scaling clock.
This module proves that

  `τ ↦ physVort α A B g x τ`

is `α`-Hölder on the strip `[0,S]`, *uniformly in `x ∈ ℝ³`*.

The structure of the argument is the following.

* The physical vorticity is the scalar
  `Φ(τ) = A(τ)⁻¹ · F(ρ(x)^{3α}/B(τ), θ(x), τ)` times the fixed vector `e_θ(x)`, and
  `‖e_θ(x)‖ ≤ 1`.  The `θ < 0` branch of the profile is the odd extension, so everything reduces
  to the absolute angle `|θ(x)| ∈ Iθ` and a *sign* that factors out.
* The scalar `Φ` is a product of the clock `A(τ)⁻¹` and the profile evaluated on the moving
  self-similar variable `Z(τ) = ρ(x)^{3α}/B(τ)`.  The two sources of `τ`-variation are
  (i) the *explicit* `τ`-dependence of the profile, controlled by the joint `α`-Hölder data
  (`Jet`) of `g`, and (ii) the *motion* of `Z(τ)`, controlled by the `Lipschitz` bound on `B`
  coming from `hBdiff`/`hBd`.
* (ii) is harmless only because the profile is *compactly supported* in `z` (`hsupp`): as soon as
  `ρ^{3α} > L·b₁` both values of the profile vanish, and otherwise `ρ^{3α} ≤ L·b₁` *bounds the
  motion* `|Z τ - Z τ'| ≤ c·|τ - τ'|` with the explicit constant `c = L·b₁·b₂/b₀²`.
* `A` is `Lipschitz` on the strip (`hAdiff`/`hAd` and the mean value inequality), and `A ≥ a₀ > 0`
  bounds `A(τ)⁻¹` above; this controls the variation of the prefactor.
* The remaining elementary step is the standard "small/large distance" split: for
  `|τ - τ'| ≤ 1` one uses `|τ - τ'| ≤ |τ - τ'|^α`, for `|τ - τ'| ≥ 1` the uniform bound on the
  scalar `Φ` (from `Fstar_abs_le` and the `Jet` box of `g`) together with `1 ≤ |τ - τ'|^α`.

The companion module `physVort_bound` supplies the two elementary facts `‖e_θ(x)‖ ≤ 1` and
`|θ(x)| ∈ Iθ`.

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
  Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.physVort_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set

namespace Work.FTS.Regularity

/-! ## Elementary tools -/

/-- The triangle inequality for the absolute value, in the form used below (the `norm` version of
Mathlib, transported to `ℝ`). -/
theorem abs_add_le_aux {a b : ℝ} : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

/-- `|a - b| ≤ |a| + |b|`. -/
theorem abs_sub_le_aux {a b : ℝ} : |a - b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_sub_le a b

/-- **Mean value inequality on the strip.**  A function on `[0,S]` whose derivative (in the sense
of `deriv`, supplied by `HasDerivAt` at every point of the strip) is bounded by `C` is
`C`-Lipschitz there. -/
theorem abs_sub_le_of_deriv_bound {S : ℝ} {f : ℝ → ℝ}
    (hd : ∀ τ ∈ Set.Icc 0 S, HasDerivAt f (deriv f τ) τ) {C : ℝ}
    (hC : ∀ τ ∈ Set.Icc 0 S, |deriv f τ| ≤ C) :
    ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |f τ - f τ'| ≤ C * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Icc 0 S)
    (fun x hx => (hd x hx).differentiableAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx) (convex_Icc 0 S) hτ hτ'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (f τ') (f τ), abs_sub_comm τ' τ] at h
  exact h

/-- For `0 ≤ s ≤ 1` and `0 < α ≤ 1` one has `s ≤ s ^ α`. -/
theorem self_le_rpow {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ s ^ α := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hα)]
  · have := Real.rpow_le_rpow_of_exponent_ge h hs1 hα1
    rwa [Real.rpow_one] at this

/-- The radial profile `F_*(z) = 2z/(1+z)²` of the fundamental model is `2`-Lipschitz on
`[0,∞)`: its derivative is `2(1-z)/(1+z)³`, whose absolute value is at most `2` there. -/
theorem FM_Fstar_abs_sub_le {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |Work.FM.Fstar z - Work.FM.Fstar z'| ≤ 2 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (C := (2:ℝ))
    (f := Work.FM.Fstar) (s := Set.Ici (0:ℝ))
    (fun x hx => (Work.FM.hasDerivAt_Fstar x (by linarith [show (0:ℝ) ≤ x from hx])).differentiableAt)
    (fun x hx => ?_) (convex_Ici 0) hz hz'
  · rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    rw [abs_sub_comm (Work.FM.Fstar z') (Work.FM.Fstar z), abs_sub_comm z' z] at h
    exact h
  · have hx0 : (0:ℝ) ≤ x := hx
    rw [Work.FM.deriv_Fstar x (by linarith), Real.norm_eq_abs]
    have hpos : (0:ℝ) < (1 + x) ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hpos]
    rw [div_le_iff₀ hpos]
    have h1 : |1 - x| ≤ 1 + x := by rw [abs_le]; constructor <;> linarith
    have h2 : (1:ℝ) ≤ 1 + x := by linarith
    nlinarith [h1, h2, sq_nonneg (1 + x), hx0]

/-- The profile `F_*(z,θ) = p·(Γ(θ)/c)·2z/(1+z)²` is `20p`-Lipschitz in `z` on `[0,∞)`. -/
theorem Fstar_abs_sub_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z z' θ : ℝ}
    (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ - Work.Construction.Fstar p z' θ| ≤ 20 * p * |z - z'| := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ :=
    Work.ConstructionInstance.Gamma_nonneg (β := p / 3) hθ
  have hG1 : Work.Spaces.Gam p θ ≤ 1 := by
    rw [← Work.ConstructionInstance.Gamma_div_three]
    exact Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
  have hcoef0 : 0 ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) := by positivity
  rw [Work.Construction.Fstar, Work.Construction.Fstar, ← mul_sub, abs_mul, abs_of_nonneg hcoef0]
  have hcoef : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2 ≤ 20 * p := by
    have h2 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
      rw [div_le_iff₀ hcpos]; nlinarith
    nlinarith [hp.le, hG0]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |Work.FM.Fstar z - Work.FM.Fstar z'|
      ≤ p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * |z - z'|) :=
        mul_le_mul_of_nonneg_left (FM_Fstar_abs_sub_le hz hz') hcoef0
    _ = (p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * 2) * |z - z'| := by ring
    _ ≤ (20 * p) * |z - z'| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- The profile of a `τ`-slice is the *sign of the angle* times the full profile evaluated at the
absolute angle `|θ|` (the odd extension of the profile in `θ`). -/
theorem profile_eq_sign_profFull {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (z τ θ : ℝ) :
    Work.ConstructionInstance.profile (pExp α) (gSlice g τ) z θ
      = (if 0 ≤ θ then (1:ℝ) else -1) * profFull α g z |θ| τ := by
  by_cases h : 0 ≤ θ
  · rw [ite_eq_left h, Work.ConstructionInstance.profile_of_nonneg h, abs_of_nonneg h]
    simp [profFull, one_mul]
  · rw [ite_eq_right h, Work.ConstructionInstance.profile_of_neg h, abs_of_neg (not_le.mp h)]
    simp [profFull]

/-! ## Joint `α`-Hölder continuity of the profile in `(z,τ)` -/

/-- **The full profile is jointly `α`-Hölder in `(z,τ)` at fixed angle.**  This is the quantitative
input from which the time-regularity of the physical vorticity is read off: the `g`-part is the
joint `α`-Hölder datum of `RegPkg.hg` in `(z,τ)` (the angular increment is `0`), and the
`F_*`-part is `Lipschitz` in `z` and bounded in `z`, so that the two regimes `t ≤ 1` and `t ≥ 1`
of the metric `t = |Δz| + |Δτ|` both give `C·t^α`. -/
theorem profFull_holder_ztau {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' θ τ τ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
      |profFull α g z θ τ - profFull α g z' θ τ'| ≤ C * (|z - z'| + |τ - τ'|) ^ α := by
  obtain ⟨Ng, hJet⟩ := h.hg
  have hNg0 : 0 ≤ Ng := hJet.1
  have hp0 : 0 < pExp α := pExp_pos h.hα
  have hp1 : pExp α ≤ 1 := pExp_le_one h.hα13
  have hα1 : α ≤ 1 := le_trans h.hα13 (by norm_num)
  refine ⟨40 * pExp α + Ng, by positivity, ?_⟩
  intro z z' θ τ τ' hz hz' hθ hτ hτ'
  have hsplit : profFull α g z θ τ - profFull α g z' θ τ'
      = (Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ)
        + (g z θ τ - g z' θ τ') := by
    simp only [profFull]; ring
  have hF := Fstar_abs_sub_le hp0 hp1 hz hz' hθ
  have hJ : |g z θ τ - g z' θ τ'| ≤ Ng * (|z - z'| + |τ - τ'|) ^ α := by
    have h1 := hJet.2.2 z z' θ θ τ τ' hz hz' hθ hθ hτ hτ'
    simpa using h1
  have hT0 : 0 ≤ |z - z'| + |τ - τ'| := by positivity
  rcases le_total (|z - z'| + |τ - τ'|) 1 with hT1 | hT1
  · have hTp : |z - z'| + |τ - τ'| ≤ (|z - z'| + |τ - τ'|) ^ α :=
      self_le_rpow h.hα hα1 hT0 hT1
    have h20 : 0 ≤ 20 * pExp α := by positivity
    have hstep : 20 * pExp α * |z - z'| ≤ 20 * pExp α * (|z - z'| + |τ - τ'|) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) h20
    calc |profFull α g z θ τ - profFull α g z' θ τ'|
        ≤ |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
          + |g z θ τ - g z' θ τ'| := by rw [hsplit]; exact abs_add_le_aux
      _ ≤ 20 * pExp α * (|z - z'| + |τ - τ'|) + Ng * (|z - z'| + |τ - τ'|) ^ α :=
          add_le_add (le_trans hF hstep) hJ
      _ ≤ 20 * pExp α * (|z - z'| + |τ - τ'|) ^ α + Ng * (|z - z'| + |τ - τ'|) ^ α := by
          have h := mul_le_mul_of_nonneg_left hTp h20
          linarith
      _ = (20 * pExp α + Ng) * (|z - z'| + |τ - τ'|) ^ α := by ring
      _ ≤ (40 * pExp α + Ng) * (|z - z'| + |τ - τ'|) ^ α := by
          have h := Real.rpow_nonneg hT0 α
          nlinarith [h, hp0.le]
  · have hTp : (1:ℝ) ≤ (|z - z'| + |τ - τ'|) ^ α := Real.one_le_rpow hT1 h.hα.le
    have hF' : |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
        ≤ 40 * pExp α := by
      have h1 := Work.ConstructionInstance.Fstar_abs_le hp0 hp1 hz hθ
      have h2 := Work.ConstructionInstance.Fstar_abs_le hp0 hp1 hz' hθ
      have hG : Work.ConstructionInstance.Gamma (pExp α / 3) θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one (by positivity) hθ
      have hG0 : 0 ≤ Work.ConstructionInstance.Gamma (pExp α / 3) θ :=
        Work.ConstructionInstance.Gamma_nonneg hθ
      have e1 : |Work.Construction.Fstar (pExp α) z θ| ≤ 20 * pExp α := by
        refine le_trans h1 ?_
        have hm := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ pExp α)
        linarith
      have e2 : |Work.Construction.Fstar (pExp α) z' θ| ≤ 20 * pExp α := by
        refine le_trans h2 ?_
        have hm := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ pExp α)
        linarith
      calc |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
          ≤ |Work.Construction.Fstar (pExp α) z θ| + |Work.Construction.Fstar (pExp α) z' θ| :=
            abs_sub_le_aux
        _ ≤ 20 * pExp α + 20 * pExp α := add_le_add e1 e2
        _ = 40 * pExp α := by ring
    calc |profFull α g z θ τ - profFull α g z' θ τ'|
        ≤ |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ|
          + |g z θ τ - g z' θ τ'| := by rw [hsplit]; exact abs_add_le_aux
      _ ≤ 40 * pExp α + Ng * (|z - z'| + |τ - τ'|) ^ α := add_le_add hF' hJ
      _ ≤ 40 * pExp α * (|z - z'| + |τ - τ'|) ^ α + Ng * (|z - z'| + |τ - τ'|) ^ α := by
          have h1 : 40 * pExp α ≤ 40 * pExp α * (|z - z'| + |τ - τ'|) ^ α :=
            le_mul_of_one_le_right (by positivity) hTp
          linarith
      _ = (40 * pExp α + Ng) * (|z - z'| + |τ - τ'|) ^ α := by ring

/-! ## The time-Hölder continuity -/

theorem physVort_holder_time {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : Work.FTS.Regularity.R3, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      ‖Work.FTS.Regularity.physVort α A B g x τ - Work.FTS.Regularity.physVort α A B g x τ'‖
        ≤ N * |τ - τ'| ^ α := by
  obtain ⟨a₀, a₁, ha₀, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hBb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  obtain ⟨Ng, hJet⟩ := h.hg
  obtain ⟨L, hLpos, hLsupp⟩ := h.hsupp
  obtain ⟨C, hC0, hC⟩ := profFull_holder_ztau h
  have hS : 0 < S := h.hS
  have h0S : (0:ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, hS.le⟩
  have ha₂0 : 0 ≤ a₂ := le_trans (abs_nonneg _) (ha₂ 0 h0S)
  have hb₂0 : 0 ≤ b₂ := le_trans (abs_nonneg _) (hb₂ 0 h0S)
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le (lt_of_lt_of_le hb₀ (hBb 0 h0S).1) (hBb 0 h0S).2
  have hNg0 : 0 ≤ Ng := hJet.1
  have hα1 : α ≤ 1 := le_trans h.hα13 (by norm_num)
  have hAlip := abs_sub_le_of_deriv_bound h.hAdiff ha₂
  have hBlip := abs_sub_le_of_deriv_bound h.hBdiff hb₂
  set p : ℝ := pExp α with hpdef
  have hp0 : 0 < p := by rw [hpdef]; exact pExp_pos h.hα
  have hp1 : p ≤ 1 := by rw [hpdef]; exact pExp_le_one h.hα13
  set M : ℝ := 20 * p + Ng with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  set c : ℝ := L * b₁ * b₂ / b₀ ^ 2 with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc1 : 0 ≤ c + 1 := by linarith
  set K : ℝ := max ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c) + (a₂ / a₀ ^ 2) * M))
    (2 * M / a₀) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine le_trans ?_ (le_max_left _ _)
    have h1 : 0 ≤ (1 / a₀) * (C * (c + 1) ^ α) := by positivity
    have h2 : 0 ≤ (1 / a₀) * (20 * p * c) := by positivity
    have h3 : 0 ≤ (a₂ / a₀ ^ 2) * M := by positivity
    linarith
  refine ⟨K, hK0, ?_⟩
  intro x τ hτ τ' hτ'
  set θ : ℝ := Work.Cyl.theta x with hθdef
  set ϑ : ℝ := |θ| with hϑdef
  have hϑI : ϑ ∈ Work.Spaces.Iθ := by rw [hϑdef]; exact abs_theta_mem_Iθ x
  have hϑ0 : 0 ≤ ϑ := by rw [hϑdef]; exact abs_nonneg θ
  set ρ : ℝ := Work.Cyl.rho x with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Work.Cyl.rho_nonneg x
  set sgn : ℝ := if 0 ≤ θ then (1:ℝ) else -1 with hsgn
  have hsgn1 : |sgn| = 1 := by rw [hsgn]; split_ifs <;> simp
  have hZnn : ∀ s ∈ Set.Icc 0 S, 0 ≤ ρ ^ p / B s := fun s hs =>
    div_nonneg (Real.rpow_nonneg hρ0 p) (h.hB s hs).le
  have hQbound : ∀ s ∈ Set.Icc 0 S, |profFull α g (ρ ^ p / B s) ϑ s| ≤ M := by
    intro s hs
    have hz := hZnn s hs
    have h1 := Work.ConstructionInstance.Fstar_abs_le hp0 hp1 hz hϑI
    have hG : Work.ConstructionInstance.Gamma (p / 3) ϑ ≤ 1 :=
      Work.ConstructionInstance.Gamma_le_one (by positivity) hϑI
    have hG0 : 0 ≤ Work.ConstructionInstance.Gamma (p / 3) ϑ :=
      Work.ConstructionInstance.Gamma_nonneg hϑI
    have h2 := hJet.abs_le hz hϑI hs
    have h3 : |profFull α g (ρ ^ p / B s) ϑ s|
        ≤ 20 * p * Work.ConstructionInstance.Gamma (p / 3) ϑ + Ng := by
      have hprof : profFull α g (ρ ^ p / B s) ϑ s
          = Work.Construction.Fstar p (ρ ^ p / B s) ϑ + g (ρ ^ p / B s) ϑ s := rfl
      rw [hprof]
      exact le_trans abs_add_le_aux (add_le_add h1 h2)
    rw [hMdef]
    have hm := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ p)
    linarith
  have hrepr : ∀ s ∈ Set.Icc 0 S, physVort α A B g x s
      = (sgn * ((A s)⁻¹ * profFull α g (ρ ^ p / B s) ϑ s)) • Work.Cyl.eTheta x := by
    intro s hs
    rw [physVort_apply, Work.ConstructionInstance.omegaSz_apply, smul_smul]
    congr 1
    rw [profile_eq_sign_profFull (α := α) (g := g) (ρ ^ p / B s) s θ, ← hsgn, hϑdef]
    ring
  have hdiff : physVort α A B g x τ - physVort α A B g x τ'
      = (sgn * ((A τ)⁻¹ * profFull α g (ρ ^ p / B τ) ϑ τ)
          - sgn * ((A τ')⁻¹ * profFull α g (ρ ^ p / B τ') ϑ τ')) • Work.Cyl.eTheta x := by
    rw [hrepr τ hτ, hrepr τ' hτ', ← sub_smul]
  set X : ℝ := (A τ)⁻¹ * profFull α g (ρ ^ p / B τ) ϑ τ with hXdef
  set Y : ℝ := (A τ')⁻¹ * profFull α g (ρ ^ p / B τ') ϑ τ' with hYdef
  have hAτ0 : 0 < A τ := h.hA τ hτ
  have hAτ'0 : 0 < A τ' := h.hA τ' hτ'
  have hinvτ : (A τ)⁻¹ ≤ 1 / a₀ := by
    simpa using one_div_le_one_div_of_le ha₀ (hAb τ hτ).1
  have hinvτ' : (A τ')⁻¹ ≤ 1 / a₀ := by
    simpa using one_div_le_one_div_of_le ha₀ (hAb τ' hτ').1
  have hbX : |X| ≤ M / a₀ := by
    rw [hXdef, abs_mul, abs_of_pos (inv_pos.mpr hAτ0)]
    calc (A τ)⁻¹ * |profFull α g (ρ ^ p / B τ) ϑ τ| ≤ (1 / a₀) * M :=
          mul_le_mul hinvτ (hQbound τ hτ) (abs_nonneg _) (by positivity)
      _ = M / a₀ := by ring
  have hbY : |Y| ≤ M / a₀ := by
    rw [hYdef, abs_mul, abs_of_pos (inv_pos.mpr hAτ'0)]
    calc (A τ')⁻¹ * |profFull α g (ρ ^ p / B τ') ϑ τ'| ≤ (1 / a₀) * M :=
          mul_le_mul hinvτ' (hQbound τ' hτ') (abs_nonneg _) (by positivity)
      _ = M / a₀ := by ring
  have hcore : |X - Y| ≤ K * |τ - τ'| ^ α := by
    by_cases hcase : ρ ^ p ≤ L * b₁
    · have hZp : |ρ ^ p / B τ - ρ ^ p / B τ'| ≤ c * |τ - τ'| := by
        have hBτ : 0 < B τ := h.hB τ hτ
        have hBτ' : 0 < B τ' := h.hB τ' hτ'
        have hnum : |B τ' - B τ| ≤ b₂ * |τ - τ'| := by
          rw [abs_sub_comm]; exact hBlip τ hτ τ' hτ'
        have hden : b₀ ^ 2 ≤ B τ * B τ' := by
          have h1 := (hBb τ hτ).1
          have h2 := (hBb τ' hτ').1
          nlinarith [mul_le_mul h1 h2 hb₀.le hBτ.le]
        have hkey : |ρ ^ p / B τ - ρ ^ p / B τ'|
            = ρ ^ p * (|B τ' - B τ| / (B τ * B τ')) := by
          have hfac : ρ ^ p / B τ - ρ ^ p / B τ'
              = ρ ^ p * ((B τ' - B τ) / (B τ * B τ')) := by
            field_simp
          rw [hfac, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ0 p), abs_div,
            abs_of_pos (mul_pos hBτ hBτ')]
        rw [hkey, hcdef]
        have hstep : |B τ' - B τ| / (B τ * B τ') ≤ (b₂ / b₀ ^ 2) * |τ - τ'| := by
          calc |B τ' - B τ| / (B τ * B τ') ≤ b₂ * |τ - τ'| / (B τ * B τ') :=
                div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hBτ hBτ'))
            _ ≤ b₂ * |τ - τ'| / b₀ ^ 2 :=
                div_le_div_of_nonneg_left (mul_nonneg hb₂0 (abs_nonneg _)) (by positivity) hden
            _ = (b₂ / b₀ ^ 2) * |τ - τ'| := by ring
        calc ρ ^ p * (|B τ' - B τ| / (B τ * B τ'))
            ≤ ρ ^ p * ((b₂ / b₀ ^ 2) * |τ - τ'|) :=
              mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hρ0 p)
          _ ≤ (L * b₁) * ((b₂ / b₀ ^ 2) * |τ - τ'|) :=
              mul_le_mul_of_nonneg_right hcase (by positivity)
          _ = L * b₁ * b₂ / b₀ ^ 2 * |τ - τ'| := by ring
      have hQh := hC (ρ ^ p / B τ) (ρ ^ p / B τ') ϑ τ τ' (hZnn τ hτ) (hZnn τ' hτ') hϑI hτ hτ'
      have hQh' : |profFull α g (ρ ^ p / B τ) ϑ τ - profFull α g (ρ ^ p / B τ') ϑ τ'|
          ≤ C * (c + 1) ^ α * |τ - τ'| ^ α := by
        have hT : |ρ ^ p / B τ - ρ ^ p / B τ'| + |τ - τ'| ≤ (c + 1) * |τ - τ'| := by
          linarith [hZp, abs_nonneg (τ - τ')]
        calc |profFull α g (ρ ^ p / B τ) ϑ τ - profFull α g (ρ ^ p / B τ') ϑ τ'|
            ≤ C * (|ρ ^ p / B τ - ρ ^ p / B τ'| + |τ - τ'|) ^ α := hQh
          _ ≤ C * ((c + 1) * |τ - τ'|) ^ α := by
              refine mul_le_mul_of_nonneg_left ?_ hC0
              exact Real.rpow_le_rpow (by positivity) hT h.hα.le
          _ = C * (c + 1) ^ α * |τ - τ'| ^ α := by
              rw [Real.mul_rpow hc1 (abs_nonneg _)]; ring
      have hinvdiff : |(A τ)⁻¹ - (A τ')⁻¹| ≤ a₂ * |τ - τ'| / a₀ ^ 2 := by
        have h1 : |A τ' - A τ| ≤ a₂ * |τ - τ'| := by
          rw [abs_sub_comm]; exact hAlip τ hτ τ' hτ'
        have hkey : |(A τ)⁻¹ - (A τ')⁻¹| = |A τ' - A τ| / (A τ * A τ') := by
          rw [inv_sub_inv (ne_of_gt hAτ0) (ne_of_gt hAτ'0), abs_div,
            abs_of_pos (mul_pos hAτ0 hAτ'0)]
        rw [hkey]
        have hden : a₀ ^ 2 ≤ A τ * A τ' := by
          have h1' := (hAb τ hτ).1
          have h2' := (hAb τ' hτ').1
          nlinarith [mul_le_mul h1' h2' ha₀.le hAτ0.le]
        calc |A τ' - A τ| / (A τ * A τ') ≤ a₂ * |τ - τ'| / (A τ * A τ') :=
              div_le_div_of_nonneg_right h1 (le_of_lt (mul_pos hAτ0 hAτ'0))
          _ ≤ a₂ * |τ - τ'| / a₀ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg ha₂0 (abs_nonneg _)) (by positivity) hden
      have hdecomp : X - Y = (A τ)⁻¹ * (profFull α g (ρ ^ p / B τ) ϑ τ
            - profFull α g (ρ ^ p / B τ') ϑ τ')
          + ((A τ)⁻¹ - (A τ')⁻¹) * profFull α g (ρ ^ p / B τ') ϑ τ' := by
        rw [hXdef, hYdef]; ring
      have hfirst : |(A τ)⁻¹ * (profFull α g (ρ ^ p / B τ) ϑ τ
            - profFull α g (ρ ^ p / B τ') ϑ τ')|
          ≤ (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α) := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hAτ0)]
        exact mul_le_mul hinvτ hQh' (abs_nonneg _) (by positivity)
      have hsecond : |((A τ)⁻¹ - (A τ')⁻¹) * profFull α g (ρ ^ p / B τ') ϑ τ'|
          ≤ (a₂ * |τ - τ'| / a₀ ^ 2) * M := by
        rw [abs_mul]
        exact mul_le_mul hinvdiff (hQbound τ' hτ') (abs_nonneg _)
          (div_nonneg (mul_nonneg ha₂0 (abs_nonneg _)) (by positivity))
      rcases le_total |τ - τ'| 1 with hsl | hsl
      · have hττ : |τ - τ'| ≤ |τ - τ'| ^ α :=
          self_le_rpow h.hα hα1 (abs_nonneg _) hsl
        have hfin : |X - Y| ≤ ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
              + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α := by
          rw [hdecomp]
          have e1 : |(A τ)⁻¹ * (profFull α g (ρ ^ p / B τ) ϑ τ
                - profFull α g (ρ ^ p / B τ') ϑ τ')
              + ((A τ)⁻¹ - (A τ')⁻¹) * profFull α g (ρ ^ p / B τ') ϑ τ'|
              ≤ (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α)
                + (a₂ * |τ - τ'| / a₀ ^ 2) * M :=
            le_trans abs_add_le_aux (add_le_add hfirst hsecond)
          have hAeq : (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α)
              = ((1 / a₀) * (C * (c + 1) ^ α)) * |τ - τ'| ^ α := by ring
          have h2 : (a₂ * |τ - τ'| / a₀ ^ 2) * M
              ≤ ((a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α := by
            rw [show (a₂ * |τ - τ'| / a₀ ^ 2) * M = ((a₂ / a₀ ^ 2) * M) * |τ - τ'| by ring]
            exact mul_le_mul_of_nonneg_left hττ (by positivity)
          have h3 : ((a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α
              ≤ ((1 / a₀) * (20 * p * c) + (a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α := by
            rw [add_mul]
            exact le_add_of_nonneg_left (by positivity)
          have hsum : (1 / a₀) * (C * (c + 1) ^ α * |τ - τ'| ^ α)
                + (a₂ * |τ - τ'| / a₀ ^ 2) * M
              ≤ ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
                + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α := by
            rw [hAeq]
            have hexp : ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
                + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α
                = ((1 / a₀) * (C * (c + 1) ^ α)) * |τ - τ'| ^ α
                  + ((1 / a₀) * (20 * p * c) + (a₂ / a₀ ^ 2) * M) * |τ - τ'| ^ α := by ring
            rw [hexp]
            exact add_le_add le_rfl (le_trans h2 h3)
          exact le_trans e1 hsum
        calc |X - Y| ≤ ((1 / a₀) * (C * (c + 1) ^ α) + ((1 / a₀) * (20 * p * c)
              + (a₂ / a₀ ^ 2) * M)) * |τ - τ'| ^ α := hfin
          _ ≤ K * |τ - τ'| ^ α := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (abs_nonneg _) α)
              rw [hKdef]
              exact le_max_left _ _
      · have hττ : (1:ℝ) ≤ |τ - τ'| ^ α := Real.one_le_rpow hsl h.hα.le
        have h2M : |X - Y| ≤ 2 * M / a₀ := by
          calc |X - Y| ≤ |X| + |Y| := abs_sub_le_aux
            _ ≤ M / a₀ + M / a₀ := add_le_add hbX hbY
            _ = 2 * M / a₀ := by ring
        calc |X - Y| ≤ 2 * M / a₀ := h2M
          _ ≤ K * |τ - τ'| ^ α := by
              have hmax : 2 * M / a₀ ≤ K := by rw [hKdef]; exact le_max_right _ _
              calc 2 * M / a₀ ≤ K := hmax
                _ = K * 1 := by ring
                _ ≤ K * |τ - τ'| ^ α := mul_le_mul_of_nonneg_left hττ hK0
    · have hfar : ρ ^ p > L * b₁ := lt_of_not_ge hcase
      have hZτ : L ≤ ρ ^ p / B τ := by
        rw [le_div_iff₀ (h.hB τ hτ)]
        calc L * B τ ≤ L * b₁ := mul_le_mul_of_nonneg_left (hBb τ hτ).2 hLpos.le
          _ ≤ ρ ^ p := hfar.le
      have hZτ' : L ≤ ρ ^ p / B τ' := by
        rw [le_div_iff₀ (h.hB τ' hτ')]
        calc L * B τ' ≤ L * b₁ := mul_le_mul_of_nonneg_left (hBb τ' hτ').2 hLpos.le
          _ ≤ ρ ^ p := hfar.le
      have h0τ : profFull α g (ρ ^ p / B τ) ϑ τ = 0 := hLsupp τ hτ _ _ hZτ
      have h0τ' : profFull α g (ρ ^ p / B τ') ϑ τ' = 0 := hLsupp τ' hτ' _ _ hZτ'
      have hzero : X - Y = 0 := by rw [hXdef, hYdef, h0τ, h0τ']; ring
      rw [hzero, abs_zero]
      exact mul_nonneg hK0 (Real.rpow_nonneg (abs_nonneg _) α)
  calc ‖physVort α A B g x τ - physVort α A B g x τ'‖
      = ‖(sgn * X - sgn * Y) • Work.Cyl.eTheta x‖ := by rw [hdiff]
    _ = |sgn * X - sgn * Y| * ‖Work.Cyl.eTheta x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |sgn * X - sgn * Y| * 1 :=
        mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
    _ = |X - Y| := by
        rw [mul_one, show sgn * X - sgn * Y = sgn * (X - Y) by ring, abs_mul, hsgn1, one_mul]
    _ ≤ K * |τ - τ'| ^ α := hcore

end Work.FTS.Regularity
