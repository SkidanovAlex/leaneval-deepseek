/-
# `Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6`

**The mean-term form of the radial `D_z`-slot bound, at level six, for a datum which is only
`C⁶` on the open quadrant.**  For `g` with `ContDiffOn ℝ 6 (uncurry g) Q0` and honest `ℋ⁶`
(`Work.Spaces.HkMem α 6 g`),

`(D_z^d g(z,θ) · w z)² ≤ C ( w z² ∫_σ (D_z^d g(z,σ))² + (γ-1)⁻¹ Aang α g d z )`,  `d ≤ 5`,

with `C` universal.  This is the *finite-order* version of
`Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6` (whose hypothesis is the much stronger
`SmoothOpen g`, i.e. `C^∞` on the open quadrant).

Route (verbatim from the `C^∞` sibling, with every smoothness input re-derived at order six):

* the angular Hardy inequality with a mean term, `Work.FTS.OpenPkg.ProdOpen.sob_theta_mean`,
  applied to the slice `h = D_z^d g(z,·)` at the fixed `z > 0`: it only needs `h` differentiable
  on `(0,π/2)` with continuous derivative, which is `C^{d+1}` of `g`; the slice is `C¹` because
  `d + 1 ≤ 6` (`contDiffOn_uncurry_DzIter_le` + `contDiffOn_slice_snd_of_uncurry`);
* the identification of the derivative term with the mixed slot uses
  `∂_θ (D_z^d g) = D_z^d (∂_θ g)` on the open quadrant, which is the iterated Clairaut identity
  `pth_DzIter_eqOn_of_contDiffOn`: it needs only `d + 1 ≤ 6` (the `d`-th radial iterate is `C²`
  when `d + 2 ≤ 6`), plus the fact that an angular multiplier passes through `D_z`-iterates
  (`sda_DzIter_const_mul_th`);
* `(h')² sin(2σ)^{2-γ} = (D_z^dD_θ g(z,σ))² sin(2σ)^{-γ}` (`deriv_mixed_weight_cd6`) and
  `(D_z^dD_θ g · W)² = (w z)² (D_z^dD_θ g)² sin(2·)^{-γ}` (`Wt_sq_eq`) give *exactly*
  `(w z)² ∫_σ (h')² sin(2·)^{2-γ} = Aang α g d z`;
* the two integrability hypotheses come from `HkMem α 6 g` (the radial slot `d ≤ 6` and the
  mixed slot `1 + d ≤ 6`, i.e. `d ≤ 5`) and the a.e. strong measurability of the slices.

All declarations are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.GalBasis.GalDense.Xmb
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Finite-order calculus on an open set -/

/-- `D_z = z ∂_z` costs one order of differentiability. -/
theorem contDiffOn_uncurry_Dz_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dz f)) V := by
  have hpz := Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pz_le hV (n := n) h
  have hfun : Function.uncurry (Work.Spaces.Dz f)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz f) p := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [hfun]
  exact contDiffOn_fst.mul hpz

/-- The iterated curvilinear radial derivative `D_z^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_DzIter_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry f) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter i f)) V := by
  intro i
  induction i with
  | zero =>
      intro k hk
      simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DzIter i f)) V := ih (k + 1) (by omega)
      simpa only [Work.Spaces.DzIter_succ] using contDiffOn_uncurry_Dz_le hV h2

/-- The angular slice of a function that is `C^n` on a product of sets is `C^n` on the second
factor. -/
theorem contDiffOn_slice_snd_of_uncurry {f : ℝ → ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (h : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry f) (s ×ˢ t)) {z : ℝ}
    (hz : z ∈ s) : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ => f z θ) t := by
  have hcomp := h.comp ((contDiffOn_const (c := z)).prodMk contDiffOn_id)
    (fun θ hθ => ⟨hz, hθ⟩)
  exact hcomp.congr (fun θ _ => rfl)

/-- The angular slice of a function that is `C^n` at a point of an open set is `C^n` there. -/
theorem contDiffAt_slice_snd_of_uncurry {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry f) V) {z θ : ℝ}
    (hzθ : (z, θ) ∈ V) : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ' => f z θ') θ := by
  have hc : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry f) (z, θ) :=
    h.contDiffAt (hV.mem_nhds hzθ)
  have hlin : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa only [Function.comp_def, Function.uncurry] using hc.comp θ hlin

/-- **Differentiability of the angular slice.**  The slice `θ ↦ f z θ` of a function that is
`C¹` on the product `s ×ˢ (0,π/2)` is differentiable on `(0,π/2)`. -/
theorem hasDerivAt_slice_snd_Ioo {f : ℝ → ℝ → ℝ} {s : Set ℝ}
    (h : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) (s ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    {z θ : ℝ} (hz : z ∈ s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    HasDerivAt (fun θ' => f z θ') (deriv (fun θ' => f z θ') θ) θ := by
  have hslice := contDiffOn_slice_snd_of_uncurry (n := 1) h hz
  have hc : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun θ' => f z θ') θ :=
    hslice.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  exact (hc.differentiableAt (by simp)).hasDerivAt

/-! ## Clairaut with radial iterates at finite order -/

/-- Pointwise Clairaut for `∂_θ` and `D_z = z ∂_z`: at a point where the uncurried `f` is `C²`,
`∂_θ (z ∂_z f) = z ∂_z (∂_θ f)`. -/
private lemma pth_Dz_eq_of_contDiffAt_two {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz f z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.pth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := rfl
  rw [h1, h2, (Work.Spaces.pz_pth_comm h).symm]

/-- **`∂_θ` commutes with every iterate of `D_z` at finite order.**  On an open set `V` where `g`
is `C^N`, and for `j + 1 ≤ N`, the plain angular derivative `∂_θ` commutes with `D_z^j`:

`∂_θ (D_z^j g) = D_z^j (∂_θ g)` on `V`.

(`D_z^j g` is `C²` as soon as `j + 2 ≤ N`, which is what Clairaut needs at the induction step;
the induction hypothesis is then used at level `j`, requiring only `j + 1 ≤ N`.) -/
theorem pth_DzIter_eqOn_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    {N : ℕ} (hg : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry g) V) :
    ∀ j : ℕ, j + 1 ≤ N →
      Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j g)))
        (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth g))) V := by
  intro j
  induction j with
  | zero => intro _ y _; rfl
  | succ j ih =>
      intro hj y hy
      obtain ⟨a, b⟩ := y
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j g)) (a, b) :=
        (contDiffOn_uncurry_DzIter_le hV hg j 2 (by omega)).contDiffAt (hV.mem_nhds hy)
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) a b
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j g)) a b :=
        pth_Dz_eq_of_contDiffAt_two hcd
      show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) a b
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth g)) a b
      rw [hstep]
      show a * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter j g)) a b
          = a * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth g)) a b
      rw [Work.Spaces.pz_congr_of_isOpen hV (ih (by omega)) hy]

/-! ## The mixed slot is the angular derivative of the radial iterate -/

/-- **The mixed slot identity at finite order.**  For `g` of class `C⁶` on the open quadrant
`Q0` and `d ≤ 5`, on `Q0`:

`D_z^d D_θ g = sin(2θ) · ∂_θ(D_z^d g)`. -/
theorem mixed_one_eq_sin_pth_cd6 {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) {d : ℕ} (hd : d ≤ 5)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.mixed d 1 g z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hV := pth_DzIter_eqOn_of_contDiffOn (V := Work.FTS.EllipticEst.Q0) (N := 6)
    Work.FTS.EllipticEst.isOpen_Q0 hg d (by omega) hQ
  have hVs : Work.Spaces.DzIter d (Work.Spaces.pth g) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by
    simpa only [Function.uncurry] using hV.symm
  calc Work.Spaces.mixed d 1 g z θ
      = Work.Spaces.DzIter d (Work.Spaces.Dth g) z θ := rfl
    _ = Work.Spaces.DzIter d (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth g z θ) z θ := rfl
    _ = Real.sin (2 * θ) * Work.Spaces.DzIter d (Work.Spaces.pth g) z θ :=
        Work.FTS.TransportS.SupDzAux.sda_DzIter_const_mul_th (fun θ' => Real.sin (2 * θ'))
          (Work.Spaces.pth g) d z θ
    _ = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by rw [hVs]

/-- **The weight identity for the angular derivative at finite order:** the square of the angular
derivative of the radial iterate, against the weight `sin(2σ)^{2-γ}`, is the square of the mixed
slot against `sin(2σ)^{-γ}`. -/
theorem deriv_mixed_weight_cd6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) {d : ℕ} (hd : d ≤ 5)
    {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
  have hshift : Work.Spaces.mixed d 1 g z σ
      = Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z σ :=
    mixed_one_eq_sin_pth_cd6 hg hd hz hσ
  have hsp : Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ 2 * Real.sin (2 * σ) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
      Real.rpow_add hsin, Real.rpow_two]
  have hd0 : deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ
      = Work.Spaces.pth (Work.Spaces.DzIter d g) z σ := rfl
  rw [hd0, hshift, mul_pow, hsp]
  ring

/-! ## The mean-term bound -/

theorem dzIter_w_mean_le6_cd6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g → d ≤ 5 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ C * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
            + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  refine ⟨C, hCpos, ?_⟩
  intro α g d hα hα1 hg hmem hd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hZpos : 0 < Work.Spaces.w z := Work.FTS.OpenPkg.ProdOpen.w_pos_of_pos hz
  have hZne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hZpos.ne'
  -- ### the angular slice `σ ↦ D_z^d g (z,σ)` is `C¹` on the open interval
  have hDz1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DzIter d g)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_DzIter_le (N := 6) Work.FTS.EllipticEst.isOpen_Q0 hg d 1 (by omega)
  have hslice1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_slice_snd_of_uncurry (n := 1) hDz1 hz
  -- ### the mixed slot `D_z^d D_θ g` is continuous along the slice
  have hpthg : ContDiffOn ℝ ((5 : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth g))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pth_le Work.FTS.EllipticEst.isOpen_Q0 (n := 5) hg
  have hDzP0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DzIter d (Work.Spaces.pth g))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_DzIter_le (N := 5) Work.FTS.EllipticEst.isOpen_Q0 hpthg d 0 (by omega)
  have hsliceP : ContinuousOn (fun σ' : ℝ => Work.Spaces.DzIter d (Work.Spaces.pth g) z σ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (contDiffOn_slice_snd_of_uncurry (n := 0) hDzP0 hz).continuousOn
  have hpoint : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ
        = Work.Spaces.DzIter d (Work.Spaces.pth g) z σ := by
    intro σ hσ
    have hQ : (z, σ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hσ.1, hσ.2⟩
    have h := pth_DzIter_eqOn_of_contDiffOn (V := Work.FTS.EllipticEst.Q0) (N := 6)
      Work.FTS.EllipticEst.isOpen_Q0 hg d (by omega) hQ
    simpa only [Function.uncurry, Work.Spaces.pth] using h
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => Work.Spaces.DzIter d g z σ')
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') x) x :=
    fun x hx => hasDerivAt_slice_snd_Ioo hDz1 hz hx
  have hcont : ContinuousOn (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsliceP.congr fun σ hσ => hpoint σ hσ
  -- ### the two integrability hypotheses of the angular inequality
  have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.DzIter d g z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 z hz.le)
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (g := fun σ : ℝ =>
        (Work.Spaces.DzIter d g z σ) ^ 2) (hslice1.continuousOn.pow 2)) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα g d 0 (by omega) hz hσ.1 hσ.2
  have hsinC : ContinuousOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.rpow_const
      (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ)))
  have hderivC : ContinuousOn (fun σ : ℝ =>
      (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont.pow 2).mul hsinC
  have hint2 : IntegrableOn (fun σ : ℝ =>
      (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine Integrable.mono' ((hmem.1 z hz.le).const_mul (((Work.Spaces.w z) ^ 2)⁻¹))
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (g := fun σ : ℝ =>
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) hderivC) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    have hmw := deriv_mixed_weight_cd6 (α := α) hg hd hz hσ
    have hnn : 0 ≤ (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
    rw [Real.norm_of_nonneg hnn, hmw]
    have hX : (Work.Spaces.mixed d 1 g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        = (((Work.Spaces.w z) ^ 2)⁻¹) * ((Work.Spaces.w z) ^ 2
            * ((Work.Spaces.mixed d 1 g z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))) := by
      rw [← mul_assoc, inv_mul_cancel₀ hZne, one_mul]
    rw [hX]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg _))
    have hkey : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
      rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
      ring
    rw [hkey]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z σ 1 d (by norm_num) (by omega)
  -- ### the angular Hardy inequality with the mean term
  have hmain := hC α (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') θ hα hα1 hθ hder hcont
    hint1 hint2
  -- ### the derivative term is exactly `Aang α g d z`, up to the radial weight
  have hAang : (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = Work.FTS.H2.WPQ.Aang α g d z := by
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))
        = (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
            (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) _ _
    rw [← hstep, Work.FTS.H2.WPQ.Aang]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    rw [deriv_mixed_weight_cd6 (α := α) hg hd hz hσ, mul_pow,
      Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    ring
  -- ### assembly
  calc (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter d g z θ) ^ 2 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (C * ((∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ,
              (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ,
                  (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
                    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))) := by ring
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by rw [hAang]

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
