/-
# `gam_rad_integral_le` — the `θ`-integral of the `ℋⁿ`-integrand of `Γ(θ)·r(z)`

The transfer `E2 α f = Ê₂ f + Γ(θ)·radS α f z` of the coercivity argument carries an angular
profile `Γ(θ) = (sin θ cos²θ)^{α/3}` times a radial function `r(z)`.  Bounding the `ℋⁿ`-norm of
this defect needs the `θ`-slice integral of the `ℋⁿ`-integrand of `Γ·r` to be controlled by the
radial density `Σ_{j ≤ n} (D_z^j r)² w²` with a constant **uniform in `α ∈ (0,1]` and `n ≤ 3`**.

That is what this file proves:

  `∃ K, 0 ≤ K ∧ ∀ α ∈ (0,1], ∀ n ≤ 3, ∀ r, ∀ z ∈ Iz,
      ∫_θ HkIntegrand α n (fun z θ => Γ(α,θ) * r z) z θ
        ≤ K · Σ_{j ≤ n} (D_z^j r z)² w(z)².`

## Proof

* The pointwise separation of an angular profile and a radial function
  (`HkIntegrand_ang_rad_le_n`, the level-`n` version of
  `NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le`) turns the integrand into

    `RintN n r z · ((a θ)² σ(θ) + 4 B1² (G θ)² τ(α,θ))`,

  where `RintN n r z = Σ_{i ≤ n} (D_z^i r z)² w(z)²`, `σ = sin(2θ)^{-η}` is the light angular
  weight and `τ = sin(2θ)^{-γ}` the heavy one.  Here `a = Γ(α,·)`, `B0 = 1` (since `Γ ≤ 1`) and
  the angular-jet hypothesis holds with

    `B1 = 10^5·α`,   `G θ = sin(2θ)^{α/5}`,

  because `|D_θ^i Γ| ≤ 10^5·α·Γ ≤ 10^5·α·sin(2θ)^{α/5}` for `1 ≤ i ≤ 4`: the `α`-power is the
  content of `dthU_iter_Gam_abs_bound` (`D_θ^{j+1}Γ = α·Tfun j·Γ`), and the exponent `α/5` is
  `LocData.Gam_le_sin_two_rpow` (`Γ ≤ sin(2θ)^{α/5}`).

* Both angular weights are then *integrable with `α`-uniform bounds that multiply out*:
  `∫_θ σ ≤ 10^4` (`Spaces.sin_two_rpow` at exponent `-η`, whose `-η + 1 = 1/100`), and
  `(G θ)² τ(α,θ) = sin(2θ)^{2α/5 - γ}` (`rpow_sq_smG_eq`) with
  `2α/5 - γ = -1 + 3α/10 < 0`, so
  `∫_θ sin(2θ)^{2α/5-γ} ≤ 100/(3α/10) = 1000/(3α)` — the divergence as `α → 0⁺` is exactly
  cancelled by the `α²` in `B1²`, giving `4 B1² ∫ ≤ 4·10^{10}α²·(1000/(3α)) ≤ 4·10^{13}/3`.

* Hence `K = 2·10^{13}` works uniformly.

All constants are `α`-independent; `n` enters only through `n ≤ 3`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_VsW_mul_Gs_le
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.LocData.DthIter_Gam_Pf
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.HkIntegrand_ang_rad_le_n
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

open Work.FTS.Nonlinear.RadialProd (smE smG)

set_option maxHeartbeats 1600000

/-! ## The level-`n` radial density -/

/-- `RintN n r z = Σ_{i ≤ n} (D_z^i r z)² w(z)²`: the radial density that the `θ`-integral of
the `ℋⁿ`-integrand of a product `a(θ)·r(z)` is bounded by.  (`Rint r` of
`Nonlinear.RadialProd` is the case `n = 4`.) -/
def RintN (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2

theorem RintN_nonneg (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : 0 ≤ RintN n r z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## The angular jet of `Γ`, with the sharp factor `α` -/

/-- **`|D_θ^i Γ(α,·)| ≤ 10^5·α·Γ(α,·)` for `1 ≤ i ≤ 4`.**  This is the `α`-carrying refinement
of `LocData.DthIter_Gam_abs_le`: since `D_θ^{j+1}Γ = α·Tfun j α·Γ` and `|Tfun j| ≤ 10^5` for
`j ≤ 3`, every one of the `D_θ`-iterates of `Γ` beyond order `0` gains a full factor `α`.
That factor is what makes the weighted `θ`-integrals of the heavy slots uniformly bounded as
`α → 0⁺`. -/
theorem DthIter_Gam_abs_le_alpha (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 100000 * α * Work.Spaces.Gam α θ := by
  have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
    fun θ' _ => Work.FTS.LocData.Tfun_abs_le (i - 1) (by omega) α hα hα1 θ'
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi α hα 100000 hT θ hθ
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
  calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
    _ = 100000 * α * Work.Spaces.Gam α θ := by ring

/-! ## The heavy angular weight of the sharp profile, with its exponent combined -/

/-- **`(sin 2θ^{α/5})² · sin(2θ)^{-γ} = sin(2θ)^{2α/5-γ}` on `Iθ`.**  Folding the squared profile
`G θ = sin(2θ)^{α/5}` into the heavy weight `τ = sin(2θ)^{-γ}` produces the single `rpow`
`sin(2θ)^{2α/5-γ}` whose exponent `2α/5 - γ = -1 + 3α/10` lies in `(-1,0)` for `α ∈ (0,1]`, so
its `θ`-integral is finite and computable (`Spaces.sin_two_rpow`).  At the two endpoints
`θ ∈ {0, π/2}` both sides vanish. -/
theorem rpow_sq_smG_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ
      = (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · have hz1 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = 0 := by
      rw [← hs, Real.zero_rpow (by positivity : α / 5 ≠ 0)]
      norm_num
    have hz2 : smG α θ = 0 := by
      rw [smG, ← hs]
      exact Real.zero_rpow (by rw [Work.Spaces.gam]; linarith : -(Work.Spaces.gam α) ≠ 0)
    have hz3 : (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) = 0 := by
      rw [← hs]
      apply Real.zero_rpow
      rw [Work.Spaces.gam]
      intro h
      nlinarith [hα, hα1]
    rw [hz1, hz2, hz3]
    norm_num
  · have hpu : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
      refine ((Real.rpow_natCast ((Real.sin (2 * θ)) ^ (α / 5)) 2).symm).trans ?_
      refine ((Real.rpow_mul (le_of_lt hs) (α / 5) 2).symm).trans ?_
      rw [show (α / 5) * 2 = 2 * (α / 5) by ring]
    rw [hpu, smG, ← Real.rpow_add hs,
      show 2 * (α / 5) + -(Work.Spaces.gam α) = 2 * (α / 5) - Work.Spaces.gam α by ring]

/-! ## The target -/

theorem gam_rad_integral_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ r : ℝ → ℝ,
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ)
          ≤ K * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  refine ⟨20000000000000, by norm_num, ?_⟩
  intro α hα hα1 n hn r z _hz
  have hB1pos : (0 : ℝ) < 100000 * α := by linarith
  -- the angular hypotheses for the level-`n` separation
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ (1 : ℝ) := fun θ hθ => by
    have h := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg h.1]; exact h.2
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (100000 * α) * (fun θ' => (Real.sin (2 * θ')) ^ (α / 5)) θ := by
    intro i hi hin θ hθ
    have hi4 : i ≤ 4 := by omega
    refine (DthIter_Gam_abs_le_alpha i hi hi4 α hα hα1 hθ).trans ?_
    exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ) (le_of_lt hB1pos)
  -- the pointwise bound, with the two angular weights combined
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ
        ≤ RintN n r z * (smE θ
            + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := by
    intro θ hθ
    have h := HkIntegrand_ang_rad_le_n (n := n) (by omega) (α := α)
      (a := fun θ => Work.Spaces.Gam α θ) (r := r) (G := fun θ' => (Real.sin (2 * θ')) ^ (α / 5))
      (B0 := 1) (B1 := 100000 * α) (z := z) (θ := θ) ha0 ha1 hθ
    refine h.trans ?_
    simp only [RintN]
    refine mul_le_mul_of_nonneg_left ?_
      (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hfac : (4 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ
        = (4 : ℝ) * (100000 * α) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
      rw [show (4 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ
            = (4 : ℝ) * (100000 * α) ^ 2
              * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ) from by ring,
        rpow_sq_smG_eq α hα hα1 hθ]
    have hone : (1 : ℝ) ^ 2 * smE θ = smE θ := by ring
    simpa only [hfac, hone] using le_rfl
  -- integrability of the two angular weights
  have hIe : IntegrableOn (fun θ : ℝ => smE θ) Work.Spaces.Iθ := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hIex : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow _ hp1 hp2).1
  have hdom : IntegrableOn (fun θ : ℝ => RintN n r z * (smE θ
      + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
      Work.Spaces.Iθ :=
    (hIe.add (hIex.const_mul _)).const_mul _
  have hmono : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, RintN n r z * (smE θ
          + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α n _ z θ)
      hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
  have hval : (∫ θ in Work.Spaces.Iθ, RintN n r z * (smE θ
        + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
      = RintN n r z * ((∫ θ in Work.Spaces.Iθ, smE θ)
          + 4 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hIe (hIex.const_mul _), MeasureTheory.integral_const_mul]
  -- the two numerical bounds for the `θ`-integrals
  have hIe_le : (∫ θ in Work.Spaces.Iθ, smE θ) ≤ 10000 := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
    have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hexp] at h
    have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
    rw [h2] at h
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hIex_le : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
      ≤ 1000 / (3 * α) := by
    have h := (Work.Spaces.sin_two_rpow _ hp1 hp2).2
    have hexp : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
      rw [Work.Spaces.gam]; ring
    rw [hexp] at h
    have heq : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
      have h1 : (3 : ℝ) * α ≠ 0 := by positivity
      have h2 : (3 : ℝ) * α / 10 ≠ 0 := by positivity
      field_simp
      ring
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
        ≤ 100 / (3 * α / 10) := h
      _ = 1000 / (3 * α) := heq
  have hkey : 10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α)) ≤ 20000000000000 := by
    have heq : 4 * (100000 * α) ^ 2 * (1000 / (3 * α)) = (40000000000000 / 3) * α := by
      have h1 : α ≠ 0 := ne_of_gt hα
      field_simp
      ring
    rw [heq]
    nlinarith [hα1]
  -- assemble
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, RintN n r z * (smE θ
          + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := hmono
    _ = RintN n r z * ((∫ θ in Work.Spaces.Iθ, smE θ)
          + 4 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := hval
    _ ≤ RintN n r z * (10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (RintN_nonneg n r z)
        have h4 : (0 : ℝ) ≤ 4 * (100000 * α) ^ 2 := by positivity
        linarith [hIe_le, mul_le_mul_of_nonneg_left hIex_le h4]
    _ ≤ 20000000000000 * RintN n r z := by
        calc RintN n r z * (10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α)))
            ≤ RintN n r z * 20000000000000 :=
              mul_le_mul_of_nonneg_left hkey (RintN_nonneg n r z)
          _ = 20000000000000 * RintN n r z := by ring
    _ = 20000000000000 * (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        simp only [RintN]

end Work.FTS.CoercivityFix.Transfer.E2norm
