/-
# Row 23 of the design table: `|N₄^{**}|_{ℋ⁴} ≤ Cα³`

`N₄^{**}(z,θ) = -(1/2) sin(2θ) · FK(F_*) z · ∂_θF_*(z,θ)` is, by `FK(F_*) = α·2z/(1+z)²`, the
product of an *angular* profile and a *radial* function:

`N₄^{**} = -(1/2) · (α·2 hKer z) · ∂_θF_*(z,θ)`,  `hKer z = z/(1+z)²`,

and `∂_θF_*` is the product of the *radial* factor `(α/c)·F_*(z)` with `Γ'(θ)`.  So
`N₄^{**} = a(θ)·r(z)` with

  `a(θ) = -(2α²/c(α))·D_θΓ(θ)`,   `r(z) = hKer(z)²`

(here `D_θΓ = sin(2θ)Γ'`).  The angular profile `a` is `O(α³)` and its `D_θ`-iterates up to
order `4` decay like `α³·Γ(θ)·(α + sin 2θ)` near the angular boundary (the sharp form
`dthU_pow_Gam_sharp`: `Γ` vanishes at the two endpoints exactly fast enough to compensate the
weight `sin(2θ)^{-γ}`, `γ = 1 + α/10 > 1`, which alone is *not* integrable), while `r ∈ ℋ⁴` with
an `α`-independent norm (`hkerSq_radial`).  The change of variables `a(θ)·r(z)` is therefore
bounded by

  `√(10000·B0² + 4·B1²·M)·|r|_{ℋ⁴}`,  `B0 = 27α³`, `B1 = 20·C·α³`,

with `M ≥ ∫_θ Γ(θ)²(α+sin 2θ)²sin(2θ)^{-γ}dθ` (`gamWeightInt`), i.e. by `Kα³`.

`Xn_ang_rad_le_gen` below is the θ/z-separation estimate of
`Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_ang_rad_le`, with the single power bound
`B1·sin(2θ)^κ` replaced by an *arbitrary* angular profile `G` (`|D_θ^i a| ≤ B1·G`): this is what
allows the sharp weight `G = Γ·(α + sin 2θ)`, whose square times `sin(2θ)^{-γ}` is integrable
*uniformly in α*, whereas `∫_θ sin(2θ)^{2κ-γ}` blows up like `1/α` for the only available `κ`
(`κ ≤ α/3`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
import Submission.Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
import Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The order-one angular bound for `Γ` -/

/-- The first `D_θ`-iterate of `Γ` is `≤ (4/3)αΓ` on the whole closed angular interval:
in the interior `D_θΓ = α q Γ` with `|q| ≤ 4/3`, and at the two endpoints both sides vanish. -/
theorem dthIter_one_Gam_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
  intro θ hθ
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
    Function.iterate_one]
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · rw [Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩, abs_mul, abs_mul, abs_of_pos hα,
        abs_of_nonneg hΓ0]
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun, abs_le]
        constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
          ≤ α * (4 / 3) * Work.Spaces.Gam α θ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hq (le_of_lt hα)) hΓ0
        _ = (4 / 3) * α * Work.Spaces.Gam α θ := by ring
    · subst h1
      rw [Work.Spaces.dthU_apply, show 2 * (Real.pi / 2) = Real.pi from by ring,
        Real.sin_pi, zero_mul, abs_zero, Work.Spaces.Gam_zero_right α (ne_of_gt hα)]
      simp
  · subst h0
    rw [Work.Spaces.dthU_apply, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero, zero_mul,
      abs_zero, Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
    simp

/-! ## Separation of an angular profile from a radial function, with an arbitrary angular
majorant -/

open Work.FTS.Nonlinear.RadialProd in
/-- **Separation of an angular profile and a radial function in `ℋ⁴`, with a general angular
majorant.**  For an angular profile `a` bounded by `B0` whose `D_θ`-iterates up to order `4` are
bounded by `B1·G` (with `G ≥ 0` a fixed angular function), and a radial function `r` of class
`ℋ⁴`,

  `|a·r|_{ℋ⁴} ≤ √(10000·B0² + 4·B1²·M1)·|r|_{ℋ⁴}`,

where `M1 ≥ ∫_θ G(θ)²·sin(2θ)^{-γ}dθ`.  This is `Xn_ang_rad_le` with `sin(2θ)^κ` replaced by
`G`; it is lossless in the factor `r` (the `θ`-integration is separated). -/
theorem Xn_ang_rad_le_gen (α : ℝ) (hα : 0 < α) (a : ℝ → ℝ) (r : ℝ → ℝ) (G : ℝ → ℝ)
    {B0 B1 M1 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hM1 : 0 ≤ M1)
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ| ≤ B1 * G θ)
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * smG α θ) Work.Spaces.Iθ)
    (hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * smG α θ ≤ M1)
    (hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z)) :
    Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
      ≤ Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
        * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by
  have hLam : (0 : ℝ) ≤ B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1 := by positivity
  -- ### Step 1: the pointwise (in `θ`) bound on the `ℋ⁴`-integrand
  have hpt : ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
        ≤ Rint r z * (B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) := by
    intro z θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    obtain ⟨hain, hain'⟩ := abs_le.mp (ha0 θ hθI)
    -- the pure slots
    have hpure : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = (a θ) ^ 2 * smE θ * Rint r z := by
      have hterm : ∀ i : ℕ, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * smE θ
            * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        intro i
        rw [dzIter_ang_rad,
          show (a θ * Work.Elliptic.DzdIter i r z
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              = ((a θ * Work.Elliptic.DzdIter i r z)
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            from by ring,
          light_sq _ z θ hsin]
        ring
      calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          = ∑ i ∈ Finset.range 5, (a θ) ^ 2 * smE θ
              * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = (a θ) ^ 2 * smE θ * Rint r z := by
            rw [← Finset.mul_sum, Rint]
    -- the mixed slots
    have hmix : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
      have hterm2 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ (if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        intro i hi j hj
        by_cases h1 : 1 ≤ i
        · by_cases h2 : i + j ≤ 4
          · rw [if_pos ⟨h1, h2⟩, if_pos h1]
            rw [mixed_ang_rad,
              show (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ
                    * Work.Elliptic.DzdIter j r z * Work.Spaces.Wt α z θ) ^ 2
                  = ((Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ
                      * Work.Elliptic.DzdIter j r z) * Work.Spaces.Wt α z θ) ^ 2 from by ring,
              heavy_sq α _ z θ hsin]
            exact le_of_eq (by ring)
          · rw [if_neg (fun h => h2 h.2), if_pos h1]
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (smG_nonneg hθI))
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        · rw [if_neg (fun h => h1 h.1), if_neg h1]
          simp
      calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0)
          ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i then
                  (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
                * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
        _ = Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
            rw [← Finset.sum_mul_sum, Rint]
            ring
    -- the comparison of the two profiles
    have hMsum : (∑ i ∈ Finset.range 5, if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
        ≤ ∑ i ∈ Finset.range 5, if 1 ≤ i then
            B1 ^ 2 * (G θ ^ 2 * smG α θ) else 0 := by
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1, if_pos h1]
        have hi4 : i ≤ 4 := by
          have := Finset.mem_range.mp hi
          omega
        have hb := ha1 i h1 hi4 θ hθI
        have h3 : (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 ≤ B1 ^ 2 * G θ ^ 2 := by
          have h4 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          rw [sq_abs, mul_pow] at h4
          exact h4
        calc (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ
            ≤ (B1 ^ 2 * G θ ^ 2) * smG α θ :=
              mul_le_mul_of_nonneg_right h3 (smG_nonneg hθI)
          _ = B1 ^ 2 * (G θ ^ 2 * smG α θ) := by ring
      · rw [if_neg h1, if_neg h1]
    have hMs : (∑ i ∈ Finset.range 5, if 1 ≤ i then
          B1 ^ 2 * (G θ ^ 2 * smG α θ) else 0)
        = 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ) := by
      rw [← Finset.sum_filter]
      rw [show (Finset.range 5).filter (fun i => 1 ≤ i) = Finset.Icc 1 4 from by decide,
        Finset.sum_const, Nat.card_Icc]
      norm_num
      ring
    have hM : (a θ) ^ 2 * smE θ + (∑ i ∈ Finset.range 5, if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
        ≤ B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ) := by
      refine add_le_add ?_ ?_
      · have h2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
          have h3 := pow_le_pow_left₀ (abs_nonneg (a θ)) (abs_le.mpr ⟨hain, hain'⟩) 2
          rwa [sq_abs] at h3
        exact mul_le_mul_of_nonneg_right h2 (smE_nonneg hθI)
      · exact hMsum.trans (le_of_eq hMs)
    calc Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
        = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
                  * Work.Spaces.Wt α z θ) ^ 2
              else 0) := by
            rw [Work.Spaces.HkIntegrand]
      _ ≤ (a θ) ^ 2 * smE θ * Rint r z
            + Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) :=
          add_le_add (le_of_eq hpure) hmix
      _ = Rint r z * ((a θ) ^ 2 * smE θ
            + (∑ i ∈ Finset.range 5, if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)) := by
          ring
      _ ≤ Rint r z * (B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) :=
          mul_le_mul_of_nonneg_left hM (Rint_nonneg r z)
  -- ### Step 2: the angular integrals
  have hexp1 : -1 < -(Work.Spaces.eta) := by
    have := Work.Spaces.eta_lt_one; linarith
  have hle0 : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have hIf : MeasureTheory.IntegrableOn (fun θ : ℝ => B0 ^ 2 * smE θ) Work.Spaces.Iθ := by
    change MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ
    exact (Work.Spaces.sin_two_rpow _ hexp1 hle0).1.const_mul _
  have hIg : MeasureTheory.IntegrableOn (fun θ : ℝ => 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ))
      Work.Spaces.Iθ := hI1.const_mul _
  have hIntA : MeasureTheory.IntegrableOn (fun θ : ℝ => B0 ^ 2 * smE θ
      + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) Work.Spaces.Iθ := hIf.add hIg
  have hA : (∫ θ in Work.Spaces.Iθ, smE θ) ≤ 10000 := by
    change (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hexp1 hle0).2
    have h1 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [h1] at h
    norm_num at h
    exact h
  have hboundA : (∫ θ in Work.Spaces.Iθ, B0 ^ 2 * smE θ
        + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) ≤ B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1 := by
    rw [MeasureTheory.integral_add hIf hIg, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    have h1 := mul_le_mul_of_nonneg_left hA (sq_nonneg B0)
    have h2 := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 4 * B1 ^ 2)
    linarith
  -- ### Step 3: integrate in `θ` and then in `z`
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ)
        ≤ Rint r z * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) := by
    intro z
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Rint r z * (B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
            (hIntA.const_mul _) ?_
          filter_upwards [Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ
          exact hpt z θ hθ
      _ = Rint r z * (∫ θ in Work.Spaces.Iθ, B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Rint r z * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) :=
          mul_le_mul_of_nonneg_left hboundA (Rint_nonneg r z)
  have houter : Work.Spaces.HkSq α 4 (fun z θ => a θ * r z)
      ≤ (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) * ∫ z in Work.Spaces.Iz, Rint r z := by
    rw [Work.Spaces.HkSq]
    have hEq : (∫ z in Work.Spaces.Iz, Rint r z
          * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1))
        = (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * ∫ z in Work.Spaces.Iz, Rint r z := by
      rw [MeasureTheory.integral_mul_const]; ring
    rw [← hEq]
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((integrable_Rint α r hrmem).mul_const _)
      (Filter.Eventually.of_forall hinner)
  have hfin : Work.Spaces.HkSq α 4 (fun z θ => a θ * r z)
      ≤ (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
        * Work.Spaces.HkSq α 4 (fun z θ => r z) := by
    refine houter.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hLam
    rw [show (∫ z in Work.Spaces.Iz, Rint r z) = Rr r from rfl]
    exact Rr_le_HkSq α r
  calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => a θ * r z)) := rfl
    _ ≤ Real.sqrt ((B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Work.Spaces.HkSq α 4 (fun z θ => r z)) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => r z)) := Real.sqrt_mul hLam _
    _ = Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := rfl

theorem row23 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α)
        ≤ K * α ^ 3 := by
  obtain ⟨Cg, hCgpos, hCg⟩ := dthU_pow_Gam_sharp
  obtain ⟨Cr, hCrpos, hCr⟩ := hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := gamWeightInt
  have hQnn : (0 : ℝ) ≤ 27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M := by positivity
  refine ⟨Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := Real.sqrt_nonneg _
    nlinarith [hCrpos]
  · intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
    -- the weight `c(α)` of the fundamental solution is bounded below by `1/10`
    have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    -- the angular profile and the radial profile
    set a : ℝ → ℝ := fun θ => (-(2 * α ^ 2 / Work.Spaces.c α))
      * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with ha
    set r : ℝ → ℝ := fun z => (Work.Spaces.hKer z) ^ 2 with hr
    set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
    -- ### 1. the factorisation `N₄^{**} = a(θ)·r(z)`
    have hid : Work.FTS.Nonlin.N4ss α = fun z θ => a θ * r z := by
      funext z θ
      rw [Work.FTS.Nonlin.N4ss]
      have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
          = (α * Work.FM.Fstar z / Work.Spaces.c α)
            * deriv (fun t => Work.Spaces.Gam α t) θ := by
        rw [Work.Spaces.pth]
        rw [show (fun θ' => Work.Construction.Fstar α z θ')
            = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α)
                * Work.Spaces.Gam α θ' from by
          funext θ'; rw [Work.Construction.Fstar]; ring]
        rw [Work.Spaces.deriv_const_mul']
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, hpth]
      simp only [ha, hr, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar,
        Work.Construction.s2]
      ring_nf
    -- ### 2. the bounds on the two profiles
    have hc2 : 2 * α ^ 2 / Work.Spaces.c α ≤ 20 * α ^ 2 := by
      rw [div_le_iff₀ hcpos]
      nlinarith [hcge, sq_nonneg α, hα]
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
      intro θ hθ
      have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have h2 : 0 ≤ Real.sin (2 * θ) :=
        Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      rw [hG]
      positivity
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ 27 * α ^ 3 := by
      intro θ hθ
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hdth := dthIter_one_Gam_le hα hα1 θ hθ
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr]; exact hdth
      have hc2' : (0 : ℝ) ≤ 2 * α ^ 2 / Work.Spaces.c α :=
        div_nonneg (by positivity) hcpos.le
      have habs : |a θ| = (2 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
        simp only [ha]
        rw [abs_mul, abs_neg, abs_of_nonneg hc2']
      rw [habs]
      calc (2 * α ^ 2 / Work.Spaces.c α)
              * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (2 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_left hb hc2'
        _ ≤ (20 * α ^ 2) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ ≤ 27 * α ^ 3 := by
          have hα3 : (0 : ℝ) ≤ α ^ 3 := by positivity
          have h := mul_le_mul_of_nonneg_left hΓ1
            (by positivity : (0 : ℝ) ≤ (80 / 3) * α ^ 3)
          nlinarith [h, hα3]
    have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ| ≤ (20 * Cg * α ^ 3) * G θ := by
      intro i hi hi4 θ hθ
      have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
          = (-(2 * α ^ 2 / Work.Spaces.c α))
            * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq i a 0 θ]
        simp only [ha]
        rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
      have hchild := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
      have hc2' : (0 : ℝ) ≤ 2 * α ^ 2 / Work.Spaces.c α :=
        div_nonneg (by positivity) hcpos.le
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      have hGunfold : G θ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by rw [hG]
      rw [hrepr, abs_mul, abs_neg, abs_of_nonneg hc2', hGunfold]
      have h1 : (2 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (2 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
        mul_le_mul_of_nonneg_left hchild hc2'
      have h2 : (2 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          ≤ (20 * Cg * α ^ 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
        rw [show (2 * α ^ 2 / Work.Spaces.c α)
              * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
            = ((2 * α ^ 2 / Work.Spaces.c α) * Cg * α)
              * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) from by ring]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 * α ^ 2 / Work.Spaces.c α) * Cg * α
            = (2 * α ^ 2 / Work.Spaces.c α) * (Cg * α) := by ring
          _ ≤ (20 * α ^ 2) * (Cg * α) :=
              mul_le_mul_of_nonneg_right hc2 (by positivity)
          _ = 20 * Cg * α ^ 3 := by ring
      exact h1.trans h2
    -- ### 3. the `θ`-mass of the angular profile
    obtain ⟨hI1raw, hm1raw⟩ := hM α hα hα1
    have hGae : (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      funext θ; rw [hG]; ring
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        Work.Spaces.Iθ := by rw [hGae]; exact hI1raw
    have hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ M := by rw [hGae]; exact hm1raw
    -- ### 4. the radial function
    obtain ⟨hrmemR, hXnR⟩ := hCr α hα hα1
    have hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z) := by rw [hr]; exact hrmemR
    have hXnR' : Work.FTS.Nonlin.Xn α (fun z θ => r z) ≤ Cr := by rw [hr]; exact hXnR
    -- ### 5. the separated estimate
    have hmain := Xn_ang_rad_le_gen α hα a r G (B0 := 27 * α ^ 3)
      (B1 := 20 * Cg * α ^ 3) (M1 := M) (by positivity) (by positivity) (le_of_lt hMpos)
      hGnn ha0 ha1 hI1 hm1 hrmem
    -- ### 6. the arithmetic
    have hsqrt : Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M)
        = α ^ 3 * Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := by
      rw [show (27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M
          = (α ^ 3) ^ 2 * (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [hid]
    calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
        ≤ Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M)
            * Work.FTS.Nonlin.Xn α (fun z θ => r z) := hmain
      _ ≤ Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M) * Cr :=
          mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _)
      _ = α ^ 3 * (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr) := by
          rw [hsqrt]; ring
      _ ≤ (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1) * α ^ 3 := by
          nlinarith [sq_nonneg α, le_of_lt hα]

end Work.FTS.Nonlinear.Pieces.RNP
