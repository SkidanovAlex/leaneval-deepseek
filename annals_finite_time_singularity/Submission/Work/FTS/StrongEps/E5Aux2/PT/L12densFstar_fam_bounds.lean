import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12densFstar_deriv
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXVP.thLip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PT

set_option maxHeartbeats 800000

/-! ## The angular weight `K` against the majorant `cos θ` -/

/-- **From a pointwise bound on the open interval to a `K`-bound against `cos θ`.**
If `|g| ≤ B` on `(0,π/2)` and `B ≥ 0`, then `K θ * |g θ| ≤ 3B cos θ` on all of
`Iθ = [0,π/2]`: in the interior this is `K θ ≤ 3 cos θ` (because `sin θ ≤ 1` and
`cos²θ ≤ cos θ` there), and at the two endpoints both sides vanish. -/
lemma K_mul_abs_le_cos_of_Ioo {g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), |g θ| ≤ B) :
    ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |g θ| ≤ 3 * B * Real.cos θ := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · have hcos0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
      have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have hcos2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith
      have hKle : Work.Spaces.K θ ≤ 3 * Real.cos θ := by
        rw [Work.Spaces.K]
        have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ := by
          have := mul_le_mul hsin1 hcos2 (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
          linarith
        nlinarith
      have hg := h θ ⟨h0, h2⟩
      calc Work.Spaces.K θ * |g θ| ≤ (3 * Real.cos θ) * B :=
            mul_le_mul hKle hg (abs_nonneg _) (by positivity)
        _ = 3 * B * Real.cos θ := by ring
    · subst h2
      rw [Work.Spaces.K, Real.sin_pi_div_two, Real.cos_pi_div_two]
      simp
  · subst h0
    rw [Work.Spaces.K, Real.sin_zero, Real.cos_zero]
    simp
    linarith

/-- **The weighted angular integral against `cos θ`.**  If `K θ * |g θ| ≤ A cos θ` on `Iθ`,
then `|∫_θ K θ g θ| ≤ A` (using `∫_θ cos θ = 1` on `Iθ`). -/
lemma abs_integral_Iθ_K_mul_le {g : ℝ → ℝ} {A : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |g θ| ≤ A * Real.cos θ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g θ| ≤ A := by
  have h1 : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * g θ| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h2 : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * g θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, A * Real.cos θ := by
    refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ _ => abs_nonneg _) ?_ ?_
    · intro θ hθ
      rw [abs_mul, abs_of_nonneg (Work.FTS.StrongEps.E5Aux2.K_nonneg_of_mem_Iθ hθ)]
      exact h θ hθ
    · rw [Work.Spaces.Iθ]
      exact (continuous_const.mul Real.continuous_cos).integrableOn_Icc
  have h3 : (∫ θ in Work.Spaces.Iθ, A * Real.cos θ) = A := by
    rw [MeasureTheory.integral_const_mul, Work.FTS.StrongEps.E5Aux2.integral_cos_Iθ, mul_one]
  linarith

/-- **The density bound.**  If `|Y s θ| ≤ B` on `(0,π/2)` and `B ≥ 0`, then
`|L12dens Y s| ≤ 3B/s` for `s > 0`. -/
lemma abs_L12dens_le_of_Ioo {Y : ℝ → ℝ → ℝ} {B s : ℝ} (hs : 0 < s)
    (hB : 0 ≤ B) (h : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), |Y s θ| ≤ B) :
    |Work.Construction.L12dens Y s| ≤ 3 * B / s :=
  Work.FTS.StrongEps.E5Aux2.AbsL12densLe hs (by linarith)
    (K_mul_abs_le_cos_of_Ioo hB h)

/-! ## Pointwise bounds for the two summands -/

/-- `|∂_zF_*(z,θ)| ≤ 20α/z` for `0 < α ≤ 1`, `z > 0`, `θ ∈ Iθ`: the sharp bound
`|D_zF_*| ≤ 20α/(1+z)` of `FstarSlotPt.DzFstar_abs_le` divided by `z`. -/
lemma pz_Fstar_abs_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz (Work.Construction.Fstar α) z θ| ≤ 20 * α / z := by
  have hDz : |z * Work.Spaces.pz (Work.Construction.Fstar α) z θ| ≤ 20 * α * (1 / (1 + z)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.DzFstar_abs_le hα hα1 hz.le hθ
  have hle : 20 * α * (1 / (1 + z)) ≤ 20 * α := by
    refine mul_le_of_le_one_right (by linarith) ?_
    rw [div_le_one (by linarith : (0:ℝ) < 1 + z)]
    linarith
  have h1 : |z * Work.Spaces.pz (Work.Construction.Fstar α) z θ| ≤ 20 * α := le_trans hDz hle
  rw [abs_mul, abs_of_pos hz] at h1
  rw [le_div_iff₀ hz]
  linarith

/-- `|∂_z u(x,θ)| ≤ C₂/x` on the open quadrant, from the bound `|D_z u| ≤ C₂`. -/
lemma pz_le_div_of_hbd1 {u : ℝ → ℝ → ℝ} {C₂ x θ : ℝ} (hx : 0 < x)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (π/2))
    (hbd1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz u z θ| ≤ C₂) :
    |Work.Spaces.pz u x θ| ≤ C₂ / x := by
  have h1 : |x * Work.Spaces.pz u x θ| ≤ C₂ := hbd1 x θ ⟨hx, hθ⟩
  rw [abs_mul, abs_of_pos hx] at h1
  rw [le_div_iff₀ hx]
  linarith

/-! ## The main statement -/

theorem L12densFstar_fam_bounds {α C₁ C₂ : ℝ} (hα : α ∈ Set.Ioc 0 1) {w : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (w n))
    (hbd0 : ∀ (n : ℕ) (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd → |w n z θ| ≤ C₁)
    (hbd1 : ∀ (n : ℕ) (z θ : ℝ), (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz (w n) z θ| ≤ C₂) :
    (∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ) (x : ℝ), 0 < x →
      |Work.Construction.L12dens (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x|
        ≤ M * (1 + 1 / x)) ∧
    (∃ L : ℝ, 0 < L ∧ ∀ (n : ℕ) (x : ℝ), 0 < x →
      |deriv (fun x => Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x) x| ≤ L * (1 + 1 / x ^ 2)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the two constants are nonnegative (evaluate the hypotheses at the point `(1,1) ∈ Qd`)
  have hC1 : 0 ≤ C₁ := by
    have h := hbd0 0 1 1 ⟨by norm_num, by norm_num, by linarith [Real.pi_gt_three]⟩
    have h2 := abs_nonneg (w 0 1 1)
    linarith
  have hC2 : 0 ≤ C₂ := by
    have h := hbd1 0 1 1 ⟨by norm_num, by norm_num, by linarith [Real.pi_gt_three]⟩
    have h2 := abs_nonneg (Work.Spaces.Dz (w 0) 1 1)
    linarith
  have hB0 : 0 ≤ 20 * α + C₁ := by linarith
  -- pointwise bounds on the open quadrant, uniform in `n`
  have hptF : ∀ (n : ℕ) (y θ : ℝ), 0 < y → θ ∈ Set.Ioo (0:ℝ) (π/2) →
      |(fun z θ => Work.Construction.Fstar α z θ + w n z θ) y θ| ≤ 20 * α + C₁ := by
    intro n y θ hy hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have h1 := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.Fstar_abs_le (α := α) (z := y)
      (θ := θ) hα0 hα1 hy.le hθI
    have h2 := hbd0 n y θ ⟨hy, hθ⟩
    have h3 : 20 * α * (1 / (1 + y)) ≤ 20 * α := by
      refine mul_le_of_le_one_right (by linarith) ?_
      rw [div_le_one (by linarith : (0:ℝ) < 1 + y)]
      linarith
    calc |Work.Construction.Fstar α y θ + w n y θ|
        ≤ |Work.Construction.Fstar α y θ| + |w n y θ| := abs_add_le _ _
      _ ≤ 20 * α + C₁ := by linarith
  have hptP : ∀ (n : ℕ) (y θ : ℝ), 0 < y → θ ∈ Set.Ioo (0:ℝ) (π/2) →
      |Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y θ|
        ≤ 20 * α / y + C₂ / y := by
    intro n y θ hy hθ
    have hadd := Work.FTS.NonlinRows.Rl1.openSlice_pz_add
      (f := Work.Construction.Fstar α) (h := w n)
      (Work.FTS_RegExport.RXR7.Support.smoothOpen_Fstar α) (hsm n) hy hθ
    rw [hadd]
    have h1 := pz_Fstar_abs_le hα0 hα1 hy ⟨hθ.1.le, hθ.2.le⟩
    have h2 := pz_le_div_of_hbd1 hy hθ (hbd1 n)
    exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
  constructor
  · -- ## the density bound
    refine ⟨3 * (20 * α + C₁) + 1, by linarith, ?_⟩
    intro n x hx
    have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
        |(fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ| ≤ 20 * α + C₁ :=
      fun θ hθ => hptF n x θ hx hθ
    have hd := abs_L12dens_le_of_Ioo (Y := fun z θ => Work.Construction.Fstar α z θ + w n z θ)
      hx hB0 hpt
    have h1x : 0 < 1 / x := one_div_pos.mpr hx
    have hM : 0 < 3 * (20 * α + C₁) + 1 := by linarith
    calc |Work.Construction.L12dens (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x|
        ≤ 3 * (20 * α + C₁) / x := hd
      _ = 3 * (20 * α + C₁) * (1 / x) := by ring
      _ ≤ (3 * (20 * α + C₁) + 1) * (1 / x) :=
          mul_le_mul_of_nonneg_right (by linarith) h1x.le
      _ ≤ (3 * (20 * α + C₁) + 1) * (1 + 1 / x) :=
          mul_le_mul_of_nonneg_left (by linarith) hM.le
  · -- ## the derivative bound
    refine ⟨3 * (20 * α + C₂) + 3 * (20 * α + C₁) + 1, by linarith, ?_⟩
    intro n x hx
    have hC : 0 ≤ 20 * α + C₁ + 40 * α / x + 2 * C₂ / x := by
      have h1 : 0 ≤ 40 * α / x := div_nonneg (by linarith) hx.le
      have h2 : 0 ≤ 2 * C₂ / x := div_nonneg (by linarith) hx.le
      linarith
    -- smoothness of the datum on the open quadrant
    have hcd : ContDiffOn ℝ 2 (Function.uncurry
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ)) Work.FTS.EllipticEst.Q0 := by
      have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar α))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS_RegExport.RXR7.Support.contDiffOn_uncurry_Fstar_Q0 α 2
      have h2 : ContDiffOn ℝ 2 (Function.uncurry (w n)) Work.FTS.EllipticEst.Q0 :=
        (Work.FTS.EllipticEst.smoothOpen_iff_forall (w n)).mp (hsm n) 2
      refine (h1.add h2).congr (fun p hp => ?_)
      rcases p with ⟨z, θ⟩
      rfl
    -- the two strip bounds required by the differentiation rule
    have hstrip0 : ∀ y ∈ Set.Ioo (x / 2) (2 * x), ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
        |(fun z θ => Work.Construction.Fstar α z θ + w n z θ) y θ|
          ≤ 20 * α + C₁ + 40 * α / x + 2 * C₂ / x := by
      intro y hy θ hθ
      have hy0 : 0 < y := by linarith [hy.1, hx]
      have h1 := hptF n y θ hy0 hθ
      have h2 : 0 ≤ 40 * α / x + 2 * C₂ / x := by
        have ha : 0 ≤ 40 * α / x := div_nonneg (by linarith) hx.le
        have hb : 0 ≤ 2 * C₂ / x := div_nonneg (by linarith) hx.le
        linarith
      linarith
    have hstrip1 : ∀ y ∈ Set.Ioo (x / 2) (2 * x), ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
        |Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y θ|
          ≤ 20 * α + C₁ + 40 * α / x + 2 * C₂ / x := by
      intro y hy θ hθ
      have hy0 : 0 < y := by linarith [hy.1, hx]
      have hle : 1 / y ≤ 2 / x := by
        have hx2 : 0 < x / 2 := by linarith
        have h := one_div_le_one_div_of_le hx2 (by linarith [hy.1] : x / 2 ≤ y)
        rwa [one_div_div] at h
      have h1 := hptP n y θ hy0 hθ
      have ha : 20 * α / y ≤ 40 * α / x := by
        calc 20 * α / y = 20 * α * (1 / y) := by ring
          _ ≤ 20 * α * (2 / x) := mul_le_mul_of_nonneg_left hle (by linarith)
          _ = 40 * α / x := by ring
      have hb : C₂ / y ≤ 2 * C₂ / x := by
        calc C₂ / y = C₂ * (1 / y) := by ring
          _ ≤ C₂ * (2 / x) := mul_le_mul_of_nonneg_left hle hC2
          _ = 2 * C₂ / x := by ring
      have h2 : 0 ≤ 20 * α + C₁ := hB0
      linarith
    -- differentiation under the angular integral
    have hd := Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
      (f := fun z θ => Work.Construction.Fstar α z θ + w n z θ) (z := x)
      (C := 20 * α + C₁ + 40 * α / x + 2 * C₂ / x) hcd hx hC hstrip1 hstrip0
    -- the density is `A(x)/x`
    have hfun : (fun y => Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y)
        = fun y => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
            (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y θ) / y := by
      funext y
      simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ,
        MeasureTheory.integral_div]
    have hq : HasDerivAt (fun y => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
            (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y θ) / y)
        (((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x
          - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * 1) / x ^ 2) x :=
      hd.div (hasDerivAt_id x) (ne_of_gt hx)
    have hderiv : deriv (fun y => Work.Construction.L12dens
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) y) x
        = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x
            - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)) / x ^ 2 := by
      rw [hfun, hq.deriv]
      ring
    -- the two integrals are bounded
    have hIx : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ|
        ≤ 3 * ((20 * α + C₂) / x) := by
      refine abs_integral_Iθ_K_mul_le ?_
      refine K_mul_abs_le_cos_of_Ioo (g := fun θ => Work.Spaces.pz
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)
        (B := (20 * α + C₂) / x) (div_nonneg (by linarith) hx.le) ?_
      intro θ hθ
      calc |Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ|
          ≤ 20 * α / x + C₂ / x := hptP n x θ hx hθ
        _ = (20 * α + C₂) / x := by ring
    have hAx : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ| ≤ 3 * (20 * α + C₁) := by
      refine abs_integral_Iθ_K_mul_le ?_
      refine K_mul_abs_le_cos_of_Ioo (g := fun θ =>
        (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)
        (B := 20 * α + C₁) hB0 ?_
      intro θ hθ
      exact hptF n x θ hx hθ
    have hnum1 : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
          (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ| * x
        ≤ 3 * (20 * α + C₂) := by
      calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
            (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ| * x
          ≤ (3 * ((20 * α + C₂) / x)) * x := mul_le_mul_of_nonneg_right hIx hx.le
        _ = 3 * ((20 * α + C₂) / x * x) := by ring
        _ = 3 * (20 * α + C₂) := by rw [div_mul_cancel₀ _ (ne_of_gt hx)]
    have hnum : |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x
            - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)|
        ≤ 3 * (20 * α + C₂) + 3 * (20 * α + C₁) := by
      have h1 : |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x
            - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)|
          ≤ |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)| * x
            + |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)| := by
        have h := abs_sub_le ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x) 0
          ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ))
        simp only [sub_zero, zero_sub, abs_neg] at h
        rw [abs_mul, abs_of_pos hx] at h
        exact h
      linarith
    have hfin : |((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x
            - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)) / x ^ 2|
        ≤ (3 * (20 * α + C₂) + 3 * (20 * α + C₁)) / x ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos hx 2)]
      exact div_le_div_of_nonneg_right hnum (by positivity)
    rw [hderiv]
    calc |((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ) * x
            - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ *
              (fun z θ => Work.Construction.Fstar α z θ + w n z θ) x θ)) / x ^ 2|
        ≤ (3 * (20 * α + C₂) + 3 * (20 * α + C₁)) / x ^ 2 := hfin
      _ = (3 * (20 * α + C₂) + 3 * (20 * α + C₁)) * (1 / x ^ 2) := by ring
      _ ≤ (3 * (20 * α + C₂) + 3 * (20 * α + C₁) + 1) * (1 / x ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (3 * (20 * α + C₂) + 3 * (20 * α + C₁) + 1) * (1 + 1 / x ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)

end Work.FTS.StrongEps.E5Aux2.PT
