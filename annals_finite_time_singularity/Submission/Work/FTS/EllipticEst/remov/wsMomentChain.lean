import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.remov.wsMomentDefs
import Submission.Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular-moment chain `F_*(D_z^j Ψ) ≡ 0` (`j ≤ 2`) for the weak elliptic class

For a datum `h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` with `k ≥ 1`, the angular moments
`F_*(D_z^j Ψ)(z) = ∫_θ D_z^j Ψ(z,θ) sinθcos²θ dθ` vanish for `j ≤ 2` and every `z > 0`.

The route is the chain rule for the moment along `D_z` (the identity
`F_*(D_z^j Ψ)(z) - F_*(D_z^j Ψ)(s) = ∫_s^z F_*(D_z^{j+1} Ψ)(r)/r dr`, obtained from
`Work.FTS.EllipticEst.moment_relation`, i.e. Fubini on a radial box), together with the
*continuity* of the moments `F_*(D_z Ψ)` and `F_*(D_z² Ψ)`:

* from `j = 0` and `F_*(Ψ) ≡ 0` the primitive of `r ↦ F_*(D_zΨ)(r)/r` vanishes identically on
  `(0,∞)`, so `F_*(D_zΨ) ≡ 0` once it is known to be continuous;
* continuity of `F_*(D_zΨ)` comes from the `j = 1` chain, which exhibits it as an indefinite
  integral of the locally integrable function `r ↦ F_*(D_z²Ψ)(r)/r`;
* the same two steps at `j = 1, 2` give `F_*(D_z²Ψ) ≡ 0`.

The only analytic input is the local integrability and finiteness of the moments
`F_*(D_z^j Ψ)`, which follows from the `θ`-slice energy bounds: the `θ`-energy of every radial
iterate `D_z^j Ψ` (`1 ≤ j ≤ 3`) is dominated on a compact radial interval by the reference
energy `Eref Ψ` (the `θ`-energies of `∂_θ²Ψ`, `D_z∂_θ²Ψ`, `z²∂_z²Ψ` and `D_z(z²∂_z²Ψ)`), and
`Eref Ψ` is locally integrable.  These bounds use the slice Poincaré inequality
`Work.FTS.EllipticEst.remov.ws_slice_pointwise_le` of `remov.wsAux` to pass from the
`ℋ^k`-honesty of `∂_θ²Ψ` (the only angular second-derivative control available) to the
`θ`-energy of `D_zΨ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Measurability helpers -/

/-- The uncurried `sEta`-weighted square of a function continuous on the open quadrant is
a.e. strongly measurable with respect to the product measure on a box. -/
theorem aesm_uncurry_sq_mul_sEta {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 * SS p.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Iθ)) :=
  Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
    (hg.pow 2 |>.mul ws_contOn_sEta) ha

/-- The `θ`-energy of a function continuous on the open quadrant is a.e. strongly measurable
in the radial variable, on any interval `(a,b]` with `a ≥ 0`. -/
theorem aesm_thetaE_Ioc {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun s => thetaE g s) (volume.restrict (Set.Ioc a b)) := by
  have h := (aesm_uncurry_sq_mul_sEta hg ha).integral_prod_right'
    (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
  simpa only [thetaE] using h

/-- `aesm_thetaE_Ioc` on a closed interval; `(a,b]` and `[a,b]` differ by the null set `{a}`. -/
theorem aesm_thetaE_Icc {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun s => thetaE g s) (volume.restrict (Set.Icc a b)) := by
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  exact aesm_thetaE_Ioc hg ha

/-- The angular moment `F_*(g)` of a function continuous on the open quadrant is a.e. strongly
measurable in the radial variable, on any interval `(a,b]` with `a ≥ 0`. -/
theorem aesm_fstar_Ioc {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun z => Work.Elliptic.Fstar g z) (volume.restrict (Set.Ioc a b)) := by
  have hcontσ : Continuous (fun p : ℝ × ℝ => sg p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * sg p.2)
      Work.FTS.EllipticEst.Q0 :=
    hg.mul hcontσ.continuousOn
  have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha).integral_prod_right'
    (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
  simpa only [Work.Elliptic.Fstar] using h

/-- `aesm_fstar_Ioc` on a closed interval. -/
theorem aesm_fstar_Icc {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun z => Work.Elliptic.Fstar g z) (volume.restrict (Set.Icc a b)) := by
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  exact aesm_fstar_Ioc hg ha

/-! ## Smoothness of `z²∂_z²Ψ` -/

/-- `z² ∂_z²Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  have hz2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst (𝕜 := ℝ) (n := Work.Stability.smoothOrder)
      (s := Work.FTS.EllipticEst.Q0)).pow 2
  refine (hz2.mul hg).congr ?_
  intro p hp
  rfl

/-! ## The `θ`-second-derivative of `∂_zΨ` is a radial iterate of `∂_θ²Ψ` -/

/-- `pthIter 2 (pz Ψ) s t = D_z∂_θ²Ψ (s,t) / s` on the open quadrant.  The one-variable content
is that the radial slice of `∂_zΨ` is the radial slice of `D_zΨ = z∂_zΨ` divided by the
constant `s`, and that `D_z` commutes with `∂_θ²` (`ws_pthIter_two_DzIter`). -/
theorem pthIter_two_pz_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {s t : ℝ} (hs : 0 < s) (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t
      = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t / s := by
  have hfun : Work.Spaces.pz Ψ s = fun t => Work.Spaces.DzIter 1 Ψ s t / s := by
    funext t
    show deriv (fun z' => Ψ z' t) s = Work.Spaces.DzIter 1 Ψ s t / s
    show deriv (fun z' => Ψ z' t) s = (s * deriv (fun z' => Ψ z' t) s) / s
    rw [mul_div_cancel_left₀ _ (ne_of_gt hs)]
  have hstep : Work.Spaces.pth (Work.Spaces.pz Ψ) s
      = fun t => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s t / s := by
    funext t
    show deriv (fun u => Work.Spaces.pz Ψ s u) t
      = deriv (fun u => Work.Spaces.DzIter 1 Ψ s u) t / s
    rw [hfun]
    have hsplit : (fun u : ℝ => Work.Spaces.DzIter 1 Ψ s u / s)
        = fun u => s⁻¹ * Work.Spaces.DzIter 1 Ψ s u := by
      funext u; rw [div_eq_mul_inv, mul_comm]
    rw [hsplit, deriv_const_mul_field]
    ring
  have hstep2 : Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s
      = fun t => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) s t / s := by
    show deriv (fun u => Work.Spaces.pth (Work.Spaces.pz Ψ) s u)
      = fun t => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) s t / s
    rw [hstep]
    funext t
    show deriv (fun u => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u / s) t
      = deriv (fun u => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u) t / s
    have hsplit : (fun u : ℝ => Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u / s)
        = fun u => s⁻¹ * Work.Spaces.pth (Work.Spaces.DzIter 1 Ψ) s u := by
      funext u; rw [div_eq_mul_inv, mul_comm]
    rw [hsplit, deriv_const_mul_field]
    ring
  rw [hstep2]
  show Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) s t / s
      = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t / s
  rw [ws_pthIter_two_DzIter hS 1 hs ht]

/-- **The `θ`-energy of the second `θ`-derivative of `∂_zΨ`.**  It is `s⁻²` times the
`θ`-energy of `D_z∂_θ²Ψ`, hence finite and integrable on every slice, by `ws_slot_slice`. -/
theorem integrableOn_pthIter_two_pz {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn
        (fun t => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t) Iθ ∧
      (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)
        = (s ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hSΨ.pth.pth
  have hbase := ws_slot_slice hSB h.memB 1 hk hs
  have hae : (fun t => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)
      =ᵐ[volume.restrict Iθ]
        (fun t => (s ^ 2)⁻¹
          * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t) ^ 2 * SS t)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun t ht => ?_)
    show (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t
      = (s ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s t) ^ 2 * SS t)
    rw [pthIter_two_pz_eq hSΨ hs ht, div_pow, div_eq_mul_inv]
    ring
  refine ⟨(hbase.const_mul _).congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
  rfl

/-- The `θ`-energy scales by the square of a constant: `∫ (c·X s)² sEta = c² ∫ (X s)² sEta`. -/
theorem thetaE_const_mul {X : ℝ → ℝ → ℝ} {c s : ℝ}
    (hX : MeasureTheory.IntegrableOn (fun θ => (X s θ) ^ 2 * SS θ) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (c * X s θ) ^ 2 * SS θ) Iθ ∧
      thetaE (fun u θ => c * X u θ) s = c ^ 2 * thetaE X s := by
  refine ⟨?_, ?_⟩
  · have hbase := hX.const_mul (c ^ 2)
    refine hbase.congr ?_
    refine Eventually.of_forall (fun θ => ?_)
    show c ^ 2 * (X s θ ^ 2 * SS θ) = (c * X s θ) ^ 2 * SS θ
    ring
  · show (∫ θ in Iθ, (c * X s θ) ^ 2 * SS θ) = c ^ 2 * (∫ θ in Iθ, (X s θ) ^ 2 * SS θ)
    have heq : (fun θ => (c * X s θ) ^ 2 * SS θ)
        = fun θ => c ^ 2 * ((X s θ) ^ 2 * SS θ) := by
      funext θ; ring
    rw [heq, MeasureTheory.integral_const_mul]

/-! ## The Poincaré bound for the slice of `∂_zΨ` -/

/-- **The slice Poincaré bound for `∂_zΨ`.**  On a compact radial interval `[a,b] ⊂ (0,∞)` the
`θ`-energy of `∂_zΨ` is dominated by a constant times `1 + thetaE (D_z∂_θ²Ψ)`; the analytic
input is the slice Poincaré inequality `ws_slice_pointwise_le` applied to the slice
`θ ↦ ∂_zΨ(s,θ)`, whose second `θ`-derivative is `D_z∂_θ²Ψ(s,·)/s`. -/
theorem thetaE_pz_le {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ s θ) ^ 2 * SS θ) Iθ ∧
      thetaE (Work.Spaces.pz Ψ) s ≤ K * (1 + Eref Ψ s) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hqI : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hQ : ∀ s ∈ Set.Icc a b, ((s, Real.pi / 4) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    fun s hs => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha hs.1, hqI.1, hqI.2⟩
  have hc1 : ContinuousOn (fun s : ℝ => Work.Spaces.pz Ψ s (Real.pi / 4)) (Set.Icc a b) :=
    (hSΨ.pz).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hQ
  have hc2 : ContinuousOn (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4))
      (Set.Icc a b) :=
    (hSΨ.pz).pth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hQ
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  set A : ℝ := max 1 (|C₁| ^ 2) with hAdef
  set B : ℝ := max 1 (|C₂| ^ 2) with hBdef
  set S : ℝ := ∫ θ in Iθ, SS θ with hSdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hS0 : 0 ≤ S := by rw [hSdef]; exact ws_sEta_integral_nonneg
  have hSle : S ≤ 10000 := by rw [hSdef]; exact ws_sEta_integral_le
  set M : ℝ := 2 * A + 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
    + 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  set Kp : ℝ := max 1 (M * 10000) with hKpdef
  have hKp0 : (0 : ℝ) < Kp := by rw [hKpdef]; positivity
  refine ⟨Kp * 10000, by positivity, ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  obtain ⟨hEint, hIval⟩ := integrableOn_pthIter_two_pz hk h hs0
  have hv : ContDiffOn ℝ 2 (fun θ => Work.Spaces.pz Ψ s θ) (Set.Ioo 0 (Real.pi / 2)) :=
    ws_contDiffOn_slice hSΨ.pz hs0
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ 2 * (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2
          + 4 * Real.pi ^ 2 * (1 + S)
            * (1 + (Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2
              + (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)) := by
    intro θ hθ
    have h := ws_slice_pointwise_le (v := fun θ => Work.Spaces.pz Ψ s θ) hv hEint θ hθ
    simpa only [← hSdef, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using h
  have hA' : (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ A := by
    have hb1 : |Work.Spaces.pz Ψ s (Real.pi / 4)| ≤ C₁ := by
      have hb := hC₁ s hs
      rwa [Real.norm_eq_abs] at hb
    have hb2 : |Work.Spaces.pz Ψ s (Real.pi / 4)| ≤ |C₁| := le_trans hb1 (le_abs_self C₁)
    rw [hAdef]
    calc (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2
        = |Work.Spaces.pz Ψ s (Real.pi / 4)| ^ 2 := by rw [sq_abs]
      _ ≤ |C₁| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
      _ ≤ max 1 (|C₁| ^ 2) := le_max_right _ _
  have hB' : (Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2 ≤ B := by
    have hb1 : |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ≤ C₂ := by
      have hb := hC₂ s hs
      rwa [Real.norm_eq_abs] at hb
    have hb2 : |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ≤ |C₂| :=
      le_trans hb1 (le_abs_self C₂)
    rw [hBdef]
    calc (Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2
        = |Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)| ^ 2 := by rw [sq_abs]
      _ ≤ |C₂| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
      _ ≤ max 1 (|C₂| ^ 2) := le_max_right _ _
  have hI : (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t)
      ≤ (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
    rw [hIval]
    have hsa : a ≤ s := hs.1
    have hs2a : a ^ 2 ≤ s ^ 2 := by nlinarith
    have h2 : (s ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < s ^ 2) (by positivity : (0 : ℝ) < a ^ 2)).mpr hs2a
    exact mul_le_mul_of_nonneg_right h2 (thetaE_nonneg _ _)
  have hmain : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
    intro θ hθ
    have hEb0 : 0 ≤ thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
      thetaE_nonneg _ _
    have hcoef : 0 ≤ 4 * Real.pi ^ 2 * (1 + S) := by positivity
    have hbr : 1 + ((Work.Spaces.pth (Work.Spaces.pz Ψ) s (Real.pi / 4)) ^ 2
          + (∫ t in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s t) ^ 2 * SS t))
        ≤ 1 + B + (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
      linarith [hB', hI]
    have hstep : (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ 2 * A + 4 * Real.pi ^ 2 * (1 + S)
            * (1 + B + (a ^ 2)⁻¹ * thetaE
                (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      have h2 := mul_le_mul_of_nonneg_left hbr hcoef
      have h3 : 2 * (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ 2 * A := by linarith [hA']
      linarith [hpt θ hθ, h2, h3]
    have hK2 : 2 * A + 4 * Real.pi ^ 2 * (1 + S)
          * (1 + B + (a ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
        ≤ M * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      rw [hMdef]
      have hd : (2 * A + 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
              + 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹)
            * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
          - (2 * A + 4 * Real.pi ^ 2 * (1 + S)
              * (1 + B + (a ^ 2)⁻¹
                * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s))
          = 2 * A * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
            + 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
              * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
            + 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹ := by ring
      have hnn1 : 0 ≤ 2 * A * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
        mul_nonneg (by linarith) hEb0
      have hnn2 : 0 ≤ 4 * Real.pi ^ 2 * (1 + S) * (1 + B)
          * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)) hEb0
      have hnn3 : 0 ≤ 4 * Real.pi ^ 2 * (1 + S) * (a ^ 2)⁻¹ :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
      linarith [hd, hnn1, hnn2, hnn3]
    have hKM : M * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
        ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
      have h1 : M ≤ Kp := by
        rw [hKpdef]
        calc M ≤ M * 10000 := by nlinarith [hM0]
          _ ≤ max 1 (M * 10000) := le_max_right _ _
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith [hstep, hK2, hKM]
  have hInt : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ s θ) ^ 2 * SS θ) Iθ := by
    refine MeasureTheory.Integrable.mono'
      (ws_sEta_integrableOn.const_mul
        (Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s))) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
        ((hSΨ.pz).continuousOn.pow 2 |>.mul ws_contOn_sEta) hs0
    · filter_upwards [ws_ae_mem_Ioo] with θ hθ
      have hSS : 0 ≤ SS θ := ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hSS)]
      exact mul_le_mul_of_nonneg_right (hmain θ hθ) hSS
  refine ⟨hInt, ?_⟩
  have hEb0 : 0 ≤ thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := thetaE_nonneg _ _
  have htheta := thetaE_le_const (X := Work.Spaces.pz Ψ) (s := s)
    (M := Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)) hmain
  have hEb_le : thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s ≤ Eref Ψ s := by
    rw [Eref]
    nlinarith [thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s,
      thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s,
      thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s]
  calc thetaE (Work.Spaces.pz Ψ) s
      ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
          * (∫ θ in Iθ, SS θ) := htheta
    _ ≤ Kp * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) * 10000 :=
        mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = Kp * 10000 * (1 + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by ring
    _ ≤ Kp * 10000 * (1 + Eref Ψ s) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hEb_le]

/-! ## The reference energy dominates each of its four summands -/

theorem Eref_ge_thetaE_pthIter (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.pthIter 2 Ψ) s ≤ Eref Ψ s := by
  unfold Eref
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
  have h4 := thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
  linarith

theorem Eref_ge_thetaE_DzpthIter (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h3 := thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
  have h4 := thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
  linarith

theorem Eref_ge_thetaE_G (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h4 := thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
  linarith

theorem Eref_ge_thetaE_DzG (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
      ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
  linarith

/-! ## The `θ`-energy of a sum of two slices -/

/-- If `f(z,·) = g(z,·) + h(z,·)` on the open angular interval and the `θ`-energies of the two
summands are finite, then so is that of `f`, and
`thetaE f z ≤ 2 thetaE g z + 2 thetaE h z`. -/
theorem thetaE_add_le {f g h : ℝ → ℝ → ℝ} {s : ℝ}
    (hf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f s θ = g s θ + h s θ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2 * SS θ) Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => (h s θ) ^ 2 * SS θ) Iθ)
    (haesm : AEStronglyMeasurable (fun θ => (f s θ) ^ 2 * SS θ) (volume.restrict Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => (f s θ) ^ 2 * SS θ) Iθ ∧
      thetaE f s ≤ 2 * thetaE g s + 2 * thetaE h s := by
  have hle : (fun θ => (f s θ) ^ 2 * SS θ) ≤ᵐ[volume.restrict Iθ]
      (fun θ => 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show (f s θ) ^ 2 * SS θ ≤ 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)
    rw [hf θ hθ]
    have hSS := ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsq : (g s θ + h s θ) ^ 2 ≤ 2 * (g s θ) ^ 2 + 2 * (h s θ) ^ 2 := by
      nlinarith [sq_nonneg (g s θ - h s θ)]
    calc (g s θ + h s θ) ^ 2 * SS θ
        ≤ (2 * (g s θ) ^ 2 + 2 * (h s θ) ^ 2) * SS θ := mul_le_mul_of_nonneg_right hsq hSS
      _ = 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ) := by ring
  have hInt : MeasureTheory.IntegrableOn
      (fun θ => 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)) Iθ :=
    (hg.const_mul 2).add (hh.const_mul 2)
  constructor
  · refine MeasureTheory.Integrable.mono' hInt haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, hle] with θ hθI hθ
    have hSS := ws_sEta_nonneg hθI
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hSS)]
    exact hθ
  · have hmono := MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Iθ)
      (f := fun θ => (f s θ) ^ 2 * SS θ)
      (g := fun θ => 2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ))
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθI
        exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθI))
      hInt hle
    show (∫ θ in Iθ, (f s θ) ^ 2 * SS θ)
        ≤ 2 * (∫ θ in Iθ, (g s θ) ^ 2 * SS θ) + 2 * (∫ θ in Iθ, (h s θ) ^ 2 * SS θ)
    calc (∫ θ in Iθ, (f s θ) ^ 2 * SS θ)
        ≤ ∫ θ in Iθ, (2 * ((g s θ) ^ 2 * SS θ) + 2 * ((h s θ) ^ 2 * SS θ)) := hmono
      _ = 2 * (∫ θ in Iθ, (g s θ) ^ 2 * SS θ) + 2 * (∫ θ in Iθ, (h s θ) ^ 2 * SS θ) := by
          rw [MeasureTheory.integral_add (hg.const_mul 2) (hh.const_mul 2),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## The pointwise splittings of the radial iterates -/

/-- `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open quadrant. -/
theorem DzIter_two_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ) {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ s θ
      = Work.Spaces.DzIter 1 Ψ s θ + s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ := by
  have h := Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hS hs hθ
  have hq : Work.FTS.EllipticEst.DzAmgm.Qop Ψ s θ
      = s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ := rfl
  rw [hq] at h
  linarith [h]

/-- `D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)` on the open quadrant. -/
theorem DzIter_three_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ) {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter 3 Ψ s θ
      = Work.Spaces.DzIter 2 Ψ s θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
  have h1 : Work.FTS.EllipticEst.DzAmgm.Qop (Work.Spaces.Dz Ψ) s θ
      = Work.Spaces.DzIter 2 (Work.Spaces.Dz Ψ) s θ
        - Work.Spaces.DzIter 1 (Work.Spaces.Dz Ψ) s θ :=
    Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hS.Dz hs hθ
  have h2 : Work.FTS.EllipticEst.DzAmgm.Qop (Work.Spaces.Dz Ψ) s θ
      = Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
    have h := Work.FTS.EllipticEst.DzAmgm.Qop_Dz_eq hS hs hθ
    have hq : Work.FTS.EllipticEst.DzAmgm.Qop Ψ
        = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl
    rw [hq] at h
    exact h
  have h4 : Work.Spaces.DzIter 2 (Work.Spaces.Dz Ψ) s θ = Work.Spaces.DzIter 3 Ψ s θ := rfl
  have h5 : Work.Spaces.DzIter 1 (Work.Spaces.Dz Ψ) s θ = Work.Spaces.DzIter 2 Ψ s θ := rfl
  rw [h4, h5] at h1
  linarith [h1, h2]

/-- **The `θ`-energy bounds for the radial iterates `D_z^j Ψ`, `1 ≤ j ≤ 3`.**

On a compact radial interval `[a,b] ⊂ (0,∞)` every `thetaE (D_z^j Ψ)` (`1 ≤ j ≤ 3`) is
dominated by a constant times `1 + Eref Ψ`, and every weighted slice square
`(D_z^j Ψ(s,·))² sEta` is integrable.  The only analytic input is the Poincaré bound
`thetaE_pz_le` for `∂_zΨ`; the levels `j = 2, 3` follow from the algebraic splittings
`D_z²Ψ = D_zΨ + z²∂_z²Ψ` and `D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)` (with `Eref`'s third and fourth
summands). -/
theorem sliceEnergyBounds {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ a b : ℝ, 0 < a → a < b → ∃ K : ℝ, 0 < K ∧
      (MeasureTheory.IntegrableOn (Eref Ψ) (Set.Icc a b)) ∧
      (∀ s ∈ Set.Icc a b, ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.DzIter j Ψ s θ) ^ 2 * SS θ) Iθ) ∧
      (∀ s ∈ Set.Icc a b, ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        thetaE (Work.Spaces.DzIter j Ψ) s ≤ K * (1 + Eref Ψ s)) := by
  intro a b ha hab
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hSΨ.pth.pth
  have hSG : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul (hSΨ.pzIter 2)
  have hRef : MeasureTheory.IntegrableOn (Eref Ψ) (Set.Icc a b) := by
    have h1 := (ws_thetaE_integrable hSB h.memB 0 (Nat.zero_le k) ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    have h2 := (ws_thetaE_integrable hSB h.memB 1 hk ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    have h3 := (ws_thetaE_integrable hSG h.memA 0 (Nat.zero_le k) ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    have h4 := (ws_thetaE_integrable hSG h.memA 1 hk ha).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    unfold Eref
    exact ((h1.add h2).add h3).add h4
  obtain ⟨Kp, hKp0, hKp⟩ := thetaE_pz_le hk h ha hab
  -- the square of the radial variable on `[a,b]`
  set Mb : ℝ := max 1 (b ^ 2) with hMbdef
  have hMb1 : (1 : ℝ) ≤ Mb := by rw [hMbdef]; exact le_max_left _ _
  have hs2Mb : ∀ s ∈ Set.Icc a b, s ^ 2 ≤ Mb := by
    intro s hs
    rw [hMbdef]
    rcases le_total 1 b with hb | hb
    · exact le_trans (by nlinarith [hs.1, hs.2, ha]) (le_max_right _ _)
    · have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2, hb, ha]
      exact le_trans hs2 (le_max_left _ _)
  set K1 : ℝ := Kp * Mb + 1 with hK1def
  have hK10 : (0 : ℝ) < K1 := by rw [hK1def]; positivity
  set K2 : ℝ := 2 * K1 + 2 with hK2def
  set K3 : ℝ := 2 * K2 + 2 with hK3def
  set K : ℝ := max K1 (max K2 K3) with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; exact lt_of_lt_of_le hK10 (le_max_left _ _)
  have hK1K : K1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK2K : K2 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3K : K3 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the `j = 1` level
  have hint1 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 1 Ψ s θ) ^ 2 * SS θ) Iθ :=
    fun s hs => (thetaE_const_mul (X := Work.Spaces.pz Ψ) (c := s) (hKp s hs).1).1
  have hle1 : ∀ s ∈ Set.Icc a b, thetaE (Work.Spaces.DzIter 1 Ψ) s ≤ K1 * (1 + Eref Ψ s) := by
    intro s hs
    have h1 : thetaE (Work.Spaces.DzIter 1 Ψ) s = s ^ 2 * thetaE (Work.Spaces.pz Ψ) s :=
      (thetaE_const_mul (X := Work.Spaces.pz Ψ) (c := s) (hKp s hs).1).2
    have h2 := (hKp s hs).2
    have h3 : s ^ 2 ≤ Mb := hs2Mb s hs
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    have hKpM : Kp * Mb ≤ K1 := by rw [hK1def]; linarith
    rw [h1]
    calc s ^ 2 * thetaE (Work.Spaces.pz Ψ) s
        ≤ Mb * (Kp * (1 + Eref Ψ s)) :=
          mul_le_mul h3 h2 (thetaE_nonneg _ _) (by positivity)
      _ = Kp * Mb * (1 + Eref Ψ s) := by ring
      _ ≤ K1 * (1 + Eref Ψ s) := mul_le_mul_of_nonneg_right hKpM hEref0
  -- the `j = 2` level
  have hint2 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 2 Ψ s θ) ^ 2 * SS θ) Iθ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    exact (thetaE_add_le (f := Work.Spaces.DzIter 2 Ψ) (g := Work.Spaces.DzIter 1 Ψ)
      (h := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (s := s)
      (fun θ hθ => DzIter_two_eq hSΨ hs0 hθ)
      (hint1 s hs)
      (by
        have hh := ws_slot_slice hSG h.memA 0 (Nat.zero_le k) hs0
        simpa only [Work.Spaces.DzIter_zero] using hh)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 2 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 2).continuousOn.pow 2).mul ws_contOn_sEta)).1
  have hle2 : ∀ s ∈ Set.Icc a b, thetaE (Work.Spaces.DzIter 2 Ψ) s ≤ K2 * (1 + Eref Ψ s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsplit := (thetaE_add_le (f := Work.Spaces.DzIter 2 Ψ) (g := Work.Spaces.DzIter 1 Ψ)
      (h := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (s := s)
      (fun θ hθ => DzIter_two_eq hSΨ hs0 hθ)
      (hint1 s hs)
      (by
        have hh := ws_slot_slice hSG h.memA 0 (Nat.zero_le k) hs0
        simpa only [Work.Spaces.DzIter_zero] using hh)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 2 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 2).continuousOn.pow 2).mul ws_contOn_sEta)).2
    have h1 := hle1 s hs
    have h2 := Eref_ge_thetaE_G Ψ s
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    have hK2eq : K2 = 2 * K1 + 2 := hK2def
    calc thetaE (Work.Spaces.DzIter 2 Ψ) s
        ≤ 2 * thetaE (Work.Spaces.DzIter 1 Ψ) s
            + 2 * thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s := hsplit
      _ ≤ 2 * (K1 * (1 + Eref Ψ s)) + 2 * Eref Ψ s := by linarith
      _ ≤ K2 * (1 + Eref Ψ s) := by rw [hK2eq]; nlinarith [hEref0]
  -- the `j = 3` level
  have hint3 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 3 Ψ s θ) ^ 2 * SS θ) Iθ := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    exact (thetaE_add_le (f := Work.Spaces.DzIter 3 Ψ) (g := Work.Spaces.DzIter 2 Ψ)
      (h := Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (s := s)
      (fun θ hθ => DzIter_three_eq hSΨ hs0 hθ)
      (hint2 s hs)
      (ws_slot_slice hSG h.memA 1 hk hs0)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 3 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 3).continuousOn.pow 2).mul ws_contOn_sEta)).1
  have hle3 : ∀ s ∈ Set.Icc a b, thetaE (Work.Spaces.DzIter 3 Ψ) s ≤ K3 * (1 + Eref Ψ s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hsplit := (thetaE_add_le (f := Work.Spaces.DzIter 3 Ψ) (g := Work.Spaces.DzIter 2 Ψ)
      (h := Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (s := s)
      (fun θ hθ => DzIter_three_eq hSΨ hs0 hθ)
      (hint2 s hs)
      (ws_slot_slice hSG h.memA 1 hk hs0)
      (by
        refine Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter 3 Ψ p.1 p.2) ^ 2 * SS p.2) ?_ hs0
        exact ((hSΨ.DzIter 3).continuousOn.pow 2).mul ws_contOn_sEta)).2
    have h1 := hle2 s hs
    have h2 := Eref_ge_thetaE_DzG Ψ s
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    have hK3eq : K3 = 2 * K2 + 2 := hK3def
    calc thetaE (Work.Spaces.DzIter 3 Ψ) s
        ≤ 2 * thetaE (Work.Spaces.DzIter 2 Ψ) s
            + 2 * thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
          hsplit
      _ ≤ 2 * (K2 * (1 + Eref Ψ s)) + 2 * Eref Ψ s := by linarith
      _ ≤ K3 * (1 + Eref Ψ s) := by rw [hK3eq]; nlinarith [hEref0]
  refine ⟨K, hK0, hRef, ?_, ?_⟩
  · intro s hs j hj1 hj3
    interval_cases j
    · exact hint1 s hs
    · exact hint2 s hs
    · exact hint3 s hs
  · intro s hs j hj1 hj3
    have hEref0 : 0 ≤ 1 + Eref Ψ s := by linarith [Eref_nonneg Ψ s]
    interval_cases j
    · exact le_trans (hle1 s hs) (mul_le_mul_of_nonneg_right hK1K hEref0)
    · exact le_trans (hle2 s hs) (mul_le_mul_of_nonneg_right hK2K hEref0)
    · exact le_trans (hle3 s hs) (mul_le_mul_of_nonneg_right hK3K hEref0)

/-! ## Box integrability of `(∂_z D_z^j Ψ)² sin(2θ)^{-η}` and the moment slices -/

/-- **The box integrability hypothesis of the moment relation.**  For `j ≤ 2` the uncurried
function `(s,θ) ↦ (∂_z D_z^j Ψ(s,θ))² sin(2θ)^{-η}` is integrable on the box `[a,b] × Iθ`:
the radial derivative is `D_z^{j+1}Ψ/s` and the `θ`-energy of `D_z^{j+1}Ψ` is controlled by
`sliceEnergyBounds`. -/
theorem moment_box {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj : j ≤ 2) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Iθ) := by
  intro a b ha hab
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨K, hK0, hEref, hsl, hbd⟩ := sliceEnergyBounds hk h a b ha hab
  -- the integrand and its basic properties
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
    ((hSΨ.DzIter j).pz.continuousOn.pow 2).mul ws_contOn_sEta
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Iθ,
      0 ≤ (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  have hsl' : ∀ s ∈ Set.Icc a b, MeasureTheory.Integrable (fun θ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Iθ) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hbase := hsl s hs (j + 1) (by omega) (by omega)
    have hfun : (fun θ => (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun θ => (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ) := by
      funext θ
      show (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ)
      have hid : Work.Spaces.DzIter (j + 1) Ψ s θ
          = s * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ := rfl
      rw [hid, Work.FTS.EllipticEst.sEta, mul_pow]
      have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs0)
      field_simp
    rw [hfun]
    exact hbase.const_mul _
  have hint' : MeasureTheory.Integrable
      (fun s => ∫ θ in Iθ, (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have haesm : AEStronglyMeasurable
        (fun s => ∫ θ in Iθ, (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict (Set.Icc a b)) := by
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
      have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha.le).integral_prod_right'
        (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
      simpa only [Function.uncurry_apply_pair] using h
    have hvol : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hdom : MeasureTheory.Integrable
        (fun s => (a ^ 2)⁻¹ * (K * (1 + Eref Ψ s))) (volume.restrict (Set.Icc a b)) :=
      (((MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol).add hEref).const_mul K).const_mul _
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have hval : (∫ θ in Iθ, (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = (s ^ 2)⁻¹ * thetaE (Work.Spaces.DzIter (j + 1) Ψ) s := by
      have hfun : (fun θ => (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = fun θ => (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ) := by
        funext θ
        show (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          = (s ^ 2)⁻¹ * ((Work.Spaces.DzIter (j + 1) Ψ s θ) ^ 2 * SS θ)
        have hid : Work.Spaces.DzIter (j + 1) Ψ s θ
            = s * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ := rfl
        rw [hid, Work.FTS.EllipticEst.sEta, mul_pow]
        have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs0)
        field_simp
      rw [hfun, MeasureTheory.integral_const_mul]
      rfl
    rw [hval, Real.norm_of_nonneg (mul_nonneg (by positivity) (thetaE_nonneg _ _))]
    have h2 : thetaE (Work.Spaces.DzIter (j + 1) Ψ) s ≤ K * (1 + Eref Ψ s) :=
      hbd s hs (j + 1) (by omega) (by omega)
    have h3 : (s ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < s ^ 2) (by positivity : (0 : ℝ) < a ^ 2)).mpr
        (by nlinarith [hs.1, ha])
    exact mul_le_mul h3 h2 (thetaE_nonneg _ _) (by positivity)
  exact Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab hcont hnn hsl' hint'

/-- **The slice integrability hypothesis of the moment relation**: for `j ≤ 2` and `z > 0` the
angular slice `θ ↦ D_z^j Ψ(z,θ) sinθcos²θ` is integrable.  For `j = 0` this is
`Psi_slice_sinCos2_integrable`; for `j = 1, 2` it is `ws_absMoment` together with the
`θ`-energy bound of `sliceEnergyBounds`. -/
theorem moment_slice {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj : j ≤ 2) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ
        * Work.Elliptic.sinCos2 θ) Iθ := by
  intro z hz
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  rcases Nat.eq_or_lt_of_le (Nat.zero_le j) with h0 | h0
  · subst h0
    -- `j = 0`: the slice of `Ψ` itself
    have hbase := Psi_slice_sinCos2_integrable hk h z hz
    have haesm : AEStronglyMeasurable (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict Iθ) := by
      have hcontσ : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
        simp only [Work.Elliptic.sinCos2]; fun_prop
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        (hSΨ.continuousOn.mul hcontσ.continuousOn) hz
    refine MeasureTheory.Integrable.mono' hbase haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    have hsg0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.sinCos2]
      exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
        (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsg0]
    exact le_rfl
  · -- `j = 1, 2`: the mean value bound of `ws_absMoment`
    have hj1 : 1 ≤ j := h0
    obtain ⟨K, hK0, hEref, hsl, hbd⟩ := sliceEnergyBounds hk h (z / 2) (z + 1)
      (by linarith) (by linarith)
    have hzmem : z ∈ Set.Icc (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
    have hgm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ)
        (volume.restrict Iθ) :=
      ws_aesm_slice (hSΨ.DzIter j) hz
    exact (ws_absMoment hgm (hsl z hzmem j hj1 (by omega))).1

/-- **Local integrability of `F_*(D_z^j Ψ)/r` for `j = 2, 3`.**  The moment is bounded by
`π/2 + thetaE (D_z^j Ψ)` (`ws_absMoment`), which is dominated by `1 + Eref Ψ`; dividing by
`r ≥ c > 0` preserves local integrability. -/
theorem moment_div_integrableOn_Icc {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj1 : 2 ≤ j) (hj3 : j ≤ 3) {c d : ℝ}
    (hc : 0 < c) (hcd : c < d) :
    MeasureTheory.IntegrableOn
      (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r) (Set.Icc c d) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨K, hK0, hEref, hsl, hbd⟩ := sliceEnergyBounds hk h c d hc hcd
  have hvol : (volume : Measure ℝ) (Set.Icc c d) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdom : MeasureTheory.Integrable
      (fun r => c⁻¹ * (Real.pi / 2 + K * (1 + Eref Ψ r))) (volume.restrict (Set.Icc c d)) := by
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => Real.pi / 2) (Set.Icc c d) :=
      MeasureTheory.integrableOn_const (C := Real.pi / 2) hvol
    have h2 : MeasureTheory.IntegrableOn (fun r => K * (1 + Eref Ψ r)) (Set.Icc c d) :=
      ((MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol).add hEref).const_mul K
    exact (h1.add h2).const_mul (c⁻¹)
  have haesm : AEStronglyMeasurable
      (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r)
      (volume.restrict (Set.Icc c d)) := by
    have h1 : AEStronglyMeasurable (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r)
        (volume.restrict (Set.Icc c d)) :=
      aesm_fstar_Icc (hSΨ.DzIter j).continuousOn hc.le
    have h2 : AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Set.Icc c d)) :=
      (continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le hc hx.1))).aestronglyMeasurable
        measurableSet_Icc
    exact (h1.mul h2).congr (Filter.Eventually.of_forall (fun r => by
      show Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r * r⁻¹
        = Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r
      rw [div_eq_mul_inv]))
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with r hr
  have hr0 : 0 < r := lt_of_lt_of_le hc hr.1
  -- the pointwise bound on the moment
  have hgm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter j Ψ r θ)
      (volume.restrict Iθ) := ws_aesm_slice (hSΨ.DzIter j) hr0
  have habs : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r| ≤ Real.pi / 2 + K * (1 + Eref Ψ r) := by
    have h1 : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r|
        ≤ ∫ θ in Iθ, |Work.Spaces.DzIter j Ψ r θ| * Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.Fstar]
      calc |∫ θ in Iθ, Work.Spaces.DzIter j Ψ r θ * Work.Elliptic.sinCos2 θ|
          ≤ ∫ θ in Iθ, |Work.Spaces.DzIter j Ψ r θ * Work.Elliptic.sinCos2 θ| :=
            abs_integral_le_integral_abs
        _ = ∫ θ in Iθ, |Work.Spaces.DzIter j Ψ r θ| * Work.Elliptic.sinCos2 θ := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
            rw [abs_mul]
            congr 1
            rw [Work.Elliptic.sinCos2]
            exact abs_of_nonneg (mul_nonneg (Real.sin_nonneg_of_mem_Icc
              ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _))
    have h2 := (ws_absMoment hgm (hsl r hr j (by omega) (by omega))).2
    have h3 : thetaE (Work.Spaces.DzIter j Ψ) r ≤ K * (1 + Eref Ψ r) :=
      hbd r hr j (by omega) (by omega)
    have h3' : (∫ θ in Iθ, (Work.Spaces.DzIter j Ψ r θ) ^ 2 * SS θ) ≤ K * (1 + Eref Ψ r) := h3
    linarith [h1, h2, h3']
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
  have hnum : 0 ≤ Real.pi / 2 + K * (1 + Eref Ψ r) := by
    nlinarith [hK0, Real.pi_pos, Eref_nonneg Ψ r]
  have h1 : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r| / r
      ≤ (Real.pi / 2 + K * (1 + Eref Ψ r)) * r⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right habs (by positivity)
  have h2 : (Real.pi / 2 + K * (1 + Eref Ψ r)) * r⁻¹
      ≤ (Real.pi / 2 + K * (1 + Eref Ψ r)) * c⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ hnum
    rw [inv_le_inv₀ hr0 hc]
    exact hr.1
  have h3 : (Real.pi / 2 + K * (1 + Eref Ψ r)) * c⁻¹
      = c⁻¹ * (Real.pi / 2 + K * (1 + Eref Ψ r)) := by ring
  linarith [h1, h2, h3]

/-- **The chain rule for the moment `F_*(D_z^j Ψ)`**, `j ≤ 2`:
`F_*(D_z^j Ψ)(b) - F_*(D_z^j Ψ)(a) = ∫_a^b F_*(D_z^{j+1} Ψ)(r)/r dr`.  It is
`moment_relation` (`Work.FTS.EllipticEst.moment_relation`) applied to `D_z^j Ψ`. -/
theorem moment_chain {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (j : ℕ) (hj : j ≤ 2) :
    ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) b
          - Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) r / r := by
  intro a b ha hab
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmain := Work.FTS.EllipticEst.moment_relation (Work.Spaces.DzIter j Ψ)
    (hSΨ.DzIter j) (moment_box hk h j hj) (moment_slice hk h j hj) ha hab
  have hinner : ∀ s ∈ Set.Icc a b,
      (∫ θ in Iθ, Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) s / s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    rw [Work.Elliptic.Fstar]
    have hfun : (fun θ => Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ * Work.Elliptic.sinCos2 θ)
        = fun θ => s⁻¹ * (Work.Spaces.DzIter (j + 1) Ψ s θ * Work.Elliptic.sinCos2 θ) := by
      funext θ
      have hid : Work.Spaces.DzIter (j + 1) Ψ s θ
          = s * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) s θ := rfl
      rw [hid]
      field_simp
    rw [hfun, MeasureTheory.integral_const_mul]
    ring
  rw [hmain]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hinner]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le]
  ring

theorem wsMomentChain (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the primitive of `F_*(D_zΨ)/r` vanishes identically
  have hprim1 : ∀ s w : ℝ, 0 < s → s < w →
      (∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r) = 0 := by
    intro s w hs hsw
    have h0 := moment_chain hk h 0 (by norm_num) s w hs hsw
    simp only [Work.Spaces.DzIter_zero] at h0
    rw [h.orthPsi w (lt_trans hs hsw), h.orthPsi s hs, sub_self] at h0
    linarith [h0]
  -- `F_*(D_zΨ)` is continuous on `(0,∞)`, being a primitive of `F_*(D_z²Ψ)/r`
  have hcont1 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have hs0 : 0 < z / 2 := by linarith
    have hInt2 : IntervalIntegrable
        (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) volume (z / 2) (2 * z) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact moment_div_integrableOn_Icc hk h 2 le_rfl (by norm_num) hs0 (by linarith)
    have hcontprim : ContinuousOn (fun w => ∫ r in z / 2..w,
        Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) (Set.uIcc (z / 2) (2 * z)) :=
      intervalIntegral.continuousOn_primitive_interval' hInt2 (by
        rw [Set.uIcc_of_le (by linarith)]
        exact ⟨le_rfl, by linarith⟩)
    have hmem : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : z / 2 ≤ 2 * z)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    have hev : (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) w) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (z / 2)
          + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      have h1 := moment_chain hk h 1 (by norm_num) (z / 2) w hs0 hw
      linarith [h1]
    have hcontc : ContinuousAt (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (z / 2)
        + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) z :=
      continuousAt_const.add (hcontprim.continuousAt hmem)
    exact (hcontc.congr hev.symm).continuousWithinAt
  have hA1zero : ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
    intro z hz
    have hs0 : 0 < z / 2 := by linarith
    have hev : (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      exact hprim1 (z / 2) w hs0 hw
    have hder0 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r) 0 z :=
      hev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
    have hcontA : ContinuousOn (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r)
        (Set.Ioi 0) := hcont1.div continuousOn_id (fun r hr => ne_of_gt hr)
    have hcontAz : ContinuousAt (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r) z :=
      hcontA.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hder1 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) r / r)
        (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z / z) z := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hcontAz
      · have hsub : Set.uIcc (z / 2) z ⊆ Set.Ioi 0 := by
          rw [Set.uIcc_of_le (by linarith)]
          exact fun r hr => lt_of_lt_of_le hs0 hr.1
        exact ((hcont1.mono hsub).div continuousOn_id
          (fun r hr => ne_of_gt (hsub hr))).intervalIntegrable
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcontA z hz
    have huniq := hder1.unique hder0
    exact (div_eq_zero_iff.mp huniq).resolve_right (ne_of_gt hz)
  -- the primitive of `F_*(D_z²Ψ)/r` vanishes identically
  have hprim2 : ∀ s w : ℝ, 0 < s → s < w →
      (∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) = 0 := by
    intro s w hs hsw
    have h1 := moment_chain hk h 1 (by norm_num) s w hs hsw
    rw [hA1zero w (lt_trans hs hsw), hA1zero s hs, sub_self] at h1
    linarith [h1]
  -- `F_*(D_z²Ψ)` is continuous on `(0,∞)`, being a primitive of `F_*(D_z³Ψ)/r`
  have hcont2 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have hs0 : 0 < z / 2 := by linarith
    have hInt3 : IntervalIntegrable
        (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) volume (z / 2) (2 * z) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
      exact moment_div_integrableOn_Icc hk h 3 (by norm_num) le_rfl hs0 (by linarith)
    have hcontprim : ContinuousOn (fun w => ∫ r in z / 2..w,
        Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) (Set.uIcc (z / 2) (2 * z)) :=
      intervalIntegral.continuousOn_primitive_interval' hInt3 (by
        rw [Set.uIcc_of_le (by linarith)]
        exact ⟨le_rfl, by linarith⟩)
    have hmem : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : z / 2 ≤ 2 * z)]
      exact Icc_mem_nhds (by linarith) (by linarith)
    have hev : (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) w) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) (z / 2)
          + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      have h1 := moment_chain hk h 2 (by norm_num) (z / 2) w hs0 hw
      linarith [h1]
    have hcontc : ContinuousAt (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) (z / 2)
        + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) r / r) z :=
      continuousAt_const.add (hcontprim.continuousAt hmem)
    exact (hcontc.congr hev.symm).continuousWithinAt
  have hA2zero : ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0 := by
    intro z hz
    have hs0 : 0 < z / 2 := by linarith
    have hev : (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with w hw
      exact hprim2 (z / 2) w hs0 hw
    have hder0 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) 0 z :=
      hev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
    have hcontA : ContinuousOn (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r)
        (Set.Ioi 0) := hcont2.div continuousOn_id (fun r hr => ne_of_gt hr)
    have hcontAz : ContinuousAt (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r) z :=
      hcontA.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hder1 : HasDerivAt
        (fun w => ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) r / r)
        (Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z / z) z := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ hcontAz
      · have hsub : Set.uIcc (z / 2) z ⊆ Set.Ioi 0 := by
          rw [Set.uIcc_of_le (by linarith)]
          exact fun r hr => lt_of_lt_of_le hs0 hr.1
        exact ((hcont2.mono hsub).div continuousOn_id
          (fun r hr => ne_of_gt (hsub hr))).intervalIntegrable
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcontA z hz
    have huniq := hder1.unique hder0
    exact (div_eq_zero_iff.mp huniq).resolve_right (ne_of_gt hz)
  intro j hj z hz
  interval_cases j
  · exact h.orthPsi z hz
  · exact hA1zero z hz
  · exact hA2zero z hz

end Work.FTS.EllipticEst.remov
