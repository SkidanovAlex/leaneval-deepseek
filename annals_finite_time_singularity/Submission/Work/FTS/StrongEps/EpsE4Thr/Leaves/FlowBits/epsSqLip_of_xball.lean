import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SqWeakAux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_StreamBdry.SB5.sb5_decay
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.LeafD2.fderivFeps_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-! ## The `fderiv`-in-`X` estimate for the difference of two right-hand sides

Statement unchanged (the harness reads it).  Proof: `Feps u − Feps v = W_ε Δ` with
`Δ = profRHS (W_ε u) − profRHS (W_ε v)` (`Wp_sub_eq_mem`), and the `ℋ⁴`-chain of
`EpsLocalPStar.profRHS_sub_sup_le_Sq` gives `HkNorm α 4 (W_ε Δ) ≤ T K₁ M₀² Q √(EpsSq (u−v))`;
the trace-free `ℋ⁴ → C¹` trade-off (`fderiv_uncurry_le_HkNorm_aux`, the `fderiv` form of
`v2_hkMem_pointwise_min`) bounds the operator norm of the two partials by
`C (1 + 1/sin 2θ) HkNorm α 4 (W_ε Δ)`. -/

/-- **The trace-free `ℋ⁴ → C¹` trade-off.**  For a function `g` smooth on the open quadrant and
honestly in `ℋ⁴` (`HkMem α 4 g`), the operator norm of the Fréchet derivative of
`Function.uncurry g` at `(z,θ)` (`z > 0`, `0 < θ < π/2`) is controlled by `HkNorm α 4 g` with the
boundary factor `1 + 1/sin 2θ` (the `z`-slot `mixed 1 0 g = z ∂_z g` needs none, the `θ`-slot
`mixed 0 1 g = sin 2θ · ∂_θ g` does).

This is the `fderiv` form of `Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min`; it is applied to
`g = W_ε Δ`, whose `ℋ⁴`-size is the output of the `profRHS`-difference chain. -/
theorem fderiv_uncurry_le_HkNorm_aux {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 g → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      ‖fderiv ℝ (Function.uncurry g) (z, θ)‖
        ≤ C * (1 + 1 / Real.sin (2 * θ)) * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C0, hC00, hbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα.1 hα.2
  refine ⟨2 * C0 + 1, by linarith, ?_⟩
  intro g hsm hmem z θ hz hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have h4 : ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hsm 4
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) := by
    have h1 : ContDiffOn ℝ 1 (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hsm 1
    exact (h1.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ⟩)
  have he1 : Work.Spaces.pz g z θ = (fderiv ℝ (Function.uncurry g) (z, θ)) (1, 0) :=
    Work.Spaces.pz_eq_fderiv hd
  have he2 : Work.Spaces.pth g z θ = (fderiv ℝ (Function.uncurry g) (z, θ)) (0, 1) :=
    Work.Spaces.pth_eq_fderiv hd
  have hKn : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hb1 : |Work.Spaces.pz g z θ| ≤ C0 * Work.Spaces.HkNorm α 4 g := by
    have h := hbd g h4 hmem 1 0 (by norm_num) z θ hz hθ0 hθ1
    have hz1 : Work.Spaces.mixed 1 0 g z θ = z * Work.Spaces.pz g z θ := rfl
    rw [hz1, abs_mul, abs_of_pos hz] at h
    have h2 : z * |Work.Spaces.pz g z θ| ≤ z * (C0 * Work.Spaces.HkNorm α 4 g) :=
      calc z * |Work.Spaces.pz g z θ| ≤ C0 * min z 1 * Work.Spaces.HkNorm α 4 g := h
        _ ≤ C0 * z * Work.Spaces.HkNorm α 4 g :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (min_le_left z 1) hC00) hKn
        _ = z * (C0 * Work.Spaces.HkNorm α 4 g) := by ring
    exact (mul_le_mul_iff_of_pos_left hz).mp h2
  have hb2 : |Work.Spaces.pth g z θ| ≤ C0 * Work.Spaces.HkNorm α 4 g / Real.sin (2 * θ) := by
    have h := hbd g h4 hmem 0 1 (by norm_num) z θ hz hθ0 hθ1
    have hz2 : Work.Spaces.mixed 0 1 g z θ = Real.sin (2 * θ) * Work.Spaces.pth g z θ := rfl
    rw [hz2, abs_mul, abs_of_pos hs] at h
    have hb : |Work.Spaces.pth g z θ| * Real.sin (2 * θ) ≤ C0 * Work.Spaces.HkNorm α 4 g :=
      calc |Work.Spaces.pth g z θ| * Real.sin (2 * θ)
          = Real.sin (2 * θ) * |Work.Spaces.pth g z θ| := by ring
        _ ≤ C0 * min z 1 * Work.Spaces.HkNorm α 4 g := h
        _ ≤ C0 * Work.Spaces.HkNorm α 4 g := by
            have hh := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (min_le_right z 1) hC00) hKn
            linarith [hh]
    exact (le_div_iff₀ hs).mpr hb
  have hfac : 0 ≤ 1 + 1 / Real.sin (2 * θ) := by
    have : 0 ≤ 1 / Real.sin (2 * θ) := by positivity
    linarith
  have hsum : |Work.Spaces.pz g z θ| + |Work.Spaces.pth g z θ|
      ≤ (2 * C0 + 1) * (1 + 1 / Real.sin (2 * θ)) * Work.Spaces.HkNorm α 4 g := by
    calc |Work.Spaces.pz g z θ| + |Work.Spaces.pth g z θ|
        ≤ C0 * Work.Spaces.HkNorm α 4 g
          + C0 * Work.Spaces.HkNorm α 4 g / Real.sin (2 * θ) := add_le_add hb1 hb2
      _ = C0 * Work.Spaces.HkNorm α 4 g * (1 + 1 / Real.sin (2 * θ)) := by ring
      _ ≤ (2 * C0 + 1) * Work.Spaces.HkNorm α 4 g * (1 + 1 / Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hKn) hfac
      _ = (2 * C0 + 1) * (1 + 1 / Real.sin (2 * θ)) * Work.Spaces.HkNorm α 4 g := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  have hxnorm : ‖x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ))‖ = max |x.1| |x.2| := by
    rw [show x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) = (x.1, x.2) from by
      ext <;> simp, Prod.norm_def]
    simp [Real.norm_eq_abs]
  rw [hx, map_add, map_smul, map_smul, ← he1, ← he2, smul_eq_mul, smul_eq_mul, Real.norm_eq_abs,
    hxnorm]
  have hm1 : |x.1| ≤ max |x.1| |x.2| := le_max_left _ _
  have hm2 : |x.2| ≤ max |x.1| |x.2| := le_max_right _ _
  have hmax0 : 0 ≤ max |x.1| |x.2| := le_trans (abs_nonneg x.1) hm1
  calc |x.1 * Work.Spaces.pz g z θ + x.2 * Work.Spaces.pth g z θ|
      ≤ |x.1| * |Work.Spaces.pz g z θ| + |x.2| * |Work.Spaces.pth g z θ| := by
        refine le_trans (abs_add_le _ _) ?_
        exact add_le_add (le_of_eq (abs_mul _ _)) (le_of_eq (abs_mul _ _))
    _ ≤ max |x.1| |x.2| * |Work.Spaces.pz g z θ|
          + max |x.1| |x.2| * |Work.Spaces.pth g z θ| :=
        add_le_add (mul_le_mul_of_nonneg_right hm1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hm2 (abs_nonneg _))
    _ = max |x.1| |x.2| * (|Work.Spaces.pz g z θ| + |Work.Spaces.pth g z θ|) := by ring
    _ ≤ max |x.1| |x.2| * ((2 * C0 + 1) * (1 + 1 / Real.sin (2 * θ))
          * Work.Spaces.HkNorm α 4 g) := mul_le_mul_of_nonneg_left hsum hmax0
    _ = (2 * C0 + 1) * (1 + 1 / Real.sin (2 * θ)) * Work.Spaces.HkNorm α 4 g
          * max |x.1| |x.2| := by ring

theorem fderivFeps_sub_le {α C₀ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Work.FTS.Galerkin.Fn,
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u → Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      ‖fderiv ℝ (Function.uncurry (fun z θ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)) (z, θ)‖
        ≤ C * (1 + 1 / Real.sin (2 * θ))
          * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- ## the constants of the library
  obtain ⟨K₁, hK₁pos, hK₁⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨CD, hCDpos, hCD⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.HkSq_Wp_sub_le_weak (α := α) hρ hα hε hε1
  obtain ⟨Cf, hCfpos, hCfb⟩ := fderiv_uncurry_le_HkNorm_aux (α := α) hα
  -- ## the `R`-dependent universe of the `ℋ⁶`-sizes of the two profiles
  set BS : ℝ := Real.sqrt (CH * (CH / ε) ^ 10 * R) + Real.sqrt (CH * (CH / ε) ^ 12 * R) + 1
    with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]
    have h1 := Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R)
    have h2 := Real.sqrt_nonneg (CH * (CH / ε) ^ 12 * R)
    linarith
  have hWp6 : ∀ {w : Fn}, Work.FTS.EllipticEst.SmoothOpen w → Work.FTS.StrongEps.EpsMem α w →
      Work.FTS.StrongEps.EpsSq α w ≤ R →
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w) ≤ BS := by
    intro w hsw hmw hrw
    have hfac : 0 ≤ CH * (CH / ε) ^ 12 := by positivity
    have hle : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)
        ≤ CH * (CH / ε) ^ 12 * R :=
      le_trans (hCH α hα ε hε hε1 6 (by norm_num) w hsw hmw)
        (mul_le_mul_of_nonneg_left hrw hfac)
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hle) ?_
    rw [hBSdef]
    linarith [Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R),
      Real.sqrt_nonneg (CH * (CH / ε) ^ 12 * R)]
  have hWp5 : ∀ {w : Fn}, Work.FTS.EllipticEst.SmoothOpen w → Work.FTS.StrongEps.EpsMem α w →
      Work.FTS.StrongEps.EpsSq α w ≤ R →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w) ≤ BS := by
    intro w hsw hmw hrw
    have hfac : 0 ≤ CH * (CH / ε) ^ 10 := by positivity
    have hle : Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)
        ≤ CH * (CH / ε) ^ 10 * R :=
      le_trans (hCH α hα ε hε hε1 5 (by norm_num) w hsw hmw)
        (mul_le_mul_of_nonneg_left hrw hfac)
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hle) ?_
    rw [hBSdef]
    linarith [Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R),
      Real.sqrt_nonneg (CH * (CH / ε) ^ 12 * R)]
  -- ## the elliptic data of the profiles
  obtain ⟨RX, hRXpos, hRX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := 2 * C₀)
      (B := BS) hα hEll hstar hml hBS0
  -- ## the final constants
  set Q : ℝ := Real.sqrt CD with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set M₀ : ℝ := 1 + 2 * BS with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  set T : ℝ := Real.sqrt (CH * (CH / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2)) with hTdef
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  refine ⟨max 1 (Cf * T * K₁ * M₀ ^ 2 * Q), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hu hv z θ hz hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  -- ## the `X`-ball data of the two data
  have hsu : Work.FTS.EllipticEst.SmoothOpen u := hu.smoothOpen
  have hsv : Work.FTS.EllipticEst.SmoothOpen v := hv.smoothOpen
  have hmu : Work.FTS.StrongEps.EpsMem α u := hu.mem
  have hmv : Work.FTS.StrongEps.EpsMem α v := hv.mem
  have hru : Work.FTS.StrongEps.EpsSq α u ≤ R := hu.sq_le
  have hrv : Work.FTS.StrongEps.EpsSq α v ≤ R := hv.sq_le
  have hclu : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) := hu.classC
  have hclv : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := hv.classC
  have hxnu : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ (2 * C₀) * α ^ 2 :=
    hu.ball
  have hxnv : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ (2 * C₀) * α ^ 2 :=
    hv.ball
  -- ## the abbreviations
  set Φu : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
    (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) with hΦudef
  set Φv : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
    (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) with hΦvdef
  set Δ : Fn := fun z θ => Φu z θ - Φv z θ with hΔdef
  set d : Fn := fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ with hddef
  -- ## the `ℋ⁴`-data of `Δ`
  obtain ⟨hΔsm₀, hΔmem₀, hΔxn₀⟩ := hK₁
    (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
    (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclu hclv hxnu hxnv
  have hΔsm : Work.FTS.EllipticEst.SmoothOpen Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef] using hΔsm₀
  have hΔmem4 : Work.Spaces.HkMem α 4 Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef] using hΔmem₀
  have hΔmem1 : Work.Spaces.HkMem α 1 Δ :=
    Work.FTS.OpenPkg.HkMem_mono_open hΔsm 1 (by norm_num) hΔmem4
  have hΔxn : Work.FTS.Nonlin.Xn α Δ
      ≤ K₁ * (1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
          + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
        * Work.Spaces.HkNorm α 5 d := by
    rw [hΔdef, hddef]
    simpa only [hΦudef, hΦvdef] using hΔxn₀
  -- ## `EpsMem`/`EpsSq` of `Δ` via the vanishing angular traces
  obtain ⟨ht1, ht2⟩ := Work.FTS.StrongEps.EpsRLX.DiffTraces (α := α) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
    (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (E := E) hα hclu hclv
    ((hEll (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) hclu).1)
    ((hEll (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclv).1) hstar
  obtain ⟨hΔepsMem, hΔepsSq⟩ := hCT α hα Δ hΔsm hΔmem1
    (fun z hz => by simpa only [hΦudef, hΦvdef] using ht1 z hz)
    (fun z hz => by simpa only [hΦudef, hΦvdef] using ht2 z hz)
  have hΔHk : Work.Spaces.HkSq α 1 Δ ≤ (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hΔmem4) ?_
    rw [show Work.FTS.Nonlin.Xn α Δ = Work.Spaces.HkNorm α 4 Δ from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 Δ)]
  -- ## the per-profile regularity of the two right-hand sides
  have hXu := hRX (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) hclu hxnu (hWp6 hsu hmu hru)
  have hXv := hRX (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclv hxnv (hWp6 hsv hmv hrv)
  have hsmΦu : Work.FTS.EllipticEst.SmoothOpen Φu := by rw [hΦudef]; exact hXu.1
  have hmem4Φu : Work.Spaces.HkMem α 4 Φu := by rw [hΦudef]; exact hXu.2.1
  have hsmΦv : Work.FTS.EllipticEst.SmoothOpen Φv := by rw [hΦvdef]; exact hXv.1
  have hmem4Φv : Work.Spaces.HkMem α 4 Φv := by rw [hΦvdef]; exact hXv.2.1
  -- ## the size bounds
  have hDd : (Work.Spaces.HkNorm α 5 d) ^ 2
      ≤ CD * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    have h := hCD hsu hsv hmu hmv hclu hclv
    rw [hddef]
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5 _)]
    exact h
  have hQbd : Work.Spaces.HkNorm α 5 d
      ≤ Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    have hd0 : 0 ≤ Work.Spaces.HkNorm α 5 d := Work.Spaces.HkNorm_nonneg α 5 d
    calc Work.Spaces.HkNorm α 5 d
        = Real.sqrt ((Work.Spaces.HkNorm α 5 d) ^ 2) := (Real.sqrt_sq hd0).symm
      _ ≤ Real.sqrt (CD * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) :=
          Real.sqrt_le_sqrt hDd
      _ = Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
          rw [hQdef, Real.sqrt_mul hCDpos.le]
  have hWu : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS :=
    hWp5 hsu hmu hru
  have hWv : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ BS :=
    hWp5 hsv hmv hrv
  have hMle : 1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ M₀ := by
    rw [hM₀def]
    linarith
  have hM0 : 0 ≤ 1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := by
    have h1 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) :=
      Work.Spaces.HkNorm_nonneg α 5 _
    have h2 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) :=
      Work.Spaces.HkNorm_nonneg α 5 _
    linarith
  have hXnΔ : Work.FTS.Nonlin.Xn α Δ ≤ K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d := by
    refine le_trans hΔxn ?_
    have hM2 : (1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2 ≤ M₀ ^ 2 :=
      pow_le_pow_left₀ hM0 hMle 2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hK₁pos.le)
      (Work.Spaces.HkNorm_nonneg α 5 d)
  have hKM : 0 ≤ K₁ * M₀ ^ 2 := mul_nonneg hK₁pos.le (pow_nonneg hM₀0 2)
  -- ## the mollified difference `W_ε Δ`
  have hsmJΔ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm)
  have hsmWpΔ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
    Work.FTS.StrongEps.EpsLocalPStar.smoothOpen_Pz hsmJΔ
  have hmemWpΔ : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
    Work.FTS.StrongEps.EpsLocalPStar.hkMem_Pz hsmJΔ (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm) hΔmem4)
  have hWpSq : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
      ≤ CH * (CH / ε) ^ 8 * Work.FTS.StrongEps.EpsSq α Δ :=
    hCH α hα ε hε hε1 4 (by norm_num) Δ hΔsm hΔepsMem
  have hTbd : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
      ≤ T * Work.Spaces.HkNorm α 4 Δ := by
    have hx0 : 0 ≤ Work.Spaces.HkNorm α 4 Δ := Work.Spaces.HkNorm_nonneg α 4 Δ
    have hc1 : 0 ≤ CH * (CH / ε) ^ 8 := by positivity
    have hc2 : 0 ≤ CT / (Work.Spaces.gam α - 1) ^ 2 := div_nonneg hCTpos.le (sq_nonneg _)
    have hprod0 : 0 ≤ CH * (CH / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2) :=
      mul_nonneg hc1 hc2
    have hA2 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
        ≤ T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2 := by
      refine le_trans hWpSq ?_
      calc CH * (CH / ε) ^ 8 * Work.FTS.StrongEps.EpsSq α Δ
          ≤ CH * (CH / ε) ^ 8
              * (CT / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 Δ) :=
            mul_le_mul_of_nonneg_left hΔepsSq hc1
        _ ≤ CH * (CH / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2
              * (Work.Spaces.HkNorm α 4 Δ) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔHk hc2) hc1
        _ = T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2 := by
            rw [hTdef, Real.sq_sqrt hprod0]; ring
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ))
        ≤ Real.sqrt (T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2) := Real.sqrt_le_sqrt hA2
      _ = T * Work.Spaces.HkNorm α 4 Δ := by
          rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0, Real.sqrt_sq hx0]
  -- ## the `ℋ⁴`-size bound of `W_ε Δ`
  have hXnb : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
      ≤ T * (K₁ * M₀ ^ 2 * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α
          (fun z θ => u z θ - v z θ)))) := by
    refine le_trans hTbd ?_
    have h4 : Work.Spaces.HkNorm α 4 Δ ≤ K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d := by
      rw [show Work.Spaces.HkNorm α 4 Δ = Work.FTS.Nonlin.Xn α Δ from rfl]
      exact hXnΔ
    exact mul_le_mul_of_nonneg_left (le_trans h4 (mul_le_mul_of_nonneg_left hQbd hKM)) hT0
  -- ## the identification of the two right-hand sides
  have hFeps : Work.FTS.EpsEngine.Feps α ρ ε Φs E u - Work.FTS.EpsEngine.Feps α ρ ε Φs E v
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ := by
    have h1 : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
          - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu)
          - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) := by
      rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E 0 u,
        Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E 0 v,
        hΦudef, hΦvdef]
      rfl
    rw [Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v, h1, hΔdef]
    exact Work.FTS.StrongEps.EpsLocalPStar.Wp_sub_eq_mem hα hρ hε hsmΦu hsmΦv hmem4Φu hmem4Φv
  have hfun : (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
      = fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ := by
    funext z θ
    exact congrFun (congrFun hFeps z) θ
  rw [hfun]
  -- ## the two partials of `W_ε Δ`
  have hsinpos : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have h1sin : 0 ≤ 1 + 1 / Real.sin (2 * θ) := by positivity
  have hstep : ‖fderiv ℝ (Function.uncurry (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)) (z, θ)‖
      ≤ Cf * (1 + 1 / Real.sin (2 * θ))
        * (T * (K₁ * M₀ ^ 2 * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α
            (fun z θ => u z θ - v z θ))))) := by
    refine le_trans (hCfb (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) hsmWpΔ hmemWpΔ z θ hz hθ) ?_
    exact mul_le_mul_of_nonneg_left hXnb (mul_nonneg hCfpos.le h1sin)
  refine le_trans hstep ?_
  have hCfin : 0 ≤ Cf * T * K₁ * M₀ ^ 2 * Q := by positivity
  calc Cf * (1 + 1 / Real.sin (2 * θ))
        * (T * (K₁ * M₀ ^ 2 * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α
            (fun z θ => u z θ - v z θ)))))
      = (Cf * T * K₁ * M₀ ^ 2 * Q) * (1 + 1 / Real.sin (2 * θ))
          * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by ring
    _ ≤ max 1 (Cf * T * K₁ * M₀ ^ 2 * Q) * (1 + 1 / Real.sin (2 * θ))
          * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ h1sin)
          (Real.sqrt_nonneg _)
        exact le_max_right _ _

end Work.FTS.StrongEps.EpsE4Thr.LeafD2
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.epsSqLip_of_xball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

/-! ## The open box carries the whole restricted product measure -/

/-- **Almost every point of `(vol↾uIoc a b) ⊗ DomM` lies in the open box
`Ioo a b × Quad`**: the time coordinate misses `{a,b}` (a null set for Lebesgue) and the profile
coordinate misses the boundary of the quadrant (`ae_open_DomM`). -/
private lemma ae_mem_box_uIoc {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM),
      p.1 ∈ Set.Ioo a b ∧ p.2 ∈ Work.FTS.StrongEps.Quad := by
  have hIoc : Set.Ioc a b =ᵐ[(MeasureTheory.volume : Measure ℝ)] Set.Ioo a b :=
    (MeasureTheory.Ioc_ae_eq_Icc).trans (MeasureTheory.Ioo_ae_eq_Icc).symm
  have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a b)), x ∈ Set.Ioo a b := by
    rw [Set.uIoc_of_le hab, MeasureTheory.Measure.restrict_congr_set hIoc]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have h2 : ∀ᵐ y ∂Work.FTS.StrongEps.EpsLocalPStar.DomM, y ∈ Work.FTS.StrongEps.Quad := by
    filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with y hy
    exact hy
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards [h1] with x hx
    filter_upwards [h2] with y hy
    exact ⟨hx, hy⟩
  · exact (measurableSet_Ioo.preimage measurable_fst).inter
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet.preimage measurable_snd)

/-- **A function continuous on the open box `Ioo a b × Quad` is a.e. strongly measurable for the
restricted product measure `(vol↾uIoc a b) ⊗ DomM`.** -/
private lemma aesm_of_continuousOn_box {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad)) :
    MeasureTheory.AEStronglyMeasurable f
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) := by
  have hU : MeasurableSet (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad) :=
    (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioo)).measurableSet
  have hμ : (((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      Work.FTS.StrongEps.EpsLocalPStar.DomM).restrict (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad))
      = ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) :=
    Measure.restrict_eq_self_of_ae_mem (ae_mem_box_uIoc hab)
  rw [← hμ]
  exact hf.aestronglyMeasurable hU

/-! ## The single-solution Volterra identity on a subinterval -/

/-- **The fake-time fundamental theorem of calculus for a regular `P₀`-solution**, on a general
subinterval `[s,t] ⊆ [0,δ]` of the horizon: on the open quadrant the increment of the family is
the interval integral of the (τ-free) right-hand side `Feps` along the curve of slices. -/
private lemma volterra_interval_of_regP {α ε δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E g₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g) :
    ∀ z θ s t : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → s ∈ Set.Icc 0 δ → t ∈ Set.Icc 0 δ →
      s ≤ t → g z θ t - g z θ s
        = ∫ σ in s..t, Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ := by
  intro z θ s t hz hθ hs ht hst
  have hder : ∀ σ ∈ Set.Icc 0 δ,
      HasDerivWithinAt (fun s' : ℝ => g z θ s')
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) (Set.Icc 0 δ) σ := by
    intro σ hσ
    have h := hsol.2 z θ σ hz hθ hσ
    rwa [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
  have hcontG : ContinuousOn (fun σ : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ)
      (Set.Icc 0 δ) :=
    Work.FTS.StrongEps.IsEpsSolPQ.continuousOn_derivWithin_curve
      (f := fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (v := fun σ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) hδ hz hθ hreg.1 hder
  have hsub : Set.Icc s t ⊆ Set.Icc 0 δ := fun x hx => ⟨le_trans hs.1 hx.1, le_trans hx.2 ht.2⟩
  have hcontf : ContinuousOn (fun σ : ℝ => g z θ σ) (Set.Icc s t) := by
    have hcurve : ContinuousOn (fun σ : ℝ => (z, (θ, σ))) (Set.Icc s t) := by fun_prop
    have hmap : Set.MapsTo (fun σ : ℝ => (z, (θ, σ))) (Set.Icc s t)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) :=
      fun σ hσ => ⟨hz, hθ, hsub hσ⟩
    exact (hreg.1.continuousOn.comp hcurve hmap).congr (fun σ _ => rfl)
  have hint : IntervalIntegrable
      (fun σ : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) volume s t :=
    ContinuousOn.intervalIntegrable_of_Icc hst (hcontG.mono hsub)
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcontf ?_ hint).symm
  intro x hx
  have hx0 : 0 < x := lt_of_le_of_lt hs.1 hx.1
  have hxδ : x < δ := lt_of_lt_of_le hx.2 ht.2
  exact (hder x ⟨hx0.le, hxδ.le⟩).hasDerivAt (Icc_mem_nhds hx0 hxδ)

/-! ## The target -/

theorem epsSqLip_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ)) :
    ∃ Lw : ℝ, 0 < Lw ∧ ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2 := by
  -- ## 1. the size bound of the scheme's right-hand side at the ball profiles
  obtain ⟨L, hLpos, hLsize⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.ConjOneSq (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs) (R := R)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
  refine ⟨L, hLpos, ?_⟩
  -- ## 2. `EpsMem`/`EpsSq` of `Feps` at every slice of the curve
  have hG : ∀ σ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ)) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ)) ≤ L := by
    intro σ hσ
    have hb := hX σ hσ
    obtain ⟨hm, hbd⟩ := hLsize (slice g σ) hb.smoothOpen hb.mem hb.sq_le hb.classC hb.ball
    rw [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 (slice g σ)] at hm hbd
    exact ⟨hm, hbd⟩
  -- ## 3. joint a.e. strong measurability of the weighted curve on the horizon
  have hmeas : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc 0 δ → b ∈ Set.Icc 0 δ →
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g p.1) p.2.1 p.2.2
            * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          Work.FTS.StrongEps.EpsLocalPStar.DomM) := by
    intro a b hab ha hb
    refine aesm_of_continuousOn_box hab ?_
    have hmem : Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad
        ⊆ Set.Ioo 0 δ ×ˢ Work.FTS.StrongEps.Quad :=
      fun p hp => ⟨⟨lt_of_le_of_lt ha.1 hp.1.1, lt_of_lt_of_le hp.1.2 hb.2⟩, hp.2⟩
    have hcont1 : ContinuousOn
        (fun p : ℝ × (ℝ × ℝ) =>
          Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1 p.2.1 p.2.2)
        (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad) :=
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.continuousOn_epsRHSP_joint_Ioo hreg hsol).mono hmem
    have hcont2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
        (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad) :=
      (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α).comp (by fun_prop) (fun p hp => hp.2)
    refine (hcont1.mul hcont2).congr (fun p hp => ?_)
    show Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1 p.2.1 p.2.2
        * Work.FTS.StrongEps.epsW α p.2.1 p.2.2
      = Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g p.1) p.2.1 p.2.2
        * Work.FTS.StrongEps.epsW α p.2.1 p.2.2
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E]
  -- ## 4. the bound on each orientation of the interval
  have hcase : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc 0 δ → b ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ => slice g a z θ - slice g b z θ)
        ≤ L * (a - b) ^ 2 := by
    intro a b hab ha hb
    have hbd : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        Work.FTS.StrongEps.EpsLocalPStar.epsL2 α
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ)) ≤ ENNReal.ofReal L := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with σ hσ
      have hσ' : σ ∈ Set.Icc 0 δ := by
        rw [Set.uIoc_of_le hab] at hσ
        exact ⟨le_trans ha.1 hσ.1.le, le_trans hσ.2 hb.2⟩
      exact Work.FTS.StrongEps.EpsLocalPStar.epsL2_le_ofReal_of_mem (hG σ hσ').1 (hG σ hσ').2
    obtain ⟨-, hsq⟩ := Work.FTS.EpsEngine.EpsSq_intervalIntegral_le_gen (α := α) (a := a) (b := b)
      (B := L) hab hLpos.le (hmeas a b hab ha hb) hbd
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
    have haeeq : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
        (fun z θ => slice g b z θ - slice g a z θ) p.1 p.2
          = (fun z θ => ∫ σ in a..b,
              Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) p.1 p.2 := by
      filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp
      have hvol := volterra_interval_of_regP hδ hsol hreg p.1 p.2 a b hp.1 ⟨hp.2.1, hp.2.2⟩ ha hb hab
      simp only [Work.FTS.Galerkin.slice_apply]
      exact hvol
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_congr_ae
      (f := fun z θ => slice g b z θ - slice g a z θ)
      (g := fun z θ => ∫ σ in a..b, Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) haeeq]
    calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => ∫ σ in a..b, Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ)
        ≤ (b - a) * ((b - a) * L) := hsq
      _ = L * (a - b) ^ 2 := by ring
  -- ## 5. both orientations
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hcase s t hst hs ht
  · have h := hcase t s hts ht hs
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
    calc Work.FTS.StrongEps.EpsSq α (fun z θ => slice g t z θ - slice g s z θ)
        ≤ L * (t - s) ^ 2 := h
      _ = L * (s - t) ^ 2 := by ring

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
