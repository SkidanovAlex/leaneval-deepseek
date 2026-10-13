import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.RegQoClosure
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SqWeakAux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.EpsRLX.XDataClean
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min

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
