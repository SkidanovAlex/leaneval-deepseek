import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPSmall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.FTS.StrongEps.HkSq_Jeps_step_le
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Auxiliary facts about the profile maps

Four elementary tools that the sup-norm estimate of the scheme's right-hand side needs:

* `pointwise_le_HkNorm` — the trace-free `ℋ⁴ → L^∞` trade-off with an *explicit* constant
  (`v2_hkMem_pointwise_min` at the slot `(b,a) = (0,0)`, the harmless `min z 1`-factor being
  dropped);
* `smoothOpen_Pz`, `hkMem_Pz` — the projection `P₀ f = f − (L₁₂ f 0/L₁₂ bump 0)•bump` preserves
  smoothness on the open quadrant and `ℋᵏ`-membership;
* `Wp_sub_eq_mem` — the additivity `W_ε u − W_ε v = W_ε (u − v)` of the projected mollifier
  (`EpsRLX.Wp_sub_eq`) under the *weaker* regularity `SmoothOpen ∧ HkMem α 4` that the difference
  of two right-hand sides supplies (`DeltaXnBound` only gives `HkMem α 4`). -/

/-- **The trace-free `ℋ⁴ → L^∞` trade-off**, with an explicit (universal) constant.  For a datum
which is `C^∞` on the open quadrant and honestly in `ℋ⁴`, every value on the open quadrant is
bounded by a universal multiple of `|f|_{ℋ⁴}`. -/
theorem pointwise_le_HkNorm {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 4 f → ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ C * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C, hC0, hbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  refine ⟨C, hC0, ?_⟩
  intro f hf hm z θ hz hθ0 hθ1
  have h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf 4
  have h := hbd f h4 hm 0 0 (by norm_num) z θ hz hθ0 hθ1
  have h' : |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.pthIter_zero] using h
  calc |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := h'
    _ ≤ C * 1 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right z 1) hC0)
          (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = C * Work.Spaces.HkNorm α 4 f := by ring

/-- The projection `P₀` preserves smoothness on the open quadrant. -/
theorem smoothOpen_Pz {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Pz f) := by
  have heq : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    ring
  rw [heq]
  exact Work.FTS.NonlinRows.smoothOpen_add hf
    (Work.FTS.NonlinRows.smoothOpen_const_mul _ Work.FTS.StrongEps.smoothOpen_bump)

/-- The projection `P₀` preserves `ℋᵏ`-membership. -/
theorem hkMem_Pz {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Pz f) := by
  have heq : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    ring
  rw [heq]
  exact Work.FTS.EllipticEst.HkMem_add_open hf
    (Work.FTS.NonlinRows.smoothOpen_const_mul _ Work.FTS.StrongEps.smoothOpen_bump) hm
    (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _
      (Work.FTS.StrongEps.PZeroAux.hkMem_bump α k))

/-- **Additivity of the projected mollifier `W_ε` at `ℋ⁴`-regularity**: the difference of the two
projected-mollified profiles is the projected-mollified profile of the difference.  This is
`EpsRLX.Wp_sub_eq` with the `ℋ⁶`-hypotheses weakened to `ℋ⁴` (only the latter is available for the
difference of two right-hand sides). -/
theorem Wp_sub_eq_mem {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {u v : Fn}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α 4 u) (hmv : Work.Spaces.HkMem α 4 v) :
    Work.FTS.StrongEps.EpsRLX.Wp ρ ε u - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε (fun z θ => u z θ - v z θ) := by
  have huc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hu
  have hvc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hv
  have hsmu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε huc
  have hsmv : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hvc
  have hmemu : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε huc hmu
  have hmemv : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hvc hmv
  have hL : Work.Construction.L12
        (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ) 0
      = Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hsmu hsmv hmemu hmemv 0
      (Set.mem_Ici.mpr le_rfl)
  have hJ : Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hu hv
  show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
      - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ))
  calc Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.StrongEps.Pz
          (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
            - Work.FTS.StrongEps.Jeps ρ ε v z θ) :=
        Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL
    _ = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ)) := by
        rw [show (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
              - Work.FTS.StrongEps.Jeps ρ ε v z θ)
            = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) from hJ]

theorem profRHS_sub_sup_le {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ v →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))) ∧
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
          - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- ## the constants of the library
  obtain ⟨K₁, hK₁pos, hK₁⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CT, hCTpos, hCT⟩ := TraceToEpsMem
  obtain ⟨CD, hCDpos, hCD⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaData (α := α) (C₀ := C₀) (B := B) (ε := ε) hρ hα ⟨hε, hε1⟩
  obtain ⟨Cw, hCwpos, hCw⟩ := Work.FTS.StrongEps.EpsRLX.WpUniformBound (ρ := ρ) hρ
  obtain ⟨CW, -, hCW⟩ := Work.FTS.StrongEps.EpsRLX.WpSixBound (ρ := ρ) hρ
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨Cpt, hCpt0, hCpt⟩ := pointwise_le_HkNorm (α := α) hα0 hα1
  -- ## the uniform `ℋ⁶`-enlargement of the size parameter
  set BS : ℝ := max B (CW / (Work.Spaces.gam α - 1) * (CW / ε) ^ 6 * B) with hBSdef
  have hBS0 : 0 ≤ BS := by rw [hBSdef]; exact le_trans hB (le_max_left _ _)
  have hWp6 : ∀ {u : Fn}, Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS := fun hd =>
    le_trans (hCW α hα ε ⟨hε, hε1⟩ hB hd) (by rw [hBSdef]; exact le_max_right _ _)
  obtain ⟨RX, hRXpos, hRX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := BS)
      hα hEll hstar hml hBS0
  -- ## the uniform profile factor
  set MW : ℝ := Cw / (Work.Spaces.gam α - 1) * (Cw / ε) ^ 6 * B with hMWdef
  have hMW0 : 0 ≤ MW := by
    rw [hMWdef]
    exact mul_nonneg (mul_nonneg (div_nonneg hCwpos.le hγ.le)
      (pow_nonneg (by positivity) 6)) hB
  set M₀ : ℝ := 1 + 2 * MW with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  -- ## the two final constants
  set Q : ℝ := Real.sqrt (CD * (CD / ε) ^ 12) with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set T : ℝ := Real.sqrt (CJ * (CJ / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2)) with hTdef
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  refine ⟨max 1 (max (Cpt * K₁ * M₀ ^ 2 * Q) (Cpt * T * K₁ * M₀ ^ 2 * Q)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro u v hdu hdv
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
      (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hdu.cls hdv.cls hdu.xn hdv.xn
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
      (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (E := E) hα hdu.cls hdv.cls
      ((hEll (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) hdu.cls).1)
      ((hEll (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hdv.cls).1) hstar
    obtain ⟨hΔepsMem, hΔepsSq⟩ := hCT α hα Δ hΔsm hΔmem1
      (fun z hz => by simpa only [hΦudef, hΦvdef] using ht1 z hz)
      (fun z hz => by simpa only [hΦudef, hΦvdef] using ht2 z hz)
    have hΔHk : Work.Spaces.HkSq α 1 Δ ≤ (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by
      refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hΔmem4) ?_
      rw [show Work.FTS.Nonlin.Xn α Δ = Work.Spaces.HkNorm α 4 Δ from rfl, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 Δ)]
    -- ## the per-profile regularity of the two right-hand sides
    have hXu := hRX (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) hdu.cls hdu.xn (hWp6 hdu)
    have hXv := hRX (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hdv.cls hdv.xn (hWp6 hdv)
    have hsmΦu : Work.FTS.EllipticEst.SmoothOpen Φu := by rw [hΦudef]; exact hXu.1
    have hmem4Φu : Work.Spaces.HkMem α 4 Φu := by rw [hΦudef]; exact hXu.2.1
    have hsmΦv : Work.FTS.EllipticEst.SmoothOpen Φv := by rw [hΦvdef]; exact hXv.1
    have hmem4Φv : Work.Spaces.HkMem α 4 Φv := by rw [hΦvdef]; exact hXv.2.1
    -- ## the three size bounds
    have hDd : (Work.Spaces.HkNorm α 5 d) ^ 2
        ≤ CD * (CD / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
      rw [hddef]
      exact (hCD hdu hdv).2.2.2
    have hWu : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ MW := by
      rw [hMWdef]
      exact hCw α hα ε ⟨hε, hε1⟩ hB hdu
    have hWv : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ MW := by
      rw [hMWdef]
      exact hCw α hα ε ⟨hε, hε1⟩ hB hdv
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
    have hQbd : Work.Spaces.HkNorm α 5 d
        ≤ Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
      have hd0 : 0 ≤ Work.Spaces.HkNorm α 5 d := Work.Spaces.HkNorm_nonneg α 5 d
      have hfac0 : 0 ≤ CD * (CD / ε) ^ 12 :=
        mul_nonneg hCDpos.le (pow_nonneg (div_nonneg hCDpos.le hε.le) 12)
      calc Work.Spaces.HkNorm α 5 d
          = Real.sqrt ((Work.Spaces.HkNorm α 5 d) ^ 2) := (Real.sqrt_sq hd0).symm
        _ ≤ Real.sqrt (CD * (CD / ε) ^ 12
              * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := Real.sqrt_le_sqrt hDd
        _ = Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
            rw [hQdef, Real.sqrt_mul hfac0]
    -- ## the two constants of the conjuncts, and the first conjunct
    refine ⟨?_, ?_⟩
    · intro z θ hz hθ0 hθ1
      have hgoal : |Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
            (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
            (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ| = |Δ z θ| := by
        simp only [hΔdef, hΦudef, hΦvdef]
      rw [hgoal]
      have h1 : |Δ z θ| ≤ (Cpt * K₁ * M₀ ^ 2 * Q)
          * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
        calc |Δ z θ| ≤ Cpt * Work.Spaces.HkNorm α 4 Δ := hCpt hΔsm hΔmem4 hz hθ0 hθ1
          _ ≤ Cpt * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) :=
              mul_le_mul_of_nonneg_left hXnΔ hCpt0
          _ ≤ Cpt * (K₁ * M₀ ^ 2
                * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQbd hKM) hCpt0
          _ = (Cpt * K₁ * M₀ ^ 2 * Q)
                * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by ring
      exact le_trans h1 (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left _ _) (le_max_right _ _)) (Real.sqrt_nonneg _))
    -- ## the second conjunct
    · intro z θ hz hθ0 hθ1
      have hIdent : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v
          = Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ := by
        have h1 : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
              - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v
            = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu)
              - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) := by
          rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E 0 u,
            Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E 0 v,
            hΦudef, hΦvdef]
          rfl
        rw [h1]
        exact Wp_sub_eq_mem hα hρ hε hsmΦu hsmΦv hmem4Φu hmem4Φv
      have hsmJΔ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
        Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm)
      have hsmWpΔ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
        smoothOpen_Pz hsmJΔ
      have hmemWpΔ : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
        hkMem_Pz hsmJΔ (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm) hΔmem4)
      have hWpSq : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
          ≤ CJ * (CJ / ε) ^ 8 * Work.FTS.StrongEps.EpsSq α Δ :=
        hCJ α hα ε hε hε1 4 (by norm_num) Δ hΔsm hΔepsMem
      have hTbd : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
          ≤ T * Work.Spaces.HkNorm α 4 Δ := by
        have hx0 : 0 ≤ Work.Spaces.HkNorm α 4 Δ := Work.Spaces.HkNorm_nonneg α 4 Δ
        have hc1 : 0 ≤ CJ * (CJ / ε) ^ 8 :=
          mul_nonneg hCJpos.le (pow_nonneg (div_nonneg hCJpos.le hε.le) 8)
        have hc2 : 0 ≤ CT / (Work.Spaces.gam α - 1) ^ 2 := div_nonneg hCTpos.le (sq_nonneg _)
        have hprod0 : 0 ≤ CJ * (CJ / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2) :=
          mul_nonneg hc1 hc2
        have hA2 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
            ≤ T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2 := by
          refine le_trans hWpSq ?_
          calc CJ * (CJ / ε) ^ 8 * Work.FTS.StrongEps.EpsSq α Δ
              ≤ CJ * (CJ / ε) ^ 8
                  * (CT / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 Δ) :=
                mul_le_mul_of_nonneg_left hΔepsSq hc1
            _ ≤ CJ * (CJ / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2
                  * (Work.Spaces.HkNorm α 4 Δ) ^ 2) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔHk hc2) hc1
            _ = T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2 := by
                rw [hTdef, Real.sq_sqrt hprod0]; ring
        rw [Work.Spaces.HkNorm]
        calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ))
            ≤ Real.sqrt (T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2) := Real.sqrt_le_sqrt hA2
          _ = T * Work.Spaces.HkNorm α 4 Δ := by
              rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0, Real.sqrt_sq hx0]
      have hpt1 : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ
          = Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ := by
        have := congrFun (congrFun hIdent z) θ
        simpa only [Pi.sub_apply] using this
      rw [hpt1]
      have hfinal : |Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ|
          ≤ (Cpt * T * K₁ * M₀ ^ 2 * Q)
            * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
        calc |Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ|
            ≤ Cpt * Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
              hCpt hsmWpΔ hmemWpΔ hz hθ0 hθ1
          _ ≤ Cpt * (T * Work.Spaces.HkNorm α 4 Δ) :=
              mul_le_mul_of_nonneg_left hTbd hCpt0
          _ ≤ Cpt * (T * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXnΔ hT0) hCpt0
          _ ≤ Cpt * (T * (K₁ * M₀ ^ 2
                * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQbd hKM) hT0) hCpt0
          _ = (Cpt * T * K₁ * M₀ ^ 2 * Q)
                * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by ring
      exact le_trans hfinal (mul_le_mul_of_nonneg_right
        (le_trans (le_max_right _ _) (le_max_right _ _)) (Real.sqrt_nonneg _))

end Work.FTS.StrongEps.EpsLocalPStar
