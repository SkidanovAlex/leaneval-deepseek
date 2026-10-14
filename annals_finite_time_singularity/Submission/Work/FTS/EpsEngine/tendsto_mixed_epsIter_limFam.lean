import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EpsEngine.exists_epsPsi_limit
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_E_of_EllLimOK3
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_val
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.Vz7Eslot
import Submission.Work.FTS_RegExport.r1Block.regExport_hVop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity on the quadrant from `logPull`-continuity -/

/-- `logPull`-continuity of a profile gives continuity of the profile on the open quadrant (where
the log-coordinate map is a homeomorphism onto `ℝ²`). -/
theorem continuousOn_uncurry_of_continuous_logPull {f : Fn}
    (h : Continuous (Work.FTS.StrongEps.logPull f)) :
    ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) Work.FTS.StrongEps.Quad := by
  have hcomp : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.logPull f
      (Work.FTS.StrongEps.sOf q.1, Work.FTS.StrongEps.zetaOf q.2)) Work.FTS.StrongEps.Quad :=
    h.comp_continuousOn (Work.FTS.StrongEps.contDiffOn_logMap 0).continuousOn
  refine hcomp.congr (fun q hq => ?_)
  simp only [Work.FTS.StrongEps.logPull, Work.FTS.StrongEps.sOf, Work.FTS.StrongEps.zetaOf]
  rw [Real.exp_log hq.1,
    Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hq.2.1 hq.2.2),
    Real.arctan_tan (by linarith [Real.pi_pos, hq.2.1]) hq.2.2]

/-! ## The mixed operator respects equality on an open set -/

/-- **Congruence of the mixed slots on an open set**: the iterated operators are `deriv`-based, so
two profiles that agree on an open set have the same slot at every point of it. -/
theorem mixed_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {j i : ℕ} {z θ : ℝ}
    (hzθ : (z, θ) ∈ V) :
    Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i g z θ := by
  have h1 := Work.FTS.TransportS.DthIter_congrOn hV h i
  have h2 := Work.FTS.TransportS.DzIter_congrOn hV h1 j
  exact h2 hzθ

/-! ## The value-only routed slot bound for `J_ε` -/

/-- **The routed slot bound for the mollified profile, from *values* of the profile alone.**  For a
profile whose `logPull` is merely locally integrable (no smoothness), every mixed slot of `J_ε f`
is bounded by the `L¹`-mass of the routed kernel times the sup of `f` on the shifted region. -/
theorem abs_mixed_Jeps_le_val_locInt {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε B : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : MeasureTheory.LocallyIntegrable (Work.FTS.StrongEps.logPull f) MeasureTheory.volume)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hF : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
      |f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ B)
    (j i : ℕ) :
    |Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ|
      ≤ (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i * B := by
  rw [mixed_Jeps_kernel_locInt hρ hε hf hz hθ j i, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ i)]
  have hKcont : Continuous (Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) j i) :=
    (Work.FTS.StrongEps.Kd_smooth _ (fun n => Work.FTS.StrongEps.Jker_smooth hρ ε) j i 1).continuous
  have hKint : Integrable (Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) j i) :=
    hKcont.integrable_of_hasCompactSupport
      (Work.FTS.StrongEps.Kd_compact _ (Work.FTS.StrongEps.Jker_hasCompactSupport hρ.moll hε) j i)
  have hbound := Work.FTS.StrongEps.abs_integral_mul_le_of_support
    (K := Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) j i) hKint
    (fun p hp => Work.FTS.StrongEps.Kd_Jker_eq_zero_of_notMem hρ.moll hε j i p hp)
    (F := fun p : ℝ × ℝ =>
      f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) hF
  calc (2 : ℝ) ^ i * |∫ p : ℝ × ℝ, Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) j i p
        * f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
      ≤ (2 : ℝ) ^ i * ((∫ p : ℝ × ℝ,
          |Work.FTS.StrongEps.Kd (Work.FTS.StrongEps.Jker ρ ε) j i p|) * B) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i * B := by
        rw [Work.FTS.StrongEps.Kmass]; ring

/-! ## Convergence of the slots of `J_ε` along a geometrically convergent sequence -/

/-- **`J_ε` of a geometrically convergent sequence of profiles**: the mixed slots of the mollified
profiles converge to the slots of the mollified limit, at the geometric rate of the profiles.  The
proof routes the derivatives onto the compactly supported kernel, so only the *values* of the
profiles enter. -/
theorem tendsto_mixed_Jeps_of_geometric {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {Ψ : ℕ → Fn} {ΨL : Fn}
    (hcont : ∀ n : ℕ, Continuous (Work.FTS.StrongEps.logPull (Ψ n)))
    (hcontL : Continuous (Work.FTS.StrongEps.logPull ΨL))
    {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hBnd : ∀ (n : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Ψ n z θ - ΨL z θ| ≤ C * r ^ n)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j i : ℕ} (hji : j + i ≤ 4) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ)) := by
  have hsmL : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε ΨL))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hcontL.locallyIntegrable 4
  -- the slot of the difference of the two mollified profiles is the slot of the mollified
  -- difference
  have hmain : ∀ n : ℕ,
      Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ
        - Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ
      = Work.Spaces.mixed j i
          (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => Ψ n z θ - ΨL z θ)) z θ := by
    intro n
    have hsmn : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε (hcont n).locallyIntegrable 4
    have h1 : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ
        - Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ
        = Work.Spaces.mixed j i (fun z θ => Work.FTS.StrongEps.Jeps ρ ε (Ψ n) z θ
            - Work.FTS.StrongEps.Jeps ρ ε ΨL z θ) z θ :=
      (Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := j) (i := i)
        (A := fun z θ => Work.FTS.StrongEps.Jeps ρ ε (Ψ n) z θ)
        (B := fun z θ => Work.FTS.StrongEps.Jeps ρ ε ΨL z θ)
        hji hz hθ hsmn hsmL).symm
    rw [h1, mixed_congrOn Work.FTS.EllipticEst.isOpen_Q0 (V := Work.FTS.EllipticEst.Q0) ?_
      (z := z) (θ := θ) (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
    intro p hp
    have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
    show Work.FTS.StrongEps.Jeps ρ ε (Ψ n) p.1 p.2 - Work.FTS.StrongEps.Jeps ρ ε ΨL p.1 p.2
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => Ψ n z θ - ΨL z θ) p.1 p.2
    rw [Work.FTS.StrongEps.E5Aux.Jeps_sub_Jeps_eq_integral hρ.moll hp'.1 ⟨hp'.2.1, hp'.2.2⟩ hε
          (continuousOn_uncurry_of_continuous_logPull (hcont n))
          (continuousOn_uncurry_of_continuous_logPull hcontL),
      Work.FTS.StrongEps.Jeps_eq_integral ρ ε _ hp'.1 ⟨hp'.2.1, hp'.2.2⟩]
  -- the geometric majorant
  have hgeo : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hz0 : Filter.Tendsto (fun n : ℕ =>
      (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i * (C * r ^ n)) Filter.atTop (nhds 0) := by
    have h := (hgeo.const_mul C).const_mul ((2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i)
    simpa using h
  have hb : ∀ n : ℕ, |Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ
      - Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ|
      ≤ (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i * (C * r ^ n) := by
    intro n
    rw [hmain n]
    refine abs_mixed_Jeps_le_val_locInt hρ hε ?_ hz hθ (fun p hp1 hp2 => ?_) j i
    · have hc : Continuous (Work.FTS.StrongEps.logPull (fun z θ => Ψ n z θ - ΨL z θ)) := by
        have hfun : Work.FTS.StrongEps.logPull (fun z θ => Ψ n z θ - ΨL z θ)
            = fun x : ℝ × ℝ => Work.FTS.StrongEps.logPull (Ψ n) x
                - Work.FTS.StrongEps.logPull ΨL x := by
          funext x
          simp only [Work.FTS.StrongEps.logPull, Pi.sub_apply]
        rw [hfun]
        exact (hcont n).sub hcontL
      exact hc.locallyIntegrable
    · exact hBnd n _ _ (Work.FTS.StrongEps.zShift_pos hz)
        (Work.FTS.StrongEps.thShift_mem hθ)
  have hzero : Filter.Tendsto (fun n : ℕ =>
      |Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ
        - Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hb hz0
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hzero)

/-! ## The target -/

theorem tendsto_mixed_epsIter_limFam {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R C₀
        (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) s z θ
          - Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) s z θ
          - Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ m) s z θ)
        ≤ q ^ n)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n s) z θ
          - Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n s
            * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun N : ℕ =>
          Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ N) s z θ)
        Filter.atTop
        (nhds (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    ∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Filter.Tendsto (fun N : ℕ =>
          Work.Spaces.mixed j i
            (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ N) τ) z θ)
        Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) τ) z θ)) := by
  intro j i hji z θ hz hθ
  -- ## the limit of the stream-function iterates
  obtain ⟨C, r, PsiL, hC0, hr0, hr1, hcontL, hcontIter, hBnd, _hTend⟩ :=
    exists_epsPsi_limit (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀) (δ := δ)
      hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hτ
  -- ## values: `J_ε Ψ_n → J_ε PsiL` on the quadrant
  have hJepsConv : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jeps ρ ε
          (epsPsi α ρ ε Φs E h₀ n τ) z θ) Filter.atTop
        (nhds (Work.FTS.StrongEps.Jeps ρ ε PsiL z θ)) := by
    intro z θ hz hθ
    have hb : Filter.Tendsto (fun n : ℕ => C * r ^ n) Filter.atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
      simpa using h
    have hsq : Filter.Tendsto (fun n : ℕ =>
        |Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
          - Work.FTS.StrongEps.Jeps ρ ε PsiL z θ|) Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun n => abs_nonneg _) (fun n => ?_)
      exact abs_Jeps_sub_le_of_logPull_le hρ hε (mul_nonneg hC0 (pow_nonneg hr0 n))
        (hcontIter n) hcontL
        (fun x => hBnd n _ _ (Real.exp_pos x.1)
          ⟨(Real.arctan_pos).mpr (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩) hz hθ
    exact (tendsto_iff_norm_sub_tendsto_zero).mpr
      (by simpa only [Real.norm_eq_abs] using hsq)
  -- ## the coefficient limit and the identity defining the limit family on the quadrant
  obtain ⟨cLim, hcLim, hIdent⟩ :=
    epsC_tendsto_and_limIdent (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
      (Lw := Lw) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀) (δ := δ)
      hρ hε hmoll hconv hτ hJepsConv
  -- ## the slot of one iterate, in terms of the pieces
  have hslot : ∀ N : ℕ, Work.Spaces.mixed j i
        (slice (epsIter α ρ ε Φs E h₀ (N + 1)) τ) z θ
      = Work.Spaces.mixed j i h₀ z θ
        + Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε
            (epsPsi α ρ ε Φs E h₀ N τ)) z θ
        - epsC α ρ ε Φs E h₀ N τ * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
    intro N
    have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
    have hEqOn : Set.EqOn (Function.uncurry (slice (epsIter α ρ ε Φs E h₀ (N + 1)) τ))
        (Function.uncurry (fun z θ => h₀ z θ
          + Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E h₀ N τ) z θ
          - epsC α ρ ε Φs E h₀ N τ * Work.FTS.StrongEps.bump z θ))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact hmoll N τ hτ p.1 p.2 hp'.1 ⟨hp'.2.1, hp'.2.2⟩
    rw [mixed_congrOn Work.FTS.EllipticEst.isOpen_Q0 hEqOn hzθ]
    have hAh : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => h₀ z θ
        + Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E h₀ N τ) z θ))
        Work.FTS.EllipticEst.Q0 :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp h0 4).add
        (Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε (hcontIter N).locallyIntegrable 4)
    have hBc : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
        epsC α ρ ε Φs E h₀ N τ * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall
        Work.FTS.StrongEps.bump).mp Work.FTS.StrongEps.smoothOpen_bump 4)
    rw [Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := j) (i := i)
      (A := fun z θ => h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
        (epsPsi α ρ ε Φs E h₀ N τ) z θ)
      (B := fun z θ => epsC α ρ ε Φs E h₀ N τ * Work.FTS.StrongEps.bump z θ)
      hji hz hθ hAh hBc]
    rw [Work.FTS.StrongEps.mixed_add (j := j) (i := i)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp h0)
      (fun n => Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε
        (hcontIter N).locallyIntegrable n) hz hθ]
    rw [Work.FTS.StrongEps.mixed_const_mul (j := j) (i := i) (epsC α ρ ε Φs E h₀ N τ)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Work.FTS.StrongEps.bump).mp
        Work.FTS.StrongEps.smoothOpen_bump) hz hθ]
  -- ## the limit of the pieces
  have hmol : Filter.Tendsto (fun N : ℕ => Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E h₀ N τ)) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε PsiL) z θ)) :=
    tendsto_mixed_Jeps_of_geometric (ρ := ρ) hρ hε hcontIter hcontL hC0 hr0 hr1 hBnd hz hθ hji
  have hcs : Filter.Tendsto (fun N : ℕ => epsC α ρ ε Φs E h₀ N τ
      * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ) Filter.atTop
      (nhds (cLim * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ)) :=
    hcLim.mul_const _
  have hlim : Filter.Tendsto (fun N : ℕ => Work.Spaces.mixed j i
        (slice (epsIter α ρ ε Φs E h₀ (N + 1)) τ) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed j i h₀ z θ
        + Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε PsiL) z θ
        - cLim * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ)) := by
    refine ((tendsto_const_nhds.add hmol).sub hcs).congr' ?_
    exact Eventually.of_forall fun N => (hslot N).symm
  -- ## the slot of the limit family, computed from the identity on the quadrant
  have hfinal : Work.Spaces.mixed j i (slice (epsLim α ρ ε Φs E h₀) τ) z θ
      = Work.Spaces.mixed j i h₀ z θ
        + Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε PsiL) z θ
        - cLim * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
    have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
    have hEqOn : Set.EqOn (Function.uncurry (slice (epsLim α ρ ε Φs E h₀) τ))
        (Function.uncurry (fun z θ => h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε PsiL z θ
          - cLim * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact hIdent p.1 p.2 hp'.1 ⟨hp'.2.1, hp'.2.2⟩
    rw [mixed_congrOn Work.FTS.EllipticEst.isOpen_Q0 hEqOn hzθ]
    have hAh : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
        h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε PsiL z θ)) Work.FTS.EllipticEst.Q0 :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp h0 4).add
        (Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hcontL.locallyIntegrable 4)
    have hBc : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
        cLim * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall
        Work.FTS.StrongEps.bump).mp Work.FTS.StrongEps.smoothOpen_bump 4)
    rw [Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := j) (i := i)
      (A := fun z θ => h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε PsiL z θ)
      (B := fun z θ => cLim * Work.FTS.StrongEps.bump z θ) hji hz hθ hAh hBc]
    rw [Work.FTS.StrongEps.mixed_add (j := j) (i := i)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp h0)
      (fun n => Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hcontL.locallyIntegrable n) hz hθ]
    rw [Work.FTS.StrongEps.mixed_const_mul (j := j) (i := i) cLim
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Work.FTS.StrongEps.bump).mp
        Work.FTS.StrongEps.smoothOpen_bump) hz hθ]
  rw [hfinal]
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hlim

end Work.FTS.EpsEngine
