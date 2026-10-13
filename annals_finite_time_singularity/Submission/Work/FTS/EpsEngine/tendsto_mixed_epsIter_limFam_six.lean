import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam
import Submission.Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six

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

/-!
# The mixed slots of the Picard iterates of the local step, order `6`

This file contains the order-`6` counterpart of `tendsto_mixed_epsIter_limFam`
(`Submission/Work/FTS/EpsEngine/tendsto_mixed_epsIter_limFam.lean`): the mixed slots
`D_z^j D_θ^i`, `i + j ≤ 6`, of the slices of the Picard iterates converge, at every point of the
open quadrant, to the corresponding slots of the slices of the limit family.

The order-`4` proof uses exactly four inputs, all of which are available at order `6`:

* the *value-routed* slot bound for the mollifier `J_ε` (`abs_mixed_Jeps_le_val_locInt`, stated for
  arbitrary `j i`) and the congruence of the slots on open sets (`mixed_congrOn`, arbitrary `j i`) —
  both from the imported file, hence reused verbatim;
* the *subtraction rule* for the mixed slots at finite regularity, which is where the order
  enters: `mixed_sub_of_contDiffOn_four` at order `4` is replaced by
  `Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six` at order `6`;
* additivity (`mixed_add`, order-free, `C^∞` data) and scalar homogeneity (`mixed_const_mul`,
  order-free, unconditional);
* `Jeps_contDiffOn`, which is `∀ n` and so is used at `n = 6`.

Besides the order, nothing changes; the two limit statements used, `exists_epsPsi_limit` and
`epsC_tendsto_and_limIdent`, are order-free.
-/

/-- **`J_ε` of a geometrically convergent sequence of profiles, order `6`**: the mixed slots
`D_z^j D_θ^i`, `i + j ≤ 6`, of the mollified profiles converge to the slots of the mollified
limit, at the geometric rate of the profiles.  The proof routes the derivatives onto the
compactly supported kernel, so only the *values* of the profiles enter. -/
theorem tendsto_mixed_Jeps_of_geometric_six {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {Ψ : ℕ → Fn} {ΨL : Fn}
    (hcont : ∀ n : ℕ, Continuous (Work.FTS.StrongEps.logPull (Ψ n)))
    (hcontL : Continuous (Work.FTS.StrongEps.logPull ΨL))
    {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hBnd : ∀ (n : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Ψ n z θ - ΨL z θ| ≤ C * r ^ n)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j i : ℕ} (hji : j + i ≤ 6) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ)) := by
  have hsmL : ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε ΨL))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hcontL.locallyIntegrable 6
  -- the slot of the difference of the two mollified profiles is the slot of the mollified
  -- difference
  have hmain : ∀ n : ℕ,
      Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ
        - Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ
      = Work.Spaces.mixed j i
          (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => Ψ n z θ - ΨL z θ)) z θ := by
    intro n
    have hsmn : ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε (hcont n).locallyIntegrable 6
    have h1 : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε (Ψ n)) z θ
        - Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε ΨL) z θ
        = Work.Spaces.mixed j i (fun z θ => Work.FTS.StrongEps.Jeps ρ ε (Ψ n) z θ
            - Work.FTS.StrongEps.Jeps ρ ε ΨL z θ) z θ :=
      (Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six (j := j) (i := i)
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

theorem tendsto_mixed_epsIter_limFam_six {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
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
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n s) z θ
          - Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n s
            * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ =>
          Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ N) s z θ)
        Filter.atTop
        (nhds (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    ∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
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
  have hJepsConv : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
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
    have hAh : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => h₀ z θ
        + Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E h₀ N τ) z θ))
        Work.FTS.EllipticEst.Q0 :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp h0 6).add
        (Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε (hcontIter N).locallyIntegrable 6)
    have hBc : ContDiffOn ℝ 6 (Function.uncurry (fun z θ =>
        epsC α ρ ε Φs E h₀ N τ * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall
        Work.FTS.StrongEps.bump).mp Work.FTS.StrongEps.smoothOpen_bump 6)
    rw [Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six (j := j) (i := i)
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
    tendsto_mixed_Jeps_of_geometric_six (ρ := ρ) hρ hε hcontIter hcontL hC0 hr0 hr1 hBnd hz hθ
      hji
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
    have hAh : ContDiffOn ℝ 6 (Function.uncurry (fun z θ =>
        h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε PsiL z θ)) Work.FTS.EllipticEst.Q0 :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp h0 6).add
        (Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε hcontL.locallyIntegrable 6)
    have hBc : ContDiffOn ℝ 6 (Function.uncurry (fun z θ =>
        cLim * Work.FTS.StrongEps.bump z θ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall
        Work.FTS.StrongEps.bump).mp Work.FTS.StrongEps.smoothOpen_bump 6)
    rw [Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six (j := j) (i := i)
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
