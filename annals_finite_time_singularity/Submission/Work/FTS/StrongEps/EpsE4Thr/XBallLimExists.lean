/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XBallLimExists.lean` — the **limit clause** of the
# `X`-ball residual bundle of the local step

`EpsE4Thr/XStepInvariant` runs the Volterra–Picard engine at the `X`-ball
`XBall α ρ ε R C₀ u = SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R ∧ ClassC α (Pz (J_ε u))
∧ Xn α (Pz (J_ε u)) ≤ C₀ α²`.  This file proves the clause at the **limit family** of the Picard
iteration, for **any** radius `R` and horizon `δ` with the contraction `δ √L < 1`, from the
iterate-wise clause only:

* `hiter` (every Picard slice `slice (iter (Feps α ρ ε Φs E) h₀ (n+1)) τ` lies in
  `XBall α ρ ε R (2 C₀)`) ⟹ every limit slice `slice (limFam (Feps α ρ ε Φs E) h₀) τ` lies in
  `XBall α ρ ε R (2 C₀)`, **and** is `ℋ⁶`-honest.

## Route (all in-tree, `sorry`-free)

1. **The datum is in the ball** (`hP₀`) and the engine's gates `hcontP`/`hzeroP` come from
   `continuousOn_Feps_of_XBall`.
2. **A-priori bounds** `iter_bounds_v4` (`q = δ²L`, `r = √q`, `q < 1` from `δ√L < 1`) give the
   ball invariant `hP` along the iterates, the geometric bounds `hB0`/`hBK`, the pointwise
   increment bound `hwpt`; `iter_cont_meas` gives the time-continuity, and
   `EpsSq_iter_sub_sq_le`/`epsPair_of_iter_bounds` the time-Lipschitz and geometric pair bounds.
   `tendsto_slice_iter_limFam` gives the pointwise convergence `hconv`, and
   `slice_iter_succ_mollForm` the mollified form `hmoll`.
3. **The four clauses at the limit**: `SmoothOpen` by
   `smoothOpen_limFam_slice_of_iter_bounds`; `EpsMem`/`EpsSq ≤ R` by `limFam_EpsMem`;
   `ClassC α (Pz (J_ε ·))` by `ThetaFromEps.classC_Pz_Jeps_of_epsMem` (with the `fsm` input from
   `XBallLimAux.FstarPzJepsSmooth`, see the trap below); the ball clause by
   `Xn_PzJeps_limFam_le_of_tail` fed with the geometric tail `EpsSq_iter_limFam_le` and the `ℋ⁴`
   honesty `HkMem_iter_feps`/`HkMem_epsLim_feps`.
4. **`ℋ⁶`-honesty of the limit slice**: the level-`6` (H4) chain — `HkMem_iter_all` at `k = 6`
   with the order-`6` per-curve data `RHSDataFepsSix.exists_RHSData_feps_six` (which needs the
   `XBall` curve and the uniform `ℋ⁸`-size `Feps_data_of_xball8`), the order-`6` per-`z` bound
   for the iterates `perz_iter_feps_le_six`, the order-`6` slot convergence
   `tendsto_mixed_epsIter_limFam_six`, and Fatou
   (`HkMem_limFam_of_slot_conv`, i.e. `StrongEps.HkMem_of_tendsto` at `k = m = 6`).

## TRAP (read this before changing the imports)

The `fsm` input of the class-`C` clause is produced by
`Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.FstarPzJepsSmooth` and **not** by the tree's
`EpsE4Thr.FstarPzJepsSmooth`: the latter's dependency cone contains the `sorry`-stub
`FstarJepsSmoothAux.ThShiftPreimageNull` (via `FstarJepsSmoothAux.MajorantIntegrable`), so
importing it would taint this module with `sorryAx`.  The `XBallLimAux` chain is the same proof
with that single gap closed:

* `XBallLimAux.ThShiftNullPreimage` — `thShift_null_preimage` (proved here, from the product
  substitution bound `FstarJepsSmoothAux.LintegralProdThShiftLe`);
* `XBallLimAux.MajorantIntegrable` — copy of `FstarJepsSmoothAux.MajorantIntegrable` using it;
* `XBallLimAux.FstarJepsSmooth`, `XBallLimAux.FstarPzJepsSmooth` — copies of the tree's
  `EpsE4Thr.FstarJepsSmooth`/`EpsE4Thr.FstarPzJepsSmooth` with the input swapped.

Once the owner of `FstarJepsSmoothAux.ThShiftPreimageNull` removes its `sorry`, the tree's
`EpsE4Thr.FstarPzJepsSmooth` becomes usable and the `XBallLimAux` copies become redundant.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.FstarPzJepsSmooth
import Submission.Work.FTS.EpsEngine.H4FepsLim
import Submission.Work.FTS.EpsEngine.limFam_EpsMem
import Submission.Work.FTS.EpsEngine.LimSmoothOpenEngine
import Submission.Work.FTS.EpsEngine.BallLimFam
import Submission.Work.FTS.EpsEngine.ClassCStepSlice
import Submission.Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq
import Submission.Work.FTS.EpsEngine.VolterraV4Iter
import Submission.Work.FTS.EpsEngine.EpsSq_iter_limFam_le
import Submission.Work.FTS.EpsEngine.HkMemIterAll
import Submission.Work.FTS.EpsEngine.slice_iter_succ_mollForm
import Submission.Work.FTS.EpsEngine.IterContMeas
import Submission.Work.FTS.EpsEngine.tendsto_slice_iter_limFam
import Submission.Work.FTS.EpsEngine.H4Feps
import Submission.Work.FTS.EpsEngine.perz_iter_feps_le
import Submission.Work.FTS.EpsEngine.SmoothOpenIterProd
import Submission.Work.FTS.EpsEngine.perz_iter_feps_le_six
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam_six

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem XBallLimExists {α C₀ Ce Cs M' Cpt L δ R : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hC₀ : 0 < C₀) (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hM : 0 ≤ M')
    (hL : 0 < L) (hδ : 0 < δ) (hδL : δ * Real.sqrt L < 1) (hR : 0 < R)
    (hbd : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hsmo : Work.FTS.EllipticEst.SmoothOpen h₀) (hmem : Work.Spaces.HkMem α 6 h₀)
    (hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M')
    (hcl : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)))
    (hball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ C₀ * α ^ 2)
    (hdatmem : Work.FTS.StrongEps.EpsMem α h₀) (hdatsq : Work.FTS.StrongEps.EpsSq α h₀ ≤ R)
    (hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ)) :
    (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ)) ∧
    (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.Spaces.HkMem α 6
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## 0. the numerical set-up of the contraction
  set q : ℝ := δ ^ 2 * L with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq]
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hp : (δ * Real.sqrt L) ^ 2 = δ ^ 2 * L := by rw [mul_pow, Real.sq_sqrt hL.le]
    have h1 : (δ * Real.sqrt L) ^ 2 < 1 := by nlinarith [hδL, mul_nonneg hδ.le hsL]
    rwa [hp] at h1
  set r : ℝ := Real.sqrt q with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Real.sqrt_mul hq0, ← hr, ih, pow_succ']
  have hr1 : r < 1 := by
    have h2 : r ^ 2 = q := by rw [hr]; exact Real.sq_sqrt hq0
    nlinarith [hr0, h2, hq1]
  -- ## 1. the datum in the ball and the gates of the engine
  have hP₀ : Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) h₀ :=
    ⟨hsmo, hdatmem, hdatsq, hcl, le_trans hball (by nlinarith [hC₀.le, sq_nonneg α])⟩
  have hcontF : ∀ u : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      ContinuousOn (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).1
  have hzeroF : ∀ u : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
        Work.FTS.EpsEngine.Feps α ρ ε Φs E u q.1 q.2 = 0 :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).2
  have hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ) := by
    intro n τ hτ
    have h : slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ
        = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ := by
      funext z θ
      simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
    rw [← h]
    exact hiter n τ hτ
  -- ## 2. the a-priori bounds of the engine
  obtain ⟨hP, hB0, hBK, hwsq, hwpt⟩ :=
    Work.FTS.EpsEngine.iter_bounds_v4 (α := α)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u)
      (Cpt := Cpt) (L := L) (δ := δ) (q := q) (r := r)
      hδ hL hδL hq hr hq0 hq1 hr0 hrpow hCpt hP₀ hbd hlip hpt hcontF hzeroF hkeepIter
  obtain ⟨hcontIter, hmeasIter⟩ :=
    Work.FTS.EpsEngine.iter_cont_meas (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u)
      hδ hL.le hCpt hP hcontF hzeroF hbd hpt
  have hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) t z θ) ≤ L * (s - t) ^ 2 :=
    fun n => Work.FTS.EpsEngine.EpsSq_iter_sub_sq_le n hδ hL.le hCpt
      (fun m hm τ hτ => hP m τ hτ) hcontF hzeroF hbd hpt
  have hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ m) s z θ) ≤ q ^ n :=
    Work.FTS.EpsEngine.epsPair_of_iter_bounds (α := α) (δ := δ) (q := q)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀) hq0 hq1
      (fun M hM s hs => (hB0 M s hs hM).2) (fun M K hK hKM s hs => (hBK M K hK hKM s hs).2)
  have hFint : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun σ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) σ) z θ) volume 0 s := by
    intro n s hs z θ hz hθ
    exact ContinuousOn.intervalIntegrable_of_Icc hs.1
      ((hcontIter n z θ hz hθ.1 hθ.2).mono (Set.Icc_subset_Icc_right hs.2))
  have hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) s z θ) Filter.atTop
        (nhds (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s z θ)) :=
    Work.FTS.EpsEngine.tendsto_slice_iter_limFam (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E)
      (h₀ := h₀) (δ := δ) (Cpt := Cpt) (r := r) hCpt hr0 hr1
      (fun n τ hτ hn z θ hz hθ0 hθ1 => hwpt n τ hτ hn z θ hz hθ0 hθ1)
  have hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n s) z θ
          - Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n s
            * Work.FTS.StrongEps.bump z θ :=
    fun n s hs z θ hz hθ =>
      Work.FTS.EpsEngine.slice_iter_succ_mollForm n hα hρ hε hε1 hEll hstar hml hR.le hL.le
        hsmo (fun σ hσ => hP n σ hσ) (fun σ hσ t ht => hEq n σ hσ t ht)
        (fun τ hτ z' θ' hz' hθ' => hFint n τ hτ z' θ' hz' hθ') hs hz hθ
  -- ## 3. the limit clauses
  have hsmoW : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EllipticEst.SmoothOpen (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) := by
    intro τ hτ
    exact Work.FTS.EpsEngine.smoothOpen_limFam_slice_of_iter_bounds (α := α) (C₀ := 2 * C₀)
      (R := R) (Ce := Ce) (Cs := Cs) (Lw := L) (δ := δ) (q := q) (Cpt := Cpt) (ρ := ρ)
      (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
      hα hρ hε hε1 hEll hstar hml hR.le hL.le hsmo hq0 hq1 hCpt hP hEq
      (fun M hM s hs => (hB0 M s hs hM).2)
      (fun M K hK hKM s hs => (hBK M K hK hKM s hs).2)
      (fun n s hs hn z θ hz hθ0 hθ1 => by
        rw [← hr]
        exact hwpt n s hs hn z θ hz hθ0 hθ1)
      (fun n s hs z θ hz hθ => hFint n s hs z θ hz hθ) hτ
  have hmet : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) ∧
      Work.FTS.StrongEps.EpsSq α (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) ≤ R := by
    intro τ hτ
    exact Work.FTS.EpsEngine.limFam_EpsMem (α := α) (R := R) (δ := δ) hR.le hconv
      (fun n σ hσ => ⟨(hP n σ hσ).mem, (hP n σ hσ).sq_le⟩) τ hτ
  have hmem4₀ : Work.Spaces.HkMem α 4 h₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmo 4 (by norm_num) hmem
  have hmem4W : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → Work.Spaces.HkMem α 4
      (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) := by
    intro τ hτ
    refine Work.FTS.EpsEngine.HkMem_epsLim_feps (α := α) (C₀ := 2 * C₀) (R := R) (Ce := Ce)
      (Cs := Cs) (Lw := L) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (g₀ := h₀)
      hα hρ hε hε1 hEll hstar hml hR.le hL.le hsmo hmem hδ.le hq0 hq1 hP hEq hpair hmoll hconv
      hτ
  have hclW : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → Work.FTS.ClassC.ClassC α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))) := by
    intro τ hτ
    exact Work.FTS.EpsEngine.ThetaFromEps.classC_Pz_Jeps_of_epsMem hρ hα hα1 hε hε1
      (hsmoW τ hτ) (hmem4W τ hτ) (hmet τ hτ).1
      (XBallLimAux.FstarPzJepsSmooth (ρ := ρ) hρ hε hα (hsmoW τ hτ)
        (Work.FTS.OpenPkg.HkMem_mono_open (hsmoW τ hτ) 1 (by norm_num) (hmem4W τ hτ)))
  have hxnW : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → Work.FTS.Nonlin.Xn α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))) ≤ 2 * C₀ * α ^ 2 := by
    intro τ hτ
    obtain ⟨B4, hB4pos, hiter4⟩ :=
      Work.FTS.EpsEngine.HkMem_iter_feps (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
        (R := R) (Lw := L) (ε := ε) (δ := δ) (τ := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := h₀)
        hρ hα hε hε1 hR.le hL.le hEll hstar hml hsmo hmem4₀ hδ.le hτ.1 hτ.2 hP hEq
    have hmemN4 : ∀ N : ℕ, Work.Spaces.HkMem α 4
        (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ) := fun N => (hiter4 N).1
    have htail : ∀ N : ℕ, 1 ≤ N →
        Work.FTS.StrongEps.EpsMem α (fun z θ =>
          slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ
          - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ) ∧
        Work.FTS.StrongEps.EpsSq α (fun z θ =>
          slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ
          - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ) ≤ q ^ N := by
      intro N hN
      obtain ⟨hm, hsq⟩ := Work.FTS.EpsEngine.EpsSq_iter_limFam_le (α := α) (q := q) (δ := δ)
        hq0 hq1 hconv (fun M K hK hKM τ' hτ' => hBK M K hK hKM τ' hτ') N hN τ hτ
      refine ⟨?_, ?_⟩
      · have hfun : (fun z θ => slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ
            - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ)
            = fun z θ => -(slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ
            - slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ) := by
          funext z θ; ring
        rw [hfun]
        exact Work.FTS.StrongEps.EpsLocalPStar.EpsMem_neg2 hm
      · rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
        exact hsq
    exact Work.FTS.EpsEngine.Xn_PzJeps_limFam_le_of_tail (α := α) (ε := ε) (C₀ := 2 * C₀)
      (q := q) (ρ := ρ) (Φs := Φs) (E := E)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀) (τ := τ)
      hρ hα hε hε1 hq0 hq1 (fun N => (hP N τ hτ).ball) (fun N hN => htail N hN)
      (fun N => (hP N τ hτ).smoothOpen) (hsmoW τ hτ) hmemN4 (hmem4W τ hτ)
  refine ⟨fun τ hτ => ⟨hsmoW τ hτ, (hmet τ hτ).1, (hmet τ hτ).2, hclW τ hτ, hxnW τ hτ⟩, ?_⟩
  -- ## 4. the `ℋ⁶`-honesty of the limit slice
  intro τ hτ
  have h06 : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 h₀ z θ) ≤ Bz :=
    fun z hz => ⟨_, le_rfl⟩
  have hz6 := Work.FTS.EpsEngine.perz_iter_feps_le_six (α := α) (C₀ := 2 * C₀) (Ce := Ce)
    (Cs := Cs) (R := R) (Lw := L) (ε := ε) (τ := τ) hρ hα hε hε1 hR.le hL.le hτ.1 hEll hstar hml
    (fun n s hs => hP n s ⟨hs.1, le_trans hs.2 hτ.2⟩)
    (fun n s hs t ht => hEq n s ⟨hs.1, le_trans hs.2 hτ.2⟩ t ⟨ht.1, le_trans ht.2 hτ.2⟩) h06
  have hslot6 := Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam_six (α := α) (C₀ := 2 * C₀)
    (R := R) (Ce := Ce) (Cs := Cs) (Lw := L) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E)
    (ε := ε) (h₀ := h₀) hα hρ hε hε1 hEll hstar hml hR.le hL.le hsmo hq0 hq1 hP hEq hpair hmoll
    hconv hτ
  obtain ⟨B6, hB6pos, hRHS6⟩ := Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six
    (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs) (R := R) (Lw := L) (ε := ε) (T := δ)
    (ρ := ρ) (Φs := Φs) (E := E) (g₀ := h₀) hρ hα hε hε1 hR.le hL.le hδ.le hEll hstar hml
  have hiter6 := Work.FTS.EpsEngine.HkMem_iter_all (α := α) (B := B6)
    (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀) (k := 6) (T := δ) (τ := τ)
    hτ.1 hτ.2 hδ.le hB6pos.le hsmo hmem (fun n => (hP n τ hτ).smoothOpen)
    (fun n => hRHS6 n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht))
  exact (Work.FTS.EpsEngine.HkMem_limFam_of_slot_conv (α := α)
    (B := Work.Spaces.HkNorm α 6 h₀ + B6 * τ) (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E)
    (h₀ := h₀) (k := 6) (τ := τ)
    (fun n => (hiter6 n).1) (fun n => (hiter6 n).2)
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hP n τ hτ).smoothOpen 6)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmoW τ hτ) 6)
    (fun j i hji z θ hzq => hslot6 j i hji z θ hzq.1 hzq.2) hz6).1

end Work.FTS.StrongEps.EpsE4Thr
