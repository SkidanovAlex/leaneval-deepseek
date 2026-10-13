/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/LimSmoothOpenEngine.lean`

**The `SmoothOpen` clause of `hlimP`, packaged against the engine's own data.**  The main
mathematical content is `LimSmoothOpen.smoothOpen_limFam_slice`; here the four structural inputs of
that lemma are *produced* from the outputs of `iter_bounds_v4` and the child lemma
`slice_iter_succ_mollForm`:

* `hpair` (the geometric pair bound of two Picard iterates) from the `hB0`/`hBK` components of
  `iter_bounds_v4`;
* `hconv` (pointwise convergence of the iterates) from `hwpt` via `tendsto_slice_iter_limFam`;
* `hmoll` (the mollified form of one Picard step) from `slice_iter_succ_mollForm`.

So the only analytic inputs left are the `X`-ball invariant `hP`, the time-Lipschitz bound `hEq`
(both produced by `SmoothOpenIterProd.EpsSq_iter_sub_sq_le` and the class preservation), the point
integrability `hFint` of the scheme's right-hand side, and the pointwise geometric bound `hwpt`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.LimSmoothOpen
import Submission.Work.FTS.EpsEngine.slice_iter_succ_mollForm
import Submission.Work.FTS.EpsEngine.tendsto_slice_iter_limFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **`hpair` from the a-priori bounds**: the ordered geometric pair bound of two Picard iterates,
in the form consumed by `smoothOpen_limFam_slice`, from the two components `hB0`/`hBK` of
`iter_bounds_v4`. -/
theorem epsPair_of_iter_bounds {α δ q : ℝ} {F : Fn → Fn} {h₀ : Fn} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hB0 : ∀ M : ℕ, 1 ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (iter F h₀ M) s z θ - h₀ z θ) ≤ q)
    (hBK : ∀ (M K : ℕ), 1 ≤ K → K ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (iter F h₀ M) s z θ - slice (iter F h₀ K) s z θ) ≤ q ^ (K + 1)) :
    ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      EpsSq α (fun z θ => slice (iter F h₀ n) s z θ - slice (iter F h₀ m) s z θ) ≤ q ^ n := by
  intro n m s hs hnm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hzero : (fun z θ => slice (iter F h₀ 0) s z θ
          - slice (iter F h₀ 0) s z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ; simp
      rw [hzero, EpsSq_zero, pow_zero]
      norm_num
    · rw [EpsSq_sub_comm, pow_zero]
      refine (hB0 m hm s hs).trans hq1.le
  · rw [EpsSq_sub_comm]
    refine (hBK m n hn hnm s hs).trans ?_
    exact pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ n)

/-- **The `SmoothOpen` clause of `hlimP`** from the engine's data: the `X`-ball invariant `hP`, the
time-Lipschitz bound `hEq`, the a-priori bounds `hB0`/`hBK`/`hwpt` of `iter_bounds_v4`, and the
point integrability `hFint` of the scheme's right-hand side. -/
theorem smoothOpen_limFam_slice_of_iter_bounds {α C₀ R Ce Cs Lw δ q Cpt : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀) (hq0 : 0 ≤ q) (hq1 : q < 1) (hCpt : 0 ≤ Cpt)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (epsIter α ρ ε Φs E h₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ n) s z θ
        - slice (epsIter α ρ ε Φs E h₀ n) t z θ) ≤ Lw * (s - t) ^ 2)
    (hB0 : ∀ M : ℕ, 1 ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ M) s z θ - h₀ z θ) ≤ q)
    (hBK : ∀ (M K : ℕ), 1 ≤ K → K ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ M) s z θ
        - slice (epsIter α ρ ε Φs E h₀ K) s z θ) ≤ q ^ (K + 1))
    (hwpt : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |wseq (Feps α ρ ε Φs E) h₀ n s z θ| ≤ δ * Cpt * (Real.sqrt q) ^ n)
    (hFint : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun σ => Feps α ρ ε Φs E
        (slice (epsIter α ρ ε Φs E h₀ n) σ) z θ) volume 0 s)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    Work.FTS.EllipticEst.SmoothOpen (slice (epsLim α ρ ε Φs E h₀) τ) := by
  have hpair := epsPair_of_iter_bounds (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀) hq0 hq1 hB0 hBK
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqrt1 : Real.sqrt q < 1 := by
    have h2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
    nlinarith
  have hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Tendsto (fun N : ℕ => slice (epsIter α ρ ε Φs E h₀ N) s z θ) atTop
        (𝓝 (slice (epsLim α ρ ε Φs E h₀) s z θ)) :=
    tendsto_slice_iter_limFam (F := Feps α ρ ε Φs E) (h₀ := h₀) hCpt hsqrt0 hsqrt1 hwpt
  have hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n s) z θ
          - epsC α ρ ε Φs E h₀ n s * bump z θ :=
    fun n s hs z θ hz hθ =>
      slice_iter_succ_mollForm n hα hρ hε hε1 hEll hstar hml hR hLw h0 (hP n) (hEq n)
        (hFint n) hs hz hθ
  exact smoothOpen_limFam_slice hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1
    hP hEq hpair hmoll hconv hτ

end Work.FTS.EpsEngine
