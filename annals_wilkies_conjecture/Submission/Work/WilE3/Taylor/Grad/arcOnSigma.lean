import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.Loj.curve_selection

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / Grad: *the arc on the sigma locus*.

  Let `Φ` be real analytic on all of `ℝ^k` with `Φ y = 0`.  Suppose that — arbitrarily close to
  `y` — there are points `x` with `x ≠ y`, `Φ x > 0`, `(‖∇Φ x‖²)^q < (Φ x)^{2p}` and with `x` a
  *sigma point* of `Φ`, i.e. `∇Φ x` and `∇(‖∇Φ x‖²)` are linearly dependent.  Then there is a real
  analytic arc `γ` through `y` along which all of this holds for all small `t > 0`.

  This is the "curve selection" step of the Łojasiewicz/Gabrielov argument: the set
  `Σ = {Φ > 0} ∩ {(Φ)^{2p} - (‖∇Φ‖²)^q > 0} ∩ {∇Φ ∥ ∇‖∇Φ‖²}` is a basic semianalytic set (the
  parallelism is imposed by the `k²` minors, each of which is analytic at `y` because the
  coordinate partial derivatives of an analytic germ are analytic), and `y` lies in its closure
  with data analytic at `y`.  The workspace's analytic curve selection
  (`Work.WilE3.Loj.curveSel_full`, i.e. `WilkiesDesign.CG.C4a.CurveSel` for every ambient
  dimension) therefore produces an analytic arc `γ` through `y` which stays in `Σ` for all small
  `s > 0`.  Since `Φ y = 0` while `Φ (γ s) > 0`, the arc automatically misses `y`, so the
  punctured-neighbourhood conclusion of the target holds outright on `(0, ε)`.

  Note that the hypothesis `p < q` of the target is not needed for this step: the curve selection
  consumes only the existence of the sequence, not its arithmetic meaning.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology

namespace Work.WilE3.Taylor.Grad

/-! ## §1. Analyticity of the coordinate gradient -/

/-- Every coordinate partial derivative `x ↦ (∇Φ x) i` of an analytic germ is analytic. -/
lemma analyticAt_grad {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (h : AnalyticAt ℝ Φ y) (i : Fin k) : AnalyticAt ℝ (fun x => grad Φ x i) y := by
  have h1 : AnalyticAt ℝ (fderiv ℝ Φ) y := h.fderiv
  have h2 : AnalyticAt ℝ (fun L : (Fin k → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ)))
      (fderiv ℝ Φ y) :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).analyticAt (fderiv ℝ Φ y)
  simpa [grad, Function.comp_def] using h2.comp h1

/-- The squared gradient norm `x ↦ ∑ l, (∇Φ x l)²` of an analytic germ is analytic. -/
lemma analyticAt_gradSumSq {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (h : AnalyticAt ℝ Φ y) :
    AnalyticAt ℝ (fun x => ∑ l : Fin k, (grad Φ x l) ^ 2) y := by
  have hsum := Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
    (fun l _ => (analyticAt_grad h l).pow 2)
  have hfun : (∑ l : Fin k, (fun x => grad Φ x l) ^ 2 : (Fin k → ℝ) → ℝ)
      = fun x => ∑ l : Fin k, (grad Φ x l) ^ 2 := by
    funext x; simp [Finset.sum_apply, Pi.pow_apply]
  rw [hfun] at hsum
  exact hsum

/-! ## §2. The tangency ("sigma") condition and the two strict inequalities -/

/-- The `(i,j)`-minor of the pair `(∇Φ, ∇‖∇Φ‖²)`: the target's tangency condition at `x` is
exactly `minorFun Φ i j x = 0` for all `i j`.  The two gradients are linearly dependent precisely
when all these minors vanish (`Work.WilE3.Taylor.minors_eq_zero_iff`). -/
noncomputable def minorFun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (i j : Fin k) : (Fin k → ℝ) → ℝ :=
  fun x => grad Φ x i * grad (fun z => ∑ l, (grad Φ z l) ^ 2) x j
    - grad Φ x j * grad (fun z => ∑ l, (grad Φ z l) ^ 2) x i

/-- Evaluation form of `minorFun`; it is the literal expression of the target's tangency
condition. -/
lemma minorFun_apply {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (i j : Fin k) (x : Fin k → ℝ) :
    minorFun Φ i j x = grad Φ x i * grad (fun z => ∑ l, (grad Φ z l) ^ 2) x j
      - grad Φ x j * grad (fun z => ∑ l, (grad Φ z l) ^ 2) x i := rfl

/-- Each minor is analytic at `y` when `Φ` is. -/
lemma analyticAt_minorFun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (h : AnalyticAt ℝ Φ y) (i j : Fin k) : AnalyticAt ℝ (minorFun Φ i j) y := by
  have hS : AnalyticAt ℝ (fun z => ∑ l, (grad Φ z l) ^ 2) y := analyticAt_gradSumSq h
  have h1 : AnalyticAt ℝ (fun x => grad Φ x i) y := analyticAt_grad h i
  have h2 : AnalyticAt ℝ (fun x => grad Φ x j) y := analyticAt_grad h j
  have h3 : AnalyticAt ℝ (fun x => grad (fun z => ∑ l, (grad Φ z l) ^ 2) x j) y :=
    analyticAt_grad hS j
  have h4 : AnalyticAt ℝ (fun x => grad (fun z => ∑ l, (grad Φ z l) ^ 2) x i) y :=
    analyticAt_grad hS i
  exact (h1.mul h3).sub (h2.mul h4)

/-- `sigmaFun Φ x = ∑_{i,j} (minorFun Φ i j x)²`: the sum of the squares of all the minors, so
that it vanishes exactly at the tangency points of `Φ` (and is a *single* analytic equation, the
form in which the curve selection lemma of this workspace consumes semianalytic data). -/
noncomputable def sigmaFun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  fun x => ∑ ij : Fin k × Fin k, (minorFun Φ ij.1 ij.2 x) ^ 2

/-- `sigmaFun` is analytic at `y` when `Φ` is. -/
lemma analyticAt_sigmaFun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ}
    (h : AnalyticAt ℝ Φ y) : AnalyticAt ℝ (sigmaFun Φ) y := by
  have hsum := Finset.analyticAt_sum (Finset.univ : Finset (Fin k × Fin k))
    (fun ij _ => (analyticAt_minorFun h ij.1 ij.2).pow 2)
  have hfun : (∑ ij : Fin k × Fin k, (fun x => minorFun Φ ij.1 ij.2 x) ^ 2 :
        (Fin k → ℝ) → ℝ)
      = fun x => ∑ ij : Fin k × Fin k, (minorFun Φ ij.1 ij.2 x) ^ 2 := by
    funext x; simp [Finset.sum_apply, Pi.pow_apply]
  rw [hfun] at hsum
  exact hsum

/-- A vanishing sum of squares vanishes termwise: the tangency of `∇Φ` and `∇‖∇Φ‖²`. -/
lemma minorFun_eq_zero_of_sigmaFun_eq_zero {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {z : Fin k → ℝ}
    (h : sigmaFun Φ z = 0) (i j : Fin k) : minorFun Φ i j z = 0 := by
  have h' : ∑ ij : Fin k × Fin k, (minorFun Φ ij.1 ij.2 z) ^ 2 = 0 := h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (f := fun ij : Fin k × Fin k => (minorFun Φ ij.1 ij.2 z) ^ 2)
      (fun ij _ => sq_nonneg _)).mp h'
  exact sq_eq_zero_iff.mp (hterm (i, j) (Finset.mem_univ _))

/-- The two strict inequalities of the target as a `Fin 2`-family: coordinate `0` is `Φ > 0`,
coordinate `1` is `(Φ)^{2p} - (∑ l, (∇Φ l)²)^q > 0`. -/
noncomputable def posFun {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) :
    Fin 2 → (Fin k → ℝ) → ℝ :=
  ![fun x => Φ x, fun x => (Φ x) ^ (2 * p) - (∑ l, (grad Φ x l) ^ 2) ^ q]

/-- Value of `posFun` at the first coordinate: `Φ > 0`. -/
lemma posFun_zero {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) :
    posFun Φ p q 0 = (fun x : Fin k → ℝ => Φ x) := by simp [posFun]

/-- Value of `posFun` at the second coordinate: `(Φ)^{2p} - (∑ l, (∇Φ l)²)^q > 0`. -/
lemma posFun_one {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (p q : ℕ) :
    posFun Φ p q 1
      = (fun x : Fin k → ℝ => (Φ x) ^ (2 * p) - (∑ l, (grad Φ x l) ^ 2) ^ q) := by
  simp [posFun]

/-- Both members of the `Fin 2`-family are analytic at `y`. -/
lemma analyticAt_posFun {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {p q : ℕ}
    (h : AnalyticAt ℝ Φ y) (j : Fin 2) : AnalyticAt ℝ (posFun Φ p q j) y := by
  have hS : AnalyticAt ℝ (fun x => ∑ l, (grad Φ x l) ^ 2) y := analyticAt_gradSumSq h
  fin_cases j
  · change AnalyticAt ℝ (posFun Φ p q 0) y
    rw [posFun_zero]; exact h
  · change AnalyticAt ℝ (posFun Φ p q 1) y
    rw [posFun_one]; exact (h.pow (2 * p)).sub (hS.pow q)

/-! ## §3. The arc -/

theorem arcOnSigma {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {p q : ℕ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hy : Φ y = 0) (hpq : p < q)
    (hseq : ∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j : Fin k,
        Work.WilE3.Taylor.grad Φ x i *
            Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) x j
          - Work.WilE3.Taylor.grad Φ x j *
            Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) x i
          = 0)) :
    ∃ γ : ℝ → Fin k → ℝ, AnalyticAt ℝ γ 0 ∧ γ 0 = y ∧
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ t ≠ y ∧ 0 < Φ (γ t) ∧
        (∑ l, (Work.WilE3.Taylor.grad Φ (γ t) l) ^ 2) ^ q < (Φ (γ t)) ^ (2 * p) ∧
        (∀ i j : Fin k,
          Work.WilE3.Taylor.grad Φ (γ t) i *
              Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) (γ t) j
            - Work.WilE3.Taylor.grad Φ (γ t) j *
              Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) (γ t) i
            = 0) := by
  have _hpq := hpq
  -- restate the sequence hypothesis in the vocabulary of this file
  have hseq' : ∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧ 0 < Φ x ∧
      (∑ l, (grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j : Fin k, minorFun Φ i j x = 0) := by
    intro n
    obtain ⟨x, h1, h2, h3, h4, h5⟩ := hseq n
    exact ⟨x, h1, h2, h3, h4, fun i j => by rw [minorFun_apply]; exact h5 i j⟩
  choose x hxne hxd hxpos hxlt hxtan using hseq'
  -- the good points tend to `y`, so `y` is a cluster point of the semianalytic set `Σ`
  have hx_tendsto : Tendsto x atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hxd n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hmemS : ∀ n, x n ∈ WilkiesDesign.CG.C4a.BasicSA (sigmaFun Φ) (posFun Φ p q) := by
    intro n
    refine ⟨?_, ?_⟩
    · have hsum : ∑ ij : Fin k × Fin k, (minorFun Φ ij.1 ij.2 (x n)) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun ij _ => ?_
        rw [hxtan n ij.1 ij.2]
        simp
      exact hsum
    · intro j
      fin_cases j
      · change 0 < posFun Φ p q 0 (x n)
        rw [posFun_zero]; exact hxpos n
      · change 0 < posFun Φ p q 1 (x n)
        rw [posFun_one]; exact sub_pos.mpr (hxlt n)
  have hycl : y ∈ closure (WilkiesDesign.CG.C4a.BasicSA (sigmaFun Φ) (posFun Φ p q)) :=
    mem_closure_of_tendsto hx_tendsto (Eventually.of_forall hmemS)
  -- analytic curve selection
  obtain ⟨γ, hγan, hγ0, ε, hεpos, hγmem⟩ :=
    Work.WilE3.Loj.curveSel_full k 2 (sigmaFun Φ) (posFun Φ p q) y
      (analyticAt_sigmaFun (hΦ y)) (fun j => analyticAt_posFun (hΦ y) j) hycl
  refine ⟨γ, hγan, hγ0, ?_⟩
  have hnb : Set.Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hεpos))
  filter_upwards [hnb] with t ht
  have hsig : sigmaFun Φ (γ t) = 0 := (hγmem t ht).1
  have hpos : 0 < Φ (γ t) := by
    have h := (hγmem t ht).2 0
    rw [posFun_zero] at h
    exact h
  have hineq : (∑ l, (grad Φ (γ t) l) ^ 2) ^ q < (Φ (γ t)) ^ (2 * p) := by
    have h2 : 0 < (Φ (γ t)) ^ (2 * p) - (∑ l, (grad Φ (γ t) l) ^ 2) ^ q := by
      have h := (hγmem t ht).2 1
      rw [posFun_one] at h
      exact h
    linarith
  have hne : γ t ≠ y := by
    intro hEq
    rw [hEq, hy] at hpos
    exact lt_irrefl 0 hpos
  exact ⟨hne, hpos, hineq, fun i j => by
    have h := minorFun_eq_zero_of_sigmaFun_eq_zero hsig i j
    rw [minorFun_apply] at h
    exact h⟩

end Work.WilE3.Taylor.Grad
