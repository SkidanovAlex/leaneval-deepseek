/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.splitPair_exists` — the split pair of a parabolic point

**(H1) of the parabolic-splitting programme.**  Let `c₀` be a root-parabolic parameter of the
period-5 component of the tricorn and `z₁` its characteristic point.  Then there are `ρ, R > 0`
and *continuous* `m G : ℂ → ℂ` with `m c₀ = z₁`, `G c₀ = 0` and, for all `c ∈ ball c₀ ρ` and
`z ∈ ball z₁ R`,

    `Work.EL.F c z = z ↔ (z - m c)² = G c`.

Here `Work.EL.F c = (T_c)^{10} = (Tsq c)^[5]` is the holomorphic second return map, `m c` is the
*midpoint* of the two fixed points near `z₁` and `G c = Δ c²` the square of their
*half-difference*.  Both are symmetric functions of the two roots, hence single-valued; the
continuity is obtained from the argument principle for the fixed-point polynomial
`Hp c = F c · - X` of `F c`:

* `Hp c` depends continuously on `c` and `Hp c₀ = (X - z₁)² · S` with `S(z₁) ≠ 0`;
* for `c` near `c₀`, `Hp c` has no zero on the circle `|z - z₁| = r`, so the argument principle
  exhibits the power sums `p_k(c) = Σ_{a ∈ roots(Hp c), |a-z₁|<r} a^k` as contour integrals,
  continuous in `c`;
* the number of roots inside the disc is `2`, by connectedness (a continuous `ℕ`-valued function);
* the two roots are exactly the roots of `(X - m c)² - G c`, where `m c = p₁(c)/2` and
  `G c = (2p₂(c) - p₁(c)²)/4`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.PARIMPL.ParSplit.exists_uniform_bounds
import Submission.Work.PARIMPL.ParSplit.polyArgPrinciple
import Submission.Work.PARIMPL.ParSplit.continuous_circleIntegral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

open Classical Polynomial Set Metric
open scoped Topology

noncomputable section

variable {c₀ : ℂ}

/-! ## The fixed-point polynomial `Hp c = F c · - X` -/

/-- `Tsq c z = (z² + c̄)² + c` as a polynomial. -/
def TsqP (c : ℂ) : ℂ[X] := (X ^ 2 + C (star c)) ^ 2 + C c

theorem TsqP_eval (c z : ℂ) : (TsqP c).eval z = Work.Landing.Tsq c z := by
  simp [TsqP, Work.Landing.Tsq]

theorem TsqP_monic (c : ℂ) : (TsqP c).Monic := by unfold TsqP; monicity!

theorem TsqP_natDegree (c : ℂ) : (TsqP c).natDegree = 4 := by unfold TsqP; compute_degree!

/-- The `n`-th composition iterate of `TsqP c`. -/
def iterP (c : ℂ) : ℕ → ℂ[X]
  | 0 => X
  | n + 1 => (TsqP c).comp (iterP c n)

theorem iterP_eval (c z : ℂ) (n : ℕ) : (iterP c n).eval z = (Work.Landing.Tsq c)^[n] z := by
  induction n with
  | zero => simp [iterP]
  | succ n ih => rw [iterP, Polynomial.eval_comp, ih, TsqP_eval, Function.iterate_succ_apply']

theorem iterP_natDegree (c : ℂ) (n : ℕ) : (iterP c n).natDegree = 4 ^ n := by
  induction n with
  | zero => simp [iterP]
  | succ n ih =>
      rw [iterP, Polynomial.natDegree_comp, TsqP_natDegree, ih, pow_succ]; ring

theorem iterP_monic (c : ℂ) (n : ℕ) : (iterP c n).Monic := by
  induction n with
  | zero => simp [iterP]
  | succ n ih =>
      rw [iterP]
      exact Polynomial.Monic.comp (TsqP_monic c) ih (by rw [iterP_natDegree]; positivity)

theorem iterP_ne_zero (c : ℂ) (n : ℕ) : iterP c n ≠ 0 := (iterP_monic c n).ne_zero

/-- **The fixed point polynomial** `Hp c = (Tsq c)^[5] · - X` of the second return map. -/
def Hp (c : ℂ) : ℂ[X] := iterP c 5 - X

theorem Hp_eval (c z : ℂ) : (Hp c).eval z = Work.EL.F c z - z := by
  simp only [Hp, Polynomial.eval_sub, Polynomial.eval_X]
  rw [iterP_eval]; rfl

theorem Hp_natDegree (c : ℂ) : (Hp c).natDegree = 1024 := by
  have h : (X : ℂ[X]).natDegree < (iterP c 5).natDegree := by
    rw [Polynomial.natDegree_X, iterP_natDegree]; norm_num
  rw [Hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt h, iterP_natDegree]
  norm_num

theorem Hp_monic (c : ℂ) : (Hp c).Monic := by
  rw [Hp]
  refine (iterP_monic c 5).sub_of_left ?_
  rw [Polynomial.degree_X, Polynomial.degree_eq_natDegree (iterP_ne_zero c 5), iterP_natDegree]
  norm_num

theorem Hp_ne_zero (c : ℂ) : Hp c ≠ 0 := (Hp_monic c).ne_zero

theorem Hp_deriv_eval (c z : ℂ) :
    (Hp c).derivative.eval z = deriv (Work.EL.F c) z - 1 := by
  rw [← Polynomial.deriv]
  simp only [Hp_eval]
  rw [show (fun x : ℂ => Work.EL.F c x - x) = (fun x => Work.EL.F c x) - fun x => x from rfl]
  rw [deriv_sub]
  · simp
  · exact (differentiable_Tsq_iterate c 5).differentiableAt
  · exact differentiableAt_id

/-! ## Joint continuity of the polynomial and of its derivative -/

theorem continuous_Hp_eval : Continuous (fun p : ℂ × ℂ => (Hp p.1).eval p.2) := by
  have h : (fun p : ℂ × ℂ => (Hp p.1).eval p.2) = fun p => Work.EL.F p.1 p.2 - p.2 := by
    funext p; exact Hp_eval p.1 p.2
  rw [h]
  exact continuous_Zr_five.sub continuous_snd

theorem continuous_Hp_deriv_eval : Continuous (fun p : ℂ × ℂ => (Hp p.1).derivative.eval p.2) := by
  have h : (fun p : ℂ × ℂ => (Hp p.1).derivative.eval p.2)
      = fun p => deriv (Work.EL.F p.1) p.2 - 1 := by
    funext p; exact Hp_deriv_eval p.1 p.2
  rw [h]
  exact continuous_Ar_five.sub continuous_const

/-! ## The root structure of `Hp c₀` at `z₁` -/

theorem Tantibar_iter_two (c : ℂ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2] = Work.Landing.Tsq c := by
  funext z
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  simp only [Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar, Work.Landing.Tsq,
    starRingEnd_apply, star_add, star_pow, star_star]

theorem F_eq_Tantibar_ten (c : ℂ) :
    Work.EL.F c = (LeanEval.ComplexAnalysis.Tantibar c)^[10] := by
  show (Work.Landing.Tsq c)^[5] = _
  rw [← Tantibar_iter_two c, ← Function.iterate_mul]

theorem F_fixed (d : Work.EL.RootParabolic c₀) : Work.EL.F c₀ d.z₁ = d.z₁ := by
  rw [F_eq_Tantibar_ten]
  rw [show (10 : ℕ) = 5 + 5 by norm_num, Function.iterate_add]
  simp only [Function.comp_apply]
  rw [d.per_half, d.per_half]

theorem eval_deriv_deriv (p : ℂ[X]) (a : ℂ) :
    p.derivative.derivative.eval a = iteratedDeriv 2 (fun x => p.eval x) a := by
  have h1 : (fun x => p.derivative.eval x) = deriv (fun x => p.eval x) := by
    funext x; rw [Polynomial.deriv]
  have h2 : (fun x => p.derivative.derivative.eval x) = deriv (fun x => p.derivative.eval x) := by
    funext x; rw [Polynomial.deriv]
  rw [iteratedDeriv_succ, iteratedDeriv_one, ← h1, ← h2]

theorem Hp_second_deriv (c z : ℂ) :
    (Hp c).derivative.derivative.eval z = iteratedDeriv 2 (Work.EL.F c) z := by
  rw [eval_deriv_deriv]
  have hfun : (fun x : ℂ => (Hp c).eval x) = Work.EL.F c - (fun x : ℂ => x) := by
    funext x; rw [Pi.sub_apply, Hp_eval]
  rw [hfun]
  rw [iteratedDeriv_sub (f := Work.EL.F c) (g := fun x : ℂ => x)]
  · have hid : iteratedDeriv 2 (fun x : ℂ => x) z = 0 := by
      rw [show (fun x : ℂ => x) = id from rfl, iteratedDeriv_id]; norm_num
    rw [hid]; ring
  · have h : Work.EL.F c = fun z => (iterP c 5).eval z := by
      funext z; rw [iterP_eval]; rfl
    rw [h]
    exact (Polynomial.differentiable (iterP c 5)).contDiff.contDiffAt
  · exact contDiffAt_id

/-- The second derivative of `(X - a)² · S` at `a` equals `2 S(a)`. -/
theorem eval_deriv_deriv_sq_mul (S : ℂ[X]) (a : ℂ) :
    ((X - C a)^2 * S).derivative.derivative.eval a = 2 * S.eval a := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_X_sub_C, Polynomial.derivative_C, Polynomial.derivative_one,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  ring

/-- The quotient of `p` by the monic linear polynomial `X - a`, evaluated at `a`, is the
derivative of `p` at `a`. -/
theorem eval_div_X_sub_C (p : ℂ[X]) (a : ℂ) (h : (X - C a) ∣ p) :
    (p /ₘ (X - C a)).eval a = p.derivative.eval a := by
  have hp : (X - C a) * (p /ₘ (X - C a)) = p := by
    have hmod : p %ₘ (X - C a) = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C a)).mpr h
    have hh := Polynomial.modByMonic_add_div p (X - C a)
    rw [hmod, zero_add] at hh
    exact hh
  have key : ((X - C a) * (p /ₘ (X - C a))).derivative.eval a
      = (p /ₘ (X - C a)).eval a := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [← key, hp]

theorem div_monic_X_sub_C (p : ℂ[X]) (a : ℂ) (h : (X - C a) ∣ p) :
    (X - C a) * (p /ₘ (X - C a)) = p := by
  have hmod : p %ₘ (X - C a) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C a)).mpr h
  have hh := Polynomial.modByMonic_add_div p (X - C a)
  rw [hmod, zero_add] at hh
  exact hh

/-- **Splitting a double root.** -/
theorem exists_sq_factor (p : ℂ[X]) (a : ℂ) (h1 : (X - C a) ∣ p)
    (h2 : p.derivative.eval a = 0) :
    ∃ S : ℂ[X], p = (X - C a)^2 * S ∧ S.eval a = p.derivative.derivative.eval a / 2 := by
  have hQeval : (p /ₘ (X - C a)).eval a = 0 := by
    rw [eval_div_X_sub_C _ _ h1]; exact h2
  have h2' : (X - C a) ∣ (p /ₘ (X - C a)) := Polynomial.dvd_iff_isRoot.mpr hQeval
  have hq1 := div_monic_X_sub_C p a h1
  have hq2 := div_monic_X_sub_C (p /ₘ (X - C a)) a h2'
  have hmain : (X - C a) * ((X - C a) * ((p /ₘ (X - C a)) /ₘ (X - C a))) = p := by
    rw [hq2, hq1]
  refine ⟨(p /ₘ (X - C a)) /ₘ (X - C a), ?_, ?_⟩
  · rw [sq, mul_assoc]; exact hmain.symm
  · have hkey := eval_deriv_deriv_sq_mul ((p /ₘ (X - C a)) /ₘ (X - C a)) a
    have heq : (X - C a)^2 * ((p /ₘ (X - C a)) /ₘ (X - C a)) = p := by
      rw [sq, mul_assoc]; exact hmain
    rw [heq] at hkey
    rw [hkey]; ring

/-- **`z₁` is a double root of `Hp c₀` and the cofactor does not vanish there.** -/
theorem Hp_c0_double_root (d : Work.EL.RootParabolic c₀) :
    ∃ S : ℂ[X], Hp c₀ = (X - C d.z₁)^2 * S ∧ S.eval d.z₁ ≠ 0 := by
  have hroot : (Hp c₀).IsRoot d.z₁ := by
    rw [Polynomial.IsRoot.def, Hp_eval, F_fixed d, sub_self]
  have hdroot : (Hp c₀).derivative.eval d.z₁ = 0 := by
    rw [Hp_deriv_eval]
    have h : deriv (Work.EL.F c₀) d.z₁ = 1 := d.mult
    rw [h, sub_self]
  obtain ⟨S, hS, hSeval⟩ :=
    exists_sq_factor (Hp c₀) d.z₁ (Polynomial.dvd_iff_isRoot.mpr hroot) hdroot
  refine ⟨S, hS, ?_⟩
  intro hzero
  have hne : (Hp c₀).derivative.derivative.eval d.z₁ ≠ 0 := by
    rw [Hp_second_deriv]; exact d.simple
  have h2 : (Hp c₀).derivative.derivative.eval d.z₁ = 0 := by
    have hz : (Hp c₀).derivative.derivative.eval d.z₁ / 2 = 0 := by rw [← hSeval, hzero]
    rcases div_eq_zero_iff.mp hz with h | h
    · exact h
    · exact absurd h (by norm_num)
  exact hne h2

/-- **A radius around `z₁` containing no other root of `Hp c₀`.** -/
theorem exists_radius (d : Work.EL.RootParabolic c₀) :
    ∃ r > 0, ∀ z ∈ Metric.closedBall d.z₁ r, (Hp c₀).eval z = 0 → z = d.z₁ := by
  obtain ⟨S, hS, hSeval⟩ := Hp_c0_double_root d
  have hcont : Continuous (fun z : ℂ => S.eval z) := Polynomial.continuous S
  have hnhds : {z : ℂ | S.eval z ≠ 0} ∈ 𝓝 d.z₁ :=
    hcont.continuousAt (isOpen_ne.mem_nhds hSeval)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r / 2, by linarith, ?_⟩
  intro z hz hroot
  have hz' : z ∈ Metric.ball d.z₁ r := by
    have hle : dist z d.z₁ ≤ r / 2 := Metric.mem_closedBall.mp hz
    rw [Metric.mem_ball]; linarith
  have hSz : S.eval z ≠ 0 := hball hz'
  have heval : (Hp c₀).eval z = (z - d.z₁)^2 * S.eval z := by
    rw [hS, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [heval] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  · exact absurd h hSz

/-- **A parameter ball on which `Hp c` has no root on the circle `|z - z₁| = r`.** -/
theorem exists_param_ball_no_root {z₁ : ℂ} {r : ℝ} (hr : 0 < r) {c₀ : ℂ}
    (h0 : ∀ z ∈ Metric.sphere z₁ r, (Hp c₀).eval z ≠ 0) :
    ∃ ρ > 0, ∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0 := by
  set Z : Set (ℂ × ℂ) := {p : ℂ × ℂ | (Hp p.1).eval p.2 = 0} with hZ
  have hZc : IsClosed Z := isClosed_singleton.preimage continuous_Hp_eval
  have hsub : ({c₀} : Set ℂ) ×ˢ Metric.sphere z₁ r ⊆ Zᶜ := by
    rw [Set.prod_subset_iff]
    intro c hc z hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [Set.mem_compl_iff, hZ]
    simpa using h0 z hz
  obtain ⟨u, v, hu, hv, hcu, hsphere, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere z₁ r) hZc.isOpen_compl hsub
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (hcu (Set.mem_singleton_iff.mpr rfl)))
  refine ⟨ρ, hρ, ?_⟩
  intro c hc z hz
  have hmem : (c, z) ∈ Zᶜ := huv (Set.mem_prod.mpr ⟨hρsub hc, hsphere hz⟩)
  rw [Set.mem_compl_iff, hZ] at hmem
  simpa using hmem

/-! ## The power sums of the roots in the disc -/

/-- `Pk z₁ r k c = ∮_{|z-z₁|=r} z^k · (Hp c)'(z)/(Hp c)(z) dz`. -/
def Pk (z₁ : ℂ) (r : ℝ) (k : ℕ) : ℂ → ℂ :=
  fun c => ∮ z in C(z₁, r), z ^ k * ((Hp c).derivative.eval z / (Hp c).eval z)

/-- The multiset of roots of `Hp c` inside `ball z₁ r`. -/
def rootFilt (z₁ : ℂ) (r : ℝ) (c : ℂ) : Multiset ℂ :=
  (Hp c).roots.filter (fun a => a ∈ Metric.ball z₁ r)

theorem two_pi_I_ne_zero : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by intro h; exact Real.pi_ne_zero (by exact_mod_cast h)
  exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero

theorem continuousOn_Pk {z₁ : ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) {c₀ : ℂ}
    (hno : ∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0) (k : ℕ) :
    ContinuousOn (Pk z₁ r k) (Metric.ball c₀ ρ) := by
  refine continuous_circleIntegral isOpen_ball hr ?_
  intro p hp
  rw [Set.mem_prod] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hne : (Hp p.1).eval p.2 ≠ 0 := hno p.1 hp1 p.2 hp2
  have hnum : ContinuousAt (fun q : ℂ × ℂ => (Hp q.1).derivative.eval q.2) p :=
    continuous_Hp_deriv_eval.continuousAt
  have hden : ContinuousAt (fun q : ℂ × ℂ => (Hp q.1).eval q.2) p :=
    continuous_Hp_eval.continuousAt
  have hpk : ContinuousAt (fun q : ℂ × ℂ => q.2 ^ k) p := continuous_snd.continuousAt.pow k
  exact hpk.mul (hnum.div hden hne)

theorem Pk_eq_sum {z₁ : ℂ} {r : ℝ} (hr : 0 < r) {c : ℂ}
    (hno : ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0) (k : ℕ) :
    Pk z₁ r k c = 2 * ↑Real.pi * Complex.I *
      ((rootFilt z₁ r c).map (fun a => a ^ k)).sum := by
  have h := polyArgPrinciple (Hp_ne_zero c) hr (g := (X : ℂ[X]) ^ k) hno
  have hcongr : (∮ z in C(z₁, r), z ^ k * ((Hp c).derivative.eval z / (Hp c).eval z))
      = ∮ z in C(z₁, r), ((Hp c).derivative.eval z / (Hp c).eval z)
          * (Polynomial.eval z ((X : ℂ[X]) ^ k)) := by
    apply circleIntegral.integral_congr hr.le
    intro z _
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [Pk, rootFilt, hcongr, h]
  congr 1
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a _
  simp

theorem sum_map_one (s : Multiset ℂ) :
    (s.map (fun _ => (1 : ℂ))).sum = (s.card : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons]; push_cast; ring

/-- The `0`-th power sum: the number of roots in the disc. -/
theorem p0_eq_card {z₁ : ℂ} {r : ℝ} (hr : 0 < r) {c : ℂ}
    (hno : ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0) :
    (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 0 c = ((rootFilt z₁ r c).card : ℂ) := by
  rw [Pk_eq_sum hr hno 0, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have hmap : (rootFilt z₁ r c).map (fun a => a ^ 0) = (rootFilt z₁ r c).map (fun _ => (1 : ℂ)) := by
    apply Multiset.map_congr rfl
    intro a _
    simp
  rw [hmap, sum_map_one]

/-- The first power sum. -/
def p1 (z₁ : ℂ) (r : ℝ) (c : ℂ) : ℂ := (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 1 c

/-- The second power sum. -/
def p2 (z₁ : ℂ) (r : ℝ) (c : ℂ) : ℂ := (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 2 c

/-- The midpoint of the two roots. -/
def mP (z₁ : ℂ) (r : ℝ) (c : ℂ) : ℂ := p1 z₁ r c / 2

/-- The square of the half-difference of the two roots. -/
def GP (z₁ : ℂ) (r : ℝ) (c : ℂ) : ℂ := (2 * p2 z₁ r c - p1 z₁ r c ^ 2) / 4

theorem p1_eq_sum {z₁ : ℂ} {r : ℝ} (hr : 0 < r) {c : ℂ}
    (hno : ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0) :
    p1 z₁ r c = (rootFilt z₁ r c).sum := by
  have hmap : (rootFilt z₁ r c).map (fun a : ℂ => a ^ 1) = rootFilt z₁ r c := by
    rw [show (fun a : ℂ => a ^ 1) = id from funext (fun a => pow_one a), Multiset.map_id]
  rw [p1, Pk_eq_sum hr hno 1, hmap, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

theorem p2_eq_sum {z₁ : ℂ} {r : ℝ} (hr : 0 < r) {c : ℂ}
    (hno : ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0) :
    p2 z₁ r c = ((rootFilt z₁ r c).map (fun a => a ^ 2)).sum := by
  rw [p2, Pk_eq_sum hr hno 2, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-! ## The number of roots in the disc is two -/

theorem one_le_norm_natCast_sub {n m : ℕ} (h : n ≠ m) :
    (1 : ℝ) ≤ ‖(n : ℂ) - (m : ℂ)‖ := by
  have hnorm : ‖(n : ℂ) - (m : ℂ)‖ = |(n : ℝ) - (m : ℝ)| := by
    have h' : ((n : ℂ) - (m : ℂ)) = ((↑((n : ℝ) - (m : ℝ))) : ℂ) := by push_cast; ring
    rw [h']
    exact RCLike.norm_ofReal _
  rw [hnorm]
  have hne : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast h
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [abs_of_neg (by linarith)]
    have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hlt)
    linarith
  · rw [abs_of_pos (by linarith)]
    have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hlt)
    linarith

/-- A preconnected subset of the natural numbers (inside `ℂ`) is a subsingleton. -/
theorem subsingleton_of_preconnected_subset_natCast {T : Set ℂ} (hT : IsPreconnected T)
    (hsub : T ⊆ Set.range (Nat.cast : ℕ → ℂ)) : T.Subsingleton := by
  rintro x hx y hy
  obtain ⟨m, rfl⟩ := hsub hx
  obtain ⟨n, rfl⟩ := hsub hy
  by_contra hmn
  have hnm : n ≠ m := fun h => hmn (by rw [h])
  have hone : (1 : ℝ) ≤ ‖(n : ℂ) - (m : ℂ)‖ := one_le_norm_natCast_sub hnm
  have hu : IsOpen {z : ℂ | (1 : ℝ) / 2 < ‖z - (m : ℂ)‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have hv : IsOpen {z : ℂ | ‖z - (m : ℂ)‖ < (1 : ℝ) / 2} :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  have hcover : T ⊆ {z : ℂ | (1 : ℝ) / 2 < ‖z - (m : ℂ)‖}
      ∪ {z : ℂ | ‖z - (m : ℂ)‖ < (1 : ℝ) / 2} := by
    intro z hz
    obtain ⟨k, rfl⟩ := hsub hz
    rcases eq_or_ne k m with h | h
    · right; simp only [Set.mem_ofPred_eq]; rw [h, sub_self, norm_zero]; norm_num
    · left
      exact lt_of_lt_of_le (by norm_num) (one_le_norm_natCast_sub h)
  have hdisj : T ∩ ({z : ℂ | (1 : ℝ) / 2 < ‖z - (m : ℂ)‖}
      ∩ {z : ℂ | ‖z - (m : ℂ)‖ < (1 : ℝ) / 2}) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, _, h1, h2⟩
    exact absurd (show ‖z - (m : ℂ)‖ < 1 / 2 from h2)
      (not_lt.mpr (le_of_lt (show (1 : ℝ) / 2 < ‖z - (m : ℂ)‖ from h1)))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hT _ _ hu hv hcover hdisj) with hcon | hcon
  · have hmem : (1 : ℝ) / 2 < ‖(m : ℂ) - (m : ℂ)‖ := hcon hx
    rw [sub_self, norm_zero] at hmem
    exact absurd hmem (by norm_num)
  · have hmem : ‖(n : ℂ) - (m : ℂ)‖ < (1 : ℝ) / 2 := hcon hy
    exact absurd hmem (not_lt.mpr (le_trans (by norm_num) hone))

/-- For `c` near `c₀` the polynomial `Hp c` has exactly two roots in the disc. -/
theorem rootFilt_card_eq_two {z₁ : ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) {c₀ : ℂ}
    (hno : ∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.sphere z₁ r, (Hp c).eval z ≠ 0)
    (h0 : (rootFilt z₁ r c₀).card = 2) :
    ∀ c ∈ Metric.ball c₀ ρ, (rootFilt z₁ r c).card = 2 := by
  intro c hc
  have hcont : ContinuousOn (fun c => (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 0 c)
      (Metric.ball c₀ ρ) := (continuousOn_Pk hr hρ hno 0).const_mul _
  have himg : IsPreconnected ((fun c => (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 0 c)
      '' Metric.ball c₀ ρ) := (convex_ball c₀ ρ).isPreconnected.image _ hcont
  have hsub : ((fun c => (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 0 c) '' Metric.ball c₀ ρ)
      ⊆ Set.range (Nat.cast : ℕ → ℂ) := by
    rintro v ⟨w, hw, rfl⟩
    exact ⟨(rootFilt z₁ r w).card, (p0_eq_card hr (hno w hw)).symm⟩
  have hsingle := subsingleton_of_preconnected_subset_natCast himg hsub
  have heq : (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 0 c₀
      = (2 * ↑Real.pi * Complex.I)⁻¹ * Pk z₁ r 0 c :=
    hsingle ⟨c₀, Metric.mem_ball_self hρ, rfl⟩ ⟨c, hc, rfl⟩
  have h1 := p0_eq_card (z₁ := z₁) hr (c := c₀) (hno c₀ (Metric.mem_ball_self hρ))
  have h2 := p0_eq_card (z₁ := z₁) hr (c := c) (hno c hc)
  rw [h1] at heq
  rw [h2] at heq
  have : ((rootFilt z₁ r c₀).card : ℂ) = ((rootFilt z₁ r c).card : ℂ) := heq
  rw [h0] at this
  exact_mod_cast this.symm

/-- **The split pair exists.** -/
theorem splitPair_exists {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    ∃ ρ > 0, ∃ R > 0, ∃ m G : ℂ → ℂ,
      ContinuousOn m (Metric.ball c₀ ρ) ∧ ContinuousOn G (Metric.ball c₀ ρ) ∧
      m c₀ = d.z₁ ∧ G c₀ = 0 ∧
      (∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.ball d.z₁ R,
        (Work.EL.F c z = z ↔ (z - m c) ^ 2 = G c)) := by
  obtain ⟨r, hr, hno₀⟩ := exists_radius d
  have hsph : ∀ z ∈ Metric.sphere d.z₁ r, (Hp c₀).eval z ≠ 0 := by
    intro z hz hz0
    have hzmem : z ∈ Metric.closedBall d.z₁ r := by
      rw [Metric.mem_closedBall]; rw [Metric.mem_sphere] at hz; linarith
    have hz1 : z = d.z₁ := hno₀ z hzmem hz0
    rw [hz1, Metric.mem_sphere, dist_self] at hz
    linarith
  obtain ⟨ρ, hρ, hno⟩ := exists_param_ball_no_root hr hsph
  have hc0 : rootFilt d.z₁ r c₀ = 2 • ({d.z₁} : Multiset ℂ) := by
    obtain ⟨S, hS, hSeval⟩ := Hp_c0_double_root d
    have hSne : S ≠ 0 := fun h => hSeval (by rw [h]; simp)
    have hqne : ((X - C d.z₁) ^ 2 : ℂ[X]) ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero d.z₁)
    have hSroots : ∀ a ∈ S.roots, a ∉ Metric.ball d.z₁ r := by
      intro a ha hball
      have heval : S.eval a = 0 := (Polynomial.mem_roots hSne).mp ha
      have hHp : (Hp c₀).eval a = 0 := by
        rw [hS, Polynomial.eval_mul, Polynomial.eval_pow, heval, mul_zero]
      have haz : a = d.z₁ := hno₀ a (Metric.ball_subset_closedBall hball) hHp
      rw [haz] at heval
      exact hSeval heval
    have hfilterS : S.roots.filter (fun a => a ∈ Metric.ball d.z₁ r) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro a ha
      exact hSroots a ha
    have htarget : (((X - C d.z₁) ^ 2 : ℂ[X]).roots.filter
        (fun a => a ∈ Metric.ball d.z₁ r)) = 2 • ({d.z₁} : Multiset ℂ) := by
      rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C]
      rw [Multiset.filter_eq_self.mpr]
      intro a ha
      rw [Multiset.nsmul_singleton, Multiset.mem_replicate] at ha
      rw [ha.2]
      exact Metric.mem_ball_self hr
    rw [rootFilt, hS, Polynomial.roots_mul (mul_ne_zero hqne hSne), Multiset.filter_add,
      htarget, hfilterS, add_zero]
  have hcard0 : (rootFilt d.z₁ r c₀).card = 2 := by
    rw [hc0, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
  have hcard := rootFilt_card_eq_two (z₁ := d.z₁) hr hρ hno hcard0
  have hmemρ : c₀ ∈ Metric.ball c₀ ρ := Metric.mem_ball_self hρ
  have hp1₀ := p1_eq_sum (z₁ := d.z₁) (r := r) hr (hno c₀ hmemρ)
  have hp2₀ := p2_eq_sum (z₁ := d.z₁) (r := r) hr (hno c₀ hmemρ)
  refine ⟨ρ, hρ, r, hr, mP d.z₁ r, GP d.z₁ r, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : ContinuousOn (fun c => p1 d.z₁ r c) (Metric.ball c₀ ρ) :=
      (continuousOn_Pk hr hρ hno 1).const_mul _
    have heq : mP d.z₁ r = fun c => p1 d.z₁ r c * (1 / 2) := by
      funext c; rw [mP]; ring
    rw [heq]; exact hm.mul_const _
  · have h1 : ContinuousOn (fun c => p1 d.z₁ r c) (Metric.ball c₀ ρ) :=
      (continuousOn_Pk hr hρ hno 1).const_mul _
    have h2 : ContinuousOn (fun c => p2 d.z₁ r c) (Metric.ball c₀ ρ) :=
      (continuousOn_Pk hr hρ hno 2).const_mul _
    have heq : GP d.z₁ r = fun c => (2 * p2 d.z₁ r c - p1 d.z₁ r c ^ 2) * (1 / 4) := by
      funext c; rw [GP]; ring
    rw [heq]
    exact (((continuousOn_const.mul h2).sub (h1.pow 2)).mul_const _)
  · rw [mP, hp1₀, hc0, Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_eq_mul]
    ring
  · rw [GP, hp1₀, hp2₀, hc0]
    simp only [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.sum_singleton,
      Multiset.map_singleton, nsmul_eq_mul]
    ring
  · intro c hc z hz
    obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.mp (hcard c hc)
    have hpc := hno c hc
    have e1 : p1 d.z₁ r c = u + v := by
      rw [p1_eq_sum (z₁ := d.z₁) (r := r) hr hpc, huv]; simp
    have e2 : p2 d.z₁ r c = u ^ 2 + v ^ 2 := by
      rw [p2_eq_sum (z₁ := d.z₁) (r := r) hr hpc, huv]; simp
    have hm : mP d.z₁ r c = (u + v) / 2 := by rw [mP, e1]
    have hG : GP d.z₁ r c = ((u - v) / 2) ^ 2 := by rw [GP, e1, e2]; ring
    have hHpF : (Work.EL.F c z = z) ↔ ((Hp c).eval z = 0) := by
      rw [Hp_eval, sub_eq_zero]
    have hroot : ((Hp c).eval z = 0) ↔ z ∈ rootFilt d.z₁ r c := by
      rw [rootFilt, Multiset.mem_filter, Polynomial.mem_roots (Hp_ne_zero c),
        Polynomial.IsRoot.def]
      exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
    have hzf : (z ∈ rootFilt d.z₁ r c) ↔ z = u ∨ z = v := by
      rw [huv]; simp
    have hfac : (z - mP d.z₁ r c) ^ 2 - GP d.z₁ r c = (z - u) * (z - v) := by
      rw [hm, hG]; ring
    have hs : ((z - mP d.z₁ r c) ^ 2 = GP d.z₁ r c)
        ↔ ((z - mP d.z₁ r c) ^ 2 - GP d.z₁ r c = 0) := sub_eq_zero.symm
    have hfinal : ((z - mP d.z₁ r c) ^ 2 = GP d.z₁ r c) ↔ (z = u ∨ z = v) := by
      rw [hs, hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    rw [hHpF, hroot, hzf, hfinal]

end

end Work.PARIMPL.ParSplit
