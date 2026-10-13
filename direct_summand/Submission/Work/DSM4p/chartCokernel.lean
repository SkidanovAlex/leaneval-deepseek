import Mathlib
import Submission.Work.DSM4p.Reduction
import Submission.Work.DSM4p.ChartUnit
import Submission.Work.DSM4p.chartMono_estimate

/-!
# DSM4p — the cokernel clause of the chart tower at the uniform constant `retC`

This module proves `Work.DSM4p.ChartCokernel`, the cokernel half of the QRET condition
`Work.DSM4p.IsQRETAt` for the chart model `D n = chartLevel hgr Q.ϖ n ⊆ B[1/g]` of
`Submission/Work/DSM4p/Chart.lean`, at the *uniform* constant `retC p k m = p^(k+1) · m`
(Bhatt, *The direct summand conjecture and its derived variant*, arXiv:1608.08882, Theorem
3.1(2) together with Remark 3.2, renormalised from the paper's `t^m` to `p^m`).

The statement is Bhatt's: for every `m, k` and every `y` in the level `n + c`
(`c := retC p k m`), the element `ϖ_k g_k · y` is congruent modulo `p^m · D n` to an element
of `B` (`g = gr 0`, `ϖ_k g_k = (ϖ g)^{1/p^k}`).

## The proof

* `chartLevel_mem_aeval_range` writes `y` as a polynomial `P` in the generators
  `x_j(n+c) = ϖ_j^{n+c}/g_j` of the level `n+c`;
* `prod_chartGen_pow_eq` collapses each monomial `∏_j x_j(n+c)^{μ_j}` to a single generator
  power `x_J(n+c)^I` with `J = max (support μ)`, `I = ∑_j μ_j · p^{J-j}` (the iterated root
  relation `x_j = x_J^{p^{J-j}}`, `Work.DSM4p.chartGen_eq_root_pow`);
* `chartMono_coeff` is the resulting per-monomial estimate, obtained from the colleague's
  `Work.DSM4p.chartMono_estimate` (Bhatt's two-case computation) by scaling with the
  `B`-coefficient of the monomial, the target `p^m · D n` being a `B`-submodule;
* summing the finitely many per-monomial congruences yields a witness `∑_μ x_μ ∈ B` for the
  whole polynomial;
* `mem_ideal_span_smul_toSubmodule_iff` finally converts the ambient membership in
  `(Ideal.span {(p : B)}^m) • (chartLevel n).toSubmodule ⊆ B[1/g]` into membership in
  `Ideal.span {(p : D n)^m}` inside the level ring `D n = chartLevel hgr Q.ϖ n`, which is the
  form in which `Work.DSM4p.ChartCokernel` is stated (`iterTr` of the tower inclusions is the
  coercion, `Work.DSM4p.chartIterTr_coe`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

/-! ## Converting `p^m`-multiples of a subalgebra between ambient and level form -/

/-- For a `B`-subalgebra `D` of a `B`-algebra `A` and `r : B`, the `r`-multiples of `D` inside
`A` are exactly the elements of the ideal `Ideal.span {algebraMap B D r}` of `D`, viewed in `A`:
localisation-free form of the identity
`(Ideal.span {r}) • D.toSubmodule = Submodule.map D.val (Ideal.span {algebraMap B D r})`. -/
theorem mem_ideal_span_smul_toSubmodule_iff {B : Type*} {A : Type*} [CommRing B] [CommRing A]
    [Algebra B A] (D : Subalgebra B A) (r : B) (z : D) :
    (z : A) ∈ (Ideal.span {r}) • D.toSubmodule ↔ z ∈ Ideal.span {algebraMap B D r} := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, hwz⟩
    refine Ideal.mem_span_singleton'.mpr ⟨⟨w, (Subalgebra.mem_toSubmodule D).mp hw⟩, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, mul_comm, ← Algebra.smul_def]
    exact hwz
  · intro hz
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨(u : A), u.2, ?_⟩
    rw [Algebra.smul_def, ← Subalgebra.coe_algebraMap (S := D) (r := r), ← Subalgebra.coe_mul,
      mul_comm (algebraMap B D r) u, hu]

/-! ## Collapsing a monomial to a single generator power -/

/-- Iterated form of the root relation `x_k(N) = x_{k+1}(N)^p` of `Work.DSM4p.chartGen_succ_pow`:
`x_k(N) = x_{k+d}(N)^{p^d}`. -/
theorem chartGen_eq_pow_add {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (gr : ℕ → B) (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (hϖ : IsRootSystem p ϖ) (N : ℕ) :
    ∀ d k : ℕ, chartGen hgr ϖ N k = (chartGen hgr ϖ N (k + d)) ^ p ^ d := by
  intro d
  induction d with
  | zero => intro k; simp
  | succ d ih =>
    intro k
    rw [ih k, chartGen_succ_pow hgr hϖ N (k + d), ← pow_mul, pow_succ',
      show k + (d + 1) = k + d + 1 from rfl]

/-- The root relation `x_j(N) = x_J(N)^{p^{J-j}}` for `j ≤ J`. -/
theorem chartGen_eq_root_pow {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (gr : ℕ → B) (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (hϖ : IsRootSystem p ϖ)
    (N j J : ℕ) (h : j ≤ J) :
    chartGen hgr ϖ N j = (chartGen hgr ϖ N J) ^ p ^ (J - j) := by
  have := chartGen_eq_pow_add gr hgr ϖ hϖ N (J - j) j
  rwa [Nat.add_sub_cancel' h] at this

/-- A product of powers of the chart generators is a single power of the generator at the top
index: for `J` above the support of `μ`,
`∏_j x_j(n)^{μ_j} = x_J(n)^{∑_j μ_j · p^{J-j}}`.
This is the iterated root relation `x_j(n) = x_{j+1}(n)^p`
(`Work.DSM4p.chartGen_succ_pow`). -/
theorem prod_chartGen_pow_eq {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (gr : ℕ → B) (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (hϖ : IsRootSystem p ϖ)
    (N : ℕ) (μ : ℕ →₀ ℕ) (J : ℕ) (hJ : ∀ j ∈ μ.support, j ≤ J) :
    ∏ j ∈ μ.support, (chartGen hgr ϖ N j) ^ (μ j) =
      (chartGen hgr ϖ N J) ^ (∑ j ∈ μ.support, μ j * p ^ (J - j)) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [chartGen_eq_root_pow gr hgr ϖ hϖ N j J (hJ j hj), ← pow_mul, mul_comm]

/-! ## The per-monomial estimate with a `B`-coefficient -/

/-- Per-monomial case of the cokernel clause of the QRET condition for the chart tower: for a
monomial `μ` and a coefficient `b : B`, the element `ϖ_k g_k · b · ∏_j x_j(n+c)^{μ_j}` is
congruent modulo `p^m · D n` to an element of `B`.  This is Bhatt's estimate
`Work.DSM4p.chartMono_estimate` (`x_J(n+c)^I`, `J = max (support μ)`, `I = ∑_j μ_j p^{J-j}`),
scaled by `b`; the target `(Ideal.span {(p : B)}^m) • (chartLevel n).toSubmodule` is a
`B`-submodule, hence stable under `b • -`. -/
theorem chartMono_coeff {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : IsRootSystem p gr)
    (m k c n : ℕ) (hc : p ^ (k + 1) * m ≤ c) (μ : ℕ →₀ ℕ) (b : B) :
    ∃ x : B, algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) *
        (algebraMap B (ChartAmbient gr) b *
          ∏ j ∈ μ.support, (chartGen hgr Q.ϖ (n + c) j) ^ (μ j)) -
        algebraMap B (ChartAmbient gr) x ∈
      (Ideal.span {(p : B)} ^ m) • (chartLevel hgr Q.ϖ n).toSubmodule := by
  obtain ⟨x₀, hx₀⟩ := chartMono_estimate Q gr hgr m k c (μ.support.sup id)
    (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j)) n hc
  refine ⟨b * x₀, ?_⟩
  rw [prod_chartGen_pow_eq gr hgr Q.ϖ Q.root (n + c) μ (μ.support.sup id)
    (fun j hj => Finset.le_sup (f := id) hj)]
  have hkey (X : ChartAmbient gr) :
      algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) *
          (algebraMap B (ChartAmbient gr) b * X) -
        algebraMap B (ChartAmbient gr) (b * x₀) =
      b • (algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) * X -
        algebraMap B (ChartAmbient gr) x₀) := by
    rw [Algebra.smul_def, map_mul (algebraMap B (ChartAmbient gr)) b x₀,
      map_mul (algebraMap B (ChartAmbient gr)) (Q.ϖ k) (gr k)]
    ring
  rw [hkey]
  exact Submodule.smul_mem _ b hx₀

/-! ## The cokernel clause -/

theorem chartCokernel {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr) (m k : ℕ) :
    Work.DSM4p.ChartCokernel Q gr hgr m k := by
  intro n y
  obtain ⟨P, hP⟩ := chartLevel_mem_aeval_range hgr Q.ϖ (n + retC p k m) y
  choose w hw using fun μ : ℕ →₀ ℕ =>
    chartMono_coeff Q gr hgr m k (retC p k m) n le_rfl μ (P.coeff μ)
  refine ⟨∑ μ ∈ P.support, w μ, ?_⟩
  set z : chartRing hgr Q.ϖ n :=
    algebraMap B (chartRing hgr Q.ϖ n) (Q.ϖ k * gr k) *
        iterTr (chartTr hgr Q.ϖ) n (retC p k m) y -
      algebraMap B (chartRing hgr Q.ϖ n) (∑ μ ∈ P.support, w μ) with hzdef
  have hexp : (y : ChartAmbient gr) =
      ∑ μ ∈ P.support, algebraMap B (ChartAmbient gr) (P.coeff μ) *
        ∏ j ∈ μ.support, (chartGen hgr Q.ϖ (n + retC p k m) j) ^ (μ j) := by
    conv_lhs => rw [← hP, MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.aeval_monomial]
    rfl
  have hmem : algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) * (y : ChartAmbient gr) -
        algebraMap B (ChartAmbient gr) (∑ μ ∈ P.support, w μ) ∈
      (Ideal.span {(p : B)} ^ m) • (chartLevel hgr Q.ϖ n).toSubmodule := by
    rw [hexp, Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib]
    exact Submodule.sum_mem _ fun μ _ => hw μ
  have hzcoe : (z : ChartAmbient gr) =
      algebraMap B (ChartAmbient gr) (Q.ϖ k * gr k) * (y : ChartAmbient gr) -
        algebraMap B (ChartAmbient gr) (∑ μ ∈ P.support, w μ) := by
    rw [hzdef]
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    rw [chartIterTr_coe Q gr hgr n (retC p k m) y]
  have hpD : algebraMap B (chartRing hgr Q.ϖ n) ((p : B) ^ m) =
      ((p : chartRing hgr Q.ϖ n)) ^ m := by
    rw [map_pow, map_natCast]
  change z ∈ Ideal.span {((p : chartRing hgr Q.ϖ n)) ^ m}
  rw [← hpD, ← mem_ideal_span_smul_toSubmodule_iff (chartLevel hgr Q.ϖ n) ((p : B) ^ m) z,
    ← Ideal.span_singleton_pow, hzcoe]
  exact hmem

end Work.DSM4p
