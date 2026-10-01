import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_TuranOther_lFunctionOrderAddInvGammaR
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_TuranOther_completedLDerivZeroSum
import Submission.Work.LinnikAreas.TuranOther.invGammaRDerivZeroSum
import Submission.Work.LinnikAreas.TuranOther.levelFactorDerivZeroSum
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Reduction

/-!
# `Work.LinnikAreas.TuranOther.pfUncompleted`

The Hadamard partial-fraction expansion of the `k`-th derivative of the logarithmic derivative of
a (not necessarily primitive) Dirichlet `L`-function, at a point `t` with `1 < Re t`:

`(logDeriv L(·,χ))^{(k)}(t) = (-1)^k k! Σ_u ord_u(L(·,χ)) · (t-u)^{-(k+1)}`,

where the sum runs over the zeros of `L(·,χ)` with multiplicity (`analyticOrderNatAt`), i.e. the
non-trivial zeros, the trivial zeros `-a-2n` and — for an imprimitive `χ` — the zeros of the
level-correction factors `1 - χ*(p) p^{-s}`.

The proof decomposes `L(·,χ) = L(·,χ*) · ∏_p (1 - χ*(p) p^{-s})` and `L(·,χ*) = Λ(·,χ*)·(Γ_ℝ(·+a))⁻¹`
and uses the zero-sum expansion for each of the three kinds of factor.
-/

open scoped Classical BigOperators
open scoped Topology
open Filter

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-! ## Multiplicativity of the zero sum and of the differentiated logarithmic derivative -/

/-- The `k`-th derivative of the logarithmic derivative is additive over pointwise products:
`(logDeriv (f·g))^{(k)} = (logDeriv f)^{(k)} + (logDeriv g)^{(k)}` at any point where `f` and `g`
are entire and non-zero. -/
lemma iteratedDeriv_logDeriv_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {t : ℂ} (hft : f t ≠ 0) (hgt : g t ≠ 0) (k : ℕ) :
    iteratedDeriv k (logDeriv (fun z => f z * g z)) t
      = iteratedDeriv k (logDeriv f) t + iteratedDeriv k (logDeriv g) t := by
  have hft_an : AnalyticAt ℂ f t := hf.analyticAt t
  have hgt_an : AnalyticAt ℂ g t := hg.analyticAt t
  have hfl : AnalyticAt ℂ (logDeriv f) t := by
    rw [show logDeriv f = fun z => deriv f z / f z from funext (logDeriv_apply f)]
    exact (hft_an.deriv).div hft_an hft
  have hgl : AnalyticAt ℂ (logDeriv g) t := by
    rw [show logDeriv g = fun z => deriv g z / g z from funext (logDeriv_apply g)]
    exact (hgt_an.deriv).div hgt_an hgt
  have hev : logDeriv (fun z => f z * g z) =ᶠ[𝓝 t]
      fun z => logDeriv f z + logDeriv g z := by
    filter_upwards [hft_an.continuousAt.eventually_ne hft, hgt_an.continuousAt.eventually_ne hgt]
      with z hz1 hz2
    exact logDeriv_mul z hz1 hz2 (hf z) (hg z)
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev,
    iteratedDeriv_fun_add hfl.contDiffAt hgl.contDiffAt]

/-- `zeroSumK` is additive over pointwise products of entire functions. -/
lemma zeroSumK_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) {t : ℂ} {k : ℕ}
    (hsf : Summable fun u : ℂ =>
      ((analyticOrderNatAt f u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
    (hsg : Summable fun u : ℂ =>
      ((analyticOrderNatAt g u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)) :
    (Summable fun u : ℂ =>
        ((analyticOrderNatAt (fun z => f z * g z) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
      ∧ zeroSumK (fun z => f z * g z) t k = zeroSumK f t k + zeroSumK g t k := by
  have hpt : ∀ u : ℂ,
      ((analyticOrderNatAt (fun z => f z * g z) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)
        = ((analyticOrderNatAt f u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)
          + ((analyticOrderNatAt g u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) := by
    intro u
    have hord : analyticOrderNatAt (fun z => f z * g z) u
        = analyticOrderNatAt f u + analyticOrderNatAt g u := by
      change analyticOrderNatAt (f * g) u = (analyticOrderNatAt f u + analyticOrderNatAt g u)
      exact analyticOrderNatAt_mul_of_differentiable hf hg hf0 hg0 u
    rw [hord]
    push_cast
    ring
  constructor
  · exact (hsf.add hsg).congr (fun u => (hpt u).symm)
  · unfold zeroSumK
    rw [tsum_congr hpt, Summable.tsum_add hsf hsg]

/-- Two functions with the same vanishing orders have the same zero sum. -/
lemma zeroSumK_congr {f g : ℂ → ℂ} {t : ℂ} {k : ℕ}
    (h : ∀ u : ℂ, analyticOrderNatAt f u = analyticOrderNatAt g u) :
    zeroSumK f t k = zeroSumK g t k := by
  unfold zeroSumK
  exact tsum_congr (fun u => by rw [h u])

/-- The constant function `1` has vanishing order `0` everywhere. -/
lemma analyticOrderNatAt_one (u : ℂ) :
    analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u = 0 := by
  have h : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) u = 0 :=
    (analyticAt_const (v := (1 : ℂ)) (x := u)).analyticOrderAt_eq_zero.mpr one_ne_zero
  simp [analyticOrderNatAt, h]

/-- The zero sum of the constant function `1` vanishes. -/
lemma zeroSumK_one (t : ℂ) (k : ℕ) :
    zeroSumK (fun _ : ℂ => (1 : ℂ)) t k = 0 := by
  unfold zeroSumK
  simp [analyticOrderNatAt_one]

/-- The logarithmic derivative of the constant function `1` vanishes, hence so do all its
iterated derivatives. -/
lemma iteratedDeriv_logDeriv_one (t : ℂ) (k : ℕ) :
    iteratedDeriv k (logDeriv (fun _ : ℂ => (1 : ℂ))) t = 0 := by
  have h : logDeriv (fun _ : ℂ => (1 : ℂ)) = fun _ : ℂ => 0 := by
    funext z
    rw [logDeriv_apply]
    simp
  rw [h]
  exact iteratedDeriv_fun_const_zero

/-! ## Finite products -/

/-- A finite product of entire functions is entire. -/
lemma diff_finsetProd {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, Differentiable ℂ (F i)) :
    Differentiable ℂ (fun z => ∏ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiable_const (1 : ℂ)
  | insert a s ha ih =>
      have h1 : Differentiable ℂ (fun z => ∏ i ∈ s, F i z) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have h2 : Differentiable ℂ (F a) := h a (Finset.mem_insert_self a s)
      have h3 : Differentiable ℂ (fun z => F a z * ∏ i ∈ s, F i z) := h2.mul h1
      simpa only [Finset.prod_insert ha] using h3

/-- Summability and additivity of the zero sum over a finite product of entire functions. -/
lemma zeroSumK_finsetProd {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z₀ : ℂ) (t : ℂ) (k : ℕ)
    (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (hF0 : ∀ i ∈ s, F i z₀ ≠ 0)
    (hsum : ∀ i ∈ s, Summable fun u : ℂ =>
      ((analyticOrderNatAt (F i) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)) :
    (Summable fun u : ℂ =>
        ((analyticOrderNatAt (fun z => ∏ i ∈ s, F i z) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
      ∧ zeroSumK (fun z => ∏ i ∈ s, F i z) t k = ∑ i ∈ s, zeroSumK (F i) t k := by
  classical
  revert hF hF0 hsum
  induction s using Finset.induction_on with
  | empty =>
      intro hF hF0 hsum
      have hone : (fun z : ℂ => ∏ i ∈ (∅ : Finset ι), F i z) = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp
      rw [hone]
      constructor
      · have h0 : (fun u : ℂ =>
            ((analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
            = fun _ : ℂ => 0 := by
          funext u; rw [analyticOrderNatAt_one]; simp
        rw [h0]
        exact summable_zero
      · rw [zeroSumK_one, Finset.sum_empty]
  | insert a s ha ih =>
      intro hF hF0 hsum
      have hF' : ∀ i ∈ s, Differentiable ℂ (F i) :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hF0' : ∀ i ∈ s, F i z₀ ≠ 0 :=
        fun i hi => hF0 i (Finset.mem_insert_of_mem hi)
      have hsum' : ∀ i ∈ s, Summable fun u : ℂ =>
          ((analyticOrderNatAt (F i) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) :=
        fun i hi => hsum i (Finset.mem_insert_of_mem hi)
      obtain ⟨hsumG, hGid⟩ := ih hF' hF0' hsum'
      have hFad : Differentiable ℂ (F a) := hF a (Finset.mem_insert_self a s)
      have hFa0 : F a z₀ ≠ 0 := hF0 a (Finset.mem_insert_self a s)
      have hFa0' : F a ≠ 0 := fun h => hFa0 (congr_fun h z₀)
      have hsuma : Summable fun u : ℂ =>
          ((analyticOrderNatAt (F a) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) :=
        hsum a (Finset.mem_insert_self a s)
      have hGdiff : Differentiable ℂ (fun z => ∏ i ∈ s, F i z) := diff_finsetProd s F hF'
      have hG0 : (fun z => ∏ i ∈ s, F i z) ≠ 0 := by
        intro h
        have hz := congr_fun h z₀
        simp only [Pi.zero_apply] at hz
        exact (Finset.prod_ne_zero_iff.mpr hF0') hz
      have hprod : (fun z : ℂ => ∏ i ∈ insert a s, F i z)
          = fun z => F a z * ∏ i ∈ s, F i z := by
        funext z; exact Finset.prod_insert ha
      obtain ⟨hsumP, hP⟩ := zeroSumK_mul hFad hGdiff hFa0' hG0 hsuma hsumG
      have hsumP' : Summable fun u : ℂ =>
          ((analyticOrderNatAt (fun z : ℂ => ∏ i ∈ insert a s, F i z) u : ℕ) : ℂ)
            * (t - u) ^ (-(k + 1) : ℤ) := by
        rw [hprod]
        exact hsumP
      refine ⟨hsumP', ?_⟩
      rw [hprod, hP, hGid, Finset.sum_insert ha]

/-- Additivity of the differentiated logarithmic derivative over a finite product. -/
lemma iteratedDeriv_logDeriv_finsetProd {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (t : ℂ) (k : ℕ)
    (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (ht : ∀ i ∈ s, F i t ≠ 0) :
    iteratedDeriv k (logDeriv (fun z => ∏ i ∈ s, F i z)) t
      = ∑ i ∈ s, iteratedDeriv k (logDeriv (F i)) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hone : (fun z : ℂ => ∏ i ∈ (∅ : Finset ι), F i z) = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp
      rw [hone, iteratedDeriv_logDeriv_one, Finset.sum_empty]
  | insert a s ha ih =>
      have hF' : ∀ i ∈ s, Differentiable ℂ (F i) :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have ht' : ∀ i ∈ s, F i t ≠ 0 := fun i hi => ht i (Finset.mem_insert_of_mem hi)
      have hGt : (∏ i ∈ s, F i t) ≠ 0 := Finset.prod_ne_zero_iff.mpr ht'
      have hGdiff : Differentiable ℂ (fun z => ∏ i ∈ s, F i z) := diff_finsetProd s F hF'
      have hprod : (fun z : ℂ => ∏ i ∈ insert a s, F i z)
          = fun z => F a z * ∏ i ∈ s, F i z := by
        funext z; exact Finset.prod_insert ha
      rw [hprod, iteratedDeriv_logDeriv_mul (hF a (Finset.mem_insert_self a s)) hGdiff
        (ht a (Finset.mem_insert_self a s)) hGt k, ih hF' ht', Finset.sum_insert ha]

/-- Values of a Dirichlet character at units have norm one. -/
lemma norm_apply_eq_one_of_isUnit {n : ℕ} (χ : DirichletCharacter ℂ n) {a : ZMod n}
    (ha : IsUnit a) : ‖χ a‖ = 1 := by
  rw [← ha.unit_spec]
  exact χ.unit_norm_eq_one ha.unit

/-! ## The trivial level-correction factor -/

/-- A level-correction factor which is identically `1` satisfies the zero-sum expansion
trivially. -/
lemma levelFactorZeroSum_triv {c : ℕ} {χ : DirichletCharacter ℂ c} {p : ℕ}
    (hp : χ (p : ZMod c) = 0) (k : ℕ) {t : ℂ} :
    (Summable fun u : ℂ =>
        ((analyticOrderNatAt (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ))
      ∧ iteratedDeriv k (logDeriv (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) t
        = (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * zeroSumK (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t k := by
  have hfun : (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) = fun _ : ℂ => (1 : ℂ) := by
    funext s
    rw [hp]
    simp
  rw [hfun]
  constructor
  · have h0 : (fun u : ℂ =>
        ((analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
        = fun _ : ℂ => 0 := by
      funext u; rw [analyticOrderNatAt_one]; simp
    rw [h0]
    exact summable_zero
  · rw [iteratedDeriv_logDeriv_one, zeroSumK_one]
    ring

/-! ## The level-correction product -/

/-- Every level-correction factor of a non-principal character is non-zero at a point with
`1 < Re t`. -/
lemma levelFactor_ne_zero {c : ℕ} (χ : DirichletCharacter ℂ c) {p : ℕ} (hp : 1 < p) {t : ℂ}
    (ht : 1 < t.re) : (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t ≠ 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hnorm : ‖χ (p : ZMod c) * (p : ℂ) ^ (-t)‖ < 1 := by
    rw [norm_mul]
    have h1 : ‖χ (p : ZMod c)‖ ≤ 1 := χ.norm_le_one _
    have hpcast : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
    have h2 : ‖(p : ℂ) ^ (-t)‖ = (p : ℝ) ^ (-t.re) := by
      rw [hpcast, Complex.norm_cpow_eq_rpow_re_of_pos (x := (p : ℝ)) hp0]
      simp
    have h3 : (p : ℝ) ^ (-t.re) < 1 := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      have h := Real.rpow_lt_rpow_of_exponent_lt hp1 (show (-t.re) < (0 : ℝ) by linarith)
      simpa using h
    calc ‖χ (p : ZMod c)‖ * ‖(p : ℂ) ^ (-t)‖
        ≤ 1 * (p : ℝ) ^ (-t.re) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (p : ℝ) ^ (-t.re) := one_mul _
      _ < 1 := h3
  have hne : χ (p : ZMod c) * (p : ℂ) ^ (-t) ≠ 1 := by
    intro h
    rw [h, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  exact sub_ne_zero.mpr (Ne.symm hne)

/-- A single level-correction factor is entire. -/
lemma levelFactor_differentiable {c : ℕ} (χ : DirichletCharacter ℂ c) {p : ℕ} (hp : p ≠ 0) :
    Differentiable ℂ (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hfun : (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))
      = fun s : ℂ => 1 - χ (p : ZMod c) * Complex.exp (Complex.log (p : ℂ) * (-s)) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hpc]
  rw [hfun]
  fun_prop

/-- **The level-correction product.**  The product `∏_{p | q} (1 - χ(p) p^{-s})` satisfies the
zero-sum expansion in every order `k ≥ 1` at every point `t` with `1 < Re t`.  This is the
imprimitive correction to the `L`-function: the fact that the factors with `p ∣ conductor` are
identically `1` is what allows the same statement to cover both imprimitive and primitive `χ`. -/
lemma levelProdZeroSum {c q : ℕ} [NeZero c] [NeZero q] (χ : DirichletCharacter ℂ c)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    (Summable fun u : ℂ =>
        ((analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors,
          (1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ))
      ∧ iteratedDeriv k (logDeriv (fun s : ℂ => ∏ p ∈ q.primeFactors,
          (1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)))) t
        = (-1 : ℂ) ^ k * (k.factorial : ℂ)
          * zeroSumK (fun s : ℂ => ∏ p ∈ q.primeFactors,
              (1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) t k := by
  classical
  have hpiece : ∀ p ∈ q.primeFactors,
      (Summable fun u : ℂ =>
          ((analyticOrderNatAt (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) u : ℕ) : ℂ)
            * (t - u) ^ (-(k + 1) : ℤ))
        ∧ iteratedDeriv k (logDeriv (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) t
          = (-1 : ℂ) ^ k * (k.factorial : ℂ)
            * zeroSumK (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t k := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    by_cases hpc : p ∣ c
    · refine levelFactorZeroSum_triv ?_ k
      refine MulChar.map_nonunit χ ?_
      intro h
      exact (Nat.Prime.coprime_iff_not_dvd hprime).mp
        ((ZMod.isUnit_iff_coprime p c).mp h) hpc
    · have hnorm : ‖χ (p : ZMod c)‖ = 1 :=
        norm_apply_eq_one_of_isUnit χ ((ZMod.isUnit_iff_coprime p c).mpr
          ((Nat.Prime.coprime_iff_not_dvd hprime).mpr hpc))
      exact levelFactorDerivZeroSum hprime (χ (p : ZMod c)) hnorm k hk ht
  have hFd : ∀ p ∈ q.primeFactors,
      Differentiable ℂ (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) := by
    intro p hp
    exact levelFactor_differentiable χ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hFt : ∀ p ∈ q.primeFactors,
      (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t ≠ 0 := by
    intro p hp
    exact levelFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp).one_lt ht
  have hsum' : Summable fun u : ℂ =>
      ((analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors,
        (1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) u : ℕ) : ℂ)
        * (t - u) ^ (-(k + 1) : ℤ) :=
    (zeroSumK_finsetProd q.primeFactors
      (fun p s => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t t k hFd hFt
      (fun p hp => (hpiece p hp).1)).1
  have hzs' : zeroSumK (fun s : ℂ => ∏ p ∈ q.primeFactors,
        (1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) t k
      = ∑ p ∈ q.primeFactors, zeroSumK
          (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t k :=
    (zeroSumK_finsetProd q.primeFactors
      (fun p s => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t t k hFd hFt
      (fun p hp => (hpiece p hp).1)).2
  have hder' : iteratedDeriv k (logDeriv (fun s : ℂ => ∏ p ∈ q.primeFactors,
        (1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)))) t
      = ∑ p ∈ q.primeFactors, iteratedDeriv k (logDeriv
          (fun s : ℂ => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s))) t :=
    iteratedDeriv_logDeriv_finsetProd q.primeFactors
      (fun p s => 1 - χ (p : ZMod c) * (p : ℂ) ^ (-s)) t k hFd hFt
  refine ⟨hsum', ?_⟩
  rw [hder', hzs', Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p hp => (hpiece p hp).2)

/-! ## Splitting `L` into the completed `L`-function and the inverse archimedean factor -/

/-- **The `L(·,χ)` zero sum splits as the `Λ(·,χ)` zero sum plus the trivial-zero sum.**
For a non-principal (possibly imprimitive) `χ` and the parity integer `a ∈ {0,1}`, the identity
`L = Λ · (Γ_ℝ(·+a))⁻¹` of entire functions gives, in every order `k ≥ 1` and at every `t` with
`1 < Re t`, both the corresponding additive identities (for the zero sums and for the `k`-th
derivatives of the logarithmic derivatives) and the summability of the `L`-summand. -/
lemma lFunctionZeroSum_eq {c : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (a : ℕ) (ha0 : χ.Even → a = 0) (ha1 : χ.Odd → a = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    (Summable fun u : ℂ =>
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
      ∧ zeroSumK (DirichletCharacter.LFunction χ) t k
          = zeroSumK (DirichletCharacter.completedLFunction χ) t k
            + zeroSumK (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) t k
      ∧ iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t
          = iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) t
            + iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t := by
  classical
  have hcne1 : c ≠ 1 := Work.LinnikAreas.DhK.level_ne_one_of_ne_one hχ
  have hfun : DirichletCharacter.LFunction χ
      = fun z : ℂ => DirichletCharacter.completedLFunction χ z * (Complex.Gammaℝ (z + a))⁻¹ := by
    funext z
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hcne1), div_eq_mul_inv]
    congr 1
    rcases χ.even_or_odd with hE | hO
    · rw [ha0 hE, show DirichletCharacter.gammaFactor χ = Complex.Gammaℝ from
        funext (fun w => hE.gammaFactor_def w)]
      simp
    · rw [ha1 hO, show DirichletCharacter.gammaFactor χ
          = (fun w : ℂ => Complex.Gammaℝ (w + 1)) from
        funext (fun w => hO.gammaFactor_def w)]
      simp
  have hLt : DirichletCharacter.LFunction χ t ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (le_of_lt ht)
  have hΓt : (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) t ≠ 0 := by
    have h : Complex.Gammaℝ (t + a) ≠ 0 := by
      refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
      have h1 : (t + (a : ℂ)).re = t.re + (a : ℝ) := by simp
      rw [h1]
      have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      linarith
    simpa using inv_ne_zero h
  have hΛt : DirichletCharacter.completedLFunction χ t ≠ 0 := by
    have hγ : DirichletCharacter.gammaFactor χ t ≠ 0 := by
      rcases Work.LinnikAreas.DhK.gammaFactor_eq_Gammaℝ_or χ with h | h
      · rw [h]
        exact Work.LinnikAreas.DhK.Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < t.re)
      · rw [h]
        exact Work.LinnikAreas.DhK.Gammaℝ_add_one_ne_zero_of_re_pos (by linarith : 0 < t.re)
    rw [Work.LinnikAreas.DhK.completedLFunction_eq_L_mul_gammaFactor χ hχ t hγ]
    exact mul_ne_zero hLt hγ
  have hΓdiff : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (a : ℂ))
  obtain ⟨hsumΛ, hΛid⟩ := completedLDerivZeroSum χ hχ hprim k hk ht
  have ha01 : a = 0 ∨ a = 1 := χ.even_or_odd.imp (fun h => ha0 h) (fun h => ha1 h)
  obtain ⟨hsumΓ, hΓid⟩ := invGammaRDerivZeroSum a ha01 k hk ht
  have hpt : ∀ u : ℂ,
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)
        + ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)
        = ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ) := by
    intro u
    rw [show analyticOrderNatAt (DirichletCharacter.LFunction χ) u
        = analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u
          + analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u from
      lFunctionOrderAddInvGammaR χ hχ a ha0 ha1 u]
    push_cast
    ring
  have hsumL : Summable fun u : ℂ =>
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ)
        * (t - u) ^ (-(k + 1) : ℤ) :=
    (hsumΛ.add hsumΓ).congr hpt
  have hzspt : ∀ u : ℂ,
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ)
          * (t - u) ^ (-(k + 1) : ℤ)
        = ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ)
            * (t - u) ^ (-(k + 1) : ℤ)
          + ((analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u : ℕ) : ℂ)
            * (t - u) ^ (-(k + 1) : ℤ) := by
    intro u
    rw [show analyticOrderNatAt (DirichletCharacter.LFunction χ) u
        = analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u
          + analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u from
      lFunctionOrderAddInvGammaR χ hχ a ha0 ha1 u]
    push_cast
    ring
  have hzsL : zeroSumK (DirichletCharacter.LFunction χ) t k
      = zeroSumK (DirichletCharacter.completedLFunction χ) t k
        + zeroSumK (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) t k := by
    unfold zeroSumK
    rw [tsum_congr hzspt, Summable.tsum_add hsumΛ hsumΓ]
  have hmul : iteratedDeriv k (logDeriv (fun z : ℂ =>
        DirichletCharacter.completedLFunction χ z * (Complex.Gammaℝ (z + a))⁻¹)) t
      = iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) t
        + iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t :=
    iteratedDeriv_logDeriv_mul (DirichletCharacter.differentiable_completedLFunction hχ)
      hΓdiff hΛt hΓt k
  have hderL : iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t
      = iteratedDeriv k (logDeriv (DirichletCharacter.completedLFunction χ)) t
        + iteratedDeriv k (logDeriv (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹)) t := by
    rw [show (fun z : ℂ => DirichletCharacter.completedLFunction χ z * (Complex.Gammaℝ (z + a))⁻¹)
        = DirichletCharacter.LFunction χ from hfun.symm] at hmul
    exact hmul
  exact ⟨hsumL, hzsL, hderL⟩

/-! ## Assembly -/

/-- The zero-sum expansion for a non-principal character with a prescribed parity shift. -/
lemma lFunction_hasZeroSum_of_parity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1)
    (a : ℕ) (ha0 : χ.primitiveCharacter.Even → a = 0)
    (ha1 : χ.primitiveCharacter.Odd → a = 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    HasZeroSumExpansion (DirichletCharacter.LFunction χ) t k := by
  classical
  have hχs1 : χ.primitiveCharacter ≠ 1 := Work.LinnikAreas.DhK.primitiveCharacter_ne_one hχ
  have hχsp : (χ.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  -- the level-correction product
  obtain ⟨hsumE, hderE⟩ :=
    levelProdZeroSum (c := χ.conductor) (q := q) (χ.primitiveCharacter) k hk ht
  -- the primitive part
  obtain ⟨hsumLs, hzsLs, hderLs⟩ :=
    lFunctionZeroSum_eq (c := χ.conductor) (χ.primitiveCharacter) hχs1 hχsp a ha0 ha1 k hk ht
  -- the factorisation `L(·,χ) = L(·,χ*) · ∏_p (...)`
  have hLfac : DirichletCharacter.LFunction χ
      = fun s : ℂ => DirichletCharacter.LFunction (χ.primitiveCharacter) s
          * ∏ p ∈ q.primeFactors,
              (1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) := by
    funext s
    have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level (χ.primitiveCharacter)
      (s := s) (Or.inl hχs1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter χ] at h
    exact h
  have hLst : DirichletCharacter.LFunction (χ.primitiveCharacter) t ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ.primitiveCharacter)
      (Or.inl hχs1) (le_of_lt ht)
  have hEt : (fun s : ℂ => ∏ p ∈ q.primeFactors,
      (1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))) t ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    exact levelFactor_ne_zero (χ.primitiveCharacter) (Nat.prime_of_mem_primeFactors hp).one_lt ht
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction (χ.primitiveCharacter)) :=
    DirichletCharacter.differentiable_LFunction hχs1
  have hEdiff : Differentiable ℂ (fun s : ℂ => ∏ p ∈ q.primeFactors,
      (1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))) :=
    diff_finsetProd q.primeFactors
      (fun p s => 1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))
      (fun p hp => levelFactor_differentiable (χ.primitiveCharacter)
        (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hLsne : DirichletCharacter.LFunction (χ.primitiveCharacter) ≠ 0 :=
    fun h => hLst (congr_fun h t)
  obtain ⟨-, hΛid⟩ := completedLDerivZeroSum (χ.primitiveCharacter) hχs1 hχsp k hk ht
  have ha01 : a = 0 ∨ a = 1 :=
    (χ.primitiveCharacter).even_or_odd.imp (fun h => ha0 h) (fun h => ha1 h)
  obtain ⟨-, hΓid⟩ := invGammaRDerivZeroSum a ha01 k hk ht
  have hEne : (fun s : ℂ => ∏ p ∈ q.primeFactors,
      (1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))) ≠ 0 :=
    fun h => hEt (congr_fun h t)
  have hszL : zeroSumK (DirichletCharacter.LFunction χ) t k
      = zeroSumK (DirichletCharacter.LFunction (χ.primitiveCharacter)) t k
        + zeroSumK (fun s : ℂ => ∏ p ∈ q.primeFactors,
            (1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))) t k := by
    rw [hLfac]
    exact (zeroSumK_mul hLdiff hEdiff hLsne hEne hsumLs hsumE).2
  have hderLχ : iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t
      = iteratedDeriv k (logDeriv (DirichletCharacter.LFunction (χ.primitiveCharacter))) t
        + iteratedDeriv k (logDeriv (fun s : ℂ => ∏ p ∈ q.primeFactors,
            (1 - (χ.primitiveCharacter) (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)))) t := by
    rw [hLfac]
    exact iteratedDeriv_logDeriv_mul hLdiff hEdiff hLst hEt k
  have hkey : (-1 : ℂ) ^ k * (k.factorial : ℂ) * zeroSumK (DirichletCharacter.LFunction χ) t k
      = iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t := by
    rw [hszL, hzsLs, hderLχ, hderLs, hΛid, hΓid, hderE]
    ring
  exact hkey.symm

theorem pfUncompleted {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    iteratedDeriv k (fun z => logDeriv (DirichletCharacter.LFunction χ) z) t =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) *
        ∑' u : ℂ, ((Work.LinnikAreas.TuranOther.multL χ u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rcases χ.primitiveCharacter.even_or_odd with hEv | hOd
  · exact lFunction_hasZeroSum_of_parity χ hχ 0 (fun _ => rfl)
      (fun h => absurd h hEv.not_odd) k hk ht
  · exact lFunction_hasZeroSum_of_parity χ hχ 1 (fun h => absurd h hOd.not_even)
      (fun _ => rfl) k hk ht

end Work.LinnikAreas.TuranOther
