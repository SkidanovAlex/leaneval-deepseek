import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Work.LinnikAreas.TuranOther.twMultMax
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_zetaZeroPowerId
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_pfUncompleted
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_primitiveLZeroPowerId
import Submission.Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul
import Submission.Work.LinnikAreas.TuranOther.levelFacZeroSumAlt
import Submission.Work.LinnikAreas.TuranOther.positivityArith

/-!
# `Work.LinnikAreas.TuranOther.twUpper`

The Hadamard-product upper bound for the twisted Turán power sum.

The proof combines the Hadamard partial-fraction expansions of `(logDeriv f)^{(2j-1)}` for
`f = ζ, L(·,χ₀), L(·,χ), L(·,χ₀χ)` (which express the multiplicity-weighted power sums over the
zeros of those four functions through `(logDeriv f)^{(2j-1)}`) with the positivity of the
arithmetic side of the differentiated explicit formula for the twisted product
`ζ(s)·L(s,χ₀)·L(s+iγ,χ)·L(s+iγ,χ₀χ)`.
-/

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-! ## Elementary rewrites -/

/-- The multiplicity of `u` as a zero of the twisted product
`D(s) = ζ(s)·L(s,χ₀)·L(s+iγ,χ)·L(s+iγ,χ₀χ)`. -/
def multD {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (γ : ℝ) (u : ℂ) : ℕ :=
  multZeta u + multL χ₀ u + multL χ (u + Complex.I * (γ : ℂ))
    + multL (χ₀ * χ) (u + Complex.I * (γ : ℂ))

lemma twMult_eq_multD {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ : ℝ) {u : ℂ}
    (h0 : u ≠ 0) (hβ : u ≠ (β₀ : ℂ)) : twMult χ₀ χ β₀ γ u = multD χ₀ χ γ u := by
  rw [twMult, if_neg (fun h => h.elim h0 hβ)]
  rfl

lemma zpow_neg_eq_one_div_pow (z : ℂ) (m : ℕ) : z ^ (-(m : ℤ)) = (1 / z) ^ m := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- Conversion between the two shapes of the partial-fraction weight. -/
lemma one_div_pow_eq_zpow_neg {z : ℂ} {k j : ℕ} (hkp : k + 1 = 2 * j) :
    (1 / z) ^ (2 * j) = z ^ (-(k + 1) : ℤ) := by
  have h : (-(k + 1) : ℤ) = -(((k + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [← hkp, h, zpow_neg_eq_one_div_pow]

lemma zval_pow_eq {α : ℝ} {j : ℕ} (hj : 1 ≤ j) (u : ℂ) :
    zval α u ^ j = (1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j) := by
  rw [zval, ← zpow_natCast, ← zpow_mul]
  have h2j : (2 * j - 1) + 1 = 2 * j := by omega
  have hcast : ((1 : ℂ) + (α : ℂ)) = (((1 + α : ℝ)) : ℂ) := by push_cast; ring
  have hexp : ((-2 : ℤ) * (j : ℤ)) = -(((2 * j - 1) + 1 : ℕ) : ℤ) := by
    rw [h2j]; push_cast; ring
  rw [hcast, hexp]
  rw [zpow_neg_eq_one_div_pow, h2j]

/-- An analytic function with a zero of finite order at `z` has vanishing order at least `1`. -/
lemma one_le_analyticOrderNatAt_of_analytic {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (htop : analyticOrderAt f z ≠ ⊤) (hz : f z = 0) : 1 ≤ analyticOrderNatAt f z := by
  have h0 : analyticOrderNatAt f z ≠ 0 := by
    intro h
    have h' := Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) htop
    rw [h] at h'
    exact (analyticOrderAt_ne_zero.mpr ⟨hf, hz⟩) h'.symm
  omega

/-- The inverse-factorial prefactor is real. -/
lemma re_inv_factorial_mul (j : ℕ) (z : ℂ) :
    ((1 / (((2 * j - 1).factorial : ℕ) : ℂ)) * z).re
      = (1 / (((2 * j - 1).factorial : ℕ) : ℝ)) * z.re := by
  have h1 : (((2 * j - 1).factorial : ℕ) : ℂ)
      = ((((2 * j - 1).factorial : ℕ) : ℝ) : ℂ) := rfl
  have h2 : (1 : ℂ) / ((((2 * j - 1).factorial : ℕ) : ℝ) : ℂ)
      = (((1 / (((2 * j - 1).factorial : ℕ) : ℝ) : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div]
  rw [h1, h2, Complex.re_ofReal_mul]

/-- The weight `Re (1/(1+α-u))^{2j}` at a real point `c`. -/
lemma weight_real_eq {α : ℝ} (j : ℕ) (c : ℝ) :
    ((1 / (((1 + α : ℝ) : ℂ) - (c : ℂ))) ^ (2 * j)).re = (1 / (1 + α - c)) ^ (2 * j) := by
  have h1 : (((1 + α : ℝ) : ℂ)) - (c : ℂ) = ((1 + α - c : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The weight at the pole `1`. -/
lemma re_one_div_sub_one_pow {α : ℝ} (j : ℕ) :
    ((1 / ((((1 + α : ℝ) : ℂ) - 1) ^ (2 * j)))).re = 1 / α ^ (2 * j) := by
  have h1 : (((1 + α : ℝ) : ℂ)) - 1 = (α : ℂ) := by push_cast; ring
  rw [h1, ← one_div_pow]
  have h2 : (1 : ℂ) / (α : ℂ) = ((1 / α : ℝ) : ℂ) := by
    rw [eq_comm, Complex.ofReal_div, Complex.ofReal_one]
  rw [h2, ← Complex.ofReal_pow, Complex.ofReal_re, one_div_pow]

/-! ## The partial-fraction expansion of `L(·,χ)` -/

/-- **The zero-sum expansion of `logDeriv L(·,χ)` in the `zeroSumK` shape**, for an arbitrary
(non-principal, possibly imprimitive) character.  Built from the primitive case
(`lFunction_logDeriv_zeroSumK`), the identity for the level-correction factors
(`levelFacZeroSumAlt`) and the multiplicativity of the vanishing orders and of the
logarithmic derivative over pointwise products. -/
lemma lZeroSumPF_gen {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ => ((multL χ u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)) ∧
    iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t
      = (-1 : ℂ) ^ k * ((k.factorial : ℕ) : ℂ) *
          zeroSumK (DirichletCharacter.LFunction χ) t k := by
  classical
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hψ
  have hψ1 : ψ ≠ 1 := by
    rw [hψ]; exact Work.LinnikAreas.DhK.primitiveCharacter_ne_one hχ
  have hψp : ψ.IsPrimitive := by
    rw [hψ]; exact DirichletCharacter.primitiveCharacter_isPrimitive χ
  set F : ℕ → ℂ → ℂ := fun p z => 1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-z) with hF
  set G : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, F p z with hG
  -- the primitive case
  obtain ⟨hsumL, hidL⟩ := lFunction_logDeriv_zeroSumK ψ hψ1 hψp k hk ht
  -- the level factors
  have hprimeF : ∀ p ∈ q.primeFactors, ((p : ℕ)).Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hFsum : ∀ p ∈ q.primeFactors, Summable (fun u : ℂ =>
      ((analyticOrderNatAt (F p) u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)) := by
    intro p hp
    by_cases hunit : IsUnit ((p : ℕ) : ZMod χ.conductor)
    · exact (levelFacZeroSumAlt (hprimeF p hp) (ψ (p : ZMod χ.conductor))
        (Or.inr (norm_apply_eq_one_of_isUnit ψ hunit)) k hk ht).1
    · exact (levelFacZeroSumAlt (hprimeF p hp) (ψ (p : ZMod χ.conductor))
        (Or.inl (MulChar.map_nonunit ψ hunit)) k hk ht).1
  have hFid : ∀ p ∈ q.primeFactors, iteratedDeriv k (logDeriv (F p)) t
      = (-1 : ℂ) ^ k * ((k.factorial : ℕ) : ℂ) * zeroSumK (F p) t k := by
    intro p hp
    by_cases hunit : IsUnit ((p : ℕ) : ZMod χ.conductor)
    · exact (levelFacZeroSumAlt (hprimeF p hp) (ψ (p : ZMod χ.conductor))
        (Or.inr (norm_apply_eq_one_of_isUnit ψ hunit)) k hk ht).2
    · exact (levelFacZeroSumAlt (hprimeF p hp) (ψ (p : ZMod χ.conductor))
        (Or.inl (MulChar.map_nonunit ψ hunit)) k hk ht).2
  have hFdiff : ∀ p ∈ q.primeFactors, Differentiable ℂ (F p) := by
    intro p hp
    rw [hF]
    exact levelFactor_differentiable ψ (Nat.Prime.ne_zero (hprimeF p hp))
  have hGdiff : Differentiable ℂ G := by
    rw [hG]
    exact diff_finsetProd q.primeFactors F hFdiff
  have hFt : ∀ p ∈ q.primeFactors, F p t ≠ 0 := by
    intro p hp
    rw [hF]
    exact levelFactor_ne_zero ψ (Nat.Prime.one_lt (hprimeF p hp)) ht
  have hGt : G t ≠ 0 := by
    rw [hG]
    exact Finset.prod_ne_zero_iff.mpr hFt
  -- the two product identities
  obtain ⟨hsumG, hZsplit⟩ := zeroSumK_finsetProd q.primeFactors F t t k hFdiff hFt hFsum
  have hGid : iteratedDeriv k (logDeriv G) t
      = ∑ p ∈ q.primeFactors, iteratedDeriv k (logDeriv (F p)) t := by
    rw [hG]
    exact iteratedDeriv_logDeriv_finsetProd q.primeFactors F t k hFdiff hFt
  -- the factorisation of `L(·,χ)`
  have hLfun : DirichletCharacter.LFunction χ
      = fun z => DirichletCharacter.LFunction ψ z * G z := by
    funext z
    have h1 := Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul χ hχ z
    rw [← hψ] at h1
    rw [hG]
    simpa only [hF] using h1
  have hLdiff : Differentiable ℂ (DirichletCharacter.LFunction ψ) :=
    DirichletCharacter.differentiable_LFunction hψ1
  have hLt : DirichletCharacter.LFunction ψ t ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (le_of_lt ht)
  have hL0 : DirichletCharacter.LFunction ψ ≠ 0 := by
    intro h
    exact hLt (by rw [h]; simp)
  have hG0 : G ≠ 0 := by
    intro h
    exact hGt (by rw [h]; simp)
  obtain ⟨hsumM, hZmul⟩ := zeroSumK_mul hLdiff hGdiff hL0 hG0 hsumL hsumG
  have hderivL : iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t
      = iteratedDeriv k (logDeriv (DirichletCharacter.LFunction ψ)) t
        + iteratedDeriv k (logDeriv G) t := by
    rw [hLfun]
    exact iteratedDeriv_logDeriv_mul hLdiff hGdiff hLt hGt k
  have hZχ : zeroSumK (DirichletCharacter.LFunction χ) t k
      = zeroSumK (DirichletCharacter.LFunction ψ) t k
        + ∑ p ∈ q.primeFactors, zeroSumK (F p) t k := by
    rw [hLfun, hZmul, hZsplit]
  refine ⟨?_, ?_⟩
  · rw [← hLfun] at hsumM
    exact hsumM
  · rw [hderivL, hidL, hGid, Finset.sum_congr rfl hFid, ← Finset.mul_sum, hZχ]
    ring

/-- The partial-fraction zero-sum expansion for `L(·,χ)`, with the summability of the zero sum. -/
lemma lZeroSumPF_form {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 1 < t.re) :
    Summable (fun u : ℂ => ((multL χ u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ)) ∧
    (-1 : ℂ) ^ k * ((k.factorial : ℕ) : ℂ) *
        (∑' u : ℂ, ((multL χ u : ℕ) : ℂ) * (t - u) ^ (-(k + 1) : ℤ))
      = iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) t := by
  obtain ⟨hS, hid⟩ := lZeroSumPF_gen χ hχ k hk ht
  exact ⟨hS, by rw [hid]; unfold zeroSumK; simp only [multL]⟩

/-- The algebra of the sign `(-1)^k` for odd `k`. -/
lemma neg_inv_fact_mul_of (k : ℕ) {T D : ℂ}
    (h : (-1 : ℂ) ^ k * ((k.factorial : ℕ) : ℂ) * T = D) (hodd : Odd k) :
    T = - (1 / ((k.factorial : ℕ) : ℂ)) * D := by
  have hkf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [hodd.neg_one_pow] at h
  have hgoal : T * ((k.factorial : ℕ) : ℂ) = -D := by
    rw [show T * ((k.factorial : ℕ) : ℂ)
        = -((-1 : ℂ) * ((k.factorial : ℕ) : ℂ) * T) by ring, h]
  rw [show - (1 / ((k.factorial : ℕ) : ℂ)) * D
      = -D / ((k.factorial : ℕ) : ℂ) by ring, eq_div_iff hkf]
  exact hgoal

/-! ## tsum manipulations with finitely many points replaced by zero -/

lemma tsum_ite_eq_single {a : ℂ} {h : ℂ → ℝ} :
    (∑' u : ℂ, (if u = a then h u else 0)) = h a := by
  rw [tsum_eq_single a]
  · simp
  · intro b hb; rw [if_neg hb]

lemma tsum_eq_tsum_sub_single {f g : ℂ → ℝ} (hf : Summable f) {a : ℂ}
    (h : ∀ u : ℂ, u ≠ a → g u = f u) (ha : g a = 0) :
    (∑' u : ℂ, g u) = (∑' u : ℂ, f u) - f a := by
  have hδ : Summable (fun u : ℂ => f u - g u) := by
    refine summable_of_ne_finset_zero (s := {a}) (fun u hu => ?_)
    rw [Finset.mem_singleton] at hu
    rw [h u hu, sub_self]
  have h1 : (∑' u : ℂ, g u) = (∑' u : ℂ, f u) - (∑' u : ℂ, (f u - g u)) := by
    have h2 := Summable.tsum_sub hf hδ
    have h3 : (fun u : ℂ => f u - (f u - g u)) = g := by funext u; ring
    rw [h3] at h2
    exact h2
  have h4 : (∑' u : ℂ, (f u - g u)) = f a := by
    have h5 : (fun u : ℂ => f u - g u) = fun u : ℂ => if u = a then f u - g u else 0 := by
      funext u
      by_cases hu : u = a
      · rw [if_pos hu]
      · rw [if_neg hu, h u hu, sub_self]
    rw [h5, tsum_ite_eq_single, ha, sub_zero]
  rw [h4] at h1
  exact h1

lemma tsum_eq_tsum_sub_pair {f g : ℂ → ℝ} (hf : Summable f) {a b : ℂ} (hab : a ≠ b)
    (h : ∀ u : ℂ, u ≠ a → u ≠ b → g u = f u) (ha : g a = 0) (hb : g b = 0) :
    (∑' u : ℂ, g u) = (∑' u : ℂ, f u) - (f a + f b) := by
  have hδ : Summable (fun u : ℂ => f u - g u) := by
    refine summable_of_ne_finset_zero (s := {a, b}) (fun u hu => ?_)
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    rw [h u hu.1 hu.2, sub_self]
  have h1 : (∑' u : ℂ, g u) = (∑' u : ℂ, f u) - (∑' u : ℂ, (f u - g u)) := by
    have h2 := Summable.tsum_sub hf hδ
    have h3 : (fun u : ℂ => f u - (f u - g u)) = g := by funext u; ring
    rw [h3] at h2
    exact h2
  have h4 : (∑' u : ℂ, (f u - g u)) = f a + f b := by
    have h5 : (fun u : ℂ => f u - g u)
        = fun u : ℂ => if u = a then f a - g a else (if u = b then f b - g b else 0) := by
      funext u
      by_cases hua : u = a
      · rw [if_pos hua, hua]
      · rw [if_neg hua]
        by_cases hub : u = b
        · rw [if_pos hub, hub]
        · rw [if_neg hub, h u hua hub, sub_self]
    rw [h5]
    have h6 : (∑' u : ℂ,
        (if u = a then f a - g a else if u = b then f b - g b else 0)) = f a - g a + (f b - g b) := by
      rw [tsum_eq_sum (s := {a, b}) (fun u hu => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        push_neg at hu
        rw [if_neg hu.1, if_neg hu.2])]
      rw [Finset.sum_pair hab, if_pos rfl, if_neg (Ne.symm hab), if_pos rfl]
    rw [h6, ha, hb]
    ring
  rw [h4] at h1
  exact h1

/-! ## The Hadamard power-sum bound for the twisted zero multiset -/

lemma multD_tsum_le {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q)
    (h₀ : χ₀ ≠ 1) (h₀sq : χ₀ * χ₀ = 1) (hχ : χ ≠ 1) (hχ₀χ : χ₀ * χ ≠ 1)
    (j : ℕ) (hj : 1 ≤ j) (γ : ℝ) {α : ℝ} (hα : 1 ≤ α) :
    Summable (fun u : ℂ => ((multD χ₀ χ γ u : ℕ) : ℝ)
        * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re) ∧
    (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℝ)
        * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re) ≤ 1 / α ^ (2 * j) := by
  classical
  set k : ℕ := 2 * j - 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hkp : k + 1 = 2 * j := by omega
  have hkodd : _root_.Odd k := by rw [hkdef]; exact ⟨j - 1, by omega⟩
  set σ : ℂ := ((1 + α : ℝ) : ℂ) with hσdef
  set σγ : ℂ := σ + Complex.I * (γ : ℂ) with hσγdef
  have hσgt : 1 < σ.re := by rw [hσdef]; simp; linarith
  have hσγgt : 1 < σγ.re := by rw [hσγdef, hσdef]; simp; linarith
  -- the four partial-fraction expansions
  obtain ⟨hS1, hid1⟩ := zetaZeroPowerId j hj (s := σ) hσgt
  obtain ⟨hS2, hid2⟩ := lZeroSumPF_form χ₀ h₀ k hk (t := σ) hσgt
  obtain ⟨hS3, hid3⟩ := lZeroSumPF_form χ hχ k hk (t := σγ) hσγgt
  obtain ⟨hS4, hid4⟩ := lZeroSumPF_form (χ₀ * χ) hχ₀χ k hk (t := σγ) hσγgt
  -- the ζ expansion in the `(σ-u)^(-(k+1))` shape
  have hid1' : (∑' u : ℂ, ((multZeta u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
      - (1 / (σ - 1) ^ (k + 1))
      = - (1 / ((k.factorial : ℕ) : ℂ)) * iteratedDeriv k (logDeriv riemannZeta) σ := by
    have hζsum : (∑' u : ℂ, ((multZeta u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
        = (∑' u : ℂ, ((analyticOrderNatAt riemannZeta u : ℕ) : ℂ) * (1 / (σ - u)) ^ (2 * j)) := by
      refine tsum_congr (fun u => ?_)
      rw [one_div_pow_eq_zpow_neg hkp]
      simp only [multZeta]
    have hpole : (1 / (σ - 1) ^ (k + 1)) = (1 / (σ - 1) ^ (2 * j)) := by rw [hkp]
    rw [hζsum, hpole, hid1, ← hkdef]
  have hS1' : Summable (fun u : ℂ => ((multZeta u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ)) :=
    hS1.congr (fun u => by
      have h := one_div_pow_eq_zpow_neg (z := σ - u) hkp
      simp only [multZeta]
      rw [h])
  -- the three `L`-expansions in the `sum = -(1/k!) D` shape
  have hid2' : (∑' u : ℂ, ((multL χ₀ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
      = - (1 / ((k.factorial : ℕ) : ℂ)) *
          iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ₀)) σ :=
    neg_inv_fact_mul_of k hid2 hkodd
  have hid3' : (∑' v : ℂ, ((multL χ v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ))
      = - (1 / ((k.factorial : ℕ) : ℂ)) *
          iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) σγ :=
    neg_inv_fact_mul_of k hid3 hkodd
  have hid4' : (∑' v : ℂ, ((multL (χ₀ * χ) v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ))
      = - (1 / ((k.factorial : ℕ) : ℂ)) *
          iteratedDeriv k (logDeriv (DirichletCharacter.LFunction (χ₀ * χ))) σγ :=
    neg_inv_fact_mul_of k hid4 hkodd
  -- reindexing the two shifted families
  have hshift : ∀ (g : ℂ → ℂ) (c : ℂ), (∑' u : ℂ, g (u + c)) = ∑' v : ℂ, g v := by
    intro g c
    exact Equiv.tsum_eq (Equiv.addRight c) g
  have hshiftS : ∀ (g : ℂ → ℂ) (c : ℂ), Summable g → Summable (fun u : ℂ => g (u + c)) := by
    intro g c hg
    exact (Equiv.summable_iff (Equiv.addRight c)).mpr hg
  have hshiftarg : ∀ u : ℂ, σγ - (u + Complex.I * (γ : ℂ)) = σ - u := by
    intro u
    rw [hσγdef, hσdef]; ring
  have hχsum : (∑' u : ℂ, ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
        * (σ - u) ^ (-(k + 1) : ℤ))
      = (∑' v : ℂ, ((multL χ v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ)) := by
    rw [← hshift (fun v : ℂ => ((multL χ v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ))
      (Complex.I * (γ : ℂ))]
    refine tsum_congr (fun u => ?_)
    rw [hshiftarg u]
  have hχid : (∑' u : ℂ, ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
        * (σ - u) ^ (-(k + 1) : ℤ))
      = - (1 / ((k.factorial : ℕ) : ℂ)) *
          iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) σγ := by
    rw [hχsum, hid3']
  have hSχ : Summable (fun u : ℂ => ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
      * (σ - u) ^ (-(k + 1) : ℤ)) := by
    have h1 : Summable (fun u : ℂ => ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
        * (σγ - (u + Complex.I * (γ : ℂ))) ^ (-(k + 1) : ℤ)) :=
      hshiftS (fun v : ℂ => ((multL χ v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ))
        (Complex.I * (γ : ℂ)) hS3
    exact h1.congr (fun u => by rw [hshiftarg u])
  have hχ₀χsum : (∑' u : ℂ, ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
        * (σ - u) ^ (-(k + 1) : ℤ))
      = (∑' v : ℂ, ((multL (χ₀ * χ) v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ)) := by
    rw [← hshift (fun v : ℂ => ((multL (χ₀ * χ) v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ))
      (Complex.I * (γ : ℂ))]
    refine tsum_congr (fun u => ?_)
    rw [hshiftarg u]
  have hχ₀χid : (∑' u : ℂ, ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
        * (σ - u) ^ (-(k + 1) : ℤ))
      = - (1 / ((k.factorial : ℕ) : ℂ)) *
          iteratedDeriv k (logDeriv (DirichletCharacter.LFunction (χ₀ * χ))) σγ := by
    rw [hχ₀χsum, hid4']
  have hSχ₀χ : Summable (fun u : ℂ => ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
      * (σ - u) ^ (-(k + 1) : ℤ)) := by
    have h1 : Summable (fun u : ℂ => ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
        * (σγ - (u + Complex.I * (γ : ℂ))) ^ (-(k + 1) : ℤ)) :=
      hshiftS (fun v : ℂ => ((multL (χ₀ * χ) v : ℕ) : ℂ) * (σγ - v) ^ (-(k + 1) : ℤ))
        (Complex.I * (γ : ℂ)) hS4
    exact h1.congr (fun u => by rw [hshiftarg u])
  -- the combined sum
  have hSall : Summable (fun u : ℂ => ((multD χ₀ χ γ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ)) := by
    have h := ((hS1'.add hS2).add hSχ).add hSχ₀χ
    refine h.congr (fun u => ?_)
    simp only [multD]
    push_cast
    ring
  have h1sum : (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
      = (∑' u : ℂ, ((multZeta u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
        + (∑' u : ℂ, ((multL χ₀ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
        + (∑' u : ℂ, ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
        + (∑' u : ℂ, ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
            * (σ - u) ^ (-(k + 1) : ℤ)) := by
    rw [← Summable.tsum_add hS1' hS2, ← Summable.tsum_add (hS1'.add hS2) hSχ,
      ← Summable.tsum_add ((hS1'.add hS2).add hSχ) hSχ₀χ]
    refine tsum_congr (fun u => ?_)
    simp only [multD]
    push_cast
    ring
  have hcomb : (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
      - (1 / (σ - 1) ^ (k + 1))
      = - ((1 / ((k.factorial : ℕ) : ℂ)) *
          (iteratedDeriv k (logDeriv riemannZeta) σ
            + iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ₀)) σ
            + iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) σγ
            + iteratedDeriv k (logDeriv (DirichletCharacter.LFunction (χ₀ * χ))) σγ)) := by
    have hsplit : (∑' u : ℂ, ((multZeta u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
          + (∑' u : ℂ, ((multL χ₀ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
          + (∑' u : ℂ, ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
          + (∑' u : ℂ, ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
              * (σ - u) ^ (-(k + 1) : ℤ)) - (1 / (σ - 1) ^ (k + 1))
        = ((∑' u : ℂ, ((multZeta u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
            - (1 / (σ - 1) ^ (k + 1)))
          + ((∑' u : ℂ, ((multL χ₀ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ))
            + (∑' u : ℂ, ((multL χ (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
                * (σ - u) ^ (-(k + 1) : ℤ))
            + (∑' u : ℂ, ((multL (χ₀ * χ) (u + Complex.I * (γ : ℂ)) : ℕ) : ℂ)
                * (σ - u) ^ (-(k + 1) : ℤ))) := by ring
    rw [h1sum, hsplit, hid1', hid2', hχid, hχ₀χid]
    ring
  -- real parts and positivity
  have hre_all : (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ)).re
      = ∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℝ) * ((σ - u) ^ (-(k + 1) : ℤ)).re := by
    rw [Complex.re_tsum hSall]
    exact tsum_congr (fun u => by rw [Complex.mul_re]; simp)
  have hpos : 0 ≤ (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) σ
      + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ₀)) σ
      + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) σγ
      + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction (χ₀ * χ))) σγ).re := by
    have hp := positivityArith χ₀ χ h₀sq j hj γ (σ := 1 + α) (by linarith)
    simpa only [hσdef, hσγdef, Complex.ofReal_ofNat, Complex.ofReal_add] using hp
  have hboundk : (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℝ)
      * ((σ - u) ^ (-(k + 1) : ℤ)).re) ≤ 1 / α ^ (2 * j) := by
    have hcomb2 := hcomb
    rw [hkdef] at hcomb2
    have hre := congrArg Complex.re hcomb2
    rw [Complex.sub_re, Complex.neg_re, re_inv_factorial_mul, Complex.add_re, Complex.add_re,
      Complex.add_re] at hre
    rw [hσdef] at hre
    rw [show (2 * j - 1) + 1 = 2 * j by omega] at hre
    rw [re_one_div_sub_one_pow j] at hre
    rw [hre_all] at hre
    have hpos' : 0 ≤ (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) σ).re
        + (iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ₀)) σ).re
        + (iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) σγ).re
        + (iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction (χ₀ * χ))) σγ).re := by
      have h := hpos
      rwa [Complex.add_re, Complex.add_re, Complex.add_re] at h
    have h1 : 0 ≤ (1 / (((2 * j - 1).factorial : ℕ) : ℝ)) := by positivity
    nlinarith [hre, hpos', h1]
  -- back to the shape of the statement
  have hconv : ∀ u : ℂ, ((σ - u) ^ (-(k + 1) : ℤ)).re
      = ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re := by
    intro u
    rw [← one_div_pow_eq_zpow_neg hkp]
  constructor
  · refine Summable.of_norm_bounded hSall.norm (fun u => ?_)
    calc ‖((multD χ₀ χ γ u : ℕ) : ℝ) * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re‖
        = ((multD χ₀ χ γ u : ℕ) : ℝ)
            * ‖((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re‖ := by
          have h0 : (0 : ℝ) ≤ ((multD χ₀ χ γ u : ℕ) : ℝ) := Nat.cast_nonneg _
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      _ ≤ ((multD χ₀ χ γ u : ℕ) : ℝ) * ‖(1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (multD χ₀ χ γ u))
          rw [Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _
      _ = ((multD χ₀ χ γ u : ℕ) : ℝ) * ‖(σ - u) ^ (-(k + 1) : ℤ)‖ := by
          rw [one_div_pow_eq_zpow_neg (z := σ - u) hkp]
      _ = ‖((multD χ₀ χ γ u : ℕ) : ℂ) * (σ - u) ^ (-(k + 1) : ℤ)‖ := by
          rw [norm_mul, Complex.norm_natCast]
  · have hsum_eq : (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℝ)
        * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re)
        = (∑' u : ℂ, ((multD χ₀ χ γ u : ℕ) : ℝ) * ((σ - u) ^ (-(k + 1) : ℤ)).re) :=
      tsum_congr (fun u => by rw [hconv u])
    rw [hsum_eq]
    exact hboundk

/-! ## The final assembly -/

theorem twUpper {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q)
    (h₀ : χ₀ ≠ 1) (h₀sq : χ₀ * χ₀ = 1) (hχ : χ ≠ 1) (hχ₀χ : χ₀ * χ ≠ 1)
    (β₀ : ℝ) (hβ₀ : DirichletCharacter.LFunction χ₀ ((β₀ : ℝ) : ℂ) = 0)
    (α : ℝ) (hα : 1 ≤ α) (γ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    Work.LinnikAreas.TuranOther.twSum χ₀ χ β₀ γ α j
      ≤ 1 / α ^ (2 * j) - (1 / (1 + α - β₀)) ^ (2 * j) := by
  classical
  obtain ⟨hMDsumm, hBound⟩ := multD_tsum_le χ₀ χ h₀ h₀sq hχ hχ₀χ j hj γ hα
  set MD : ℂ → ℝ := fun u => ((multD χ₀ χ γ u : ℕ) : ℝ)
      * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re with hMD
  set TW : ℂ → ℝ := fun u => ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ)
      * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re with hTW
  have hMDsumm' : Summable MD := hMDsumm
  have htw : twSum χ₀ χ β₀ γ α j = ∑' u : ℂ, TW u := by
    rw [twSum]
    refine tsum_congr (fun u => ?_)
    show ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) * (zval α u ^ j).re = TW u
    rw [hTW, zval_pow_eq hj u]
  -- the multiplicity of the exceptional zero is at least one
  have hβ1 : 1 ≤ multD χ₀ χ γ (β₀ : ℂ) := by
    have hL0 : DirichletCharacter.LFunction χ₀ ≠ 0 := by
      intro h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₀ (Or.inl h₀) (by norm_num)
        (congr_fun h 2)
    have hLd : Differentiable ℂ (DirichletCharacter.LFunction χ₀) :=
      DirichletCharacter.differentiable_LFunction h₀
    have htop : analyticOrderAt (DirichletCharacter.LFunction χ₀) ((β₀ : ℝ) : ℂ) ≠ ⊤ :=
      analyticOrderAt_ne_top_of_diff_ne_zero hLd hL0 _
    have h1 := one_le_analyticOrderNatAt_of_analytic (hLd.analyticAt _) htop hβ₀
    simp only [multD, multL]
    omega
  have hW0 : MD 0 = ((multD χ₀ χ γ 0 : ℕ) : ℝ) * (1 / (1 + α)) ^ (2 * j) := by
    show ((multD χ₀ χ γ 0 : ℕ) : ℝ) * ((1 / (((1 + α : ℝ) : ℂ) - 0)) ^ (2 * j)).re
      = ((multD χ₀ χ γ 0 : ℕ) : ℝ) * (1 / (1 + α)) ^ (2 * j)
    congr 1
    rw [show (((1 + α : ℝ) : ℂ)) - 0 = (((1 + α : ℝ)) : ℂ) by ring,
      ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hWβ : MD ((β₀ : ℝ) : ℂ)
      = ((multD χ₀ χ γ (β₀ : ℂ) : ℕ) : ℝ) * (1 / (1 + α - β₀)) ^ (2 * j) := by
    show ((multD χ₀ χ γ ((β₀ : ℝ) : ℂ) : ℕ) : ℝ)
        * ((1 / (((1 + α : ℝ) : ℂ) - ((β₀ : ℝ) : ℂ))) ^ (2 * j)).re
      = ((multD χ₀ χ γ (β₀ : ℂ) : ℕ) : ℝ) * (1 / (1 + α - β₀)) ^ (2 * j)
    rw [weight_real_eq]
  by_cases hβ0 : β₀ = 0
  · have hTWsum : (∑' u : ℂ, TW u) = (∑' u : ℂ, MD u) - MD 0 := by
      refine tsum_eq_tsum_sub_single hMDsumm' (fun u hu => ?_)
        (by show ((twMult χ₀ χ β₀ γ 0 : ℕ) : ℝ)
              * ((1 / (((1 + α : ℝ) : ℂ) - 0)) ^ (2 * j)).re = 0
            rw [twMult, if_pos (Or.inl rfl)]
            simp)
      show ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re
        = ((multD χ₀ χ γ u : ℕ) : ℝ) * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re
      rw [twMult_eq_multD χ₀ χ β₀ γ hu (by rw [hβ0]; simpa using hu)]
    have hMD0le : (1 / (1 + α - β₀)) ^ (2 * j) ≤ MD 0 := by
      rw [hW0, show (1 + α - β₀) = 1 + α by rw [hβ0]; ring]
      have h1 : (1 : ℝ) ≤ ((multD χ₀ χ γ 0 : ℕ) : ℝ) := by
        have h2 : (β₀ : ℂ) = 0 := by rw [hβ0]; simp
        rw [h2] at hβ1
        exact_mod_cast hβ1
      have h2 : (0 : ℝ) ≤ (1 / (1 + α)) ^ (2 * j) := by
        rw [pow_mul]
        exact pow_nonneg (sq_nonneg _) j
      calc (1 / (1 + α)) ^ (2 * j)
          = 1 * (1 / (1 + α)) ^ (2 * j) := (one_mul _).symm
        _ ≤ ((multD χ₀ χ γ 0 : ℕ) : ℝ) * (1 / (1 + α)) ^ (2 * j) :=
            mul_le_mul_of_nonneg_right h1 h2
    rw [htw, hTWsum]
    exact sub_le_sub hBound hMD0le
  · have hTWsum : (∑' u : ℂ, TW u) = (∑' u : ℂ, MD u) - (MD 0 + MD ((β₀ : ℝ) : ℂ)) := by
      refine tsum_eq_tsum_sub_pair hMDsumm' ?_ (fun u hu hv => ?_)
        (by show ((twMult χ₀ χ β₀ γ 0 : ℕ) : ℝ)
              * ((1 / (((1 + α : ℝ) : ℂ) - 0)) ^ (2 * j)).re = 0
            rw [twMult, if_pos (Or.inl rfl)]
            simp)
        (by show ((twMult χ₀ χ β₀ γ ((β₀ : ℝ) : ℂ) : ℕ) : ℝ)
              * ((1 / (((1 + α : ℝ) : ℂ) - ((β₀ : ℝ) : ℂ))) ^ (2 * j)).re = 0
            rw [twMult, if_pos (Or.inr rfl)]
            simp)
      · intro hcon
        exact hβ0 (by exact_mod_cast hcon.symm)
      · show ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re
          = ((multD χ₀ χ γ u : ℕ) : ℝ) * ((1 / (((1 + α : ℝ) : ℂ) - u)) ^ (2 * j)).re
        rw [twMult_eq_multD χ₀ χ β₀ γ hu hv]
    have hMD0nn : 0 ≤ MD 0 := by
      rw [hW0]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j
    have hMDβle : (1 / (1 + α - β₀)) ^ (2 * j) ≤ MD ((β₀ : ℝ) : ℂ) := by
      rw [hWβ]
      have h1 : (1 : ℝ) ≤ ((multD χ₀ χ γ (β₀ : ℂ) : ℕ) : ℝ) := by exact_mod_cast hβ1
      have h2 : (0 : ℝ) ≤ (1 / (1 + α - β₀)) ^ (2 * j) := by
        rw [pow_mul]
        exact pow_nonneg (sq_nonneg _) j
      calc (1 / (1 + α - β₀)) ^ (2 * j)
          = 1 * (1 / (1 + α - β₀)) ^ (2 * j) := (one_mul _).symm
        _ ≤ ((multD χ₀ χ γ (β₀ : ℂ) : ℕ) : ℝ) * (1 / (1 + α - β₀)) ^ (2 * j) :=
            mul_le_mul_of_nonneg_right h1 h2
    rw [htw, hTWsum]
    simpa only [zero_add] using sub_le_sub hBound (add_le_add hMD0nn hMDβle)

end Work.LinnikAreas.TuranOther
