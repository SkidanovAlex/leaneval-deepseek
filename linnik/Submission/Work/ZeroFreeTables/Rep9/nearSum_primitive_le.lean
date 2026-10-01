/-
# ZeroFreeTables/Rep9/nearSum_primitive_le

The imprimitive ↔ primitive bridge for HB's near-zero sums `P3NearSumL` of §9.

An imprimitive Dirichlet character `χ` (mod `q`) and the primitive character `χ*` inducing it
have the same completed `L`-function up to the Euler factors at the primes `p | q`:

  `Λ(χ,u) = Λ(χ*,u) · ∏_{p | q} (1 − χ*(p)·p^{-u})`     (`Re u > 0`),

and every factor `1 − χ*(p)p^{-u}` is holomorphic and non-vanishing on `Re u > 0` (it vanishes
only when `p^{-u} = χ*(p)^{-1}`, which forces `Re u = 0`).  Since the summing window of
`P3NearSumL` lies in `Re u > 0` as soon as `δ < 1`, the two near sums coincide, so in particular

  `P3NearSumL q L χ s a λ₁ δ ≤ P3NearSumL χ.conductor L χ* s a λ₁ δ`.

This lets the §9 derivation combine `masterP3` (stated for a *primitive* character) with
`nearSum_bounds` (stated for the character mod `q`, e.g. the multiplicity bound
`2P₃(1) ≤ P3NearSumL q …`).

Mathlib contains the relation only for `χ.conductor = q` (i.e. for primitive `χ`); the general
imprimitive case is established here.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL

open DirichletCharacter Complex
open scoped Classical BigOperators Topology Filter
noncomputable section

namespace Work.ZeroFreeTables.Rep9

/-! ## Parity and the gamma factor under `changeLevel` -/

lemma chL_neg_one {n m : ℕ} [NeZero m] (hm : n ∣ m) (ψ : DirichletCharacter ℂ n) :
    (changeLevel hm ψ) (-1) = ψ (-1) := by
  rw [show ((-1 : ZMod m)) = (((-1:ℤ) : ZMod m)) by norm_num,
      show ((-1 : ZMod n)) = (((-1:ℤ) : ZMod n)) by norm_num]
  exact DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hm
    ((isCoprime_one_left (x := (m:ℤ))).neg_left)

lemma chL_even {n m : ℕ} [NeZero m] (hm : n ∣ m) (ψ : DirichletCharacter ℂ n) :
    (changeLevel hm ψ).Even ↔ ψ.Even := by
  rw [DirichletCharacter.Even, DirichletCharacter.Even, chL_neg_one hm ψ]

lemma gammaFactor_changeLevel {n m : ℕ} [NeZero m] (hm : n ∣ m)
    (ψ : DirichletCharacter ℂ n) (s : ℂ) :
    gammaFactor (changeLevel hm ψ) s = gammaFactor ψ s := by
  have hiff := chL_even hm ψ
  by_cases h : ψ.Even
  · rw [gammaFactor, gammaFactor, if_pos h, if_pos (hiff.mpr h)]
  · rw [gammaFactor, gammaFactor, if_neg h, if_neg (fun hc => h (hiff.mp hc))]

/-! ## The Euler factor and the completed `L`-function relation -/

/-- The Euler factor relating the completed `L`-functions of an imprimitive character and its
primitive character. -/
def eulerFac {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  ∏ p ∈ q.primeFactors, fun u : ℂ =>
    1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)

lemma eulerFac_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℂ) :
    eulerFac χ u = ∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)) := by
  rw [eulerFac, Finset.prod_apply]

/-- `u ↦ Λ(χ,u)` (the imprimitive completed `L`-function). -/
def clfA {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  fun u => DirichletCharacter.completedLFunction χ u

/-- `u ↦ Λ(χ*,u)` (the completed `L`-function of the primitive character). -/
def clfB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  fun u => @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
    χ.primitiveCharacter u

/-- `Λ(χ,u) = Λ(χ*,u)·∏_{p|q}(1 − χ*(p)p^{-u})` for `Re u > 0`. -/
theorem clf_prim_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {u : ℂ} (hu : 0 < u.re) :
    @DirichletCharacter.completedLFunction q _ χ u
      = @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
          χ.primitiveCharacter u
        * ∏ p ∈ q.primeFactors,
            (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    have h := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h
    exact h.symm
  have hL := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (s := u) (Or.inl hχ')
  rw [χ.changeLevel_primitiveCharacter] at hL
  have hC1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hu0)
  have hC2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.primitiveCharacter u
      (Or.inl hu0)
  have hγeq : gammaFactor χ u = gammaFactor χ.primitiveCharacter u := by
    have h1 : gammaFactor (changeLevel χ.conductor_dvd_level χ.primitiveCharacter) u
        = gammaFactor χ.primitiveCharacter u := gammaFactor_changeLevel _ _ _
    rwa [χ.changeLevel_primitiveCharacter] at h1
  have hGamR : ∀ z : ℂ, 0 < z.re → z.Gammaℝ ≠ 0 := by
    intro z hz h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    have hz' : z.re = -(2 * (n:ℝ)) := by rw [hn]; simp
    have : (0:ℝ) ≤ 2 * (n:ℝ) := by positivity
    linarith
  have hγne : gammaFactor χ.primitiveCharacter u ≠ 0 := by
    rw [DirichletCharacter.gammaFactor]
    split_ifs with h
    · exact hGamR u hu
    · exact hGamR (u+1) (by simp only [Complex.add_re, Complex.one_re]; linarith)
  rw [hC1, hC2, hγeq] at hL
  have hq : @DirichletCharacter.completedLFunction q _ χ u / gammaFactor χ.primitiveCharacter u
      = (@DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
            χ.primitiveCharacter u
          * ∏ p ∈ q.primeFactors,
              (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)))
        / gammaFactor χ.primitiveCharacter u := by
    rw [hL]; ring
  calc @DirichletCharacter.completedLFunction q _ χ u
      = @DirichletCharacter.completedLFunction q _ χ u / gammaFactor χ.primitiveCharacter u
          * gammaFactor χ.primitiveCharacter u := (div_mul_cancel₀ _ hγne).symm
    _ = ((@DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
            χ.primitiveCharacter u
          * ∏ p ∈ q.primeFactors,
              (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)))
        / gammaFactor χ.primitiveCharacter u) * gammaFactor χ.primitiveCharacter u := by rw [hq]
    _ = @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
          χ.primitiveCharacter u
        * ∏ p ∈ q.primeFactors,
            (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)) :=
        div_mul_cancel₀ _ hγne

/-- The Euler factor is holomorphic. -/
lemma eulerFac_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    AnalyticAt ℂ (eulerFac χ) z := by
  unfold eulerFac
  refine Finset.analyticAt_prod (𝕜 := ℂ) (E := ℂ) (A := ℂ) (c := z)
    (f := fun (p : ℕ) (u : ℂ) =>
      1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u))
    q.primeFactors (fun p hp => ?_)
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hmem : (p : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    simpa using (show (0:ℝ) < (p:ℝ) by exact_mod_cast hpprime.pos)
  have hc : AnalyticAt ℂ (fun u : ℂ => (p : ℂ) ^ (-u)) z :=
    AnalyticAt.cpow analyticAt_const analyticAt_id.neg hmem
  exact (analyticAt_const (𝕜 := ℂ) (E := ℂ) (v := (1:ℂ))).sub
    ((analyticAt_const (𝕜 := ℂ) (E := ℂ)
      (v := χ.primitiveCharacter (p : ZMod χ.conductor))).mul hc)

/-- The Euler factor does not vanish on `Re z > 0`. -/
lemma eulerFac_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz : 0 < z.re) : eulerFac χ z ≠ 0 := by
  rw [eulerFac, Finset.prod_apply, Finset.prod_ne_zero_iff]
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 1 < (p:ℝ) := by exact_mod_cast hpprime.one_lt
  have hppos : (0:ℝ) < p := by exact_mod_cast hpprime.pos
  intro h
  have h1 : χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ)^(-z) = 1 :=
    (sub_eq_zero.mp h).symm
  have h3 : ‖(p : ℂ)^(-z)‖ = (p : ℝ)^(-z.re) := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p (s := -z)
        (by simp only [Complex.neg_re]; linarith), Complex.neg_re]
  have h2 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ)^(-z)‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  rw [h3] at h2
  have h4 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 :=
    DirichletCharacter.norm_le_one _ _
  have hXpos : 0 < (p : ℝ)^(-z.re) := Real.rpow_pos_of_pos hppos _
  have h5 : 1 ≤ (p : ℝ)^(-z.re) := by nlinarith [h2, h4, hXpos]
  have h7 : (p:ℝ)^(0:ℝ) ≤ (p:ℝ)^(-z.re) := by rw [Real.rpow_zero]; exact h5
  have h6 : (0:ℝ) ≤ -z.re := (Real.rpow_le_rpow_left_iff hp2).mp h7
  linarith

/-! ## Equality of the local orders and of the divisors -/

/-- The imprimitive and the primitive completed `L`-functions have the same order at every point
of `Re z > 0`. -/
theorem meromorphicOrderAt_clf_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (clfA χ) z = meromorphicOrderAt (clfB χ) z := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    have h := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h
    exact h.symm
  have hA : AnalyticAt ℂ (clfA χ) z :=
    (differentiable_completedLFunction hχ).differentiableOn.analyticAt Filter.univ_mem
  have hB : AnalyticAt ℂ (clfB χ) z :=
    (differentiable_completedLFunction hχ').differentiableOn.analyticAt Filter.univ_mem
  have hP : AnalyticAt ℂ (eulerFac χ) z := eulerFac_analyticAt χ z
  have hPz : eulerFac χ z ≠ 0 := eulerFac_ne_zero χ hz
  have hev : (fun u => @DirichletCharacter.completedLFunction q _ χ u)
      =ᶠ[𝓝 z] ((fun u => @DirichletCharacter.completedLFunction χ.conductor
          ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter u) * eulerFac χ) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hz] with w hw
    change @DirichletCharacter.completedLFunction q _ χ w
      = @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
          χ.primitiveCharacter w * eulerFac χ w
    rw [eulerFac_apply]
    exact clf_prim_mul χ hχ hw
  have h1 : meromorphicOrderAt (clfA χ) z = meromorphicOrderAt (clfB χ * eulerFac χ) z :=
    meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)
  have hPz0 : meromorphicOrderAt (eulerFac χ) z = 0 := by
    rw [hP.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (eulerFac χ) z = 0 :=
      (AnalyticAt.analyticOrderAt_eq_zero hP).mpr hPz
    rw [h0]; simp
  rw [h1, meromorphicOrderAt_mul hB.meromorphicAt hP.meromorphicAt, hPz0, add_zero]

/-- The divisors of the imprimitive and of the primitive completed `L`-functions agree at every
point of `Re z > 0`. -/
theorem pdiv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) {z : ℂ}
    (hz : 0 < z.re) :
    @Work.ZeroFreeTables.pdiv q _ χ s z
      = @Work.ZeroFreeTables.pdiv χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter s z := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    have h := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h
    exact h.symm
  show MeromorphicOn.divisor (clfA χ) (Metric.closedBall 0 (|s.im| + 2)) z
      = MeromorphicOn.divisor (clfB χ) (Metric.closedBall 0 (|s.im| + 2)) z
  have hAmer : MeromorphicOn (clfA χ) (Metric.closedBall 0 (|s.im| + 2)) := fun w _ =>
    ((differentiable_completedLFunction hχ).differentiableOn.analyticAt Filter.univ_mem).meromorphicAt
  have hBmer : MeromorphicOn (clfB χ) (Metric.closedBall 0 (|s.im| + 2)) := fun w _ =>
    ((differentiable_completedLFunction hχ').differentiableOn.analyticAt Filter.univ_mem).meromorphicAt
  by_cases hzU : z ∈ Metric.closedBall 0 (|s.im| + 2)
  · rw [MeromorphicOn.divisor_apply hAmer hzU, MeromorphicOn.divisor_apply hBmer hzU,
      meromorphicOrderAt_clf_eq χ hχ hz]
  · rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def]
    simp [hzU]

/-! ## The near-sum inequality -/

/-- **Imprimitive ↔ primitive near-zero sums.**  For `δ < 1` the near-zero sums of an imprimitive
character and of the primitive character inducing it coincide (hence the stated inequality). -/
theorem nearSum_primitive_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (L : ℝ) (s : ℂ) (a lam₁ δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    Work.ZeroFreeTables.P3NearSumL q L χ s a lam₁ δ
      ≤ @Work.ZeroFreeTables.P3NearSumL χ.conductor ⟨χ.conductor_ne_zero⟩ L
          χ.primitiveCharacter s a lam₁ δ := by
  apply le_of_eq
  have hsummand : ∀ u : ℂ,
      ((@Work.ZeroFreeTables.pdiv q _ χ s u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
            then (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re else 0)
        = ((@Work.ZeroFreeTables.pdiv χ.conductor ⟨χ.conductor_ne_zero⟩
              χ.primitiveCharacter s u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
            then (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re else 0) := by
    intro u
    by_cases h : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
    · have hu_pos : 0 < u.re := by
        have hlt : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ < 1 := lt_of_le_of_lt h hδ1
        have h1 : |((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re|
            ≤ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := Complex.abs_re_le_norm _
        have hre : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by
          simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
        rw [hre] at h1
        have := (abs_lt.mp (lt_of_le_of_lt h1 hlt)).2
        linarith
      rw [if_pos h, pdiv_eq χ hχ s hu_pos]
    · rw [if_neg h]; ring
  rw [Work.ZeroFreeTables.P3NearSumL, Work.ZeroFreeTables.P3NearSumL]
  exact finsum_congr hsummand

end Work.ZeroFreeTables.Rep9
