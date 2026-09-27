import Mathlib

/-!
# The Cauchy kernel `2a/(a² + cψ²)` and its derivatives

Auxiliary definitions for the domination of the Poisson kernel by the Cauchy kernel and for the
integration-by-parts estimate in `pk_near_part_bound`.

`cauchyK a c ψ = 2a/(a² + cψ²)`, `cauchyKq a c = -d/dψ cauchyK a c`, and
`cauchyKern a c ψ = ψ * cauchyKq a c ψ`.
-/

namespace Work.EQ.Fatou

open MeasureTheory Set intervalIntegral Filter

/-- The Cauchy kernel `2a/(a² + cψ²)`. -/
noncomputable def cauchyK (a c ψ : ℝ) : ℝ := 2 * a / (a ^ 2 + c * ψ ^ 2)

/-- The `ψ`-derivative of the Cauchy kernel. -/
noncomputable def cauchyKderiv (a c x : ℝ) : ℝ := -(4 * a * c * x) / (a ^ 2 + c * x ^ 2) ^ 2

/-- The negated `ψ`-derivative of the Cauchy kernel. -/
noncomputable def cauchyKq (a c x : ℝ) : ℝ := 4 * a * c * x / (a ^ 2 + c * x ^ 2) ^ 2

/-- `ψ · (-d/dψ) cauchyK`, i.e. `4acψ²/(a²+cψ²)²`. -/
noncomputable def cauchyKern (a c x : ℝ) : ℝ := 4 * a * c * x ^ 2 / (a ^ 2 + c * x ^ 2) ^ 2

lemma cauchyK_pos {a c ψ : ℝ} (ha : 0 < a) (hc : 0 < c) : 0 < cauchyK a c ψ := by
  rw [cauchyK]
  exact div_pos (by positivity) (by positivity)

lemma cauchyK_nonneg {a c ψ : ℝ} (ha : 0 < a) (hc : 0 < c) : 0 ≤ cauchyK a c ψ :=
  le_of_lt (cauchyK_pos ha hc)

lemma cauchyK_continuous {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) : Continuous (cauchyK a c) := by
  have hK : cauchyK a c = fun ψ : ℝ => 2 * a / (a ^ 2 + c * ψ ^ 2) :=
    funext (fun ψ => by rw [cauchyK])
  rw [hK]
  apply Continuous.div <;> try fun_prop
  intro ψ
  have h1 : 0 < a ^ 2 := by positivity
  nlinarith [sq_nonneg ψ, mul_nonneg hc (sq_nonneg ψ)]

lemma cauchyKq_continuous {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) : Continuous (cauchyKq a c) := by
  have hK : cauchyKq a c = fun ψ : ℝ => 4 * a * c * ψ / (a ^ 2 + c * ψ ^ 2) ^ 2 :=
    funext (fun ψ => by rw [cauchyKq])
  rw [hK]
  apply Continuous.div <;> try fun_prop
  intro ψ
  have h1 : 0 < a ^ 2 := by positivity
  have h2 : 0 ≤ c * ψ ^ 2 := mul_nonneg hc (sq_nonneg ψ)
  nlinarith [sq_nonneg ψ, h2]

lemma cauchyKern_continuous {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) : Continuous (cauchyKern a c) := by
  have hK : cauchyKern a c = fun ψ : ℝ => 4 * a * c * ψ ^ 2 / (a ^ 2 + c * ψ ^ 2) ^ 2 :=
    funext (fun ψ => by rw [cauchyKern])
  rw [hK]
  apply Continuous.div <;> try fun_prop
  intro ψ
  have h1 : 0 < a ^ 2 := by positivity
  have h2 : 0 ≤ c * ψ ^ 2 := mul_nonneg hc (sq_nonneg ψ)
  nlinarith [sq_nonneg ψ, h2]

lemma cauchyKq_nonneg {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) (hx : 0 ≤ x) :
    0 ≤ cauchyKq a c x := by
  rw [cauchyKq]
  exact div_nonneg (by positivity) (by positivity)

lemma cauchyKern_nonneg {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) : 0 ≤ cauchyKern a c x := by
  rw [cauchyKern]
  exact div_nonneg (by positivity) (by positivity)

lemma hasDerivAt_cauchyK {a c x : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    HasDerivAt (cauchyK a c) (cauchyKderiv a c x) x := by
  have hxden : a ^ 2 + c * x ^ 2 ≠ 0 := by
    have h1 : 0 < a ^ 2 := by positivity
    have h2 : 0 ≤ c * x ^ 2 := mul_nonneg hc (sq_nonneg x)
    nlinarith [sq_nonneg x, h2]
  have h1 : HasDerivAt (fun ψ : ℝ => a ^ 2 + c * ψ ^ 2) (2 * c * x) x := by
    have h10 : HasDerivAt (fun ψ : ℝ => ψ ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hd := (hasDerivAt_const (x := x) (c := a ^ 2)).add (h10.const_mul c)
    convert hd using 1
    ring
  have h2 : HasDerivAt (fun ψ : ℝ => 2 * a / (a ^ 2 + c * ψ ^ 2))
      ((0 * (a ^ 2 + c * x ^ 2) - 2 * a * (2 * c * x)) / (a ^ 2 + c * x ^ 2) ^ 2) x :=
    (hasDerivAt_const (x := x) (c := 2 * a)).div h1 hxden
  have hnum : (0 * (a ^ 2 + c * x ^ 2) - 2 * a * (2 * c * x)) = -(4 * a * c * x) := by ring
  rw [hnum] at h2
  have hK : cauchyK a c = fun ψ : ℝ => 2 * a / (a ^ 2 + c * ψ ^ 2) :=
    funext (fun ψ => by rw [cauchyK])
  rw [hK, cauchyKderiv]
  exact h2

lemma deriv_cauchyK {a c x : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    deriv (cauchyK a c) x = cauchyKderiv a c x :=
  (hasDerivAt_cauchyK ha hc).deriv

lemma cauchyKderiv_eq_neg_q (a c x : ℝ) : cauchyKderiv a c x = -cauchyKq a c x := by
  rw [cauchyKderiv, cauchyKq]
  ring

lemma cauchyKern_eq_q_mul (a c x : ℝ) : cauchyKern a c x = cauchyKq a c x * x := by
  rw [cauchyKern, cauchyKq]
  ring

lemma cauchyKern_eq_mul_q (a c x : ℝ) : cauchyKern a c x = x * cauchyKq a c x := by
  rw [cauchyKern, cauchyKq]
  ring

end Work.EQ.Fatou
