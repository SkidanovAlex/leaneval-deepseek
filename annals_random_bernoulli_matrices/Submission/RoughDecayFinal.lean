import Mathlib
import Submission.RoughStep10
import Submission.Commons.Analysis.Real.rough_decay_layer0_rpow52

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: Proposition `p: rough decay` in paper counting form

Assembles `Submission.RoughStep10.rough_decay_counting` with the layer-0
real-asymptotic lemma `Commons.Analysis.Real.rough_decay_layer0_abs`
(fleet L46) into the `∃ L n₀` paper form:

for every decay rate `M`, Bernoulli parameter `p ∈ (0,1/2]`, compressibility
slack `δ ∈ (0,1/2]` and `ε ∈ (0,p)` there is an `L ≥ 1` and an `n₀ ≥ 2` such
that for all admissible `(N,n,δ)`-coordinate families `A` (origin-symmetric,
radius-`nN`) and all probability-density candidates `f` with `‖f‖₁ ≤ 1`, the
number of tuples whose level-`ℓ` average exceeds
`max(L/(N√n), (1−p+ε)^ℓ·‖f‖∞)` is at most
`e^{−Mn} · ∏_j |A_j|`.

The `∏|A_j|` on the right is the standard volume factor of the counting
argument; later stages compare the combinatorial object against probability
measures of cylinders, where each `A_j` carries mass `≤ |A_j|·(...)`.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Measure

namespace Submission.RoughDecayFinal

attribute [local instance] Classical.propDecidable

open Submission.Sec3
open Submission.Sec3Tower
open Submission.IntFun
open Submission.RoughDecay
open Submission.RoughDecay2
open Submission.RoughProduct
open Submission.Admissible
open Submission.RoughAssembly
open Submission.ProdCount
open Submission.RoughStep10

/-! ## STEP A: rpow bridge `n^{5/2} = n²·√n` -/

/-- `n^(5/2) = n²·√n` for `n ≥ 1`. -/
lemma rpow52_eq {n : ℕ} (hn1 : 1 ≤ n) :
    (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast (n : ℝ) 2]
  rw [← Real.rpow_add hn]
  congr 1
  norm_num

/-! ## STEP B: positivity of the decay rate `ηdec` -/

/-- `0 < ηdec p ε` for `0 < ε < p ≤ 1/2`. -/
lemma eta_dec_pos {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) :
    0 < ηdec p ε := by
  let a : ℝ := 1 - (p : ℝ) + ε
  let b : ℝ := 1 - (p : ℝ) + ε / 2
  have hb0 : 0 < b := by
    dsimp [b]
    nlinarith [hp₁]
  have hb1 : b < 1 := by
    dsimp [b]
    nlinarith [hp₀]
  have hab : b < a := by
    dsimp [a, b]
    nlinarith [hε0]
  have ha1 : 1 < a / b := (one_lt_div₀ hb0).2 hab
  have hla : 0 < Real.log (a / b) := Real.log_pos ha1
  have hlb : Real.log b < 0 := (Real.log_neg_iff hb0).2 hb1
  dsimp [ηdec]
  change 0 < Real.log (a / b) / (2 * -Real.log b)
  exact div_pos hla (mul_pos (by norm_num : (0 : ℝ) < 2) (neg_pos.mpr hlb))

/-! ## STEP C: cardinality of the root window `D0` -/

/-- `|D0| ≤ 5·N²·n^{5/2}` under `1 ≤ ℓ ≤ n`. -/
lemma D0rd_card_le_5 {ℓ N n : ℕ} (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) (hℓ1 : 1 ≤ ℓ)
    (hℓle : ℓ ≤ n) {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) :
    ((D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum).card : ℝ) ≤
      5 * (N : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ) := by
  have hb := D0rd_card_le (ℓ := ℓ) hN1 hn1 hfpos hfsum hfmass
  have hsq0 : 0 ≤ (N : ℝ) * Real.sqrt (n : ℝ) := by positivity
  have hℓn : (ℓ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hℓle
  have hnN : 1 ≤ n * N := by
    have h := Nat.mul_le_mul hn1 hN1
    simpa using h
  have hx1nat : 1 ≤ ℓ * (n * N) := by
    have h := Nat.mul_le_mul hℓ1 hnN
    simpa using h
  have hx1 : (1 : ℝ) ≤ (ℓ : ℝ) * (n : ℝ) * (N : ℝ) := by
    have h1R : (1 : ℝ) ≤ ((ℓ * (n * N) : ℕ) : ℝ) := by exact_mod_cast hx1nat
    have hc : ((ℓ * (n * N) : ℕ) : ℝ) = (ℓ : ℝ) * (n : ℝ) * (N : ℝ) := by
      simp [Nat.cast_mul]
      ring
    nlinarith
  have h41 : 4 * (ℓ : ℝ) * (n : ℝ) * (N : ℝ) + 1 ≤ 5 * (ℓ : ℝ) * (n : ℝ) * (N : ℝ) := by
    nlinarith
  calc
    ((D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum).card : ℝ)
        ≤ (N : ℝ) * Real.sqrt (n : ℝ) * ((4 * ℓ * (n * N) : ℕ) + 1 : ℝ) := hb
    _ = (N : ℝ) * Real.sqrt (n : ℝ) * (4 * (ℓ : ℝ) * (n : ℝ) * (N : ℝ) + 1) := by
          congr 1
          simp [Nat.cast_add, Nat.cast_mul]
          ring
    _ ≤ (N : ℝ) * Real.sqrt (n : ℝ) * (5 * (ℓ : ℝ) * (n : ℝ) * (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h41 hsq0
    _ = 5 * (N : ℝ) * Real.sqrt (n : ℝ) * (n : ℝ) * (N : ℝ) * (ℓ : ℝ) := by ring
    _ ≤ 5 * (N : ℝ) * Real.sqrt (n : ℝ) * (n : ℝ) * (N : ℝ) * (n : ℝ) := by
          have hmono : 0 ≤ 5 * (N : ℝ) * Real.sqrt (n : ℝ) * (n : ℝ) * (N : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hℓn hmono
    _ = 5 * (N : ℝ) ^ 2 * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by ring
    _ = 5 * (N : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ) := by rw [← rpow52_eq hn1]
/-! ## STEP D: Proposition `p: rough decay` in paper counting form -/

/-- Proposition `p: rough decay` (counting form): for every `M > 0`,
`p ∈ (0,1/2]`, `δ ∈ (0,1/2]` and `ε ∈ (0,p)` there are `L ≥ 1` and `n₀ ≥ 2`
such that for every `n ≥ n₀`, every `1 ≤ N ≤ 2^n`, every `ℓ ∈ [n/2, n]`,
every `(N,n,δ)`-admissible family `A` of origin-symmetric radius-`nN`
coordinate intervals and every nonnegative summable `f` with `‖f‖₁ ≤ 1`,
the number of `x ∈ ∏ A_j` whose level-`ℓ` average exceeds
`max(L/(N√n), (1−p+ε)^ℓ·‖f‖∞)` is at most `e^{−Mn}·∏_j |A_j|`. -/
theorem rough_decay {M : ℝ} (hM : 0 < M) {p : unitInterval} (hp₀ : 0 < (p : ℝ))
    (hp₁ : (p : ℝ) ≤ 1 / 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 < ε) (hεp : ε < (p : ℝ)) :
    ∃ (L : ℝ) (n₀ : ℕ), 1 ≤ L ∧ 2 ≤ n₀ ∧
      ∀ (n : ℕ) (hn₀ : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N)
        (hN2 : (N : ℝ) ≤ (2 : ℝ) ^ n), ∀ (ℓ : ℕ) (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n),
        ∀ (A : Fin ℓ → Finset ℤ) (hAdm : Admissible N n ℓ δ A)
          (hrad : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
          (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j),
        ∀ (f : ℤ → ℝ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
          ((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
            eventPred f p L (N : ℝ) (n : ℝ) ε x)).card ≤
            Real.exp (-M * (n : ℝ)) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  classical
  rcases exists_perStepProp with ⟨Cq₁, hCq₁pos, hPer₁⟩
  rcases exists_twoArmProp with ⟨Cq₂, hCq₂pos, hPer₂⟩
  let η : ℝ := min δ (ηdec p ε)
  let δ₀ : ℝ := η / 2
  have hηpos : 0 < η := by
    dsimp [η]
    rcases le_total δ (ηdec p ε) with h | h
    · rw [min_eq_left h]
      exact hδ0
    · rw [min_eq_right h]
      exact eta_dec_pos hp₀ hp₁ hε0 hεp
  have hη0 : 0 ≤ η := le_of_lt hηpos
  have hηleηdec : η ≤ ηdec p ε := by
    dsimp [η]
    exact min_le_right δ (ηdec p ε)
  have hηleδ : η ≤ δ := by
    dsimp [η]
    exact min_le_left δ (ηdec p ε)
  have hη12 : η ≤ 1 / 2 := le_trans hηleδ hδ12
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact half_pos hηpos
  have hδ₀leδ : δ₀ ≤ δ := by
    dsimp [δ₀]
    calc
      η / 2 ≤ δ / 2 := div_le_div_of_nonneg_right hηleδ (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ δ := by linarith
  let cQ : ℝ := (2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * Real.sqrt (δ₀ * (p : ℝ)))
  have hcQpos : 0 < cQ := by
    dsimp [cQ]
    have hδ₀p : 0 < δ₀ * (p : ℝ) := mul_pos hδ₀pos hp₀
    have hsqrt : 0 < Real.sqrt (δ₀ * (p : ℝ)) := Real.sqrt_pos.2 hδ₀p
    exact div_pos (by positivity) (by positivity)
  rcases Commons.Analysis.Real.rough_decay_layer0_rpow52 hM hηpos hη12 hcQpos with
    ⟨L, n₁, hL1, _hn₁1, hAbs⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL1
  let nslack : ℕ := Nat.ceil (2 / δ)
  let n₀ : ℕ := max (max 2 n₁) nslack
  have h2n₀ : 2 ≤ n₀ := by
    have : 2 ≤ max 2 n₁ := le_max_left 2 n₁
    dsimp [n₀]
    exact le_trans this (le_max_left (max 2 n₁) nslack)
  refine ⟨L, n₀, hL1, h2n₀, ?_⟩
  intro n hn₀ N hN1 hN2 ℓ hℓge hℓle A hAdm hrad hsym f hfpos hfsum hfmass
  have h2n : 2 ≤ n := le_trans h2n₀ hn₀
  have hn1 : 1 ≤ n := by omega
  have hℓ1 : 1 ≤ ℓ := by omega
  have hn₁n : n₁ ≤ n := by
    have h1 : n₁ ≤ max 2 n₁ := le_max_right 2 n₁
    have h2 : max 2 n₁ ≤ n₀ := by dsimp [n₀]; exact le_max_left (max 2 n₁) nslack
    exact le_trans h1 (le_trans h2 hn₀)
  have hnslack₀ : nslack ≤ n := by
    have h1 : nslack ≤ n₀ := by dsimp [n₀]; exact le_max_right (max 2 n₁) nslack
    exact le_trans h1 hn₀
  -- slack: (δ − δ₀)·n ≥ 1 for n ≥ ⌈2/δ⌉
  have hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ) := by
    have h2δ : (2 / δ : ℝ) ≤ (nslack : ℝ) := by
      dsimp [nslack]
      exact Nat.le_ceil (2 / δ)
    have hnslR : (nslack : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnslack₀
    have hn2δ : (2 / δ : ℝ) ≤ (n : ℝ) := le_trans h2δ hnslR
    have hδ2pos : 0 < (δ : ℝ) / 2 := by positivity
    have hδ2n : (δ : ℝ) / 2 * (2 / δ) = 1 := by field_simp [hδ0.ne']
    have hm1 : (1 : ℝ) ≤ (δ : ℝ) / 2 * (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hn2δ (le_of_lt hδ2pos)
      rwa [hδ2n] at hmul
    have hsub : (δ : ℝ) / 2 ≤ δ - δ₀ := by
      dsimp [δ₀]
      have hη2leδ2 : η / 2 ≤ δ / 2 := div_le_div_of_nonneg_right hηleδ (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    have hnR0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hm2 : (δ : ℝ) / 2 * (n : ℝ) ≤ (δ - δ₀) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hsub hnR0
    exact le_trans hm1 hm2
  let qexpr : ℝ := (2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))
  let prod : ℝ := ∏ j : Fin ℓ, ((A j).card : ℝ)
  let D0 : Finset ℤ := D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum
  have hqeq : qexpr = cQ / L := by
    dsimp [qexpr, cQ]
    have hδ₀p : 0 < δ₀ * (p : ℝ) := mul_pos hδ₀pos hp₀
    have hsqrt0 : Real.sqrt (δ₀ * (p : ℝ)) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 hδ₀p)
    field_simp [hL0.ne', hε0.ne', hsqrt0]
  have hcQL1 : cQ / L ≤ 1 := (hAbs n hn₁n N hN1 hN2 ℓ hℓge hℓle).1
  have hq1 : qexpr ≤ 1 := by
    rwa [← hqeq] at hcQL1
  have hcnt := rough_decay_counting hn1 hδ₀pos hδ₀leδ hslack hp₀ hp₁ hε0 hεp hL0 hL1
    hN1 hℓge hℓle hfpos hfsum hfmass hη0 hηleηdec hAdm hrad hsym
    Cq₁ hCq₁pos Cq₂ hCq₂pos hPer₁ hPer₂ hq1
  let X0 : ℝ := (2 : ℝ) ^ ℓ * ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
    qexpr ^ (Nat.ceil (η * (n : ℝ)) - Nat.ceil (δ₀ * (n : ℝ))) * prod
  have hqexprpos : 0 < qexpr := by
    dsimp [qexpr]
    have hδ₀p : 0 < δ₀ * (p : ℝ) := mul_pos hδ₀pos hp₀
    have hsqrt : 0 < Real.sqrt (δ₀ * (p : ℝ)) := Real.sqrt_pos.2 hδ₀p
    exact div_pos (by positivity) (by positivity)
  have hX0 : 0 ≤ X0 := by
    dsimp [X0]
    have h2 : 0 ≤ (2 : ℝ) ^ ℓ := pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ℓ
    have hC : 0 ≤ ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    have hqpow : 0 ≤ qexpr ^ (Nat.ceil (η * (n : ℝ)) - Nat.ceil (δ₀ * (n : ℝ))) :=
      pow_nonneg (le_of_lt hqexprpos) _
    have hprod0 : 0 ≤ prod := by
      dsimp [prod]
      exact Finset.prod_nonneg (fun j _ => by exact_mod_cast (Nat.zero_le (A j).card))
    exact mul_nonneg (mul_nonneg (mul_nonneg h2 hC) hqpow) hprod0
  have h5 : ((D0).card : ℝ) ≤ 5 * (N : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2) :=
    D0rd_card_le_5 hN1 hn1 hℓ1 hℓle hfpos hfsum hfmass
  calc
    ((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
        eventPred f p L (N : ℝ) (n : ℝ) ε x)).card
        ≤ ((D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum).card : ℝ) * (2 : ℝ) ^ ℓ *
            ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
            ((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ^
              (Nat.ceil (η * (n : ℝ)) - Nat.ceil (δ₀ * (n : ℝ))) *
            (∏ j : Fin ℓ, ((A j).card : ℝ)) := hcnt
    _ = ((D0rd (ℓ := ℓ) hN1 hn1 f hfpos hfsum).card : ℝ) * X0 := by ring
    _ ≤ (5 * (N : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2)) * X0 := by
          exact mul_le_mul_of_nonneg_right h5 hX0
    _ = 5 * (N : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2) * (2 : ℝ) ^ ℓ *
          ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
          qexpr ^ (Nat.ceil (η * (n : ℝ)) - Nat.ceil (δ₀ * (n : ℝ))) * prod := by ring
    _ = 5 * (N : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2) * (2 : ℝ) ^ ℓ *
          ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
          (cQ / L) ^ (Nat.ceil (η * (n : ℝ)) - Nat.ceil (δ₀ * (n : ℝ))) * prod := by
          rw [hqeq]
    _ ≤ Real.exp (-M * (n : ℝ)) * prod := by
          have hlay := (hAbs n hn₁n N hN1 hN2 ℓ hℓge hℓle).2
          have hprod0 : 0 ≤ prod := by
            dsimp [prod]
            exact Finset.prod_nonneg (fun j _ => by exact_mod_cast (Nat.zero_le (A j).card))
          exact mul_le_mul_of_nonneg_right hlay hprod0

end Submission.RoughDecayFinal
