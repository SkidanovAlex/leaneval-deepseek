import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_const
import Submission.Work.BMF.adi_main
import Submission.Work.BMF.consts_le_C1c
import Submission.Work.BMF.Ceps2_add_le
import Submission.Work.BMF.qfin_bound
import Submission.Work.BMF.qfin_dvd
import Submission.Work.BMF.K_absorb
import Submission.Work.BMF.exists_lattice_points
import Submission.Work.BMF.gamma_integral
import Submission.Work.BMF.eps_deriv_eq
import Submission.Work.BMF.poly_deriv_bound
import Submission.Work.BMF.sum_tay_deriv_bound
import Submission.Work.BMF.IntegralOn_dil_sub
import Submission.Work.BMF.eps2_final_bound
import Submission.Work.BMF.deriv_sub_log_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

/-!
# N6 `solve_adi`: solving the approximate dilation invariance (MRTTZ Prop. 3.8)

Given `P_i(a_i ·) ~ P_i(b_i ·)` and the edge relation `P₁(p₂ ·) ~ P₂(p₁ ·)` modulo `1/Qm` with
`Qm` huge compared with `Z = a₁a₂p₁p₂NL`, the polynomials are `P_i = ε_i + (T/2π) log + γ_i`
with `γ_i` integral on a lattice `(q/Qm)ℤ`, `q ≤ Z^{K₀}`, `|T| ≤ C₁N^{k+1}` and
`|ε_i'| ≤ C₁/L`, together with `γ₁(p₂ ·) - γ₂(p₁ ·)` integer valued.

The proof runs the degree descent `Work.BMF.DInv`/`dstep` for each side and then uses the edge
relation to identify the two constants `T` and to make the two lattice parts congruent.
-/

namespace Work.BMF

open Polynomial

/-- Degree bound from `degreeLE`. -/
theorem natDegree_le_of_mem_degreeLE {k : ℕ} {p : ℝ[X]} (h : p ∈ degreeLE ℝ (k : WithBot ℕ)) :
    p.natDegree ≤ k :=
  (Polynomial.natDegree_le_iff_degree_le).mpr (Polynomial.mem_degreeLE.mp h)

/-- A polynomial of degree `≤ k` taking the same value at `k+1` distinct points is constant. -/
theorem poly_eq_C_of_eval_eq {k : ℕ} {G : ℝ[X]} (hdeg : G.natDegree ≤ k) {c : ℝ}
    {v : Fin (k + 1) → ℝ} (hv : Function.Injective v) (h : ∀ i, G.eval (v i) = c) :
    G = C c := by
  have hdeg' : (G - C c).natDegree ≤ k := by
    refine le_trans (natDegree_sub_le _ _) ?_
    rw [natDegree_C]
    exact max_le hdeg (Nat.zero_le _)
  have hroot : ∀ i, (G - C c).eval (v i) = 0 := by
    intro i
    rw [eval_sub, h i, eval_C, sub_self]
  have hzero : G - C c = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (G - C c) hv hroot ?_
    rw [Fintype.card_fin]
    omega
  exact sub_eq_zero.mp hzero

/-- Two integers at distance `< 1` are equal. -/
theorem int_eq_of_abs_sub_lt_one {y y' : ℝ} (hy : ∃ m : ℤ, y = (m : ℝ))
    (hy' : ∃ m : ℤ, y' = (m : ℝ)) (h : |y - y'| < 1) : y = y' := by
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := hy'
  have h1 : (m : ℝ) < (n : ℝ) + 1 := by
    have := lt_of_le_of_lt (le_abs_self ((m : ℝ) - (n : ℝ))) h
    linarith
  have h2 : (n : ℝ) < (m : ℝ) + 1 := by
    have := lt_of_le_of_lt (neg_le_abs ((m : ℝ) - (n : ℝ))) h
    linarith
  have h1' : m ≤ n := by
    by_contra hc
    push_neg at hc
    have hc' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hc
    linarith
  have h2' : n ≤ m := by
    by_contra hc
    push_neg at hc
    have hc' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hc
    linarith
  exact_mod_cast (le_antisymm h1' h2')

/-- Derivative of a dilate. -/
theorem eval_dil (a t : ℝ) (P : ℝ[X]) : (dil a P).eval t = P.eval (a * t) := by
  simp [dil, eval_comp]

/-- A function which agrees with a constant near `t` has zero derivative at `t`. -/
theorem deriv_eq_zero_of_eventuallyEq_const {F : ℝ → ℝ} {c t : ℝ}
    (h : F =ᶠ[nhds t] (fun _ => c)) : deriv F t = 0 := by
  rw [h.deriv_eq, deriv_const]

/-- One-sided descent from a `PolyRel` hypothesis. -/
theorem descent_of_polyrel (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) {P : ℝ[X]} {x L N : ℝ}
    {a b Qm : ℕ} (hdeg : P.natDegree ≤ k) (hL : 2 ≤ L) (hN : 100 * C₀ ^ 4 ≤ N)
    (hx1 : N * L ≤ C₀ * x) (hx2 : x ≤ C₀ * (N * L)) (hxpos : 0 < x) (hQm : 1 ≤ Qm)
    (hb : 1 ≤ b) (hba : b < a) (ha1 : (a : ℝ) ≤ C₀ * N * ((a : ℝ) - b))
    (ha2 : N * ((a : ℝ) - b) ≤ C₀ * a)
    (hrel : PolyRel k C₀ (1 / (Qm : ℝ)) (x / a) (L / a) (dil a P) (x / b) (L / b) (dil b P)) :
    ∃ c0 : ℝ, ∃ T mu : ℕ → ℝ,
      (P = C c0 + ∑ m ∈ Finset.Icc 1 k,
        (C (T m / (2 * Real.pi)) * Tay m x + C (mu m) * X ^ m)) ∧
      (∀ m ∈ Finset.Icc 1 k, |T m| ≤ CTc k C₀ * N ^ (m + 1)) ∧
      (∀ m ∈ Finset.Icc 1 k, ∃ z : ℤ,
        mu m = z * (Qm : ℝ) ^ m /
          (((Dfac k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) *
            (((qj a b m : ℕ) : ℝ)))) := by
  rw [PolyRel] at hrel
  obtain ⟨-, -, -, ε, γ, hdegε, hdegγ, hrel', hbd, hint⟩ := hrel
  refine descent_result ⟨k, C₀, a, b, x, L, Qm, N, P⟩
    ⟨hC₀, hdeg, hL, hN, hQm, hxpos, hx1, hx2, hb, hba, ha1, ha2⟩ ε γ ?_ ?_ ?_ ?_ ?_
  · exact natDegree_le_of_mem_degreeLE hdegε
  · exact natDegree_le_of_mem_degreeLE hdegγ
  · rw [hrel']; ring
  · have hval : x / (a : ℝ) + L / (a : ℝ) = (x + L) / (a : ℝ) := by ring
    intro t ht
    refine hbd t ?_
    rw [Set.mem_Icc] at ht ⊢
    exact ⟨ht.1, by rw [hval]; exact ht.2⟩
  · exact hint

/-- `400 ≤ a*b*c*d*e` from `2 ≤ a`, `1 ≤ b`, `1 ≤ c`, `100 ≤ d`, `2 ≤ e`. -/
theorem le_prod5 {a b c d e : ℝ} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 100 ≤ d)
    (he : 2 ≤ e) : 400 ≤ a * b * c * d * e := by
  have h1 : (0 : ℝ) ≤ a := by linarith
  have h2 : (0 : ℝ) ≤ b := by linarith
  have h3 : (0 : ℝ) ≤ c := by linarith
  have h4 : (0 : ℝ) ≤ d := by linarith
  have h5 : (0 : ℝ) ≤ e := by linarith
  have e1 : 2 ≤ a * b := by nlinarith
  have e2 : 2 ≤ a * b * c := by nlinarith
  have e3 : 200 ≤ a * b * c * d := by nlinarith
  have e4 : 400 ≤ a * b * c * d * e := by nlinarith
  linarith

/-- `1 ≤ a*b*c*d*e` from `1 ≤ a`, `1 ≤ b`, `1 ≤ c`, `100 ≤ d`, `2 ≤ e`. -/
theorem one_le_prod5 {a b c d e : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 100 ≤ d)
    (he : 2 ≤ e) : 1 ≤ a * b * c * d * e := by
  have h1 : (0 : ℝ) ≤ a := by linarith
  have h2 : (0 : ℝ) ≤ b := by linarith
  have h3 : (0 : ℝ) ≤ c := by linarith
  have h4 : (0 : ℝ) ≤ d := by linarith
  have h5 : (0 : ℝ) ≤ e := by linarith
  have e1 : 1 ≤ a * b := by nlinarith
  have e2 : 1 ≤ a * b * c := by nlinarith
  have e3 : 100 ≤ a * b * c * d := by nlinarith
  have e4 : 1 ≤ a * b * c * d * e := by nlinarith
  linarith

/-- `2 ≤ a*b*c*d*e*f` from `2 ≤ a`, `2 ≤ b`, `1 ≤ c`, `1 ≤ d`, `100 ≤ e`, `2 ≤ f`. -/
theorem two_le_prod6 {a b c d e f : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (he : 100 ≤ e) (hf : 2 ≤ f) : 2 ≤ a * b * c * d * e * f := by
  have h1 : (0 : ℝ) ≤ a := by linarith
  have h2 : (0 : ℝ) ≤ b := by linarith
  have h3 : (0 : ℝ) ≤ c := by linarith
  have h4 : (0 : ℝ) ≤ d := by linarith
  have h5 : (0 : ℝ) ≤ e := by linarith
  have h6 : (0 : ℝ) ≤ f := by linarith
  have e1 : 4 ≤ a * b := by nlinarith
  have e2 : 4 ≤ a * b * c := by nlinarith
  have e3 : 4 ≤ a * b * c * d := by nlinarith
  have e4 : 400 ≤ a * b * c * d * e := by nlinarith
  have e5 : 800 ≤ a * b * c * d * e * f := by nlinarith
  linarith

/-- `CTc` is nonnegative. -/
theorem CTc_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : 0 ≤ CTc k C₀ := by
  have hC0nn : (0 : ℝ) ≤ C₀ := le_trans zero_le_one hC₀
  have hA : 0 ≤ Alev k C₀ 0 := Alev_nonneg k C₀ hC₀ (Nat.zero_le k)
  have h1 : 0 ≤ CT1 k C₀ := by
    unfold CT1
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 : (0 : ℝ) ≤ (k : ℝ) ^ k := pow_nonneg h2 k
    have h4 : (0 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have h5 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h5) h2)
      h4) h3) hC0nn
  have h5 : (0 : ℝ) ≤ C₀ ^ k := pow_nonneg hC0nn k
  unfold CTc
  exact mul_nonneg (mul_nonneg hA h1) h5

/-- Mean value bound: a function whose derivative is bounded by `C` on the interval spanned by
`u` and `v` has `|f v - f u| ≤ C |v - u|`. -/
theorem abs_sub_le_of_deriv_bound {f : ℝ → ℝ} {g : ℝ → ℝ} {u v C : ℝ}
    (hderiv : ∀ x ∈ Set.Icc (min u v) (max u v), HasDerivAt f (g x) x)
    (hbd : ∀ x ∈ Set.Icc (min u v) (max u v), |g x| ≤ C) :
    |f v - f u| ≤ C * |v - u| := by
  have hcvx : Convex ℝ (Set.Icc (min u v) (max u v)) := convex_Icc _ _
  have h1 : ∀ x ∈ Set.Icc (min u v) (max u v), DifferentiableAt ℝ f x :=
    fun x hx => (hderiv x hx).differentiableAt
  have h2 : ∀ x ∈ Set.Icc (min u v) (max u v), ‖deriv f x‖ ≤ C := by
    intro x hx
    rw [(hderiv x hx).deriv]
    simpa using hbd x hx
  have hu : u ∈ Set.Icc (min u v) (max u v) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hv : v ∈ Set.Icc (min u v) (max u v) := ⟨min_le_right _ _, le_max_right _ _⟩
  have := hcvx.norm_image_sub_le_of_norm_deriv_le h1 h2 hu hv
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact this


/-- A dilate of a lattice-integral polynomial is lattice-integral. -/
theorem IntegralOn.dil (p : ℕ) (δ : ℝ) {γ : ℝ[X]} (h : IntegralOn δ γ) :
    IntegralOn δ (dil (p : ℝ) γ) := by
  intro n
  obtain ⟨z, hz⟩ := h ((p : ℤ) * n)
  refine ⟨z, ?_⟩
  rw [eval_dil]
  convert hz using 2
  push_cast
  ring

/-- The interval spanned by two points of `[a,b]` stays in `[a,b]`. -/
theorem min_max_mem {a b t t' : ℝ} (ht : t ∈ Set.Icc a b) (ht' : t' ∈ Set.Icc a b) :
    ∀ x ∈ Set.Icc (min t t') (max t t'), x ∈ Set.Icc a b := by
  intro x hx
  rw [Set.mem_Icc] at hx ⊢
  exact ⟨le_trans (le_min ht.1 ht'.1) hx.1, le_trans hx.2 (max_le ht.2 ht'.2)⟩

/-- `Kc k = (Kc k - K0c k - k - 1) + (K0c k + k + 1)`. -/
theorem Kc_sub (k : ℕ) : Kc k = (Kc k - K0c k - k - 1) + (K0c k + k + 1) := by
  unfold Kc K0c Eexp
  omega

/-- The exponent bookkeeping of the final modulus comparison. -/
theorem main_ineq_gen (k : ℕ) (C₀ Z c1 : ℝ) (hZ1 : 1 ≤ Z)
    (hKabs : ((k : ℝ) + 1) * c1 * C₀ ^ k ≤ Z ^ (Kc k - K0c k - k - 1)) :
    ((k : ℝ) + 1) * Z ^ (K0c k) * c1 * (C₀ * Z) ^ k * Z ≤ 2 * Z ^ (Kc k) := by
  have hZpos : 0 < Z := lt_of_lt_of_le one_pos hZ1
  have hZnn : 0 ≤ Z := le_of_lt hZpos
  have hCZ : (C₀ * Z) ^ k = C₀ ^ k * Z ^ k := mul_pow C₀ Z k
  have hZa : Z ^ (Kc k) = Z ^ (Kc k - K0c k - k - 1) * Z ^ (K0c k + k + 1) := by
    conv_lhs => rw [Kc_sub k, pow_add]
  have hpow : Z ^ (K0c k) * Z ^ k * Z = Z ^ (K0c k + k + 1) := by
    rw [mul_assoc, ← pow_succ, ← pow_add, Nat.add_assoc]
  have heq : ((k : ℝ) + 1) * Z ^ (K0c k) * c1 * (C₀ * Z) ^ k * Z =
      ((k : ℝ) + 1) * c1 * C₀ ^ k * Z ^ (K0c k + k + 1) := by
    rw [hCZ]
    have hrep : ((k : ℝ) + 1) * Z ^ (K0c k) * c1 * (C₀ ^ k * Z ^ k) * Z =
        ((k : ℝ) + 1) * c1 * C₀ ^ k * (Z ^ (K0c k) * Z ^ k * Z) := by ring
    rw [hrep, hpow]
  rw [heq]
  have hfin : Z ^ (Kc k - K0c k - k - 1) * Z ^ (K0c k + k + 1) ≤ 2 * Z ^ (Kc k) := by
    rw [← hZa]
    exact le_mul_of_one_le_left (pow_nonneg hZnn _) (by norm_num)
  exact le_trans (mul_le_mul_of_nonneg_right hKabs (pow_nonneg hZnn _)) hfin

/-- `2 ≤ C₁c k C₀`. -/
theorem C1c_ge_two (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : (2 : ℝ) ≤ C1c k C₀ := by
  rw [C1c]
  have hb : (1 : ℝ) ≤ C₀ + 2 := by linarith
  have h1 : (3 : ℝ) ^ 100 ≤ (C₀ + 2) ^ (Eexp k) := by
    calc (3 : ℝ) ^ 100 ≤ (C₀ + 2) ^ 100 := pow_le_pow_left₀ (by norm_num) (by linarith) 100
      _ ≤ (C₀ + 2) ^ (Eexp k) := by
          refine pow_le_pow_right₀ hb ?_
          rw [Eexp]; omega
  have h2 : (2 : ℝ) ≤ 3 ^ 100 := by norm_num
  linarith

/-- `C₀ + 2 ≤ 3 C₀` for `C₀ ≥ 1`. -/
theorem add_two_le_three_mul {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : C₀ + 2 ≤ 3 * C₀ := by linarith

/-- `(C₀+2)^3 ≤ 40000 C₀^3` for `C₀ ≥ 1`. -/
theorem base_pow3_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : (C₀ + 2) ^ 3 ≤ 40000 * C₀ ^ 3 := by
  have h3 : C₀ + 2 ≤ 3 * C₀ := add_two_le_three_mul hC₀
  have h6 : (0 : ℝ) ≤ C₀ + 2 := by linarith
  have h7 : (C₀ + 2) ^ 3 ≤ (3 * C₀) ^ 3 := pow_le_pow_left₀ h6 h3 3
  have h8 : (3 * C₀) ^ 3 = 27 * C₀ ^ 3 := by ring
  have h9 : (0 : ℝ) ≤ C₀ ^ 3 := by positivity
  nlinarith [h7, h8, h9]

/-- `100 C₀^3 ≤ 100 C₀^4` for `C₀ ≥ 1`. -/
theorem hundred_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 100 * C₀ ^ 3 ≤ 100 * C₀ ^ 4 := by
  have h : C₀ ^ 3 ≤ C₀ ^ 4 := pow_le_pow_right₀ hC₀ (by norm_num)
  linarith

/-- `6 C₀^3 ≤ 100 C₀^4` for `C₀ ≥ 1`. -/
theorem six_le_hundred {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 6 * C₀ ^ 3 ≤ 100 * C₀ ^ 4 := by
  have h1 : (0 : ℝ) ≤ C₀ ^ 3 := by positivity
  have h2 : 6 * C₀ ^ 3 ≤ 100 * C₀ ^ 3 := by linarith
  have h3 := hundred_le hC₀
  linarith

/-- The `ε₁` derivative bound on `Icc x₁ (x₁+L)`. -/
theorem eps_sum_bound_1 (k : ℕ) (C₀ x₁ L N : ℝ) (hC₀ : 1 ≤ C₀) (hLpos : 0 < L)
    (hNpos : 0 < N) (hx1a : N * L ≤ C₀ * x₁) (hx1pos : 0 < x₁) {T1 : ℕ → ℝ}
    (hT1 : ∀ m ∈ Finset.Icc 1 k, |T1 m| ≤ CTc k C₀ * N ^ (m + 1))
    {t : ℝ} (htpos : 0 < t) (ht1 : x₁ ≤ t) (ht2 : t ≤ x₁ + L) :
    |∑ m ∈ Finset.Icc 1 k, T1 m / (2 * Real.pi) *
        ((Tay m x₁).derivative.eval t - 1 / t)| ≤ Ceps1 k C₀ / L := by
  have hC0pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hctc0 : 0 ≤ CTc k C₀ := CTc_nonneg k C₀ hC₀
  have htd : |t - x₁| ≤ L := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hsum := sum_tay_deriv_bound (T := T1) (CT := CTc k C₀) (N := N)
    hx1pos htpos (le_of_lt hLpos) htd hNpos hctc0 hT1
  refine le_trans hsum ?_
  have hmax : max 1 ((N * L / x₁) ^ k) ≤ C₀ ^ k := by
    refine max_le (one_le_pow₀ hC₀) ?_
    refine pow_le_pow_left₀ (by positivity) ?_ k
    rw [div_le_iff₀ hx1pos]
    linarith
  have htge : N * L / C₀ ≤ t := by
    have h1 : N * L / C₀ ≤ x₁ := by rw [div_le_iff₀ hC0pos]; linarith
    linarith
  have hNLt : N * L ≤ C₀ * t := by
    have h1 : N * L ≤ C₀ * x₁ := hx1a
    exact le_trans h1 (mul_le_mul_of_nonneg_left ht1 (le_of_lt hC0pos))
  have hcoef : ((k : ℝ) + 1) * CTc k C₀ * N / (2 * Real.pi * t) ≤
      ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((k : ℝ) + 1) * CTc k C₀ * N * (2 * Real.pi * L)
        = ((k : ℝ) + 1) * CTc k C₀ * (2 * Real.pi) * (N * L) := by ring
      _ ≤ ((k : ℝ) + 1) * CTc k C₀ * (2 * Real.pi) * (C₀ * t) :=
          mul_le_mul_of_nonneg_left hNLt (by positivity)
      _ = ((k : ℝ) + 1) * CTc k C₀ * C₀ * (2 * Real.pi * t) := by ring
  calc ((k : ℝ) + 1) * CTc k C₀ * N / (2 * Real.pi * t) * max 1 ((N * L / x₁) ^ k)
      ≤ ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi * L) * C₀ ^ k :=
        mul_le_mul hcoef hmax (by positivity) (by positivity)
    _ = Ceps1 k C₀ / L := by rw [Ceps1]; ring

/-- The `ε₂` derivative bound on the enlarged interval `[x₂ - 3C₀²L, x₂ + 3C₀²L]`. -/
theorem eps_sum_bound_2 (k : ℕ) (C₀ x₂ L N : ℝ) (hC₀ : 1 ≤ C₀) (hLpos : 0 < L)
    (hNpos : 0 < N) (hx2a : N * L ≤ C₀ * x₂) (hx2pos : 0 < x₂) (hN6 : 6 * C₀ ^ 3 ≤ N)
    {T2 : ℕ → ℝ} (hT2 : ∀ m ∈ Finset.Icc 1 k, |T2 m| ≤ CTc k C₀ * N ^ (m + 1))
    {t : ℝ} (htpos : 0 < t) (ht1 : x₂ - 3 * C₀ ^ 2 * L ≤ t)
    (ht2 : t ≤ x₂ + 3 * C₀ ^ 2 * L) :
    |∑ m ∈ Finset.Icc 1 k, T2 m / (2 * Real.pi) *
        ((Tay m x₂).derivative.eval t - 1 / t)| ≤ Ceps2 k C₀ / L := by
  have hC0pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hctc0 : 0 ≤ CTc k C₀ := CTc_nonneg k C₀ hC₀
  have htd : |t - x₂| ≤ 3 * C₀ ^ 2 * L := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hlam2 : (0 : ℝ) < 3 * C₀ ^ 2 * L := by positivity
  have hsum := sum_tay_deriv_bound (T := T2) (CT := CTc k C₀) (N := N)
    hx2pos htpos (le_of_lt hlam2) htd hNpos hctc0 hT2
  refine le_trans hsum ?_
  have hmax : max 1 ((N * (3 * C₀ ^ 2 * L) / x₂) ^ k) ≤ (3 * C₀ ^ 3) ^ k := by
    refine max_le ?_ ?_
    · exact one_le_pow₀ (by nlinarith [hC₀, hC0pos] : (1 : ℝ) ≤ 3 * C₀ ^ 3)
    · refine pow_le_pow_left₀ (by positivity) ?_ k
      rw [div_le_iff₀ hx2pos]
      nlinarith [hx2a, hC0pos, hNpos, hLpos]
  have hsplit : 3 * C₀ ^ 2 * L ≤ N * L / (2 * C₀) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hN6, hC0pos]
  have hnlt : N * L ≤ 2 * C₀ * t := by
    have h1 : C₀ * (x₂ - 3 * C₀ ^ 2 * L) ≤ C₀ * t :=
      mul_le_mul_of_nonneg_left ht1 (le_of_lt hC0pos)
    have h2 : C₀ * (x₂ - 3 * C₀ ^ 2 * L) = C₀ * x₂ - 3 * C₀ ^ 3 * L := by ring
    nlinarith [h1, h2, hx2a, hN6, hC0pos, hNpos, hLpos]
  have hcoef : ((k : ℝ) + 1) * CTc k C₀ * N / (2 * Real.pi * t) ≤
      ((k : ℝ) + 1) * CTc k C₀ * (2 * C₀) / (2 * Real.pi * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((k : ℝ) + 1) * CTc k C₀ * N * (2 * Real.pi * L)
        = ((k : ℝ) + 1) * CTc k C₀ * (2 * Real.pi) * (N * L) := by ring
      _ ≤ ((k : ℝ) + 1) * CTc k C₀ * (2 * Real.pi) * (2 * C₀ * t) :=
          mul_le_mul_of_nonneg_left hnlt (by positivity)
      _ = ((k : ℝ) + 1) * CTc k C₀ * (2 * C₀) * (2 * Real.pi * t) := by ring
  calc ((k : ℝ) + 1) * CTc k C₀ * N / (2 * Real.pi * t) *
        max 1 ((N * (3 * C₀ ^ 2 * L) / x₂) ^ k)
      ≤ ((k : ℝ) + 1) * CTc k C₀ * (2 * C₀) / (2 * Real.pi * L) * (3 * C₀ ^ 3) ^ k :=
        mul_le_mul hcoef hmax (by positivity) (by positivity)
    _ = Ceps2 k C₀ / L := by rw [Ceps2]; ring

/-- Nonnegativity of `Ceps1`. -/
theorem Ceps1_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : 0 ≤ Ceps1 k C₀ := by
  rw [Ceps1]
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (CTc_nonneg k C₀ hC₀))
    (pow_nonneg (by linarith : (0:ℝ) ≤ C₀) _)) (by positivity)

/-- Nonnegativity of `Ceps2`. -/
theorem Ceps2_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : 0 ≤ Ceps2 k C₀ := by
  rw [Ceps2]
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (CTc_nonneg k C₀ hC₀))
    (by linarith : (0:ℝ) ≤ C₀)) (pow_nonneg (by positivity) _)) Real.pi_pos.le

/-- Nonnegativity of `C2c`. -/
theorem C2c_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : 0 ≤ C2c k C₀ := by
  rw [C2c]
  exact add_nonneg (add_nonneg (Ceps1_nonneg k C₀ hC₀)
    (mul_nonneg (by linarith : (0:ℝ) ≤ C₀) (Ceps2_nonneg k C₀ hC₀)))
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (by linarith : (0:ℝ) ≤ C₀))

/-- Nonnegativity of `Cgs`. -/
theorem Cgs_nonneg (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) : 0 ≤ Cgs k C₀ := by
  rw [Cgs]
  exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by positivity) (CTc_nonneg k C₀ hC₀))
    (by linarith : (0:ℝ) ≤ C₀)) (by positivity)) (C2c_nonneg k C₀ hC₀)

/-- The `Δ/t` term of `G'`. -/
theorem asm_termA (k : ℕ) (C₀ t N L p₂ : ℝ) (hC₀ : 1 ≤ C₀) (hTc : 0 ≤ CTc k C₀)
    (hN : 1 ≤ N) (hL : 0 < L) (hp₂ : 0 < p₂)
    (ht : N * L / (C₀ * p₂) ≤ t)
    {d : ℝ} (hd : |d| ≤ 2 * (((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1))) :
    |d / (2 * Real.pi) / t| ≤ 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi) * N ^ k * p₂ / L := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  rw [div_div, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * t)]
  refine le_trans (div_le_div_of_nonneg_right hd (by positivity)) ?_
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi * t)]
  have hkey : N * L ≤ C₀ * p₂ * t := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < C₀ * p₂)).mp ht
    linarith
  have hNk : (0:ℝ) ≤ N ^ k := le_of_lt (pow_pos hNpos k)
  have hcoef : (0:ℝ) ≤ 2 * ((k:ℝ)+1) * CTc k C₀ * N ^ k := by positivity
  have hkey' : N ≤ C₀ * p₂ * t / L := by rw [le_div_iff₀ hL]; linarith
  have hterm : 2 * (((k:ℝ)+1) * CTc k C₀ * N ^ (k+1)) ≤
      2 * ((k:ℝ)+1) * CTc k C₀ * N ^ k * (C₀ * p₂ * t / L) := by
    calc 2 * (((k:ℝ)+1) * CTc k C₀ * N ^ (k+1))
        = (2 * ((k:ℝ)+1) * CTc k C₀ * N ^ k) * N := by rw [pow_succ]; ring
      _ ≤ (2 * ((k:ℝ)+1) * CTc k C₀ * N ^ k) * (C₀ * p₂ * t / L) :=
          mul_le_mul_of_nonneg_left hkey' hcoef
      _ = 2 * ((k:ℝ)+1) * CTc k C₀ * N ^ k * (C₀ * p₂ * t / L) := by ring
  have hM : (2 * ((k:ℝ)+1) * CTc k C₀ * C₀ / (2 * Real.pi) * N ^ k * p₂ / L) *
      (2 * Real.pi * t) = 2 * ((k:ℝ)+1) * CTc k C₀ * N ^ k * (C₀ * p₂ * t / L) := by
    field_simp
  rw [hM]
  linarith [hterm]

/-- The `p₂ ε₁'` term of `G'`. -/
theorem asm_termB (k : ℕ) (C₀ N L p₂ : ℝ) (hN : 1 ≤ N) (hL : 0 < L) (hp₂ : 0 < p₂)
    (hCe : 0 ≤ Ceps1 k C₀) {d : ℝ} (hd : |d| ≤ Ceps1 k C₀ / L) :
    |p₂ * d| ≤ Ceps1 k C₀ * N ^ k * p₂ / L := by
  rw [abs_mul, abs_of_pos hp₂]
  refine le_trans (mul_le_mul_of_nonneg_left hd (le_of_lt hp₂)) ?_
  conv_lhs => rw [← mul_div_assoc]
  have hNk : (1:ℝ) ≤ N ^ k := one_le_pow₀ hN
  have h2 : p₂ * Ceps1 k C₀ ≤ Ceps1 k C₀ * N ^ k * p₂ := by
    calc p₂ * Ceps1 k C₀ = Ceps1 k C₀ * p₂ := by ring
      _ ≤ Ceps1 k C₀ * p₂ * N ^ k := le_mul_of_one_le_right (mul_nonneg hCe (le_of_lt hp₂)) hNk
      _ = Ceps1 k C₀ * N ^ k * p₂ := by ring
  exact div_le_div_of_nonneg_right h2 (le_of_lt hL)

/-- The `p₁ ε₂'` term of `G'`. -/
theorem asm_termC (k : ℕ) (C₀ p₁ p₂ N L : ℝ) (hC₀ : 0 ≤ C₀) (hp1 : 0 < p₁) (hp2 : 0 < p₂)
    (hL : 0 < L) (hN : 1 ≤ N) (hp1p2 : p₁ ≤ C₀ * p₂) (hCe : 0 ≤ Ceps2 k C₀)
    {d : ℝ} (hd : |d| ≤ Ceps2 k C₀ / L) :
    |p₁ * d| ≤ C₀ * Ceps2 k C₀ * N ^ k * p₂ / L := by
  rw [abs_mul, abs_of_pos hp1]
  refine le_trans (mul_le_mul_of_nonneg_left hd (le_of_lt hp1)) ?_
  conv_lhs => rw [← mul_div_assoc]
  have hNk : (1:ℝ) ≤ N ^ k := one_le_pow₀ hN
  have h2 : p₁ * Ceps2 k C₀ ≤ C₀ * Ceps2 k C₀ * N ^ k * p₂ := by
    calc p₁ * Ceps2 k C₀ ≤ (C₀ * p₂) * Ceps2 k C₀ := mul_le_mul_of_nonneg_right hp1p2 hCe
      _ = C₀ * Ceps2 k C₀ * p₂ := by ring
      _ ≤ C₀ * Ceps2 k C₀ * p₂ * N ^ k := le_mul_of_one_le_right (by positivity) hNk
      _ = C₀ * Ceps2 k C₀ * N ^ k * p₂ := by ring
  exact div_le_div_of_nonneg_right h2 (le_of_lt hL)

/-- The `ε†'` (Markov) term of `G'`, with the `N^k` absorbed. -/
theorem asm_termD (k : ℕ) (C₀ N L p₂ : ℝ) (hC₀ : 0 ≤ C₀) (hL : 0 < L) (hp2 : 0 < p₂)
    (hN : 1 ≤ N) {d : ℝ} (hd : |d| ≤ 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂ / L) :
    |d| ≤ 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * N^k * p₂ / L := by
  have hNk : (1:ℝ) ≤ N ^ k := one_le_pow₀ hN
  refine le_trans hd ?_
  calc 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂ / L
      = (2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂) / L := by ring
    _ ≤ (2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂) * N ^ k / L :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hNk) (le_of_lt hL)
    _ = 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * N ^ k * p₂ / L := by ring

/-- Combining the four terms of `G'`. -/
theorem asm_four (k : ℕ) (C₀ N L p₂ A B C D : ℝ)
    (hA : |A| ≤ 2 * ((k:ℝ)+1) * CTc k C₀ * C₀ / (2*Real.pi) * N^k * p₂ / L)
    (hB : |B| ≤ Ceps1 k C₀ * N^k * p₂ / L)
    (hC : |C| ≤ C₀ * Ceps2 k C₀ * N^k * p₂ / L)
    (hD : |D| ≤ 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * N^k * p₂ / L) :
    |A + B - C - D| ≤ Cgs k C₀ * N^k * p₂ / L := by
  have h1 : |A + B - C - D| ≤ |A| + |B| + |C| + |D| := by
    rw [show A + B - C - D = (A + B) - (C + D) by ring, abs_sub_le_iff]
    constructor <;> linarith [le_abs_self A, le_abs_self B, le_abs_self C, le_abs_self D,
      neg_le_abs A, neg_le_abs B, neg_le_abs C, neg_le_abs D]
  have hsum : 2 * ((k:ℝ)+1) * CTc k C₀ * C₀ / (2*Real.pi) * N^k * p₂ / L
      + Ceps1 k C₀ * N^k * p₂ / L + C₀ * Ceps2 k C₀ * N^k * p₂ / L
      + 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * N^k * p₂ / L = Cgs k C₀ * N^k * p₂ / L := by
    rw [Cgs, C2c]; ring
  linarith [h1, hA, hB, hC, hD, hsum]

/-- The `C2c` combination appearing in the bound for `|T₁ - T₂|`. -/
theorem asm_C2c_sum (k : ℕ) (C₀ p₁ p₂ L : ℝ) (hC₀ : 0 ≤ C₀) (hp1 : 0 < p₁) (hp2 : 0 < p₂)
    (hL : 0 < L) (hp1p2 : p₁ ≤ C₀ * p₂) (hCe2 : 0 ≤ Ceps2 k C₀)
    {e1 e2 etd : ℝ} (he1 : |e1| ≤ Ceps1 k C₀ / L) (he2 : |e2| ≤ Ceps2 k C₀ / L)
    (het : |etd| ≤ 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂ / L) :
    |p₂ * e1 - p₁ * e2 - etd| ≤ C2c k C₀ * p₂ / L := by
  have h1 : |p₂ * e1 - p₁ * e2 - etd| ≤ |p₂ * e1| + |p₁ * e2| + |etd| := by
    have hA : |p₂ * e1 - p₁ * e2 - etd| ≤ |p₂ * e1 - p₁ * e2| + |etd| := by
      rw [show p₂ * e1 - p₁ * e2 - etd = (p₂ * e1 - p₁ * e2) - etd by ring, abs_sub_le_iff]
      constructor <;> linarith [le_abs_self (p₂*e1 - p₁*e2), neg_le_abs (p₂*e1 - p₁*e2),
        le_abs_self etd, neg_le_abs etd]
    have hB : |p₂ * e1 - p₁ * e2| ≤ |p₂ * e1| + |p₁ * e2| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [le_abs_self (p₂*e1), neg_le_abs (p₂*e1),
        le_abs_self (p₁*e2), neg_le_abs (p₁*e2)]
    linarith
  refine le_trans h1 ?_
  have hp2e1 : |p₂ * e1| ≤ Ceps1 k C₀ * p₂ / L := by
    rw [abs_mul, abs_of_pos hp2, le_div_iff₀ hL]
    have h : |e1| * L ≤ Ceps1 k C₀ := (le_div_iff₀ hL).mp he1
    calc p₂ * |e1| * L = (|e1| * L) * p₂ := by ring
      _ ≤ Ceps1 k C₀ * p₂ := mul_le_mul_of_nonneg_right h (le_of_lt hp2)
  have hp1e2 : |p₁ * e2| ≤ C₀ * Ceps2 k C₀ * p₂ / L := by
    rw [abs_mul, abs_of_pos hp1, le_div_iff₀ hL]
    have h : |e2| * L ≤ Ceps2 k C₀ := (le_div_iff₀ hL).mp he2
    calc p₁ * |e2| * L = (|e2| * L) * p₁ := by ring
      _ ≤ Ceps2 k C₀ * p₁ := mul_le_mul_of_nonneg_right h (le_of_lt hp1)
      _ ≤ Ceps2 k C₀ * (C₀ * p₂) := mul_le_mul_of_nonneg_left hp1p2 hCe2
      _ = C₀ * Ceps2 k C₀ * p₂ := by ring
  have hsum : Ceps1 k C₀ * p₂ / L + C₀ * Ceps2 k C₀ * p₂ / L
      + 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂ / L = C2c k C₀ * p₂ / L := by
    rw [C2c]; ring
  linarith [hp2e1, hp1e2, het, hsum]


/-- **N6. Solving the approximate dilation invariance** (MRTTZ Prop. 3.8; the research core).
Let `P₁, P₂` have degree `≤ k`, let `I_i = [x_i, x_i + L]` with `x_i ≍ N L`, and let
`b_i < a_i` with `a_i - b_i ≍ a_i / N`. Suppose, modulo `1/Q` with `Q` huge compared with
`Z = a₁a₂p₁p₂NL`, that `P_i(a_i ·) ~ P_i(b_i ·)` on `I_i / a_i` (for `i = 1, 2`) and
`P₁(p₂ ·) ~ P₂(p₁ ·)` on `I₁ / p₂`. Then there are `T = O(N^{k+1})`, `q ≤ Z^{K₀}` and
`Q/q`-integral polynomials `γ_i` with `P_i = ε_i + (T/2π) log + γ_i`, where `|ε_i'| ≤ C₁/L` on
`I_i`, and `γ₁(p₂ ·) - γ₂(p₁ ·)` is integer valued on `ℤ`. -/
theorem solve_adi (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ K₀ K : ℕ,
      ∀ (P₁ P₂ : ℝ[X]) (x₁ x₂ L N : ℝ) (a₁ b₁ a₂ b₂ p₁ p₂ Qm : ℕ),
        P₁ ∈ degreeLE ℝ (k : WithBot ℕ) → P₂ ∈ degreeLE ℝ (k : WithBot ℕ) →
        2 ≤ L → 100 * C₀ ^ 4 ≤ N →
        N * L ≤ C₀ * x₁ → x₁ ≤ C₀ * (N * L) → N * L ≤ C₀ * x₂ → x₂ ≤ C₀ * (N * L) →
        1 ≤ p₁ → 1 ≤ p₂ → 1 ≤ b₁ → b₁ < a₁ → 1 ≤ b₂ → b₂ < a₂ →
        (a₁ : ℝ) ≤ C₀ * N * ((a₁ : ℝ) - b₁) → N * ((a₁ : ℝ) - b₁) ≤ C₀ * a₁ →
        (a₂ : ℝ) ≤ C₀ * N * ((a₂ : ℝ) - b₂) → N * ((a₂ : ℝ) - b₂) ≤ C₀ * a₂ →
        ((a₁ : ℝ) * a₂ * p₁ * p₂ * N * L) ^ K ≤ (Qm : ℝ) →
        PolyRel k C₀ (1 / (Qm : ℝ)) (x₁ / a₁) (L / a₁) (dil a₁ P₁) (x₁ / b₁) (L / b₁) (dil b₁ P₁) →
        PolyRel k C₀ (1 / (Qm : ℝ)) (x₂ / a₂) (L / a₂) (dil a₂ P₂) (x₂ / b₂) (L / b₂) (dil b₂ P₂) →
        PolyRel k C₀ (1 / (Qm : ℝ)) (x₁ / p₂) (L / p₂) (dil p₂ P₁) (x₂ / p₁) (L / p₁) (dil p₁ P₂) →
        ∃ T : ℝ, |T| ≤ C₁ * N ^ (k + 1) ∧ ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≤ ((a₁ : ℝ) * a₂ * p₁ * p₂ * N * L) ^ K₀ ∧
          ∃ γ₁ γ₂ : ℝ[X], γ₁ ∈ degreeLE ℝ (k : WithBot ℕ) ∧ γ₂ ∈ degreeLE ℝ (k : WithBot ℕ) ∧
            IntegralOn ((q : ℝ) / Qm) γ₁ ∧ IntegralOn ((q : ℝ) / Qm) γ₂ ∧
            (∀ t ∈ Set.Icc x₁ (x₁ + L),
              |deriv (fun s ↦ P₁.eval s - T / (2 * Real.pi) * Real.log s - γ₁.eval s) t|
                ≤ C₁ / L) ∧
            (∀ t ∈ Set.Icc x₂ (x₂ + L),
              |deriv (fun s ↦ P₂.eval s - T / (2 * Real.pi) * Real.log s - γ₂.eval s) t|
                ≤ C₁ / L) ∧
            IntegralOn 1 (dil p₂ γ₁ - dil p₁ γ₂) := by
  refine ⟨C1c k C₀, ?_, K0c k, Kc k, ?_⟩
  · have h1 := (consts_le_C1c k C₀ hC₀).1
    linarith
  intro P₁ P₂ x₁ x₂ L N a₁ b₁ a₂ b₂ p₁ p₂ Qm hP1deg hP2deg hL hN hx1a hx1b hx2a hx2b
    hp1 hp2 hb1 hba1 hb2 hba2 ha1a ha1b ha2a ha2b hQm hrel1 hrel2 hedge
  -- ### basic facts
  have hC0pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hC04 : (1 : ℝ) ≤ C₀ ^ 4 := one_le_pow₀ hC₀
  have hNpos : 0 < N := by linarith [hC04, hN]
  have hLpos : 0 < L := by linarith
  have ha1pos : (0 : ℝ) < (a₁ : ℝ) := by
    have : 0 < a₁ := by omega
    exact_mod_cast this
  have ha2pos : (0 : ℝ) < (a₂ : ℝ) := by
    have : 0 < a₂ := by omega
    exact_mod_cast this
  have hp1pos : (0 : ℝ) < (p₁ : ℝ) := by
    have : 0 < p₁ := by omega
    exact_mod_cast this
  have hp2pos : (0 : ℝ) < (p₂ : ℝ) := by
    have : 0 < p₂ := by omega
    exact_mod_cast this
  have hNLpos : 0 < N * L := mul_pos hNpos hLpos
  have hx1pos : 0 < x₁ :=
    pos_of_mul_pos_right (lt_of_lt_of_le hNLpos hx1a) (le_of_lt hC0pos)
  have hx2pos : 0 < x₂ :=
    pos_of_mul_pos_right (lt_of_lt_of_le hNLpos hx2a) (le_of_lt hC0pos)
  have hNle : N ≤ C₀ * a₁ := by
    have h1 : (1 : ℝ) ≤ (a₁ : ℝ) - (b₁ : ℝ) := by
      have h2 : b₁ + 1 ≤ a₁ := by omega
      have h3 : ((b₁ : ℝ) + 1) ≤ (a₁ : ℝ) := by exact_mod_cast h2
      linarith
    nlinarith [ha1b, h1]
  have hNle2 : N ≤ C₀ * a₂ := by
    have h1 : (1 : ℝ) ≤ (a₂ : ℝ) - (b₂ : ℝ) := by
      have h2 : b₂ + 1 ≤ a₂ := by omega
      have h3 : ((b₂ : ℝ) + 1) ≤ (a₂ : ℝ) := by exact_mod_cast h2
      linarith
    nlinarith [ha2b, h1]
  have ha1ge : N / C₀ ≤ (a₁ : ℝ) := by
    rw [div_le_iff₀ hC0pos]
    linarith
  have ha1ge2 : (2 : ℝ) ≤ (a₁ : ℝ) := by
    have : 2 ≤ a₁ := by omega
    exact_mod_cast this
  have ha2ge2 : (2 : ℝ) ≤ (a₂ : ℝ) := by
    have : 2 ≤ a₂ := by omega
    exact_mod_cast this
  -- ### the modulus `Z`
  set Z : ℝ := (a₁ : ℝ) * a₂ * p₁ * p₂ * N * L with hZdef
  have hZp : Z = (a₁ : ℝ) * a₂ * p₁ * p₂ * N * L := hZdef
  have hN100 : (100 : ℝ) ≤ N := by linarith [hC04, hN]
  have hp1_1 : (1 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hp1
  have hp2_1 : (1 : ℝ) ≤ (p₂ : ℝ) := by exact_mod_cast hp2
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hZ2 : (2 : ℝ) ≤ Z := by
    rw [hZp]
    exact two_le_prod6 ha1ge2 ha2ge2 hp1_1 hp2_1 hN100 hL2
  have hZge1 : (1 : ℝ) ≤ Z := by linarith
  have hprod1 : (1 : ℝ) ≤ a₂ * p₁ * p₂ * N * L :=
    one_le_prod5 (by linarith [ha2ge2]) hp1_1 hp2_1 hN100 hL2
  have hZle_a1 : (a₁ : ℝ) ≤ Z := by
    rw [hZp]
    calc (a₁ : ℝ) = (a₁ : ℝ) * 1 := by ring
      _ ≤ (a₁ : ℝ) * (a₂ * p₁ * p₂ * N * L) :=
          mul_le_mul_of_nonneg_left hprod1 (le_of_lt ha1pos)
      _ = (a₁ : ℝ) * a₂ * p₁ * p₂ * N * L := by ring
  have hprod2 : (1 : ℝ) ≤ (a₁ : ℝ) * p₁ * p₂ * N * L :=
    one_le_prod5 (by linarith [ha1ge2]) hp1_1 hp2_1 hN100 hL2
  have hZle_a2 : (a₂ : ℝ) ≤ Z := by
    rw [hZp]
    calc (a₂ : ℝ) = (a₂ : ℝ) * 1 := by ring
      _ ≤ (a₂ : ℝ) * ((a₁ : ℝ) * p₁ * p₂ * N * L) := by
          exact mul_le_mul_of_nonneg_left hprod2 (le_of_lt ha2pos)
      _ = (a₁ : ℝ) * a₂ * p₁ * p₂ * N * L := by ring
  have ha1ge3 : 100 * C₀ ^ 3 ≤ (a₁ : ℝ) := by
    have h2 : 100 * C₀ ^ 4 ≤ (a₁ : ℝ) * C₀ := by
      have h3 : 100 * C₀ ^ 4 ≤ C₀ * (a₁ : ℝ) := le_trans hN hNle
      linarith
    exact le_of_mul_le_mul_right (by nlinarith [h2]) hC0pos
  have hZbig : (C₀ + 2) ^ 3 ≤ Z := by
    have hprod3 : (400 : ℝ) ≤ a₂ * p₁ * p₂ * N * L :=
      le_prod5 ha2ge2 hp1_1 hp2_1 hN100 hL2
    have h4 : 40000 * C₀ ^ 3 ≤ (a₁ : ℝ) * (a₂ * p₁ * p₂ * N * L) := by
      calc 40000 * C₀ ^ 3 = (100 * C₀ ^ 3) * 400 := by ring
        _ ≤ (a₁ : ℝ) * (a₂ * p₁ * p₂ * N * L) :=
            mul_le_mul ha1ge3 hprod3 (by norm_num) (le_of_lt ha1pos)
    have h2 : (C₀ + 2) ^ 3 ≤ 40000 * C₀ ^ 3 := base_pow3_le hC₀
    rw [hZp]
    calc (C₀ + 2) ^ 3 ≤ 40000 * C₀ ^ 3 := h2
      _ ≤ (a₁ : ℝ) * (a₂ * p₁ * p₂ * N * L) := h4
      _ = (a₁ : ℝ) * a₂ * p₁ * p₂ * N * L := by ring
  have hQm1 : 1 ≤ Qm := by
    have h1 : (1 : ℝ) ≤ Z ^ (Kc k) := one_le_pow₀ hZge1
    have h2 : (1 : ℝ) ≤ (Qm : ℝ) := le_trans h1 hQm
    have h2' : ((1 : ℕ) : ℝ) ≤ ((Qm : ℕ) : ℝ) := by push_cast; exact h2
    exact Nat.cast_le.mp h2'
  -- ### the two one-sided descents
  obtain ⟨c01, T1, mu1, hP1, hT1, hmu1⟩ :=
    descent_of_polyrel k C₀ hC₀ (natDegree_le_of_mem_degreeLE hP1deg) hL hN hx1a hx1b hx1pos
      hQm1 hb1 hba1 ha1a ha1b hrel1
  obtain ⟨c02, T2, mu2, hP2, hT2, hmu2⟩ :=
    descent_of_polyrel k C₀ hC₀ (natDegree_le_of_mem_degreeLE hP2deg) hL hN hx2a hx2b hx2pos
      hQm1 hb2 hba2 ha2a ha2b hrel2
  set Tsum1 : ℝ := ∑ m ∈ Finset.Icc 1 k, T1 m with hTsum1
  set Tsum2 : ℝ := ∑ m ∈ Finset.Icc 1 k, T2 m with hTsum2
  set G1 : ℝ[X] := ∑ m ∈ Finset.Icc 1 k, C (mu1 m) * X ^ m with hG1
  set G2 : ℝ[X] := ∑ m ∈ Finset.Icc 1 k, C (mu2 m) * X ^ m with hG2
  set q : ℕ := Qfin k a₁ b₁ a₂ b₂ with hqdef
  have hQfinpos : 0 < Qfin k a₁ b₁ a₂ b₂ := by
    rw [Qfin]
    refine pow_pos (mul_pos (mul_pos (pow_pos (Nat.factorial_pos k) _) ?_) ?_) _
    · exact Finset.prod_pos fun m hm => qj_pos a₁ b₁ m hba1 (Finset.mem_Icc.mp hm).1
    · exact Finset.prod_pos fun m hm => qj_pos a₂ b₂ m hba2 (Finset.mem_Icc.mp hm).1
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hQfinpos)
  have hqZ : (q : ℝ) ≤ Z ^ (K0c k) := by
    rw [hqdef]
    exact qfin_bound k a₁ b₁ a₂ b₂ hZ2 hZle_a1 hZle_a2
  -- ===== the two derivative bounds for `eps`
  -- ### the sup bound `ctc` for `|T_m|` and the constant comparisons
  have h2cgs : 2 * Cgs k C₀ ≤ C1c k C₀ := (consts_le_C1c k C₀ hC₀).2.1
  have hT1c : ((k : ℝ) + 1) * CTc k C₀ ≤ C1c k C₀ := (consts_le_C1c k C₀ hC₀).2.2.1
  have hce1le : Ceps1 k C₀ ≤ C1c k C₀ := (consts_le_C1c k C₀ hC₀).2.2.2.1
  have hce2le : Ceps2 k C₀ ≤ C1c k C₀ := (consts_le_C1c k C₀ hC₀).2.2.2.2.1
  have hCeps2add : Ceps2 k C₀ + 2 * C₀ ^ 2 * C2c k C₀ ≤ C1c k C₀ :=
    Ceps2_add_le k C₀ hC₀
  have hC1c2 : (2 : ℝ) ≤ C1c k C₀ := C1c_ge_two k C₀ hC₀
  have hctc0 : 0 ≤ CTc k C₀ := CTc_nonneg k C₀ hC₀
  have hctc_le : CTc k C₀ ≤ C1c k C₀ := by
    have := hT1c
    nlinarith [hctc0]
  -- ### the |T| bound
  have hTsum1_le : |Tsum1| ≤ C1c k C₀ * N ^ (k + 1) := by
    rw [hTsum1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h1 : ∀ m ∈ Finset.Icc 1 k, |T1 m| ≤ CTc k C₀ * N ^ (k + 1) := by
      intro m hm
      refine le_trans (hT1 m hm) ?_
      have hmk : m + 1 ≤ k + 1 := Nat.succ_le_succ (Finset.mem_Icc.mp hm).2
      have hN1 : (1 : ℝ) ≤ N := by linarith [hC04, hN]
      have := pow_le_pow_right₀ hN1 hmk
      nlinarith [hctc0]
    calc ∑ m ∈ Finset.Icc 1 k, |T1 m| ≤ ∑ _m ∈ Finset.Icc 1 k, CTc k C₀ * N ^ (k + 1) :=
          Finset.sum_le_sum h1
      _ = (Finset.Icc 1 k).card * (CTc k C₀ * N ^ (k + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (k : ℝ) * (CTc k C₀ * N ^ (k + 1)) := by
          have hc : (Finset.Icc 1 k).card = k := by simp
          rw [hc]
      _ ≤ ((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1) := by
          have h2 : (0 : ℝ) ≤ CTc k C₀ * N ^ (k + 1) := by positivity
          nlinarith
      _ ≤ C1c k C₀ * N ^ (k + 1) := by
          have h3 : (0 : ℝ) ≤ N ^ (k + 1) := by positivity
          nlinarith [hT1c, h3]
  -- ### integrality of the two lattice parts
  have hG1deg : G1.natDegree ≤ k := by
    rw [hG1]
    refine natDegree_finset_sum_le _ _ fun m hm => ?_
    refine le_trans (natDegree_mul_le) ?_
    have h1 : (C (mu1 m) : ℝ[X]).natDegree = 0 := natDegree_C _
    have h2 : (X ^ m : ℝ[X]).natDegree = m := natDegree_X_pow m
    have h3 : m ≤ k := (Finset.mem_Icc.mp hm).2
    rw [h1, h2, zero_add]; exact h3
  have hG2deg : G2.natDegree ≤ k := by
    rw [hG2]
    refine natDegree_finset_sum_le _ _ fun m hm => ?_
    refine le_trans (natDegree_mul_le) ?_
    have h1 : (C (mu2 m) : ℝ[X]).natDegree = 0 := natDegree_C _
    have h2 : (X ^ m : ℝ[X]).natDegree = m := natDegree_X_pow m
    have h3 : m ≤ k := (Finset.mem_Icc.mp hm).2
    rw [h1, h2, zero_add]; exact h3
  have hG1in : IntegralOn ((q : ℝ) / Qm) G1 := by
    have h1 : Qfin k a₂ b₂ a₁ b₁ = Qfin k a₁ b₁ a₂ b₂ := by
      rw [Qfin, Qfin]; ring
    have h2 := gamma_integral k a₁ b₁ Qm hQm1 hmu1
      (fun m hm => qfin_dvd k a₁ b₁ a₂ b₂ m hm hQfinpos)
    simpa only [hqdef] using h2
  have hG2in : IntegralOn ((q : ℝ) / Qm) G2 := by
    have h1 : Qfin k a₂ b₂ a₁ b₁ = Qfin k a₁ b₁ a₂ b₂ := by
      rw [Qfin, Qfin]; ring
    have hQp : 0 < Qfin k a₂ b₂ a₁ b₁ := by rw [h1]; exact hQfinpos
    have h2 := gamma_integral k a₂ b₂ Qm hQm1 hmu2
      (fun m hm => qfin_dvd k a₂ b₂ a₁ b₁ m hm hQp)
    rw [hqdef, ← h1]
    exact h2
  -- ### the degree of `G1`,`G2` and the final `γ`'s
  have hq2 : 1 ≤ q := hq1
  -- ### `dil` preserves integrality
  -- ### the epsilon functions and their derivative bounds
  set eps1 : ℝ → ℝ := fun s => P₁.eval s - (Tsum1 / (2 * Real.pi)) * Real.log s - G1.eval s
    with heps1
  set eps2 : ℝ → ℝ := fun s => P₂.eval s - (Tsum2 / (2 * Real.pi)) * Real.log s - G2.eval s
    with heps2
  have heps1der : ∀ s : ℝ, s ≠ 0 → HasDerivAt eps1
      (P₁.derivative.eval s - (Tsum1 / (2 * Real.pi)) * s⁻¹ - G1.derivative.eval s) s := by
    intro s hs
    rw [heps1]
    exact ((P₁.hasDerivAt s).sub ((Real.hasDerivAt_log hs).const_mul _)).sub (G1.hasDerivAt s)
  have heps2der : ∀ s : ℝ, s ≠ 0 → HasDerivAt eps2
      (P₂.derivative.eval s - (Tsum2 / (2 * Real.pi)) * s⁻¹ - G2.derivative.eval s) s := by
    intro s hs
    rw [heps2]
    exact ((P₂.hasDerivAt s).sub ((Real.hasDerivAt_log hs).const_mul _)).sub (G2.hasDerivAt s)
  have hN6 : 6 * C₀ ^ 3 ≤ N := by nlinarith [hN, hC₀]
  have hsum1 : ∀ t : ℝ, 0 < t → x₁ ≤ t → t ≤ x₁ + L →
      |∑ m ∈ Finset.Icc 1 k, T1 m / (2 * Real.pi) *
        ((Tay m x₁).derivative.eval t - 1 / t)| ≤ Ceps1 k C₀ / L :=
    fun t htpos ht1 ht2 => eps_sum_bound_1 k C₀ x₁ L N hC₀ hLpos hNpos hx1a hx1pos hT1 htpos ht1 ht2
  have hsum2 : ∀ t : ℝ, 0 < t → x₂ - 3 * C₀ ^ 2 * L ≤ t → t ≤ x₂ + 3 * C₀ ^ 2 * L →
      |∑ m ∈ Finset.Icc 1 k, T2 m / (2 * Real.pi) *
        ((Tay m x₂).derivative.eval t - 1 / t)| ≤ Ceps2 k C₀ / L :=
    fun t htpos ht1 ht2 => eps_sum_bound_2 k C₀ x₂ L N hC₀ hLpos hNpos hx2a hx2pos hN6 hT2 htpos ht1 ht2
  have hder1 : ∀ t ∈ Set.Icc x₁ (x₁ + L), |deriv eps1 t| ≤ Ceps1 k C₀ / L := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htpos : 0 < t := lt_of_lt_of_le hx1pos ht.1
    have h1 : deriv eps1 t =
        P₁.derivative.eval t - (Tsum1 / (2 * Real.pi)) * t⁻¹ - G1.derivative.eval t :=
      (heps1der t (ne_of_gt htpos)).deriv
    have h2 : P₁.derivative.eval t - (Tsum1 / (2 * Real.pi)) * t⁻¹ - G1.derivative.eval t =
        ∑ m ∈ Finset.Icc 1 k, T1 m / (2 * Real.pi) *
          ((Tay m x₁).derivative.eval t - 1 / t) := by
      rw [← h1, heps1]
      exact eps_deriv_eq k hP1 hG1 t (ne_of_gt htpos)
    rw [h1, h2]
    exact hsum1 t htpos ht.1 ht.2
  have hder2 : ∀ t ∈ Set.Icc (x₂ - 3 * C₀ ^ 2 * L) (x₂ + 3 * C₀ ^ 2 * L),
      |deriv eps2 t| ≤ Ceps2 k C₀ / L := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htpos : 0 < t := by
      have h1 : N * L / (2 * C₀) ≤ x₂ - 3 * C₀ ^ 2 * L := by
        have hsplit : 3 * C₀ ^ 2 * L ≤ N * L / (2 * C₀) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [hN6, hC0pos]
        have h4 : N * L / C₀ ≤ x₂ := by rw [div_le_iff₀ hC0pos]; linarith [hx2a]
        have h5 : 2 * (N * L / (2 * C₀)) = N * L / C₀ := by field_simp
        linarith [hsplit, h4, h5]
      have h2 : 0 < N * L / (2 * C₀) := by positivity
      linarith
    have h1 : deriv eps2 t =
        P₂.derivative.eval t - (Tsum2 / (2 * Real.pi)) * t⁻¹ - G2.derivative.eval t :=
      (heps2der t (ne_of_gt htpos)).deriv
    have h2 : P₂.derivative.eval t - (Tsum2 / (2 * Real.pi)) * t⁻¹ - G2.derivative.eval t =
        ∑ m ∈ Finset.Icc 1 k, T2 m / (2 * Real.pi) *
          ((Tay m x₂).derivative.eval t - 1 / t) := by
      rw [← h1, heps2]
      exact eps_deriv_eq k hP2 hG2 t (ne_of_gt htpos)
    rw [h1, h2]
    exact hsum2 t htpos ht.1 ht.2
  -- ### the edge relation data
  rw [PolyRel] at hedge
  obtain ⟨hedgeL1, hedgeL2, hedgeX, et, gt, hdeget, hdeggt, hedgeRel, hedgeBd, hedgeHint⟩ := hedge
  have hdeget' : et.natDegree ≤ k := natDegree_le_of_mem_degreeLE hdeget
  have hdeggt' : gt.natDegree ≤ k := natDegree_le_of_mem_degreeLE hdeggt
  have hp1p2 : (p₁ : ℝ) ≤ C₀ * p₂ := by
    have h3 : L ≤ C₀ * (L / p₁) * p₂ := (div_le_iff₀ hp2pos).mp hedgeL1
    have h4 : L * p₁ ≤ C₀ * (L / p₁) * p₂ * p₁ :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hp1pos)
    have h5 : C₀ * (L / p₁) * p₂ * p₁ = C₀ * L * p₂ := by field_simp
    rw [h5] at h4
    have h7 : C₀ * L * p₂ = L * (C₀ * p₂) := by ring
    rw [h7] at h4
    exact le_of_mul_le_mul_left h4 hLpos
  have hp2p1 : (p₂ : ℝ) ≤ C₀ * p₁ := by
    have h3 : L ≤ C₀ * (L / p₂) * p₁ := (div_le_iff₀ hp1pos).mp hedgeL2
    have h4 : L * p₂ ≤ C₀ * (L / p₂) * p₁ * p₂ :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hp2pos)
    have h5 : C₀ * (L / p₂) * p₁ * p₂ = C₀ * L * p₁ := by field_simp
    rw [h5] at h4
    have h7 : C₀ * L * p₁ = L * (C₀ * p₁) := by ring
    rw [h7] at h4
    exact le_of_mul_le_mul_left h4 hLpos
  -- ### the polynomial `G` and its integrality
  set G : ℝ[X] := gt + dil (p₁ : ℝ) G2 - dil (p₂ : ℝ) G1 with hGdef
  have hGdeg : G.natDegree ≤ k := by
    rw [hGdef]
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_add_le _ _) (max_le hdeggt' ?_)
      exact le_trans (natDegree_dil_le _ _) hG2deg
    · exact le_trans (natDegree_dil_le _ _) hG1deg
  have hGint : IntegralOn ((q : ℝ) / Qm) G := by
    rw [hGdef]
    refine IntegralOn.sub (IntegralOn.add ?_ ?_) ?_
    · refine IntegralOn.mono (δ := 1 / (Qm : ℝ)) (m := (q : ℤ)) ?_ hedgeHint
      rw [one_div, inv_mul_eq_div, Int.cast_natCast]
    · exact IntegralOn.dil p₁ ((q : ℝ) / Qm) hG2in
    · exact IntegralOn.dil p₂ ((q : ℝ) / Qm) hG1in
  -- ### the identity on `J`
  have hGid : ∀ t : ℝ, 0 < t → G.eval t = eps1 ((p₂ : ℝ) * t) - eps2 ((p₁ : ℝ) * t) +
      (Tsum1 / (2 * Real.pi)) * Real.log ((p₂ : ℝ) * t) -
      (Tsum2 / (2 * Real.pi)) * Real.log ((p₁ : ℝ) * t) - et.eval t := by
    intro t ht
    have h1 : (dil (p₂ : ℝ) P₁).eval t = et.eval t + (dil (p₁ : ℝ) P₂).eval t + gt.eval t := by
      rw [hedgeRel]; simp only [eval_add]
    rw [eval_dil, eval_dil] at h1
    rw [hGdef]
    simp only [eval_add, eval_sub, eval_dil]
    rw [heps1, heps2]
    simp only []
    rw [h1]
    ring
  -- ### the derivative identity for `G` on the interior of `J`
  have hJpos : 0 < x₁ / (p₂ : ℝ) := by positivity
  have hTsum1b : |Tsum1| ≤ ((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1) := by
    rw [hTsum1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h1 : ∀ m ∈ Finset.Icc 1 k, |T1 m| ≤ CTc k C₀ * N ^ (k + 1) := by
      intro m hm
      refine le_trans (hT1 m hm) ?_
      have hmk : m + 1 ≤ k + 1 := Nat.succ_le_succ (Finset.mem_Icc.mp hm).2
      have hN1 : (1 : ℝ) ≤ N := by linarith [hC04, hN]
      have h2 := pow_le_pow_right₀ hN1 hmk
      nlinarith [hctc0]
    calc ∑ m ∈ Finset.Icc 1 k, |T1 m| ≤ ∑ _m ∈ Finset.Icc 1 k, CTc k C₀ * N ^ (k + 1) :=
          Finset.sum_le_sum h1
      _ = (Finset.Icc 1 k).card * (CTc k C₀ * N ^ (k + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (k : ℝ) * (CTc k C₀ * N ^ (k + 1)) := by
          have hc : (Finset.Icc 1 k).card = k := by simp
          rw [hc]
      _ ≤ ((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1) := by
          have h2 : (0 : ℝ) ≤ CTc k C₀ * N ^ (k + 1) := by positivity
          nlinarith
  have hDelta : |Tsum1 - Tsum2| ≤ 2 * (((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1)) := by
    have h2 := hTsum1b
    have h3 : |Tsum2| ≤ ((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1) := by
      rw [hTsum2]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have h1 : ∀ m ∈ Finset.Icc 1 k, |T2 m| ≤ CTc k C₀ * N ^ (k + 1) := by
        intro m hm
        refine le_trans (hT2 m hm) ?_
        have hmk : m + 1 ≤ k + 1 := Nat.succ_le_succ (Finset.mem_Icc.mp hm).2
        have hN1 : (1 : ℝ) ≤ N := by linarith [hC04, hN]
        have h4 := pow_le_pow_right₀ hN1 hmk
        nlinarith [hctc0]
      calc ∑ m ∈ Finset.Icc 1 k, |T2 m| ≤ ∑ _m ∈ Finset.Icc 1 k, CTc k C₀ * N ^ (k + 1) :=
            Finset.sum_le_sum h1
        _ = (Finset.Icc 1 k).card * (CTc k C₀ * N ^ (k + 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (k : ℝ) * (CTc k C₀ * N ^ (k + 1)) := by
            have hc : (Finset.Icc 1 k).card = k := by simp
            rw [hc]
        _ ≤ ((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1) := by
            have h5 : (0 : ℝ) ≤ CTc k C₀ * N ^ (k + 1) := by positivity
            nlinarith
    have habs : |Tsum1 - Tsum2| ≤ |Tsum1| + |Tsum2| := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [le_abs_self Tsum1, neg_le_abs Tsum2],
        by linarith [le_abs_self Tsum2, neg_le_abs Tsum1]⟩
    calc |Tsum1 - Tsum2| ≤ |Tsum1| + |Tsum2| := habs
      _ ≤ 2 * (((k : ℝ) + 1) * CTc k C₀ * N ^ (k + 1)) := by linarith
  have hderivG : ∀ t ∈ Set.Ioo (x₁ / (p₂ : ℝ)) ((x₁ + L) / (p₂ : ℝ)),
      G.derivative.eval t = (Tsum1 - Tsum2) / (2 * Real.pi) / t +
        (p₂ : ℝ) * deriv eps1 ((p₂ : ℝ) * t) - (p₁ : ℝ) * deriv eps2 ((p₁ : ℝ) * t) -
        et.derivative.eval t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hJpos (le_of_lt ht.1)
    have hp2ne : (p₂ : ℝ) ≠ 0 := ne_of_gt hp2pos
    have hp1ne : (p₁ : ℝ) ≠ 0 := ne_of_gt hp1pos
    have htne : t ≠ 0 := ne_of_gt htpos
    have hq : (p₂ : ℝ) * t ≠ 0 := mul_ne_zero hp2ne htne
    have hq' : (p₁ : ℝ) * t ≠ 0 := mul_ne_zero hp1ne htne
    have hloc : (fun s => eps1 ((p₂ : ℝ) * s) - eps2 ((p₁ : ℝ) * s) +
        (Tsum1 / (2 * Real.pi)) * Real.log ((p₂ : ℝ) * s) -
        (Tsum2 / (2 * Real.pi)) * Real.log ((p₁ : ℝ) * s) - et.eval s) =ᶠ[nhds t]
        (fun s => G.eval s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (hGid s (lt_of_lt_of_le hJpos (le_of_lt hs.1))).symm
    have h1 : deriv (fun s => eps1 ((p₂ : ℝ) * s) - eps2 ((p₁ : ℝ) * s) +
        (Tsum1 / (2 * Real.pi)) * Real.log ((p₂ : ℝ) * s) -
        (Tsum2 / (2 * Real.pi)) * Real.log ((p₁ : ℝ) * s) - et.eval s) t =
        G.derivative.eval t := by
      rw [hloc.deriv_eq, (G.hasDerivAt t).deriv]
    have hd1 : HasDerivAt (fun s : ℝ => eps1 ((p₂ : ℝ) * s))
        (deriv eps1 ((p₂ : ℝ) * t) * (p₂ : ℝ)) t := by
      have hx : HasDerivAt (fun s : ℝ => (p₂ : ℝ) * s) (p₂ : ℝ) t :=
        hasDerivAt_const_mul (p₂ : ℝ)
      have hdiff : DifferentiableAt ℝ eps1 ((p₂ : ℝ) * t) :=
        (heps1der _ hq).differentiableAt
      exact (DifferentiableAt.hasDerivAt hdiff).comp t hx
    have hd2 : HasDerivAt (fun s : ℝ => eps2 ((p₁ : ℝ) * s))
        (deriv eps2 ((p₁ : ℝ) * t) * (p₁ : ℝ)) t := by
      have hx : HasDerivAt (fun s : ℝ => (p₁ : ℝ) * s) (p₁ : ℝ) t :=
        hasDerivAt_const_mul (p₁ : ℝ)
      have hdiff : DifferentiableAt ℝ eps2 ((p₁ : ℝ) * t) :=
        (heps2der _ hq').differentiableAt
      exact (DifferentiableAt.hasDerivAt hdiff).comp t hx
    have hdlog1 : HasDerivAt (fun s : ℝ => (Tsum1 / (2 * Real.pi)) * Real.log ((p₂ : ℝ) * s))
        ((Tsum1 / (2 * Real.pi)) * (1 / t)) t := by
      have hx : HasDerivAt (fun s : ℝ => (p₂ : ℝ) * s) (p₂ : ℝ) t :=
        hasDerivAt_const_mul (p₂ : ℝ)
      have hl : HasDerivAt (fun s : ℝ => Real.log ((p₂ : ℝ) * s)) ((1 / t)) t := by
        have h := (Real.hasDerivAt_log hq).comp t hx
        rw [show ((p₂ : ℝ) * t)⁻¹ * (p₂ : ℝ) = 1 / t by field_simp] at h
        exact h
      exact hl.const_mul _
    have hdlog2 : HasDerivAt (fun s : ℝ => (Tsum2 / (2 * Real.pi)) * Real.log ((p₁ : ℝ) * s))
        ((Tsum2 / (2 * Real.pi)) * (1 / t)) t := by
      have hx : HasDerivAt (fun s : ℝ => (p₁ : ℝ) * s) (p₁ : ℝ) t :=
        hasDerivAt_const_mul (p₁ : ℝ)
      have hl : HasDerivAt (fun s : ℝ => Real.log ((p₁ : ℝ) * s)) ((1 / t)) t := by
        have h := (Real.hasDerivAt_log hq').comp t hx
        rw [show ((p₁ : ℝ) * t)⁻¹ * (p₁ : ℝ) = 1 / t by field_simp] at h
        exact h
      exact hl.const_mul _
    have hdet : HasDerivAt (fun s : ℝ => et.eval s) (et.derivative.eval t) t := et.hasDerivAt t
    have hF : HasDerivAt (fun s => eps1 ((p₂ : ℝ) * s) - eps2 ((p₁ : ℝ) * s) +
        (Tsum1 / (2 * Real.pi)) * Real.log ((p₂ : ℝ) * s) -
        (Tsum2 / (2 * Real.pi)) * Real.log ((p₁ : ℝ) * s) - et.eval s)
        ((deriv eps1 ((p₂ : ℝ) * t) * (p₂ : ℝ) - deriv eps2 ((p₁ : ℝ) * t) * (p₁ : ℝ)) +
        (Tsum1 / (2 * Real.pi)) * (1 / t) - (Tsum2 / (2 * Real.pi)) * (1 / t) -
        et.derivative.eval t) t :=
      (((hd1.sub hd2).add hdlog1).sub hdlog2).sub hdet
    rw [← h1, hF.deriv]
    ring
  -- ### the constant `Cg` and the window
  set Cg : ℝ := max (Cgs k C₀) 1 with hCg
  have hCg1 : (1 : ℝ) ≤ Cg := le_max_right _ _
  have hCgs_le : Cgs k C₀ ≤ Cg := le_max_left _ _
  have hCgpos : 0 < Cg := lt_of_lt_of_le one_pos hCg1
  have h2Cg : 2 * Cg ≤ C1c k C₀ := by
    rcases le_total (Cgs k C₀) 1 with h | h
    · rw [show Cg = 1 from max_eq_right h]; linarith [hC1c2]
    · rw [show Cg = Cgs k C₀ from max_eq_left h]; linarith [h2cgs]
  set W : ℝ := L / (2 * Cg * N ^ k * p₂) with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  have hWle : W ≤ L / (2 * p₂) := by
    rw [hW, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1' : (1 : ℝ) ≤ N ^ k := one_le_pow₀ (by linarith [hC04, hN])
    have h1 : (1 : ℝ) ≤ Cg * N ^ k := by nlinarith [hCg1, h1']
    calc L * (2 * p₂) ≤ L * (2 * p₂) * (Cg * N ^ k) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = L * (2 * Cg * N ^ k * p₂) := by ring
  have hp2Z : (p₂ : ℝ) ≤ Z := by
    rw [hZp]
    have h1 : (1 : ℝ) ≤ (a₁ : ℝ) * a₂ * p₁ * N * L := by
      exact one_le_prod5 (by linarith [ha1ge2]) (by linarith [ha2ge2]) hp1_1 hN100 hL2
    calc (p₂ : ℝ) = (p₂ : ℝ) * 1 := by ring
      _ ≤ (p₂ : ℝ) * ((a₁ : ℝ) * a₂ * p₁ * N * L) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hp2pos)
      _ = (a₁ : ℝ) * a₂ * p₁ * p₂ * N * L := by ring
  have hmain : ((k : ℝ) + 1) * (q : ℝ) * (2 * Cg) * N ^ k * p₂ ≤ L * (Qm : ℝ) := by
    have hNleZ : N ≤ C₀ * Z :=
      le_trans hNle (mul_le_mul_of_nonneg_left hZle_a1 (le_of_lt hC0pos))
    have hNk : N ^ k ≤ (C₀ * Z) ^ k := pow_le_pow_left₀ (le_of_lt hNpos) hNleZ k
    have hKabs : ((k : ℝ) + 1) * C1c k C₀ * C₀ ^ k ≤ Z ^ (Kc k - K0c k - k - 1) :=
      K_absorb k C₀ hC₀ hZbig
    have h1 : ((k : ℝ) + 1) * (q : ℝ) * (2 * Cg) * N ^ k * p₂ ≤
        ((k : ℝ) + 1) * Z ^ (K0c k) * (C1c k C₀) * (C₀ * Z) ^ k * Z := by
      have hstep1 : (q : ℝ) * (2 * Cg) ≤ Z ^ (K0c k) * (C1c k C₀) :=
        mul_le_mul hqZ h2Cg (by positivity) (by positivity)
      have hstep2 : N ^ k * ((q : ℝ) * (2 * Cg)) ≤
          (C₀ * Z) ^ k * (Z ^ (K0c k) * C1c k C₀) :=
        mul_le_mul hNk hstep1 (by positivity) (by positivity)
      have hstep3 : N ^ k * ((q : ℝ) * (2 * Cg)) * p₂ ≤
          (C₀ * Z) ^ k * (Z ^ (K0c k) * C1c k C₀) * Z :=
        mul_le_mul hstep2 hp2Z (le_of_lt hp2pos) (by positivity)
      calc ((k : ℝ) + 1) * (q : ℝ) * (2 * Cg) * N ^ k * p₂
          = ((k : ℝ) + 1) * (N ^ k * ((q : ℝ) * (2 * Cg)) * p₂) := by ring
        _ ≤ ((k : ℝ) + 1) * ((C₀ * Z) ^ k * (Z ^ (K0c k) * C1c k C₀) * Z) :=
            mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = ((k : ℝ) + 1) * Z ^ (K0c k) * (C1c k C₀) * (C₀ * Z) ^ k * Z := by ring
    have h2 : ((k : ℝ) + 1) * Z ^ (K0c k) * (C1c k C₀) * (C₀ * Z) ^ k * Z ≤ 2 * Z ^ (Kc k) :=
      main_ineq_gen k C₀ Z (C1c k C₀) hZge1 hKabs
    have h4 : 2 * Z ^ (Kc k) ≤ L * (Qm : ℝ) := by
      have hQ : Z ^ (Kc k) ≤ (Qm : ℝ) := hQm
      nlinarith [hL2, hQ, hZge1]
    linarith [h1, h2, h4]
  -- ### remaining: lattice points in a short window, constancy of `G`, the bound on
  -- `|Tsum1 - Tsum2|` and the final assembly (see the handoff notes).
  -- ### the lattice window inside `J`, the bound on `G'` there and the constancy of `G`
  have hQmpos : (0 : ℝ) < (Qm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQm1)
  have hN1 : (1 : ℝ) ≤ N := by linarith [hN100]
  have hC0nn : (0 : ℝ) ≤ C₀ := le_of_lt hC0pos
  have hCeps1nn : (0 : ℝ) ≤ Ceps1 k C₀ := Ceps1_nonneg k C₀ hC₀
  have hCeps2nn : (0 : ℝ) ≤ Ceps2 k C₀ := Ceps2_nonneg k C₀ hC₀
  have hC2cnn : (0 : ℝ) ≤ C2c k C₀ := C2c_nonneg k C₀ hC₀
  have hδpos : (0 : ℝ) < (q : ℝ) / Qm := by
    have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    exact div_pos h1 hQmpos
  set u : ℝ := x₁ / (p₂ : ℝ) + L / (4 * (p₂ : ℝ)) with hu
  have hu_gt : x₁ / (p₂ : ℝ) < u := by
    rw [hu]
    have h : (0 : ℝ) < L / (4 * (p₂ : ℝ)) := by positivity
    linarith
  have huW_lt : u + W < (x₁ + L) / (p₂ : ℝ) := by
    have h4 : u + W ≤ u + L / (2 * (p₂ : ℝ)) := add_le_add (le_refl u) hWle
    have h5 : u + L / (2 * (p₂ : ℝ)) = (x₁ + 3 * L / 4) / (p₂ : ℝ) := by
      rw [hu]; field_simp; try ring
    have h6 : (x₁ + 3 * L / 4) / (p₂ : ℝ) < (x₁ + L) / (p₂ : ℝ) := by
      rw [div_lt_div_iff₀ hp2pos hp2pos]; nlinarith [hLpos, hp2pos]
    linarith
  have huW : u ≤ u + W := by linarith [hWpos]
  have hwin : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      t ∈ Set.Ioo (x₁ / (p₂ : ℝ)) ((x₁ + L) / (p₂ : ℝ)) :=
    fun t h1 h2 => ⟨lt_of_lt_of_le hu_gt h1, lt_of_le_of_lt h2 huW_lt⟩
  have hBmem : ∀ t : ℝ, u ≤ t → t ≤ u + W → (p₂ : ℝ) * t ∈ Set.Icc x₁ (x₁ + L) := by
    intro t ht1 ht2
    have hp2u : (p₂ : ℝ) * u = x₁ + L / 4 := by rw [hu]; field_simp; try ring
    have h3 : (p₂ : ℝ) * t ≤ (p₂ : ℝ) * (u + W) :=
      mul_le_mul_of_nonneg_left ht2 (le_of_lt hp2pos)
    have h4a : (p₂ : ℝ) * (u + W) < (p₂ : ℝ) * ((x₁ + L) / (p₂ : ℝ)) :=
      mul_lt_mul_of_pos_left huW_lt hp2pos
    have h4b : (p₂ : ℝ) * ((x₁ + L) / (p₂ : ℝ)) = x₁ + L := by field_simp
    refine ⟨?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left ht1 (le_of_lt hp2pos)
      linarith [h, hp2u]
    · linarith [h3, h4a, h4b]
  have hCmem : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      (p₁ : ℝ) * t ∈ Set.Icc (x₂ - 3 * C₀ ^ 2 * L) (x₂ + 3 * C₀ ^ 2 * L) := by
    have hxlow : x₂ / (p₁ : ℝ) - C₀ * (L / (p₂ : ℝ)) ≤ x₁ / (p₂ : ℝ) := by
      have h := (abs_le.mp hedgeX).1; linarith
    have hxup : x₁ / (p₂ : ℝ) ≤ x₂ / (p₁ : ℝ) + C₀ * (L / (p₂ : ℝ)) := by
      have h := (abs_le.mp hedgeX).2; linarith
    have hCCl : C₀ * L * p₁ / (p₂ : ℝ) ≤ C₀ ^ 2 * L := by
      rw [div_le_iff₀ hp2pos]
      calc C₀ * L * p₁ = (C₀ * L) * p₁ := by ring
        _ ≤ (C₀ * L) * (C₀ * p₂) := mul_le_mul_of_nonneg_left hp1p2 (by positivity)
        _ = C₀ ^ 2 * L * p₂ := by ring
    have hp1L : (p₁ : ℝ) * L / (p₂ : ℝ) ≤ C₀ ^ 2 * L := by
      rw [div_le_iff₀ hp2pos]
      have h1 : C₀ ≤ C₀ ^ 2 := by nlinarith [hC₀]
      calc (p₁ : ℝ) * L = L * p₁ := by ring
        _ ≤ L * (C₀ * p₂) := mul_le_mul_of_nonneg_left hp1p2 (le_of_lt hLpos)
        _ ≤ L * (C₀ ^ 2 * p₂) := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hLpos)
              exact mul_le_mul_of_nonneg_right h1 (le_of_lt hp2pos)
        _ = C₀ ^ 2 * L * p₂ := by ring
    intro t ht1 ht2
    have h3 : (p₁ : ℝ) * t ≤ (p₁ : ℝ) * (u + W) :=
      mul_le_mul_of_nonneg_left ht2 (le_of_lt hp1pos)
    refine ⟨?_, ?_⟩
    · have h1 : (p₁ : ℝ) * (x₁ / (p₂ : ℝ)) ≤ (p₁ : ℝ) * t :=
        mul_le_mul_of_nonneg_left (le_trans (le_of_lt hu_gt) ht1) (le_of_lt hp1pos)
      have h2a : (p₁ : ℝ) * (x₂ / (p₁ : ℝ) - C₀ * (L / (p₂ : ℝ))) ≤
          (p₁ : ℝ) * (x₁ / (p₂ : ℝ)) := mul_le_mul_of_nonneg_left hxlow (le_of_lt hp1pos)
      have h2b : (p₁ : ℝ) * (x₂ / (p₁ : ℝ) - C₀ * (L / (p₂ : ℝ))) =
          x₂ - C₀ * L * p₁ / (p₂ : ℝ) := by field_simp; try ring
      nlinarith [h1, h2a, h2b, hCCl, hC0pos, hLpos]
    · have h5 : (p₁ : ℝ) * (u + W) ≤ (p₁ : ℝ) * ((x₁ + L) / (p₂ : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt huW_lt) (le_of_lt hp1pos)
      have h6 : (p₁ : ℝ) * ((x₁ + L) / (p₂ : ℝ)) =
          (p₁ : ℝ) * (x₁ / (p₂ : ℝ)) + (p₁ : ℝ) * L / (p₂ : ℝ) := by field_simp; try ring
      have h7 : (p₁ : ℝ) * (x₁ / (p₂ : ℝ)) ≤ x₂ + C₀ ^ 2 * L := by
        have h1 : (p₁ : ℝ) * (x₁ / (p₂ : ℝ)) ≤
            (p₁ : ℝ) * (x₂ / (p₁ : ℝ) + C₀ * (L / (p₂ : ℝ))) :=
          mul_le_mul_of_nonneg_left hxup (le_of_lt hp1pos)
        have h2 : (p₁ : ℝ) * (x₂ / (p₁ : ℝ) + C₀ * (L / (p₂ : ℝ))) =
            x₂ + C₀ * L * p₁ / (p₂ : ℝ) := by field_simp; try ring
        linarith [h1, h2, hCCl]
      have hpos : (0 : ℝ) < C₀ ^ 2 * L := by positivity
      linarith [h3, h5, h6, h7, hp1L, hpos]
  have hedgeBd' : ∀ s ∈ Set.Icc (x₁ / (p₂ : ℝ)) ((x₁ + L) / (p₂ : ℝ)), |et.eval s| ≤ C₀ := by
    have hsum : (x₁ + L) / (p₂ : ℝ) = x₁ / (p₂ : ℝ) + L / (p₂ : ℝ) := by ring
    intro s hs
    refine hedgeBd s ?_
    rw [← hsum]; exact hs
  have hwin_sub : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      Set.Icc (t - (L / (2 * (p₂ : ℝ))) / 2) (t + (L / (2 * (p₂ : ℝ))) / 2) ⊆
        Set.Icc (x₁ / (p₂ : ℝ)) ((x₁ + L) / (p₂ : ℝ)) := by
    intro t ht1 ht2 s hs
    rw [Set.mem_Icc] at hs ⊢
    have h4 : (L / (2 * (p₂ : ℝ))) / 2 = L / (4 * (p₂ : ℝ)) := by field_simp; try ring
    rw [h4] at hs
    constructor
    · have hu1 : x₁ / (p₂ : ℝ) ≤ t - L / (4 * (p₂ : ℝ)) := by
        rw [hu] at ht1; linarith
      linarith [hu1, hs.1]
    · have h5 : t ≤ x₁ / (p₂ : ℝ) + 3 * L / (4 * (p₂ : ℝ)) := by
        have h6 : u + W ≤ u + L / (2 * (p₂ : ℝ)) := add_le_add (le_refl u) hWle
        have h7 : u + L / (2 * (p₂ : ℝ)) = x₁ / (p₂ : ℝ) + 3 * L / (4 * (p₂ : ℝ)) := by
          rw [hu]; field_simp; try ring
        linarith [ht2, h6, h7]
      have h8 : x₁ / (p₂ : ℝ) + 3 * L / (4 * (p₂ : ℝ)) + L / (4 * (p₂ : ℝ)) =
          (x₁ + L) / (p₂ : ℝ) := by field_simp; try ring
      linarith [hs.2, h5, h8]
  have hAbd : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      |(Tsum1 - Tsum2) / (2 * Real.pi) / t| ≤
        2 * ((k:ℝ)+1) * CTc k C₀ * C₀ / (2 * Real.pi) * N ^ k * p₂ / L := by
    intro t ht1 ht2
    refine asm_termA k C₀ t N L p₂ hC₀ hctc0 hN1 hLpos hp2pos ?_ hDelta
    have h1 : N * L / C₀ ≤ x₁ := by rw [div_le_iff₀ hC0pos]; linarith [hx1a]
    have h2 : N * L / (C₀ * p₂) = (N * L / C₀) / p₂ := by field_simp; try ring
    rw [h2]
    have h3 : (N * L / C₀) / p₂ ≤ x₁ / p₂ := div_le_div_of_nonneg_right h1 (le_of_lt hp2pos)
    linarith [h3, le_of_lt hu_gt, ht1]
  have hBbd : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      |(p₂ : ℝ) * deriv eps1 ((p₂ : ℝ) * t)| ≤ Ceps1 k C₀ * N ^ k * p₂ / L :=
    fun t ht1 ht2 => asm_termB k C₀ N L p₂ hN1 hLpos hp2pos hCeps1nn (hder1 _ (hBmem t ht1 ht2))
  have hCbd : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      |(p₁ : ℝ) * deriv eps2 ((p₁ : ℝ) * t)| ≤ C₀ * Ceps2 k C₀ * N ^ k * p₂ / L :=
    fun t ht1 ht2 => asm_termC k C₀ p₁ p₂ N L hC0nn hp1pos hp2pos hLpos hN1 hp1p2 hCeps2nn
      (hder2 _ (hCmem t ht1 ht2))
  have hetbd : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      |et.derivative.eval t| ≤ 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂ / L := by
    intro t ht1 ht2
    have hpd := poly_deriv_bound hdeget' hC0nn (show (0:ℝ) < L / (2 * (p₂:ℝ)) by positivity)
      (c := t) (lam := L / (2 * (p₂:ℝ))) (fun s hs => hedgeBd' s (hwin_sub t ht1 ht2 hs))
    have heq : ((k:ℝ)+1)^(2*k+4) * C₀ / (L / (2 * (p₂:ℝ))) =
        2 * ((k:ℝ)+1)^(2*k+4) * C₀ * p₂ / L := by field_simp; try ring
    rw [heq] at hpd
    exact hpd
  have hDbd : ∀ t : ℝ, u ≤ t → t ≤ u + W →
      |et.derivative.eval t| ≤ 2 * ((k:ℝ)+1)^(2*k+4) * C₀ * N ^ k * p₂ / L :=
    fun t ht1 ht2 => asm_termD k C₀ N L p₂ hC0nn hLpos hp2pos hN1 (hetbd t ht1 ht2)
  have hGbd : ∀ t : ℝ, u ≤ t → t ≤ u + W → |G.derivative.eval t| ≤ Cg * N ^ k * p₂ / L := by
    intro t ht1 ht2
    rw [hderivG t (hwin t ht1 ht2)]
    have hfour := asm_four k C₀ N L p₂ _ _ _ _
      (hAbd t ht1 ht2) (hBbd t ht1 ht2) (hCbd t ht1 ht2) (hDbd t ht1 ht2)
    refine le_trans hfour ?_
    calc Cgs k C₀ * N ^ k * p₂ / L = Cgs k C₀ * (N ^ k * p₂ / L) := by ring
      _ ≤ Cg * (N ^ k * p₂ / L) := mul_le_mul_of_nonneg_right hCgs_le (by positivity)
      _ = Cg * N ^ k * p₂ / L := by ring
  have hstep : ((k : ℝ) + 1) * ((q : ℝ) / Qm) ≤ W := by
    rw [hW, ← mul_div_assoc, div_le_div_iff₀ hQmpos (by positivity)]
    nlinarith [hmain]
  obtain ⟨f, hfinj, hfmem⟩ := exists_lattice_points (delta := (q : ℝ) / Qm) (u := u) (W := W)
    (n := k) hδpos hstep
  have hconst : ∀ i : Fin (k + 1),
      G.eval ((q : ℝ) / Qm * (f i)) = G.eval ((q : ℝ) / Qm * (f 0)) := by
    intro i
    refine int_eq_of_abs_sub_lt_one (hGint (f i)) (hGint (f 0)) ?_
    have hi := hfmem i
    have h0 := hfmem 0
    have h1 : |G.eval ((q:ℝ)/Qm*(f i)) - G.eval ((q:ℝ)/Qm*(f 0))| ≤
        Cg * N ^ k * p₂ / L * |(q:ℝ)/Qm*(f i) - (q:ℝ)/Qm*(f 0)| := by
      refine abs_sub_le_of_deriv_bound (f := fun s => G.eval s)
        (g := fun x => G.derivative.eval x) (u := (q:ℝ)/Qm*(f 0)) (v := (q:ℝ)/Qm*(f i))
        (C := Cg * N ^ k * p₂ / L) ?_ ?_
      · intro x _; exact G.hasDerivAt x
      · intro x hx
        have hx2 := min_max_mem ⟨h0.1, h0.2⟩ ⟨hi.1, hi.2⟩ x hx
        exact hGbd x hx2.1 hx2.2
    have h2 : |(q:ℝ)/Qm*(f i) - (q:ℝ)/Qm*(f 0)| ≤ W := by
      rw [abs_le]
      constructor <;> linarith [hi.1, hi.2, h0.1, h0.2]
    have h4 : Cg * N ^ k * p₂ / L * W = 1/2 := by
      rw [hW]; field_simp; try ring
    have h5 : Cg * N ^ k * p₂ / L * |(q:ℝ)/Qm*(f i) - (q:ℝ)/Qm*(f 0)| ≤ 1/2 := by
      rw [← h4]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h5]
  have hGconst : G = Polynomial.C (G.eval ((q : ℝ) / Qm * (f 0))) :=
    poly_eq_C_of_eval_eq hGdeg hfinj hconst
  obtain ⟨m0, hm0⟩ := hGint (f 0)
  have hInt : IntegralOn 1 (dil (p₂ : ℝ) G1 - dil (p₁ : ℝ) G2) :=
    IntegralOn_dil_sub (p₁ := p₁) (p₂ := p₂) (Qm := Qm) (G := G) (gt := gt) (G1 := G1)
      (G2 := G2) (c := G.eval ((q : ℝ) / Qm * (f 0))) hQmpos hGdef hGconst ⟨m0, hm0⟩ hedgeHint
  have hΔbound : |Tsum1 - Tsum2| ≤ 4 * Real.pi * C₀ * C2c k C₀ * N := by
    have hzag : |(Tsum1 - Tsum2) / (2 * Real.pi) / u| ≤ C2c k C₀ * p₂ / L := by
      have h1 := hderivG u (hwin u le_rfl huW)
      have hGzero : G.derivative.eval u = 0 := by rw [hGconst]; simp
      rw [hGzero] at h1
      have h2 : (Tsum1 - Tsum2) / (2 * Real.pi) / u =
          -((p₂:ℝ) * deriv eps1 ((p₂:ℝ)*u) - (p₁:ℝ) * deriv eps2 ((p₁:ℝ)*u) -
            et.derivative.eval u) := by linarith
      rw [h2, abs_neg]
      exact asm_C2c_sum k C₀ p₁ p₂ L hC0nn hp1pos hp2pos hLpos hp1p2 hCeps2nn
        (hder1 _ (hBmem u le_rfl huW)) (hder2 _ (hCmem u le_rfl huW)) (hetbd u le_rfl huW)
    have hup2le : u * (p₂ : ℝ) ≤ 2 * C₀ * N * L := by
      have h1 : u < (x₁ + L) / (p₂ : ℝ) := by linarith [huW_lt, hWpos]
      have h2 : u * (p₂ : ℝ) < x₁ + L := (lt_div_iff₀ hp2pos).mp h1
      have h3 : L ≤ x₁ := by
        have h4 : N * L / C₀ ≤ x₁ := by rw [div_le_iff₀ hC0pos]; linarith [hx1a]
        have h5 : L ≤ N * L / C₀ := by
          rw [le_div_iff₀ hC0pos]
          nlinarith [hLpos, hNpos, hC0pos, hN100]
        linarith [h4, h5]
      have h6 : x₁ + L ≤ 2 * C₀ * N * L := by
        have h7 : x₁ + L ≤ 2 * x₁ := by linarith [h3]
        linarith [h7, hx1b]
      linarith [h2, h6]
    have hfin1 : |(Tsum1 - Tsum2) / (2 * Real.pi) / u| * (2 * Real.pi * u) ≤
        (C2c k C₀ * p₂ / L) * (2 * Real.pi * u) :=
      mul_le_mul_of_nonneg_right hzag (by positivity)
    have heq : |Tsum1 - Tsum2| =
        |(Tsum1 - Tsum2) / (2 * Real.pi) / u| * (2 * Real.pi * u) := by
      have h2piu : (0:ℝ) < 2 * Real.pi * u := by positivity
      have hne : (2 * Real.pi * u) ≠ 0 := ne_of_gt h2piu
      rw [show (Tsum1 - Tsum2) / (2 * Real.pi) / u = (Tsum1 - Tsum2) * (2 * Real.pi * u)⁻¹ by ring,
        abs_mul, abs_of_pos (inv_pos.mpr h2piu), mul_assoc, inv_mul_cancel₀ hne, mul_one]
    have hfin2 : (C2c k C₀ * p₂ / L) * (2 * Real.pi * u) ≤
        4 * Real.pi * C₀ * C2c k C₀ * N := by
      have h6 : (C2c k C₀ * p₂ / L) * (2 * Real.pi * u) =
          2 * Real.pi * C2c k C₀ * (u * p₂) / L := by field_simp; try ring
      rw [h6, div_le_iff₀ hLpos]
      have h7 : 2 * Real.pi * C2c k C₀ * (u * p₂) ≤
          2 * Real.pi * C2c k C₀ * (2 * C₀ * N * L) :=
        mul_le_mul_of_nonneg_left hup2le (by positivity)
      linarith [h7]
    linarith [hfin1, heq, hfin2]
  refine ⟨Tsum1, hTsum1_le, q, hq1, ?_, G1, G2, ?_, ?_, hG1in, hG2in, ?_, ?_, hInt⟩
  · simpa [hZdef] using hqZ
  · exact Polynomial.mem_degreeLE.mpr ((Polynomial.natDegree_le_iff_degree_le).mp hG1deg)
  · exact Polynomial.mem_degreeLE.mpr ((Polynomial.natDegree_le_iff_degree_le).mp hG2deg)
  · intro t ht
    have h1 : deriv (fun s => P₁.eval s - Tsum1 / (2 * Real.pi) * Real.log s - G1.eval s) t
        = deriv eps1 t := by rw [heps1]
    rw [h1]
    exact le_trans (hder1 t ht) (div_le_div_of_nonneg_right hce1le (le_of_lt hLpos))
  · intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hx2pos ht.1
    have hNLt : N * L / C₀ ≤ t := by
      rw [div_le_iff₀ hC0pos]
      have h := mul_le_mul_of_nonneg_left ht.1 (le_of_lt hC0pos)
      linarith [hx2a, h]
    have hhe : |deriv eps2 t| ≤ Ceps2 k C₀ / L :=
      hder2 t ⟨by nlinarith [ht.1, hC0pos, hLpos], by nlinarith [ht.2, hC0pos, hLpos]⟩
    have hkey := eps2_final_bound k C₀ L N t (Tsum1 - Tsum2) (deriv eps2 t) hC₀ hLpos
      hC2cnn hΔbound hNLt ht0 hhe
    have hd := deriv_sub_log_const P₂ G2 Tsum2 Tsum1 t ht0
    have hd2 : deriv (fun s => P₂.eval s - Tsum2 / (2 * Real.pi) * Real.log s - G2.eval s) t
        = deriv eps2 t := by rw [heps2]
    rw [hd, hd2]
    rw [show (Tsum1 - Tsum2) / (2 * Real.pi) * (1 / t) =
        (Tsum1 - Tsum2) / (2 * Real.pi) / t by ring]
    exact hkey


end Work.BMF
