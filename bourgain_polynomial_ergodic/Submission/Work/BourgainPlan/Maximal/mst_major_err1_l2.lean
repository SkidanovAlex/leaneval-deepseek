import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.major_arc_nbd_bound
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.khatZMult_coeFn_star_mstWeyl

/-!
# The `ℓ²` estimate for the first major-arc error `m_{2^n} Ξ_n − ν_{2^n}`

Auxiliary lemmas (periodicity of the Weyl kernel, the support radius of the level bump, the
"exponential beats subexponential" arithmetic) followed by the target estimate
`mst_major_err1_l2`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle


/-! ## Periodicity of the Weyl kernel -/

/-- For an integer `m` and a real `a`, `e^{2πi(a+m)} = e^{2πia}`. -/
lemma exp_two_pi_I_add_int (a : ℝ) (m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (((a + (m : ℝ)) : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
  have hsplit : 2 * Real.pi * Complex.I * (((a + (m : ℝ)) : ℝ) : ℂ)
      = 2 * Real.pi * Complex.I * (a : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The Weyl kernel `θ ↦ N⁻¹ Σ_{n<N} e(θ P(n))` is `1`-periodic in `θ` (the exponents `P(n)` are
integers). -/
lemma polyWeylKernel_add_int (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) (k : ℤ) :
    polyWeylKernel P N (θ + k) = polyWeylKernel P N θ := by
  unfold polyWeylKernel
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have h : (θ + (k : ℝ)) * ((P.eval (n : ℤ) : ℤ) : ℝ)
      = θ * ((P.eval (n : ℤ) : ℤ) : ℝ) + ((k * P.eval (n : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h]
  exact exp_two_pi_I_add_int _ _

/-- The Weyl kernel only depends on the class of its argument modulo `1`. -/
lemma polyWeylKernel_of_coe_eq (P : Polynomial ℤ) (N : ℕ) {x y : ℝ}
    (h : ((x : ℝ) : Circ) = ((y : ℝ) : Circ)) :
    polyWeylKernel P N x = polyWeylKernel P N y := by
  have hzero : ((x - y : ℝ) : Circ) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  rw [Int.smul_one_eq_cast] at hn
  have hxy : x = y + (n : ℝ) := by linarith
  rw [hxy, polyWeylKernel_add_int]

/-! ## The support radius of the level bump -/

/-- `iwRep` is a canonical representative of modulus `≤ 1/2`, where the circle norm is the absolute
value. -/
lemma norm_eq_abs_iwRep_of_le_half {ζ : Circ} (h : |iwRep ζ| ≤ 1 / 2) : ‖ζ‖ = |iwRep ζ| := by
  have h2 :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (x := iwRep ζ) (by norm_num)).mpr (by simpa using h)
  rwa [coe_iwRep ζ] at h2

/-- **The support radius of the level bump `η_n`**: if `η_n(ζ) ≠ 0` then `|iwRep ζ| ≤ ½·2^{−n(d−χ)}`
(the bump `η` vanishes beyond `1/2`). -/
lemma mstEta_ne_zero_abs_iwRep (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (n : ℕ) {ζ : Circ}
    (h : mstEta d χ η n ζ ≠ 0) :
    |iwRep ζ| ≤ (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
  set c : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hle : |c * iwRep ζ| ≤ 1 / 2 := by
    by_contra hlt
    rw [not_le] at hlt
    exact h (by rw [mstEta_apply]; exact hη2 _ hlt)
  rw [abs_mul, abs_of_pos hcpos] at hle
  have h1 : |iwRep ζ| ≤ (1 / 2) / c := by
    rw [le_div_iff₀ hcpos]; linarith
  have h2 : (1 / 2) / c = (1 / 2) * c⁻¹ := by ring
  have h3 : c⁻¹ = (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
    rw [hc]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
  rwa [h2, h3] at h1

/-! ## Arithmetic: exponential beats subexponential -/

/-- **Sublinear growth of `n^{1/10}`**: for every `B > 0`, `n^{1/10} ≤ B n` for all large `n`. -/
lemma rpow_ten_le_mul (B : ℝ) (hB : 0 < B) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ (1 / 10 : ℝ) ≤ B * (n : ℝ) := by
  refine ⟨max 1 ⌈(B⁻¹) ^ 10⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : (B⁻¹) ^ 10 ≤ (n : ℝ) := by
    have h : ((⌈(B⁻¹) ^ 10⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    exact le_trans (Nat.le_ceil _) h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h9 : (n : ℝ) ≤ (n : ℝ) ^ 9 := le_self_pow₀ hnR1 (by norm_num)
  have hprod : (1 : ℝ) ≤ B ^ 10 * (n : ℝ) ^ 9 := by
    have hle : B ^ 10 * (B⁻¹) ^ 10 ≤ B ^ 10 * (n : ℝ) ^ 9 :=
      mul_le_mul_of_nonneg_left (le_trans hnB h9) (by positivity)
    have : B ^ 10 * (B⁻¹) ^ 10 = 1 := by rw [← mul_pow]; field_simp
    linarith
  have hnle : (n : ℝ) ≤ (B * (n : ℝ)) ^ 10 := by
    have h : (n : ℝ) * 1 ≤ (n : ℝ) * (B ^ 10 * (n : ℝ) ^ 9) :=
      mul_le_mul_of_nonneg_left hprod hnpos.le
    have heq : (n : ℝ) * (B ^ 10 * (n : ℝ) ^ 9) = (B * (n : ℝ)) ^ 10 := by ring
    linarith
  have hpow : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 10 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hkey : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 10 ≤ (B * (n : ℝ)) ^ 10 := by
    rw [hpow]; exact hnle
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (10 : ℕ) ≠ 0)).mp hkey

/-- **The MST scale**: with `ρ = mstRho l = 1/(10 l)` and `N = n`, `(n^ρ) = n^{1/10}`. -/
lemma mstRho_pow_eq_real (l : ℕ) (hl : 1 ≤ l) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ l) ^ (mstRho l) = (n : ℝ) ^ (1 / 10 : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
    linarith
  rw [mstRho, ← Real.rpow_natCast (n : ℝ) l, ← Real.rpow_mul hn0]
  congr 1
  field_simp

/-- **The level scale dominates the support radius**: for large `n`,
`2^{−n(d−χ)} < 2 e^{−n^{1/10}}`, which forces the bump supports to be pairwise disjoint. -/
lemma pow_two_neg_lt_two_exp_neg (d : ℕ) (hd : 1 ≤ d) {χ : ℝ} (hχ : χ < 1 / 10) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) < 2 * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hδ : 0 < (d : ℝ) - χ := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨N₁, hN₁⟩ := rpow_ten_le_mul (Real.log 2 * ((d : ℝ) - χ) / 2) (by positivity)
  refine ⟨max N₁ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hle := hN₁ n (le_trans (le_max_left _ _) hn)
  have hlt : (n : ℝ) ^ (1 / 10 : ℝ) < (Real.log 2 * ((d : ℝ) - χ)) * (n : ℝ) := by
    have hpos : 0 < (Real.log 2 * ((d : ℝ) - χ)) * (n : ℝ) := mul_pos (mul_pos hlog2 hδ) hnpos
    have h : (Real.log 2 * ((d : ℝ) - χ) / 2) * (n : ℝ)
        = ((Real.log 2 * ((d : ℝ) - χ)) * (n : ℝ)) / 2 := by ring
    rw [h] at hle
    linarith
  have hpow : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
      = Real.exp (-((Real.log 2 * ((d : ℝ) - χ)) * (n : ℝ))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  rw [hpow]
  have h1 : Real.exp (-((Real.log 2 * ((d : ℝ) - χ)) * (n : ℝ)))
      < Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : (0 : ℝ) < Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := Real.exp_pos _
  linarith

/-- **The final arithmetic bound of the first major-arc error estimate**: for large `n` and all `l'`
with `2^{l'} ≤ 2 e^{n^{1/10}}`,
`2^{l'} (2^{−n(d−χ)} · 2^{n(d−1)} + 2^{−n}) ≤ 4 · 2^{−n/2}`. -/
lemma mst_major_err1_arith (d : ℕ) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ l' : ℕ,
      (2 : ℝ) ^ l' ≤ 2 * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) →
      (2 : ℝ) ^ l' * ((2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
          * (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹)
        ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hhalf : 0 < 1 / 2 - χ := by linarith
  obtain ⟨N₁, hN₁⟩ := rpow_ten_le_mul (Real.log 2 * (1 / 2 - χ)) (by positivity)
  obtain ⟨N₂, hN₂⟩ := rpow_ten_le_mul (Real.log 2 / 2) (by positivity)
  refine ⟨max N₁ (max N₂ 1), fun n hn l' hl' => ?_⟩
  have hn1 : 1 ≤ n := by omega
  set e : ℝ := (n : ℝ) ^ (1 / 10 : ℝ) with he
  have hb1 : Real.exp e * (2 : ℝ) ^ (-((1 - χ) * (n : ℝ))) ≤ (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-((1 - χ) * (n : ℝ))), ← Real.exp_add,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-((n : ℝ) / 2))]
    apply Real.exp_le_exp.mpr
    have h := hN₁ n (le_trans (le_max_left _ _) hn)
    rw [← he] at h
    calc e + Real.log 2 * (-((1 - χ) * (n : ℝ)))
        ≤ (Real.log 2 * (1 / 2 - χ)) * (n : ℝ) + Real.log 2 * (-((1 - χ) * (n : ℝ))) := by
          linarith
      _ = Real.log 2 * (-((n : ℝ) / 2)) := by ring
  have hb2 : Real.exp e * (2 : ℝ) ^ (-(n : ℝ)) ≤ (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-(n : ℝ)), ← Real.exp_add,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-((n : ℝ) / 2))]
    apply Real.exp_le_exp.mpr
    have h := hN₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    rw [← he] at h
    calc e + Real.log 2 * (-(n : ℝ))
        ≤ (Real.log 2 / 2) * (n : ℝ) + Real.log 2 * (-(n : ℝ)) := by linarith
      _ = Real.log 2 * (-((n : ℝ) / 2)) := by ring
  have hA : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) * (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - 1))
      = (2 : ℝ) ^ (-((1 - χ) * (n : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hB : ((2 : ℝ) ^ (n : ℝ))⁻¹ = (2 : ℝ) ^ (-(n : ℝ)) :=
    (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ)).symm
  have hbr : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
      * (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹ := by positivity
  calc (2 : ℝ) ^ l' * ((2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
          * (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹)
      ≤ (2 * Real.exp e) * ((2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
          * (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right hl' hbr
    _ = 2 * (Real.exp e * (2 : ℝ) ^ (-((1 - χ) * (n : ℝ)))
          + Real.exp e * (2 : ℝ) ^ (-(n : ℝ))) := by rw [hA, hB]; ring
    _ ≤ 2 * ((2 : ℝ) ^ (-((n : ℝ) / 2)) + (2 : ℝ) ^ (-((n : ℝ) / 2))) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by norm_num)
    _ = 4 * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by ring

/-- `2` to a natural power, written as a real power of the natural cast. -/
lemma pow_two_nat_rpow_cast (n : ℕ) (t : ℝ) :
    (((2 ^ n : ℕ) : ℝ)) ^ t = (2 : ℝ) ^ ((n : ℝ) * t) := by
  have h : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by push_cast; norm_num
  rw [h, ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- For large `n`, `2^n ≥ 3` and `2 · e^{n^{1/10}} ≤ 2^n`. -/
lemma two_pow_ge_three_nat_and_two_mul_exp_le :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      (3 : ℕ) ≤ 2 ^ n ∧ 2 * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ (2 : ℝ) ^ n := by
  obtain ⟨N₁, hN₁⟩ := rpow_ten_le_mul (Real.log 2 / 2) (by positivity)
  refine ⟨max N₁ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h := hN₁ n (le_trans (le_max_left _ _) hn)
  have h3 : (3 : ℕ) ≤ 2 ^ n := by
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  refine ⟨h3, ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hkey : (n : ℝ) ^ (1 / 10 : ℝ) ≤ Real.log 2 * ((n : ℝ) - 1) := by
    calc (n : ℝ) ^ (1 / 10 : ℝ) ≤ Real.log 2 / 2 * (n : ℝ) := h
      _ ≤ Real.log 2 * ((n : ℝ) - 1) := by nlinarith
  have hexp : Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ (2 : ℝ) ^ ((n : ℝ) - 1) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow : (2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) - 1) = (2 : ℝ) ^ (n : ℝ) := by
    conv_rhs => rw [← show (1 : ℝ) + ((n : ℝ) - 1) = (n : ℝ) by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have h2n : (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n := Real.rpow_natCast 2 n
  calc 2 * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))
      ≤ 2 * (2 : ℝ) ^ ((n : ℝ) - 1) := by linarith
    _ = (2 : ℝ) ^ (n : ℝ) := hpow
    _ = (2 : ℝ) ^ n := h2n

/-! ## The pointwise major-arc error for one arc -/

/-- **MST §4.2, eqs. (37)–(38): the major-arc error at one level-`n` arc.**  For `β ∈ 𝒰(n)` with a
representative `β = arcPt q a` carrying the weight `mstG P β = polyWeight P q a` and
`q ≤ e^{n^{1/10}}`, and for `ξ` in the support of the level bump `η_n(· − β)`, the Weyl kernel
`mstWeyl P (2^n) ξ` differs from the model term `mstG P β · mstProf P (2^n) (ξ − β)` by at most
`C 2^{−n/2}`.

Proof: the bump support gives `|iwRep (ξ − β)| ≤ ½·2^{−n(d−χ)}`; applying `major_arc_nbd_bound` at
the real point `iwRep (ξ − β) + a/q` (whose class is that of `iwRep ξ`, so the Weyl kernel is the
one at `ξ`, and whose offset from `a/q` is exactly `iwRep (ξ − β)`, so the profile is the one at
`ξ − β`) with `M = 2^{n(d−χ)}` and `2^{l'}` the dyadic rounding of `q` gives an error
`≤ C·2^{l'}(2^{−n(1−χ)} + 2^{−n}) ≤ C·4·2^{−n/2}` by `mst_major_err1_arith`. -/
lemma mst_major_err1_term
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l) (N₀ : ℕ)
    (hrep : ∀ n : ℕ, N₀ ≤ n → ∀ β ∈ mstU l n, ∃ (q : ℕ) (a : ℤ),
      0 < q ∧ 0 ≤ a ∧ a < q ∧ arcPt q a = β ∧ mstG P β = polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ (β ξ : Circ),
      β ∈ mstU l n → mstEta P.natDegree χ η n (ξ - β) ≠ 0 →
      ‖mstWeyl P (2 ^ n) ξ - mstG P β * mstProf P (2 ^ n) (ξ - β)‖
        ≤ C * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
  classical
  obtain ⟨Ca, hCa, hMA⟩ := major_arc_nbd_bound P hd
  obtain ⟨Nar, hNar⟩ := mst_major_err1_arith (P.natDegree) (χ := χ) hχ0 hχ1
  obtain ⟨Npw, hNpw⟩ := two_pow_ge_three_nat_and_two_mul_exp_le
  refine ⟨4 * Ca, by positivity, max N₀ (max Nar (max Npw 2)), fun n hn β ξ hβ hne => ?_⟩
  have hnN₀ : N₀ ≤ n := by omega
  have hnAr : Nar ≤ n := by omega
  have hnPw : Npw ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨q, a, hq0, ha0, haq, harc, hG, hqbd⟩ := hrep n hnN₀ β hβ
  have hq1 : 1 ≤ q := hq0
  set l' : ℕ := Nat.log 2 (2 * q) with hl'def
  have hq2l : q ≤ 2 ^ l' := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (2 * q)
    rw [← hl'def] at h
    rw [Nat.succ_eq_add_one, pow_add, pow_one] at h
    omega
  have h2l'' : 2 ^ l' ≤ 2 * q := by
    have h := Nat.pow_log_le_self 2 (by omega : 2 * q ≠ 0)
    rwa [← hl'def] at h
  have hql' : (q : ℝ) ≤ (2 : ℝ) ^ l' := by
    calc (q : ℝ) ≤ ((2 ^ l' : ℕ) : ℝ) := by exact_mod_cast hq2l
      _ = (2 : ℝ) ^ l' := by push_cast; ring
  have h2l' : (2 : ℝ) ^ l' ≤ 2 * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) := by
    have hbd := hqbd
    rw [mstRho_pow_eq_real l hl n hn1] at hbd
    calc (2 : ℝ) ^ l' = ((2 ^ l' : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast h2l''
      _ = 2 * (q : ℝ) := by push_cast; ring
      _ ≤ 2 * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) := by linarith
  have hl'N : (2 : ℝ) ^ l' ≤ (((2 ^ n : ℕ)) : ℝ) := by
    calc (2 : ℝ) ^ l' ≤ 2 * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ)) := h2l'
      _ ≤ (2 : ℝ) ^ n := (hNpw n hnPw).2
      _ = (((2 ^ n : ℕ)) : ℝ) := by push_cast; ring
  have hN3 : 3 ≤ 2 ^ n := (hNpw n hnPw).1
  set M : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ)) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    refine Real.one_le_rpow (by norm_num) ?_
    have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.natDegree)
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  have hu : |iwRep (ξ - β)| ≤ (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) :=
    mstEta_ne_zero_abs_iwRep P.natDegree χ η hη2 n hne
  have hcond : |(iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) - (a : ℝ) / (q : ℝ)| ≤ 1 / M := by
    have h1 : |iwRep (ξ - β)| ≤ M⁻¹ := by
      rw [hMdef, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) := by positivity
      linarith
    rw [add_sub_cancel_right, one_div]
    exact h1
  have hx : ((iwRep (ξ - β) + (a : ℝ) / (q : ℝ) : ℝ) : Circ) = ((iwRep ξ : ℝ) : Circ) := by
    rw [AddCircle.coe_add, coe_iwRep (ξ - β), coe_iwRep ξ, ← harc, arcPt]
    abel
  have hkey := hMA (2 ^ n) q a l' (iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) M
    hN3 hq1 hql' hl'N hM1 hcond
  have hxsub : (iwRep (ξ - β) + (a : ℝ) / (q : ℝ)) - (a : ℝ) / (q : ℝ) = iwRep (ξ - β) := by ring
  rw [hxsub, ← hG] at hkey
  have hweyl : polyWeylKernel P (2 ^ n) (iwRep (ξ - β) + (a : ℝ) / (q : ℝ))
      = mstWeyl P (2 ^ n) ξ := by
    rw [mstWeyl_apply]
    exact polyWeylKernel_of_coe_eq P (2 ^ n) hx
  rw [hweyl] at hkey
  have hthird : (((2 ^ n : ℕ) : ℝ))⁻¹ = ((2 : ℝ) ^ (n : ℝ))⁻¹ := by
    have h : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by push_cast; norm_num
    rw [h, ← Real.rpow_natCast (2 : ℝ) n]
  have hconv : M⁻¹ * (((2 ^ n : ℕ) : ℝ)) ^ ((P.natDegree : ℝ) - 1) + (((2 ^ n : ℕ) : ℝ))⁻¹
      = (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
        * (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹ := by
    rw [hMdef, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), pow_two_nat_rpow_cast, hthird]
  have hfinal : Ca * (2 : ℝ) ^ l' * (M⁻¹ * (((2 ^ n : ℕ) : ℝ)) ^ ((P.natDegree : ℝ) - 1)
        + (((2 ^ n : ℕ) : ℝ))⁻¹) ≤ (4 * Ca) * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
    rw [hconv]
    calc Ca * (2 : ℝ) ^ l' * ((2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
            * (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹)
        = Ca * ((2 : ℝ) ^ l' * ((2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ)))
            * (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - 1)) + ((2 : ℝ) ^ (n : ℝ))⁻¹)) := by
          ring
      _ ≤ Ca * (4 * (2 : ℝ) ^ (-((n : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (hNar n hnAr l' h2l') hCa.le
      _ = (4 * Ca) * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by ring
  exact hkey.trans hfinal

/-! ## The pairwise disjointness of the bump supports -/

/-- `mstRho l = 1/(10 l) > 0` for `l ≥ 1`. -/
lemma mstRho_pos (l : ℕ) (hl : 1 ≤ l) : 0 < mstRho l := by
  rw [mstRho]
  have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
  positivity

/-- The support radius of the level bump `η_n` is at most `1/2`. -/
lemma mstEta_ne_zero_abs_iwRep_le_half (d : ℕ) (hd : 1 ≤ d) {χ : ℝ} (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (n : ℕ) {ζ : Circ}
    (h : mstEta d χ η n ζ ≠ 0) :
    |iwRep ζ| ≤ 1 / 2 ∧ ‖ζ‖ = |iwRep ζ| ∧
      ‖ζ‖ ≤ (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
  have h1 := mstEta_ne_zero_abs_iwRep d χ η hη2 n h
  have hde : 0 ≤ (d : ℝ) - χ := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have he : 0 ≤ (n : ℝ) * ((d : ℝ) - χ) := mul_nonneg (by positivity) hde
  have h2 : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) ≤ 1 := by
    calc (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero 2
  have h3 : |iwRep ζ| ≤ 1 / 2 := by linarith [h1, h2]
  have h4 : ‖ζ‖ ≤ (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
    rw [norm_eq_abs_iwRep_of_le_half h3]; exact h1
  exact ⟨h3, norm_eq_abs_iwRep_of_le_half h3, h4⟩

/-- **Pairwise disjoint bump supports at one level**: for `β ≠ β'` in `𝒰(n)`, the supports of
`η_n(· − β)` and `η_n(· − β')` do not meet (for large `n`), because the points of `𝒰(n)` are
`2e^{−n^{1/10}}`-separated while the radius is only `½·2^{−n(d−χ)}`. -/
lemma mstEta_arc_unique (l : ℕ) (hl : 1 ≤ l) (d : ℕ) (hd : 1 ≤ d) {χ : ℝ} (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ ξ : Circ, ∀ β ∈ mstU l n, ∀ β' ∈ mstU l n,
      mstEta d χ η n (ξ - β) ≠ 0 → mstEta d χ η n (ξ - β') ≠ 0 → β = β' := by
  obtain ⟨Ns, hNs⟩ := sigmaN_separated (mstRho_pos l hl)
  obtain ⟨Nt, hNt⟩ := pow_two_neg_lt_two_exp_neg d hd hχ1
  refine ⟨max (max Ns Nt) 1, fun n hn ξ β hβ β' hβ' hb hb' => ?_⟩
  by_contra hne
  have hn1 : 1 ≤ n := by omega
  have hNs' : Ns ≤ n ^ l := by
    have h1 : Ns ≤ n := by omega
    calc Ns ≤ n := h1
      _ = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ l := Nat.pow_le_pow_right (n := n) (by omega) hl
  have hβU : β ∈ sigmaLeFinset (taoSetS (mstRho l) (n ^ l)) (⌊2 / mstRho l⌋₊ + 1) := by
    simpa only [mstU, iwSigma, iwK] using hβ
  have hβU' : β' ∈ sigmaLeFinset (taoSetS (mstRho l) (n ^ l)) (⌊2 / mstRho l⌋₊ + 1) := by
    simpa only [mstU, iwSigma, iwK] using hβ'
  have hsep := hNs (n ^ l) hNs' β hβU β' hβU' hne
  rw [Nat.cast_pow, mstRho_pow_eq_real l hl n hn1] at hsep
  have rβ := (mstEta_ne_zero_abs_iwRep_le_half d hd hχ1 η hη2 n hb).2.2
  have rβ' := (mstEta_ne_zero_abs_iwRep_le_half d hd hχ1 η hη2 n hb').2.2
  have htri0 : ‖β - β'‖ ≤ ‖β - ξ‖ + ‖ξ - β'‖ := by
    have h : β - β' = (β - ξ) + (ξ - β') := by abel
    rw [h]; exact norm_add_le _ _
  have htri : ‖β - β'‖ ≤ (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
    calc ‖β - β'‖ ≤ ‖β - ξ‖ + ‖ξ - β'‖ := htri0
      _ = ‖ξ - β‖ + ‖ξ - β'‖ := by rw [norm_sub_rev β ξ]
      _ ≤ (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
            + (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := add_le_add rβ rβ'
      _ = (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by ring
  linarith [hNt n (by omega), htri, hsep]

/-! ## The sum of the bump moduli and the a.e. description of the error multiplier -/

/-- **At most one bump contributes at each point**: the sum of the moduli of the level bumps
`η_n(ξ − β)`, `β ∈ 𝒰(n)`, is at most `M`. -/
lemma mstEta_sum_le (l : ℕ) (hl : 1 ≤ l) (d : ℕ) (hd : 1 ≤ d) {χ : ℝ} (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ ξ : Circ,
      ∑ β ∈ mstU l n, ‖mstEta d χ η n (ξ - β)‖ ≤ M := by
  obtain ⟨Nu, hNu⟩ := mstEta_arc_unique l hl d hd hχ1 η hη2
  refine ⟨Nu, fun n hn ξ => ?_⟩
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hηbd 0)
  set A := (mstU l n).filter (fun β => mstEta d χ η n (ξ - β) ≠ 0) with hA
  have hcard : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro β hβ β' hβ'
    rw [hA, Finset.mem_filter] at hβ hβ'
    exact hNu n hn ξ β hβ.1 β' hβ'.1 hβ.2 hβ'.2
  have hsum : ∑ β ∈ mstU l n, ‖mstEta d χ η n (ξ - β)‖
      = ∑ β ∈ A, ‖mstEta d χ η n (ξ - β)‖ := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    have hm : mstEta d χ η n (ξ - β)
        = η ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep (ξ - β)) := rfl
    by_cases h : mstEta d χ η n (ξ - β) = 0
    · have h' : η ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep (ξ - β)) = 0 := by
        rwa [hm] at h
      simp [h']
    · have h' : ¬(η ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep (ξ - β)) = 0) := by
        rwa [hm] at h
      simp [h']
  rw [hsum]
  calc ∑ β ∈ A, ‖mstEta d χ η n (ξ - β)‖ ≤ ∑ _β ∈ A, M :=
        Finset.sum_le_sum (fun β _ => hηbd _)
    _ = (A.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * M := by
        have : (A.card : ℝ) ≤ 1 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right this hMnn
    _ = M := one_mul M

/-- **The a.e. values of the first major-arc error class**: the `L^∞`-class `mstMajErr1Cls` of
`m_{2^n} Ξ_n − ν_{2^n}` is a.e. the sum
`Σ_{β ∈ 𝒰(n)} star (mstWeyl P (2^n) ξ − mstG P β · mstProf P (2^n) (ξ−β)) · η_n(ξ−β)` (the
conjugation is the sign convention of `khatZMult`). -/
lemma mstMajErr1Cls_coeFn (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hν : MemLp (mstNu P l d χ η n) ⊤ (AddCircle.haarAddCircle (T := 1))) :
    (mstMajErr1Cls P l d χ η n hη hν : Circ → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => ∑ β ∈ mstU l n,
        star (mstWeyl P (2 ^ n) ξ - mstG P β * mstProf P (2 ^ n) (ξ - β))
          * mstEta d χ η n (ξ - β) := by
  change ((mstProjCls P l d χ η n hη - mstNuCls P l d χ η n hν :
      Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circ → ℂ)
    =ᵐ[AddCircle.haarAddCircle (T := 1)] _
  have hsub := Lp.coeFn_sub (mstProjCls P l d χ η n hη) (mstNuCls P l d χ η n hν)
  have hproj : (mstProjCls P l d χ η n hη : Circ → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => star (mstWeyl P (2 ^ n) ξ) * mstXi l d χ η n ξ := by
    change (((khatZMult P (2 ^ n) • arcSymbolLp (mstEta d χ η n) hη (mstU l n) :
      Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circ → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => star (mstWeyl P (2 ^ n) ξ) * mstXi l d χ η n ξ)
    have hsmul := Lp.coeFn_lpSMul (r := ⊤) (khatZMult P (2 ^ n))
      (arcSymbolLp (mstEta d χ η n) hη (mstU l n))
    have hsmul' : ((khatZMult P (2 ^ n) • arcSymbolLp (mstEta d χ η n) hη (mstU l n) :
        Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circ → ℂ)
        =ᵐ[AddCircle.haarAddCircle (T := 1)]
        fun ξ => (khatZMult P (2 ^ n) : Circ → ℂ) ξ
          * (arcSymbolLp (mstEta d χ η n) hη (mstU l n) : Circ → ℂ) ξ := by
      filter_upwards [hsmul] with ξ h; rw [h]; rfl
    have hk := khatZMult_coeFn_star_mstWeyl P (2 ^ n)
    have hx := arcSymbolLp_coeFn (mstEta d χ η n) hη (mstU l n)
    filter_upwards [hsmul', hk, hx] with ξ h1 h2 h3
    rw [h1, h2, h3]
    rfl
  have hnu : (mstNuCls P l d χ η n hν : Circ → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => ∑ β ∈ mstU l n,
        star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) * mstEta d χ η n (ξ - β)) := by
    change (((MemLp.toLp (mstNu P l d χ η n) hν :
      Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circ → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ => ∑ β ∈ mstU l n,
        star (mstG P β) * (star (mstProf P (2 ^ n) (ξ - β)) * mstEta d χ η n (ξ - β)))
    have h := MemLp.coeFn_toLp hν
    filter_upwards [h] with ξ h1
    rw [h1]
    exact mstNu_apply P l d χ η n ξ
  filter_upwards [hsub, hproj, hnu] with ξ h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, mstXi_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [star_sub, star_mul (mstG P β) (mstProf P (2 ^ n) (ξ - β))]
  ring

/-- **The pointwise bound on the first major-arc error symbol**: for all large `n` and every `ξ`,
the sum `Σ_{β ∈ 𝒰(n)} star (mstWeyl P (2^n) ξ − mstG P β · mstProf P (2^n) (ξ−β)) · η_n(ξ−β)` is
bounded by `C · 2^{−n/2}`.  At most one `β` contributes (`mstEta_arc_unique`), and for it the
term bound `mst_major_err1_term` applies. -/
lemma mst_major_err1_sym_bound
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l) (N₀ : ℕ)
    (hrep : ∀ n : ℕ, N₀ ≤ n → ∀ β ∈ mstU l n, ∃ (q : ℕ) (a : ℤ),
      0 < q ∧ 0 ≤ a ∧ a < q ∧ arcPt q a = β ∧ mstG P β = polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ ξ : Circ,
      ‖∑ β ∈ mstU l n, star (mstWeyl P (2 ^ n) ξ - mstG P β * mstProf P (2 ^ n) (ξ - β))
          * mstEta P.natDegree χ η n (ξ - β)‖
        ≤ C * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
  obtain ⟨C₁, hC₁, N₁, hN₁⟩ := mst_major_err1_term P hd hc hχ0 hχ1 η hη2 l hl N₀ hrep
  obtain ⟨N₂, hN₂⟩ := mstEta_sum_le l hl P.natDegree (by omega) hχ1 η M hηbd hη2
  refine ⟨C₁ * (M + 1), by positivity, max N₁ N₂, fun n hn ξ => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hterm : ∀ β ∈ mstU l n,
      ‖star (mstWeyl P (2 ^ n) ξ - mstG P β * mstProf P (2 ^ n) (ξ - β))
          * mstEta P.natDegree χ η n (ξ - β)‖
        ≤ C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2)) * ‖mstEta P.natDegree χ η n (ξ - β)‖ := by
    intro β hβ
    by_cases hb : mstEta P.natDegree χ η n (ξ - β) = 0
    · rw [hb, mul_zero, norm_zero]; positivity
    · rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hN₁ n hn₁ β ξ hβ hb) (norm_nonneg _)
  calc ‖∑ β ∈ mstU l n, star (mstWeyl P (2 ^ n) ξ - mstG P β * mstProf P (2 ^ n) (ξ - β))
        * mstEta P.natDegree χ η n (ξ - β)‖
      ≤ ∑ β ∈ mstU l n, ‖star (mstWeyl P (2 ^ n) ξ - mstG P β * mstProf P (2 ^ n) (ξ - β))
          * mstEta P.natDegree χ η n (ξ - β)‖ := norm_sum_le _ _
    _ ≤ ∑ β ∈ mstU l n,
          C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2)) * ‖mstEta P.natDegree χ η n (ξ - β)‖ :=
        Finset.sum_le_sum hterm
    _ = C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2))
          * ∑ β ∈ mstU l n, ‖mstEta P.natDegree χ η n (ξ - β)‖ := by
        rw [Finset.mul_sum]
    _ ≤ C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2)) * M :=
        mul_le_mul_of_nonneg_left (hN₂ n hn₂ ξ)
          (le_of_lt (mul_pos hC₁ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)))
    _ ≤ C₁ * (M + 1) * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
        have h1 : M ≤ M + 1 := by linarith
        have h2 : (0 : ℝ) ≤ C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2)) :=
          le_of_lt (mul_pos hC₁ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _))
        calc C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2)) * M
            ≤ C₁ * (2 : ℝ) ^ (-((n : ℝ) / 2)) * (M + 1) :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = C₁ * (M + 1) * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by ring

/-- Mirek-Stein-Trojan, arXiv:1512.07518, §4.2, eqs. (37), (38), (70): the `ℓ²` estimate for the first major-arc error `m_{2^n} Ξ_n − ν_{2^n}`.

`mstMajErr1Cls P l d χ η n` is the `L^∞(𝕋)`-class of `m_{2^n}(ξ) Ξ_n(ξ) − ν_{2^n}(ξ)` (up to the a.e. identification of `khatZMult` with `star ∘ mstWeyl`, `khatZMult_coeFn_star_mstWeyl`), where `mstNu = Σ_{β ∈ 𝒰(n)} star (mstG P β · mstProf P (2^n) (ξ−β)) · mstEta d χ η n (ξ−β)` is the conjugate model — the conjugation is the sign convention of `khatZMult` — and `Ξ_n = mstXi l d χ η n` is the projection symbol.  The conclusion: this multiplier is `ℓ²`-bounded with gain `2^{−n/2}` for all large `n`.

Route:
* pointwise: for `β ∈ mstU l n` with `η_n(ξ−β) ≠ 0` one has `‖ξ − β‖ ≤ 2^{−n(d−χ)}/2`; the hypothesis `hrep` supplies a representative `β = arcPt q a` with `mstG P β = polyWeight P q a` and `q ≤ exp((n^l)^{1/(10l)})`, and `major_arc_nbd_bound` (with `N = 2^n`, `M := 2^{n(d−χ)}`, and `2^{l'}` an integer with `q ≤ 2^{l'} ≤ 2q`, e.g. `l' := Nat.log 2 (2*q)`) gives `‖mstWeyl P (2^n) ξ − mstG P β * mstProf P (2^n) (ξ−β)‖ ≤ C 2^{l'}(2^{−n(1−χ)} + 2^{−n}) ≤ C' 2^{−n/2}`, since `2^{l'} ≤ 2 exp(n^{1/10})` and `χ < 1/10`;
* the level bumps have pairwise disjoint supports (`sigmaN_separated`: points of `𝒰(n)` are `exp(−2n^{1/10})`-separated, far more than the support radius `2^{−n(d−χ)}`), so at most one `β` contributes at each `ξ` and the pointwise bound of the class symbol is `≤ C' M 2^{−n/2}`;
* Plancherel (`eLpNorm_two_opMul_le`) converts the a.e. `L^∞`-bound of the class into the `ℓ²` bound; the `=ᵐ` identifications of `khatZMult`, `arcSymbolLp` and the `toLp` classes are `Lp.coeFn_sub`, `Lp.coeFn_lpSMul`, `arcSymbolLp_coeFn`, `MemLp.coeFn_toLp` bookkeeping (cf. `mstMinorCls_coeFn` in `Maximal/mst_minor_per_n.lean` for the template). -/
theorem mst_major_err1_l2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l)
    (hrep : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ β ∈ Work.BourgainPlan.Maximal.mstU l n,
      ∃ (q : ℕ) (a : ℤ),
      0 < q ∧ 0 ≤ a ∧ a < q ∧ Work.BourgainPlan.IonescuWainger.arcPt q a = β ∧
        Work.BourgainPlan.Maximal.mstG P β = Work.BourgainPlan.Maximal.polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (Work.BourgainPlan.Maximal.mstRho l)))
    (hηml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n))
            f hf) (ENNReal.ofReal 2) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-((n : ℝ) / 2)))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  obtain ⟨N₀, hrep'⟩ := hrep
  obtain ⟨C, hC, N₁, hN₁⟩ :=
    mst_major_err1_sym_bound P hd hc hχ0 hχ1 η M hM hηbd hη2 l hl N₀ hrep'
  refine ⟨C, hC, N₁, fun n hn f hf => ?_⟩
  have hbound : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖
        ≤ C * (2 : ℝ) ^ (-((n : ℝ) / 2)) := by
    filter_upwards [mstMajErr1Cls_coeFn P l P.natDegree χ η n (hηml n) (hνml n)] with ξ h
    rw [h]
    exact hN₁ n hn ξ
  exact eLpNorm_two_opMul_le hf (by positivity) hbound

end

end Work.BourgainPlan.Maximal
