import Mathlib
import Submission.Work.GYBox
import Submission.Commons.NumberTheory.Sieve.prod_LambdaR_sq_eq
import Submission.Commons.NumberTheory.Sieve.card_box_residue_close

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

noncomputable def theta (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (x : Fin t → ℤ) (i : Fin m) : ℤ :=
  (W : ℤ) * ((∑ j, A i j * x j) + b i) + 1

noncomputable def box (l r : Fin t → ℤ) : Finset (Fin t → ℤ) :=
  Fintype.piFinset (fun j => Finset.Ico (l j) (r j))

@[simp] lemma mem_box {l r : Fin t → ℤ} {x : Fin t → ℤ} :
    x ∈ box l r ↔ ∀ j, l j ≤ x j ∧ x j < r j := by
  simp [box]

lemma prod_LambdaR_sq_theta (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (x : Fin t → ℤ) (hpos : ∀ i, 0 < theta W A b x i) :
    ∏ i, (Commons.NumberTheory.Sieve.LambdaR R (Int.toNat (theta W A b x i))) ^ 2
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R),
          ∑ e ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R),
            ∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
                    * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
                    * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ))
                  * (if Nat.lcm (d i) (e i) ∣ Int.toNat (theta W A b x i) then (1 : ℝ) else 0)) :=
  Commons.NumberTheory.Sieve.prod_LambdaR_sq_eq R m
    (fun i => Int.toNat (theta W A b x i)) (fun i => by have h := hpos i; omega)

theorem sum_LambdaR_sq_box (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (l r : Fin t → ℤ) (hpos : ∀ x ∈ box l r, ∀ i, 0 < theta W A b x i) :
    ∑ x ∈ box l r, ∏ i, (Commons.NumberTheory.Sieve.LambdaR R (Int.toNat (theta W A b x i))) ^ 2
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R),
        ∑ e ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R),
          (∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
                  * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
                  * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ))))
          * (((box l r).filter (fun x => ∀ i, Nat.lcm (d i) (e i)
              ∣ Int.toNat (theta W A b x i))).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun x hx => prod_LambdaR_sq_theta R W A b x (hpos x hx))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have step : ∀ x : Fin t → ℤ, ∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
        * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
        * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ))
      * (if Nat.lcm (d i) (e i) ∣ Int.toNat (theta W A b x i) then (1 : ℝ) else 0))
      = (∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
        * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
        * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ))))
        * (if ∀ i, Nat.lcm (d i) (e i) ∣ Int.toNat (theta W A b x i) then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_boole]
    simp
  rw [Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole]

section Counting

variable {m t : ℕ}

/-- The linear form `W(∑_j A_ij y_j + b_i) + 1` evaluated on residues mod `N`. -/
noncomputable def formVal (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (N : ℕ)
    (i : Fin m) (y : Fin t → ZMod N) : ZMod N :=
  (W : ZMod N) * ((∑ j, ((A i j : ℤ) : ZMod N) * y j) + ((b i : ℤ) : ZMod N)) + 1

/-- `D(d,e) = ∏_i lcm(d_i, e_i)`, the common modulus of the congruence system. -/
noncomputable def Ddd (d e : Fin m → ℕ) : ℕ := ∏ i, Nat.lcm (d i) (e i)

/-- The solution set, in `(Fin D)^t`, of the congruence system `lcm(d_i,e_i) ∣ θ_i(x)`.
Using `Fin D` rather than `ZMod D` avoids any `NeZero` side condition. -/
noncomputable def Sfin (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ) :
    Finset (Fin t → Fin (Ddd d e)) :=
  Finset.univ.filter (fun y => ∀ i, (Nat.lcm (d i) (e i) : ℤ) ∣
    theta W A b (fun j => ((y j : ℕ) : ℤ)) i)

/-- The density `ρ(d,e)` of the congruence system. -/
noncomputable def rho (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ) : ℝ :=
  ((Ddd d e : ℝ) ^ t)⁻¹ * ((Sfin W A b d e).card : ℝ)

lemma formVal_apply_int (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (N : ℕ)
    (x : Fin t → ℤ) (i : Fin m) :
    formVal W A b N i (fun j => ((x j : ℤ) : ZMod N)) = ((theta W A b x i : ℤ) : ZMod N) := by
  simp only [formVal, theta, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast,
    Int.cast_sum]

lemma nat_dvd_toNat_iff {k : ℕ} {n : ℤ} (hn : 0 < n) : k ∣ n.toNat ↔ (k : ℤ) ∣ n := by
  rw [← Int.toNat_of_nonneg hn.le]
  exact Int.natCast_dvd_natCast.symm

end Counting

section Main

open Commons.NumberTheory.Sieve

variable {m t : ℕ}

/-- The coefficient `∏_i μ(d_i) μ(e_i) log(R/d_i) log(R/e_i)` of the double divisor sum. -/
noncomputable def coef (R : ℕ) (d e : Fin m → ℕ) : ℝ :=
  ∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)
          * ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)
          * Real.log ((R : ℝ) / (d i : ℝ)) * Real.log ((R : ℝ) / (e i : ℝ)))

/-- The range of the divisor sum: `d_i, e_i ∈ [1, R]`. -/
noncomputable def P (R : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 R)

/-- The box average numerator `∑_{x ∈ ∏[l_j,r_j)} ∏_i Λ_R(θ_i(x))²`. -/
noncomputable def boxSum (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ) : ℝ :=
  ∑ x ∈ box l r, ∏ i, (LambdaR R (Int.toNat (theta W A b x i))) ^ 2

/-- The number of `x` in the box satisfying the congruence system `lcm(d_i,e_i) ∣ θ_i(x)`. -/
noncomputable def countBox (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ)
    (d e : Fin m → ℕ) : ℕ :=
  ((box l r).filter (fun x => ∀ i, Nat.lcm (d i) (e i) ∣ Int.toNat (theta W A b x i))).card

/-- The side product `∏_j (r_j - l_j)`. -/
noncomputable def sideProd (l r : Fin t → ℤ) : ℝ := ∏ j, ((r j - l j : ℤ) : ℝ)

/-- The main (divisor-sum) term of the box average (Green–Tao (ddr)). -/
noncomputable def mainSum (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) : ℝ :=
  ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R, coef R d e * rho W A b d e

/-- The error factor of the box-average reduction. -/
noncomputable def Efac (d e : Fin m → ℕ) (l r : Fin t → ℤ) : ℝ :=
  ((∏ j, (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) + 1))
      - (∏ j, (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) - 1)))
    / (∏ j, (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ)))

/-- The error term of the box-average reduction. -/
noncomputable def errBd (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ) : ℝ :=
  ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
    |coef R d e| * rho W A b d e * Efac d e l r

lemma box_sum_eq_divisor (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ)
    (hpos : ∀ x ∈ box l r, ∀ i, 0 < theta W A b x i) :
    boxSum (m := m) (t := t) R W A b l r
      = ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R, coef R d e * ((countBox W A b l r d e : ℕ) : ℝ) := by
  rw [boxSum, sum_LambdaR_sq_box R W A b l r hpos]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
  rw [coef, countBox]

/-- **The box-average reduction** (Green–Tao §10, step (ds) + the residue-class counting):
the box average of `∏_i Λ_R(θ_i)²` equals the divisor-sum main term up to the error `errBd`. -/
theorem box_sum_le_main (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ)
    (hpos : ∀ x ∈ box l r, ∀ i, 0 < theta W A b x i)
    (hS : 0 < sideProd l r)
    (hcount : ∀ d ∈ P (m := m) R, ∀ e ∈ P (m := m) R,
      |((countBox W A b l r d e : ℕ) : ℝ) - sideProd l r * rho W A b d e|
        ≤ sideProd l r * rho W A b d e * Efac d e l r) :
    |(sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r - mainSum (m := m) (t := t) R W A b|
      ≤ errBd (m := m) (t := t) R W A b l r := by
  classical
  rw [box_sum_eq_divisor R W A b l r hpos]
  set S := sideProd l r with hSdef
  set E : (Fin m → ℕ) → (Fin m → ℕ) → ℝ := fun d e => Efac d e l r with hEdef
  have hSne : S ≠ 0 := ne_of_gt hS
  -- rewrite the two sums
  have h1 : S⁻¹ * (∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
        coef R d e * ((countBox W A b l r d e : ℕ) : ℝ))
      = ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
          (S⁻¹ * coef R d e) * ((countBox W A b l r d e : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have h2 : mainSum (m := m) (t := t) R W A b
      = ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
          (S⁻¹ * coef R d e) * (S * rho W A b d e) := by
    rw [mainSum]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    field_simp
  rw [h1, h2]
  have hcombine : (∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
        (S⁻¹ * coef R d e) * ((countBox W A b l r d e : ℕ) : ℝ))
      - (∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
          (S⁻¹ * coef R d e) * (S * rho W A b d e))
      = ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
          ((S⁻¹ * coef R d e) * ((countBox W A b l r d e : ℕ) : ℝ)
            - (S⁻¹ * coef R d e) * (S * rho W A b d e)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_sub_distrib]
  rw [hcombine]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [errBd]
  refine Finset.sum_le_sum (fun d hd => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun e he => ?_)
  have hc := hcount d hd e he
  have hsub : (S⁻¹ * coef R d e) * ((countBox W A b l r d e : ℕ) : ℝ)
        - (S⁻¹ * coef R d e) * (S * rho W A b d e)
      = (S⁻¹ * coef R d e)
        * (((countBox W A b l r d e : ℕ) : ℝ) - S * rho W A b d e) := by ring
  rw [hsub, abs_mul]
  have h1 : |S⁻¹ * coef R d e| = S⁻¹ * |coef R d e| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hS)]
  rw [h1]
  calc S⁻¹ * |coef R d e| * |((countBox W A b l r d e : ℕ) : ℝ) - S * rho W A b d e|
      ≤ S⁻¹ * |coef R d e| * (S * rho W A b d e * E d e) := by
        refine mul_le_mul_of_nonneg_left hc ?_
        positivity
    _ = |coef R d e| * rho W A b d e * E d e := by
        field_simp

/-- Bundles the hypotheses of Green–Tao's box-average statement (Proposition 9.5). -/
def BoxData (k R W m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ) : Prop :=
  1 ≤ m ∧ m ≤ k * 2 ^ (k - 1) ∧ 0 < t ∧ t ≤ 3 * k - 4 ∧
  (∀ i, ∃ j, A i j ≠ 0) ∧
  (∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ)) ∧
  (∀ i j, (A i j).natAbs ≤ k.factorial * k) ∧
  (∀ j, (R : ℤ) ^ (10 * m) ≤ r j - l j) ∧
  (∀ x ∈ box l r, ∀ i, 0 < theta W A b x i)

/-- **The box-average asymptotic from the divisor-sum main term** (Green–Tao Proposition 9.5,
reduced to the two analytic/counting inputs `hmain` (their (ddr)) and `hcount` (the residue-class
counting) plus the elementary error estimate `herr`). -/
theorem boxAvgGood_of_main (k R W : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hmain : ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
      BoxData k R W m t A b l r →
      |mainSum R W A b - ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m|
        ≤ (ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m)
    (hcount : ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
      BoxData k R W m t A b l r →
      ∀ d ∈ P (m := m) R, ∀ e ∈ P (m := m) R,
        |((countBox W A b l r d e : ℕ) : ℝ) - sideProd l r * rho W A b d e|
          ≤ sideProd l r * rho W A b d e * Efac d e l r)
    (herr : ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
      BoxData k R W m t A b l r →
      errBd R W A b l r ≤ (ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m) :
    BoxAvgGood k R W ε := by
  intro m t A b l r hm1 hm ht1 ht2 hne hprop hbound hside hpos
  have hboxfun : (fun j => Finset.Icc (l j) (r j - 1)) = (fun j => Finset.Ico (l j) (r j)) := by
    funext j
    ext x
    simp
  rw [hboxfun] at hpos ⊢
  have hD : BoxData k R W m t A b l r :=
    ⟨hm1, hm, ht1, ht2, hne, hprop, hbound, hside, hpos⟩
  have hS : 0 < sideProd l r := by
    rw [sideProd]
    refine Finset.prod_pos (fun j _ => ?_)
    have h1 : (1 : ℤ) ≤ (R : ℤ) ^ (10 * m) := one_le_pow₀ (by exact_mod_cast hR)
    have h2 : (0 : ℤ) < r j - l j := lt_of_lt_of_le (by norm_num) (le_trans h1 (hside j))
    exact_mod_cast h2
  set A' : ℝ := ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m with hA'
  have hle := box_sum_le_main (m := m) (t := t) R W A b l r hpos hS (hcount m t A b l r hD)
  have hm' := hmain m t A b l r hD
  have he' := herr m t A b l r hD
  rw [← hA'] at hm' he'
  have hswap : |(sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r - A'|
      ≤ |(sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r
            - mainSum (m := m) (t := t) R W A b| + |mainSum (m := m) (t := t) R W A b - A'| := by
    have h1 : (sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r - A'
        = ((sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r
            - mainSum (m := m) (t := t) R W A b)
          + (mainSum (m := m) (t := t) R W A b - A') := by ring
    rw [h1]
    exact abs_add_le _ _
  calc |(sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r - A'|
      ≤ |(sideProd l r)⁻¹ * boxSum (m := m) (t := t) R W A b l r
            - mainSum (m := m) (t := t) R W A b| + |mainSum (m := m) (t := t) R W A b - A'| := hswap
    _ ≤ errBd (m := m) (t := t) R W A b l r + ε / 2 * A' := add_le_add hle hm'
    _ ≤ ε / 2 * A' + ε / 2 * A' := by linarith
    _ = ε * A' := by ring

end Main

section Bridge

variable {m t : ℕ}

/-- The `ZMod`-valued solution set of the congruence system `lcm(d_i,e_i) ∣ θ_i(x)`. -/
noncomputable def SsetZ (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (D : ℕ) [NeZero D]
    (d e : Fin m → ℕ) (hL : ∀ i, Nat.lcm (d i) (e i) ∣ D) : Finset (Fin t → ZMod D) :=
  Finset.univ.filter (fun y => ∀ i, ZMod.castHom (hL i) (ZMod (Nat.lcm (d i) (e i)))
    (formVal W A b D i y) = 0)

lemma dvd_prod_lcm (d e : Fin m → ℕ) (i : Fin m) :
    Nat.lcm (d i) (e i) ∣ Ddd d e :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

lemma Ddd_pos (d e : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i) : 0 < Ddd d e :=
  Finset.prod_pos (fun i _ => Nat.lcm_pos (by have := hd i; omega) (by have := he i; omega))

/-- `formVal` of a `ZMod N`-valued tuple is the cast of the corresponding integer `θ`. -/
lemma formVal_eq_theta_lift (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (N : ℕ) [NeZero N]
    (y : Fin t → ZMod N) (i : Fin m) :
    formVal W A b N i y = ((theta W A b (fun j => ((y j).val : ℤ)) i : ℤ) : ZMod N) := by
  have h : y = (fun j => (((y j).val : ℤ) : ZMod N)) := by
    funext j
    have h := (ZMod.natCast_zmod_val (y j)).symm
    rw [h]
    simp
  conv_lhs => rw [h]
  exact formVal_apply_int W A b N (fun j => ((y j).val : ℤ)) i

/-- The `ZMod`-valued and `Fin`-valued solution sets have the same cardinality. -/
theorem card_Sfin_eq (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ)
    (hL : ∀ i, Nat.lcm (d i) (e i) ∣ Ddd d e) [NeZero (Ddd d e)] :
    (Sfin W A b d e).card = (SsetZ W A b (Ddd d e) d e hL).card := by
  classical
  have key : ∀ (y : Fin t → Fin (Ddd d e)) (i : Fin m),
      ((ZMod.castHom (hL i) (ZMod (Nat.lcm (d i) (e i)))
          (formVal W A b (Ddd d e) i (fun j => ((y j : ℕ) : ZMod (Ddd d e)))) = 0)
        ↔ ((Nat.lcm (d i) (e i) : ℤ) ∣ theta W A b (fun j => ((y j : ℕ) : ℤ)) i)) := by
    intro y i
    have h1 : formVal W A b (Ddd d e) i (fun j => ((y j : ℕ) : ZMod (Ddd d e)))
        = ((theta W A b (fun j => ((y j : ℕ) : ℤ)) i : ℤ) : ZMod (Ddd d e)) := by
      simp only [formVal, theta, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast,
        Int.cast_sum]
    rw [h1]
    simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine Finset.card_bij
    (fun (y : Fin t → Fin (Ddd d e)) (_ : y ∈ Sfin W A b d e) =>
      fun j => ((y j : ℕ) : ZMod (Ddd d e))) ?_ ?_ ?_
  · intro y hy
    simp only [SsetZ, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact (key y i).mpr (hy i)
  · intro y₁ hy₁ y₂ hy₂ h
    funext j
    apply Fin.ext
    have h1 : (((y₁ j : ℕ) : ZMod (Ddd d e))).val = y₁ j :=
      ZMod.val_natCast_of_lt (y₁ j).isLt
    have h2 : (((y₂ j : ℕ) : ZMod (Ddd d e))).val = y₂ j :=
      ZMod.val_natCast_of_lt (y₂ j).isLt
    have h3 : ((y₁ j : ℕ) : ZMod (Ddd d e)) = ((y₂ j : ℕ) : ZMod (Ddd d e)) := by
      simpa using congrFun h j
    rw [← h1, ← h2, h3]
  · intro y' hy'
    simp only [SsetZ, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    refine ⟨fun j => ⟨(y' j).val, ZMod.val_lt _⟩, ?_, ?_⟩
    · simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      have hy'' : ((Nat.lcm (d i) (e i) : ℤ) ∣ theta W A b (fun j => ((y' j).val : ℤ)) i) := by
        have h1 := hy' i
        rw [formVal_eq_theta_lift] at h1
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h1
      simpa using hy''
    · funext j
      exact ZMod.natCast_zmod_val (y' j)

/-- The box congruence count (from the commons `card_box_residue_close` plus the identity of
`rho` with the `ZMod`-valued solution density), in the two-sided form
`ρ · ∏(N_j - D) ≤ #{x} ≤ ρ · ∏(N_j + D)`. -/
theorem countBox_two_sided (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ)
    (d e : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i) (he : ∀ i, 1 ≤ e i)
    (hpos : ∀ x ∈ box l r, ∀ i, 0 < theta W A b x i)
    (hN : ∀ j, (Ddd d e : ℤ) ≤ r j - l j) :
    rho W A b d e * (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ)))
        ≤ ((countBox W A b l r d e : ℕ) : ℝ)
      ∧ ((countBox W A b l r d e : ℕ) : ℝ)
        ≤ rho W A b d e * (∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ))) := by
  classical
  haveI : NeZero (Ddd d e) := ⟨ne_of_gt (Ddd_pos d e hd he)⟩
  have hL : ∀ i, Nat.lcm (d i) (e i) ∣ Ddd d e := dvd_prod_lcm d e
  have hcard := Commons.NumberTheory.Sieve.card_box_residue_close l r (Ddd d e)
    (SsetZ W A b (Ddd d e) d e hL) hN
  have hcount := card_Sfin_eq W A b d e hL
  have hset : (box l r).filter (fun x => ∀ i, Nat.lcm (d i) (e i) ∣ Int.toNat (theta W A b x i))
      = (box l r).filter (fun x => (fun j => ((x j : ℤ) : ZMod (Ddd d e))) ∈
          SsetZ W A b (Ddd d e) d e hL) := by
    refine Finset.filter_congr (fun x hx => ?_)
    simp only [SsetZ, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h i
      have h1 : ((Nat.lcm (d i) (e i) : ℤ) ∣ theta W A b x i) :=
        (nat_dvd_toNat_iff (hpos x hx i)).mp (h i)
      rw [formVal_apply_int]
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h1
    · intro h i
      have h1 := h i
      rw [formVal_apply_int] at h1
      have h2 : ((Nat.lcm (d i) (e i) : ℤ) ∣ theta W A b x i) := by
        simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h1
      exact (nat_dvd_toNat_iff (hpos x hx i)).mpr h2
  have hbox : box l r = Fintype.piFinset (fun j => Finset.Ico (l j) (r j)) := rfl
  have hDne : (Ddd d e : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (Ddd_pos d e hd he))
  have hrho_neg : rho W A b d e * (∏ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ)))
      = ((SsetZ W A b (Ddd d e) d e hL).card : ℝ)
        * ∏ j, (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) - 1) := by
    have hfac : ∀ j, (((r j - l j : ℤ) : ℝ) - (Ddd d e : ℝ))
        = (Ddd d e : ℝ) * (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) - 1) := by
      intro j; field_simp
    rw [rho, ← hcount]
    simp only [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    field_simp
  have hrho_pos : rho W A b d e * (∏ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ)))
      = ((SsetZ W A b (Ddd d e) d e hL).card : ℝ)
        * ∏ j, (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) + 1) := by
    have hfac : ∀ j, (((r j - l j : ℤ) : ℝ) + (Ddd d e : ℝ))
        = (Ddd d e : ℝ) * (((r j - l j : ℤ) : ℝ) / (Ddd d e : ℝ) + 1) := by
      intro j; field_simp
    rw [rho, ← hcount]
    simp only [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    field_simp
  rw [countBox, hset, hbox, hrho_neg, hrho_pos]
  exact hcard

end Bridge

end BoxAvg
end GYMaj
