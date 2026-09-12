import Mathlib
import Submission.MarkovSBern

/-!
# Markov's inequality on `[-1,1]`

**Markov's inequality**: for a real polynomial `P` of degree ≤ n bounded by `M`
on `[−1,1]`, its derivative is bounded by `n²·M` on `[−1,1]` (sharp constant
`n²`).  This is the engine behind Smith's `lem:Remez`.
-/

noncomputable section

open scoped Real BigOperators

namespace ChebSum

noncomputable def cotR (x : ℝ) : ℝ := Real.cos x / Real.sin x

lemma one_sub_cos_two_mul (u : ℝ) : 1 - Real.cos (2 * u) = 2 * Real.sin u ^ 2 := by
  rw [Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq u
  nlinarith

lemma cos_sub_cos_eq {A B : ℝ} : Real.cos A - Real.cos B =
    2 * Real.sin ((A + B) / 2) * Real.sin ((B - A) / 2) := by
  rw [Real.cos_sub_cos]
  have h : Real.sin ((A - B) / 2) = - Real.sin ((B - A) / 2) := by
    rw [← Real.sin_neg]
    ring_nf
  rw [h]
  ring

lemma cot_sub_cot_eq_sin_sub_div {A B : ℝ} (hA : Real.sin A ≠ 0) (hB : Real.sin B ≠ 0) :
    cotR A - cotR B = Real.sin (B - A) / (Real.sin A * Real.sin B) := by
  unfold cotR
  field_simp [hA, hB]
  rw [Real.sin_sub B A]
  ring

lemma sum_Icc_sub_succ {α : Type*} [AddCommGroup α] (f : ℕ → α) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (f j - f (j + 1)) = f 1 - f (n + 1) := by
  classical
  induction' n with n ih
  · simp
  · rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    abel

/-- telescoping of cot differences over j = 1..n -/
lemma sum_cot_sub (u : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (cotR ((2 * (j : ℝ) - 1) * u) - cotR ((2 * (j : ℝ) + 1) * u))) =
      cotR u - cotR ((2 * (n : ℝ) + 1) * u) := by
  let f : ℕ → ℝ := fun m => cotR ((2 * (m : ℝ) - 1) * u)
  have htel := sum_Icc_sub_succ f n
  calc
    (∑ j ∈ Finset.Icc 1 n, (cotR ((2 * (j : ℝ) - 1) * u) - cotR ((2 * (j : ℝ) + 1) * u)))
        = (∑ j ∈ Finset.Icc 1 n, (f j - f (j + 1))) := by
          apply Finset.sum_congr rfl
          intro j hj
          unfold f
          congr 1 <;> push_cast <;> ring
    _ = f 1 - f (n + 1) := htel
    _ = cotR u - cotR ((2 * (n : ℝ) + 1) * u) := by
          unfold f
          congr 1 <;> push_cast <;> ring

/-- per-j identity -/
lemma uj_eq_cot (u : ℝ) (j : ℕ) (hcos : Real.cos u ≠ 0) (hsin : Real.sin u ≠ 0)
    (hA : Real.sin ((2 * (j : ℝ) - 1) * u) ≠ 0)
    (hB : Real.sin ((2 * (j : ℝ) + 1) * u) ≠ 0) :
    Real.sin u ^ 2 / (Real.sin ((2 * (j : ℝ) - 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * u)) =
      (Real.tan u / 2) * (cotR ((2 * (j : ℝ) - 1) * u) - cotR ((2 * (j : ℝ) + 1) * u)) := by
  rw [Real.tan_eq_sin_div_cos]
  rw [cot_sub_cot_eq_sin_sub_div (A := (2 * (j : ℝ) - 1) * u) (B := (2 * (j : ℝ) + 1) * u) hA hB]
  have harg : Real.sin ((2 * (j : ℝ) + 1) * u - (2 * (j : ℝ) - 1) * u) = Real.sin (2 * u) := by
    congr 1
    ring
  rw [harg]
  rw [Real.sin_two_mul]
  field_simp [hA, hB, hcos, hsin]

/-- Sum over j of the u_j = (tan u/2)(cot u − cot((2n+1)u)) -/
lemma sum_uj (u : ℝ) (n : ℕ) (hcos : Real.cos u ≠ 0) (hsin : Real.sin u ≠ 0)
    (hsins : ∀ j : ℕ, j ∈ Finset.Icc 1 n →
      Real.sin ((2 * (j : ℝ) - 1) * u) ≠ 0 ∧ Real.sin ((2 * (j : ℝ) + 1) * u) ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n,
      Real.sin u ^ 2 / (Real.sin ((2 * (j : ℝ) - 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * u))
    = (Real.tan u / 2) * (cotR u - cotR ((2 * (n : ℝ) + 1) * u)) := by
  calc
    ∑ j ∈ Finset.Icc 1 n,
        Real.sin u ^ 2 / (Real.sin ((2 * (j : ℝ) - 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * u))
        = ∑ j ∈ Finset.Icc 1 n, (Real.tan u / 2) *
            (cotR ((2 * (j : ℝ) - 1) * u) - cotR ((2 * (j : ℝ) + 1) * u)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact uj_eq_cot u j hcos hsin (hsins j hj).1 (hsins j hj).2
    _ = (Real.tan u / 2) *
          (∑ j ∈ Finset.Icc 1 n,
            (cotR ((2 * (j : ℝ) - 1) * u) - cotR ((2 * (j : ℝ) + 1) * u))) := by
          rw [← Finset.mul_sum]
    _ = (Real.tan u / 2) * (cotR u - cotR ((2 * (n : ℝ) + 1) * u)) := by
          rw [sum_cot_sub]

end ChebSum


namespace ChebSum

lemma uj_eq (u : ℝ) (j : ℕ) (hA : Real.sin ((2 * (j : ℝ) - 1) * u) ≠ 0)
    (hB : Real.sin ((2 * (j : ℝ) + 1) * u) ≠ 0) :
    (1 - Real.cos (2 * u)) * (Real.cos (2 * u) - Real.cos (4 * (j : ℝ) * u))⁻¹ =
      Real.sin u ^ 2 / (Real.sin ((2 * (j : ℝ) - 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * u)) := by
  rw [one_sub_cos_two_mul]
  rw [Real.cos_sub_cos]
  have h1 : Real.sin ((2 * u + 4 * (j : ℝ) * u) / 2) = Real.sin ((2 * (j : ℝ) + 1) * u) := by
    congr 1
    ring
  have h2 : Real.sin ((2 * u - 4 * (j : ℝ) * u) / 2) = - Real.sin ((2 * (j : ℝ) - 1) * u) := by
    rw [← Real.sin_neg]
    congr 1
    ring
  rw [h1, h2]
  field_simp [hA, hB]

/-- The key endpoint estimate: (1−s)·Σ_j 1/(s−cos(jπ/n)) ≤ 1 at s = cos(π/2n). -/
lemma cheb_endpoint_sum_le (n : ℕ) (hn : 1 ≤ n) :
    (1 - Real.cos (Real.pi / (2 * (n : ℝ)))) *
      ∑ j ∈ Finset.Icc 1 n, (Real.cos (Real.pi / (2 * (n : ℝ))) - Real.cos ((j : ℝ) * Real.pi / (n : ℝ)))⁻¹
      ≤ 1 := by
  classical
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  let u : ℝ := Real.pi / (4 * (n : ℝ))
  have hu : u = Real.pi / (4 * (n : ℝ)) := rfl
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu4 : u ≤ Real.pi / 4 := by
    dsimp [u]
    rw [div_le_div_iff₀]
    · exact mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le
    · positivity
    · norm_num
  have hpi4 : Real.pi / 4 < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hpi2 : Real.pi / 2 < Real.pi := by nlinarith [Real.pi_pos]
  have hu4lt : u < Real.pi / 2 := by linarith
  have hcosu : Real.cos u ≠ 0 := by
    have hpos : 0 < Real.cos u :=
      Real.cos_pos_of_mem_Ioo (x := u) (by constructor <;> linarith [hu0, hu4lt])
    exact ne_of_gt hpos
  have hsinu : Real.sin u ≠ 0 := by
    have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu4lt, hpi2])
    exact ne_of_gt hs
  have hsins : ∀ j : ℕ, j ∈ Finset.Icc 1 n →
      Real.sin ((2 * (j : ℝ) - 1) * u) ≠ 0 ∧ Real.sin ((2 * (j : ℝ) + 1) * u) ≠ 0 := by
    intro j hj
    have hj1n : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjnn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj1n
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hjnn
    have hjm1pos : 0 < (2 * (j : ℝ) - 1) := by nlinarith [hj1]
    have hjm1 : 0 < (2 * (j : ℝ) - 1) * u := mul_pos hjm1pos hu0
    have h23 : 2 * (j : ℝ) + 1 ≤ 2 * (n : ℝ) + 1 := by nlinarith [hjn]
    have hle : (2 * (j : ℝ) + 1) * u ≤ (2 * (n : ℝ) + 1) * u :=
      mul_le_mul_of_nonneg_right h23 (le_of_lt hu0)
    have h1lt2n : 2 * n + 1 < 4 * n := by omega
    have h1lt2nR : 2 * (n : ℝ) + 1 < 4 * (n : ℝ) := by exact_mod_cast h1lt2n
    have hval : (2 * (n : ℝ) + 1) * u < Real.pi := by
      rw [hu]
      have hpos : 0 < 4 * (n : ℝ) := by positivity
      calc
        (2 * (n : ℝ) + 1) * (Real.pi / (4 * (n : ℝ))) = ((2 * (n : ℝ) + 1) * Real.pi) / (4 * (n : ℝ)) := by
          rw [div_eq_mul_inv]
          ring
        _ < Real.pi := by
          rw [div_lt_iff₀ hpos]
          calc
            (2 * (n : ℝ) + 1) * Real.pi < (4 * (n : ℝ)) * Real.pi := by
              exact mul_lt_mul_of_pos_right h1lt2nR Real.pi_pos
            _ = Real.pi * (4 * (n : ℝ)) := by ring
    have hjp1lt : (2 * (j : ℝ) + 1) * u < Real.pi := by
      linarith [hle, hval]
    have hjm1lt : (2 * (j : ℝ) - 1) * u < Real.pi := by
      have hm : (2 * (j : ℝ) - 1) * u < (2 * (j : ℝ) + 1) * u := by
        have hmm : (2 * (j : ℝ) - 1) < (2 * (j : ℝ) + 1) := by nlinarith [hj1]
        exact mul_lt_mul_of_pos_right hmm hu0
      linarith [hm, hjp1lt]
    constructor
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hjm1 hjm1lt)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) hjp1lt)
  have hsum := sum_uj u n hcosu hsinu hsins
  have hterm : (∑ j ∈ Finset.Icc 1 n, (1 - Real.cos (Real.pi / (2 * (n : ℝ)))) *
      (Real.cos (Real.pi / (2 * (n : ℝ))) - Real.cos ((j : ℝ) * Real.pi / (n : ℝ)))⁻¹)
      = (∑ j ∈ Finset.Icc 1 n,
          Real.sin u ^ 2 / (Real.sin ((2 * (j : ℝ) - 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * u))) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hc2 : Real.cos (Real.pi / (2 * (n : ℝ))) = Real.cos (2 * u) := by
      congr 1
      rw [hu]
      field_simp [hn0] <;> ring
    have hcj : Real.cos ((j : ℝ) * Real.pi / (n : ℝ)) = Real.cos (4 * (j : ℝ) * u) := by
      congr 1
      rw [hu]
      field_simp [hn0] <;> ring
    rw [hc2, hcj]
    exact uj_eq u j (hsins j hj).1 (hsins j hj).2
  have hphase : (2 * (n : ℝ) + 1) * u = Real.pi / 2 + u := by
    rw [hu]
    field_simp [hn0] <;> ring
  have hcot : cotR ((2 * (n : ℝ) + 1) * u) = - Real.tan u := by
    rw [hphase]
    unfold cotR
    rw [show Real.cos (Real.pi / 2 + u) = Real.cos (u + Real.pi / 2) by rw [add_comm]]
    rw [show Real.sin (Real.pi / 2 + u) = Real.sin (u + Real.pi / 2) by rw [add_comm]]
    rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcosu] <;> ring
  have hsum2 : (Real.tan u / 2) * (cotR u - cotR ((2 * (n : ℝ) + 1) * u)) =
      (1 + Real.tan u ^ 2) / 2 := by
    rw [hcot]
    unfold cotR
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcosu, hsinu] <;> ring
  calc
    (1 - Real.cos (Real.pi / (2 * (n : ℝ)))) *
        ∑ j ∈ Finset.Icc 1 n, (Real.cos (Real.pi / (2 * (n : ℝ))) - Real.cos ((j : ℝ) * Real.pi / (n : ℝ)))⁻¹
        = (∑ j ∈ Finset.Icc 1 n, (1 - Real.cos (Real.pi / (2 * (n : ℝ)))) *
            (Real.cos (Real.pi / (2 * (n : ℝ))) - Real.cos ((j : ℝ) * Real.pi / (n : ℝ)))⁻¹) := by
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.Icc 1 n,
          Real.sin u ^ 2 / (Real.sin ((2 * (j : ℝ) - 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * u)) := hterm
    _ = (1 + Real.tan u ^ 2) / 2 := by
          rw [hsum, hsum2]
    _ ≤ 1 := by
          have htpos : 0 ≤ Real.tan u := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (le_of_lt hu0) (le_of_lt hu4lt)
          have htle : Real.tan u ≤ 1 := by
            have hsinle : Real.sin u ≤ Real.cos u := by
              have hu' : u ≤ Real.pi / 2 - u := by linarith
              have harg1 : -(Real.pi / 2) ≤ u := by linarith [hu0]
              have harg2 : Real.pi / 2 - u ≤ Real.pi / 2 := by linarith
              have hs := Real.sin_le_sin_of_le_of_le_pi_div_two harg1 harg2 hu'
              rwa [Real.sin_pi_div_two_sub] at hs
            rw [Real.tan_eq_sin_div_cos]
            rw [div_le_one]
            · exact hsinle
            · exact Real.cos_pos_of_mem_Ioo (x := u) (by constructor <;> linarith [hu0, hu4lt])
          have ht2 : Real.tan u ^ 2 ≤ 1 := by nlinarith
          nlinarith

end ChebSum

namespace Markov2

noncomputable section

open Polynomial

/-- indices of the Chebyshev extrema nodes for degree n : {0..n} -/
def tset (n : ℕ) : Finset ℕ := Finset.range (n + 1)

/-- Chebyshev extrema nodes: t_j = cos(jπ/n) -/
def tnode (n i : ℕ) : ℝ := Polynomial.Chebyshev.node n i

/-- Lagrange fundamental polynomial at the node i (degree n) -/
def lfun (n i : ℕ) : ℝ[X] := Lagrange.basis (tset n) (fun k => tnode n k) i

lemma tset_mem {n i : ℕ} : i ∈ tset n ↔ i ≤ n := by
  simp [tset]

lemma inj_tnode (n : ℕ) : Set.InjOn (fun i => tnode n i) (↑(tset n)) := by
  unfold tnode
  simpa [tset] using (Polynomial.Chebyshev.strictAntiOn_node n).injOn

lemma lfun_eval_self (n i : ℕ) (hi : i ≤ n) : (lfun n i).eval (tnode n i) = 1 := by
  unfold lfun
  exact (Lagrange.eval_basis_self (s := tset n) (v := fun k => tnode n k) (i := i)
    (inj_tnode n) (tset_mem.mpr hi))

lemma lfun_eval_ne (n i j : ℕ) (hj : j ≤ n) (hij : i ≠ j) : (lfun n i).eval (tnode n j) = 0 := by
  unfold lfun
  exact (Lagrange.eval_basis_of_ne (s := tset n) (v := fun k => tnode n k)
    (i := i) (j := j) (hij := hij) (tset_mem.mpr hj))

lemma lfun_natDegree (n i : ℕ) (hi : i ≤ n) : (lfun n i).natDegree = n := by
  unfold lfun
  have h := Lagrange.natDegree_basis (s := tset n) (v := fun k => tnode n k) (i := i)
    (inj_tnode n) (tset_mem.mpr hi)
  simpa [tset] using h

lemma lfun_degree (n i : ℕ) (hi : i ≤ n) : (lfun n i).degree = (n : WithBot ℕ) := by
  have hnd := lfun_natDegree n i hi
  rw [degree_eq_natDegree (by
    intro hz
    have : (lfun n i).eval (tnode n i) = 0 := by rw [hz]; simp
    simpa [lfun_eval_self n i hi] using this), hnd]

/-- interpolation identity: p = Σ p(t_i) ℓ_i, for natDegree ≤ n -/
lemma interp_sum {n : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    p = ∑ i ∈ tset n, C (p.eval (tnode n i)) * lfun n i := by
  classical
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (tset n) (inj_tnode n) ?_ ?_ ?_
  · have hpdeg : p.degree ≤ (n : WithBot ℕ) := (Polynomial.natDegree_le_iff_degree_le).mp hp
    have hcard : ((tset n).card : WithBot ℕ) = ((n + 1 : ℕ) : WithBot ℕ) := by simp [tset]
    rw [hcard]
    exact lt_of_le_of_lt hpdeg (by exact_mod_cast (Nat.lt_succ_self n))
  · -- degree of the sum < n+1
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by norm_num : (⊥ : WithBot ℕ) < ((tset n).card : WithBot ℕ))]
    intro i hi
    have hi' : i ≤ n := (tset_mem.mp hi)
    have h1 : (C (p.eval (tnode n i)) * lfun n i).degree ≤ (n : WithBot ℕ) := by
      calc
        (C (p.eval (tnode n i)) * lfun n i).degree ≤ (C (p.eval (tnode n i))).degree + (lfun n i).degree :=
          Polynomial.degree_mul_le _ _
        _ ≤ (0 : WithBot ℕ) + (n : WithBot ℕ) := by
          exact add_le_add Polynomial.degree_C_le (le_of_eq (lfun_degree n i hi'))
        _ = n := by simp
    have hcard : ((tset n).card : WithBot ℕ) = ((n + 1 : ℕ) : WithBot ℕ) := by simp [tset]
    rw [hcard]
    exact lt_of_le_of_lt h1 (by exact_mod_cast (Nat.lt_succ_self n))
  · -- values agree at nodes
    intro i hi
    have hi' : i ≤ n := tset_mem.mp hi
    rw [Polynomial.eval_finsetSum]
    rw [← Finset.add_sum_erase _ _ hi]
    -- main term
    have h_main : (C (p.eval (tnode n i)) * lfun n i).eval (tnode n i) = p.eval (tnode n i) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, lfun_eval_self n i hi']
      ring
    rw [h_main]
    have h_rest : (∑ j ∈ (tset n).erase i, (C (p.eval (tnode n j)) * lfun n j).eval (tnode n i)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hjl : j ≤ n := tset_mem.mp (Finset.mem_erase.mp hj).2
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      rw [lfun_eval_ne n j i hi' hji]
      ring
    rw [h_rest]
    ring

/-- derivative evaluation at x of the interpolated identity -/
lemma eval_deriv_interp {n : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ n) (x : ℝ) :
    p.derivative.eval x = ∑ i ∈ tset n, p.eval (tnode n i) * (lfun n i).derivative.eval x := by
  classical
  calc
    p.derivative.eval x = (∑ i ∈ tset n, C (p.eval (tnode n i)) * lfun n i).derivative.eval x := by
      exact congrArg (fun q : ℝ[X] => q.derivative.eval x) (interp_sum p hp)
    _ = ∑ i ∈ tset n, p.eval (tnode n i) * (lfun n i).derivative.eval x := by
      rw [Polynomial.derivative_sum]
      simp_rw [Polynomial.derivative_C_mul]
      rw [Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- T_n = Σ (−1)^i ℓ_i -/
lemma T_sum_lfun (n : ℕ) :
    Polynomial.Chebyshev.T ℝ n = ∑ i ∈ tset n, C ((-1 : ℝ) ^ i) * lfun n i := by
  classical
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (tset n) (inj_tnode n) ?_ ?_ ?_
  · have hd : (Polynomial.Chebyshev.T ℝ n).degree = (n : WithBot ℕ) := by
      rw [Polynomial.Chebyshev.degree_T]
      simp
    rw [hd]
    have hcard : ((tset n).card : WithBot ℕ) = ((n + 1 : ℕ) : WithBot ℕ) := by simp [tset]
    rw [hcard]
    exact_mod_cast (Nat.lt_succ_self n)
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by norm_num : (⊥ : WithBot ℕ) < ((tset n).card : WithBot ℕ))]
    intro i hi
    have hi' : i ≤ n := (tset_mem.mp hi)
    have h1 : (C ((-1 : ℝ) ^ i) * lfun n i).degree ≤ (n : WithBot ℕ) := by
      calc
        (C ((-1 : ℝ) ^ i) * lfun n i).degree ≤ (C ((-1 : ℝ) ^ i)).degree + (lfun n i).degree :=
          Polynomial.degree_mul_le _ _
        _ ≤ (0 : WithBot ℕ) + (n : WithBot ℕ) := by
          exact add_le_add Polynomial.degree_C_le (le_of_eq (lfun_degree n i hi'))
        _ = n := by simp
    have hcard : ((tset n).card : WithBot ℕ) = ((n + 1 : ℕ) : WithBot ℕ) := by simp [tset]
    rw [hcard]
    exact lt_of_le_of_lt h1 (by exact_mod_cast (Nat.lt_succ_self n))
  · intro i hi
    have hi' : i ≤ n := tset_mem.mp hi
    rw [Polynomial.eval_finsetSum]
    rw [← Finset.add_sum_erase _ _ hi]
    have h_main : (C ((-1 : ℝ) ^ i) * lfun n i).eval (tnode n i) = (-1 : ℝ) ^ i := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, lfun_eval_self n i hi']
      ring
    rw [h_main]
    have h_rest : (∑ j ∈ (tset n).erase i, (C ((-1 : ℝ) ^ j) * lfun n j).eval (tnode n i)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hjl : j ≤ n := tset_mem.mp (Finset.mem_erase.mp hj).2
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      rw [lfun_eval_ne n j i hi' hji]
      ring
    rw [h_rest]
    unfold tnode
    rw [Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hi')]
    ring

end
noncomputable section

open Polynomial

/-- derivative of a Finset product of linear factors -/
lemma derivative_prod_X_sub_C {t : Finset ℕ} (a : ℕ → ℝ) :
    (∏ j ∈ t, (X - C (a j))).derivative = ∑ k ∈ t, ∏ j ∈ t.erase k, (X - C (a j)) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp
  · intro i s his ih
    calc
      derivative (∏ j ∈ insert i s, (X - C (a j)))
          = derivative ((X - C (a i)) * ∏ j ∈ s, (X - C (a j))) := by
              rw [Finset.prod_insert his]
      _ = derivative (X - C (a i)) * (∏ j ∈ s, (X - C (a j))) +
            (X - C (a i)) * derivative (∏ j ∈ s, (X - C (a j))) := by
              rw [Polynomial.derivative_mul]
      _ = ∏ j ∈ s, (X - C (a j)) + (X - C (a i)) * (∑ k ∈ s, ∏ j ∈ s.erase k, (X - C (a j))) := by
              rw [Polynomial.derivative_X_sub_C, ih]
              ring
      _ = ∑ k ∈ insert i s, ∏ j ∈ (insert i s).erase k, (X - C (a j)) := by
              rw [Finset.sum_insert his]
              rw [Finset.erase_insert his]
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              have hik : i ≠ k := by
                intro hik
                subst k
                exact his hk
              have hprod : (∏ j ∈ (insert i s).erase k, (X - C (a j))) =
                  (X - C (a i)) * (∏ j ∈ s.erase k, (X - C (a j))) := by
                rw [Finset.erase_insert_of_ne hik, Finset.prod_insert]
                · simp [his, hik]
              rw [hprod]

/-- product factor extraction -/
lemma prod_erase_mul {t : Finset ℕ} {a : ℕ → ℝ} {i k : ℕ} (hk : k ∈ t) (hik : i ≠ k)
    {x : ℝ} :
    (∏ j ∈ t.erase i, (x - a j)) = (x - a k) * (∏ j ∈ (t.erase i).erase k, (x - a j)) := by
  classical
  rw [Finset.mul_prod_erase (s := t.erase i) (f := fun j => x - a j) (a := k)
    (h := Finset.mem_erase.mpr ⟨Ne.symm hik, hk⟩)]

/-- factorization of derivative sums: Σ_k ∏_{j≠i,k} (x−v_j) = A_i · Σ_k (x−v_k)⁻¹ -/
lemma deriv_sum_factor {t : Finset ℕ} {a : ℕ → ℝ} (i : ℕ) {x : ℝ}
    (hx : ∀ k ∈ t.erase i, x - a k ≠ 0) :
    (∑ k ∈ t.erase i, (∏ j ∈ (t.erase i).erase k, (x - a j))) =
      (∏ j ∈ t.erase i, (x - a j)) * (∑ k ∈ t.erase i, (x - a k)⁻¹) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]
  rw [prod_erase_mul (t := t) (a := a) (i := i) (k := k) (hk := (Finset.mem_erase.mp hk).2)
    (hik := Ne.symm (Finset.mem_erase.mp hk).1)]
  field_simp [hx k hk]


/-- basis polynomial as C c * product -/
lemma lfun_eq (n i : ℕ) (hi : i ∈ tset n) :
    lfun n i = C ((∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
      (∏ j ∈ (tset n).erase i, (X - C (tnode n j))) := by
  classical
  unfold lfun Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod (C : ℝ →+* ℝ[X]) (fun j => (tnode n i - tnode n j)⁻¹)]
  congr 1
  rw [Finset.prod_inv_distrib]

/-- closed form for the derivative of the fundamental polynomial at x (x off the nodes) -/
lemma lfun_deriv_eval (n i : ℕ) (hi : i ∈ tset n) {x : ℝ}
    (hx : ∀ j ∈ (tset n).erase i, x - tnode n j ≠ 0) :
    (lfun n i).derivative.eval x =
      (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹ *
      (∏ j ∈ (tset n).erase i, (x - tnode n j)) *
      (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹) := by
  classical
  have hpoly := lfun_eq n i hi
  calc
    (lfun n i).derivative.eval x
        = (C ((∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
            (∏ j ∈ (tset n).erase i, (X - C (tnode n j)))).derivative.eval x := by
              rw [hpoly]
    _ = ((∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
          ((∏ j ∈ (tset n).erase i, (X - C (tnode n j))).derivative.eval x) := by
              rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    _ = ((∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
          (∑ k ∈ (tset n).erase i, (∏ j ∈ ((tset n).erase i).erase k, (x - tnode n j))) := by
              rw [derivative_prod_X_sub_C (t := (tset n).erase i) (a := fun j => tnode n j)]
              rw [Polynomial.eval_finsetSum]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              rw [Polynomial.eval_prod]
              simp
    _ = ((∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
          ((∏ j ∈ (tset n).erase i, (x - tnode n j)) *
            (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹)) := by
              rw [deriv_sum_factor (t := tset n) (i := i) (a := fun j => tnode n j) hx]
    _ = (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹ *
          (∏ j ∈ (tset n).erase i, (x - tnode n j)) *
          (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹) := by
              ring




lemma cheb_endpoint_sum_le (n : ℕ) (hn : 1 ≤ n) :
    (1 - Real.cos (Real.pi / (2 * (n : ℝ)))) *
      ∑ j ∈ Finset.Icc 1 n, (Real.cos (Real.pi / (2 * (n : ℝ))) - Real.cos ((j : ℝ) * Real.pi / (n : ℝ)))⁻¹ ≤ 1 :=
  ChebSum.cheb_endpoint_sum_le n hn

lemma tnode_eq_cos {n j : ℕ} : tnode n j = Real.cos ((j : ℝ) * Real.pi / (n : ℝ)) := by
  unfold tnode Polynomial.Chebyshev.node
  congr 1

lemma cos_jn_lt_cos_half (n j : ℕ) (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    Real.cos ((j : ℝ) * Real.pi / (n : ℝ)) < Real.cos (Real.pi / (2 * (n : ℝ))) := by
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
    have hjn' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    calc
      (j : ℝ) * Real.pi / (n : ℝ) ≤ (n : ℝ) * Real.pi / (n : ℝ) := by gcongr
      _ = Real.pi := by field_simp [hn0] <;> ring
  · have hw : 0 < Real.pi / (2 * (n : ℝ)) := by positivity
    have hj1r : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    calc
      Real.pi / (2 * (n : ℝ)) = 1 * (Real.pi / (2 * (n : ℝ))) := by ring
      _ < (2 * (j : ℝ)) * (Real.pi / (2 * (n : ℝ))) := by
        exact mul_lt_mul_of_pos_right (by nlinarith) hw
      _ = (j : ℝ) * Real.pi / (n : ℝ) := by
        have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
        field_simp [hn0] <;> ring

lemma tnode_lt_cos (n j : ℕ) (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    tnode n j < Real.cos (Real.pi / (2 * (n : ℝ))) := by
  rw [tnode_eq_cos]
  exact cos_jn_lt_cos_half n j hn hj1 hjn

lemma tnode_le_cos_pi_n (n j : ℕ) (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    tnode n j ≤ Real.cos (Real.pi / (n : ℝ)) := by
  classical
  rw [tnode_eq_cos]
  by_cases hj : j = 1
  · subst j
    simp
  · have hj2 : 2 ≤ j := by omega
    apply le_of_lt
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
      have hjn' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
      calc
        (j : ℝ) * Real.pi / (n : ℝ) ≤ (n : ℝ) * Real.pi / (n : ℝ) := by gcongr
        _ = Real.pi := by field_simp [hn0] <;> ring
    · have hw : 0 < Real.pi / (n : ℝ) := by positivity
      have hj2r : (2 : ℝ) ≤ j := by exact_mod_cast hj2
      calc
        Real.pi / (n : ℝ) = 1 * (Real.pi / (n : ℝ)) := by ring
        _ < (j : ℝ) * (Real.pi / (n : ℝ)) := by
          exact mul_lt_mul_of_pos_right (by nlinarith) hw
        _ = (j : ℝ) * Real.pi / (n : ℝ) := by
          have hn0 : (n : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
          field_simp [hn0] <;> ring

/-- sum of reciprocals bound: Σ_{j=1}^n 1/(x−t_j) ≤ 1/(1−x) -/
lemma sum_recip_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x)
    (hx1 : x < 1) :
    (∑ j ∈ Finset.Icc 1 n, (x - tnode n j)⁻¹) ≤ (1 - x)⁻¹ := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let s : ℝ := Real.cos (Real.pi / (2 * (n : ℝ)))
  have hs1 : 0 < 1 - s := by
    have hc : Real.cos (Real.pi / (2 * (n : ℝ))) < 1 := by
      have ht0 : 0 < Real.pi / (2 * (n : ℝ)) := by positivity
      have ht2 : Real.pi / (2 * (n : ℝ)) < Real.pi := by
        rw [div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))]
        calc
          Real.pi = Real.pi * 1 := by ring
          _ < Real.pi * (2 * (n : ℝ)) := by
            exact mul_lt_mul_of_pos_left (by nlinarith) Real.pi_pos
      have hgt : Real.cos (Real.pi / (2 * (n : ℝ))) < Real.cos 0 := by
        refine Real.cos_lt_cos_of_nonneg_of_le_pi ?_ ?_ ?_
        · positivity
        · exact le_of_lt ht2
        · exact ht0
      simpa using hgt
    dsimp [s]
    linarith
  have hx1' : 0 < 1 - x := by linarith
  have hpos : ∀ j ∈ Finset.Icc 1 n, 0 < x - tnode n j ∧ 0 < s - tnode n j := by
    intro j hj
    have hj1n : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjnn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hts : tnode n j < s := by
      dsimp [s]
      exact tnode_lt_cos n j hn hj1n hjnn
    have htl : tnode n j < x := lt_of_lt_of_le hts hxs
    constructor <;> linarith
  calc
    (∑ j ∈ Finset.Icc 1 n, (x - tnode n j)⁻¹)
        ≤ (∑ j ∈ Finset.Icc 1 n, (s - tnode n j)⁻¹) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjd := hpos j hj
          rw [inv_le_inv₀]
          · linarith
          · exact hjd.1
          · exact hjd.2
    _ = (1 - s)⁻¹ * ((1 - s) * (∑ j ∈ Finset.Icc 1 n, (s - tnode n j)⁻¹)) := by
          field_simp [hs1.ne']
    _ ≤ (1 - s)⁻¹ * 1 := by
          gcongr
          have hs' : (1 - s) * (∑ j ∈ Finset.Icc 1 n, (s - tnode n j)⁻¹) ≤ 1 := by
            have htmp := cheb_endpoint_sum_le n hn
            simpa [s, tnode_eq_cos] using htmp
          exact hs'
    _ = (1 - s)⁻¹ := by ring
    _ ≤ (1 - x)⁻¹ := by
          rw [inv_le_inv₀]
          · linarith
          · exact hs1
          · exact hx1'


lemma erase0_eq_Icc (n : ℕ) : (tset n).erase 0 = Finset.Icc 1 n := by
  ext j
  simp [tset, Finset.mem_erase, Finset.mem_Icc]
  omega

lemma erase_comm (s : Finset ℕ) (a b : ℕ) : (s.erase a).erase b = (s.erase b).erase a := by
  ext j
  simp only [Finset.mem_erase]
  tauto

lemma sum_erase_add (s : Finset ℕ) (a : ℕ) (f : ℕ → ℝ) (h : a ∈ s) :
    (∑ x ∈ s.erase a, f x) + f a = (∑ x ∈ s, f x) := by
  rw [add_comm]
  exact Finset.add_sum_erase s f h

lemma prod_erase_mul_general (s : Finset ℕ) (a : ℕ) (f : ℕ → ℝ) (h : a ∈ s) :
    (∏ x ∈ s, f x) = f a * (∏ x ∈ s.erase a, f x) := by
  exact (Finset.mul_prod_erase s f h).symm




lemma tnode_zero (n : ℕ) : tnode n 0 = 1 := by
  simp [tnode, Polynomial.Chebyshev.node]

lemma coeff_pos {n i : ℕ} (hi : i ≤ n) :
    0 < (-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹ := by
  have h := Polynomial.Chebyshev.zero_lt_prod_node_sub_node (n := n) (i := i) hi
  have h' : 0 < (-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j)) := by
    simpa [tset, tnode] using h
  have hinv : ((-1 : ℝ) ^ i)⁻¹ = (-1 : ℝ) ^ i := by
    rw [← inv_pow]
    simp
  have heq : (-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹ =
      (((-1 : ℝ) ^ i) * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j)))⁻¹ := by
    rw [mul_inv]
    rw [hinv]
  rw [heq]
  exact inv_pos.mpr h'

lemma x_sub_node_pos {n j : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    0 < x - tnode n j := by
  have hts : tnode n j < Real.cos (Real.pi / (2 * (n : ℝ))) := tnode_lt_cos n j hn hj1 hjn
  have htx : tnode n j < x := lt_of_lt_of_le hts hxs
  linarith

lemma sum_recip_erase_neg {n i : ℕ} (hn : 1 ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) {x : ℝ}
    (hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x) (hx1 : x < 1) :
    (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹) < 0 := by
  classical
  have h0e : 0 ∈ (tset n).erase i := by
    simp [tset, Finset.mem_erase]
    omega
  have his : i ∈ Finset.Icc 1 n := by simp [Finset.mem_Icc, hi1, hin]
  have hres : ((tset n).erase i).erase 0 = (Finset.Icc 1 n).erase i := by
    rw [erase_comm (tset n) i 0, erase0_eq_Icc]
  have hgi0 : (x - tnode n 0)⁻¹ = - (1 - x)⁻¹ := by
    rw [tnode_zero]
    have hne : x - 1 ≠ 0 := by linarith
    have hne2 : 1 - x ≠ 0 := by linarith
    field_simp [hne, hne2] <;> ring
  have hgipos : 0 < (x - tnode n i)⁻¹ := by
    exact inv_pos.mpr (x_sub_node_pos hn hxs hi1 hin)
  have hsum0 : (∑ j ∈ (Finset.Icc 1 n).erase i, (x - tnode n j)⁻¹) =
      (∑ j ∈ Finset.Icc 1 n, (x - tnode n j)⁻¹) - (x - tnode n i)⁻¹ := by
    have h := Finset.add_sum_erase (Finset.Icc 1 n) (fun j => (x - tnode n j)⁻¹) his
    -- h : g i + Σ erase = Σ Icc
    linarith
  calc
    (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹)
        = (∑ j ∈ ((tset n).erase i).erase 0, (x - tnode n j)⁻¹) + (x - tnode n 0)⁻¹ := by
          rw [add_comm]
          exact (Finset.add_sum_erase ((tset n).erase i) (fun j => (x - tnode n j)⁻¹) h0e).symm
    _ = (∑ j ∈ (Finset.Icc 1 n).erase i, (x - tnode n j)⁻¹) - (1 - x)⁻¹ := by
          rw [hres, hgi0]
          ring
    _ = ((∑ j ∈ Finset.Icc 1 n, (x - tnode n j)⁻¹) - (x - tnode n i)⁻¹) - (1 - x)⁻¹ := by
          rw [hsum0]
    _ ≤ (((1 - x)⁻¹) - (x - tnode n i)⁻¹) - (1 - x)⁻¹ := by
          gcongr
          exact sum_recip_le hn hxs hx1
    _ < 0 := by
          have hle : ((1 - x)⁻¹ - (x - tnode n i)⁻¹) - (1 - x)⁻¹ = - (x - tnode n i)⁻¹ := by ring
          rw [hle]
          exact neg_neg_of_pos hgipos

lemma prod_erase_neg {n i : ℕ} (hn : 1 ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) {x : ℝ}
    (hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x) (hx1 : x < 1) :
    (∏ j ∈ (tset n).erase i, (x - tnode n j)) < 0 := by
  classical
  have h0e : 0 ∈ (tset n).erase i := by
    simp [tset, Finset.mem_erase]
    omega
  have hres : ((tset n).erase i).erase 0 = (Finset.Icc 1 n).erase i := by
    rw [erase_comm (tset n) i 0, erase0_eq_Icc]
  calc
    (∏ j ∈ (tset n).erase i, (x - tnode n j))
        = (x - tnode n 0) * (∏ j ∈ ((tset n).erase i).erase 0, (x - tnode n j)) := by
          exact (Finset.mul_prod_erase ((tset n).erase i) (fun j => x - tnode n j) h0e).symm
    _ = (x - 1) * (∏ j ∈ (Finset.Icc 1 n).erase i, (x - tnode n j)) := by
          rw [hres, tnode_zero]
    _ < 0 := by
          have hx : x - 1 < 0 := by linarith
          have hprodpos : 0 < (∏ j ∈ (Finset.Icc 1 n).erase i, (x - tnode n j)) := by
            apply Finset.prod_pos
            intro j hj
            have hj1n : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1
            have hjnn : j ≤ n := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).2
            exact x_sub_node_pos hn hxs hj1n hjnn
          exact mul_neg_of_neg_of_pos hx hprodpos

lemma sign_lfun {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x) (hx1 : x < 1)
    {i : ℕ} (hi : i ≤ n) :
    0 ≤ (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by
  classical
  by_cases hi0 : i = 0
  · subst i
    have hmem : 0 ∈ tset n := tset_mem.mpr (by omega)
    have hxne : ∀ j ∈ (tset n).erase 0, x - tnode n j ≠ 0 := by
      intro j hj
      have hjl : j ≤ n := tset_mem.mp (Finset.mem_erase.mp hj).2
      have hjp : 1 ≤ j := by
        have h0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        omega
      have hpos : 0 < x - tnode n j := x_sub_node_pos hn hxs hjp hjl
      exact ne_of_gt hpos
    have hform := lfun_deriv_eval n 0 hmem hxne
    have hc : 0 < (∏ j ∈ (tset n).erase 0, (tnode n 0 - tnode n j))⁻¹ := by
      have hc0 := coeff_pos (n := n) (i := 0) (by omega : 0 ≤ n)
      simpa using hc0
    have hA : 0 < (∏ j ∈ (tset n).erase 0, (x - tnode n j)) := by
      apply Finset.prod_pos
      intro j hj
      have hjl : j ≤ n := tset_mem.mp (Finset.mem_erase.mp hj).2
      have hjp : 1 ≤ j := by
        have h0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        omega
      exact x_sub_node_pos hn hxs hjp hjl
    have hS : 0 ≤ (∑ j ∈ (tset n).erase 0, (x - tnode n j)⁻¹) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjl : j ≤ n := tset_mem.mp (Finset.mem_erase.mp hj).2
      have hjp : 1 ≤ j := by
        have h0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        omega
      exact inv_nonneg.mpr (le_of_lt (x_sub_node_pos hn hxs hjp hjl))
    rw [hform]
    norm_num
    -- product of three positives ≥ 0
    have hcA : 0 ≤ (∏ j ∈ (tset n).erase 0, (tnode n 0 - tnode n j))⁻¹ *
        (∏ j ∈ (tset n).erase 0, (x - tnode n j)) := by
      exact (mul_pos hc hA).le
    exact mul_nonneg hcA hS
  · have hi1 : 1 ≤ i := by omega
    have hmem : i ∈ tset n := tset_mem.mpr hi
    have hxne : ∀ j ∈ (tset n).erase i, x - tnode n j ≠ 0 := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        intro h
        rw [tnode_zero] at h
        linarith
      · have hjl : j ≤ n := tset_mem.mp (Finset.mem_erase.mp hj).2
        have hjp : 1 ≤ j := by omega
        have hpos : 0 < x - tnode n j := x_sub_node_pos hn hxs hjp hjl
        exact ne_of_gt hpos
    have hform := lfun_deriv_eval n i hmem hxne
    have hc : 0 < (-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹ := coeff_pos hi
    have hA : (∏ j ∈ (tset n).erase i, (x - tnode n j)) < 0 := prod_erase_neg hn hi1 hi hxs hx1
    have hS : (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹) < 0 := sum_recip_erase_neg hn hi1 hi hxs hx1
    rw [hform]
    have hgoal : 0 ≤ ((-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
        (∏ j ∈ (tset n).erase i, (x - tnode n j)) *
        (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹) := by
      have hcA : ((-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
          (∏ j ∈ (tset n).erase i, (x - tnode n j)) < 0 :=
        mul_neg_of_pos_of_neg hc hA
      exact (mul_pos_of_neg_of_neg hcA hS).le
    have hring : (-1 : ℝ) ^ i * (((∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹ *
        (∏ j ∈ (tset n).erase i, (x - tnode n j))) *
        (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹)) =
        ((-1 : ℝ) ^ i * (∏ j ∈ (tset n).erase i, (tnode n i - tnode n j))⁻¹) *
        (∏ j ∈ (tset n).erase i, (x - tnode n j)) *
        (∑ j ∈ (tset n).erase i, (x - tnode n j)⁻¹) := by ring
    rw [hring]
    exact hgoal



/-- Bernstein's algebraic inequality (from the trigonometric Bernstein in `MarkovSBern`). -/
lemma bernstein_abs_deriv {P : Polynomial ℝ} {n : ℕ}
    (hdeg : P.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |P.eval x| ≤ 1)
    (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    |P.derivative.eval x| ≤ (n : ℝ) / Real.sqrt (1 - x ^ 2) := by
  by_cases hn0 : n = 0
  · have hp : P.derivative = 0 := by
      have hP : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by simpa [hn0] using hdeg)
      rw [hP]
      simp
    simp [hp, hn0]
  · have hn : 1 ≤ n := by omega
    have hM0 : 0 ≤ (1 : ℝ) := by norm_num
    have hb := Submission.MarkovSBern.bernstein_cos hdeg hM0 hbd (Real.arccos x) (by
      constructor
      · exact (Real.arccos_pos (x := x)).mpr hx.2
      · exact (Real.arccos_lt_pi (x := x)).mpr hx.1)
    have hcos : Real.cos (Real.arccos x) = x :=
      Real.cos_arccos (le_of_lt hx.1) (le_of_lt hx.2)
    have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
    have hmain : |P.derivative.eval x| * Real.sqrt (1 - x ^ 2) ≤ (n : ℝ) := by
      have hb' : |P.derivative.eval (Real.cos (Real.arccos x))| * Real.sin (Real.arccos x) ≤ (n : ℝ) * 1 := hb
      rw [hcos, hsin] at hb'
      simpa using hb'
    have hsqpos : 0 < Real.sqrt (1 - x ^ 2) := by
      apply Real.sqrt_pos.2
      have habs : |x| < 1 := abs_lt.mpr ⟨hx.1, hx.2⟩
      have h : x ^ 2 < 1 := by
        have hh : |x| < |(1 : ℝ)| := by simpa using habs
        simpa using sq_lt_sq.mpr hh
      nlinarith
    exact (le_div_iff₀ hsqpos).mpr (by simpa [mul_comm] using hmain)

lemma T_deriv_one_nat (n : ℕ) : ((Polynomial.Chebyshev.T ℝ n).derivative.eval 1) = (n : ℝ) ^ 2 := by
  have hU : (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval 1 = (n : ℤ) := by
    simpa using Polynomial.Chebyshev.U_eval_one ℝ ((n : ℤ) - 1)
  calc
    ((Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval 1) =
        (((n : ℤ) : ℝ[X]) * Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval 1 := by
      rw [Polynomial.Chebyshev.T_derivative_eq_U]
    _ = ((n : ℤ) : ℝ) * ((Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval 1) := by simp
    _ = ((n : ℤ) : ℝ) * (n : ℤ) := by rw [hU]
    _ = (n : ℝ) ^ 2 := by norm_num; ring

lemma T_deriv_eval_le {n : ℕ} {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(Polynomial.Chebyshev.T ℝ n).derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  have h := Polynomial.Chebyshev.abs_iterate_derivative_T_real_le (n : ℤ) (k := 1) (x := x) (by
    rw [abs_le]; constructor <;> linarith)
  -- h : |eval x (derivative^[1] (T ℝ ↑n))| ≤ eval 1 (derivative^[1] (T ℝ ↑n))
  have h1 : ((Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval x) = (Polynomial.Chebyshev.T ℝ n).derivative.eval x := by
    simp
  have h2 : ((Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval 1) = (n : ℝ) ^ 2 := by
    simpa using T_deriv_one_nat n
  simpa [h1, h2] using h

lemma abs_sum_le_sum_abs' (s : Finset ℕ) (f : ℕ → ℝ) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
  have h := norm_sum_le s f
  simpa [Real.norm_eq_abs] using h

/-- derivative of the interpolated T identity at x -/
lemma T_deriv_interp_eval (n : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ n).derivative.eval x =
      ∑ i ∈ tset n, (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by
  calc
    (Polynomial.Chebyshev.T ℝ n).derivative.eval x
        = (∑ i ∈ tset n, C ((-1 : ℝ) ^ i) * lfun n i).derivative.eval x := by
          exact congrArg (fun q : ℝ[X] => q.derivative.eval x) (T_sum_lfun n)
    _ = ∑ i ∈ tset n, (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by
          rw [Polynomial.derivative_sum]
          simp_rw [Polynomial.derivative_C_mul]
          rw [Polynomial.eval_finsetSum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- In the endpoint region (x close to 1): |p'| ≤ T_n'(x) ≤ n². -/
lemma endpoint_region_bound {p : ℝ[X]} {n : ℕ} (hn : 1 ≤ n) (hdeg : p.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1)
    {x : ℝ} (hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x) (hx1 : x < 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  classical
  have hb : ∀ i ∈ tset n, |p.eval (tnode n i)| ≤ 1 := by
    intro i hi
    have hin : tnode n i ∈ Set.Icc (-1) 1 := by
      dsimp [tnode]
      exact Polynomial.Chebyshev.node_mem_Icc
    exact hbd (tnode n i) hin
  have hsign : ∀ i ∈ tset n, 0 ≤ (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by
    intro i hi
    exact sign_lfun hn hxs hx1 (tset_mem.mp hi)
  -- p'(x) = Σ p(v_i)·ℓ_i'(x) ; |p'| ≤ Σ |ℓ_i'| = Σ (−1)^i ℓ_i' = T'(x)
  have hsum := eval_deriv_interp p hdeg x
  have hT := T_deriv_interp_eval n x
  have hmain : |p.derivative.eval x| ≤ (Polynomial.Chebyshev.T ℝ n).derivative.eval x := by
    calc
      |p.derivative.eval x| = |∑ i ∈ tset n, p.eval (tnode n i) * (lfun n i).derivative.eval x| := by rw [hsum]
      _ ≤ ∑ i ∈ tset n, |p.eval (tnode n i) * (lfun n i).derivative.eval x| := by
            exact abs_sum_le_sum_abs' (tset n) (fun i => p.eval (tnode n i) * (lfun n i).derivative.eval x)
      _ ≤ ∑ i ∈ tset n, (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by
            apply Finset.sum_le_sum
            intro i hi
            -- |p(v_i)| ≤ 1 and |ℓ_i'| = (−1)^i·ℓ_i' (since sign_lfun ≥ 0)
            have hs := hsign i hi
            have habs2 : |(-1 : ℝ) ^ i * (lfun n i).derivative.eval x| = (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := abs_of_nonneg hs
            have hm : |(lfun n i).derivative.eval x| = (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by
              rw [← habs2]
              rw [abs_mul, abs_neg_one_pow, one_mul]
            have hp : |p.eval (tnode n i)| ≤ 1 := hb i hi
            calc
              |p.eval (tnode n i) * (lfun n i).derivative.eval x| = |p.eval (tnode n i)| * |(lfun n i).derivative.eval x| := by
                    rw [abs_mul]
              _ ≤ 1 * |(lfun n i).derivative.eval x| := by
                    exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
              _ = (-1 : ℝ) ^ i * (lfun n i).derivative.eval x := by rw [hm]; ring
      _ = (Polynomial.Chebyshev.T ℝ n).derivative.eval x := hT.symm
  have hTle : (Polynomial.Chebyshev.T ℝ n).derivative.eval x ≤ (n : ℝ) ^ 2 := by
    have habsT : |(Polynomial.Chebyshev.T ℝ n).derivative.eval x| ≤ (n : ℝ) ^ 2 := by
      have hxabs : |x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [hxs, Real.neg_one_le_cos (Real.pi / (2 * (n : ℝ)))]
        · linarith
      have h := Polynomial.Chebyshev.abs_iterate_derivative_T_real_le (n : ℤ) (k := 1) (x := x) hxabs
      simpa [T_deriv_one_nat] using h
    have hTnonneg : 0 ≤ (Polynomial.Chebyshev.T ℝ n).derivative.eval x := by
      rw [hT]
      exact Finset.sum_nonneg (fun i hi => hsign i hi)
    rw [abs_of_nonneg hTnonneg] at habsT
    exact habsT
  exact le_trans hmain hTle

/-- reflected polynomial for symmetry -/
def refl (p : ℝ[X]) : ℝ[X] := p.comp (-Polynomial.X)

lemma refl_eval (p : ℝ[X]) (x : ℝ) : (refl p).eval x = p.eval (-x) := by
  simp [refl, Polynomial.eval_comp]

lemma refl_deriv_eval (p : ℝ[X]) (x : ℝ) : (refl p).derivative.eval x = - p.derivative.eval (-x) := by
  simp [refl]
  rw [Polynomial.derivative_comp]
  simp

lemma refl_natDegree (p : ℝ[X]) : (refl p).natDegree = p.natDegree := by
  unfold refl
  rw [Polynomial.natDegree_comp]
  simp

lemma refl_bound {p : ℝ[X]} (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1) :
    ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |(refl p).eval y| ≤ 1 := by
  intro y hy
  simpa [refl_eval] using hbd (-y) (by constructor <;> linarith [hy.1, hy.2])

/-- In the endpoint region (x close to −1): |p'| ≤ n². -/
lemma endpoint_region_bound_neg {p : ℝ[X]} {n : ℕ} (hn : 1 ≤ n) (hdeg : p.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1)
    {x : ℝ} (hx0 : -1 < x) (hxs : x ≤ - Real.cos (Real.pi / (2 * (n : ℝ)))) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  have hbd' : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |(refl p).eval y| ≤ 1 := by
    intro y hy
    have hneg : -y ∈ Set.Icc (-1) 1 := by constructor <;> linarith [hy.1, hy.2]
    simpa [refl_eval, abs_neg] using hbd (-y) hneg
  have hycos : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ -x := by linarith
  have hy1 : -x < 1 := by linarith
  have hb := endpoint_region_bound (p := refl p) (n := n) hn (by
    rw [refl_natDegree]; exact hdeg) hbd' (x := -x) hycos hy1
  have hm : |(refl p).derivative.eval (-x)| = |p.derivative.eval x| := by
    simp [refl_deriv_eval, abs_neg]
  simpa [hm] using hb

/-- π ≤ π·n -/
lemma pi_le_pi_mul_n (n : ℕ) (hn : 1 ≤ n) : Real.pi ≤ Real.pi * (n : ℝ) := by
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : Real.pi * 1 ≤ Real.pi * (n : ℝ) := mul_le_mul_of_nonneg_left h1n Real.pi_pos.le
  simpa using hmul

/-- sin(π/(2n)) ≥ 1/n -/
lemma sin_pi_two_n_ge (n : ℕ) (hn : 1 ≤ n) : (1 : ℝ) / n ≤ Real.sin (Real.pi / (2 * (n : ℝ))) := by
  have ht0 : 0 ≤ Real.pi / (2 * (n : ℝ)) := by positivity
  have ht2 : Real.pi / (2 * (n : ℝ)) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))]
    calc
      Real.pi ≤ Real.pi * (n : ℝ) := pi_le_pi_mul_n n hn
      _ = (Real.pi / 2) * (2 * (n : ℝ)) := by ring
  have h := Real.mul_le_sin ht0 ht2
  have hleft : (2 / Real.pi) * (Real.pi / (2 * (n : ℝ))) = (1 : ℝ) / n := by
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
    field_simp [Real.pi_pos.ne', hn0]
  rwa [hleft] at h

/-- cos(π/(2n)) ≥ 0 -/
lemma cos_pi_two_n_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ Real.cos (Real.pi / (2 * (n : ℝ))) := by
  have hlt : Real.pi / (2 * (n : ℝ)) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))]
    calc
      Real.pi ≤ Real.pi * (n : ℝ) := pi_le_pi_mul_n n hn
      _ = (Real.pi / 2) * (2 * (n : ℝ)) := by ring
  have h0 : 0 ≤ Real.pi / (2 * (n : ℝ)) := by positivity
  exact Real.cos_nonneg_of_mem_Icc (x := Real.pi / (2 * (n : ℝ))) (by constructor <;> linarith)

/-- middle region bound: |x| ≤ cos(π/2n) ⇒ |p'| ≤ n²  (uses Bernstein) -/
lemma middle_region_bound {p : ℝ[X]} {n : ℕ} (hn : 1 ≤ n) (hdeg : p.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1)
    {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1)
    (hxs : |x| ≤ Real.cos (Real.pi / (2 * (n : ℝ)))) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  have hb := bernstein_abs_deriv hdeg hbd x (by constructor <;> linarith)
  have hx2 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg x, hx0, hx1]
  have hx2pos : 0 < 1 - x ^ 2 := by
    have habs : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
    have : x ^ 2 < 1 := by
      have hh : |x| < |(1 : ℝ)| := by simpa using habs
      simpa using sq_lt_sq.mpr hh
    nlinarith
  have hposn : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hcpos : 0 ≤ Real.cos (Real.pi / (2 * (n : ℝ))) := cos_pi_two_n_nonneg n hn
  have hsin := sin_pi_two_n_ge n hn
  have hsin2 : ((1 : ℝ) / n) ^ 2 ≤ (Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 2 := by
    have h2 : 0 ≤ (1 : ℝ) / n := by positivity
    have h3 : 0 ≤ Real.sin (Real.pi / (2 * (n : ℝ))) := by
      have : 0 < (1 : ℝ) / n := by positivity
      exact le_of_lt (lt_of_lt_of_le this hsin)
    apply sq_le_sq.mpr
    rw [abs_of_nonneg h2, abs_of_nonneg h3]
    exact hsin
  have hsq : (1 : ℝ) / n ≤ Real.sqrt (1 - x ^ 2) := by
    have hcx : x ^ 2 ≤ (Real.cos (Real.pi / (2 * (n : ℝ)))) ^ 2 := by
      have habs : |x| ≤ |Real.cos (Real.pi / (2 * (n : ℝ)))| := by
        rw [abs_of_nonneg hcpos]
        exact hxs
      exact sq_le_sq.mpr habs
    have hineq : ((1 : ℝ) / n) ^ 2 ≤ 1 - x ^ 2 := by
      have hsc : (Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 2 = 1 - (Real.cos (Real.pi / (2 * (n : ℝ)))) ^ 2 := by
        have h := Real.sin_sq_add_cos_sq (Real.pi / (2 * (n : ℝ)))
        nlinarith
      calc
        ((1 : ℝ) / n) ^ 2 ≤ (Real.sin (Real.pi / (2 * (n : ℝ)))) ^ 2 := hsin2
        _ = 1 - (Real.cos (Real.pi / (2 * (n : ℝ)))) ^ 2 := hsc
        _ ≤ 1 - x ^ 2 := by nlinarith
    exact (Real.le_sqrt (one_div_nonneg.mpr (le_of_lt hposn)) hx2).mpr hineq
  calc
    |p.derivative.eval x| ≤ (n : ℝ) / Real.sqrt (1 - x ^ 2) := hb
    _ ≤ (n : ℝ) ^ 2 := by
      have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hx2pos
      rw [div_le_iff₀ hs]
      have hm1 : (1 / n) * (n : ℝ) ^ 2 ≤ Real.sqrt (1 - x ^ 2) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg (n : ℝ))
      have h1 : (1 / n) * (n : ℝ) ^ 2 = n := by
        have hnn : (n : ℝ) ≠ 0 := by positivity
        field_simp [hnn] <;> ring
      have h2 : Real.sqrt (1 - x ^ 2) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * Real.sqrt (1 - x ^ 2) := by ring
      rwa [h1, h2] at hm1

/-- endpoint x=1 bound -/
lemma endpoint_bound_one {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1) :
    |p.derivative.eval 1| ≤ (n : ℝ) ^ 2 := by
  have hdeg' : p.degree ≤ (n : WithBot ℕ) := (Polynomial.natDegree_le_iff_degree_le).mp hdeg
  have h1 : p.derivative.eval 1 ≤ (n : ℝ) ^ 2 := by
    have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := n) (P := p) (k := 1) (x := 1) le_rfl hdeg' hbd
    simpa [T_deriv_one_nat] using h
  have hbd' : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |(-p).eval x| ≤ 1 := by
    intro x hx
    simpa using hbd x hx
  have h2 : p.derivative.eval 1 ≥ - (n : ℝ) ^ 2 := by
    have hdegneg : (-p).natDegree ≤ n := by
      simpa using hdeg
    have hdeg'' : (-p).degree ≤ (n : WithBot ℕ) := (Polynomial.natDegree_le_iff_degree_le).mp hdegneg
    have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := n) (P := -p) (k := 1) (x := 1) le_rfl hdeg'' hbd'
    have h' : (-p).derivative.eval 1 ≤ (n : ℝ) ^ 2 := by
      simpa [T_deriv_one_nat] using h
    have hm : (-p).derivative.eval 1 = - p.derivative.eval 1 := by simp
    rw [hm] at h'
    linarith
  rw [abs_le]
  constructor
  · linarith
  · exact h1

/-- The main unit-norm theorem: ‖p‖ ≤ 1, deg ≤ n ⇒ |p'| ≤ n² on [−1,1]. -/
lemma markov_unit_bound {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree ≤ n)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  intro x hx
  have hx1 : -1 ≤ x := hx.1
  have hx2 : x ≤ 1 := hx.2
  by_cases hn0 : n = 0
  · subst n
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by simpa using hdeg)
    rw [hpC]
    simp
  · have hn : 1 ≤ n := by omega
    by_cases h1 : x = 1
    · subst x
      exact endpoint_bound_one hdeg hbd
    by_cases hm1 : x = -1
    · subst x
      have hdegrefl : (refl p).natDegree ≤ n := by
        rw [refl_natDegree]
        exact hdeg
      have hb' := endpoint_bound_one (p := refl p) hdegrefl (refl_bound hbd)
      have hm : |(refl p).derivative.eval 1| = |p.derivative.eval (-1)| := by
        rw [refl_deriv_eval]
        simp
      simpa [hm] using hb'
    · have hx0 : -1 < x := by
        apply lt_of_le_of_ne hx1
        intro h
        exact hm1 h.symm
      have hx9 : x < 1 := by
        apply lt_of_le_of_ne hx2
        intro h
        exact h1 h
      by_cases hmiddle : |x| ≤ Real.cos (Real.pi / (2 * (n : ℝ)))
      · exact middle_region_bound hn hdeg hbd hx0 hx9 hmiddle
      · have hnot : Real.cos (Real.pi / (2 * (n : ℝ))) < |x| := by linarith
        by_cases hxpos : 0 ≤ x
        · have hxs : Real.cos (Real.pi / (2 * (n : ℝ))) ≤ x := by
            have : |x| = x := abs_of_nonneg hxpos
            rw [this] at hnot
            exact le_of_lt hnot
          exact endpoint_region_bound hn hdeg hbd hxs hx9
        · have hxneg : x < 0 := by linarith
          have hxs2 : x ≤ - Real.cos (Real.pi / (2 * (n : ℝ))) := by
            have : |x| = -x := abs_of_neg hxneg
            rw [this] at hnot
            linarith
          exact endpoint_region_bound_neg hn hdeg hbd hx0 hxs2



/-- P vanishes on [−1,1] with M=0 forcing P=0 -/
lemma zero_of_bound_zero {P : Polynomial ℝ} (hP : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → P.eval x = 0) :
    P = 0 := by
  classical
  refine Polynomial.eq_zero_of_infinite_isRoot P ?_
  -- the set of roots is infinite: contains range of an injective map into [−1,1]
  let f : ℕ → ℝ := fun m => (m : ℝ) / ((m : ℝ) + 1)
  have hf_inj : Function.Injective f := by
    intro a b hab
    unfold f at hab
    have hden : (a : ℝ) + 1 ≠ 0 := by positivity
    have hden' : (b : ℝ) + 1 ≠ 0 := by positivity
    have hcross : (a : ℝ) * ((b : ℝ) + 1) = (b : ℝ) * ((a : ℝ) + 1) := by
      field_simp [hden, hden'] at hab
      nlinarith
    have hlin : (a : ℝ) = (b : ℝ) := by nlinarith
    exact_mod_cast hlin
  have hrange : Set.range f ⊆ {x : ℝ | P.IsRoot x} := by
    intro x hx
    rcases hx with ⟨m, rfl⟩
    unfold f
    have hmem : (m : ℝ) / ((m : ℝ) + 1) ∈ Set.Icc (-1) 1 := by
      constructor
      · have hd : 0 ≤ (m : ℝ) / ((m : ℝ) + 1) := by positivity
        linarith
      · have hd : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_iff₀ (by positivity : 0 < (m : ℝ) + 1)]
          nlinarith
        linarith
    simpa [Polynomial.IsRoot] using hP ((m : ℝ) / ((m : ℝ) + 1)) hmem
  exact Set.Infinite.mono hrange (Set.infinite_range_of_injective hf_inj)

/-- **Markov's inequality** (general M): deg ≤ n, |P| ≤ M on [−1,1] ⇒ |P'| ≤ n²·M. -/
lemma markov_unit_general {P : ℝ[X]} {n : ℕ} (hdeg : P.natDegree ≤ n)
    {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |P.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    |P.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
  by_cases hM0 : M = 0
  · have hP : P = 0 := zero_of_bound_zero (fun y hy => by
        have habs := hbd y hy
        have hle : |P.eval y| ≤ 0 := by simpa [hM0] using habs
        have habs0 : |P.eval y| = 0 := le_antisymm hle (abs_nonneg _)
        exact abs_eq_zero.mp habs0)
    subst M
    simp [hP]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    let Q : ℝ[X] := Polynomial.C (M⁻¹) * P
    have hdegQ : Q.natDegree ≤ n := by
      unfold Q
      have hc : M⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hMpos)
      rw [Polynomial.natDegree_C_mul hc]
      exact hdeg
    have hbdQ : ∀ y : ℝ, y ∈ Set.Icc (-1) 1 → |Q.eval y| ≤ 1 := by
      intro y hy
      have habs := hbd y hy
      unfold Q
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      have hnonneg : 0 ≤ M⁻¹ := inv_nonneg.mpr hM
      rw [abs_mul, abs_of_nonneg hnonneg]
      have hmul : M⁻¹ * |P.eval y| ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left habs hnonneg
      have hmul2 : M⁻¹ * M = 1 := inv_mul_cancel₀ (ne_of_gt hMpos)
      rwa [hmul2] at hmul
    have hunit := markov_unit_bound (p := Q) hdegQ hbdQ x hx
    -- |Q'.eval x| ≤ n² : Q = C M⁻¹ * P: Q'.eval x = M⁻¹ · P'.eval x
    have hQ : Q.derivative.eval x = M⁻¹ * P.derivative.eval x := by
      unfold Q
      rw [Polynomial.derivative_C_mul]
      simp
    have hm : M⁻¹ * |P.derivative.eval x| = |Q.derivative.eval x| := by
      rw [hQ]
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hM)]
    have hmain : M⁻¹ * |P.derivative.eval x| ≤ (n : ℝ) ^ 2 := by
      rw [hm]
      exact hunit
    -- multiply by M: |P'| ≤ M·n² = n²·M
    have hmul := mul_le_mul_of_nonneg_left hmain hM
    -- M · (M⁻¹ · |P'|) = |P'|
    have hcancel : M * (M⁻¹ * |P.derivative.eval x|) = |P.derivative.eval x| := by
      field_simp [ne_of_gt hMpos]
    rw [hcancel] at hmul
    -- goal: |P'| ≤ n²·M : hmul : |P'| ≤ M·n² : ring commute
    nlinarith


end
end Markov2

namespace Submission.Markov

open Markov2


/-- **Classical Markov inequality on `[-1,1]`**: a degree-`≤ n` real polynomial
bounded in modulus by `M ≥ 0` has derivative bounded by `n²·M`. -/
lemma markov_unit {P : Polynomial ℝ} {n : ℕ} (hdeg : P.natDegree ≤ n)
    {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |P.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    |P.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
  exact Markov2.markov_unit_general hdeg hM hbd x hx

end Submission.Markov
