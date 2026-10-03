import Mathlib
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red5.window_T1_le
import Submission.Work.FITop4.Red5.window_sharp_count
import Submission.Work.FITop4.Red5.isPrimitive_of_sqfree_primary
import Submission.Work.FIArea2.hits_card_le
import Submission.Work.FIRed6Axis.nearMass_tau_sum_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Helper lemmas -/

lemma pcCond_of_cfVal_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ} {z : GaussianInt}
    (h : Work.FITop4.Red5.cfVal Pa φ q p z ≠ 0) : Work.FITop4.Red5.pcCond Pa φ z := by
  by_contra hc
  exact h (by rw [Work.FITop4.Red5.cfVal, Work.FITop4.Red5.pcInd, if_neg hc, zero_mul])

lemma squarefree_of_cfVal_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ} {z : GaussianInt}
    (h : Work.FITop4.Red5.cfVal Pa φ q p z ≠ 0) : Squarefree (Work.FIPlan.gnorm z) := by
  have hc := pcCond_of_cfVal_ne_zero h
  have hprod : (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
      * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
      * Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)) ≠ 0 := by
    intro h0
    exact h (by rw [Work.FITop4.Red5.cfVal, Work.FITop4.Red5.pcInd, if_pos hc, one_mul, h0])
  have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ) ≠ 0 := fun h0 =>
    hprod (by rw [h0]; ring)
  exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (by
    intro h0; exact hmu (by rw [h0]; norm_num))

/-- Reordering a four-fold sum, moving the last index out front. -/
lemma sum4_perm {ι₂ ι₃ ι₄ ι₅ : Type*} [DecidableEq ι₂] [DecidableEq ι₃] [DecidableEq ι₄]
    [DecidableEq ι₅]
    (t : Finset ι₂) (r : Finset ι₃) (u : Finset ι₅) (v : Finset ι₄)
    (f : ι₂ → ι₃ → ι₅ → ι₄ → ℝ) :
    (∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u, ∑ z ∈ v, f i k w z)
      = ∑ z ∈ v, ∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u, f i k w z := by
  symm
  calc ∑ z ∈ v, ∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u, f i k w z
      = ∑ i ∈ t, ∑ z ∈ v, ∑ k ∈ r, ∑ w ∈ u, f i k w z := Finset.sum_comm
    _ = ∑ i ∈ t, ∑ k ∈ r, ∑ z ∈ v, ∑ w ∈ u, f i k w z := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u, ∑ z ∈ v, f i k w z := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- The five-fold reordering + factorisation of a product summand. -/
lemma sum5_swap_factor {ι₁ ι₂ ι₃ ι₄ ι₅ : Type*} [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    [DecidableEq ι₄] [DecidableEq ι₅]
    (s : Finset ι₁) (t : Finset ι₂) (r : Finset ι₃) (v : Finset ι₄) (u : ι₁ → Finset ι₅)
    (c : ι₂ → ι₃ → ι₄ → ℝ) (Z : ι₅ → ι₄ → ℝ) :
    (∑ m ∈ s, ∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u m, ∑ z ∈ v, c i k z * Z w z)
      = ∑ z ∈ v, (∑ i ∈ t, ∑ k ∈ r, c i k z) * (∑ m ∈ s, ∑ w ∈ u m, Z w z) := by
  have h1 : ∀ m ∈ s, (∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u m, ∑ z ∈ v, c i k z * Z w z)
      = ∑ z ∈ v, ∑ i ∈ t, ∑ k ∈ r, ∑ w ∈ u m, c i k z * Z w z :=
    fun m _ => sum4_perm t r (u m) v (fun i k w z => c i k z * Z w z)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  conv_lhs => simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-! ## Two elementary pieces, proved locally (the delegated versions stalled) -/

lemma nearAxis_geom_absorb {c : ℝ} (hc : 0 < c) {A N n : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N) (hNn : N ≤ n)
    (hnN : n ≤ 2 * N) (hNA : (N : ℝ) ≤ (A : ℝ)) :
    c * ((A : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(1 : ℝ) / 4)
        + ((A : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 4))
      ≤ 3 * c * (A : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hAnn : (0 : ℝ) ≤ (A : ℝ) := le_of_lt hApos
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hNn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnN' : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hnN
  -- (1) the first term
  have ht1 : (n : ℝ) ^ (-(1 : ℝ) / 4) ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos hNpos hNn' (by norm_num)
  have hterm1 : (A : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(1 : ℝ) / 4)
      ≤ (A : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left ht1 (Real.rpow_nonneg hAnn _)
  -- (2) the second term
  set X : ℝ := (A : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4) with hX
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hX4 : X ^ 4 = (A : ℝ) ^ 3 * (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [hX, mul_pow]
    congr 1
    · rw [← Real.rpow_natCast ((A : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul hAnn]
      norm_num
    · rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 : ℝ) / 4)) 4, ← Real.rpow_mul hNnn]
      norm_num
  have hbig : 16 * (A : ℝ) ^ 3 * (N : ℝ) ^ (-(1 : ℝ)) * (N : ℝ) = 16 * (A : ℝ) ^ 3 := by
    rw [Real.rpow_neg_one]
    field_simp
  have hkey : (A : ℝ) * (n : ℝ) * (N : ℝ) ≤ 16 * (A : ℝ) ^ 3 := by
    have h1 : (A : ℝ) * (n : ℝ) * (N : ℝ) ≤ (A : ℝ) * (2 * (N : ℝ)) * (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hNnn
      exact mul_le_mul_of_nonneg_left hnN' hAnn
    have h2 : (A : ℝ) * (2 * (N : ℝ)) * (N : ℝ) = 2 * (A : ℝ) * (N : ℝ) ^ 2 := by ring
    have h3 : (N : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hNnn hNA 2
      simpa using this
    have h4 : 2 * (A : ℝ) * (N : ℝ) ^ 2 ≤ 2 * (A : ℝ) * (A : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 * (A : ℝ) * (A : ℝ) ^ 2 ≤ 16 * (A : ℝ) ^ 3 := by nlinarith [hApos]
    linarith [h1, h2 ▸ le_refl ((A : ℝ) * (2 * (N : ℝ)) * (N : ℝ)), h4, h5]
  have hbase : (A : ℝ) * (n : ℝ) ≤ (2 * X) ^ 4 := by
    have h16 : (2 * X) ^ 4 = 16 * (A : ℝ) ^ 3 * (N : ℝ) ^ (-(1 : ℝ)) := by
      rw [mul_pow, hX4]; ring
    rw [h16]
    exact le_of_mul_le_mul_right (by rw [hbig]; exact hkey) hNpos
  have hterm2 : ((A : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 4) ≤ 2 * X := by
    calc ((A : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ ((2 * X) ^ 4) ^ ((1 : ℝ) / 4) := by
          apply Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = 2 * X := by
          rw [← Real.rpow_natCast (2 * X) 4, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * X)]
          norm_num
  have hmain : (A : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(1 : ℝ) / 4)
      + ((A : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 4) ≤ 3 * X := by
    rw [hX] at hterm2 ⊢
    linarith [hterm1, hterm2]
  calc c * ((A : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ (-(1 : ℝ) / 4)
        + ((A : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 4))
      ≤ c * (3 * X) := mul_le_mul_of_nonneg_left hmain (le_of_lt hc)
    _ = 3 * c * (A : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4) := by rw [hX]; ring

lemma nearAxis_coeff_mass {K K' : ℕ} (N : ℕ) (θ : ℝ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (S : Finset (Fin K')) (z : GaussianInt)
    (hN : 1 ≤ N) (ha : ∀ i, (N : ℝ) ≤ a i) (hPaN : ∀ i k, (Pa i k).N = a i)
    (hp0 : ∀ i u, 0 ≤ p i u) (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (hpsum : ∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1)
    (hq0 : ∀ k α, 0 ≤ q k α)
    (hang : ∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1)
    (hz : z ∈ Work.FITop4.Red5.primAnn (2 * N)) :
    (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|)
      ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  set n : ℕ := Work.FIPlan.gnorm z with hn
  set α : ℝ := Complex.arg z.toComplex with hαdef
  have hmem := Iff.mp (Work.FITop4.Red5.mem_primAnn_iff' (R := 2 * N) (z := z)) hz
  obtain ⟨-, hgn1, hgn2N, hprim⟩ := hmem
  have hn1 : 1 ≤ n := by rw [hn]; exact hgn1
  have hn2N : n ≤ 2 * N := by rw [hn]; exact hgn2N
  have hnle' : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn2N
  have hαlo : -Real.pi ≤ α := le_of_lt (Complex.neg_pi_lt_arg z.toComplex)
  have hαhi : α ≤ Real.pi := Complex.arg_le_pi z.toComplex
  by_cases hcase : (N : ℝ) < (n : ℝ)
  · -- main case
    have hP : (∑ i, p i (n : ℝ)) ≤ 1 := hpsum (n : ℝ) hcase hnle'
    have hQ : (∑ k ∈ S, q k (α - φ k)) ≤ 1 := by
      rw [← hang α hαlo hαhi]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun k _ _ => hq0 k (α - φ k))
    have hP0 : 0 ≤ ∑ i, p i (n : ℝ) := Finset.sum_nonneg fun i _ => hp0 i _
    have hQ0 : 0 ≤ ∑ k ∈ S, q k (α - φ k) :=
      Finset.sum_nonneg fun k _ => hq0 k (α - φ k)
    -- the pointwise bound
    have hpt : ∀ i : Fin K, ∀ k ∈ S,
        |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|
          ≤ (p i (n : ℝ) * q k (α - φ k)) * (((n.divisors.card : ℕ)) : ℝ) := by
      intro i k _
      rw [Work.FITop4.Red5.abs_cfVal (Pa i k) (φ k) (q k) (p i) z (hq0 k _) (hp0 i _)]
      have hpc : Work.FITop4.Red5.pcInd (Pa i k) (φ k) z ≤ 1 :=
        Work.FITop4.Red5.pcInd_one_le _ _ _
      have hpc0 : 0 ≤ Work.FITop4.Red5.pcInd (Pa i k) (φ k) z :=
        Work.FITop4.Red5.pcInd_nonneg _ _ _
      have hgn : (Work.FIPlan.gnorm z) = n := hn.symm
      have hpp : p i (Work.FIPlan.gnorm z) = p i (n : ℝ) := by rw [hgn]
      have hqq : q k (Complex.arg z.toComplex - φ k) = q k (α - φ k) := by rw [hαdef]
      have hmm : |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          = |(ArithmeticFunction.moebius n : ℝ)| := by rw [hgn]
      have hgg : |Work.FIPlan.gammaTrunc (Pa i k).C (Work.FIPlan.gnorm z)|
          = |Work.FIPlan.gammaTrunc (Pa i k).C n| := by rw [hgn]
      rw [hpp, hqq, hmm, hgg]
      have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := n)
        exact_mod_cast this
      have hga : |Work.FIPlan.gammaTrunc (Pa i k).C n| ≤ (((n.divisors.card : ℕ)) : ℝ) :=
        Work.FITop3.abs_gammaTrunc_le _ _
      have hqp : 0 ≤ q k (α - φ k) * p i (n : ℝ) := mul_nonneg (hq0 k _) (hp0 i _)
      have hmu0 : 0 ≤ |(ArithmeticFunction.moebius n : ℝ)| := abs_nonneg _
      have hga0 : 0 ≤ |Work.FIPlan.gammaTrunc (Pa i k).C n| := abs_nonneg _
      have hTn0 : 0 ≤ (((n.divisors.card : ℕ)) : ℝ) := Nat.cast_nonneg _
      calc Work.FITop4.Red5.pcInd (Pa i k) (φ k) z
            * (q k (α - φ k) * p i (n : ℝ) * |(ArithmeticFunction.moebius n : ℝ)|
                * |Work.FIPlan.gammaTrunc (Pa i k).C n|)
          ≤ 1 * (q k (α - φ k) * p i (n : ℝ) * |(ArithmeticFunction.moebius n : ℝ)|
                * |Work.FIPlan.gammaTrunc (Pa i k).C n|) :=
            mul_le_mul_of_nonneg_right hpc (by positivity)
        _ = (q k (α - φ k) * p i (n : ℝ)) * (|(ArithmeticFunction.moebius n : ℝ)|
                * |Work.FIPlan.gammaTrunc (Pa i k).C n|) := by ring
        _ ≤ (q k (α - φ k) * p i (n : ℝ)) * (1 * (((n.divisors.card : ℕ)) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hqp
            exact mul_le_mul hmu hga hga0 (by norm_num)
        _ = (p i (n : ℝ) * q k (α - φ k)) * (((n.divisors.card : ℕ)) : ℝ) := by ring
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k hk => hpt i k hk) ?_
    have hfact : (∑ i, ∑ k ∈ S, (p i (n : ℝ) * q k (α - φ k)) * (((n.divisors.card : ℕ)) : ℝ))
        = (∑ i, p i (n : ℝ)) * (∑ k ∈ S, q k (α - φ k)) * (((n.divisors.card : ℕ)) : ℝ) := by
      have h : ∀ i : Fin K, (∑ k ∈ S, (p i (n : ℝ) * q k (α - φ k))
            * (((n.divisors.card : ℕ)) : ℝ))
          = p i (n : ℝ) * (∑ k ∈ S, q k (α - φ k)) * (((n.divisors.card : ℕ)) : ℝ) := by
        intro i
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i _ => h i)]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [hfact]
    have hTn0 : 0 ≤ (((n.divisors.card : ℕ)) : ℝ) := Nat.cast_nonneg _
    calc (∑ i, p i (n : ℝ)) * (∑ k ∈ S, q k (α - φ k)) * (((n.divisors.card : ℕ)) : ℝ)
        ≤ 1 * 1 * (((n.divisors.card : ℕ)) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hTn0
          exact mul_le_mul hP hQ hQ0 zero_le_one
      _ = (((n.divisors.card : ℕ)) : ℝ) := by ring
  · -- degenerate case: `n ≤ N`, all coefficients vanish
    have hnleN : (n : ℝ) ≤ (N : ℝ) := le_of_not_gt hcase
    have hzero : (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      have hcc : Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z = 0 := by
        have hnc : ¬ Work.FITop4.Red5.pcCond (Pa i k) (φ k) z := by
          intro hc
          have hbox : Work.FITop4.InPolarBox (Pa i k) (φ k) z := hc.1
          have h1 := hbox.2.1
          rw [hPaN i k] at h1
          have h2 : (Work.FIPlan.gnorm z : ℝ) = (n : ℝ) := by rw [hn]
          rw [h2] at h1
          linarith [ha i, hnleN]
        rw [Work.FITop4.Red5.cfVal, Work.FITop4.Red5.pcInd, if_neg hnc, zero_mul]
      rw [hcc, abs_zero]
    rw [hzero]
    exact Nat.cast_nonneg _


/-- **The (5.16) trivial bound for the near cells, from the mass bound** (`NearAxisBound` from
`NearMassBound`; unfold both Props from `Submission/Work/FIRed6Axis/Statement.lean`).

Route.  (i) `‖Σ_z β_z Z(Re wz)‖ ≤ Σ_z |β_z| Z(Re wz)` (as `Z ≥ 0`), and the `badInd` summand is the
same with a factor `≤ 2`, so the LHS of `NearAxisBound` is at most
`3·Σ_{m,i,k∈S,w,z} |pieceCoeff …| Z(Re wz)` after dropping the "active-`i`" filter (a superset).
(ii) Swap the finite sums so that each `z ∈ primAnn (2N)` carries
`Σ_{m ∈ (Mn,2Mn]} Σ_{w ∈ wSph m} Z(Re wz) = Σ_{w ∈ annM (Pa i k)} Z(Re wz)`
(`Work.FITop4.Red5.fiber_sum_annM`), and bound it by `C(Mn)^{3/4}|z|^{-1/2}`: either directly with
`Work.FITop4.Red5.disk_per_c_bound` (`Z(b) = #{c : ℤ // c² = b}`; `|Re wz| ≤ |w||z| ≤ √(2Mn)√(gnorm z)`
bounds the number of `c`'s by `≤ 4(2Mn·gnorm z)^{1/4}`, and each line `cForm · z = c²` meets the disc
`gnorm w ≤ 2Mn` in `≤ 2√(2Mn/gnorm z)+1`, with coprimality of `z.re, z.im` from
`Squarefree (gnorm z)`), or by `Work.FITop4.Red5.sum_Zint_annM_prim_le`.
(iii) For a nonvanishing `pieceCoeff`, `|β_{i,k,z}| ≤ p_i(|z|²)·q_k(arg z - φ_k)·τ(|z|²)`, so
`Σ_{i}Σ_{k∈S}|β_{i,k,z}| ≤ (Σ_i p_i(|z|²))·(Σ_{k∈S} q_k(arg z - φ_k))·τ(|z|²) ≤ τ(|z|²)` using
`hpsup`/`hpsum` (with `N < |z|² ≤ 2N`), `hqsup`/`hang`/`hq0` (`S ⊆ univ`), `|μ| ≤ 1` and
`|γ(n;C)| ≤ τ(n)` (`Work.FITop3.abs_gammaTrunc_le`); the hypothesis `hfarS` forces `nearArg (4ϑ) z`,
and every nonvanishing point has squarefree norm (the Möbius factor of `pieceCoeff`).
(iv) Apply `h : NearMassBound` to `T := (primAnn (2N)).filter (fun z => ∃ i k ∈ S,
pieceCoeff (Pa i k) (φ k) (q k) (p i) z ≠ 0)` and multiply the constants, using
`gnorm z ≤ 2N ≤ 2Mn` (from `(N:ℝ) ≤ (Mn:ℝ)`). -/
theorem nearAxisBound_of_mass (h : Work.FIRed6Axis.NearMassBound) :
    Work.FIRed6Axis.NearAxisBound := by
  obtain ⟨Cmass, hCpos, hmass⟩ := h
  obtain ⟨cw, hcwpos, hwsc⟩ := Work.FITop4.Red5.window_sharp_count
  refine ⟨9 * cw * Cmass, by positivity, ?_⟩
  intro x N Pz Mn Ccoe τ θ ϑ K K' a p φ q Pa S
  intro hMn hN hθ0 hθ1 hϑ0 hϑ1 h4πθ hNM ha hPaN hp0 hpsup hpsum hq0 hqsup hang hfarS
  set Win : Finset ℕ := Finset.Icc (Mn + 1) (2 * Mn) with hWin
  set Sz : Finset GaussianInt := Work.FITop4.Red5.primAnn (2 * N) with hSz
  set T : Finset GaussianInt := Sz.filter (fun z => ∃ i : Fin K, ∃ k : Fin K',
      k ∈ S ∧ Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z ≠ 0) with hT
  set G : GaussianInt → ℝ := (fun z => ∑ m ∈ Win, ∑ w ∈ Work.FITop4.Red5.wSph m,
      (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) with hGdef
  have hGnn : ∀ z : GaussianInt, 0 ≤ G z := by
    intro z
    rw [hGdef]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun w _ =>
      Work.FITop4.Red5.Zint_nonneg (Work.FIPlan.cForm w z)
  have hswap :
      (∑ m ∈ Win, ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m, ∑ z ∈ Sz,
          |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        = ∑ z ∈ Sz,
            (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z := by
    rw [hGdef]
    exact sum5_swap_factor Win Finset.univ S Sz Work.FITop4.Red5.wSph
      (fun i k z => |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|)
      (fun w z => (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
  have hzero : ∀ z ∈ Sz, z ∉ T →
      (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z = 0 := by
    intro z hz hzT
    have hsum0 : (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k hk => ?_
      have hc0 : Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z = 0 := by
        by_contra hne
        exact hzT (by
          rw [hT]
          exact Finset.mem_filter.mpr ⟨hz, i, k, hk, hne⟩)
      rw [hc0, abs_zero]
    rw [hsum0, zero_mul]
  have hD1 :
      (∑ z ∈ Sz, (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z)
        = ∑ z ∈ T,
            (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  have hD2 :
      (∑ z ∈ T, (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z)
        ≤ ∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) * G z := by
    refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right ?_ (hGnn z)
    have hzSz : z ∈ Sz := (Finset.mem_filter.mp (hT ▸ hz)).1
    exact nearAxis_coeff_mass N θ a p φ q Pa S z hN ha hPaN hp0 hpsup hpsum hq0 hang
      hzSz
  have hGz : ∀ z ∈ T, G z ≤ 3 * cw * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4) := by
    intro z hz
    have hz' := hT ▸ hz
    have hzSz : z ∈ Sz := (Finset.mem_filter.mp hz').1
    obtain ⟨i₀, k₀, hk₀, hcz⟩ := (Finset.mem_filter.mp hz').2
    have hpc : Work.FITop4.Red5.pcCond (Pa i₀ k₀) (φ k₀) z := pcCond_of_cfVal_ne_zero hcz
    have hbox : Work.FITop4.InPolarBox (Pa i₀ k₀) (φ k₀) z := hpc.1
    have hsq : Squarefree (Work.FIPlan.gnorm z) := squarefree_of_cfVal_ne_zero hcz
    have hmem := Iff.mp (Work.FITop4.Red5.mem_primAnn_iff' (R := 2 * N) (z := z)) hzSz
    obtain ⟨-, hgn1, hgn2N, hprimz⟩ := hmem
    have hprim : Work.FIPlan.IsPrimitive z :=
      Work.FITop4.Red5.isPrimitive_of_sqfree_primary hsq hprimz
    have hnlt : (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
      have h1 := hbox.2.1
      rw [hPaN i₀ k₀] at h1
      linarith [ha i₀]
    have hNn : N ≤ Work.FIPlan.gnorm z := by exact_mod_cast le_of_lt hnlt
    have hGle := hwsc Mn z hMn hprim hgn1
    rw [← hWin] at hGle
    have hGle' : G z ≤ cw * ((Mn : ℝ) ^ ((3 : ℝ) / 4) * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4)
        + ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) := by
      rw [hGdef]
      exact hGle
    exact hGle'.trans (nearAxis_geom_absorb (c := cw) hcwpos hMn hN hNn hgn2N hNM)
  have hmass' : (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ Cmass * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
            + (N : ℝ) ^ ((2 : ℝ) / 3) + 1) * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ) := by
    refine nearMass_tau_sum_le (Cmass := Cmass) (N := N) (ϑ := ϑ) hmass hN hϑ0 hϑ1 T ?_
    intro z hz
    have hz' := hT ▸ hz
    have hzSz : z ∈ Sz := (Finset.mem_filter.mp hz').1
    obtain ⟨i₀, k₀, hk₀, hcz⟩ := (Finset.mem_filter.mp hz').2
    have hpc : Work.FITop4.Red5.pcCond (Pa i₀ k₀) (φ k₀) z := pcCond_of_cfVal_ne_zero hcz
    have hbox : Work.FITop4.InPolarBox (Pa i₀ k₀) (φ k₀) z := hpc.1
    have hsq : Squarefree (Work.FIPlan.gnorm z) := squarefree_of_cfVal_ne_zero hcz
    have hnlt : (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
      have h1 := hbox.2.1
      rw [hPaN i₀ k₀] at h1
      linarith [ha i₀]
    exact ⟨hzSz, by exact_mod_cast hnlt, hsq, hfarS k₀ hk₀ i₀ z hbox⟩
  calc
    (∑ m ∈ Win, ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m,
        (‖∑ z ∈ Sz, Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
              * Work.FITop3.Zc w z‖
          + ∑ z ∈ Sz, 2 * Work.FITop4.Red5.badInd m x τ (Work.FIPlan.gnorm z)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                  * Work.FITop3.Zc w z‖))
        ≤ (∑ m ∈ Win, ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m, 3 * ∑ z ∈ Sz, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z| * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun w _ => ?_
          have h1 : ‖∑ z ∈ Sz, Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                * Work.FITop3.Zc w z‖
              ≤ ∑ z ∈ Sz, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
            rw [Work.FITop4.Red5.norm_pieceCoeff_mul_Zc]
          have h2 : (∑ z ∈ Sz, 2 * Work.FITop4.Red5.badInd m x τ (Work.FIPlan.gnorm z)
                * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                    * Work.FITop3.Zc w z‖)
              ≤ 2 * ∑ z ∈ Sz, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun z _ => ?_
            rw [Work.FITop4.Red5.norm_pieceCoeff_mul_Zc]
            have hb1 := Work.FITop4.Red5.badInd_one_le m x τ (Work.FIPlan.gnorm z)
            have hb0 := Work.FITop4.Red5.badInd_nonneg m x τ (Work.FIPlan.gnorm z)
            have hZ := Work.FITop4.Red5.Zint_nonneg (Work.FIPlan.cForm w z)
            have hcf := abs_nonneg (Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z)
            have hX : (0 : ℝ) ≤ |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := mul_nonneg hcf hZ
            nlinarith [mul_le_mul_of_nonneg_left hb1 hX]
          linarith [h1, h2]
    _ = 3 * (∑ m ∈ Win, ∑ i, ∑ k ∈ S, ∑ w ∈ Work.FITop4.Red5.wSph m, ∑ z ∈ Sz,
              |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
          simp only [← Finset.mul_sum]
    _ = 3 * (∑ z ∈ Sz,
            (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z) := by
          rw [hswap]
    _ = 3 * (∑ z ∈ T,
            (∑ i, ∑ k ∈ S, |Work.FITop4.Red5.cfVal (Pa i k) (φ k) (q k) (p i) z|) * G z) := by
          rw [hD1]
    _ ≤ 3 * (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) * G z) := by
          linarith [hD2]
    _ ≤ 3 * ((∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
            * (3 * cw * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4))) := by
          have h := mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hGz z hz)
              (by positivity : (0 : ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)))
            (by norm_num : (0 : ℝ) ≤ 3)
          rw [← Finset.sum_mul] at h
          linarith [h]
    _ ≤ 3 * ((Cmass * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
              + (N : ℝ) ^ ((2 : ℝ) / 3) + 1) * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ))
            * (3 * cw * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4))) := by
          have h := mul_le_mul_of_nonneg_right hmass'
            (by positivity : (0 : ℝ) ≤ 3 * cw * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4))
          linarith [h]
    _ = (9 * cw * Cmass) * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ (-(1 : ℝ) / 4)
          * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
              + (N : ℝ) ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ) := by
          ring

end

end Work.FIRed6Axis
