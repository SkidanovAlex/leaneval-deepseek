/-
  `Work.WilC4aP.tschirnhausen_reduce`: the Tschirnhausen (translation) normalisation used at
  the start of the complex Puiseux development.

  Given a monic polynomial `P` with holomorphic coefficients at `0`, of degree `m ≥ 2`, whose
  fibre at `0` is a pure `m`-th power `(X - C α) ^ m`, we produce an analytic translation
  `d` such that `P' := P.comp (X + C d)` has fibre `X ^ m` at `0`, and additionally the
  coefficient of `X ^ (m-1)` of `P'` vanishes.

  The two requirements force `d` : the coefficient of `X ^ (m-1)` in `P.comp (X + C d)` is
  `m * d + P.coeff (m-1)` (binomial expansion), so `d` must be the function
  `z ↦ -(P.coeff (m-1) z) / m`.  That this `d` also satisfies `d 0 = α` is *automatic*:
  comparing coefficients of `X ^ (m-1)` in `Pz P 0 = (X - C α) ^ m` gives `(P.coeff (m-1)) 0 =
  -m * α`.
-/
import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators Topology

namespace Work.WilC4aP

open Polynomial

/-! ## The coefficient of `X ^ (m-1)` after a translation

Everything here is elementary polynomial algebra over a general commutative semiring. -/

/-- Explicit formula for the coefficients of `P.comp (X + C c)`: expanding `(X + C c) ^ n` by
the binomial theorem, the coefficient of `X ^ k` in `(X + C c) ^ n` is `c ^ (n - k) * (n choose k)`,
and the substitution is a finite sum over the support of `P`. -/
private lemma coeff_comp_X_add_C_sum {R : Type*} [Semiring R] (p : R[X]) (c : R) (k : ℕ) :
    (p.comp (X + C c)).coeff k
      = ∑ n ∈ p.support, p.coeff n * (c ^ (n - k) * ((n.choose k : ℕ) : R)) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum, Polynomial.sum_def]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]

/-- The sum over `range (m+1)` of a sequence vanishing below `m-1` is the sum of its last two
terms. -/
private lemma sum_range_succ_sub_one {R : Type*} [AddCommMonoid R] {m : ℕ} (hm : 0 < m)
    (f : ℕ → R) (hf : ∀ n, n < m - 1 → f n = 0) :
    ∑ x ∈ Finset.range (m + 1), f x = f (m - 1) + f m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hf' : ∀ n, n < j → f n = 0 := fun n hn => hf n (by omega)
  have hgoal : (j + 1) - 1 = j := by omega
  rw [hgoal, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero (fun x hx => hf' x (Finset.mem_range.mp hx))]
  simp

private lemma choose_pred_self {m : ℕ} (hm : 0 < m) : m.choose (m - 1) = m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp [Nat.choose_succ_self_right]

/-- **Tschirnhausen coefficient identity.**  If `p` is monic of degree `m > 0` over a
commutative semiring, the coefficient of `X ^ (m-1)` in `p.comp (X + C c)` is
`p.coeff (m-1) + c * m`. -/
private lemma coeff_comp_X_add_C_sub_one {R : Type*} [CommSemiring R] {p : R[X]} {m : ℕ}
    (hmon : p.Monic) (hdeg : p.natDegree = m) (hm : 0 < m) (c : R) :
    (p.comp (X + C c)).coeff (m - 1) = p.coeff (m - 1) + c * (m : R) := by
  set f : ℕ → R := fun n => p.coeff n * (c ^ (n - (m - 1)) * ((n.choose (m - 1) : ℕ) : R))
    with hfdef
  have hsupp : p.support ⊆ Finset.range (m + 1) := by
    intro n hn
    rw [Finset.mem_range, ← hdeg]
    exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp n hn)
  have hside : ∀ x ∈ Finset.range (m + 1), x ∉ p.support → f x = 0 := by
    intro x _ hx
    simp [hfdef, Polynomial.notMem_support_iff.mp hx]
  have hF1 : f (m - 1) = p.coeff (m - 1) := by
    simp [hfdef]
  have hF2 : f m = c * (m : R) := by
    have hm1 : m - (m - 1) = 1 := by omega
    have hcm : p.coeff m = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
    simp [hfdef, hm1, choose_pred_self hm, hcm]
  have hsmall : ∀ n, n < m - 1 → f n = 0 := by
    intro n hn
    simp [hfdef, Nat.choose_eq_zero_of_lt hn]
  rw [coeff_comp_X_add_C_sum p c (m - 1), Finset.sum_subset hsupp hside,
    sum_range_succ_sub_one hm f hsmall, hF1, hF2]

/-! ## Holomorphy of the coefficients after a translation -/

/-- Substituting `Y ↦ Y + ζ` into a polynomial with holomorphic coefficients preserves
holomorphy of the coefficients, provided `ζ` is holomorphic at `0`. -/
private lemma holCoeffs_comp_X_add_C {P : Polynomial (ℂ → ℂ)} {ζ : ℂ → ℂ}
    (hP : HolCoeffs P 0) (hζ : AnalyticAt ℂ ζ 0) :
    HolCoeffs (P.comp (X + C ζ)) 0 := by
  intro k
  rw [coeff_comp_X_add_C_sum]
  refine Finset.analyticAt_sum _ fun n _ => ?_
  have h2 : AnalyticAt ℂ (((n.choose k : ℕ) : ℂ → ℂ)) 0 :=
    analyticAt_const (v := ((n.choose k : ℕ) : ℂ)) (x := (0 : ℂ))
  exact (hP n).mul ((hζ.pow (n - k)).mul h2)

/-- Coefficients of a fibre of `P` are the values of the coefficients of `P`. -/
private lemma Pz_coeff_apply (P : Polynomial (ℂ → ℂ)) (z : ℂ) (k : ℕ) :
    (Pz P z).coeff k = (P.coeff k) z := by
  simp [Pz, Polynomial.coeff_map]

/-! ## The Tschirnhausen reduction -/

lemma tschirnhausen_reduce {m : ℕ} (hm : 2 ≤ m) (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (hdeg : P.natDegree = m) (hhol : HolCoeffs P 0) (α : ℂ)
    (h0 : Pz P 0 = (Polynomial.X - Polynomial.C α) ^ m) :
    ∃ (d : ℂ → ℂ) (P' : Polynomial (ℂ → ℂ)), AnalyticAt ℂ d 0 ∧
      P' = P.comp (Polynomial.X + Polynomial.C d) ∧
      P'.Monic ∧ P'.natDegree = m ∧ HolCoeffs P' 0 ∧ Pz P' 0 = Polynomial.X ^ m ∧
      P'.coeff (m - 1) = 0 := by
  have hmpos : 0 < m := by omega
  have hm0 : (m : ℂ) ≠ 0 := by
    intro hc
    have h : (m : ℂ) = ((0 : ℕ) : ℂ) := by simpa using hc
    exact (by omega : m ≠ 0) (Nat.cast_injective h)
  -- the (forced) translation
  set d : ℂ → ℂ := fun z => (-(P.coeff (m - 1) z)) * (m : ℂ)⁻¹ with hd
  have hdan : AnalyticAt ℂ d 0 := by
    rw [hd]
    exact ((hhol (m - 1)).neg).mul (analyticAt_const (v := (m : ℂ)⁻¹))
  -- the coefficient of `X ^ (m-1)` in the fibre at `0`
  have hcoeff0 : (P.coeff (m - 1)) 0 = -((m : ℂ) * α) := by
    have hc := congrArg (fun q : ℂ[X] => q.coeff (m - 1)) h0
    have h1 : (Pz P 0).coeff (m - 1) = (P.coeff (m - 1)) 0 := Pz_coeff_apply P 0 (m - 1)
    have h2 : (((Polynomial.X : ℂ[X]) - Polynomial.C α) ^ m).coeff (m - 1) = -((m : ℂ) * α) := by
      have hX : ((Polynomial.X : ℂ[X]) - Polynomial.C α) = Polynomial.X + Polynomial.C (-α) := by
        rw [sub_eq_add_neg, Polynomial.C_neg]
      rw [hX, Polynomial.coeff_X_add_C_pow]
      have hm1 : m - (m - 1) = 1 := by omega
      rw [hm1, choose_pred_self hmpos, pow_one]
      ring
    rw [h1, h2] at hc
    exact hc
  have hd0 : d 0 = α := by
    have h1 : d 0 = (-(P.coeff (m - 1) 0)) * (m : ℂ)⁻¹ := by simp [hd]
    rw [h1, hcoeff0, neg_neg, mul_assoc, mul_comm α (m : ℂ)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hm0, one_mul]
  -- the reduction
  have hred : Pz (P.comp (Polynomial.X + Polynomial.C d)) 0 = Polynomial.X ^ m := by
    rw [Pz_comp_X_add_C, h0, hd0]
    have hX : (((Polynomial.X : ℂ[X]) - Polynomial.C α)).comp
        (Polynomial.X + Polynomial.C α) = Polynomial.X := by
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
      simp
    rw [Polynomial.pow_comp, hX]
  have hmon' : (P.comp (Polynomial.X + Polynomial.C d)).Monic := hmon.comp_X_add_C d
  have hdeg' : (P.comp (Polynomial.X + Polynomial.C d)).natDegree = m := by
    rw [← natDegree_Pz hmon' 0, hred, Polynomial.natDegree_X_pow]
  have hhol' : HolCoeffs (P.comp (Polynomial.X + Polynomial.C d)) 0 :=
    holCoeffs_comp_X_add_C hhol hdan
  have hczero : (P.comp (Polynomial.X + Polynomial.C d)).coeff (m - 1) = 0 := by
    funext z
    change ((P.comp (Polynomial.X + Polynomial.C d)).coeff (m - 1)) z = (0 : ℂ)
    rw [← Pz_coeff_apply (P.comp (Polynomial.X + Polynomial.C d)) z (m - 1)]
    rw [Pz_comp_X_add_C,
      coeff_comp_X_add_C_sub_one (monic_Pz hmon z)
        (by rw [natDegree_Pz hmon z, hdeg]) hmpos (d z)]
    have hdle : (d z) * (m : ℂ) = -(P.coeff (m - 1) z) := by
      have h1 : d z = (-(P.coeff (m - 1) z)) * (m : ℂ)⁻¹ := by simp [hd]
      rw [h1, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
    rw [Pz_coeff_apply, hdle, add_neg_cancel]
  exact ⟨d, P.comp (Polynomial.X + Polynomial.C d), hdan, rfl, hmon', hdeg', hhol', hred, hczero⟩

end Work.WilC4aP
