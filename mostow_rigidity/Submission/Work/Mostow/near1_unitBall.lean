import Mathlib
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hlift_entry_le_cosh_one
import Submission.Work.Mostow.hdist_lt_of_cc_lt

/-!
# `near1_unitBall`: entrywise near-identity on `O(n,1)` gives a uniformly small displacement

If a matrix `A ∈ O(n,1)` is entrywise `q`-close to the identity (`Near1 A q`), then the hyperbolic
displacement `hdist v (A • v)` is small, *uniformly* over the hyperbolic unit ball
`{v | hdist 0 v ≤ 1}`.  This is the quantitative "continuity at the identity" of the action on
the unit ball, with an explicit modulus.

The argument is elementary and fully explicit.  Write `x = hlift v ∈ ℝ^{Fin n ⊕ Fin 1}` for the
hyperboloid point over `v`, and `M = mat A`.  For `q ≤ 1/2` the time–time entry of `M` is
positive, so `tsign A = 1` and by `Hyper.hlift_actO`

`hlift (actO A v) = M *ᵥ x`.

Hence, with `E = M - 1` and using `cc u w = -⟨hlift u, hlift w⟩` (`Hyper.cc_equiv`),

`cc v (actO A v) = -⟨x, M x⟩ = 1 - ⟨x, E x⟩`,

and since `hdist 0 v ≤ 1` forces `|x k| ≤ cosh 1` for every `k`, the entrywise bound
`|E k l| ≤ q` gives `|⟨x, E x⟩| ≤ q ((n+1) cosh 1)^2`.  Choosing `q` so that
`q ((n+1) cosh 1)^2 < (cosh η - 1)/2` therefore yields
`cosh (hdist v (A • v)) = cc v (actO A v) < cosh η`, i.e. `hdist v (A • v) < η`.
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow

noncomputable section

/-! ## Elementary Minkowski-form bookkeeping -/

private lemma near1_mink_add_right {n : ℕ} (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (y + z) = Hyper.mink x y + Hyper.mink x z := by
  unfold Hyper.mink
  rw [Matrix.mulVec_add, dotProduct_add]

/-- The Minkowski form is bounded by the paired `l¹` sum of the coordinates. -/
private lemma near1_abs_mink_le {n : ℕ} (x y : Fin n ⊕ Fin 1 → ℝ) :
    |Hyper.mink x y| ≤ ∑ k, |x k| * |y k| := by
  have habs : |x (Sum.inr 0) * y (Sum.inr 0)| = |x (Sum.inr 0)| * |y (Sum.inr 0)| :=
    abs_mul _ _
  rw [Hyper.mink_apply]
  have hsum : (∑ k : Fin n ⊕ Fin 1, |x k| * |y k|)
      = (∑ i : Fin n, |x (Sum.inl i)| * |y (Sum.inl i)|)
        + |x (Sum.inr 0)| * |y (Sum.inr 0)| := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_one]
  have h1 : |(∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i))|
      ≤ ∑ i : Fin n, |x (Sum.inl i)| * |y (Sum.inl i)| := by
    calc |∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)|
        ≤ ∑ i : Fin n, |x (Sum.inl i) * y (Sum.inl i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |x (Sum.inl i)| * |y (Sum.inl i)| := by simp only [abs_mul]
  have h2 : |(∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) - x (Sum.inr 0) * y (Sum.inr 0)|
      ≤ |(∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i))| + |x (Sum.inr 0) * y (Sum.inr 0)| := by
    rw [sub_eq_add_neg, ← abs_neg (x (Sum.inr 0) * y (Sum.inr 0))]
    exact abs_add_le _ _
  rw [hsum]
  linarith [h1, h2]

/-! ## The key estimate -/

/-- The key estimate of `near1_unitBall`: if `A` is entrywise `q`-close to the identity
(`q ≤ 1/2`) and `|hlift v k| ≤ X` for all `k`, then the cosh-kernel between `v` and `actO A v`
is at most `1 + q (((n : ℝ) + 1) X)^2`.  In particular the right-hand side is an explicit bound
for `cosh (hdist v (A • v))`. -/
lemma near1_cc_actO_le {n : ℕ} {A : O1 n} {v : E n} {q X : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 2) (hA : Near1 A q)
    (hX : 0 ≤ X) (hXv : ∀ k : Fin n ⊕ Fin 1, |hlift v k| ≤ X) :
    Hyper.cc v (actO A v) ≤ 1 + q * (((n : ℝ) + 1) * X) ^ 2 := by
  have hs : tsign A = 1 := by
    rw [tsign_eq_one_iff]
    have h := hA (Sum.inr 0) (Sum.inr 0)
    rw [dE_self] at h
    have h1 : -(1 / 2 : ℝ) ≤ mat A (Sum.inr 0) (Sum.inr 0) - 1 :=
      (abs_le.mp (le_trans h hq1)).1
    linarith
  set x : Fin n ⊕ Fin 1 → ℝ := hlift v with hx
  set E : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := mat A - 1 with hE
  have hsumX : (∑ k, |x k|) ≤ ((n : ℝ) + 1) * X := by
    calc (∑ k, |x k|) ≤ ∑ _k : Fin n ⊕ Fin 1, X := Finset.sum_le_sum fun k _ => hXv k
      _ = ((n : ℝ) + 1) * X := by
          rw [Finset.sum_const, Finset.card_univ, card_sum_fin, nsmul_eq_mul]
          push_cast
          ring
  have hEx : ∀ k, |Matrix.mulVec E x k| ≤ q * (((n : ℝ) + 1) * X) := by
    intro k
    rw [Matrix.mulVec, dotProduct]
    calc |∑ l, E k l * x l| ≤ ∑ l, |E k l * x l| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |E k l| * |x l| := by simp only [abs_mul]
      _ ≤ ∑ l, q * |x l| := by
            refine Finset.sum_le_sum fun l _ => ?_
            have hkl : |E k l| ≤ q := by
              rw [hE, sub_one_entry]
              exact hA k l
            exact mul_le_mul_of_nonneg_right hkl (abs_nonneg _)
      _ = q * (∑ l, |x l|) := by rw [Finset.mul_sum]
      _ ≤ q * (((n : ℝ) + 1) * X) := mul_le_mul_of_nonneg_left hsumX hq
  have hmink : |Hyper.mink x (Matrix.mulVec E x)| ≤ q * (((n : ℝ) + 1) * X) ^ 2 := by
    have hb := near1_abs_mink_le x (Matrix.mulVec E x)
    have hb2 : (∑ k, |x k| * |Matrix.mulVec E x k|)
        ≤ ∑ _k : Fin n ⊕ Fin 1, X * (q * (((n : ℝ) + 1) * X)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul (hXv k) (hEx k) (abs_nonneg _) hX
    have hb3 : (∑ _k : Fin n ⊕ Fin 1, X * (q * (((n : ℝ) + 1) * X)))
        = ((n : ℝ) + 1) * (X * (q * (((n : ℝ) + 1) * X))) := by
      rw [Finset.sum_const, Finset.card_univ, card_sum_fin, nsmul_eq_mul]
      push_cast
      ring
    linarith [hb, hb2, hb3]
  have hmat : Matrix.mulVec (mat A) x = Matrix.mulVec E x + Matrix.mulVec 1 x := by
    rw [show mat A = (mat A - 1) + 1 from by abel, Matrix.add_mulVec]
  have hdec : Hyper.mink x (Matrix.mulVec (mat A) x)
      = Hyper.mink x (Matrix.mulVec E x) + Hyper.mink x x := by
    rw [hmat, Matrix.one_mulVec, near1_mink_add_right]
  have hxx : Hyper.mink x x = -1 := by
    rw [hx]
    exact Hyper.mink_hlift_self v
  have hcc : Hyper.cc v (actO A v) = -Hyper.mink x (Matrix.mulVec (mat A) x) := by
    rw [Hyper.cc_equiv, Hyper.hlift_actO, hs, one_smul, ← hx]
  rw [hcc, hdec, hxx]
  linarith [hmink, neg_le_abs (Hyper.mink x (Matrix.mulVec E x))]

/-! ## The theorem -/

theorem near1_unitBall (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ q : ℝ, 0 < q ∧ ∀ (A : O1 n) (v : E n),
      Near1 A q → hdist (0 : E n) v ≤ 1 → hdist v ((A : PO n 1) • v) < η := by
  intro η hη
  set C : ℝ := ((n : ℝ) + 1) * Real.cosh 1 with hC
  have hC1 : 1 ≤ C := by
    rw [hC]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have h2 : 1 ≤ Real.cosh 1 := Real.one_le_cosh 1
    nlinarith [h1, h2]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hdpos : 0 < Real.cosh η - 1 := by
    have h := Real.one_lt_cosh.mpr (ne_of_gt hη)
    linarith
  set q : ℝ := min (1 / 2) ((Real.cosh η - 1) / (2 * C ^ 2)) with hq
  have hqpos : 0 < q := by
    rw [hq]
    exact lt_min (by norm_num) (div_pos hdpos (by positivity))
  refine ⟨q, hqpos, ?_⟩
  intro A v hnear hv
  have hq1 : q ≤ 1 / 2 := by rw [hq]; exact min_le_left _ _
  have hqle : q ≤ (Real.cosh η - 1) / (2 * C ^ 2) := by rw [hq]; exact min_le_right _ _
  have hqC : q * C ^ 2 ≤ (Real.cosh η - 1) / 2 := by
    have h1 : q * C ^ 2 ≤ ((Real.cosh η - 1) / (2 * C ^ 2)) * C ^ 2 :=
      mul_le_mul_of_nonneg_right hqle (by positivity)
    have h2 : ((Real.cosh η - 1) / (2 * C ^ 2)) * C ^ 2 = (Real.cosh η - 1) / 2 := by
      field_simp
    linarith [h1, h2]
  have hX : 0 ≤ Real.cosh 1 := le_of_lt (Real.cosh_pos 1)
  have hbound := near1_cc_actO_le (le_of_lt hqpos) hq1 hnear hX (hlift_entry_le_cosh_one hv)
  rw [hC] at hqC
  have hlt : Hyper.cc v (actO A v) < Real.cosh η := by
    linarith [hbound, hqC]
  have hd := hdist_lt_of_cc_lt hη hlt
  rw [hA.2.1 A v]
  exact hd

end

end Work.Mostow
