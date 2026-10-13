import Mathlib
import Submission.Work.WilE9.Ift.OneShotDefs

set_option maxHeartbeats 1000000

namespace Work.WilE9.Ift.OneShot

open WilkiesDesign WilkiesDesign.E

/-! ## Degree of the single new equation of the one-shot construction

`oneShotBasic c F L = ⟨[z * Q^(2|L|) - P_L], []⟩` has

* `eqs = [oneShotEq c F L]`, `pos = []`, hence
  `(oneShotBasic c F L).deg = (oneShotEq c F L).totalDegree + 1`
  (because `Basic.deg` is the sum of `atomDeg = totalDegree + 1` over the atoms);

* `oneShotEq c F L = X z * (extend (jQ c F))^(2|L|) - extend (iftP c F 0 L)`, a difference of
  two products, so its total degree is at most the maximum of the total degrees of

  - `X z * (extend (jQ c F))^(2|L|)`, of degree `1 + 2|L| · deg Q`, and
  - `extend (iftP c F 0 L)`, of degree `deg P_L`,

  where `extend` is a `rename` along the injective `oneShotInj n m` and therefore preserves the
  total degree.

With `q = 1 + m` the number of equations and `D` a bound on `(F j).totalDegree`, the two
ingredients are bounded by `q * D` (the determinant `Q`, `Deg.jQ_totalDegree_le`) and by
`(q * D + 1) + |L| · (4 (q³+q²+q+1) (q * D + 1))` (`Deg.iftP_totalDegree_le`, the "sharp"
additive growth).  Adding the `+1` of `atomDeg` and replacing the outer `max` by the sum gives
the two-variable polynomial `oneShotDegPoly q` below. -/

/-- The two-variable degree polynomial of the one-shot construction, for a system of `q`
equations: a (deliberately generous) common upper bound for
`1 + 2 |L| (q D)`, `(q D + 1) + |L| (4 (q³+q²+q+1) (q D + 1))` and their sum. -/
noncomputable def oneShotDegPoly (q : ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.C 2
    + MvPolynomial.C 2 * MvPolynomial.X 1 * (MvPolynomial.C q * MvPolynomial.X 0)
    + (MvPolynomial.C q * MvPolynomial.X 0 + MvPolynomial.C 1)
    + MvPolynomial.X 1 *
        (MvPolynomial.C (4 * (q * q * q + q * q + q + 1)) *
          (MvPolynomial.C q * MvPolynomial.X 0 + MvPolynomial.C 1))

/-- Evaluation of `oneShotDegPoly`: the polynomial value at `(D, t)`. -/
theorem oneShotDegPoly_eval (q D t : ℕ) :
    MvPolynomial.eval ![D, t] (oneShotDegPoly q)
      = 2 + 2 * t * (q * D) + (q * D + 1)
        + t * (4 * (q * q * q + q * q + q + 1) * (q * D + 1)) := by
  simp [oneShotDegPoly]

/-- `EAPoly.extend` is a `rename` along `Sum.map e id`; for injective `e` it preserves the total
degree. -/
theorem extend_totalDegree {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (Q : EAPoly k r) :
    (Work.WilE8.EAPoly.extend e Q).totalDegree = Q.totalDegree := by
  rw [Work.WilE8.EAPoly.extend]
  exact Work.WilE8.Extend.totalDegree_rename_of_injective _
    (Sum.map_injective.mpr ⟨he, Function.injective_id⟩) Q

/-- `Q = det (∂F/∂y)` is bounded in degree by `q * D` when every equation has degree `≤ D`. -/
theorem jQ_totalDegree_le_of_bound {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (D : ℕ) (hF : ∀ j, (F j).totalDegree ≤ D) :
    (Work.WilE9.jQ c F).totalDegree ≤ q * D := by
  have hsum : ∑ j : Fin q, (F j).totalDegree ≤ q * D := by
    calc ∑ j : Fin q, (F j).totalDegree ≤ ∑ _j : Fin q, D := Finset.sum_le_sum (fun j _ => hF j)
      _ = q * D := by simp
  exact (Work.WilE9.Deg.jQ_totalDegree_le c F).trans hsum

/-- The implicit-derivative polynomial `P_L` is bounded in degree by
`(q D + 1) + |L| (4 (q³+q²+q+1) (q D + 1))` when every equation has degree `≤ D`. -/
theorem iftP_totalDegree_le_of_bound {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (l₀ : Fin q) (L : List (Fin n)) (D : ℕ)
    (hF : ∀ j, (F j).totalDegree ≤ D) :
    (Work.WilE9.iftP c F l₀ L).totalDegree ≤
      (q * D + 1) + L.length * (4 * (q * q * q + q * q + q + 1) * (q * D + 1)) := by
  have hsum : ∑ j : Fin q, (F j).totalDegree ≤ q * D := by
    calc ∑ j : Fin q, (F j).totalDegree ≤ ∑ _j : Fin q, D := Finset.sum_le_sum (fun j _ => hF j)
      _ = q * D := by simp
  refine (Work.WilE9.Deg.iftP_totalDegree_le c F l₀ L).trans ?_
  exact Nat.add_le_add (by omega)
    (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _
        (by omega : (∑ j : Fin q, (F j).totalDegree) + 1 ≤ q * D + 1)))

/-- The degree of the single new equation `z * Q^(2|L|) - P_L` of the one-shot construction is
bounded by a two-variable polynomial in `(D, |L|)`, where `D` bounds the total degrees of the
equations `F j`.  The polynomial depends only on the number `1 + m` of equations, not on the
chain, on the system `F` or on the order `L`: this is the "sharp" degree growth. -/
theorem oneShotBasic_deg_le (m : ℕ) :
    ∃ PolyB : MvPolynomial (Fin 2) ℕ, ∀ {n r : ℕ}
      (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
      (F : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r)
      (L : List (Fin n)) (D : ℕ),
      (∀ j : Fin (1 + m), (F j).totalDegree ≤ D) →
      (Work.WilE9.Ift.oneShotBasic c F L).deg ≤ MvPolynomial.eval ![D, L.length] PolyB := by
  refine ⟨oneShotDegPoly (1 + m), ?_⟩
  intro n r c F L D hF
  rw [oneShotDegPoly_eval]
  rw [show (Work.WilE9.Ift.oneShotBasic c F L).deg
        = (Work.WilE9.Ift.oneShotEq c F L).totalDegree + 1 from by
      simp [Work.WilE9.Ift.oneShotBasic, Basic.deg, atomDeg]]
  have hQext : (Work.WilE8.EAPoly.extend (oneShotInj n m) (Work.WilE9.jQ c F)).totalDegree ≤
      (1 + m) * D := by
    rw [extend_totalDegree (oneShotInj_injective n m)]
    exact jQ_totalDegree_le_of_bound c F D hF
  have hPext : (Work.WilE8.EAPoly.extend (oneShotInj n m)
        (Work.WilE9.iftP c F (0 : Fin (1 + m)) L)).totalDegree ≤
      ((1 + m) * D + 1) + L.length *
        (4 * ((1 + m) * (1 + m) * (1 + m) + (1 + m) * (1 + m) + (1 + m) + 1)
          * ((1 + m) * D + 1)) := by
    rw [extend_totalDegree (oneShotInj_injective n m)]
    exact iftP_totalDegree_le_of_bound c F (0 : Fin (1 + m)) L D hF
  set A : ℕ := 1 + 2 * L.length * ((1 + m) * D) with hA
  set B : ℕ := ((1 + m) * D + 1) + L.length *
        (4 * ((1 + m) * (1 + m) * (1 + m) + (1 + m) * (1 + m) + (1 + m) + 1)
          * ((1 + m) * D + 1)) with hB
  have hprod : (MvPolynomial.X (Sum.inl (oneShotNew n m)) *
        (Work.WilE8.EAPoly.extend (oneShotInj n m) (Work.WilE9.jQ c F)) ^
          (2 * L.length)).totalDegree ≤ A := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
    refine Nat.add_le_add_left ?_ 1
    exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hQext)
  have htot : (Work.WilE9.Ift.oneShotEq c F L).totalDegree ≤ max A B := by
    rw [Work.WilE9.Ift.oneShotEq]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max hprod hPext)
  rw [hA, hB] at htot
  omega

end Work.WilE9.Ift.OneShot
