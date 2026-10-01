import Mathlib
import Submission.Work.LinnikAreas.CIDefs

/-!
# Orthogonality of the class von Mangoldt sum

The class von Mangoldt sum `classSum a X` (the tent-weighted sum of `Λ(n)/n` over the `n ≤ X`
with `n ≡ a (mod q)`) is the inverse `φ(q)⁻¹`-twisted sum of the twisted character sums
`chiSum χ q X`:

`classSum a X = φ(q)⁻¹ · Σ_χ χ̄(a) · chiSum χ q X`   (`a` coprime to `q`),

which is precisely the classical orthogonality relation
`Σ_χ χ̄(a) χ(b) = φ(q)` if `b = a` and `0` otherwise, for `a` a unit of `ZMod q`
(Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`).

The formal content is:

* `classSum` is rewritten as `Σ_{n ≤ X} 1_{n ≡ a} · Λ(n)/n · h(log n / log q)`,
  and `chiSum χ q X` as `Σ_{n ≤ X} χ(n) · Λ(n)/n · h(log n / log q)` (the common weight is
  `classW q n`);
* `Finset.sum_comm` interchanges the sums over `χ` and over `n ≤ X`, so the inner sum becomes
  `Σ_χ χ̄(a) χ(n)`, evaluated by orthogonality;
* the twist `φ(q)⁻¹ · φ(q)` cancels.
-/

open DirichletCharacter Complex
open scoped BigOperators Classical
noncomputable section

namespace Work.LinnikAreas

/-- The common summand of `classSum` and `chiSum`: the tent-weighted `Λ(n)/n`
(so that `chiSum χ q X = Σ_{n ≤ X} χ(n) · classW q n`). -/
abbrev classW (q : ℕ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)) *
    ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)

/-- `Ioc 0 X = Icc 1 X` in `ℕ`, so that the index sets of `classSum` and `chiSum` agree. -/
lemma ioc_zero_eq_icc_one (X : ℕ) : Finset.Ioc 0 X = Finset.Icc 1 X := by
  ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-- `classSum` as a sum over `Icc 1 X` of the indicator of the class `a mod q` times the
common weight. -/
lemma classSum_eq_indicator_sum {q : ℕ} [NeZero q] (a X : ℕ) :
    classSum (q := q) a X = ∑ n ∈ Finset.Icc 1 X,
      (if (n : ZMod q) = (a : ZMod q) then (1 : ℂ) else 0) * classW q n := by
  rw [show classSum (q := q) a X = ∑ n ∈ Finset.Ioc 0 X,
      ((ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n : ℝ) : ℂ) *
        (((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) / (n : ℂ)) from rfl]
  rw [ioc_zero_eq_icc_one]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases h : (n : ZMod q) = (a : ZMod q)
  · simp only [h, if_true]
    ring
  · simp only [h, if_false]
    simp

/-- `chiSum` as a sum over `Icc 1 X` of `χ(n)` times the common weight. -/
lemma chiSum_eq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℕ) :
    chiSum χ q X = ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q) * classW q n := by
  rw [show chiSum χ q X = ∑ n ∈ Finset.Icc 1 X,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) *
        ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) from rfl]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- On a unit `aa` of `ZMod q`, the conjugate of a character value is the value at the
inverse: `χ̄(a) = χ(a⁻¹)`. -/
lemma star_char_apply_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {aa : ZMod q}
    (haa : IsUnit aa) : (starRingEnd ℂ) (χ aa) = χ aa⁻¹ := by
  rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, ZMod.mul_inv_of_unit aa haa, map_one]

/-- **Character orthogonality**, in the form used below: for `aa` a unit of `ZMod q` and any
`n`, the sum of `χ̄(aa) · χ(n)` over all Dirichlet characters mod `q` is `φ(q)` when `n ≡ aa`
and vanishes otherwise. -/
lemma sum_star_char_mul_char {q : ℕ} [NeZero q] (aa : ZMod q) (haa : IsUnit aa) (n : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ aa) * χ n
      = if n = aa then (q.totient : ℂ) else 0 := by
  have h : ∀ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ aa) = χ aa⁻¹ :=
    fun χ => star_char_apply_inv χ haa
  simp only [h]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ haa n]
  by_cases hn : n = aa
  · rw [if_pos hn, if_pos hn.symm]
  · rw [if_neg hn, if_neg (Ne.symm hn)]

theorem ClassSumOrthogonality {q : ℕ} [NeZero q] (a : ℕ) (ha : a.Coprime q) (X : ℕ) :
    Work.LinnikAreas.classSum (q := q) a X = ((q.totient : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * Work.LinnikAreas.chiSum χ q X := by
  have hφne : (q.totient : ℂ) ≠ 0 := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast h.ne'
  have haa : IsUnit ((a : ZMod q)) := isUnit_of_coprime ha
  have horth : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      (starRingEnd ℂ) (χ (a : ZMod q)) * χ (n : ZMod q)
        = if (n : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0 :=
    fun n => sum_star_char_mul_char (a : ZMod q) haa (n : ZMod q)
  have h1 := classSum_eq_indicator_sum (q := q) a X
  have h2 : ∀ χ : DirichletCharacter ℂ q,
      chiSum χ q X = ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q) * classW q n :=
    fun χ => chiSum_eq_sum χ X
  have h3 : ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * chiSum χ q X
      = ∑ n ∈ Finset.Icc 1 X,
          (if (n : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0) * classW q n := by
    calc ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * chiSum χ q X
        = ∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) *
            ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q) * classW q n := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [h2 χ]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Icc 1 X,
            (starRingEnd ℂ) (χ (a : ZMod q)) * (χ (n : ZMod q) * classW q n) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Icc 1 X,
            (starRingEnd ℂ) (χ (a : ZMod q)) * χ (n : ZMod q) * classW q n := by
          refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun n _ => ?_
          ring
      _ = ∑ n ∈ Finset.Icc 1 X, ∑ χ : DirichletCharacter ℂ q,
            (starRingEnd ℂ) (χ (a : ZMod q)) * χ (n : ZMod q) * classW q n :=
          Finset.sum_comm
      _ = ∑ n ∈ Finset.Icc 1 X,
            (∑ χ : DirichletCharacter ℂ q, (starRingEnd ℂ) (χ (a : ZMod q)) * χ (n : ZMod q))
              * classW q n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ n ∈ Finset.Icc 1 X,
            (if (n : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0) * classW q n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [horth n]
  have h4 : (q.totient : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 X,
        (if (n : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0) * classW q n)
      = ∑ n ∈ Finset.Icc 1 X,
        (if (n : ZMod q) = (a : ZMod q) then (1 : ℂ) else 0) * classW q n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : (n : ZMod q) = (a : ZMod q)
    · rw [if_pos h, if_pos h, ← mul_assoc, inv_mul_cancel₀ hφne, one_mul]
    · rw [if_neg h, if_neg h]
      ring
  calc classSum (q := q) a X
      = ∑ n ∈ Finset.Icc 1 X,
          (if (n : ZMod q) = (a : ZMod q) then (1 : ℂ) else 0) * classW q n := h1
    _ = (q.totient : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 X,
          (if (n : ZMod q) = (a : ZMod q) then (q.totient : ℂ) else 0) * classW q n) := h4.symm
    _ = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          (starRingEnd ℂ) (χ (a : ZMod q)) * chiSum χ q X := by rw [h3]

end Work.LinnikAreas
