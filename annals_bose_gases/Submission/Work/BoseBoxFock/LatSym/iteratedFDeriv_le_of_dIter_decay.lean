import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.NormSymAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary lemmas for the operator-norm upgrade

The three ingredients of the proof of `iteratedFDeriv_le_of_dIter_decay` are isolated here:

* `single_sum_eq` — the expansion of a vector of `ℝ³` in the standard basis
  `EuclideanSpace.single k 1`;
* `expansion` and `opNorm_le_basis` — the purely multilinear-algebraic step: the operator norm of a
  continuous multilinear map on `Fin n → ℝ³` is bounded by `3 ^ n` times the maximum of its values
  on the tuples of basis vectors;
* `iteratedFDeriv_cast` and `dIter_ofFn` — the comparison of the iterated derivative along the
  explicit list `List.ofFn g` with `iteratedFDeriv ℝ n v p g`.
-/

/-- Expansion of a vector of `ℝ³` in the standard basis: `x = ∑ k, x k • single k 1`. -/
lemma single_sum_eq (x : E3) : x = ∑ k : Fin 3, (x k) • EuclideanSpace.single k (1 : ℝ) := by
  apply PiLp.ext
  intro j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, PiLp.ofLp_single, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun c => x.ofLp c)]
  simp

/-- Multilinear expansion of `m x` in the standard basis: `m x` is the sum over all choices of one
basis index per slot of the product of the corresponding coordinates times the value of `m` on the
corresponding tuple of basis vectors. -/
lemma expansion {n : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin n => E3) ℂ)
    (x : Fin n → E3) :
    m x = ∑ φ : Fin n → Fin 3, (∏ j, x j (φ j)) • m (fun j => EuclideanSpace.single (φ j) 1) := by
  conv_lhs => rw [show x = (fun j => ∑ k : Fin 3, (x j k) • EuclideanSpace.single k 1)
      from funext (fun j => single_sum_eq (x j))]
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  rw [ContinuousMultilinearMap.map_smul_univ]

/-- Operator-norm bound from the values on the tuples of standard basis vectors. -/
lemma opNorm_le_basis {n : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin n => E3) ℂ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ φ : Fin n → Fin 3, ‖m (fun j => EuclideanSpace.single (φ j) 1)‖ ≤ B) :
    ‖m‖ ≤ 3 ^ n * B := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (pow_nonneg (by norm_num) n) hB) (fun x => ?_)
  rw [expansion m x]
  calc ‖∑ φ : Fin n → Fin 3, (∏ j, x j (φ j)) • m (fun j => EuclideanSpace.single (φ j) 1)‖
      ≤ ∑ φ : Fin n → Fin 3, ‖(∏ j, x j (φ j)) • m (fun j => EuclideanSpace.single (φ j) 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _φ : Fin n → Fin 3, (∏ j, ‖x j‖) * B := by
        refine Finset.sum_le_sum (fun φ _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
        refine mul_le_mul ?_ (h φ) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => norm_nonneg _))
        refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => ?_)
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x j) (φ j)
    _ = 3 ^ n * B * ∏ j, ‖x j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-- The iterated derivative of order `m = n` on a tuple transported along `Fin.cast`. -/
lemma iteratedFDeriv_cast {m n : ℕ} (h : m = n) (v : E3 → ℂ) (p : E3) (g : Fin n → E3) :
    iteratedFDeriv ℝ m v p (fun i : Fin m => g (Fin.cast h i)) = iteratedFDeriv ℝ n v p g := by
  cases h
  rfl

/-- `dIter` along the list `List.ofFn g` is the `n`-th iterated derivative evaluated on `g`. -/
lemma dIter_ofFn (v : E3 → ℂ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (n : ℕ) (g : Fin n → E3) (p : E3) :
    Work.BoseBoxFock.dIter v (List.ofFn g) p = iteratedFDeriv ℝ n v p g := by
  rw [Work.BoseBoxFock.dIter_eq_iteratedFDeriv v hv]
  have hfun : (fun i : Fin (List.ofFn g).length => (List.ofFn g).get i)
      = fun i => g (Fin.cast (List.length_ofFn) i) := by
    funext i
    rw [List.get_ofFn]
  rw [hfun]
  exact iteratedFDeriv_cast (List.length_ofFn) v p g

/-- **Weighted decay of the full iterated derivatives from the decay of the directional ones.**

`Work.BoseBoxFock.dIter v L p` is the iterated directional derivative of `v` along the list `L`
at `p` (head of the list = outermost derivative), and
`Work.BoseBoxFock.dIter_eq_iteratedFDeriv` says `dIter v L p = iteratedFDeriv ℝ L.length v p (L.get)`.
So the hypothesis bounds the `i`-th iterated derivative of `v` at `p` evaluated on *every* tuple of
directions with a constant depending on the tuple; the conclusion upgrades this to a bound on the
operator norm of `iteratedFDeriv ℝ i v p`, uniform in the tuple, for `i ≤ 6`.

Route: `dIter v L p = iteratedFDeriv ℝ L.length v p (fun j => L.get j)`, so choosing the finitely
many lists `L_φ = List.ofFn (fun j : Fin i => EuclideanSpace.single (φ j) 1)`, `φ : Fin i → Fin 3`,
`i ≤ 6`, and taking the maximum `K` of the constants supplied by the hypothesis gives
`‖iteratedFDeriv ℝ i v p (fun j => single (φ j) 1)‖ ≤ K (1+‖p‖)⁻⁷` for every *basis* tuple. Then
expand a general tuple `x`: `x j = ∑ k, (x j).ofLp k • EuclideanSpace.single k 1` (prove this with
`WithLp.ofLp_injective`, `WithLp.ofLp_sum`, `PiLp.single_apply`), use
`ContinuousMultilinearMap.map_sum` (`(f fun i => ∑ j, g i j) = ∑ r, f fun i => g i (r i)`) and
`ContinuousMultilinearMap.map_smul_univ` to write
`m x = ∑ φ, (∏ j, (x j).ofLp (φ j)) • m (fun j => single (φ j) 1)`, bound
`|(x j).ofLp (φ j)| ≤ ‖x j‖` (`EuclideanSpace.basisFun_inner`, `EuclideanSpace.norm_single`,
`abs_real_inner_le_norm`), and conclude with `ContinuousMultilinearMap.opNorm_le_bound`: the
constant is `3^i · K ≤ 3^6 · K` for `i ≤ 6`. -/
theorem iteratedFDeriv_le_of_dIter_decay {v : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvdec : ∀ L : List (EuclideanSpace ℝ (Fin 3)), L.length ≤ 6 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : EuclideanSpace ℝ (Fin 3),
        ‖Work.BoseBoxFock.dIter v L p‖ ≤ C * (1 + ‖p‖) ^ (-7 : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : ℕ), i ≤ 6 → ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ i v p‖ ≤ K * (1 + ‖p‖) ^ (-7 : ℝ) := by
  classical
  -- the finitely many constants supplied by the hypothesis
  choose C hC using fun s : (Σ i : Fin 7, Fin i → Fin 3) =>
    hvdec (List.ofFn (fun j : Fin s.1.val => EuclideanSpace.single (s.2 j) 1))
      (by simp only [List.length_ofFn]; omega)
  -- their sum dominates each of them (all are nonnegative)
  let K0 : ℝ := ∑ s : (Σ i : Fin 7, Fin i → Fin 3), C s
  have hK0 : 0 ≤ K0 := Finset.sum_nonneg (fun s _ => (hC s).1)
  have hle : ∀ s : (Σ i : Fin 7, Fin i → Fin 3), C s ≤ K0 := fun s =>
    Finset.single_le_sum (fun t _ => (hC t).1) (Finset.mem_univ s)
  refine ⟨3 ^ 6 * K0, by positivity, ?_⟩
  intro i hi p
  have hr : 0 ≤ (1 + ‖p‖) ^ (-7 : ℝ) := Real.rpow_nonneg (by positivity) _
  -- the bound on every tuple of standard basis vectors
  have hbasis : ∀ φ : Fin i → Fin 3,
      ‖iteratedFDeriv ℝ i v p (fun j => EuclideanSpace.single (φ j) 1)‖
        ≤ K0 * (1 + ‖p‖) ^ (-7 : ℝ) := by
    intro φ
    have h1 : iteratedFDeriv ℝ i v p (fun j => EuclideanSpace.single (φ j) 1)
        = Work.BoseBoxFock.dIter v
            (List.ofFn (fun j : Fin i => EuclideanSpace.single (φ j) 1)) p :=
      (dIter_ofFn v hv i (fun j => EuclideanSpace.single (φ j) 1) p).symm
    rw [h1]
    have h2 := (hC ⟨⟨i, by omega⟩, φ⟩).2 p
    exact h2.trans (mul_le_mul_of_nonneg_right (hle _) hr)
  -- upgrade to the operator norm, then to the uniform constant `3 ^ 6 * K0`
  have hmain := opNorm_le_basis (B := K0 * (1 + ‖p‖) ^ (-7 : ℝ))
    (iteratedFDeriv ℝ i v p) (mul_nonneg hK0 hr) hbasis
  refine hmain.trans ?_
  calc (3 : ℝ) ^ i * (K0 * (1 + ‖p‖) ^ (-7 : ℝ))
      ≤ 3 ^ 6 * (K0 * (1 + ‖p‖) ^ (-7 : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg hK0 hr)
    _ = (3 : ℝ) ^ 6 * K0 * (1 + ‖p‖) ^ (-7 : ℝ) := by ring

end Work.BoseBoxFock.LatSym
