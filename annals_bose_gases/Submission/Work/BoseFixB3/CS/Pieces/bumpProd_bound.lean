import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Work.BoseFixB3.CS.Pieces.chiScale_iteratedFDeriv_le
import Submission.Work.BoseFixB3.CS.Pieces.uniform_idfb_nat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.bumpProd_bound`

The product `χ_ℓ(y) · χ_ℓ(y+z) = chiU ℓ 0 y · chiU ℓ 0 (y+z)` of two copies of the
scaled cubic bump is uniformly bounded, and so are all its iterated Fréchet
derivatives up to order `40`, with the scaling `ℓ^{-j}` in the `j`-th derivative.

Concretely we produce a single constant `M ≥ 0` with

* `|χ_ℓ(y) χ_ℓ(y+z)| ≤ M` for all `z`, `ℓ > 0` and `y`;
* `‖D^j (χ_ℓ(·) χ_ℓ(·+z)) y‖ ≤ M / ℓ^j` for all `j ≤ 40`.

The proof is three steps.

1. `uniform_idfb_nat`: a compactly supported smooth `f : E → ℝ` has uniformly
   bounded iterated derivatives, `‖D^k f x‖ ≤ G k` (`G k ≥ 0`).
2. `chiScale_iteratedFDeriv_le`: scaling `χ_ℓ = χ(ℓ⁻¹ • ·)` multiplies the norm of
   the `k`-th derivative by `(ℓ⁻¹)^k`, and the same bound holds for the translate
   `y ↦ χ_ℓ(y+z)`.
3. The multilinear product rule `norm_iteratedFDeriv_mul_le` bounds the `j`-th
   derivative of the product by `∑_{i≤j} C(j,i) ‖D^i χ_ℓ y‖ ‖D^{j-i} χ_ℓ(·+z) y‖
   ≤ (ℓ⁻¹)^j · chiProdV G j`, where
   `chiProdV G j = ∑_{i≤j} C(j,i) G i G (j-i) ≥ 0`.

The constant is `M := ∑_{k<41} chiProdV G k`, which dominates every
`chiProdV G j` for `j ≤ 40` (all terms being nonnegative).  The `j = 0` case of
`chiProdV` bounds the pointwise product, and in the derivative estimate we convert
`M / ℓ^j = M * (ℓ⁻¹)^j` with `div_eq_mul_inv` and `inv_pow`.
-/

noncomputable section
open scoped ContDiff

namespace Work.BoseFixB3.CS.Pieces

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The combinatorial constant `∑_{i ≤ j} C(j,i) G i G (j-i)` produced by the
multilinear product rule. -/
def chiProdV (G : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * G i * G (j - i)

/-- **The `j`-th derivative of the product bump**, bounded by `chiProdV G j`
times the scaling factor `(ℓ⁻¹)^j`. -/
lemma bumpProd_deriv_le (G : ℕ → ℝ)
    (hG : ∀ k (x : ℝ³), ‖iteratedFDeriv ℝ k Submission.BoseGases.chi x‖ ≤ G k)
    (z : ℝ³) (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (y : ℝ³) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ³ =>
        Submission.BoseGases.chiScale ℓ y * Submission.BoseGases.chiScale ℓ (y + z)) y‖
      ≤ chiProdV G j * (ℓ⁻¹) ^ j := by
  have hG0 : ∀ k, 0 ≤ G k := fun k => le_trans (norm_nonneg _) (hG k 0)
  have hw : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr (le_of_lt hℓ)
  obtain ⟨hscal, hsh⟩ := chiScale_iteratedFDeriv_le G hG ℓ hℓ
  have hu : ContDiff ℝ ∞ (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)
  have hv : ContDiff ℝ ∞ (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ (y + z)) :=
    hu.comp (contDiff_id.add contDiff_const)
  have hcast : ((j : ℕ∞ω)) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hstep : (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (Submission.BoseGases.chiScale ℓ) y‖ *
          ‖iteratedFDeriv ℝ (j - i)
            (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ (y + z)) y‖)
      ≤ ∑ i ∈ Finset.range (j + 1),
          (ℓ⁻¹) ^ j * ((j.choose i : ℝ) * G i * G (j - i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hb : ‖iteratedFDeriv ℝ i (Submission.BoseGases.chiScale ℓ) y‖ ≤ (ℓ⁻¹) ^ i * G i :=
      hscal i y
    have hc : ‖iteratedFDeriv ℝ (j - i)
        (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ (y + z)) y‖ ≤
          (ℓ⁻¹) ^ (j - i) * G (j - i) := hsh (j - i) z y
    have hci : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have hbc : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (Submission.BoseGases.chiScale ℓ) y‖ ≤
        (j.choose i : ℝ) * ((ℓ⁻¹) ^ i * G i) :=
      mul_le_mul_of_nonneg_left hb hci
    have hpos : 0 ≤ (j.choose i : ℝ) * ((ℓ⁻¹) ^ i * G i) :=
      mul_nonneg hci (mul_nonneg (pow_nonneg hw i) (hG0 i))
    have h2 := mul_le_mul hbc hc (norm_nonneg _) hpos
    have hpow : (ℓ⁻¹) ^ i * (ℓ⁻¹) ^ (j - i) = (ℓ⁻¹) ^ j := by
      rw [← pow_add]; congr 1; omega
    have hterm : (j.choose i : ℝ) * ((ℓ⁻¹) ^ i * G i) * ((ℓ⁻¹) ^ (j - i) * G (j - i))
        = (ℓ⁻¹) ^ j * ((j.choose i : ℝ) * G i * G (j - i)) := by
      rw [← hpow]; ring
    exact h2.trans (le_of_eq hterm)
  calc ‖iteratedFDeriv ℝ j (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y *
          Submission.BoseGases.chiScale ℓ (y + z)) y‖
      ≤ (∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (Submission.BoseGases.chiScale ℓ) y‖ *
            ‖iteratedFDeriv ℝ (j - i)
              (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ (y + z)) y‖) :=
        norm_iteratedFDeriv_mul_le hu hv y hcast
    _ ≤ (∑ i ∈ Finset.range (j + 1),
          (ℓ⁻¹) ^ j * ((j.choose i : ℝ) * G i * G (j - i))) := hstep
    _ = (ℓ⁻¹) ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * G i * G (j - i)) :=
        (Finset.mul_sum _ _ _).symm
    _ = chiProdV G j * (ℓ⁻¹) ^ j := by unfold chiProdV; ring

theorem bumpProd_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (z : EuclideanSpace ℝ (Fin 3)) (ℓ : ℝ), 0 < ℓ →
        (∀ y : EuclideanSpace ℝ (Fin 3),
            |Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)| ≤ M) ∧
        (∀ (j : ℕ), j ≤ 40 → ∀ y : EuclideanSpace ℝ (Fin 3),
            ‖iteratedFDeriv ℝ j
                (fun y : EuclideanSpace ℝ (Fin 3) =>
                  Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)) y‖
              ≤ M / ℓ ^ j) := by
  obtain ⟨G, hG0, hG⟩ := uniform_idfb_nat Submission.BoseGases.chi
      (fun k => contDiff_infty.mp Submission.BoseGases.chi_contDiff k)
      Submission.BoseGases.chi_hasCompactSupport
  have hV0 : ∀ k, 0 ≤ chiProdV G k := by
    intro k
    unfold chiProdV
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG0 i)) (hG0 (k - i)))
  refine ⟨∑ k ∈ Finset.range 41, chiProdV G k,
    Finset.sum_nonneg (fun k _ => hV0 k), ?_⟩
  intro z ℓ hℓ
  have hbody : ∀ y : ℝ³,
      Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z) =
        Submission.BoseGases.chiScale ℓ y * Submission.BoseGases.chiScale ℓ (y + z) := by
    intro y
    simp only [Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]
  have hfun : (fun y : ℝ³ =>
        Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)) =
      fun y : ℝ³ =>
        Submission.BoseGases.chiScale ℓ y * Submission.BoseGases.chiScale ℓ (y + z) := by
    funext y
    exact hbody y
  constructor
  · intro y
    rw [hbody y]
    have hb := bumpProd_deriv_le G hG z ℓ hℓ 0 y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] at hb
    exact hb.trans (Finset.single_le_sum (fun k _ => hV0 k)
      (Finset.mem_range.mpr (by norm_num)))
  · intro j hj y
    rw [hfun]
    have hb := bumpProd_deriv_le G hG z ℓ hℓ j y
    have hMle : chiProdV G j ≤ ∑ k ∈ Finset.range 41, chiProdV G k :=
      Finset.single_le_sum (fun k _ => hV0 k) (Finset.mem_range.mpr (by omega))
    rw [div_eq_mul_inv, ← inv_pow]
    exact hb.trans (mul_le_mul_of_nonneg_right hMle
      (pow_nonneg (inv_nonneg.mpr (le_of_lt hℓ)) j))

end Work.BoseFixB3.CS.Pieces
