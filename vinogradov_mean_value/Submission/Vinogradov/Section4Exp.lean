/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.FromDecLin
import Submission.Vinogradov.CurveLayer

/-!
# GLYZ §4: the exponent set of the linear decoupling

The first, design-independent layer of the exponent bootstrap of Guo–Li–Yung–Zorin-Kranich §4.
The decoupling exponent `η` of the paper is the infimum of the exponents for which the linear
`ℓ²`-decoupling holds with a constant `δ^{-η}`; in our dyadic normalisation (`δ = 1/N`, pieces of
length `1/N`) that is

  `linExpSet k = {e ≥ 0 | ∃ K > 0, ∀ N ≥ 1, DecLinScale k N 2 (ofReal (K N^e))}`,
  `etaLin k = sInf (linExpSet k)`.

The intersection with `[0,∞)` is harmless (the sharp exponent is `≥ 0`) and makes the set bounded
below, which is what the `sInf` API of `ℝ` needs (`csInf_le`, `csInf_lt_iff`).

* `bddBelow_linExpSet`, `linExpSet_nonempty` (via the trivial bound `curveDec_trivial`),
* `linExpSet_mono` (the exponent set is an up-set),
* `etaLin_le_of_mem`,
* **`exists_decLinScale_of_etaLin_nonpos`** — the passage from `η ≤ 0` to the ε-form of the
  decoupling theorem: for every `ε > 0` there is `K > 0` with `DecLinScale k N 2 (ofReal (K N^ε))`
  for every `N ≥ 1`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- **The exponent set of the linear `ℓ²`-decoupling** of the moment curve of degree `k`: the real
numbers `e ≥ 0` for which there is `K > 0` with
`DecLinScale k N 2 (K N^e)` for every level `N ≥ 1`.

Intersecting with `[0,∞)` is harmless (the sharp exponent is `≥ 0`) and it makes the set bounded
below, which is what the `sInf` API of `ℝ` needs. -/
def linExpSet (k : ℕ) : Set ℝ :=
  {e : ℝ | 0 ≤ e ∧ ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N →
    DecLinScale k N 2 (ENNReal.ofReal (K * (N : ℝ) ^ e))}

/-- **The decoupling exponent** of the moment curve of degree `k` (GLYZ's `η`). -/
noncomputable def etaLin (k : ℕ) : ℝ := sInf (linExpSet k)

lemma bddBelow_linExpSet (k : ℕ) : BddBelow (linExpSet k) :=
  ⟨0, fun e he => he.1⟩

/-- **The exponent set is an up-set** in the exponent. -/
lemma linExpSet_mono {k : ℕ} {e e' : ℝ} (he : e ∈ linExpSet k) (h : e ≤ e') :
    e' ∈ linExpSet k := by
  obtain ⟨he0, K, hK, hD⟩ := he
  refine ⟨le_trans he0 h, K, hK, fun N hN => ?_⟩
  refine DecLinScale_mono ?_ (hD N hN)
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (N : ℝ) ^ e ≤ (N : ℝ) ^ e' := Real.rpow_le_rpow_of_exponent_le h1 h
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 hK.le)

lemma one_half_mem_linExpSet (k : ℕ) (hk : 1 ≤ k) : ((1 : ℝ) / 2) ∈ linExpSet k := by
  refine ⟨by norm_num, 1, one_pos, fun N hN => ?_⟩
  have h := curveDec_trivial k hk (gammaDeriv k) N 2
  rw [curveDec_gammaDeriv_iff] at h
  refine DecLinScale_mono ?_ h
  rw [show (1 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ ((1 : ℝ) / 2) from one_mul _]
  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) (by norm_num)]
  exact le_of_eq (by rw [ENNReal.ofReal_natCast])

lemma linExpSet_nonempty (k : ℕ) (hk : 1 ≤ k) : (linExpSet k).Nonempty :=
  ⟨1 / 2, one_half_mem_linExpSet k hk⟩

lemma etaLin_le_of_mem {k : ℕ} {e : ℝ} (he : e ∈ linExpSet k) : etaLin k ≤ e :=
  csInf_le (bddBelow_linExpSet k) he

/-- **The passage from `η ≤ 0` to the ε-form of the decoupling theorem.** -/
theorem exists_decLinScale_of_etaLin_nonpos {k : ℕ} (hk : 1 ≤ k) (h : etaLin k ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N →
      DecLinScale k N 2 (ENNReal.ofReal (K * (N : ℝ) ^ ε)) := by
  have hlt : sInf (linExpSet k) < ε := lt_of_le_of_lt h hε
  obtain ⟨e, he, heε⟩ :=
    (csInf_lt_iff (bddBelow_linExpSet k) (linExpSet_nonempty k hk)).mp hlt
  obtain ⟨-, K, hK, hD⟩ := linExpSet_mono he heε.le
  exact ⟨K, hK, hD⟩


end Submission.Vinogradov
