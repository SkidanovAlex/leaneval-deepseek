/-
# The clamped variation exhausts the free variation (area A8)

`Work.KMTAreas.A8.varPart r a` is the free variation part of the challenge's variational norm:
the supremum, over every `J : ℕ` and every monotone `N : ℕ → ℕ`, of the `ℓ^r`-norm of the
increments of `a` along the chain `N 0, N 1, …, N J`.  The clamped quantity
`Work.KMTAreas.varK r K a` computes the same supremum but over chains living in the finite set
`{0, …, K}` with at most `K` increments.

The point of this lemma is that the clamping loses nothing:

  `varPart r a ≤ ⨆ K, ENNReal.ofReal (varK r K a)`,

i.e. the free variation is dominated by the sup of the clamped ones.  (The reverse inequality is
`Work.KMTAreas.A8.varK_le_varPart`; together they give `varPart r a = ⨆ K, ofReal (varK r K a)`.)

The proof is short because `Chain K` places no restriction tying the number of increments to the
indices: a chain is a pair `(J, w)` with `J ≤ K` and `w : Fin (J+1) → Fin (K+1)` monotone, with
*no* strictness requirement on `w`.  Hence a free chain `(J, N)` is clamped simply by taking

  `M := max J (N J)`,

so that `J ≤ M` (the length fits) and `N i ≤ N J ≤ M` for all `i ≤ J` (the values fit); the map
`i ↦ ⟨N i, ·⟩ : Fin (J+1) → Fin (M+1)` is monotone and reproduces the free chain verbatim.  No
compression of repeated values is needed, because repeated values contribute the increment `0`.
-/
import Mathlib
import Submission.Work.KMTAreas.A8.vNormK_defs

namespace Work.KMTAreas.A8

open scoped BigOperators ENNReal NNReal

theorem varPart_le_iSup_varK (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    Work.KMTAreas.A8.varPart r a ≤ ⨆ K, ENNReal.ofReal (Work.KMTAreas.varK r K a) := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  set M : ℕ := max J (N J) with hM
  have hJM : J < M + 1 := by
    rw [hM]
    have : J ≤ max J (N J) := le_max_left _ _
    omega
  have hwle : ∀ i : Fin (J + 1), N i < M + 1 := by
    intro i
    rw [hM]
    have : N ↑i ≤ max J (N J) := le_trans (hN (Nat.lt_succ_iff.mp i.2)) (le_max_right _ _)
    omega
  have hwmono : Monotone (fun i : Fin (J + 1) => (⟨N i, hwle i⟩ : Fin (M + 1))) := by
    intro i j hij
    exact hN (by simpa only [Fin.le_def] using hij)
  let p : Chain M := ⟨⟨J, hJM⟩, ⟨fun i => ⟨N i, hwle i⟩, hwmono⟩⟩
  have hsup : (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      ≤ Work.KMTAreas.varK r M a := by
    have h1 := Finset.le_sup' (s := (Finset.univ : Finset (Chain M)))
      (f := fun q : Chain M =>
        (∑ i : Fin q.1.1, ‖a (q.2.1 i.succ) - a (q.2.1 i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)))
      (b := p) (Finset.mem_univ p)
    have h2 : (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ ^ (r : ℝ))
        = ∑ i : Fin p.1.1, ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ) := by
      refine Finset.sum_congr ?_ fun i _ => ?_
      · rfl
      · simp only [p, Fin.val_succ, Fin.val_castSucc]
    calc (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))
        = (∑ i : Fin p.1.1,
            ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
          rw [h2]
      _ ≤ Work.KMTAreas.varK r M a := h1
  calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (N (i + 1)) - a (N i))‖
      = (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ofReal_norm_toLp_eq_sum hr _
    _ = ENNReal.ofReal
          ((∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))) := by
        rw [← ofReal_norm_toLp_eq_sum hr (fun i : Fin J => a (N (i + 1)) - a (N i)),
          norm_toLp_eq_sum_rpow hr]
    _ ≤ ENNReal.ofReal (Work.KMTAreas.varK r M a) := ENNReal.ofReal_le_ofReal hsup
    _ ≤ ⨆ K, ENNReal.ofReal (Work.KMTAreas.varK r K a) :=
        le_iSup (fun K => ENNReal.ofReal (Work.KMTAreas.varK r K a)) M

end Work.KMTAreas.A8
