import Mathlib
import Submission.Subspace.RealRank.Reindex
import Submission.Subspace.RealRank.Box
import Submission.Subspace.RankDescReal
import Submission.Subspace.RealRank.RealComplex

/-!
# The maximal-rank case of the real rank descent

If, for infinitely many solutions `x`, the space `V_x = approxSpace L c ‖x‖` is a hyperplane
(`finrank = N - 1`), then the maximal-rank finiteness theorem
(`Submission.Subspace.maximal_rank_finiteness_reindex`) shows that the spaces `V_x` take only
finitely many values; each such value is a proper subspace containing the corresponding `x`, and
this contradicts general position.

The only bookkeeping is the normalisation of the exponents: replacing `c` by `c / (1 + s)` with
`s ≥ max (c i) - 1` makes all exponents `≤ 1` while leaving the boxes unchanged, since
`box (c, Q) = box (c / (1+s), Q ^ (1+s))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N : ℕ}

lemma boxT_toC (M : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) (Q t : ℝ) :
    boxT (toC M) c Q t = {y : Fin N → ℤ | ∀ i, |∑ k, M i k * (y k : ℝ)| ≤ t * Q ^ (c i)} := by
  ext y
  simp only [boxT, Set.mem_ofPred_eq]
  exact forall_congr' fun i => by rw [norm_toC_apply]

/-- **Rescaling the exponents.** -/
lemma approxBox_rpow_div (L : Fin N → Fin N → ℂ) (c : Fin N → ℝ) {s Q : ℝ} (hs : 0 < s)
    (hQ : 0 < Q) :
    approxBox L c Q = approxBox L (fun i => c i / s) (Q ^ s) := by
  ext y
  simp only [approxBox, Set.mem_ofPred_eq]
  exact forall_congr' fun i => by
    rw [← Real.rpow_mul hQ.le, mul_div_cancel₀ (c i) (ne_of_gt hs)]

private lemma exists_norm_le_of_rpow_lt {Q₀ : ℝ} (hQ₀1 : 1 ≤ Q₀) {s : ℝ} (hs : 1 ≤ s) :
    ∃ R : ℝ, ∀ x : Fin N → ℤ, ‖x‖ ^ s < Q₀ → ‖x‖ ≤ R := by
  refine ⟨max 1 Q₀, fun x hx => ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 : 1 ≤ ‖x‖ := le_trans (le_max_left _ _) hcon.le
  have h2 : Q₀ ≤ ‖x‖ := le_trans (le_max_right _ _) hcon.le
  have h3 : ‖x‖ ^ (1:ℝ) ≤ ‖x‖ ^ s := Real.rpow_le_rpow_of_exponent_le h1 hs
  rw [Real.rpow_one] at h3
  linarith

/-- **The maximal-rank case.**  If infinitely many solutions have `V_x` of dimension `N-1`, then
general position is violated. -/
theorem maxCase_false (hN : 2 ≤ N) (Mr : Matrix (Fin N) (Fin N) ℝ) (hMr : Mr.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (Mr i j))
    (c : Fin N → ℝ) (hc : ∑ i, c i < 0)
    {Y : Set (Fin N → ℤ)} (hgp : GenPos Y)
    (hb : ∀ x ∈ Y, ∀ i, ‖∑ k, toC Mr i k * (x k : ℂ)‖ ≤ ‖x‖ ^ (c i))
    (hmax : {x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = N - 1}.Infinite) :
    False := by
  classical
  -- ## normalisation of the exponents
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  set s : ℝ := max 0 ((Finset.univ : Finset (Fin N)).sup' hne c - 1) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact le_max_left 0 _
  have hs1 : 0 < 1 + s := by linarith
  set c' : Fin N → ℝ := fun i => c i / (1 + s) with hc'def
  have hc'1 : ∀ i, c' i ≤ 1 := by
    intro i
    have h2 : c i ≤ (Finset.univ : Finset (Fin N)).sup' hne c :=
      Finset.le_sup' (s := (Finset.univ : Finset (Fin N))) (f := c) (Finset.mem_univ i)
    have h1 : c i - 1 ≤ s := by
      rw [hsdef]
      exact le_trans (by linarith) (le_max_right _ _)
    rw [hc'def, div_le_one hs1]
    linarith
  have hc'sum : ∑ i, c' i < 0 := by
    rw [hc'def, ← Finset.sum_div]
    exact div_neg_of_neg_of_pos hc hs1
  -- ## the complex matrix
  have hdetC : (Matrix.of (toC Mr)).det ≠ 0 := by
    intro h0
    have h1 : (Matrix.of (toC Mr)).det = ((Mr.det : ℝ) : ℂ) := by
      rw [show Matrix.of (toC Mr) = (algebraMap ℝ ℂ).mapMatrix Mr from rfl]
      exact (RingHom.map_det (algebraMap ℝ ℂ) Mr).symm
    exact hMr (Complex.ofReal_eq_zero.mp (by rw [← h1]; exact h0))
  have halgC : ∀ i j, IsAlgebraic ℚ ((toC Mr) i j) := fun i j =>
    IsAlgebraic.algebraMap (halg i j)
  -- ## maximal-rank finiteness
  obtain ⟨Q₀, hQ₀1, S, hSfin, hS⟩ :=
    maximal_rank_finiteness_reindex (toC Mr) hdetC halgC c' hc'1 hc'sum
  -- ## the general-position transfer
  have hgp' := Submission.Subspace.genPos_image Y hgp
  -- ## the subfamily at large scale
  set Z : Set (Fin N → ℤ) := {x | x ∈ Y ∧ Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = N - 1
    ∧ Q₀ ≤ ‖x‖ ^ (1 + s)} with hZdef
  have hZinf : Z.Infinite := by
    have hsmall : ({x : Fin N → ℤ | ‖x‖ ^ (1 + s) < Q₀}).Finite := by
      obtain ⟨R, hR⟩ := exists_norm_le_of_rpow_lt (N := N) hQ₀1 (s := 1 + s) (by linarith)
      exact (Commons.Analysis.Normed.finite_bounded_int_vectors R).subset fun x hx => hR x hx
    have hsub : {x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = N - 1} ⊆
        Z ∪ {x : Fin N → ℤ | ‖x‖ ^ (1 + s) < Q₀} := by
      intro x hx
      by_cases h : Q₀ ≤ ‖x‖ ^ (1 + s)
      · exact Or.inl ⟨hx.1, hx.2, h⟩
      · exact Or.inr (lt_of_not_ge h)
    by_contra hcon
    rw [Set.not_infinite] at hcon
    exact hmax ((hcon.union hsmall).subset hsub)
  have hZinf' : (intCastVec '' Z).Infinite := hZinf.image intCastVec_injective.injOn
  -- ## the cover by proper subspaces
  refine Commons.LinearAlgebra.GeneralPosition.not_finite_cover_of_genPos
    (K := ℚ) (V := Fin N → ℚ)
    (fun T' hT' hcard => hgp' T' (fun v hv => Set.image_mono (fun x hx => hx.1) (hT' hv)) hcard)
    (hZinf.image intCastVec_injective.injOn)
    ⟨hSfin.toFinset.filter (fun V => V ≠ ⊤), ?_, ?_⟩
  · intro W hW
    exact (Finset.mem_filter.mp hW).2
  · rintro v ⟨x, hx, rfl⟩
    have hxfin : Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = N - 1 := hx.2.1
    have hQx : Q₀ ≤ ‖x‖ ^ (1 + s) := hx.2.2
    have hQx0 : 0 < ‖x‖ := by
      by_contra hcon
      push_neg at hcon
      have h0 : ‖x‖ = 0 := le_antisymm hcon (norm_nonneg x)
      have hz : (0:ℝ) ^ (1 + s) = 0 := Real.zero_rpow (by linarith)
      rw [h0, hz] at hQx
      linarith
    have heq : approxSpace (toC Mr) c ‖x‖ = approxSpace (toC Mr) c' (‖x‖ ^ (1 + s)) := by
      rw [hc'def]
      simp only [approxSpace]
      rw [approxBox_rpow_div (toC Mr) c hs1 hQx0]
    have hfr' : Module.finrank ℚ (approxSpace (toC Mr) c' (‖x‖ ^ (1 + s))) = N - 1 := by
      rw [← heq]; exact hxfin
    have hmemS : approxSpace (toC Mr) c' (‖x‖ ^ (1 + s)) ∈ S := by
      refine hS (‖x‖ ^ (1 + s)) hQx ?_
      rwa [Fintype.card_fin]
    have hW : approxSpace (toC Mr) c ‖x‖ ∈ hSfin.toFinset.filter (fun V => V ≠ ⊤) := by
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [heq, Set.Finite.mem_toFinset]
        exact hmemS
      · intro htop
        have h1 : Module.finrank ℚ (approxSpace (toC Mr) c' (‖x‖ ^ (1 + s)))
            = Module.finrank ℚ (Fin N → ℚ) := by rw [← heq, htop, finrank_top]
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hfr'] at h1
        omega
    refine ⟨approxSpace (toC Mr) c ‖x‖, hW, ?_⟩
    exact mem_approxSpace_of_mem_box ((mem_approxBox_iff).mpr (hb x hx.1))

end Submission.Subspace.RealRank
