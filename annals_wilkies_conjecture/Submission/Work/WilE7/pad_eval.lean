import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Zero-padding a chain: consistency of the padded vocabulary

`EAChain.pad hm c` writes the coefficients of the `k`-chain `c` into a `K`-chain
(`k ≤ K`) and puts `0` in the extra coordinates, and `takeZ hm` truncates a
point of `ℝ^K` to its first `k` coordinates.  The lemmas in `padAux` record that
this is exactly the "forget the extra coordinates" operation on the level of
functions (`pad_ell`), of `EA`-polynomials (`eaEval_pad`) and of basic sets
(`holds_pad`).  The conjunction `pad_eval` below is what the E7 development
consumes. -/

namespace padAux

/-- Sums of `Fin k`-indexed families, written as sums over `Fin K` (`k ≤ K`) of
the padded family `if i < k then f i else 0`. -/
theorem sum_univ_pad {k K : ℕ} (hm : k ≤ K) (f : Fin k → ℝ) (y : Fin K → ℝ) :
    (∑ i : Fin K, (if h : i.val < k then f ⟨i.val, h⟩ else 0) * y i)
      = ∑ i : Fin k, f i * y (Fin.castLE hm i) := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have hsub : Finset.range k ⊆ Finset.range K := Finset.range_subset_range.mpr hm
  have hzero : ∀ x ∈ Finset.range K, x ∉ Finset.range k →
      (if h : x < K then (if h' : x < k then f ⟨x, h'⟩ else 0) * y ⟨x, h⟩ else 0) = 0 := by
    intro x hx hxk
    rw [Finset.mem_range] at hx
    have hxk' : ¬ x < k := by simpa [Finset.mem_range] using hxk
    simp [hx, hxk']
  rw [← Finset.sum_subset hsub hzero]
  apply Finset.sum_congr rfl
  intro x hx
  have hxk : x < k := Finset.mem_range.mp hx
  have hxK : x < K := lt_of_lt_of_le hxk hm
  simp [hxk, hxK]

/-- The chain functions of a padded chain are the old chain functions evaluated
at the truncated point. -/
theorem pad_ell {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (j : Fin r) (y : Fin K → ℝ) :
    (EAChain.pad hm c).ell j y = c.ell j (takeZ hm y) := by
  rw [EAChain.ell, EAChain.ell]
  simp only [EAChain.pad]
  rw [sum_univ_pad hm (c.a j) y]
  rfl

/-- Evaluating a padded `EA`-polynomial in the padded chain at `y` is the same
as evaluating the original polynomial in the original chain at the truncated
point `takeZ hm y`. -/
theorem eaEval_pad {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (Q : EAPoly k r)
    (y : Fin K → ℝ) :
    eaEval (EAChain.pad hm c) (EAPoly.pad hm Q) y = eaEval c Q (takeZ hm y) := by
  have hell : ∀ j : Fin r, (EAChain.pad hm c).ell j y = c.ell j (takeZ hm y) :=
    fun j => pad_ell hm c j y
  have hfun : (Sum.elim y fun j => Real.exp ((EAChain.pad hm c).ell j y)) ∘
        Sum.map (Fin.castLE hm) id =
      Sum.elim (takeZ hm y) fun j => Real.exp (c.ell j (takeZ hm y)) := by
    funext s
    rcases s with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
      exact congrArg Real.exp (hell j)
  simp only [eaEval, EAPoly.pad, MvPolynomial.eval_rename, hfun]

/-- A padded basic set holds at `y` in the padded chain exactly when the
original basic set holds at the truncated point. -/
theorem holds_pad {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (B : Basic k r) (y : Fin K → ℝ) :
    (Basic.pad hm B).holds (EAChain.pad hm c) y ↔ B.holds c (takeZ hm y) := by
  simp only [Basic.holds, Basic.pad]
  constructor
  · intro h
    exact ⟨fun f hf => by
        have h' := h.1 (EAPoly.pad hm f) (List.mem_map_of_mem hf)
        rwa [eaEval_pad hm c f y] at h',
      fun g hg => by
        have h' := h.2 (EAPoly.pad hm g) (List.mem_map_of_mem hg)
        rwa [eaEval_pad hm c g y] at h'⟩
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_pad hm c f₀ y]
      exact h.1 f₀ hf₀
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      rw [eaEval_pad hm c g₀ y]
      exact h.2 g₀ hg₀

end padAux

theorem pad_eval {k K r : ℕ} (hm : k ≤ K) (c : WilkiesDesign.E.EAChain k r) :
    (∀ (j : Fin r) (y : Fin K → ℝ),
        (Work.WilE7.EAChain.pad hm c).ell j y = c.ell j (Work.WilE7.takeZ hm y)) ∧
    (∀ (B : WilkiesDesign.E.Basic k r) (y : Fin K → ℝ),
        (Work.WilE7.Basic.pad hm B).holds (Work.WilE7.EAChain.pad hm c) y ↔
          B.holds c (Work.WilE7.takeZ hm y)) ∧
    (∀ (Q : WilkiesDesign.E.EAPoly k r) (y : Fin K → ℝ),
        WilkiesDesign.E.eaEval (Work.WilE7.EAChain.pad hm c) (Work.WilE7.EAPoly.pad hm Q) y =
          WilkiesDesign.E.eaEval c Q (Work.WilE7.takeZ hm y)) :=
  ⟨fun j y => padAux.pad_ell hm c j y,
   fun B y => padAux.holds_pad hm c B y,
   fun Q y => padAux.eaEval_pad hm c Q y⟩

end Work.WilE7
