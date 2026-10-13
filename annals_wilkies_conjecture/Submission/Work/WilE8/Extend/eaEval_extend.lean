import Mathlib
import Submission.Work.WilE8.Extend

namespace Work.WilE8.Extend

open WilkiesDesign WilkiesDesign.E

/-- The coefficient function `(Work.WilE8.EAChain.extend e c).a j` is the pull-back of
`c.a j` along the injection `e` on the image of `e`, and `0` off it.  Consequently its
weighted sum against a function `x : Fin k' → ℝ` collapses to the corresponding sum over
`Fin k` (this is where injectivity of `e` is used). -/
lemma sum_extend_a {k k' : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (a : Fin k → ℝ) (x : Fin k' → ℝ) :
    (∑ i' : Fin k', (if h : ∃ i, e i = i' then a h.choose else 0) * x i')
      = ∑ i : Fin k, a i * x (e i) := by
  have hcoeff : ∀ i : Fin k,
      (if h : ∃ i', e i' = e i then a h.choose else 0) * x (e i) = a i * x (e i) := by
    intro i
    have hex : ∃ i', e i' = e i := ⟨i, rfl⟩
    rw [dite_eq_left hex]
    have hch : hex.choose = i := he hex.choose_spec
    rw [hch]
  have hzero : ∀ i' ∈ (Finset.univ : Finset (Fin k')), i' ∉ Finset.univ.image e →
      (if h : ∃ i, e i = i' then a h.choose else 0) * x i' = 0 := by
    intro i' _ hi'
    have hnot : ¬ ∃ i, e i = i' := by
      rintro ⟨i, hi⟩
      exact hi' (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    rw [dite_eq_right hnot, zero_mul]
  calc (∑ i' : Fin k', (if h : ∃ i, e i = i' then a h.choose else 0) * x i')
      = ∑ i' ∈ (Finset.univ : Finset (Fin k)).image e,
          (if h : ∃ i, e i = i' then a h.choose else 0) * x i' :=
        (Finset.sum_subset (Finset.subset_univ _) hzero).symm
    _ = ∑ i : Fin k,
          (if h : ∃ i', e i' = e i then a h.choose else 0) * x (e i) :=
        Finset.sum_image
          (f := fun i' => (if h : ∃ i, e i = i' then a h.choose else 0) * x i')
          (g := e) (fun a _ b _ h => he h)
    _ = ∑ i : Fin k, a i * x (e i) := Finset.sum_congr rfl (fun i _ => hcoeff i)

/-- The `ell`-part of `eaEval_extend`: extending an EA chain along `e` does not change the
linear forms, pulled back along `e`. -/
lemma ell_extend {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : EAChain k r) (j : Fin r) (x : Fin k' → ℝ) :
    (EAChain.extend e c).ell j x = c.ell j (fun i => x (e i)) := by
  simp only [EAChain.ell, EAChain.extend]
  rw [sum_extend_a he (c.a j) x]

theorem eaEval_extend {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : WilkiesDesign.E.EAChain k r) (Q : WilkiesDesign.E.EAPoly k r) (x : Fin k' → ℝ) :
    (∀ j : Fin r, (Work.WilE8.EAChain.extend e c).ell j x = c.ell j (fun i => x (e i))) ∧
    WilkiesDesign.E.eaEval (Work.WilE8.EAChain.extend e c) (Work.WilE8.EAPoly.extend e Q) x
      = WilkiesDesign.E.eaEval c Q (fun i => x (e i)) := by
  refine ⟨fun j => ell_extend he c j x, ?_⟩
  have hfun : (Sum.elim x fun j => Real.exp ((EAChain.extend e c).ell j x)) ∘ Sum.map e id
      = Sum.elim (fun i => x (e i)) fun j => Real.exp (c.ell j fun i => x (e i)) := by
    funext z
    rcases z with i | j
    · rfl
    · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
      exact congrArg Real.exp (ell_extend he c j x)
  simp only [eaEval, EAPoly.extend]
  rw [MvPolynomial.eval_rename, hfun]

end Work.WilE8.Extend
