import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

open WilkiesDesign WilkiesDesign.E WilkiesDesign.CG.C4a

/-- Over the empty exp-affine chain the two evaluations agree: `eaEval` reduces to `ev0`. -/
private lemma eaEval_nil_eq_ev0 {D : ℕ} (p : EAPoly D 0) (v : Fin D → ℝ) :
    eaEval (EAChain.nil D) p v = Work.WilC4aCS.ev0 v p := by
  have h : (Sum.elim v (fun j : Fin 0 => Real.exp ((EAChain.nil D).ell j v)))
      = (Sum.elim v fun _ : Fin 0 => (0 : ℝ)) := by
    funext s
    rcases s with i | j
    · rfl
    · exact j.elim0
  rw [eaEval, Work.WilC4aCS.ev0, h]

theorem Base_eq_BasicSA {n l : ℕ} (d : Fin (l + 1) → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (B : WilkiesDesign.E.Basic (∑ i, d i) 0) :
    Work.WilC4aCS.Base d a B =
      WilkiesDesign.CG.C4a.BasicSA
        (fun x' : Fin n → ℝ => ∑ f ∈ B.eqs.toFinset,
          (Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') f) ^ 2)
        (fun j : Fin B.pos.length => fun x' : Fin n → ℝ =>
          Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x') (B.pos.get j)) := by
  ext x
  simp only [Work.WilC4aCS.Base, Set.mem_preimage, Work.WilC4aCS.BSet,
    WilkiesDesign.E.Basic.holds, WilkiesDesign.CG.C4a.BasicSA, Set.mem_ofPred_eq,
    eaEval_nil_eq_ev0]
  constructor
  · rintro ⟨he, hp⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_zero_iff_of_nonneg (fun f _ => sq_nonneg _)]
      intro f hf
      rw [he f (List.mem_toFinset.mp hf)]
      norm_num
    · intro j
      exact hp (B.pos.get j) (List.get_mem _ _)
  · rintro ⟨he, hp⟩
    refine ⟨?_, ?_⟩
    · intro f hf
      have hmem : f ∈ B.eqs.toFinset := List.mem_toFinset.mpr hf
      have h0 : (Work.WilC4aCS.ev0 (Work.WilC4aCS.coefFun d a x) f) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun f _ => sq_nonneg _)).mp he f hmem
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h0
    · intro g hg
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
      rw [← hi]
      exact hp i

end Work.WilC4aCS
