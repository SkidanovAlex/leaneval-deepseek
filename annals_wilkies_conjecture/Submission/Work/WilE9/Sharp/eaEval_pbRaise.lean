import Mathlib
import Submission.Work.WilE9.Sharp.PbSystem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The `a`-coefficient of the pulled-back chain, read off from the definitional unfolding. -/
lemma pbChain_a {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (j : Fin r) (l : Fin (Npb n m)) :
    (pbChain c).a j l = ∑ i : Fin (n + (1 + m)), if sIdxPb n m i = l then c.a j i else 0 := rfl

/-- The `b`-coefficient of the pulled-back chain is unchanged. -/
lemma pbChain_b {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (j : Fin r) :
    (pbChain c).b j = c.b j := rfl

/-- The linear forms of the pulled-back chain agree with those of `c` after reading the point in
the stratum's own coordinates: `(pbChain c).ell j z = c.ell j (pbStrat z)`. -/
lemma pbChain_ell {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (j : Fin r) : (pbChain c).ell j z = c.ell j (pbStrat z) := by
  have hsum : ∑ l : Fin (Npb n m),
        (∑ i : Fin (n + (1 + m)), if sIdxPb n m i = l then c.a j i else 0) * z l
      = ∑ i : Fin (n + (1 + m)), c.a j i * z (sIdxPb n m i) := by
    calc
      ∑ l : Fin (Npb n m),
            (∑ i : Fin (n + (1 + m)), if sIdxPb n m i = l then c.a j i else 0) * z l
          = ∑ l : Fin (Npb n m), ∑ i : Fin (n + (1 + m)),
              (if sIdxPb n m i = l then c.a j i else 0) * z l := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [Finset.sum_mul]
      _ = ∑ i : Fin (n + (1 + m)), ∑ l : Fin (Npb n m),
              (if sIdxPb n m i = l then c.a j i else 0) * z l := Finset.sum_comm
      _ = ∑ i : Fin (n + (1 + m)), c.a j i * z (sIdxPb n m i) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have h2 : ∀ l : Fin (Npb n m),
                (if sIdxPb n m i = l then c.a j i else 0) * z l
                  = if sIdxPb n m i = l then c.a j i * z l else 0 := by
              intro l; rw [ite_mul, zero_mul]
            refine (Finset.sum_congr rfl (fun l _ => h2 l)).trans ?_
            rw [Finset.sum_ite_eq]
            simp
  simp only [EAChain.ell, pbChain_a, pbChain_b, pbStrat]
  rw [hsum]

theorem eaEval_pbRaise {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (P : WilkiesDesign.E.EAPoly (n + (1 + m)) r) (z : Fin (Work.WilE9.Sharp.Npb n m) → ℝ) :
    WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain c) (Work.WilE9.Sharp.pbRaise P) z =
      WilkiesDesign.E.eaEval c P (Work.WilE9.Sharp.pbStrat z) := by
  unfold WilkiesDesign.E.eaEval Work.WilE9.Sharp.pbRaise
  rw [MvPolynomial.eval_rename]
  have h : (Sum.elim z (fun j => Real.exp ((pbChain c).ell j z)))
        ∘ (Sum.map (sIdxPb n m) id)
      = Sum.elim (pbStrat z) (fun j => Real.exp (c.ell j (pbStrat z))) := by
    funext t
    cases t with
    | inl i => rfl
    | inr j => exact congrArg Real.exp (pbChain_ell c z j)
  rw [h]

end Work.WilE9.Sharp
