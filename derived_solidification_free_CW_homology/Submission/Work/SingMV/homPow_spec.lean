import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.sddeg_d
import Submission.Work.SingMV.homdeg_spec

/-!
# The telescoped homotopy recursion for the barycentric subdivision

`Work.SingMV.homPow X n k` is the `k`-fold telescoped homotopy operator
`h_k = h + sd ∘ h_{k-1}` built from the subdivision homotopy `homdeg` and the subdivision
operator `sddeg`; it satisfies the chain homotopy relation

  `∂ h_k + h_k ∂ = sd^k − 1`.

This is proved by induction on `k` from the two single-step inputs:

* `homdeg_spec` : `∂ ∘ homdeg + homdeg ∘ ∂ = sddeg − 1` (the barycentric subdivision homotopy),
* `sddeg_d`     : `∂ ∘ sddeg = sddeg ∘ ∂` (the degreewise subdivision is a chain map).

Indeed, writing `A_k = ∂∘h_k + h_k∘∂` and `s = sddeg`, the recursion `h_{k+1} = h + s∘h_k` gives
`A_{k+1} = (∂h + h∂) + s∘A_k = (s − 1) + s(s^k − 1) = s^{k+1} − 1`.
-/

open CategoryTheory

namespace Work.SingMV

/-- One step of the telescoped homotopy recursion, unfolded. -/
lemma homPow_succ (X : TopCat) (n k : ℕ) (z : ((Submission.Blueprint.singC).obj X).X n) :
    homPow X n (k+1) z = homdeg X n z + sddeg X (n+1) (homPow X n k z) := rfl

/-- The chain homotopy relation `∂ h_k + h_k ∂ = sd^k − 1` for the telescoped homotopy operator,
deduced from the single-step inputs `homdeg_spec` and `sddeg_d`. -/
theorem homPow_spec_of (X : TopCat)
    (hsd : ∀ (m : ℕ) (w : ((Submission.Blueprint.singC).obj X).X (m+1)),
      (((Submission.Blueprint.singC).obj X).d (m+1) m) (sddeg X (m+1) w) =
        sddeg X m ((((Submission.Blueprint.singC).obj X).d (m+1) m) w))
    (hdeg : ∀ (m : ℕ) (w : ((Submission.Blueprint.singC).obj X).X (m+1)),
      (((Submission.Blueprint.singC).obj X).d (m+2) (m+1)) (homdeg X (m+1) w) +
        homdeg X m ((((Submission.Blueprint.singC).obj X).d (m+1) m) w) =
      sddeg X (m+1) w - w) :
    ∀ (k n : ℕ) (z : ((Submission.Blueprint.singC).obj X).X (n+1)),
      (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (homPow X (n+1) k z) +
        homPow X n k ((((Submission.Blueprint.singC).obj X).d (n+1) n) z) =
      (sddeg X (n+1))^[k] z - z := by
  intro k
  induction k with
  | zero =>
      intro n z
      simp [homPow]
  | succ k ih =>
      intro n z
      calc (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (homPow X (n+1) (k+1) z) +
              homPow X n (k+1) ((((Submission.Blueprint.singC).obj X).d (n+1) n) z)
          = (((Submission.Blueprint.singC).obj X).d (n+2) (n+1))
                (homdeg X (n+1) z + sddeg X (n+2) (homPow X (n+1) k z)) +
              (homdeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n) z) +
                sddeg X (n+1)
                  (homPow X n k ((((Submission.Blueprint.singC).obj X).d (n+1) n) z))) := by
            rw [homPow_succ, homPow_succ]
        _ = (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (homdeg X (n+1) z) +
              homdeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n) z) +
              (sddeg X (n+1) ((((Submission.Blueprint.singC).obj X).d (n+2) (n+1))
                  (homPow X (n+1) k z)) +
                sddeg X (n+1)
                  (homPow X n k ((((Submission.Blueprint.singC).obj X).d (n+1) n) z))) := by
            rw [map_add, hsd (n+1) (homPow X (n+1) k z)]
            abel
        _ = (sddeg X (n+1) z - z) +
              sddeg X (n+1)
                ((((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (homPow X (n+1) k z) +
                  homPow X n k ((((Submission.Blueprint.singC).obj X).d (n+1) n) z)) := by
            rw [hdeg n z, ← map_add]
        _ = (sddeg X (n+1) z - z) + sddeg X (n+1) ((sddeg X (n+1))^[k] z - z) := by
            rw [ih n z]
        _ = (sddeg X (n+1) z - z) +
              (sddeg X (n+1) ((sddeg X (n+1))^[k] z) - sddeg X (n+1) z) := by
            rw [map_sub]
        _ = (sddeg X (n+1))^[k+1] z - z := by
            rw [Function.iterate_succ_apply']
            abel

theorem homPow_spec (X : TopCat) (n k : ℕ) (z : ((Submission.Blueprint.singC).obj X).X (n+1)) :
    (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (Work.SingMV.homPow X (n+1) k z) +
        Work.SingMV.homPow X n k ((((Submission.Blueprint.singC).obj X).d (n+1) n) z) =
      (Work.SingMV.sddeg X (n+1))^[k] z - z :=
  homPow_spec_of X (fun m w => sddeg_d X m w) (fun m w => homdeg_spec X m w) k n z

end Work.SingMV
