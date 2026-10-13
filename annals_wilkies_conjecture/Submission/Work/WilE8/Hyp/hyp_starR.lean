import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Clear
import Submission.Work.WilE8.Clear.clearDenom_eval
import Submission.Work.WilE8.Clear.clearDenom_totalDegree_le
import Submission.Work.WilE8.E2.star_of_semipf
import Submission.Work.WilE8.Poly.eval_mono_nat
import Submission.Work.WilE10.Psi
import Submission.Work.WilE8.Hyp.Basic
import Submission.Work.WilE8.Hyp.hyperPF_subset
import Submission.Work.WilE8.Hyp.hyperPF_supset
import Submission.Work.WilE8.Hyp.hyperPF_deg_le
import Submission.Work.WilE8.Hyp.poly_dom_comp

set_option autoImplicit false
noncomputable section
namespace Work.WilE8.Hyp

open WilkiesDesign WilkiesDesign.E

/-- `psiV : ℝⁿ → ℝⁿ` is injective (coordinatewise injectivity of `psi`). -/
theorem psiV_injective (n : ℕ) :
    Function.Injective (psiV : (Fin n → ℝ) → (Fin n → ℝ)) := by
  intro x y h
  funext i
  exact Work.WilE10.psi_injective (congrFun h i)

/-- Since `psiV` is injective, taking the preimage of the image is the identity. -/
theorem preimage_image_psiV {n : ℕ} (A : Set (Fin n → ℝ)) :
    psiV ⁻¹' (psiV '' A) = A := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [← psiV_injective n hxy]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem hyp_starR
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (Q : MvPolynomial (Fin n) ℝ), 1 ≤ Q.totalDegree →
      WilkiesDesign.E.StarR (2 * n) (p.eval Q.totalDegree) n
        {x : Fin n → ℝ | MvPolynomial.eval x Q = 0} := by
  let P2 : Polynomial ℕ := (hE2 (n + n)).choose
  obtain ⟨p, hp⟩ := poly_dom_comp P2 n
  refine ⟨p, fun Q _ => ?_⟩
  have hfmt : (hyperPF Q).fmt = n + n := rfl
  have hstar0 := Work.WilE8.E2.star_of_semipf hE2 n n (hyperPF Q)
  have hdeg_le : (hyperPF Q).deg ≤ 5 * n + 1 + n * Q.totalDegree := hyperPF_deg_le Q
  have hD : (hE2 ((hyperPF Q).fmt)).choose.eval (hyperPF Q).deg * (hyperPF Q).deg
      ≤ p.eval Q.totalDegree := by
    rw [hfmt]
    show P2.eval (hyperPF Q).deg * (hyperPF Q).deg ≤ p.eval Q.totalDegree
    exact le_trans (Nat.mul_le_mul (Work.WilE8.Poly.eval_mono_nat P2 hdeg_le) hdeg_le)
      (hp Q.totalDegree)
  have hstar : WilkiesDesign.E.Star (2 * n) (p.eval Q.totalDegree) n
      (projFirst n n '' (hyperPF Q).set) :=
    Work.WilE8.Star.mono hstar0 (by rw [hfmt]; omega) hD
  have hset : projFirst n n '' (hyperPF Q).set =
      psiV '' {x : Fin n → ℝ | MvPolynomial.eval x Q = 0} :=
    Set.Subset.antisymm (hyperPF_subset Q) (hyperPF_supset Q)
  exact ⟨projFirst n n '' (hyperPF Q).set, hstar, by
    rw [hset]
    exact (preimage_image_psiV _).symm⟩

end Work.WilE8.Hyp
