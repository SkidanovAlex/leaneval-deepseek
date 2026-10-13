import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-- Monotonicity of `List.sum` under a pointwise bound of the summands. -/
theorem list_sum_map_le {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp))
      (ih fun b hb => h b (by simp [hb]))

/-- Padding an `EA`-polynomial to more coordinates does not raise its atom degree:
`EAPoly.pad` is a polynomial *renaming*, and `MvPolynomial.rename` never raises the total
degree. -/
theorem atomDeg_pad_le {k K r : ℕ} (hm : k ≤ K) (Q : EAPoly k r) :
    atomDeg (EAPoly.pad hm Q) ≤ atomDeg Q := by
  simp only [atomDeg, EAPoly.pad]
  exact Nat.add_le_add_right
    (MvPolynomial.totalDegree_rename_le (Sum.map (Fin.castLE hm) id) Q) 1

/-- Padding a basic set does not raise its degree: both lists of atoms are padded one by one. -/
theorem basic_deg_pad_le {k K r : ℕ} (hm : k ≤ K) (B : Basic k r) :
    (Basic.pad hm B).deg ≤ B.deg := by
  have h := list_sum_map_le (B.eqs ++ B.pos) (fun Q => atomDeg (EAPoly.pad hm Q)) atomDeg
    (fun Q _ => atomDeg_pad_le hm Q)
  simp only [Basic.deg, Basic.pad, List.map_append, List.map_map] at h ⊢
  exact h

/-- Padding a semi-Pfaffian set does not raise its degree: the DNF list is padded entrywise. -/
theorem semipf_deg_pad_le {k K : ℕ} (hm : k ≤ K) (X : SemiPf k) :
    (SemiPf.pad hm X).deg ≤ X.deg := by
  have h := list_sum_map_le X.basics (fun B => (Basic.pad hm B).deg) Basic.deg
    (fun B _ => basic_deg_pad_le hm B)
  simp only [SemiPf.deg, SemiPf.pad, List.map_map] at h ⊢
  exact h

theorem pad_deg :
    (∀ {k K r : ℕ} (hm : k ≤ K) (Q : WilkiesDesign.E.EAPoly k r),
        WilkiesDesign.E.atomDeg (Work.WilE7.EAPoly.pad hm Q) ≤ WilkiesDesign.E.atomDeg Q) ∧
    (∀ {k K r : ℕ} (hm : k ≤ K) (B : WilkiesDesign.E.Basic k r),
        WilkiesDesign.E.Basic.deg (Work.WilE7.Basic.pad hm B) ≤ WilkiesDesign.E.Basic.deg B) ∧
    (∀ {k K : ℕ} (hm : k ≤ K) (X : WilkiesDesign.E.SemiPf k),
        WilkiesDesign.E.SemiPf.deg (Work.WilE7.SemiPf.pad hm X) ≤ WilkiesDesign.E.SemiPf.deg X) :=
  ⟨fun hm Q => atomDeg_pad_le hm Q, fun hm B => basic_deg_pad_le hm B,
   fun hm X => semipf_deg_pad_le hm X⟩

end Work.WilE7
