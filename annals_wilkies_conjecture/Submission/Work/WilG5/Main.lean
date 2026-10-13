/-
  WilG5 — assembly of `WilkiesDesign.CG.G5_alg_of_FLem_proved`.

  The algebraic lemma (`WilkiesDesign.AlgLemma`) is proved by induction on the ambient
  dimension `n`, with `∀ F` universally quantified:

  * the points of `X` inside the open cube are covered by the F-lemma charts
    (`Work.WilG5.Interior.interior_charts`); for `n = 0` the open cube is everything, so this
    already gives the base case;
  * the points of `X` on the boundary are covered by the induction hypothesis applied to the
    faces of the cube (`Work.WilG5.Face.face_charts`).

  The two halves give chart families whose cardinalities are bounded by two polynomials; the
  bound for the union is the sum of the two bounds.
-/
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Interior.interior_charts
import Submission.Work.WilG5.Face.face_charts

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign WilkiesConjecture

theorem G5_alg_of_FLem_proved (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hF : ∀ p n, FLem S p n) (F n : ℕ) : AlgLemma S F n := by
  have _hder := hder
  have hmain : ∀ n, ∀ G : ℕ, AlgLemma S G n := by
    intro n
    induction n with
    | zero =>
      intro G
      obtain ⟨p, hpnn, hp⟩ := Work.WilG5.Interior.interior_charts S hcd hF G 0
      refine ⟨p, ?_⟩
      intro D r ε hε0 hε1 μ X hμ hsub hX hdim
      obtain ⟨Φ, hcard, hprop, hcov⟩ := hp D r ε hε0 hε1 μ X hμ hsub hX hdim
      exact ⟨Φ, hcard, hprop, fun x hx => hcov x hx (fun i => Fin.elim0 i)⟩
    | succ n ih =>
      intro G
      obtain ⟨p₁, hp₁nn, hp₁⟩ := Work.WilG5.Interior.interior_charts S hcd hF G (n + 1)
      obtain ⟨p₂, hp₂nn, hp₂⟩ :=
        Work.WilG5.Face.face_charts S (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
          (fun F' => (Nat.succ_sub_one n) ▸ ih F') G
      refine ⟨p₁ + p₂, ?_⟩
      intro D r ε hε0 hε1 μ X hμ hsub hX hdim
      obtain ⟨Φ₁, hc₁, hp₁', hcv₁⟩ := hp₁ D r ε hε0 hε1 μ X hμ hsub hX hdim
      obtain ⟨Φ₂, hc₂, hp₂', hcv₂⟩ := hp₂ D r ε hε0 hε1 μ X hμ hsub hX hdim
      refine ⟨Φ₁ ∪ Φ₂, ?_, ?_, ?_⟩
      · have hcard : (((Φ₁ ∪ Φ₂).card : ℕ) : ℝ) ≤ (Φ₁.card : ℝ) + (Φ₂.card : ℝ) := by
          exact_mod_cast Finset.card_union_le Φ₁ Φ₂
        rw [MvPolynomial.eval_add]
        exact le_trans hcard (add_le_add hc₁ hc₂)
      · intro φ hφ
        rcases Finset.mem_union.mp hφ with h | h
        · exact hp₁' φ h
        · exact hp₂' φ h
      · intro x hx
        by_cases hxo : x ∈ openCube (n + 1)
        · obtain ⟨φ, hφ, t, ht, hd⟩ := hcv₁ x hx hxo
          exact ⟨φ, Finset.mem_union_left _ hφ, t, ht, hd⟩
        · obtain ⟨φ, hφ, t, ht, hd⟩ := hcv₂ x hx hxo
          exact ⟨φ, Finset.mem_union_right _ hφ, t, ht, hd⟩
  exact hmain n F

end WilkiesDesign.CG
