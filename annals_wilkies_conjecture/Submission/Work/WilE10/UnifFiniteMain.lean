/-
  WilE10 — `E0b_unif_finite`: uniform finiteness of the fibres of an `rexp`-existential family,
  from the sharp cell decomposition of BV (`E7_prop_main`), the component bound for `Ω`-sets in
  dimension one (`E8_comps`) and `E10_rexp_to_subpf`.
-/
import Submission.Work.WilE10.UnifFinite.unif_finite_core
import Submission.Work.WilE10.RexpSubMain

set_option autoImplicit false
noncomputable section
open Classical

namespace WilkiesDesign.CG

open WilkiesDesign WilkiesDesign.E

/-- **E0b.** Fibres of an `rexp`-existential family have uniformly finitely many components. -/
theorem E0b_unif_finite_proved
    (hE7 : ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → SemiPf (n + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
      ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
        (∀ i, ∀ κ ∈ C,
          κ ⊆ projFirst n m '' (X i).set ∨ Disjoint κ (projFirst n m '' (X i).set)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧
        ∀ κ ∈ C, Star a (c.eval D) n κ ∧ SubPf n κ)
    (hE8 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (D : ℕ) (A : Set (Fin 1 → ℝ)),
      Gen F D 1 A →
      ∃ s : Finset (Set (Fin 1 → ℝ)), s.card ≤ p.eval D ∧ (∀ I ∈ s, IsPreconnected I) ∧
        A = ⋃₀ (s : Set (Set (Fin 1 → ℝ)))) :
    UnifFiniteRExp :=
  Work.WilE10.UnifFinite.unif_finite_core hE7 hE8
    (fun n X hX => E10_rexp_to_subpf_proved X hX)

end WilkiesDesign.CG
