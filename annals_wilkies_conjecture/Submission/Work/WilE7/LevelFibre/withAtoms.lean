/-
  Area E7, `Work.WilE7.LevelFibre.withAtoms`: a restricted semi-Pfaffian set can be cut by
  *semialgebraic* atoms, i.e. by polynomial equations and inequalities in the plain coordinates
  of `ℝⁿ` (no chain variable involved).

  The construction appends, to every branch of the DNF presentation of `X`, the (image of the)
  extra equations and inequalities; the chain `X.c` is reused unchanged, since a plain
  polynomial is an EA polynomial in which no chain variable occurs (`eaEmbed`).

  The set identity `addAtoms_set` is the semantic content, and `withAtoms` is its rewriting into
  the `MvPolynomial.eval` form requested by the caller.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.LevelFibre

open WilkiesDesign WilkiesDesign.E

/-! ## Plain polynomials as EA polynomials

`eaEmbed Q` views a polynomial `Q` in the coordinates `x` as a polynomial in the coordinates `x`
together with the chain variables `Eⱼ`; no chain variable actually occurs, so evaluating it in
an EA chain agrees with the plain evaluation. -/

/-- Regard a polynomial in the coordinates `Fin n` as an EA polynomial of rank `r` (the chain
variables `Sum.inr j` do not occur). -/
def eaEmbed {n r : ℕ} (Q : MvPolynomial (Fin n) ℝ) : EAPoly n r :=
  MvPolynomial.rename Sum.inl Q

/-- Evaluation of an embedded plain polynomial is the plain evaluation. -/
theorem eaEval_eaEmbed {n r : ℕ} (c : EAChain n r) (Q : MvPolynomial (Fin n) ℝ)
    (z : Fin n → ℝ) : eaEval c (eaEmbed Q) z = MvPolynomial.eval z Q := by
  rw [eaEval, eaEmbed, MvPolynomial.eval_rename]
  simp only [Function.comp_def, Sum.elim_inl]

/-! ## Cutting a semi-Pfaffian set by EA equations and inequalities -/

/-- Appending equations and inequalities to a basic set: semantics. -/
theorem holds_append {n r : ℕ} (c : EAChain n r) (B : Basic n r) (E P : List (EAPoly n r))
    (z : Fin n → ℝ) :
    (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic n r).holds c z ↔
      B.holds c z ∧ (∀ f ∈ E, eaEval c f z = 0) ∧ (∀ g ∈ P, 0 < eaEval c g z) := by
  simp only [Basic.holds, List.forall_mem_append]
  tauto

/-- Append the EA equations `E` and the EA inequalities `P` to every branch of the DNF
presentation of `X`.  The chain is unchanged. -/
def addAtoms {n : ℕ} (X : SemiPf n) (E P : List (EAPoly n X.r)) : SemiPf n :=
  ⟨X.r, X.c, X.basics.map (fun B => (⟨B.eqs ++ E, B.pos ++ P⟩ : Basic n X.r))⟩

/-- The point set of `addAtoms X E P` is `X.set` cut by `E = 0` and `P > 0`. -/
theorem addAtoms_set {n : ℕ} (X : SemiPf n) (E P : List (EAPoly n X.r)) :
    (addAtoms X E P).set = X.set ∩ {z | ∀ f ∈ E, eaEval X.c f z = 0} ∩
      {z | ∀ g ∈ P, 0 < eaEval X.c g z} := by
  ext z
  simp only [addAtoms, SemiPf.set, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hz, B, hB, hh⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    obtain ⟨h1, h2, h3⟩ := (holds_append X.c B₀ E P z).mp hh
    exact ⟨⟨⟨hz, B₀, hB₀, h1⟩, h2⟩, h3⟩
  · rintro ⟨⟨⟨hz, B, hB, hh⟩, h2⟩, h3⟩
    exact ⟨hz, ⟨B.eqs ++ E, B.pos ++ P⟩, List.mem_map.mpr ⟨B, hB, rfl⟩,
      (holds_append X.c B E P z).mpr ⟨hh, h2, h3⟩⟩

/-! ## The requested statement -/

theorem withAtoms {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (eqs pos : List (MvPolynomial (Fin n) ℝ)) :
    ∃ Y : WilkiesDesign.E.SemiPf n, Y.set = X.set ∩
      {z : Fin n → ℝ | (∀ Q ∈ eqs, MvPolynomial.eval z Q = 0) ∧
        (∀ P ∈ pos, 0 < MvPolynomial.eval z P)} := by
  refine ⟨addAtoms X (eqs.map (@eaEmbed n X.r)) (pos.map (@eaEmbed n X.r)), ?_⟩
  have hE : {z : Fin n → ℝ | ∀ f ∈ eqs.map (@eaEmbed n X.r), eaEval X.c f z = 0} =
      {z : Fin n → ℝ | ∀ Q ∈ eqs, MvPolynomial.eval z Q = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, List.forall_mem_map, eaEval_eaEmbed]
  have hP : {z : Fin n → ℝ | ∀ g ∈ pos.map (@eaEmbed n X.r), 0 < eaEval X.c g z} =
      {z : Fin n → ℝ | ∀ P ∈ pos, 0 < MvPolynomial.eval z P} := by
    ext z
    simp only [Set.mem_ofPred_eq, List.forall_mem_map, eaEval_eaEmbed]
  rw [addAtoms_set, hE, hP]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

end Work.WilE7.LevelFibre
