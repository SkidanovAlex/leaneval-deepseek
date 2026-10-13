import Mathlib
import Submission.Work.WilE6.E6_closure_proved
import Submission.Work.WilE6.E6_closure_cubeSaturated
import Submission.Work.WilE6.exists_cubeSaturated
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.E6Frontier.Defs
import Submission.Work.WilE6.E6Frontier.interCat_set
import Submission.Work.WilE6.E6Frontier.interCat_deg_le
import Submission.Work.WilE6.E6Frontier.fiberClosure_subset_cubeC
import Submission.Work.WilE5.Basic
import Submission.Work.WilE9.Ift.OneShot.exists_clean

set_option autoImplicit false
noncomputable section
open Classical Topology

namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem E6_fiber_closure_proved_of_complement (hE3b : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (B : WilkiesDesign.E.Basic k r) (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ → (y ∈ closure {x | B.holds c x} ↔ y ∈ closure {x | (∀ f ∈ B.eqs, |WilkiesDesign.E.eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧ (∀ g ∈ B.pos, dist x y ^ κ < WilkiesDesign.E.eaTaylor c g κ y x)})) (hE4 : ∀ p q : ℕ, ∃ b : Polynomial ℕ, ∀ X : WilkiesDesign.E.SA (p + q), ∃ Y : WilkiesDesign.E.SA (p + q), Y.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set) (hcompl : ∀ (F : ℕ), ∃ (p : Polynomial ℕ), ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (basics : List (WilkiesDesign.E.Basic k r)), k + r ≤ F → ∃ (basics' : List (WilkiesDesign.E.Basic k r)), (basics'.map WilkiesDesign.E.Basic.deg).sum ≤ p.eval ((basics.map WilkiesDesign.E.Basic.deg).sum) ∧ {x : Fin k → ℝ | x ∈ WilkiesDesign.E.cubeC k ∧ ∃ B ∈ basics', B.holds c x} = WilkiesDesign.E.cubeC k \ {x : Fin k → ℝ | x ∈ WilkiesDesign.E.cubeC k ∧ ∃ B ∈ basics, B.holds c x}) (F : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F → ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧ Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧ Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set := by
  -- The closure half: `Y` with `Y.set = fiberClosure X.set`, format `≤ a₁`, degree `≤ b₁ D`.
  obtain ⟨a₁, b₁, hclos⟩ := E6_closure_proved hE3b hE4 F
  -- The effective complement: over the same chain as `X`.
  obtain ⟨pc, hpc⟩ := hcompl F
  refine ⟨F + a₁, (pc + 1) * b₁ + (b₁ + 1) * pc, ?_⟩
  intro p q X hX
  obtain ⟨Y, hYfmt, hYdeg, hYset⟩ := hclos p q X hX
  obtain ⟨bs', hbs'deg, hbs'set⟩ := hpc (p + q) X.r X.c X.basics hX
  -- Both the closure and the complement are "cleaned", so that the number of disjuncts is
  -- bounded by the degree (`exists_clean`).
  obtain ⟨Y1, hY1set, hY1r, hY1deg, hY1len⟩ := Work.WilE9.Ift.OneShot.exists_clean (p + q) Y
  obtain ⟨Z1, hZ1set, hZ1r, hZ1deg, hZ1len⟩ :=
    Work.WilE9.Ift.OneShot.exists_clean (p + q) (⟨X.r, X.c, bs'⟩ : SemiPf (p + q))
  -- The fibrewise closure stays in the cube, so the frontier is the intersection with the
  -- complement inside the cube.
  have hcube : X.set ⊆ cubeC (p + q) := Work.WilE5.semiPf_set_subset_cube X
  have hsub : fiberClosure X.set ⊆ cubeC (p + q) :=
    E6Frontier.fiberClosure_subset_cubeC hcube
  -- The complement describes `cubeC \ X.set`.
  have hZ1set' : Z1.set = cubeC (p + q) \ X.set := by
    rw [hZ1set]
    show {x : Fin (p + q) → ℝ | x ∈ cubeC (p + q) ∧ ∃ B ∈ bs', B.holds X.c x} =
      cubeC (p + q) \ X.set
    rw [show X.set = {x : Fin (p + q) → ℝ | x ∈ cubeC (p + q) ∧
      ∃ B ∈ X.basics, B.holds X.c x} from rfl]
    exact hbs'set
  -- The degree of the product DNF, evaluated at `X.deg`.
  have heval : ((pc + 1) * b₁ + (b₁ + 1) * pc).eval X.deg =
      (pc.eval X.deg + 1) * b₁.eval X.deg + (b₁.eval X.deg + 1) * pc.eval X.deg := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  refine ⟨Y, interCat Y1 Z1, ?_, ?_, ?_, ?_, hYset, ?_⟩
  · -- format of `Y`
    show (p + q) + Y.r ≤ F + a₁
    have h1 : (p + q) + Y.r ≤ a₁ := hYfmt
    omega
  · -- degree of `Y`
    show Y.deg ≤ ((pc + 1) * b₁ + (b₁ + 1) * pc).eval X.deg
    rw [heval]
    refine hYdeg.trans ?_
    exact (Nat.le_mul_of_pos_left (b₁.eval X.deg) (Nat.succ_pos _)).trans (Nat.le_add_right _ _)
  · -- format of the frontier
    show (p + q) + (Y1.r + Z1.r) ≤ F + a₁
    have h1 : (p + q) + Y.r ≤ a₁ := hYfmt
    have h2 : (p + q) + X.r ≤ F := hX
    have h3 : Z1.r ≤ X.r := hZ1r
    omega
  · -- degree of the frontier
    show (interCat Y1 Z1).deg ≤ ((pc + 1) * b₁ + (b₁ + 1) * pc).eval X.deg
    rw [heval]
    have hZ1len' : Z1.basics.length ≤ pc.eval X.deg + 1 := by
      have h := hZ1len
      simp only [SemiPf.deg] at h
      exact h.trans (Nat.add_le_add_right hbs'deg 1)
    have hY1deg' : Y1.deg ≤ b₁.eval X.deg := hY1deg.trans hYdeg
    have hY1len' : Y1.basics.length ≤ b₁.eval X.deg + 1 :=
      hY1len.trans (Nat.add_le_add_right hYdeg 1)
    have hZ1deg' : Z1.deg ≤ pc.eval X.deg := by
      have h := hZ1deg
      simp only [SemiPf.deg] at h
      exact h.trans hbs'deg
    calc (interCat Y1 Z1).deg
        ≤ Z1.basics.length * Y1.deg + Y1.basics.length * Z1.deg :=
          E6Frontier.interCat_deg_le Y1 Z1
      _ ≤ (pc.eval X.deg + 1) * b₁.eval X.deg + (b₁.eval X.deg + 1) * pc.eval X.deg :=
          Nat.add_le_add (Nat.mul_le_mul hZ1len' hY1deg') (Nat.mul_le_mul hY1len' hZ1deg')
  · -- the frontier set
    show (interCat Y1 Z1).set = fiberClosure X.set \ X.set
    rw [E6Frontier.interCat_set, hY1set, hYset, hZ1set']
    ext x
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hsub h1, h2⟩

end Work.WilE6
