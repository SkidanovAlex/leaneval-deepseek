/-
  WilG4a : area G4a of the Wilkie/Pfaffian project (BNZ §5.1).

  This module proves the trivial case `n = 0` of the family lemma, i.e. the hole
  `WilkiesDesign.CG.G4_zero` of `Submission.Work.Wilkies.CG.Spec`, with the conclusion
  identical to the frozen statement (`G4_zero_proved`).  No hypotheses from other areas
  are needed.
-/
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign WilkiesConjecture

/-- The (only) chart for the case `n = 0`: the empty family of coordinates. -/
def zeroChart (p : ℕ) : Fin 0 → (Fin p → ℝ) → (Fin 0 → ℝ) → ℝ :=
  fun j => Fin.elim0 j

@[simp] theorem zeroChart_apply (p : ℕ) (j : Fin 0) :
    zeroChart p j = Fin.elim0 j := rfl

/-- Any two maps out of `Fin 0` are equal. -/
theorem zeroChart_subsingleton {α : Sort*} (f g : Fin 0 → α) : f = g :=
  Subsingleton.elim f g

/-- `openCube 0` is everything. -/
@[simp] theorem openCube_zero_eq_univ : (openCube 0 : Set (Fin 0 → ℝ)) = Set.univ := by
  ext x
  simp [openCube]

/-- **`G4_zero` (BNZ Lemma 5.1, case `n = 0`): trivial.** The only chart is the empty
family of coordinates; the cube `openCube 0` is a single point, so the `ε`-cover is exact. -/
theorem G4_zero_proved (S : SOMin) (p : ℕ) : FLem S p 0 := by
  intro F0
  refine ⟨F0, 1, 1, ?_⟩
  intro D r k ε hε _hε1 Λ F _hgraph hI
  refine ⟨{zeroChart p}, ?_, ?_, ?_⟩
  · rw [Finset.card_singleton]
    simp
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    refine ⟨fun j => Fin.elim0 j, fun l hl => ⟨?_, ?_⟩⟩
    · intro t _
      simp [openCube]
    · intro i
      have hconst : (fun t : Fin 0 → ℝ => F i l (fun j => zeroChart p j l t)) =
          (fun _ : Fin 0 → ℝ => F i l (fun _ => (0 : ℝ))) := by
        funext t
        congr 1
        exact zeroChart_subsingleton _ _
      refine ⟨?_, ?_⟩
      · rw [hconst]; exact contDiffOn_const
      · intro m _hm t _
        rw [hconst]
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          have hx : (fun _ : Fin 0 => (0 : ℝ)) ∈ openCube 0 := by simp [openCube]
          have hmem := hI i l hl (fun _ => (0 : ℝ)) hx
          rw [abs_of_pos hmem.1]
          exact hmem.2.le
        · rw [iteratedFDeriv_const_of_ne (by omega) (F i l (fun _ => (0 : ℝ)))]
          simp
  · intro l hl x hx
    refine ⟨zeroChart p, Finset.mem_singleton_self _, x, ?_, ?_⟩
    · exact hx
    · intro i
      have hx0 : (fun j => zeroChart p j l x) = x := zeroChart_subsingleton _ _
      rw [hx0, sub_self, abs_zero]
      exact hε

end WilkiesDesign.CG
