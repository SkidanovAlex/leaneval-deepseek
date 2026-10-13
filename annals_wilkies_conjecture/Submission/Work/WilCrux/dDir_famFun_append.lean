import Mathlib
import Submission.Work.WilCrux.fibreFderivFamFun
import Submission.Work.WilG4b.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

lemma dDir_famFun_append {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ) (j : Fin b)
    (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z)
      = fderiv ℝ (G w) z (Pi.single j 1) := by
  rw [Work.WilG4b.dDir]
  have h := fibreFderivFamFun (a := a) (b := b) G w z (Pi.single j 1) hd
  rw [← h]
  congr 1
  have hc1 : ∀ i : Fin a, (Fin.castAdd b i : Fin (a + b)).val = i.val := fun i => rfl
  have hn : ∀ j' : Fin b, (Fin.natAdd a j' : Fin (a + b)).val = a + j'.val := fun j' => rfl
  have key : (Pi.single (Fin.natAdd a j) (1:ℝ) : Fin (a+b) → ℝ)
      = Fin.append (0 : Fin a → ℝ) (Pi.single j (1:ℝ)) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) k
    · rw [Fin.append_left,
        Pi.single_eq_of_ne (i := Fin.natAdd a j) (h := by
          intro hcl
          have hv := congrArg Fin.val hcl
          rw [hc1 i, hn j] at hv
          omega)]
      rfl
    · rw [Fin.append_right]
      by_cases hj : j' = j
      · subst hj; simp
      · rw [Pi.single_eq_of_ne (i := Fin.natAdd a j) (h := by
              intro hcl
              apply hj
              apply Fin.ext
              have hv := congrArg Fin.val hcl
              rw [hn j', hn j] at hv
              omega),
            Pi.single_eq_of_ne (i := j) (h := hj)]
  exact key

end Work.WilCrux
