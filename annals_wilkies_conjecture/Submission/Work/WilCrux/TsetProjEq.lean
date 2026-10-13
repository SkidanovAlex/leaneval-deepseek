import Mathlib
import Submission.Work.WilCrux.OmegaDefs
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux

open Work.WilG0

/-- Membership of a `snocIt`-vector in `Tset f ε`, expressed through the front vector `x` and
the tail vector `w`. -/
theorem mem_Tset_snocIt_iff {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (ε : ℝ)
    (x : Fin (a + 1) → ℝ) (w : Fin (a + b) → ℝ) :
    snocIt (a + 1) (a + b) x w ∈ Tset f ε ↔
      (∀ i : Fin a, |Fin.init x i - w (Fin.castAdd b i)| < x (Fin.last a)) ∧
      (fun j : Fin b => w (Fin.natAdd a j)) ≠ 0 ∧
      (∀ j : Fin b, |w (Fin.natAdd a j)| < x (Fin.last a)) ∧
      ¬ (|f (fun i : Fin a => w (Fin.castAdd b i)) (fun j : Fin b => w (Fin.natAdd a j))| < ε) := by
  simp only [Tset, Set.mem_ofPred_eq, etaIdx, centreIdx, upperIdx, fibreIdx, famLift,
    Fin.init_def, snocIt_castAdd, snocIt_natAdd]

theorem TsetProjEq {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (ε : ℝ) :
    Work.WilG0.projLastIter (a + 1) (a + b) (Work.WilCrux.Tset f ε) =
      {p : Fin (a + 1) → ℝ | ∃ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        (∀ i : Fin a, |Fin.init p i - w' i| < p (Fin.last a)) ∧ z ≠ 0 ∧
        (∀ j : Fin b, |z j| < p (Fin.last a)) ∧ ¬ (|f w' z| < ε)} := by
  rw [Work.WilG0.projLastIter_eq]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_Tset_snocIt_iff] at hw
    exact ⟨fun i : Fin a => w (Fin.castAdd b i), fun j : Fin b => w (Fin.natAdd a j),
      hw.1, hw.2.1, hw.2.2.1, hw.2.2.2⟩
  · rintro ⟨w', z, h1, h2, h3, h4⟩
    refine ⟨Fin.append w' z, ?_⟩
    rw [mem_Tset_snocIt_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [Fin.append_left]
      exact h1 i
    · have hz : (fun j : Fin b => Fin.append w' z (Fin.natAdd a j)) = z := by
        funext j; rw [Fin.append_right]
      rw [hz]; exact h2
    · intro j
      rw [Fin.append_right]
      exact h3 j
    · have hw'e : (fun i : Fin a => Fin.append w' z (Fin.castAdd b i)) = w' := by
        funext i; rw [Fin.append_left]
      have hz : (fun j : Fin b => Fin.append w' z (Fin.natAdd a j)) = z := by
        funext j; rw [Fin.append_right]
      rw [hw'e, hz]
      exact h4

end Work.WilCrux
