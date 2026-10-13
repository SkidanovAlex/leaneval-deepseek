/-
  Area E7, module `Submission.Work.WilE7.Deg.SeqLemmas`: the elementary properties of the format and
  degree sequences of `Submission.Work.WilE7.Deg.Seq`, plus the domination of the child bounds by
  `chpoly` and the order theory of the fibrewise closure used in the assembly.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.Deg.Bounds
import Submission.Work.WilE7.Deg.Seq

set_option autoImplicit false
noncomputable section
open Classical Topology
open scoped Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The format sequence -/

theorem fmtSeq_mono (hE5 : E5Interface) (hE6 : E6Interface) (A₀ : ℕ) :
    Monotone (fmtSeq hE5 hE6 A₀) := by
  apply monotone_nat_of_le_succ
  intro t
  show fmtSeq hE5 hE6 A₀ t ≤ fmtSeq hE5 hE6 A₀ (t + 1)
  rw [show fmtSeq hE5 hE6 A₀ (t + 1) = fmtStep hE5 hE6 (fmtSeq hE5 hE6 A₀ t) from rfl]
  exact le_max_left _ _

theorem Fb_succ (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀) :
    Fb hE5 hE6 A₀ k₀ k = fmtStep hE5 hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)) := by
  show fmtSeq hE5 hE6 A₀ (k₀ - k) = fmtStep hE5 hE6 (fmtSeq hE5 hE6 A₀ (k₀ - (k + 1)))
  rw [show k₀ - k = (k₀ - (k + 1)) + 1 by omega]
  rfl

theorem Pb_succ (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀) :
    Pb hE5 hE6 A₀ k₀ k
      = degStep hE5 hE6 A₀ (Fb hE5 hE6 A₀ k₀ (k + 1)) (Pb hE5 hE6 A₀ k₀ (k + 1)) := by
  show degSeq hE5 hE6 A₀ (k₀ - k)
      = degStep hE5 hE6 A₀ (fmtSeq hE5 hE6 A₀ (k₀ - (k + 1)))
          (degSeq hE5 hE6 A₀ (k₀ - (k + 1)))
  rw [show k₀ - k = (k₀ - (k + 1)) + 1 by omega]
  rfl

theorem Fb_ge_A₀ (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) :
    A₀ ≤ Fb hE5 hE6 A₀ k₀ k := by
  show A₀ ≤ fmtSeq hE5 hE6 A₀ (k₀ - k)
  have h := fmtSeq_mono hE5 hE6 A₀ (Nat.zero_le (k₀ - k))
  rw [show fmtSeq hE5 hE6 A₀ 0 = A₀ from rfl] at h
  exact h

theorem e5fmt_Fb_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀) :
    e5fmt hE5 (Fb hE5 hE6 A₀ k₀ (k + 1)) ≤ Fb hE5 hE6 A₀ k₀ k := by
  rw [Fb_succ hE5 hE6 A₀ k₀ k hk, fmtStep]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem e5fmt_e6fmt_Fb_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀) :
    e5fmt hE5 (e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1))) ≤ Fb hE5 hE6 A₀ k₀ k := by
  rw [Fb_succ hE5 hE6 A₀ k₀ k hk, fmtStep]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem Fb_self_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀) :
    Fb hE5 hE6 A₀ k₀ (k + 1) ≤ Fb hE5 hE6 A₀ k₀ k := by
  rw [Fb_succ hE5 hE6 A₀ k₀ k hk, fmtStep]
  exact le_max_left _ _

/-! ## The degree sequence -/

theorem degSeq_eval_ge (hE5 : E5Interface) (hE6 : E6Interface) (A₀ D : ℕ) :
    ∀ t, D ≤ (degSeq hE5 hE6 A₀ t).eval D := by
  intro t
  induction t with
  | zero =>
      show D ≤ (Polynomial.X : Polynomial ℕ).eval D
      simp
  | succ t ih =>
      show D ≤ (degSeq hE5 hE6 A₀ (t + 1)).eval D
      rw [show degSeq hE5 hE6 A₀ (t + 1)
            = degStep hE5 hE6 A₀ (fmtSeq hE5 hE6 A₀ t) (degSeq hE5 hE6 A₀ t) from rfl,
        degStep, Polynomial.eval_add]
      omega

/-! ## The budget-indexed sequences -/

theorem Pb_succ_eval (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀)
    (D : ℕ) :
    (Pb hE5 hE6 A₀ k₀ k).eval D
      = (Pb hE5 hE6 A₀ k₀ (k + 1)).eval D + (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by
  rw [Pb_succ hE5 hE6 A₀ k₀ k hk, degStep, Polynomial.eval_add]
  rfl

theorem brB_eval_ge_one (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ j D : ℕ) :
    1 ≤ (brB hE5 hE6 A₀ k₀ j).eval D := by
  show 1 ≤ (chpoly hE5 hE6 A₀ (Fb hE5 hE6 A₀ k₀ j) (Pb hE5 hE6 A₀ k₀ j)).eval D
  simp only [chpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one]
  omega

theorem Kb_eval_mono (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ D : ℕ) :
    Monotone (fun j => (Kb hE5 hE6 A₀ k₀ j).eval D) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [show Kb hE5 hE6 A₀ k₀ (j + 1) = brB hE5 hE6 A₀ k₀ (j + 1) * Kb hE5 hE6 A₀ k₀ j from rfl,
    Polynomial.eval_mul]
  exact Nat.le_mul_of_pos_left _
    (by have := brB_eval_ge_one hE5 hE6 A₀ k₀ (j + 1) D; omega)

/-! ## The child bounds dominate -/

theorem chpoly_frontier_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ F : ℕ)
    (p : Polynomial ℕ) (D : ℕ) :
    ((e5deg hE5 (e6fmt hE6 F)).comp ((e6deg hE6 F).comp p)).eval D
      ≤ (chpoly hE5 hE6 A₀ F p).eval D := by
  simp only [chpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp]
  omega

theorem chpoly_crit_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ F : ℕ)
    (p : Polynomial ℕ) (D : ℕ) :
    ((e5deg hE5 F).comp ((cdpoly F).comp p)).eval D ≤ (chpoly hE5 hE6 A₀ F p).eval D := by
  simp only [chpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp]
  have h : (e5deg hE5 F).eval ((cdpoly F).eval (p.eval D))
      ≤ (A₀ + 1) * (e5deg hE5 F).eval ((cdpoly F).eval (p.eval D)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos A₀)
  omega

theorem chpoly_crit_mul_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ F : ℕ)
    (p : Polynomial ℕ) (D : ℕ) (mm : ℕ) (hm : mm ≤ A₀) :
    mm * ((e5deg hE5 F).comp ((cdpoly F).comp p)).eval D
      ≤ (chpoly hE5 hE6 A₀ F p).eval D := by
  simp only [chpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp]
  have h2 : mm * (e5deg hE5 F).eval ((cdpoly F).eval (p.eval D))
      ≤ (A₀ + 1) * (e5deg hE5 F).eval ((cdpoly F).eval (p.eval D)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem chpoly_count_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ F : ℕ)
    (p : Polynomial ℕ) (D : ℕ) :
    ((e5deg hE5 (e6fmt hE6 F)).comp ((e6deg hE6 F).comp p)).eval D
        + A₀ * ((e5deg hE5 F).comp ((cdpoly F).comp p)).eval D
      ≤ (chpoly hE5 hE6 A₀ F p).eval D := by
  simp only [chpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp]
  have h : A₀ * (e5deg hE5 F).eval ((cdpoly F).eval (p.eval D))
      ≤ (A₀ + 1) * (e5deg hE5 F).eval ((cdpoly F).eval (p.eval D)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem brB_eval_le_Pb (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀)
    (D : ℕ) :
    (brB hE5 hE6 A₀ k₀ (k + 1)).eval D ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
  rw [Pb_succ_eval hE5 hE6 A₀ k₀ k hk D]
  omega

theorem Pb_eval_le (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ k : ℕ) (hk : k < k₀) (D : ℕ) :
    (Pb hE5 hE6 A₀ k₀ (k + 1)).eval D ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
  rw [Pb_succ_eval hE5 hE6 A₀ k₀ k hk D]
  omega

/-! ## Fibrewise closures of children -/

/-- A child whose set lies in the fibrewise closure of the parent keeps its own fibrewise closure
inside the parent's. -/
theorem image_fiberClosure_le_of_subset {n m : ℕ} {A B : Set (Fin (n + m) → ℝ)} (h : A ⊆ B) :
    projFirst n m '' fiberClosure A ⊆ projFirst n m '' fiberClosure B :=
  Set.image_mono (Deg.fiberClosure_mono h)

/-- A child lying in the frontier of the parent: its fibrewise closure stays inside the parent's
(using idempotence of the fibrewise closure). -/
theorem image_fiberClosure_le_of_subset_frontier {n m : ℕ} {A B : Set (Fin (n + m) → ℝ)}
    (h : A ⊆ fiberClosure B \ B) :
    projFirst n m '' fiberClosure A ⊆ projFirst n m '' fiberClosure B := by
  have h' : A ⊆ fiberClosure B := h.trans Set.diff_subset
  have h2 : fiberClosure A ⊆ fiberClosure (fiberClosure B) := Deg.fiberClosure_mono h'
  rw [Deg.fiberClosure_idem] at h2
  exact Set.image_mono h2

end Work.WilE7
