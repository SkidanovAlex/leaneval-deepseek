import Mathlib

namespace Work.WilE7.FrontierCS

/-- Auxiliary induction statement for `multiAffine_eq_zero`.

A function `f : (Fin m → ℝ) → ℝ` which is affine in each coordinate separately and which
vanishes at every vertex of the cube `{0,1}^m` is identically zero. -/
lemma multiAffine_aux : ∀ (m : ℕ) (f : (Fin m → ℝ) → ℝ),
    (∀ (x : Fin m → ℝ) (i : Fin m) (t : ℝ), f (Function.update x i t) =
      f (Function.update x i 0) + t * (f (Function.update x i 1) - f (Function.update x i 0))) →
    (∀ b : Fin m → Bool, f (fun i => if b i then 1 else 0) = 0) →
    ∀ x, f x = 0 := by
  intro m
  induction m with
  | zero =>
    intro f haff hcube x
    have hx : x = (fun i : Fin 0 => if (fun _ : Fin 0 => false) i then (1 : ℝ) else 0) := by
      funext i
      exact Fin.elim0 i
    rw [hx]
    exact hcube (fun _ => false)
  | succ m ih =>
    intro f haff hcube x
    -- `y ↦ f (Fin.cons 0 y)` is affine in each coordinate and vanishes on the cube.
    have hA : ∀ y : Fin m → ℝ, f (Fin.cons (0 : ℝ) y) = 0 := by
      refine ih (fun y : Fin m → ℝ => f (Fin.cons (0 : ℝ) y)) ?_ ?_
      · intro y i t
        simp only [Fin.cons_update]
        exact haff (Fin.cons (0 : ℝ) y) i.succ t
      · intro c
        have h : (Fin.cons (0 : ℝ) (fun i : Fin m => if c i then (1 : ℝ) else 0) :
              Fin (m + 1) → ℝ) =
            (fun j : Fin (m + 1) =>
              if ((Fin.cons false c : Fin (m + 1) → Bool)) j then (1 : ℝ) else 0) := by
          funext j
          cases j using Fin.cases <;> simp
        rw [h]
        exact hcube (Fin.cons false c)
    -- `y ↦ f (Fin.cons 1 y)` is affine in each coordinate and vanishes on the cube.
    have hB : ∀ y : Fin m → ℝ, f (Fin.cons (1 : ℝ) y) = 0 := by
      refine ih (fun y : Fin m → ℝ => f (Fin.cons (1 : ℝ) y)) ?_ ?_
      · intro y i t
        simp only [Fin.cons_update]
        exact haff (Fin.cons (1 : ℝ) y) i.succ t
      · intro c
        have h : (Fin.cons (1 : ℝ) (fun i : Fin m => if c i then (1 : ℝ) else 0) :
              Fin (m + 1) → ℝ) =
            (fun j : Fin (m + 1) =>
              if ((Fin.cons true c : Fin (m + 1) → Bool)) j then (1 : ℝ) else 0) := by
          funext j
          cases j using Fin.cases <;> simp
        rw [h]
        exact hcube (Fin.cons true c)
    -- Affineness in the first coordinate closes the induction.
    rw [← Fin.cons_self_tail x]
    have h := haff (Fin.cons (x 0) (Fin.tail x)) 0 (x 0)
    simp only [Fin.update_cons_zero] at h
    rw [hA (Fin.tail x), hB (Fin.tail x)] at h
    simpa using h

theorem multiAffine_eq_zero {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (haff : ∀ (x : Fin m → ℝ) (i : Fin m) (t : ℝ), f (Function.update x i t) =
      f (Function.update x i 0) + t * (f (Function.update x i 1) - f (Function.update x i 0)))
    (hcube : ∀ b : Fin m → Bool, f (fun i => if b i then 1 else 0) = 0) :
    ∀ x, f x = 0 :=
  multiAffine_aux m f haff hcube

end Work.WilE7.FrontierCS
