import Mathlib
import Submission.Work.WilG4b.Basic

namespace Work.WilG4b

open WilkiesDesign

/-! ## Coordinates of a point of `StarSet`

The hypothesis of `starAt` is that a point built out of the scalar `t` and the vector `γv`
(by concatenating `t` in front of `γv`) lies in `StarSet f c d M`.  The four lemmas below
compute the individual coordinates of that point in terms of `t` and `γv`. -/

/-- The zeroth coordinate of `Fin.append (fun _ => t) γv` is `t`. -/
theorem starAt_append_zero {n : ℕ} (t : ℝ) (γv : Fin (n + 2) → ℝ) :
    (Fin.append (fun _ : Fin 1 => t) γv) (⟨(0 : Fin (n + 3)).1, by omega⟩ : Fin (1 + (n + 2)))
      = t := by
  have key : (⟨(0 : Fin (n + 3)).1, by omega⟩ : Fin (1 + (n + 2)))
      = Fin.castAdd (n + 2) (0 : Fin 1) := by
    apply Fin.ext; simp
  rw [key, Fin.append_left]

/-- The coordinate at the index `1 + (castAdd 2 j)` of `Fin.append (fun _ => t) γv` is
`γv` at `castAdd 2 j`. -/
theorem starAt_append_succ {n : ℕ} (t : ℝ) (γv : Fin (n + 2) → ℝ) (j : Fin n) :
    (Fin.append (fun _ : Fin 1 => t) γv) (⟨(Fin.castAdd 2 j.succ).1, by omega⟩ : Fin (1 + (n + 2)))
      = γv (Fin.castAdd 2 j) := by
  have key : (⟨(Fin.castAdd 2 j.succ).1, by omega⟩ : Fin (1 + (n + 2)))
      = Fin.natAdd 1 (Fin.castAdd 2 j) := by
    apply Fin.ext; simp [Fin.castAdd, Fin.natAdd]; omega
  rw [key, Fin.append_right]

/-- The coordinate at the index `n + 1` of `Fin.append (fun _ => t) γv` is `γv ⟨n, _⟩`. -/
theorem starAt_append_n1 {n : ℕ} (t : ℝ) (γv : Fin (n + 2) → ℝ) :
    (Fin.append (fun _ : Fin 1 => t) γv)
        (⟨(⟨n + 1, by omega⟩ : Fin (n + 3)).1, by omega⟩ : Fin (1 + (n + 2)))
      = γv ⟨n, by omega⟩ := by
  have key : (⟨(⟨n + 1, by omega⟩ : Fin (n + 3)).1, by omega⟩ : Fin (1 + (n + 2)))
      = Fin.natAdd 1 (⟨n, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext; simp [Fin.natAdd]; omega
  rw [key, Fin.append_right]

/-- The last coordinate of `Fin.append (fun _ => t) γv` is `γv ⟨n + 1, _⟩`. -/
theorem starAt_append_last {n : ℕ} (t : ℝ) (γv : Fin (n + 2) → ℝ) :
    (Fin.append (fun _ : Fin 1 => t) γv) (⟨(Fin.last (n + 2)).1, by omega⟩ : Fin (1 + (n + 2)))
      = γv ⟨n + 1, by omega⟩ := by
  have key : (⟨(Fin.last (n + 2)).1, by omega⟩ : Fin (1 + (n + 2)))
      = Fin.natAdd 1 (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext; simp [Fin.natAdd]; omega
  rw [key, Fin.append_right]

theorem starAt {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} {c d M t : ℝ} {γv : Fin (n + 2) → ℝ}
    (h : (Fin.append (fun _ : Fin 1 => t) γv) ∘
        (fun i : Fin (n + 3) => (⟨i.1, by omega⟩ : Fin (1 + (n + 2)))) ∈
      Work.WilG4b.StarSet f c d M) :
    ∃ (y : Fin n → ℝ) (w u : ℝ), t ∈ Set.Ioo c d ∧ y ∈ WilkiesDesign.openCube n ∧
      (∀ j : Fin n, y j = γv (Fin.castAdd 2 j)) ∧ w = γv ⟨n, by omega⟩ ∧
      u = γv ⟨n + 1, by omega⟩ ∧
      Fin.snoc (Fin.cons t y) w ∈ WilkiesDesign.graphOf f ∧ 0 ≤ u ∧
      (∃ w₀ : ℝ, Fin.snoc (Fin.cons t y) w₀ ∈ Work.WilG4b.derivGraph f 0 ∧
          M * (1 + n * u) < |w₀|) ∧
      (∀ j : Fin n, ∃ wj : ℝ, Fin.snoc (Fin.cons t y) wj ∈ Work.WilG4b.derivGraph f j.succ ∧
          |wj| ≤ u) := by
  classical
  set V : Fin (n + 3) → ℝ :=
    (Fin.append (fun _ : Fin 1 => t) γv) ∘
      (fun i : Fin (n + 3) => (⟨i.1, by omega⟩ : Fin (1 + (n + 2)))) with hV
  have hVmem : V ∈ StarSet f c d M := h
  simp only [StarSet, Set.mem_ofPred_eq] at hVmem
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hVmem
  -- coordinates of `V`
  have hV0 : V 0 = t := by
    rw [hV]; simp only [Function.comp_apply]
    exact starAt_append_zero t γv
  have hVs : ∀ j : Fin n, V (Fin.castAdd 2 j.succ) = γv (Fin.castAdd 2 j) := by
    intro j
    rw [hV]; simp only [Function.comp_apply]
    exact starAt_append_succ t γv j
  have hVn1 : V ⟨n + 1, by omega⟩ = γv ⟨n, by omega⟩ := by
    rw [hV]; simp only [Function.comp_apply]
    exact starAt_append_n1 t γv
  have hVlast : V (Fin.last (n + 2)) = γv ⟨n + 1, by omega⟩ := by
    rw [hV]; simp only [Function.comp_apply]
    exact starAt_append_last t γv
  let y : Fin n → ℝ := fun j => V (Fin.castAdd 2 j.succ)
  let w : ℝ := V ⟨n + 1, by omega⟩
  let u : ℝ := V (Fin.last (n + 2))
  -- `Fin.init (Fin.init V) = Fin.cons t y`
  have hB : Fin.init (Fin.init V) = Fin.cons t y := by
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [Fin.cons_zero]
      change V ((Fin.castSucc (0 : Fin (n + 1))).castSucc) = t
      have hk0 : ((Fin.castSucc (0 : Fin (n + 1))).castSucc : Fin (n + 3)) = (0 : Fin (n + 3)) := by
        apply Fin.ext; simp [Fin.castSucc]
      rw [hk0, hV0]
    · intro j
      rw [Fin.cons_succ]
      change V ((Fin.castSucc j.succ).castSucc) = y j
      have hkj : ((Fin.castSucc j.succ).castSucc : Fin (n + 3)) = Fin.castAdd 2 j.succ := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd]
      rw [hkj]
  -- `Fin.init V = Fin.snoc (Fin.cons t y) w`
  have hA : Fin.init V = Fin.snoc (Fin.cons t y) w := by
    have hh := Fin.snoc_init_self (Fin.init V)
    rw [hB] at hh
    have hlast : Fin.init V (Fin.last (n + 1)) = w := by
      change V ((Fin.last (n + 1)).castSucc) = w
      have hkl : ((Fin.last (n + 1)).castSucc : Fin (n + 3))
          = (⟨n + 1, by omega⟩ : Fin (n + 3)) := by
        apply Fin.ext; simp [Fin.last]
      rw [hkl]
    rw [hlast] at hh
    exact hh.symm
  refine ⟨y, w, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hV0]; exact h1
  · exact h2
  · intro j; exact hVs j
  · exact hVn1
  · exact hVlast
  · rw [← hA]; exact h3
  · exact h4
  · obtain ⟨w₀, hm, hlt⟩ := h5
    exact ⟨w₀, by rw [← hB]; exact hm, hlt⟩
  · intro j
    obtain ⟨wj, hm, hle⟩ := h6 j
    exact ⟨wj, by rw [← hB]; exact hm, hle⟩

end Work.WilG4b
