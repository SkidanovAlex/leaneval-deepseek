/-
  WilE6: the block decomposition of the fibre `Fin (FQ k p)` of `critSA`.

  The fibre of `critSA` is `(u, t, wm, w0, wb, we)` with block sizes
  `k, 1, k, 1, 2p, 2`.  `CritSA.lean` names the corresponding coordinates of the *ambient*
  space `Fin (BP k r + FQ k p)` (`idxU`, `idxT`, …); this file names the same coordinates
  inside the fibre `Fin (FQ k p)` (`fU`, `fT`, …), defines the projection `projU` onto the
  `u`-block, proves the bridges between the two naming schemes, and proves that the six blocks
  cover the whole fibre.
-/
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.Base

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The `u`-block of the fibre. -/
def fU (k p : ℕ) (i : Fin k) : Fin (FQ k p) := ⟨i.1, by simp [FQ]; omega⟩
/-- The `t`-coordinate of the fibre. -/
def fT (k p : ℕ) : Fin (FQ k p) := ⟨k, by simp [FQ]; omega⟩
/-- The `wm`-block of the fibre. -/
def fWm (k p : ℕ) (i : Fin k) : Fin (FQ k p) := ⟨k + 1 + i.1, by simp [FQ]; omega⟩
/-- The `w0`-coordinate of the fibre. -/
def fW0 (k p : ℕ) : Fin (FQ k p) := ⟨2 * k + 1, by simp [FQ]; omega⟩
/-- The `wb`-block of the fibre. -/
def fWb (k p : ℕ) (b : Fin (2 * p)) : Fin (FQ k p) := ⟨2 * k + 2 + b.1, by simp [FQ]; omega⟩
/-- The `we`-block of the fibre. -/
def fWe (k p : ℕ) (e : Fin 2) : Fin (FQ k p) := ⟨2 * k + 2 + 2 * p + e.1, by simp [FQ]; omega⟩

/-- The projection of a fibre point onto its `u`-coordinates. -/
def projU (k p : ℕ) (v : Fin (FQ k p) → ℝ) : Fin k → ℝ := fun i => v (fU k p i)

variable {k r p : ℕ}

@[simp] theorem fU_val (i : Fin k) : (fU k p i : ℕ) = i.1 := rfl
@[simp] theorem fT_val : (fT k p : ℕ) = k := rfl
@[simp] theorem fWm_val (i : Fin k) : (fWm k p i : ℕ) = k + 1 + i.1 := rfl
@[simp] theorem fW0_val : (fW0 k p : ℕ) = 2 * k + 1 := rfl
@[simp] theorem fWb_val (b : Fin (2 * p)) : (fWb k p b : ℕ) = 2 * k + 2 + b.1 := rfl
@[simp] theorem fWe_val (e : Fin 2) : (fWe k p e : ℕ) = 2 * k + 2 + 2 * p + e.1 := rfl

/-- The bridge between the ambient coordinate `idxU` and the fibre coordinate `fU`. -/
theorem idxU_eq_natAdd (i : Fin k) :
    idxU k r p i = Fin.natAdd (BP k r) (fU k p i) := by
  apply Fin.ext; show BP k r + i.1 = BP k r + i.1; omega

theorem idxT_eq_natAdd : idxT k r p = Fin.natAdd (BP k r) (fT k p) := by
  apply Fin.ext; show BP k r + k = BP k r + k; omega

theorem idxWm_eq_natAdd (i : Fin k) :
    idxWm k r p i = Fin.natAdd (BP k r) (fWm k p i) := by
  apply Fin.ext; show BP k r + k + 1 + i.1 = BP k r + (k + 1 + i.1); omega

theorem idxW0_eq_natAdd : idxW0 k r p = Fin.natAdd (BP k r) (fW0 k p) := by
  apply Fin.ext; show BP k r + 2 * k + 1 = BP k r + (2 * k + 1); omega

theorem idxWb_eq_natAdd (b : Fin (2 * p)) :
    idxWb k r p b = Fin.natAdd (BP k r) (fWb k p b) := by
  apply Fin.ext; show BP k r + 2 * k + 2 + b.1 = BP k r + (2 * k + 2 + b.1); omega

theorem idxWe_eq_natAdd (e : Fin 2) :
    idxWe k r p e = Fin.natAdd (BP k r) (fWe k p e) := by
  apply Fin.ext
  show BP k r + 2 * k + 2 + 2 * p + e.1 = BP k r + (2 * k + 2 + 2 * p + e.1); omega

/-- The `u`-coordinates of `Fin.append (graphPt c z) v`. -/
theorem append_gp_idxU (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (i : Fin k) :
    Fin.append (graphPt c z) v (idxU k r p i) = v (fU k p i) := by
  rw [idxU_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem append_gp_idxT (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) :
    Fin.append (graphPt c z) v (idxT k r p) = v (fT k p) := by
  rw [idxT_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem append_gp_idxWm (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ)
    (i : Fin k) :
    Fin.append (graphPt c z) v (idxWm k r p i) = v (fWm k p i) := by
  rw [idxWm_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem append_gp_idxW0 (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) :
    Fin.append (graphPt c z) v (idxW0 k r p) = v (fW0 k p) := by
  rw [idxW0_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem append_gp_idxWb (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ)
    (b : Fin (2 * p)) :
    Fin.append (graphPt c z) v (idxWb k r p b) = v (fWb k p b) := by
  rw [idxWb_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

theorem append_gp_idxWe (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ)
    (e : Fin 2) :
    Fin.append (graphPt c z) v (idxWe k r p e) = v (fWe k p e) := by
  rw [idxWe_eq_natAdd]; first | rfl | exact Fin.append_right _ _ _

/-- The `z`-coordinates of `Fin.append (graphPt c z) v` are those of `z`. -/
theorem append_gp_idxZ (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (i : Fin k) :
    Fin.append (graphPt c z) v (idxZ k r p i) = z i := by
  have h1 : idxZ k r p i = Fin.castAdd (FQ k p) (Fin.castAdd r i) := Fin.ext rfl
  rw [h1, Fin.append_left, graphPt_castAdd]

theorem append_gp_idxH (c : EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ) (j : Fin r) :
    Fin.append (graphPt c z) v (idxH k r p j) = hvec c z j := by
  have h1 : idxH k r p j = Fin.castAdd (FQ k p) (Fin.natAdd k j) := Fin.ext rfl
  rw [h1, Fin.append_left, graphPt_natAdd]

/-- The six blocks cover the fibre `Fin (FQ k p)`. -/
theorem FQ_cover (i : Fin (FQ k p)) :
    (∃ j : Fin k, i = fU k p j) ∨ i = fT k p ∨ (∃ j : Fin k, i = fWm k p j) ∨
      i = fW0 k p ∨ (∃ b : Fin (2 * p), i = fWb k p b) ∨ (∃ e : Fin 2, i = fWe k p e) := by
  have hi : (i : ℕ) < 2 * k + 2 * p + 4 := by
    have h := i.2; simp only [FQ] at h; omega
  by_cases h1 : (i : ℕ) < k
  · exact Or.inl ⟨⟨i.1, h1⟩, Fin.ext rfl⟩
  · right
    by_cases h2 : (i : ℕ) = k
    · exact Or.inl (Fin.ext (by show (i : ℕ) = k; exact h2))
    · right
      have hk : k + 1 ≤ (i : ℕ) := by omega
      by_cases h3 : (i : ℕ) < 2 * k + 1
      · refine Or.inl ⟨⟨i.1 - k - 1, by omega⟩, Fin.ext ?_⟩
        show (i : ℕ) = k + 1 + (i.1 - k - 1)
        omega
      · right
        by_cases h4 : (i : ℕ) = 2 * k + 1
        · exact Or.inl (Fin.ext (by show (i : ℕ) = 2 * k + 1; exact h4))
        · right
          have hk2 : 2 * k + 2 ≤ (i : ℕ) := by omega
          by_cases h5 : (i : ℕ) < 2 * k + 2 + 2 * p
          · refine Or.inl ⟨⟨i.1 - (2 * k + 2), by omega⟩, Fin.ext ?_⟩
            show (i : ℕ) = 2 * k + 2 + (i.1 - (2 * k + 2))
            omega
          · refine Or.inr ⟨⟨i.1 - (2 * k + 2 + 2 * p), by omega⟩, Fin.ext ?_⟩
            show (i : ℕ) = 2 * k + 2 + 2 * p + (i.1 - (2 * k + 2 + 2 * p))
            omega

end Work.WilE6
