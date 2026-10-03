import Mathlib
import Submission.Work.Pert.AsmDefs
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.pert2v2.RCloseTwoPiece` — `PertData.R_close` for the two-piece return map

`PertData.R_close` reads `∀ w ∈ K ∪ {y₁ ≤ |w.im|}, ‖R w + 1/rotOf f - d.E w‖ < δ`.

For the glued two-piece `R` (`pert2v2.twoPieceR_overlap`) the work splits in two, and only the
second half is shared:

* **the two chart estimates** `‖Rlow w + 1/α - d.E w‖ < δ` on `Ulow` (crux residual + (A.4.4),
  `pert2v2.Rlow_close_of_res`) and `‖Rhigh w + 1/α - d.E w‖ < δ` on `Uhigh`
  (`pert2v2.high_band_R_close_v2`);
* **the transport along the `ℤ`-saturation**: every `w ∈ DR` is an integer translate of a chart
  point, and both `R` (`T`-equivariance) and `d.E` (`ParabData.E_add_one`) shift by the same `n`, so
  `R w + 1/α - d.E w = R z + 1/α - d.E z`.  Here `IsTInvariant DR` makes the walk automatic: it is
  closed under `±1`, so *every* intermediate point of the translate stays in `DR`.

This file proves the transport step (the shared skeleton); the two estimates are supplied by the
caller.  Note that the height split of `DR_sub_overlap` (§11.1) is not needed here: the transport
works for every `w ∈ DR` at once.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- **Translating a `T`-equivariant map along the `ℤ`-saturation**: for `u ∈ DR` (which is
`T`-invariant, so the whole translate stays inside), `R (u + n) = R u + n` for every `n : ℤ`. -/
theorem TEquivOn_add_int {R : ℂ → ℂ} {DR : Set ℂ} (h : MandelDim.IsTEquivariantOn R DR)
    (n : ℤ) {u : ℂ} (hu : u ∈ DR) : R (u + (n : ℂ)) = R u + (n : ℂ) := by
  classical
  have hstep : ∀ x ∈ DR, x + 1 ∈ DR := fun x hx => (h.1 x).mp hx
  have hstep' : ∀ x ∈ DR, x - 1 ∈ DR := fun x hx => (h.1 (x - 1)).mpr (by simpa using hx)
  -- forward
  have hfwd : ∀ (u : ℂ), u ∈ DR → ∀ m : ℕ,
      (u + (m : ℂ) ∈ DR) ∧ R (u + (m : ℂ)) = R u + (m : ℂ) := by
    intro u hu m
    induction m with
    | zero => exact ⟨by simpa using hu, by simp⟩
    | succ k ih =>
      have hk : u + (k : ℂ) ∈ DR := ih.1
      have h1 : u + ((k + 1 : ℕ) : ℂ) = (u + (k : ℂ)) + 1 := by push_cast; ring
      refine ⟨by rw [h1]; exact hstep _ hk, ?_⟩
      rw [h1, h.2 _ hk, ih.2]
      push_cast; ring
  -- backward
  have hbwd : ∀ (u : ℂ), u ∈ DR → ∀ m : ℕ,
      R (u - (m : ℂ)) = R u - (m : ℂ) := by
    intro u hu m
    induction m with
    | zero => simp
    | succ k ih =>
      have hk : u - (k : ℂ) ∈ DR := by
        clear ih
        induction k with
        | zero => simpa using hu
        | succ l ihl =>
          have h1 : u - ((l + 1 : ℕ) : ℂ) = (u - (l : ℂ)) - 1 := by push_cast; ring
          rw [h1]; exact hstep' _ ihl
      have h1 : u - ((k + 1 : ℕ) : ℂ) = (u - (k : ℂ)) - 1 := by push_cast; ring
      have h2 : ((u - (k : ℂ)) - 1) + 1 = u - (k : ℂ) := by ring
      have hst : R (u - (k : ℂ)) = R ((u - (k : ℂ)) - 1) + 1 := by
        have := h.2 ((u - (k : ℂ)) - 1) (hstep' _ hk)
        rwa [h2] at this
      have hgoal : R ((u - (k : ℂ)) - 1) = R (u - (k : ℂ)) - 1 :=
        eq_sub_iff_add_eq.mpr hst.symm
      rw [h1, hgoal, ih]
      push_cast; ring
  rcases lt_or_ge n 0 with hn | hn
  · -- `n < 0`: write the shift as a subtraction and run the backward walk
    have hkey : u + (n : ℂ) = u - (((-n).toNat : ℕ) : ℂ) := by
      have hcast : (n : ℂ) = -((((-n).toNat : ℕ)) : ℂ) := by
        have hZ : n = -(((-n).toNat : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)]; ring
        exact_mod_cast hZ
      rw [hcast]; ring
    rw [hkey, hbwd u hu ((-n).toNat)]
    have hcast2 : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by
      have hZ : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)
      have := congrArg (fun z : ℤ => (z : ℂ)) hZ
      push_cast at this
      exact this
    rw [hcast2]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    subst hm
    exact (hfwd u hu m).2

/-- **Translating a `1`-periodic-difference map by an integer**: `E (u + n) = E u + n`. -/
theorem add_int_of_add_one {E : ℂ → ℂ} (hE : ∀ w : ℂ, E (w + 1) = E w + 1) (n : ℤ) (u : ℂ) :
    E (u + (n : ℂ)) = E u + (n : ℂ) := by
  classical
  have hfwd : ∀ m : ℕ, E (u + (m : ℂ)) = E u + (m : ℂ) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show u + ((k + 1 : ℕ) : ℂ) = (u + (k : ℂ)) + 1 from by push_cast; ring, hE, ih]
      push_cast; ring
  have hbwd : ∀ m : ℕ, E (u - (m : ℂ)) = E u - (m : ℂ) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have hst : E (u - (k : ℂ)) = E ((u - (k : ℂ)) - 1) + 1 := by
        have := hE ((u - (k : ℂ)) - 1)
        rwa [show ((u - (k : ℂ)) - 1) + 1 = u - (k : ℂ) from by ring] at this
      have hgoal : E ((u - (k : ℂ)) - 1) = E (u - (k : ℂ)) - 1 :=
        eq_sub_iff_add_eq.mpr hst.symm
      rw [show u - ((k + 1 : ℕ) : ℂ) = (u - (k : ℂ)) - 1 from by push_cast; ring, hgoal, ih]
      push_cast; ring
  rcases lt_or_ge n 0 with hn | hn
  · have hkey : u + (n : ℂ) = u - (((-n).toNat : ℕ) : ℂ) := by
      have hcast : (n : ℂ) = -((((-n).toNat : ℕ)) : ℂ) := by
        have hZ : n = -(((-n).toNat : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)]; ring
        exact_mod_cast hZ
      rw [hcast]; ring
    rw [hkey, hbwd ((-n).toNat)]
    have hcast2 : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by
      have hZ : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)
      have := congrArg (fun z : ℤ => (z : ℂ)) hZ
      push_cast at this
      exact this
    rw [hcast2]; ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    subst hm
    exact hfwd m

/-- **`PertData.R_close` for the two-piece return map, from the two chart estimates.**  Given that
`DR` is the `ℤ`-saturation of the two charts (`hDR`), that `R` agrees with the pieces there
(`hRlow`, `hRhigh`), that `R` is `T`-equivariant (`hequiv`) and that `d.E` shifts by `1`
(`hE`), the *same* shift `n` cancels in `R w + 1/α - d.E w`, so the estimate needed at `w` is the
one at its chart representative.  Proved in one go for both halves; the *height* split is only
needed to produce `hEstLow`/`hEstHigh`. -/
theorem R_close_twoPiece {R E Rlow Rhigh : ℂ → ℂ} {DR Ulow Uhigh K : Set ℂ} {α : ℂ} {y₁ δ : ℝ}
    (hequiv : MandelDim.IsTEquivariantOn R DR)
    (hE : ∀ w : ℂ, E (w + 1) = E w + 1)
    (hDR : DR = ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' (Ulow ∪ Uhigh))
    (hRlow : ∀ w : ℂ, w ∈ Ulow → R w = Rlow w)
    (hRhigh : ∀ w : ℂ, w ∈ Uhigh → R w = Rhigh w)
    (hEstLow : ∀ w : ℂ, w ∈ Ulow → ‖Rlow w + 1 / α - E w‖ < δ)
    (hEstHigh : ∀ w : ℂ, w ∈ Uhigh → ‖Rhigh w + 1 / α - E w‖ < δ)
    (hband : K ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ DR) :
    ∀ w ∈ K ∪ {w : ℂ | y₁ ≤ |w.im|}, ‖R w + 1 / α - E w‖ < δ := by
  intro w hw
  have hwDR : w ∈ DR := hband hw
  rw [hDR] at hwDR
  simp only [Set.mem_iUnion, Set.mem_image] at hwDR
  obtain ⟨n, z, hzU, hzw⟩ := hwDR
  -- `w = z + n` with `z` in a chart
  have hwz : w = z + (n : ℂ) := hzw.symm
  have hzDR : z ∈ DR := by
    rw [hDR]
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    simpa using Set.mem_image_of_mem (fun u : ℂ => u + ((0 : ℤ) : ℂ)) hzU
  have hRw : R w = R z + (n : ℂ) := by rw [hwz]; exact TEquivOn_add_int hequiv n hzDR
  have hEw : E w = E z + (n : ℂ) := by rw [hwz]; exact add_int_of_add_one hE n z
  have harith : R z + (n : ℂ) + 1 / α - (E z + (n : ℂ)) = R z + 1 / α - E z := by ring
  rw [hRw, hEw, harith]
  rcases hzU with hzU | hzU
  · rw [hRlow z hzU]; exact hEstLow z hzU
  · rw [hRhigh z hzU]; exact hEstHigh z hzU

end

end Work.Pert.pert2v2
