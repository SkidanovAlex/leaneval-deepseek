import Submission.Work.StemsB.CubePairStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The middle slab of the cube cover is `Iⁿ × (1/4,3/4) × Y`

The Mayer–Vietoris step (`Submission/Work/StemsB/CubePairStep.lean`) computes the relative homology
of `(I^{n+1} × Y, ∂I^{n+1} × Y)` as that of the middle slab `{1/4 < last < 3/4}` relative to its
boundary part.  This file identifies that pair with the pair `(Iⁿ × W, ∂Iⁿ × W)` for the parameter
space `W = (1/4,3/4) × Y`, by splitting off the last coordinate:

* `Work.StemsB.midTo`, `Work.StemsB.midFrom`, `Work.StemsB.midHomeo` — the homeomorphism;
* `Work.StemsB.midTo_mem_bdry`, `Work.StemsB.midFrom_mem_bdry` — it maps the boundary part to the
  boundary (the last coordinate of a point of the middle slab is never `0` or `1`).
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The boundary `∂Iᵏ × Y` of the `k`-cube, for a general number `k` of coordinates (the
definitions of `Submission/Work/StemsB/CubePairGeom.lean` are stated for the `(n+1)`-cube). -/
abbrev cubeBdryK (Y : Type) (k : ℕ) : Set (CubeP Y k) := {p | p.1 ∈ Cube.boundary (Fin k)}

/-- The parameter space obtained from the middle slab by removing the cube factor: `(1/4,3/4) × Y`. -/
abbrev midParam (Y : Type) : Type := ↥(Set.Ioo (1/4:ℝ) (3/4)) × Y

/-- The forward map of the identification of the middle slab with `Iⁿ × (1/4,3/4) × Y`. -/
def midTo (n : ℕ) (z : ↥(slabMid (Y := Y) n)) : CubeP (midParam Y) n :=
  (fun i : Fin n => z.1.1 i.castSucc,
   (⟨((z.1.1 (Fin.last n) : unitInterval) : ℝ), z.2.2, z.2.1⟩, z.1.2))

/-- The coordinates of a point of `Iⁿ × (1/4,3/4) × Y` viewed on the `(n+1)`-cube: the last
coordinate carries the interval parameter. -/
def midCoords (n : ℕ) (w : CubeP (midParam Y) n) : Fin (n+1) → unitInterval :=
  fun i => Fin.lastCases
    (⟨(w.2.1 : ℝ), le_trans (by norm_num) (le_of_lt w.2.1.2.1),
      le_of_lt (lt_trans w.2.1.2.2 (by norm_num))⟩ : unitInterval)
    (fun j => w.1 j) i

@[simp] theorem midCoords_castSucc (n : ℕ) (w : CubeP (midParam Y) n) (i : Fin n) :
    midCoords n w i.castSucc = w.1 i :=
  Fin.lastCases_castSucc i

@[simp] theorem midCoords_last (n : ℕ) (w : CubeP (midParam Y) n) :
    ((midCoords n w (Fin.last n) : unitInterval) : ℝ) = (w.2.1 : ℝ) := by
  simp only [midCoords, Fin.lastCases_last]

/-- The inverse map of the identification of the middle slab with `Iⁿ × (1/4,3/4) × Y`. -/
def midFrom (n : ℕ) (w : CubeP (midParam Y) n) : ↥(slabMid (Y := Y) n) :=
  ⟨(midCoords n w, w.2.2),
   ⟨by
      show ((midCoords n w (Fin.last n) : unitInterval) : ℝ) < 3/4
      rw [midCoords_last]; exact w.2.1.2.2,
    by
      show (1:ℝ)/4 < ((midCoords n w (Fin.last n) : unitInterval) : ℝ)
      rw [midCoords_last]; exact w.2.1.2.1⟩⟩

@[simp] theorem midTo_apply_castSucc (n : ℕ) (z : ↥(slabMid (Y := Y) n)) (i : Fin n) :
    (midTo n z).1 i = z.1.1 i.castSucc := rfl

@[simp] theorem midFrom_apply_castSucc (n : ℕ) (w : CubeP (midParam Y) n) (i : Fin n) :
    (midFrom n w).1.1 i.castSucc = w.1 i :=
  midCoords_castSucc n w i

@[simp] theorem midFrom_apply_last (n : ℕ) (w : CubeP (midParam Y) n) :
    ((midFrom n w).1.1 (Fin.last n) : ℝ) = (w.2.1 : ℝ) :=
  midCoords_last n w

theorem midTo_midFrom (n : ℕ) (w : CubeP (midParam Y) n) : midTo n (midFrom n w) = w := by
  apply Prod.ext
  · funext i
    exact midFrom_apply_castSucc n w i
  · apply Prod.ext
    · apply Subtype.ext
      exact midFrom_apply_last n w
    · rfl

theorem midFrom_midTo (n : ℕ) (z : ↥(slabMid (Y := Y) n)) : midFrom n (midTo n z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact midFrom_apply_castSucc n (midTo n z) j
    · apply Subtype.ext
      exact midFrom_apply_last n (midTo n z)
  · rfl

theorem continuous_midTo (n : ℕ) : Continuous (midTo (Y := Y) n) := by
  refine Continuous.prodMk (continuous_pi fun i => ?_) ?_
  · exact (continuous_apply i.castSucc).comp (continuous_fst.comp continuous_subtype_val)
  refine Continuous.prodMk ?_ (continuous_snd.comp continuous_subtype_val)
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp
    ((continuous_apply (Fin.last n)).comp (continuous_fst.comp continuous_subtype_val)))

theorem continuous_midFrom (n : ℕ) : Continuous (midFrom (Y := Y) n) := by
  refine Continuous.subtype_mk (Continuous.prodMk (continuous_pi fun i => ?_) (by fun_prop)) _
  induction i using Fin.lastCases with
  | last =>
      simp only [midCoords, Fin.lastCases_last]
      refine Continuous.subtype_mk (by fun_prop) _
  | cast j =>
      simp only [midCoords, Fin.lastCases_castSucc]
      exact (continuous_apply j).comp continuous_fst

/-- **The canonical homeomorphism** from the middle slab of the cover of `I^{n+1} × Y` to
`Iⁿ × ((1/4,3/4) × Y)`. -/
def midHomeo (n : ℕ) : ↥(slabMid (Y := Y) n) ≃ₜ CubeP (midParam Y) n where
  toEquiv :=
    { toFun := midTo n
      invFun := midFrom n
      left_inv := midFrom_midTo n
      right_inv := midTo_midFrom n }
  continuous_toFun := continuous_midTo n
  continuous_invFun := continuous_midFrom n

/-- The homeomorphism sends the boundary part of the middle slab into the boundary of
`Iⁿ × (1/4,3/4) × Y`: the last coordinate of a point of the middle slab is never `0` or `1`, so a
boundary coordinate must lie among the first `n` coordinates. -/
theorem midTo_mem_bdry (n : ℕ) {z : ↥(slabMid (Y := Y) n)} (hz : z ∈ slabMidi (Y := Y) n) :
    midTo n z ∈ cubeBdryK (midParam Y) n := by
  obtain ⟨-, i, hi⟩ := hz
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact ⟨j, by simpa only [midTo_apply_castSucc] using hi⟩
  · have hlow : (1/4 : ℝ) < ((z.1.1 (Fin.last n) : unitInterval) : ℝ) := z.2.2
    have hup : ((z.1.1 (Fin.last n) : unitInterval) : ℝ) < 3/4 := z.2.1
    rcases hi with h0 | h1
    · rw [h0] at hlow; norm_num at hlow
    · rw [h1] at hup; norm_num at hup

/-- The inverse homeomorphism sends the boundary of `Iⁿ × (1/4,3/4) × Y` into the boundary part of
the middle slab. -/
theorem midFrom_mem_bdry (n : ℕ) {w : CubeP (midParam Y) n}
    (hw : w ∈ cubeBdryK (midParam Y) n) : midFrom n w ∈ slabMidi (Y := Y) n := by
  obtain ⟨i, hi⟩ := hw
  refine ⟨(midFrom n w).2, ⟨i.castSucc, ?_⟩⟩
  simpa only [midFrom_apply_castSucc] using hi

end

end Work.StemsB
