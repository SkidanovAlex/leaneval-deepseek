import Mathlib
import Submission.Work.Cohomology.RelMVLes
import Submission.Work.Cohomology.Endgame.relCohMV_elim
import Submission.Work.Cohomology.localHomology
-- Re-pointed (Islands subproject, 2026): the workspace has two copies of this module
-- (`Cohomology/prodSphereAux.lean` and the identical `Cohomology/CompatTrans/prodSphereAux.lean`);
-- the rest of the workspace uses the `CompatTrans` copy, so importing the original here put the
-- two copies into one environment and made the STEMS-B chain unusable next to the chapters.
import Submission.Work.Cohomology.CompatTrans.prodSphereAux
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.ThreeConnected.Excision.PairVanish
import Submission.Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
import Submission.Work.ThreeConnected.Excision.isIso_relMVdelta_of_coverData
import Submission.Work.StemsB.RelChainsR

/-!
# The disc pair `(Iⁿ, ∂Iⁿ)` times a parameter space: geometry of the Mayer–Vietoris step

This file sets up the point-set input for the computation, by induction on `n`, of the relative
singular homology of the pair `(Iⁿ × Y, ∂Iⁿ × Y)` — the "trivial disc bundle pair" over `Y`
(the computation itself is in `Submission/Work/StemsB/CubePairHomology.lean`).

The cover of `I^{n+1} × Y` is by the two slabs `U = {last < 3/4}` and `V = {last > 1/4}`, whose
intersection is `{1/4 < last < 3/4}`.  The key geometric facts established here are:

* the slabs are open and cover the cube;
* `{last = 0} × Y` is an explicit *homotopy* retract of the first slab (push the last coordinate to
  `0`), and `{last = 1} × Y` of the second (push the last coordinate to `1`);
* consequently the two halves of the cover are acyclic relative to the boundary;
* the part of the boundary lying in the middle slab is `(1/4,3/4) × ∂Iⁿ × Y`.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.StemsB

noncomputable section

/-- The `n`-cube times a parameter space `Y`. -/
abbrev CubeP (Y : Type) (n : ℕ) : Type := (Fin n → unitInterval) × Y

/-- The `n`-cube times `Y`, as a topological space. -/
abbrev CubeSpace (Y : Type) [TopologicalSpace Y] (n : ℕ) : TopCat := TopCat.of (CubeP Y n)

variable {Y : Type} [TopologicalSpace Y]

/-- The first slab `{last < 3/4}` of the cover of `I^{n+1} × Y`. -/
def slabA (n : ℕ) : Set (CubeP Y (n+1)) := {p | (p.1 (Fin.last n) : ℝ) < 3/4}

/-- The second slab `{last > 1/4}` of the cover of `I^{n+1} × Y`. -/
def slabB (n : ℕ) : Set (CubeP Y (n+1)) := {p | (1:ℝ)/4 < (p.1 (Fin.last n) : ℝ)}

/-- The boundary `∂I^{n+1} × Y`. -/
def cubeBdry (n : ℕ) : Set (CubeP Y (n+1)) := {p | p.1 ∈ Cube.boundary (Fin (n+1))}

theorem isOpen_slabA (n : ℕ) : IsOpen (slabA (Y := Y) n) :=
  isOpen_lt (continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_fst))
    continuous_const

theorem isOpen_slabB (n : ℕ) : IsOpen (slabB (Y := Y) n) :=
  isOpen_lt continuous_const
    (continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_fst))

theorem slabA_union_slabB (n : ℕ) : slabA (Y := Y) n ∪ slabB (Y := Y) n = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_univ, slabA, slabB, Set.mem_setOf_eq, iff_true, true_iff]
  rcases lt_or_ge ((p.1 (Fin.last n) : unitInterval) : ℝ) (3/4) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-! ## Two interval operations -/

/-- The product `s * t` of two elements of the unit interval. -/
def smulI (s t : unitInterval) : unitInterval :=
  ⟨(s:ℝ) * (t:ℝ), ⟨mul_nonneg s.2.1 t.2.1, by
    have h1 : (s:ℝ) * (t:ℝ) ≤ 1 * 1 := mul_le_mul s.2.2 t.2.2 t.2.1 (by norm_num)
    simpa using h1⟩⟩

@[simp] theorem smulI_coe (s t : unitInterval) : ((smulI s t : unitInterval) : ℝ) = (s:ℝ)*(t:ℝ) :=
  rfl

@[simp] theorem smulI_zero_left (t : unitInterval) : smulI 0 t = 0 := by ext; simp [smulI]

@[simp] theorem smulI_zero_right (s : unitInterval) : smulI s 0 = 0 := by ext; simp [smulI]

@[simp] theorem smulI_one_left (t : unitInterval) : smulI 1 t = t := by ext; simp [smulI]

theorem smulI_le (s t : unitInterval) : (smulI s t : ℝ) ≤ (t : ℝ) := by
  have h1 : (s:ℝ) * (t:ℝ) ≤ 1 * (t:ℝ) := mul_le_mul_of_nonneg_right s.2.2 t.2.1
  simpa [smulI] using h1

/-- The interpolation `(1-s)·1 + s·t` between `1` and `t`. -/
def mixI (s t : unitInterval) : unitInterval :=
  ⟨(1:ℝ) - (s:ℝ) * ((1:ℝ) - (t:ℝ)),
    ⟨by
      have h1 : (s:ℝ) * ((1:ℝ) - (t:ℝ)) ≤ 1 * ((1:ℝ) - (t:ℝ)) :=
        mul_le_mul_of_nonneg_right s.2.2 (by linarith [t.2.2])
      have h2 : (1:ℝ) - (t:ℝ) ≤ 1 := by linarith [t.2.1]
      nlinarith [h1, h2],
     by
      have h1 : (0:ℝ) ≤ (s:ℝ) * ((1:ℝ) - (t:ℝ)) := mul_nonneg s.2.1 (by linarith [t.2.2])
      linarith⟩⟩

@[simp] theorem mixI_coe (s t : unitInterval) :
    ((mixI s t : unitInterval) : ℝ) = 1 - (s:ℝ) * (1 - (t:ℝ)) := rfl

@[simp] theorem mixI_zero_left (t : unitInterval) : mixI 0 t = 1 := by ext; simp [mixI]

@[simp] theorem mixI_right_one (s : unitInterval) : mixI s 1 = 1 := by ext; simp [mixI]

@[simp] theorem mixI_one_left (t : unitInterval) : mixI 1 t = t := by ext; simp [mixI]

theorem le_mixI (s t : unitInterval) : (t : ℝ) ≤ (mixI s t : ℝ) := by
  have h1 : (0:ℝ) ≤ (1:ℝ) - (s:ℝ) := by linarith [s.2.2]
  have h2 : (0:ℝ) ≤ (1:ℝ) - (t:ℝ) := by linarith [t.2.2]
  have h3 : (0:ℝ) ≤ ((1:ℝ) - (s:ℝ)) * ((1:ℝ) - (t:ℝ)) := mul_nonneg h1 h2
  simp only [mixI_coe]
  nlinarith [h3]

theorem continuous_smulI : Continuous fun p : unitInterval × unitInterval => smulI p.1 p.2 :=
  Continuous.subtype_mk (by fun_prop) (fun p => ⟨mul_nonneg p.1.2.1 p.2.2.1, by
    have h1 : (p.1:ℝ) * (p.2:ℝ) ≤ 1 * 1 := mul_le_mul p.1.2.2 p.2.2.2 p.2.2.1 (by norm_num)
    simpa using h1⟩)

theorem continuous_mixI : Continuous fun p : unitInterval × unitInterval => mixI p.1 p.2 :=
  Continuous.subtype_mk (by fun_prop) (fun p => ⟨by
      have h1 : (p.1:ℝ) * ((1:ℝ) - (p.2:ℝ)) ≤ 1 * ((1:ℝ) - (p.2:ℝ)) :=
        mul_le_mul_of_nonneg_right p.1.2.2 (by linarith [p.2.2.2])
      have h2 : (1:ℝ) - (p.2:ℝ) ≤ 1 := by linarith [p.2.2.1]
      nlinarith [h1, h2],
     by
      have h1 : (0:ℝ) ≤ (p.1:ℝ) * ((1:ℝ) - (p.2:ℝ)) :=
        mul_nonneg p.1.2.1 (by linarith [p.2.2.2])
      linarith⟩)

/-! ## The push maps -/

/-- The map `(x, t, y) ↦ (x, 0, y)`: push the last coordinate to zero. -/
def pushLast (n : ℕ) (p : CubeP Y (n+1)) : CubeP Y (n+1) :=
  (fun i => if i = Fin.last n then 0 else p.1 i, p.2)

/-- The map `(x, t, y) ↦ (x, 1, y)`: push the last coordinate to one. -/
def pushToOne (n : ℕ) (p : CubeP Y (n+1)) : CubeP Y (n+1) :=
  (fun i => if i = Fin.last n then 1 else p.1 i, p.2)

@[simp] theorem pushLast_fst_last (n : ℕ) (p : CubeP Y (n+1)) :
    (pushLast n p).1 (Fin.last n) = (0 : unitInterval) := by simp [pushLast]

@[simp] theorem pushToOne_fst_last (n : ℕ) (p : CubeP Y (n+1)) :
    (pushToOne n p).1 (Fin.last n) = (1 : unitInterval) := by simp [pushToOne]

theorem pushLast_fst_of_ne (n : ℕ) (p : CubeP Y (n+1)) {i : Fin (n+1)}
    (h : i ≠ Fin.last n) : (pushLast n p).1 i = p.1 i := by simp [pushLast, h]

theorem pushToOne_fst_of_ne (n : ℕ) (p : CubeP Y (n+1)) {i : Fin (n+1)}
    (h : i ≠ Fin.last n) : (pushToOne n p).1 i = p.1 i := by simp [pushToOne, h]

@[simp] theorem pushLast_snd (n : ℕ) (p : CubeP Y (n+1)) : (pushLast n p).2 = p.2 := rfl

@[simp] theorem pushToOne_snd (n : ℕ) (p : CubeP Y (n+1)) : (pushToOne n p).2 = p.2 := rfl

theorem pushLast_mem_slabA (n : ℕ) (p : CubeP Y (n+1)) : pushLast n p ∈ slabA n := by
  show ((pushLast n p).1 (Fin.last n) : ℝ) < 3/4
  simp

theorem pushLast_mem_bdry (n : ℕ) (p : CubeP Y (n+1)) : pushLast n p ∈ cubeBdry n :=
  ⟨Fin.last n, Or.inl (by simp)⟩

theorem pushToOne_mem_slabB (n : ℕ) (p : CubeP Y (n+1)) : pushToOne n p ∈ slabB n := by
  show (1:ℝ)/4 < ((pushToOne n p).1 (Fin.last n) : ℝ)
  norm_num

theorem pushToOne_mem_bdry (n : ℕ) (p : CubeP Y (n+1)) : pushToOne n p ∈ cubeBdry n :=
  ⟨Fin.last n, Or.inr (by simp)⟩

theorem continuous_pushLast (n : ℕ) : Continuous (pushLast (Y := Y) n) := by
  refine Continuous.prodMk ?_ continuous_snd
  apply continuous_pi
  intro i
  by_cases h : i = Fin.last n
  · simp only [pushLast, h, ↓reduceIte]
    exact continuous_const
  · simp only [pushLast, h, ↓reduceIte]
    exact (continuous_apply i).comp continuous_fst

theorem continuous_pushToOne (n : ℕ) : Continuous (pushToOne (Y := Y) n) := by
  refine Continuous.prodMk ?_ continuous_snd
  apply continuous_pi
  intro i
  by_cases h : i = Fin.last n
  · simp only [pushToOne, h, ↓reduceIte]
    exact continuous_const
  · simp only [pushToOne, h, ↓reduceIte]
    exact (continuous_apply i).comp continuous_fst

/-! ## The homotopies -/

/-- The homotopy `(x,t,y) ↦ (x, s·t, y)`, scaling the last coordinate down: at `s = 1` it is the
identity and at `s = 0` the push map. -/
def homA (n : ℕ) (z : unitInterval × CubeP Y (n+1)) : CubeP Y (n+1) :=
  (fun i => if i = Fin.last n then smulI z.1 (z.2.1 (Fin.last n)) else z.2.1 i, z.2.2)

/-- The homotopy `(x,t,y) ↦ (x, 1 - s(1-t), y)`: at `s = 1` the identity, at `s = 0` the push
map. -/
def homB (n : ℕ) (z : unitInterval × CubeP Y (n+1)) : CubeP Y (n+1) :=
  (fun i => if i = Fin.last n then mixI z.1 (z.2.1 (Fin.last n)) else z.2.1 i, z.2.2)

theorem homA_fst_last (n : ℕ) (z : unitInterval × CubeP Y (n+1)) :
    (homA n z).1 (Fin.last n) = smulI z.1 (z.2.1 (Fin.last n)) := by simp [homA]

theorem homB_fst_last (n : ℕ) (z : unitInterval × CubeP Y (n+1)) :
    (homB n z).1 (Fin.last n) = mixI z.1 (z.2.1 (Fin.last n)) := by simp [homB]

theorem homA_fst_of_ne (n : ℕ) (z : unitInterval × CubeP Y (n+1)) {i : Fin (n+1)}
    (h : i ≠ Fin.last n) : (homA n z).1 i = z.2.1 i := by simp [homA, h]

theorem homB_fst_of_ne (n : ℕ) (z : unitInterval × CubeP Y (n+1)) {i : Fin (n+1)}
    (h : i ≠ Fin.last n) : (homB n z).1 i = z.2.1 i := by simp [homB, h]

@[simp] theorem homA_snd (n : ℕ) (z : unitInterval × CubeP Y (n+1)) : (homA n z).2 = z.2.2 := rfl

@[simp] theorem homB_snd (n : ℕ) (z : unitInterval × CubeP Y (n+1)) : (homB n z).2 = z.2.2 := rfl

theorem continuous_homA (n : ℕ) : Continuous (homA (Y := Y) n) := by
  refine Continuous.prodMk ?_ (continuous_snd.comp continuous_snd)
  apply continuous_pi
  intro i
  by_cases h : i = Fin.last n
  · simp only [homA, h, ↓reduceIte]
    exact continuous_smulI.comp (Continuous.prodMk continuous_fst
      ((continuous_apply (Fin.last n)).comp (continuous_fst.comp continuous_snd)))
  · simp only [homA, h, ↓reduceIte]
    exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)

theorem continuous_homB (n : ℕ) : Continuous (homB (Y := Y) n) := by
  refine Continuous.prodMk ?_ (continuous_snd.comp continuous_snd)
  apply continuous_pi
  intro i
  by_cases h : i = Fin.last n
  · simp only [homB, h, ↓reduceIte]
    exact continuous_mixI.comp (Continuous.prodMk continuous_fst
      ((continuous_apply (Fin.last n)).comp (continuous_fst.comp continuous_snd)))
  · simp only [homB, h, ↓reduceIte]
    exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)

theorem homA_zero (n : ℕ) (p : CubeP Y (n+1)) : homA n ((0 : unitInterval), p) = pushLast n p := by
  apply Prod.ext
  · funext i
    by_cases h : i = Fin.last n
    · subst h; simp [homA, pushLast]
    · simp [homA, pushLast, h]
  · rfl

theorem homA_one (n : ℕ) (p : CubeP Y (n+1)) : homA n ((1 : unitInterval), p) = p := by
  apply Prod.ext
  · funext i
    by_cases h : i = Fin.last n
    · subst h; simp [homA]
    · simp [homA, h]
  · rfl

theorem homB_zero (n : ℕ) (p : CubeP Y (n+1)) : homB n ((0 : unitInterval), p) = pushToOne n p := by
  apply Prod.ext
  · funext i
    by_cases h : i = Fin.last n
    · subst h; simp [homB, pushToOne]
    · simp [homB, pushToOne, h]
  · rfl

theorem homB_one (n : ℕ) (p : CubeP Y (n+1)) : homB n ((1 : unitInterval), p) = p := by
  apply Prod.ext
  · funext i
    by_cases h : i = Fin.last n
    · subst h; simp [homB]
    · simp [homB, h]
  · rfl

theorem homA_mem_slabA (n : ℕ) {z : unitInterval × CubeP Y (n+1)} (hz : z.2 ∈ slabA n) :
    homA n z ∈ slabA n := by
  have hle := smulI_le z.1 (z.2.1 (Fin.last n))
  have hlast : ((homA n z).1 (Fin.last n) : ℝ) = (smulI z.1 (z.2.1 (Fin.last n)) : ℝ) := by
    rw [homA_fst_last]
  simp only [slabA, Set.mem_setOf_eq] at hz ⊢
  rw [hlast]
  linarith

theorem homB_mem_slabB (n : ℕ) {z : unitInterval × CubeP Y (n+1)} (hz : z.2 ∈ slabB n) :
    homB n z ∈ slabB n := by
  have hle := le_mixI z.1 (z.2.1 (Fin.last n))
  have hlast : ((homB n z).1 (Fin.last n) : ℝ) = (mixI z.1 (z.2.1 (Fin.last n)) : ℝ) := by
    rw [homB_fst_last]
  simp only [slabB, Set.mem_setOf_eq] at hz ⊢
  rw [hlast]
  linarith

theorem homA_mem_bdry (n : ℕ) {z : unitInterval × CubeP Y (n+1)} (hzA : z.2 ∈ slabA n)
    (hzC : z.2 ∈ cubeBdry n) : homA n z ∈ cubeBdry n := by
  obtain ⟨i, hi⟩ := hzC
  rcases eq_or_ne i (Fin.last n) with h | h
  · subst h
    rcases hi with h0 | h1
    · exact ⟨Fin.last n, Or.inl (by rw [homA_fst_last, h0]; simp)⟩
    · exact absurd (by rw [h1]; rfl : ((z.2.1 (Fin.last n) : unitInterval) : ℝ) = 1)
        (by have := hzA; simp only [slabA, Set.mem_setOf_eq] at this; linarith)
  · exact ⟨i, by rw [homA_fst_of_ne n z h]; exact hi⟩

theorem homB_mem_bdry (n : ℕ) {z : unitInterval × CubeP Y (n+1)} (hzB : z.2 ∈ slabB n)
    (hzC : z.2 ∈ cubeBdry n) : homB n z ∈ cubeBdry n := by
  obtain ⟨i, hi⟩ := hzC
  rcases eq_or_ne i (Fin.last n) with h | h
  · subst h
    rcases hi with h0 | h1
    · exact absurd (by rw [h0]; rfl : ((z.2.1 (Fin.last n) : unitInterval) : ℝ) = 0)
        (by have := hzB; simp only [slabB, Set.mem_setOf_eq] at this; linarith)
    · exact ⟨Fin.last n, Or.inr (by rw [homB_fst_last, h1]; simp)⟩
  · exact ⟨i, by rw [homB_fst_of_ne n z h]; exact hi⟩

/-! ## The boundary part of the slabs, and the retraction data -/

/-- The part of the boundary lying in the first slab, viewed inside the first slab. -/
def slabAi (n : ℕ) : Set ↥(slabA (Y := Y) n) := (Subtype.val) ⁻¹' (slabA n ∩ cubeBdry n)

/-- The part of the boundary lying in the second slab, viewed inside the second slab. -/
def slabBi (n : ℕ) : Set ↥(slabB (Y := Y) n) := (Subtype.val) ⁻¹' (slabB n ∩ cubeBdry n)

theorem pushLast_mem_slabAi (n : ℕ) (p : ↥(slabA (Y := Y) n)) :
    (⟨pushLast n p.1, pushLast_mem_slabA n p.1⟩ : ↥(slabA (Y := Y) n)) ∈ slabAi (Y := Y) n :=
  ⟨pushLast_mem_slabA n p.1, pushLast_mem_bdry n p.1⟩

theorem pushToOne_mem_slabBi (n : ℕ) (p : ↥(slabB (Y := Y) n)) :
    (⟨pushToOne n p.1, pushToOne_mem_slabB n p.1⟩ : ↥(slabB (Y := Y) n)) ∈ slabBi (Y := Y) n :=
  ⟨pushToOne_mem_slabB n p.1, pushToOne_mem_bdry n p.1⟩

/-- The push map from the first slab onto its boundary part. -/
def pushSlabA (n : ℕ) : TopCat.of ↥(slabA (Y := Y) n) ⟶ TopCat.of (slabAi (Y := Y) n) :=
  TopCat.ofHom
    ⟨fun p => ⟨⟨pushLast n p.1, pushLast_mem_slabA n p.1⟩, pushLast_mem_slabAi (Y := Y) n p⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        ((continuous_pushLast n).comp continuous_subtype_val) _) _⟩

/-- The push map from the second slab onto its boundary part. -/
def pushSlabB (n : ℕ) : TopCat.of ↥(slabB (Y := Y) n) ⟶ TopCat.of (slabBi (Y := Y) n) :=
  TopCat.ofHom
    ⟨fun p => ⟨⟨pushToOne n p.1, pushToOne_mem_slabB n p.1⟩, pushToOne_mem_slabBi (Y := Y) n p⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        ((continuous_pushToOne n).comp continuous_subtype_val) _) _⟩

/-- The inclusion of the boundary part of the first slab. -/
def inclSlabA (n : ℕ) :
    TopCat.of (slabAi (Y := Y) n) ⟶ TopCat.of ↥(slabA (Y := Y) n) :=
  Work.Cohomology.subtypeIncl (TopCat.of ↥(slabA (Y := Y) n)) (slabAi (Y := Y) n)

/-- The inclusion of the boundary part of the second slab. -/
def inclSlabB (n : ℕ) :
    TopCat.of (slabBi (Y := Y) n) ⟶ TopCat.of ↥(slabB (Y := Y) n) :=
  Work.Cohomology.subtypeIncl (TopCat.of ↥(slabB (Y := Y) n)) (slabBi (Y := Y) n)

/-- The homotopy `homA` restricted to the first slab, as a continuous map. -/
def homASlabA (n : ℕ) :
    C(unitInterval × ↥(slabA (Y := Y) n), CubeP Y (n+1)) :=
  ⟨fun z => homA n (z.1, z.2.1),
    (continuous_homA n).comp
      (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd))⟩

/-- The homotopy `homB` restricted to the second slab, as a continuous map. -/
def homBSlabB (n : ℕ) :
    C(unitInterval × ↥(slabB (Y := Y) n), CubeP Y (n+1)) :=
  ⟨fun z => homB n (z.1, z.2.1),
    (continuous_homB n).comp
      (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd))⟩

/-- The homotopy `homA` restricted to the boundary part of the first slab. -/
def homASlabAi (n : ℕ) :
    C(unitInterval × ↥(slabAi (Y := Y) n), CubeP Y (n+1)) :=
  ⟨fun z => homA n (z.1, z.2.1.1),
    (continuous_homA n).comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))⟩

/-- The homotopy `homB` restricted to the boundary part of the second slab. -/
def homBSlabBi (n : ℕ) :
    C(unitInterval × ↥(slabBi (Y := Y) n), CubeP Y (n+1)) :=
  ⟨fun z => homB n (z.1, z.2.1.1),
    (continuous_homB n).comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))⟩

/-- The homotopy on the first slab exhibiting the push map as a deformation retraction. -/
def homSlabA (n : ℕ) :
    TopCat.Homotopy (pushSlabA n ≫ inclSlabA n) (𝟙 (TopCat.of ↥(slabA (Y := Y) n))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨homASlabA n z, homA_mem_slabA n z.2.2⟩,
      (homASlabA n).continuous.subtype_mk _⟩
    (fun p => by
      apply Subtype.ext
      change homA n ((0 : unitInterval), p.1) = pushLast n p.1
      rw [homA_zero])
    (fun p => by
      apply Subtype.ext
      change homA n ((1 : unitInterval), p.1) = p.1
      rw [homA_one])

/-- The homotopy on the second slab exhibiting the push map as a deformation retraction. -/
def homSlabB (n : ℕ) :
    TopCat.Homotopy (pushSlabB n ≫ inclSlabB n) (𝟙 (TopCat.of ↥(slabB (Y := Y) n))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨homBSlabB n z, homB_mem_slabB n z.2.2⟩,
      (homBSlabB n).continuous.subtype_mk _⟩
    (fun p => by
      apply Subtype.ext
      change homB n ((0 : unitInterval), p.1) = pushToOne n p.1
      rw [homB_zero])
    (fun p => by
      apply Subtype.ext
      change homB n ((1 : unitInterval), p.1) = p.1
      rw [homB_one])

/-- The homotopy on the boundary part of the first slab: the inclusion followed by the push map is
homotopic to the identity. -/
def homSlabAi (n : ℕ) :
    TopCat.Homotopy (inclSlabA n ≫ pushSlabA n) (𝟙 (TopCat.of (slabAi (Y := Y) n))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨⟨homASlabAi n z, homA_mem_slabA n z.2.2.1⟩,
        homA_mem_slabA n z.2.2.1, homA_mem_bdry n z.2.2.1 z.2.2.2⟩,
      Continuous.subtype_mk ((homASlabAi n).continuous.subtype_mk _) _⟩
    (fun a => by
      apply Subtype.ext
      apply Subtype.ext
      change homA n ((0 : unitInterval), a.1.1) = pushLast n a.1.1
      rw [homA_zero])
    (fun a => by
      apply Subtype.ext
      apply Subtype.ext
      change homA n ((1 : unitInterval), a.1.1) = a.1.1
      rw [homA_one])

/-- The homotopy on the boundary part of the second slab. -/
def homSlabBi (n : ℕ) :
    TopCat.Homotopy (inclSlabB n ≫ pushSlabB n) (𝟙 (TopCat.of (slabBi (Y := Y) n))) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨⟨homBSlabBi n z, homB_mem_slabB n z.2.2.1⟩,
        homB_mem_slabB n z.2.2.1, homB_mem_bdry n z.2.2.1 z.2.2.2⟩,
      Continuous.subtype_mk ((homBSlabBi n).continuous.subtype_mk _) _⟩
    (fun a => by
      apply Subtype.ext
      apply Subtype.ext
      change homB n ((0 : unitInterval), a.1.1) = pushToOne n a.1.1
      rw [homB_zero])
    (fun a => by
      apply Subtype.ext
      apply Subtype.ext
      change homB n ((1 : unitInterval), a.1.1) = a.1.1
      rw [homB_one])

end

end Work.StemsB
