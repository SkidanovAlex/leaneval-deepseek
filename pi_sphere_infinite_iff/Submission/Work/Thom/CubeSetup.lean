import Mathlib
import Submission.Work.Thom.EucCube
import Submission.Work.Cohomology.pd_glue_defs

/-!
# The cube pieces used in the vanishing theorem `Work.Thom.subsingleton_relComplex_cube`

This file fixes the notation for the Mayer–Vietoris induction proving that the relative cohomology
of the pair `(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ)` vanishes below degree `n`.

Writing `ℝⁿ⁺¹ = ℝⁿ × ℝ` (last coordinate), the cube `euCube (n+1)` is covered by the two open
pieces `pieceTop n W` (last coordinate `> -1/2`) and `pieceBot n W` (last coordinate `< 1/2`), whose
overlap is `{p | |p (last)| < 1/2}` and whose boundary part `bdrySet (n+1) W` is the set of points
with some coordinate `±1`.

* `withLast x c` — the vector `x` with its last coordinate replaced by `c`;
* `pieceTop`, `pieceBot`, `bdrySet` — the subsets above;
* `pieceCoh n W S j` — `H^j` of the piece of `W × euCube (n+1)` cut out by a condition `S` on the
  last coordinate, relative to its boundary part
  (`H^j(W × {last ∈ S}, W × {last ∈ S} ∩ ∂)`),
* `overlapCoh n W k` — the same for the overlap `pieceTop n W ∩ pieceBot n W`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Thom
namespace Cube

/-! ## Replacing the last coordinate of a vector of `ℝⁿ⁺¹` -/

/-- `withLast x c` is `x` with its last coordinate replaced by `c`. -/
def withLast {n : ℕ} (x : Fin (n+1) → ℝ) (c : ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc (fun i : Fin n => x i.castSucc) c

variable {n : ℕ}

@[simp] theorem withLast_castSucc (x : Fin (n+1) → ℝ) (c : ℝ) (i : Fin n) :
    withLast x c i.castSucc = x i.castSucc := by simp [withLast]

@[simp] theorem withLast_last (x : Fin (n+1) → ℝ) (c : ℝ) :
    withLast x c (Fin.last n) = c := by simp [withLast]

theorem withLast_self (x : Fin (n+1) → ℝ) : withLast x (x (Fin.last n)) = x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [withLast_last]
  · intro j; rw [withLast_castSucc]

theorem withLast_eq_self_iff {x : Fin (n+1) → ℝ} {c : ℝ} :
    withLast x c = x ↔ c = x (Fin.last n) := by
  constructor
  · intro h
    have := congrFun h (Fin.last n)
    simpa using this
  · intro h
    rw [h, withLast_self]

theorem continuous_withLast (c : ℝ) : Continuous fun x : Fin (n+1) → ℝ => withLast x c := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · simpa [withLast] using (continuous_const : Continuous fun _ : Fin (n+1) → ℝ => c)
  · intro j
    simpa [withLast] using
      (continuous_apply j.castSucc : Continuous fun x : Fin (n+1) → ℝ => x j.castSucc)

theorem continuous_withLast' {α : Type} [TopologicalSpace α] {f : α → Fin (n+1) → ℝ}
    (hf : Continuous f) {g : α → ℝ} (hg : Continuous g) :
    Continuous fun a => withLast (f a) (g a) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · simpa [withLast] using hg
  · intro j
    have h2 : Continuous fun a => f a (j.castSucc) :=
      (continuous_apply j.castSucc :
        Continuous fun x : Fin (n+1) → ℝ => x j.castSucc).comp hf
    simpa [withLast] using h2

theorem continuous_withLast_val {α : Type} [TopologicalSpace α] {f : α → ↥(euCube (n+1))}
    (hf : Continuous f) (c : ℝ) :
    Continuous fun a => withLast ((f a : ↥(euCube (n+1))) : Fin (n+1) → ℝ) c :=
  (continuous_withLast c).comp (continuous_subtype_val.comp hf)

theorem continuous_withLast_val' {α : Type} [TopologicalSpace α] {f : α → ↥(euCube (n+1))}
    (hf : Continuous f) {g : α → ℝ} (hg : Continuous g) :
    Continuous fun a => withLast ((f a : ↥(euCube (n+1))) : Fin (n+1) → ℝ) (g a) :=
  continuous_withLast' (continuous_subtype_val.comp hf) hg

/-! ## Membership of `withLast` in the cube and its boundary -/

theorem withLast_mem_euCube {x : Fin (n+1) → ℝ} (hx : x ∈ euCube (n+1)) {c : ℝ}
    (hc : |c| ≤ 1) : withLast x c ∈ euCube (n+1) := by
  rw [mem_euCube]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · rw [withLast_last]; exact hc
  · intro j; rw [withLast_castSucc]; exact (mem_euCube.mp hx) j.castSucc

theorem withLast_mem_euCube_of_abs_le_one {x : Fin (n+1) → ℝ} (hx : x ∈ euCube (n+1)) {c : ℝ}
    (hc : c ∈ Set.Icc (-1 : ℝ) 1) : withLast x c ∈ euCube (n+1) :=
  withLast_mem_euCube hx (abs_le.mpr hc)

theorem withLast_mem_euCubeBdry {x : Fin (n+1) → ℝ} (hx : x ∈ euCube (n+1)) {c : ℝ}
    (hc : |c| = 1) : withLast x c ∈ euCubeBdry (n+1) :=
  ⟨withLast_mem_euCube hx (le_of_eq hc),
    ⟨Fin.last n, by rw [withLast_last]; exact hc⟩⟩

/-! ## Convex combinations of the last coordinate -/

/-- The interpolation `x + s (c - x)` stays in `[-1,1]` when `x, c` do. -/
theorem interp_mem_Icc {x c s : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : x + s * (c - x) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsum : x + (c - x) ∈ Set.Icc (-1 : ℝ) 1 := by simpa using hc
  have := (convex_Icc (-1 : ℝ) 1).add_smul_mem hx hsum hs
  simpa using this

theorem abs_interp_le_one {x c s : ℝ} (hx : |x| ≤ 1) (hc : |c| ≤ 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : |x + s * (c - x)| ≤ 1 :=
  abs_le.mpr (interp_mem_Icc (abs_le.mp hx) (abs_le.mp hc) ⟨hs0, hs1⟩)

theorem interp_zero (x c : ℝ) : x + 0 * (c - x) = x := by ring

theorem interp_one (x c : ℝ) : x + 1 * (c - x) = c := by ring

/-! ## The two pieces of the cube `euCube (n+1)`, and the boundary part -/

/-- The "upper" piece of the cube `euCube (n+1)`: its last coordinate exceeds `-1/2`. -/
def pieceTop (n : ℕ) (W : Type) : Set (W × ↥(euCube (n+1))) :=
  {p | (p.2 : Fin (n+1) → ℝ) (Fin.last n) ∈ Set.Ioi (-1/2)}

/-- The "lower" piece of the cube `euCube (n+1)`: its last coordinate is less than `1/2`. -/
def pieceBot (n : ℕ) (W : Type) : Set (W × ↥(euCube (n+1))) :=
  {p | (p.2 : Fin (n+1) → ℝ) (Fin.last n) ∈ Set.Iio (1/2)}

/-- The boundary part of `W × euCube n`. -/
def bdrySet (n : ℕ) (W : Type) : Set (W × ↥(euCube n)) :=
  {p | (p.2 : Fin n → ℝ) ∈ euCubeBdry n}

theorem bdrySet_def (n : ℕ) (W : Type) :
    bdrySet n W = {p : W × ↥(euCube n) | (p.2 : Fin n → ℝ) ∈ euCubeBdry n} := rfl

@[simp] theorem mem_pieceTop {W : Type} {p : W × ↥(euCube (n+1))} :
    p ∈ pieceTop n W ↔ (p.2 : Fin (n+1) → ℝ) (Fin.last n) > -1/2 := by
  simp [pieceTop]

@[simp] theorem mem_pieceBot {W : Type} {p : W × ↥(euCube (n+1))} :
    p ∈ pieceBot n W ↔ (p.2 : Fin (n+1) → ℝ) (Fin.last n) < 1/2 := by
  simp [pieceBot]

@[simp] theorem mem_bdrySet {W : Type} {p : W × ↥(euCube n)} :
    p ∈ bdrySet n W ↔ (p.2 : Fin n → ℝ) ∈ euCubeBdry n := Iff.rfl

theorem mem_piece_inter {W : Type} {p : W × ↥(euCube (n+1))} :
    p ∈ pieceTop n W ∩ pieceBot n W ↔
      (p.2 : Fin (n+1) → ℝ) (Fin.last n) ∈ Set.Ioo (-1/2) (1/2) := by
  simp only [Set.mem_inter_iff, mem_pieceTop, mem_pieceBot, Set.mem_Ioo]

theorem abs_last_lt_of_mem_inter {W : Type} {p : W × ↥(euCube (n+1))}
    (hp : p ∈ pieceTop n W ∩ pieceBot n W) :
    |(p.2 : Fin (n+1) → ℝ) (Fin.last n)| < 1/2 := by
  rw [mem_piece_inter, Set.mem_Ioo] at hp
  exact abs_lt.mpr ⟨by linarith [hp.1], hp.2⟩

theorem isOpen_pieceTop (n : ℕ) (W : Type) [TopologicalSpace W] : IsOpen (pieceTop n W) := by
  have hc : Continuous fun p : W × ↥(euCube (n+1)) =>
      (p.2 : Fin (n+1) → ℝ) (Fin.last n) :=
    (continuous_apply (Fin.last n)).comp (continuous_subtype_val.comp continuous_snd)
  have h := (isOpen_Ioi (a := (-1/2 : ℝ))).preimage hc
  rw [pieceTop]
  exact h

theorem isOpen_pieceBot (n : ℕ) (W : Type) [TopologicalSpace W] : IsOpen (pieceBot n W) := by
  have hc : Continuous fun p : W × ↥(euCube (n+1)) =>
      (p.2 : Fin (n+1) → ℝ) (Fin.last n) :=
    (continuous_apply (Fin.last n)).comp (continuous_subtype_val.comp continuous_snd)
  have h := (isOpen_Iio (a := (1/2 : ℝ))).preimage hc
  rw [pieceBot]
  exact h

theorem pieceTop_union_pieceBot (n : ℕ) (W : Type) :
    pieceTop n W ∪ pieceBot n W = Set.univ := by
  ext p
  rw [Set.mem_union, mem_pieceTop, mem_pieceBot]
  exact ⟨fun _ => trivial, fun _ => by
    rcases lt_or_ge (-1/2 : ℝ) ((p.2 : Fin (n+1) → ℝ) (Fin.last n)) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)⟩

/-! ## The relative cohomology of the pieces -/

/-- `H^j` of the piece `{p | last coordinate of p ∈ S}` of `W × euCube (n+1)`, relative to its
boundary part. -/
noncomputable abbrev pieceCoh (n : ℕ) (W : Type) [TopologicalSpace W] (S : Set ℝ) (j : ℕ) : ModuleCat ℤ :=
  Work.Cohomology.pdCohSub (TopCat.of (W × ↥(euCube (n+1)))) (bdrySet (n+1) W)
    {p : W × ↥(euCube (n+1)) | (p.2 : Fin (n+1) → ℝ) (Fin.last n) ∈ S} j

/-- `H^k` of the overlap `pieceTop n W ∩ pieceBot n W`, relative to its boundary part. -/
noncomputable abbrev overlapCoh (n : ℕ) (W : Type) [TopologicalSpace W] (k : ℕ) : ModuleCat ℤ :=
  Work.Cohomology.pdCohSub (TopCat.of (W × ↥(euCube (n+1)))) (bdrySet (n+1) W)
    (pieceTop n W ∩ pieceBot n W) k

theorem pieceCoh_top (n : ℕ) (W : Type) [TopologicalSpace W] (j : ℕ) :
    pieceCoh n W (Set.Ioi (-1/2)) j
      = Work.Cohomology.pdCohSub (TopCat.of (W × ↥(euCube (n+1)))) (bdrySet (n+1) W)
          (pieceTop n W) j := rfl

theorem pieceCoh_bot (n : ℕ) (W : Type) [TopologicalSpace W] (j : ℕ) :
    pieceCoh n W (Set.Iio (1/2)) j
      = Work.Cohomology.pdCohSub (TopCat.of (W × ↥(euCube (n+1)))) (bdrySet (n+1) W)
          (pieceBot n W) j := rfl

theorem overlapCoh_def (n : ℕ) (W : Type) [TopologicalSpace W] (k : ℕ) :
    overlapCoh n W k = Work.Cohomology.pdCohSub (TopCat.of (W × ↥(euCube (n+1))))
      (bdrySet (n+1) W) (pieceTop n W ∩ pieceBot n W) k := rfl

/-! ## The two instantiations used in the induction -/

theorem convex_Ioi_half : Convex ℝ (Set.Ioi (-1/2 : ℝ)) := convex_Ioi _

theorem convex_Iio_half : Convex ℝ (Set.Iio (1/2 : ℝ)) := convex_Iio _

theorem unit_Ioi_half : ∀ t ∈ Set.Ioi (-1/2 : ℝ), |t| = 1 → t = (1 : ℝ) := by
  intro t ht h1
  rw [Set.mem_Ioi] at ht
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h1 with h | h
  · exact h
  · rw [h] at ht; norm_num at ht

theorem unit_Iio_half : ∀ t ∈ Set.Iio (1/2 : ℝ), |t| = 1 → t = (-1 : ℝ) := by
  intro t ht h1
  rw [Set.mem_Iio] at ht
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h1 with h | h
  · rw [h] at ht; norm_num at ht
  · exact h

end Cube
end Work.Thom
