import Mathlib
import Submission.Work.Thom.CubeSetup
import Submission.Work.Thom.EucCube
import Submission.Work.Thom.homotopyRetractVanishing
import Submission.Work.Thom.subsingleton_relComplex_of_homotopyData

/-!
# Vanishing of the relative cohomology of a cube piece cut out by a convex set of last coordinates

Let `S ⊆ ℝ` be convex, let `c ∈ S` with `|c| = 1`, and suppose that `c` is the *only* point of `S`
of modulus one.  For `W` any space, the piece

`{p : W × euCube (n+1) | last coordinate of p ∈ S}`

has the following property: the "push the last coordinate to `c`" map is a homotopy inverse to the
inclusion of the relative part `{p | p ∈ S, p ∈ ∂}` (the points of the piece that lie in the
boundary of the cube).  Indeed

* the straight line `xₙ ↦ xₙ + t (c - xₙ)` stays in `S` (convexity, `S ∋ c`),
* at the endpoint the last coordinate equals `c`, so the point lies in the boundary of the cube,
* a point of the relative part which is *not* already detected by one of the other coordinates has
  `|xₙ| = 1`, hence `xₙ = c` by the uniqueness assumption, and is therefore fixed by the homotopy.

Consequently `H^j` of the pair `(piece, piece ∩ ∂)` vanishes in every degree, by
`Work.Thom.subsingleton_relComplex_of_homotopyData`.  In particular this covers the two pieces
`S = (1/2, ∞)` (with `c = 1`) and `S = (-∞, -1/2)` (with `c = -1`) used in the Mayer–Vietoris
induction of `Work.Thom.subsingleton_relComplex_cube`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Thom
namespace Piece

/-! ## The last coordinate and the straight-line interpolation -/

/-- The last coordinate of a point of the cube `euCube (n+1)`. -/
def lastCoord (n : ℕ) (x : ↥(euCube (n+1))) : ℝ := (x : Fin (n+1) → ℝ) (Fin.last n)

theorem continuous_lastCoord (n : ℕ) : Continuous (lastCoord n) :=
  (continuous_apply (Fin.last n)).comp continuous_subtype_val

/-- The straight-line interpolation of the last coordinate from `x` to `c`. -/
def interpLast (n : ℕ) (c : ℝ) (t : ℝ) (x : ↥(euCube (n+1))) : ℝ :=
  lastCoord n x + t * (c - lastCoord n x)

theorem continuous_interpLast (n : ℕ) (c : ℝ) :
    Continuous fun z : ↑unitInterval × ↥(euCube (n+1)) => interpLast n c (z.1 : ℝ) z.2 := by
  simp only [interpLast]
  exact ((continuous_lastCoord n).comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.sub ((continuous_lastCoord n).comp continuous_snd)))

/-! ## The push map on the cube fibre, and its straight-line homotopy -/

/-- Pushing the last coordinate of a point of the cube to `c`. -/
def pushFibreMap (n : ℕ) {c : ℝ} (hc1 : |c| ≤ 1) : C(↥(euCube (n+1)), ↥(euCube (n+1))) where
  toFun x := ⟨Cube.withLast (x : Fin (n+1) → ℝ) c, Cube.withLast_mem_euCube x.2 hc1⟩
  continuous_toFun := Continuous.subtype_mk
    (Cube.continuous_withLast_val continuous_id c)
    (fun x => Cube.withLast_mem_euCube x.2 hc1)

/-- The straight-line homotopy pushing the last coordinate of a point of the cube to `c`. -/
def pushFibreHom (n : ℕ) {c : ℝ} (hc1 : |c| ≤ 1) :
    C(↑unitInterval × ↥(euCube (n+1)), ↥(euCube (n+1))) where
  toFun z := ⟨Cube.withLast (z.2 : Fin (n+1) → ℝ) (interpLast n c (z.1 : ℝ) z.2),
    Cube.withLast_mem_euCube z.2.2 (by
      have hx : |lastCoord n z.2| ≤ 1 := (mem_euCube.mp z.2.2) (Fin.last n)
      exact Cube.abs_interp_le_one hx hc1 z.1.2.1 z.1.2.2)⟩
  continuous_toFun := Continuous.subtype_mk
    (Cube.continuous_withLast_val' (α := ↑unitInterval × ↥(euCube (n+1))) continuous_snd
      (continuous_interpLast n c))
    (fun z => Cube.withLast_mem_euCube z.2.2 (by
      have hx : |lastCoord n z.2| ≤ 1 := (mem_euCube.mp z.2.2) (Fin.last n)
      exact Cube.abs_interp_le_one hx hc1 z.1.2.1 z.1.2.2))

theorem pushFibreHom_zero (n : ℕ) {c : ℝ} (hc1 : |c| ≤ 1) (x : ↥(euCube (n+1))) :
    pushFibreHom n hc1 (0, x) = x := by
  apply Subtype.ext
  show Cube.withLast (x : Fin (n+1) → ℝ) (interpLast n c (0 : ℝ) x) = (x : Fin (n+1) → ℝ)
  rw [Cube.withLast_eq_self_iff, interpLast]
  simp [lastCoord]

theorem pushFibreHom_one (n : ℕ) {c : ℝ} (hc1 : |c| ≤ 1) (x : ↥(euCube (n+1))) :
    pushFibreHom n hc1 (1, x) = pushFibreMap n hc1 x := by
  apply Subtype.ext
  show Cube.withLast (x : Fin (n+1) → ℝ) (interpLast n c (1 : ℝ) x)
      = Cube.withLast (x : Fin (n+1) → ℝ) c
  rw [interpLast]
  congr 1
  ring

/-! ## The same on `W × euCube (n+1)` -/

/-- Pushing the last coordinate of the cube to `c`, on `W × euCube (n+1)`. -/
def pushMap (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc1 : |c| ≤ 1) :
    C(W × ↥(euCube (n+1)), W × ↥(euCube (n+1))) :=
  (ContinuousMap.id W).prodMap (pushFibreMap n hc1)

/-- The straight-line homotopy pushing the last coordinate of the cube to `c`, on
`W × euCube (n+1)`. -/
def pushHom (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc1 : |c| ≤ 1) :
    C(↑unitInterval × (W × ↥(euCube (n+1))), W × ↥(euCube (n+1))) where
  toFun z := (z.2.1, pushFibreHom n hc1 (z.1, z.2.2))
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    ((pushFibreHom n hc1).continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

theorem lastCoord_pushMap (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc1 : |c| ≤ 1)
    (p : W × ↥(euCube (n+1))) : lastCoord n (pushMap n W hc1 p).2 = c := by
  show Cube.withLast (p.2 : Fin (n+1) → ℝ) c (Fin.last n) = c
  rw [Cube.withLast_last]

theorem lastCoord_pushHom (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc1 : |c| ≤ 1)
    (z : ↑unitInterval × (W × ↥(euCube (n+1)))) :
    lastCoord n (pushHom n W hc1 z).2 = interpLast n c (z.1 : ℝ) z.2.2 := by
  show Cube.withLast (z.2.2 : Fin (n+1) → ℝ) (interpLast n c (z.1 : ℝ) z.2.2) (Fin.last n)
      = interpLast n c (z.1 : ℝ) z.2.2
  rw [Cube.withLast_last]

theorem pushHom_zero (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc1 : |c| ≤ 1)
    (y : W × ↥(euCube (n+1))) : pushHom n W hc1 (0, y) = y := by
  refine Prod.ext rfl ?_
  exact pushFibreHom_zero n hc1 y.2

theorem pushHom_one (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc1 : |c| ≤ 1)
    (y : W × ↥(euCube (n+1))) : pushHom n W hc1 (1, y) = pushMap n W hc1 y := by
  refine Prod.ext rfl ?_
  exact pushFibreHom_one n hc1 y.2

/-! ## The piece and the relative part -/

/-- The piece `{last coordinate ∈ S}` of `W × euCube (n+1)`. -/
abbrev pieceSet (n : ℕ) (W : Type) (S : Set ℝ) : Set (W × ↥(euCube (n+1))) :=
  {p | lastCoord n p.2 ∈ S}

@[simp] theorem mem_pieceSet {n : ℕ} {W : Type} {S : Set ℝ} {p : W × ↥(euCube (n+1))} :
    p ∈ pieceSet n W S ↔ lastCoord n p.2 ∈ S := Iff.rfl

theorem pushMap_mem_pieceSet (n : ℕ) (W : Type) [TopologicalSpace W] {S : Set ℝ} {c : ℝ}
    (hc1 : |c| ≤ 1) (hcS : c ∈ S) {p : W × ↥(euCube (n+1))} (_hp : p ∈ pieceSet n W S) :
    pushMap n W hc1 p ∈ pieceSet n W S := by
  rw [mem_pieceSet, lastCoord_pushMap n W hc1 p]
  exact hcS

theorem pushMap_mem_bdrySet (n : ℕ) (W : Type) [TopologicalSpace W] {c : ℝ} (hc : |c| = 1)
    (p : W × ↥(euCube (n+1))) :
    pushMap n W (le_of_eq hc) p ∈ Cube.bdrySet (n+1) W := by
  rw [Cube.mem_bdrySet]
  show Cube.withLast (p.2 : Fin (n+1) → ℝ) c ∈ euCubeBdry (n+1)
  exact Cube.withLast_mem_euCubeBdry p.2.2 hc

theorem pushHom_mem_pieceSet (n : ℕ) (W : Type) [TopologicalSpace W] {S : Set ℝ} {c : ℝ}
    (hc1 : |c| ≤ 1) (hcS : c ∈ S) (hconv : Convex ℝ S) (t : ↑unitInterval)
    {p : W × ↥(euCube (n+1))} (hp : p ∈ pieceSet n W S) :
    pushHom n W hc1 (t, p) ∈ pieceSet n W S := by
  rw [mem_pieceSet, lastCoord_pushHom n W hc1 (t, p)]
  have hpS : lastCoord n p.2 ∈ S := hp
  have h := hconv hpS hcS (show (0:ℝ) ≤ 1 - (t:ℝ) by linarith [t.2.2])
    (show (0:ℝ) ≤ (t:ℝ) by linarith [t.2.1]) (by ring)
  have hmul : (1 - (t:ℝ)) * lastCoord n p.2 + (t:ℝ) * c ∈ S := by
    simpa only [smul_eq_mul] using h
  convert hmul using 1
  rw [interpLast]; ring

theorem pushHom_mem_bdrySet (n : ℕ) (W : Type) [TopologicalSpace W] {S : Set ℝ} {c : ℝ}
    (hc : |c| = 1) (_hcS : c ∈ S) (hunit : ∀ t ∈ S, |t| = 1 → t = c) (t : ↑unitInterval)
    {p : W × ↥(euCube (n+1))} (hp : p ∈ pieceSet n W S) (hpA : p ∈ Cube.bdrySet (n+1) W) :
    pushHom n W (le_of_eq hc) (t, p) ∈ Cube.bdrySet (n+1) W := by
  rw [Cube.mem_bdrySet]
  show Cube.withLast (p.2 : Fin (n+1) → ℝ) (interpLast n c (t : ℝ) p.2) ∈ euCubeBdry (n+1)
  have hpS : lastCoord n p.2 ∈ S := hp
  rw [Cube.mem_bdrySet] at hpA
  obtain ⟨-, i, hi⟩ := hpA
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hlast
  · refine ⟨Cube.withLast_mem_euCube p.2.2 (by
      have hx : |lastCoord n p.2| ≤ 1 := (mem_euCube.mp p.2.2) (Fin.last n)
      exact Cube.abs_interp_le_one hx (le_of_eq hc) t.2.1 t.2.2), ⟨j.castSucc, ?_⟩⟩
    rw [Cube.withLast_castSucc]
    exact hi
  · subst hlast
    have h1 : lastCoord n p.2 = c := hunit _ hpS (by rw [lastCoord]; exact hi)
    have hinterp : interpLast n c (t : ℝ) p.2 = c := by rw [interpLast, h1]; ring
    rw [hinterp]
    exact Cube.withLast_mem_euCubeBdry p.2.2 hc

end Piece

theorem subsingleton_pieceCoh_cube (n : ℕ) (W : Type) [TopologicalSpace W] (S : Set ℝ)
    (c : ℝ) (hc : |c| = 1) (hcS : c ∈ S) (hconv : Convex ℝ S)
    (hunit : ∀ t ∈ S, |t| = 1 → t = c) (j : ℕ) :
    Subsingleton (Work.Thom.Cube.pieceCoh n W S j) := by
  have hc1 : |c| ≤ 1 := le_of_eq hc
  have key := subsingleton_relComplex_of_homotopyData
    (U := Piece.pieceSet n W S) (A := Cube.bdrySet (n+1) W)
    (Piece.pushMap n W hc1) (Piece.pushHom n W hc1)
    (fun y => Piece.pushHom_zero n W hc1 y)
    (fun y => Piece.pushHom_one n W hc1 y)
    (fun y hy => Piece.pushMap_mem_pieceSet n W hc1 hcS hy)
    (fun y _ => Piece.pushMap_mem_bdrySet n W hc y)
    (fun t y hy => Piece.pushHom_mem_pieceSet n W hc1 hcS hconv t hy)
    (fun t y hy hyA => Piece.pushHom_mem_bdrySet n W hc hcS hunit t hy hyA)
    j
  show Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of ↥(Piece.pieceSet n W S))
      {y : ↥(Piece.pieceSet n W S) | (y : W × ↥(euCube (n+1))) ∈ Cube.bdrySet (n+1) W}).homology j)
  exact key

end Work.Thom
