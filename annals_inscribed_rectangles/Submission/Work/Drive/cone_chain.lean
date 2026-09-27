import Mathlib
import Submission.Work.Drive.parity_tools_defs

/-!
# The cone filling a loop, and the symmetry of its two seam faces

Sub-case 3 of `SURF_PLAN.md` ("fill / comparison"): a closed loop of the plane bounds a 2-chain — the
*cone* over it from a point off the loop — and a closed loop then meets any closed curve evenly.  This
file builds the 2-chain and proves the piece of boundary bookkeeping that removes the "other faces"
from the count: **the two `s`-faces (the seams) of the square contribute equally**.

For a 2-chain `D : ℝ² → ℝ²` whose two `s`-faces carry the same map (`D (0,u) = D (1,u)` — true for the
cone over a *closed* loop, `cone_seam_eq`) and a 1-chain `N : ℝ → ℝ²`, the zeros of the difference map
`genDiff D N` on the faces `{x 0 = 0}` and `{x 0 = 1}` of the box `Amb 2` are exchanged by the flip
`x 0 ↦ 1 - x 0`, which preserves the difference map exactly because the two seam maps agree.  Hence the
two seam counts are equal and their total contribution to `meetD D N` is even; with the apex face
(`x 1 = 0`, where `D` is constant) empty and `Work.Drive.even_ncard_meetD_of_closed` making `meetD`
itself even, the remaining face — the loop `x 1 = 1` — has an even count, which is the "closed loop
meets a closed curve evenly" statement of sub-case 3.
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000

noncomputable section

/-! ## Points of the square and of the box -/

/-- The point `(s,u)` of the square `[0,1]²`, the argument of a `2`-chain. -/
def mk2 (s u : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![s, u]

@[simp] lemma mk2_apply_zero (s u : ℝ) : mk2 s u 0 = s := rfl

@[simp] lemma mk2_apply_one (s u : ℝ) : mk2 s u 1 = u := rfl

/-- The point `(s,u,z)` of the box `Amb 2`: the square's two coordinates followed by the curve's. -/
def mkBox (s u z : ℝ) : Amb 2 := WithLp.toLp 2 ![s, u, z]

@[simp] lemma mkBox_zero (s u z : ℝ) : mkBox s u z 0 = s := rfl

@[simp] lemma mkBox_one (s u z : ℝ) : mkBox s u z 1 = u := rfl

@[simp] lemma mkBox_two (s u z : ℝ) : mkBox s u z 2 = z := rfl

lemma mkBox_mem_unitBox {s u z : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) : mkBox s u z ∈ unitBox 2 := by
  intro i
  fin_cases i
  · simpa using hs
  · simpa using hu
  · simpa using hz

/-- Every point of the box is `(x 0, x 1, x 2)`. -/
lemma eq_mkBox (x : Amb 2) : x = mkBox (x 0) (x 1) (x 2) := by
  ext i
  fin_cases i <;> rfl

/-! ## The cone over a loop -/

/-- The **cone** over a loop `ℓ` from an apex `p₀`: the 2-chain `(s,u) ↦ p₀ + u • (ℓ s - p₀)`, whose
`u = 1` face is `ℓ` and whose `u = 0` face is the constant `p₀`. -/
def cone (ℓ : ℝ → EuclideanSpace ℝ (Fin 2)) (p₀ : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun x => p₀ + x 1 • (ℓ (x 0) - p₀)

@[simp] lemma cone_mk2 (ℓ : ℝ → EuclideanSpace ℝ (Fin 2)) (p₀ : EuclideanSpace ℝ (Fin 2))
    (s u : ℝ) : cone ℓ p₀ (mk2 s u) = p₀ + u • (ℓ s - p₀) := rfl

/-- The two seam faces of the cone over a **closed** loop carry the same map. -/
lemma cone_seam_eq (ℓ : ℝ → EuclideanSpace ℝ (Fin 2)) (p₀ : EuclideanSpace ℝ (Fin 2))
    (hℓ : ℓ 0 = ℓ 1) (u : ℝ) : cone ℓ p₀ (mk2 0 u) = cone ℓ p₀ (mk2 1 u) := by
  rw [cone_mk2, cone_mk2, hℓ]

/-! ## The coordinate flip -/

/-- Flip the first coordinate of the box: `(s,u,z) ↦ (1 - s, u, z)`.  It exchanges the two seam faces
and preserves the box. -/
def flipFirst (x : Amb 2) : Amb 2 := mkBox (1 - x 0) (x 1) (x 2)

@[simp] lemma flipFirst_zero (x : Amb 2) : flipFirst x 0 = 1 - x 0 := rfl

@[simp] lemma flipFirst_one (x : Amb 2) : flipFirst x 1 = x 1 := rfl

@[simp] lemma flipFirst_two (x : Amb 2) : flipFirst x 2 = x 2 := rfl

lemma flipFirst_invol (x : Amb 2) : flipFirst (flipFirst x) = x := by
  ext i
  fin_cases i <;> simp [flipFirst, mkBox]

lemma flipFirst_mem_unitBox {x : Amb 2} (h : x ∈ unitBox 2) : flipFirst x ∈ unitBox 2 := by
  rw [show flipFirst x = mkBox (1 - x 0) (x 1) (x 2) from rfl]
  have h0 : (0 : ℝ) ≤ x 0 ∧ x 0 ≤ 1 := by simpa using h 0
  refine mkBox_mem_unitBox ⟨?_, ?_⟩ (h 1) (h 2) <;> linarith [h0.1, h0.2]

/-- The `p`-projection of the box is the first two coordinates. -/
lemma pqPart_apply_box (x : Amb 2) : pqPart 2 1 x = mk2 (x 0) (x 1) := by
  ext i
  fin_cases i <;> rfl

/-- The `q`-projection of the box is the last coordinate. -/
lemma qpPart_apply_box (x : Amb 2) : qpPart 2 1 x = WithLp.toLp 2 ![x 2] := by
  ext i
  fin_cases i <;> rfl

/-- The zero set of the difference map on the seam face `{x 0 = a}`. -/
def seamZero {D : EuclideanSpace ℝ (Fin 2) → Tgt 2}
    (N : EuclideanSpace ℝ (Fin 1) → Tgt 2) (a : ℝ) : Set (Amb 2) :=
  {x | x ∈ unitBox 2 ∧ x 0 = a ∧ genDiff D N x = 0}

/-- **The seam symmetry.**  If the two `s`-faces of the 2-chain `D` carry the same map
(`D (0,u) = D (1,u)`, true for the cone over a closed loop, `cone_seam_eq`), then the difference map
has equally many zeros on the two seam faces `{x 0 = 0}` and `{x 0 = 1}`: the flip
`x 0 ↦ 1 - x 0` (`flipFirst`) is a bijection of the box which preserves the difference map, because
`pqPart` of a flipped point is the flipped `pqPart`, the `q`-part is unchanged, and the two seam maps
of `D` agree. -/
theorem ncard_seamZero_eq {D : EuclideanSpace ℝ (Fin 2) → Tgt 2}
    {N : EuclideanSpace ℝ (Fin 1) → Tgt 2}
    (hD : ∀ u : ℝ, D (mk2 0 u) = D (mk2 1 u)) :
    (seamZero (D := D) N 0).ncard = (seamZero (D := D) N 1).ncard := by
  classical
  -- the flip preserves the difference map, on the face `{x 0 = 0}`
  have key : ∀ x : Amb 2, x 0 = 0 →
      (genDiff D N (flipFirst x) = 0 ↔ genDiff D N x = 0) := by
    intro x hx
    have hqx : qpPart 2 1 (flipFirst x) = qpPart 2 1 x := by
      rw [qpPart_apply_box, qpPart_apply_box]
      have e : (flipFirst x) 2 = x 2 := rfl
      rw [e]
    have h1 : pqPart 2 1 (flipFirst x) = mk2 1 (x 1) := by
      rw [pqPart_apply_box]
      have e0 : (flipFirst x) 0 = 1 := by rw [flipFirst_zero, hx]; norm_num
      have e1 : (flipFirst x) 1 = x 1 := rfl
      rw [e0, e1]
    have h2 : pqPart 2 1 x = mk2 0 (x 1) := by
      rw [pqPart_apply_box, hx]
    show D (pqPart 2 1 (flipFirst x)) - N (qpPart 2 1 (flipFirst x)) = 0 ↔
      D (pqPart 2 1 x) - N (qpPart 2 1 x) = 0
    rw [hqx, h1, h2, ← hD (x 1)]
  have himg : flipFirst '' (seamZero (D := D) N 0) = seamZero (D := D) N 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hybox, hy0, hyz⟩, rfl⟩
      exact ⟨flipFirst_mem_unitBox hybox, by simp only [flipFirst_zero, hy0, sub_zero],
        (key y hy0).mpr hyz⟩
    · rintro ⟨hxbox, hx1, hxz⟩
      have hf0 : (flipFirst x) 0 = 0 := by simp only [flipFirst_zero, hx1, sub_self]
      have hflip : genDiff D N (flipFirst (flipFirst x)) = 0 := by
        rw [flipFirst_invol]
        exact hxz
      exact ⟨flipFirst x, ⟨flipFirst_mem_unitBox hxbox, hf0, (key (flipFirst x) hf0).mp hflip⟩,
        flipFirst_invol x⟩
  have hinj : Function.Injective flipFirst := by
    intro a b h
    have h0 : a 0 = b 0 := by
      have hh := congrArg (fun z : Amb 2 => z 0) h
      simp only [flipFirst_zero] at hh
      linarith
    have h1 : a 1 = b 1 := by
      have hh := congrArg (fun z : Amb 2 => z 1) h
      simpa only [flipFirst_one] using hh
    have h2 : a 2 = b 2 := by
      have hh := congrArg (fun z : Amb 2 => z 2) h
      simpa only [flipFirst_two] using hh
    rw [eq_mkBox a, eq_mkBox b, h0, h1, h2]
  rw [← himg]
  exact (Set.ncard_image_of_injective (seamZero (D := D) N 0) hinj).symm

end

end Work.Drive
