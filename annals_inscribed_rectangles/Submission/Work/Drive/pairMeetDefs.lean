import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.SeamMeetDefs
import Submission.Work.Drive.SeamSweep

/-!
# T1/T3 of the radial-collapse transport: the pair-meet (split `D₀`) box-parity engine

The radial collapse (`Submission/Work/Drive/TRANSPORT_COLLAPSE_STATUS.md`, the lead's design of
2026-09-25 11:00) computes the transport `n_P ≡ ε_Q · ε_R` as the bordism invariance of the count

> `K s = #{(u, y, z) ∈ □ × □ × □ | E s u = V y ∧ E' u = W z}`

of the **pair meets** of a one-parameter family `s ↦ E s` of `2`-chains (the collapsed planes
`colPlane β Q s`) with a fixed `3`-chain `V`, *simultaneously* with the meets of the fixed `2`-chain
`E'` (the plane `diskPlane Q`) with a fixed `3`-chain `W`.  The parameter count is `2 + 3 + 3 = 8`
(the plane parameter `u` and the two sweep parameters `y, z`), so the meets are *isolated* and the
bordism statement is the mod-2 boundary parity (`Submission.Drive.ParityProp`, proved as
`Work.Drive.boxParity`) for the **difference map on the `9`-box** that carries the family parameter `s`
as its first coordinate:

> `pairDiff E E' V W x = (E (x 0) (ftU x) − V (ftY x), E' (ftU x) − W (ftZ x))`,

packed into `ℝ⁸` by `pairUp`/`pair44`.  Its zeros are the pair meets at the family parameter `x 0`, and
`boxParity` gives an even number of zeros on the boundary of the `9`-box.  Splitting the boundary zeros
by their unique face coordinate (`hface`):

* the two `s`-faces give `K 0` and `K 1` (the two counts whose parities are to be compared);
* the `u`- and `y`- and `z`-*seam* faces are paired pairwise by the seam involutions `seamInv2`
  (on `u`) and `seamInv` (on `y`, `z`), using only the *seam invariance* of the four chains
  (`hseamU`, `hseamU'`, `hseamV`, `hseamW`) — each pairing is a fixed-point-free involution, so the
  total contribution of each pair of faces is even;
* the `y`- and `z`-*level* faces (`ftY2 x ∈ {0,1}`, `ftZ2 x ∈ {0,1}`: the top face of a sweep, where
  the sweep is the plane itself, and the bottom face at the level `c`) carry no zeros at all
  (`havY`, `havZ`).

Hence `K 0 + K 1` is even.  This file holds the vocabulary; the theorem is delegated as
`Work.Drive.even_ncard_pairMeetBdry`.
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The packing `ℝ⁴ × ℝ⁴ → ℝ⁸` -/

/-- **Two vectors of `ℝ⁴` stacked into a vector of `ℝ⁸`** (the first four coordinates the first vector,
the last four the second).  This is the same packing as `Work.Drive.pair33` one dimension up. -/
def pair44 (a b : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 fun k : Fin 8 =>
    if h : k.val < 4 then a ⟨k.val, h⟩ else b ⟨k.val - 4, by omega⟩

@[simp] lemma pair44_apply_fst (a b : EuclideanSpace ℝ (Fin 4)) (k : Fin 4) :
    pair44 a b (Fin.castAdd 4 k) = a k := by
  simp only [pair44, WithLp.ofLp_toLp]
  rw [dif_pos (by simp)]
  exact congrArg a (Fin.ext (by simp))

@[simp] lemma pair44_apply_snd (a b : EuclideanSpace ℝ (Fin 4)) (k : Fin 4) :
    pair44 a b (Fin.natAdd 4 k) = b k := by
  simp only [pair44, WithLp.ofLp_toLp]
  rw [dif_neg (by simp)]
  exact congrArg b (Fin.ext (by simp))

/-! ## The coordinate blocks of the `9`-box -/

/-- The family parameter of a point of the `9`-box. -/
def ftS (x : EuclideanSpace ℝ (Fin 9)) : ℝ := x 0

/-- The plane parameter `u` of a point of the `9`-box (the coordinates `1, 2`). -/
def ftU (x : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i : Fin 2 => x ⟨1 + i.val, by omega⟩

/-- The first sweep parameter `y` of a point of the `9`-box (the coordinates `3, 4, 5`). -/
def ftY (x : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i : Fin 3 => x ⟨3 + i.val, by omega⟩

/-- The second sweep parameter `z` of a point of the `9`-box (the coordinates `6, 7, 8`). -/
def ftZ (x : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i : Fin 3 => x ⟨6 + i.val, by omega⟩

/-- The **level** coordinate of the first sweep parameter (the `x 2` of the sweep's cube: the top face
`= 1` is the plane itself, the bottom face `= 0` is the shadow at the level `c`). -/
def ftY2 (x : EuclideanSpace ℝ (Fin 9)) : ℝ := x ⟨5, by omega⟩

/-- The level coordinate of the second sweep parameter. -/
def ftZ2 (x : EuclideanSpace ℝ (Fin 9)) : ℝ := x ⟨8, by omega⟩

/-! ## The pair difference map and the pair meet set -/

/-- **The pair difference map of the collapse family**: at the point `x = (s, u, y, z)` of the `9`-box
it is the pair `(E s u − V y, E' u − W z)` of `ℝ⁴`-vectors.  Its zeros are exactly the *pair meets*
of the family at the parameter `s = x 0`. -/
def pairDiff (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
  fun x => pair44 (E (ftS x) (ftU x) - V (ftY x)) (E' (ftU x) - W (ftZ x))

/-- **The pair meet set at the family parameter `s`**: the parameter triples `(u, y, z)` of the box at
which the two pair equations hold simultaneously. -/
def pairMeetSet (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) (s : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2.1 ∈ Submission.Drive.unitBox 2 ∧
       p.2.2 ∈ Submission.Drive.unitBox 2 ∧ E s p.1 = V p.2.1 ∧ E' p.1 = W p.2.2}

/-- **The zeros of the pair difference map are the pair meets**: `pairDiff E E' V W x = 0` iff the two
pair equations `E (x 0) u = V y` and `E' u = W z` hold for the blocks `u, y, z` of `x`. -/
lemma pairDiff_eq_zero_iff (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 9)) :
    pairDiff E E' V W x = 0 ↔ E (ftS x) (ftU x) = V (ftY x) ∧ E' (ftU x) = W (ftZ x) := by
  have hpair : pairDiff E E' V W x
      = pair44 (E (ftS x) (ftU x) - V (ftY x)) (E' (ftU x) - W (ftZ x)) := rfl
  constructor
  · intro h
    have h1 : E (ftS x) (ftU x) - V (ftY x) = 0 := by
      ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.castAdd 4 j)) h
      rw [hpair] at this
      simpa using this
    have h2 : E' (ftU x) - W (ftZ x) = 0 := by
      ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.natAdd 4 j)) h
      rw [hpair] at this
      simpa using this
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [hpair, sub_eq_zero.mpr h1, sub_eq_zero.mpr h2]
    ext i
    fin_cases i <;> simp [pair44]

end

end Work.Drive
