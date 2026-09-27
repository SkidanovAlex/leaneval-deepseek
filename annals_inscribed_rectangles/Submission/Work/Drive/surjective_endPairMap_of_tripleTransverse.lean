import Mathlib
import Submission.Work.Drive.encodedTransverse
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.ppParity.Defs

/-!
# The pair map `(s, u, y, z) ↦ (d₀ u − d₁ y, d₀ u − d₂ z)` of a transverse triple is onto

`Work.Drive.TripleTransverse d₀ d₁ d₂` says that the difference map
`(v₀,v₁,v₂) ↦ (d₀v₀ − d₁v₁, d₀v₀ − d₂v₂)` of the three derivatives is **onto** `ℝ⁴ × ℝ⁴`.  The pair
map of the box-parity engine (`Submission/Work/Drive/pairMeetDefs.lean`) uses only a *restricted*
domain: the first block is `mk (ftU x)` — the first parameter is `u ∈ ℝ²`, pushed into `ℝ³` by a
linear map `mk` onto the plane `{v | v 2 = 0}` — while the two sweep parameters `y, z ∈ ℝ³` are free.
So the pair map factors as

> `ℝ² × ℝ³ × ℝ³ → ℝ⁴ × ℝ⁴`,  `(u, y, z) ↦ (d₀ (mk u) − d₁ y, d₀ (mk u) − d₂ z)`,

an `8`-parameter map, and the question is whether it is still onto.  It is, and the only input beyond
`TripleTransverse` is the **common direction** hypothesis `hcd`: a common tangent direction `c` of the
three derivatives (`TripleCommonDir`, i.e. an element of the kernel of the difference map) whose
*first* component has non-zero `2`-coordinate.

The proof is a one-line cancellation.  Take any `(w₁, w₂)`; transversality gives a triple
`(v₀,v₁,v₂)` solving it.  Subtracting the multiple `λ = (v₀)₂ / (c₀)₂` of the common direction `c`
from the triple leaves the two differences unchanged (the difference map is linear and kills `c`) and
kills the `2`-coordinate of the first block — and the plane `{v 2 = 0}` is exactly the range of `mk`
(`hmksurj`).  No dimension theory is needed; the whole content of `hcd` is that *some* kernel
direction moves the plane `{v₀ 2 = 0}` off the kernel.

This is the surjectivity input of the box-parity engine at the level of the *derivatives*: it says
that the triple intersection of the three chains, viewed through the pair map, meets every target
value, i.e. that the pair-meet equation is solvable at every point of the box and also with the first
coordinate of the box pinned to `0` (the slice used by the boundary parity `K 0 ≡ K 1`).
-/

set_option autoImplicit false

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-! ## The point of the `9`-box with prescribed blocks -/

/-- **The point of the `9`-box with prescribed parameter blocks `u, y, z`** and first coordinate `0`:
its `u`-block (`ftU`) is `u`, its first sweep block (`ftY`) is `y`, its second sweep block (`ftZ`) is
`z`, and the family coordinate `x 0` is `0`. -/
def mkZ (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 ![(0 : ℝ), u 0, u 1, y 0, y 1, y 2, z 0, z 1, z 2]

lemma ftU_mkZ (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftU (mkZ u y z) = u := by
  ext i
  fin_cases i <;> rfl

lemma ftY_mkZ (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftY (mkZ u y z) = y := by
  ext i
  fin_cases i <;> rfl

lemma ftZ_mkZ (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftZ (mkZ u y z) = z := by
  ext i
  fin_cases i <;> rfl

lemma mkZ_apply_zero (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    (mkZ u y z) 0 = 0 := rfl

/-! ## The flat solution of the pair equation -/

/-- **The pair equation `d₀ (mk u) − d₁ y = w₁`, `d₀ (mk u) − d₂ z = w₂` is always solvable.**  Given
the transversality of the triple and a common direction `c` with `(c 0) 2 ≠ 0`, every pair
`(w₁, w₂)` is realised by parameters `(u, y, z)` with `u ∈ ℝ²` (i.e. with the first block in the
plane `{v 2 = 0}`), the two sweeps being arbitrary vectors of `ℝ³`. -/
lemma exists_flat_solution_of_tripleTransverse
    (mk : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hmksurj : ∀ v : EuclideanSpace ℝ (Fin 3), v 2 = 0 → ∃ a, mk a = v)
    (d0 d1 d2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hT : TripleTransverse d0 d1 d2)
    (hcd : ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
      TripleCommonDir d0 d1 d2 v ∧ (v 0) 2 ≠ 0)
    (w₁ w₂ : EuclideanSpace ℝ (Fin 4)) :
    ∃ u : EuclideanSpace ℝ (Fin 2), ∃ y z : EuclideanSpace ℝ (Fin 3),
      d0 (mk u) - d1 y = w₁ ∧ d0 (mk u) - d2 z = w₂ := by
  obtain ⟨v, hv1, hv2⟩ := hT w₁ w₂
  obtain ⟨c, hc, hcs⟩ := hcd
  have hs : (c 0) 2 ≠ 0 := hcs
  -- the multiple of the common direction that kills the `2`-coordinate of the first block
  let lam : ℝ := (v 0) 2 / (c 0) 2
  let v' : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun k => v k - lam • c k
  have hv'2 : (v' 0) 2 = 0 := by
    dsimp only [v', lam]
    rw [WithLp.ofLp_sub, WithLp.ofLp_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hs, sub_self]
  -- the difference map kills the common direction, so the two differences are unchanged
  have h1 : d0 (v' 0) - d1 (v' 1) = w₁ := by
    have eq1 : d0 (v' 0) - d1 (v' 1) = d0 (v 0) - d1 (v 1) := by
      dsimp only [v']
      simp only [map_sub, map_smul, hc.1]
      abel
    rw [eq1, hv1]
  have h2 : d0 (v' 0) - d2 (v' 2) = w₂ := by
    have eq1 : d0 (v' 0) - d2 (v' 2) = d0 (v 0) - d2 (v 2) := by
      dsimp only [v']
      simp only [map_sub, map_smul, hc.2]
      abel
    rw [eq1, hv2]
  obtain ⟨u, hu⟩ := hmksurj (v' 0) hv'2
  exact ⟨u, v' 1, v' 2, by rw [hu]; exact h1, by rw [hu]; exact h2⟩

/-! ## The surjectivity of the pair map -/

theorem surjective_endPairMap_of_tripleTransverse
    (mk : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hmk : ∀ a : EuclideanSpace ℝ (Fin 2), (mk a) 2 = 0)
    (hmksurj : ∀ v : EuclideanSpace ℝ (Fin 3), v 2 = 0 → ∃ a, mk a = v)
    (d0 d1 d2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hT : Work.Drive.TripleTransverse d0 d1 d2)
    (hcd : ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
      Work.Drive.TripleCommonDir d0 d1 d2 v ∧ (v 0) 2 ≠ 0) :
    Function.Surjective (fun z : EuclideanSpace ℝ (Fin 9) =>
        (d0 (mk (Work.Drive.ftU z)) - d1 (Work.Drive.ftY z),
          d0 (mk (Work.Drive.ftU z)) - d2 (Work.Drive.ftZ z))) ∧
      Function.Surjective (fun z : {z : EuclideanSpace ℝ (Fin 9) // z 0 = 0} =>
        (d0 (mk (Work.Drive.ftU z.1)) - d1 (Work.Drive.ftY z.1),
          d0 (mk (Work.Drive.ftU z.1)) - d2 (Work.Drive.ftZ z.1))) := by
  have key : ∀ w₁ w₂ : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin 2),
      ∃ y z : EuclideanSpace ℝ (Fin 3),
        d0 (mk u) - d1 y = w₁ ∧ d0 (mk u) - d2 z = w₂ :=
    exists_flat_solution_of_tripleTransverse mk hmksurj d0 d1 d2 hT hcd
  constructor
  · rintro ⟨w₁, w₂⟩
    obtain ⟨u, y, z, h₁, h₂⟩ := key w₁ w₂
    exact ⟨mkZ u y z, by simp only [ftU_mkZ, ftY_mkZ, ftZ_mkZ, h₁, h₂]⟩
  · rintro ⟨w₁, w₂⟩
    obtain ⟨u, y, z, h₁, h₂⟩ := key w₁ w₂
    exact ⟨⟨mkZ u y z, mkZ_apply_zero u y z⟩,
      by simp only [ftU_mkZ, ftY_mkZ, ftZ_mkZ, h₁, h₂]⟩

end

end Work.Drive
