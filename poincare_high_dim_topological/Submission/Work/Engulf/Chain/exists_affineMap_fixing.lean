import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.Chain

/-- **The affine projection onto the affine span of `σ`**: for a nonempty affinely independent
`σ : Finset (PL.E N)` and a point `a` outside `affineSpan ℝ σ` there is an affine map `A` of the
ambient space which fixes `σ` pointwise (equivalently fixes `affineSpan ℝ σ` pointwise) and sends
`a` into `simp σ`.  This is the retraction `coneBd a σ → simp σ` used to extend `f` over the
lateral boundary of the cone `aσ` (E3 = Newman §12).

Suggested construction: pick `b ∈ σ` (e.g. a vertex) and `u := a - b ∉ direction (affineSpan ℝ σ)`;
take a linear map `L : PL.E N →ₗ[ℝ] PL.E N` which is the identity on `direction (affineSpan ℝ σ)`
and kills `u` (`direction (affineSpan ℝ σ) ⊓ span {u} = ⊥`, and a linear map defined on a submodule
extends to the whole space), and set `A x = b + L (x - b)`. -/
theorem exists_affineMap_fixing {N : ℕ} (σ : Finset (PL.E N)) (a : PL.E N)
    (hne : σ.Nonempty) (hind : AffineIndependent ℝ ((↑) : σ → PL.E N))
    (ha : a ∉ (affineSpan ℝ (σ : Set (PL.E N)) : Set (PL.E N))) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E N, (∀ v ∈ σ, A v = v) ∧ A a ∈ PL.simp σ := by
  -- Pick a vertex `b ∈ σ`; it lies in the affine span of `σ`.
  obtain ⟨b, hb⟩ := hne
  have hb_mem : b ∈ affineSpan ℝ (σ : Set (PL.E N)) :=
    subset_affineSpan ℝ (σ : Set (PL.E N)) (by simpa using hb)
  -- `D` is the direction of the affine span, and `u := a - b` is outside it.
  set D := (affineSpan ℝ (σ : Set (PL.E N))).direction with hD
  have hu : a -ᵥ b ∉ D := by
    rw [hD]
    intro h
    exact ha ((AffineSubspace.vsub_right_mem_direction_iff_mem hb_mem a).mp h)
  -- A linear map fixing `D` pointwise and killing `u`.
  obtain ⟨g, hg_comp, hg_u⟩ :=
    LinearMap.exists_extend_of_notMem (p := D) (v := a -ᵥ b) D.subtype hu 0
  have hg_fix : ∀ x ∈ D, g x = x := by
    intro x hx
    have h1 := LinearMap.congr_fun hg_comp ⟨x, hx⟩
    simpa using h1
  -- The affine map `A x = g x + (b - g b)`, i.e. `A x = b + g (x - b)`.
  refine ⟨⟨fun x => g x + (b - g b), g, ?_⟩, ?_, ?_⟩
  · intro p v
    simp only [vadd_eq_add, map_add]
    abel
  · -- `A` fixes `σ` pointwise.
    intro v hv
    have hv_mem : v ∈ affineSpan ℝ (σ : Set (PL.E N)) :=
      subset_affineSpan ℝ (σ : Set (PL.E N)) (by simpa using hv)
    have hvb : v -ᵥ b ∈ D := by
      rw [hD]
      exact (AffineSubspace.vsub_right_mem_direction_iff_mem hb_mem v).mpr hv_mem
    have hgvb : g (v -ᵥ b) = v -ᵥ b := hg_fix _ hvb
    have key : g v = g b + (v - b) := by
      have h2 : g v - g b = v - b := by
        rw [← map_sub]
        simpa [vsub_eq_sub] using hgvb
      rw [← h2]; abel
    change g v + (b - g b) = v
    rw [key]; abel
  · -- `A a = b ∈ simp σ`.
    have key : g a = g b := by
      have h2 : g a - g b = 0 := by
        rw [← map_sub]
        simpa [vsub_eq_sub] using hg_u
      exact sub_eq_zero.mp h2
    have haz : g a + (b - g b) = b := by
      rw [key]; abel
    change g a + (b - g b) ∈ PL.simp σ
    rw [haz]
    exact subset_convexHull ℝ (σ : Set (PL.E N)) (by simpa using hb)

end Work.Engulf.Chain
