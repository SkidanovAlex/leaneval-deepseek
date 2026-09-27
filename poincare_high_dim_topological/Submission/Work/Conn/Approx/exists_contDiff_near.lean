import Mathlib
import Submission.Work.Conn.Basic

namespace Work.Conn.Approx

open Metric (sphere)
open ContinuousMap

/-- Auxiliary norm estimate on a Euclidean space: the norm of a vector is at most the sum of the
norms of its coordinates.  (For `m = 0` both sides vanish.) -/
theorem norm_le_sum_norm_coord (m : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    ‖y‖ ≤ ∑ i, ‖y i‖ := by
  have hdec : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext j; simp
  calc ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := by conv_lhs => rw [hdec]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖y i‖ := by simp [PiLp.norm_single]

/-- The subalgebra of `C(Sph k, ℝ)` consisting of the functions on the sphere `𝕊ᵏ` that are the
restriction of a smooth (`C^∞`) function on the ambient Euclidean space `ℝᵏ⁺¹`. -/
noncomputable def smoothRestrictionSubalgebra (k : ℕ) : Subalgebra ℝ C(Sph k, ℝ) where
  carrier := {g | ∃ G : EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
    ContDiff ℝ ⊤ G ∧ ∀ x : Sph k, G x = g x}
  mul_mem' := by
    rintro g h ⟨G, hG, hGg⟩ ⟨H, hH, hHh⟩
    exact ⟨fun z => G z * H z, hG.mul hH, by intro x; simp [hGg x, hHh x]⟩
  one_mem' := ⟨fun _ => 1, contDiff_const, by intro x; simp⟩
  add_mem' := by
    rintro g h ⟨G, hG, hGg⟩ ⟨H, hH, hHh⟩
    exact ⟨fun z => G z + H z, hG.add hH, by intro x; simp [hGg x, hHh x]⟩
  zero_mem' := ⟨fun _ => 0, contDiff_const, by intro x; simp⟩
  algebraMap_mem' := by
    intro c
    exact ⟨fun _ => c, contDiff_const, by intro x; simp⟩

/-- The subalgebra of restrictions of smooth ambient functions separates the points of the sphere:
the ambient coordinate functions do. -/
theorem smoothRestrictionSubalgebra_separatesPoints (k : ℕ) :
    (smoothRestrictionSubalgebra k).SeparatesPoints := by
  intro x y hxy
  have hex : ∃ i : Fin (k + 1), (x : EuclideanSpace ℝ (Fin (k + 1))) i ≠
      (y : EuclideanSpace ℝ (Fin (k + 1))) i := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (by ext j; exact h j))
  obtain ⟨i, hi⟩ := hex
  let g : C(Sph k, ℝ) := ⟨fun z => (z : EuclideanSpace ℝ (Fin (k + 1))) i, by fun_prop⟩
  refine ⟨g, ⟨g, ?_, rfl⟩, ?_⟩
  · exact ⟨fun z : EuclideanSpace ℝ (Fin (k + 1)) => z i, by fun_prop, fun z => rfl⟩
  · exact hi

/-- Every continuous map `𝕊ᵏ → ℝᵐ` is uniformly approximated by the restriction of a smooth
(`C^∞`) map of the ambient space `ℝᵏ⁺¹`.  Here `Sph k` is `Work.Conn.Sph k`, the unit sphere of
`EuclideanSpace ℝ (Fin (k+1))`, and `dist` is the Euclidean distance.

Route: the set `A` of `g : C(Sph k, ℝ)` that are the restriction of a `ContDiff ℝ ⊤` function on
the ambient space is a subalgebra of `C(Sph k, ℝ)` (closure under `+`, `*`, scalars and constants
because sums/products/composites of smooth functions are smooth) which separates points: the
coordinate functions `x ↦ x i` do, and they are restrictions of continuous linear maps.
Stone–Weierstrass (`ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`)
approximates each coordinate of `f` within `ε` by an element of `A`; combine the `m` smooth
ambient functions into one smooth map `P` and bound the error with `‖y‖ ≤ ∑ i, ‖y i‖`. -/
theorem exists_contDiff_near (k m : ℕ) (f : C(Sph k, EuclideanSpace ℝ (Fin m))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ⊤ P ∧ ∀ x : Sph k, dist (P x) (f x) < ε := by
  classical
  set δ : ℝ := ε / ((m : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  choose g hgnear using fun i : Fin m =>
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (smoothRestrictionSubalgebra k) (smoothRestrictionSubalgebra_separatesPoints k)
      (fun x => f x i) (by fun_prop) δ hδ
  have hGex : ∀ i : Fin m, ∃ G : EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
      ContDiff ℝ ⊤ G ∧ ∀ x : Sph k, G x = (g i : Sph k → ℝ) x :=
    fun i => (g i).property
  choose G hGsmooth hGeq using hGex
  let P : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin m) :=
    fun z => WithLp.toLp 2 (fun i => G i z)
  have hP : ContDiff ℝ ⊤ P := by
    have h1 : ContDiff ℝ ⊤
        (fun z : EuclideanSpace ℝ (Fin (k + 1)) => fun i : Fin m => G i z) :=
      contDiff_pi.mpr (fun i => hGsmooth i)
    exact PiLp.contDiff_toLp.comp h1
  refine ⟨P, hP, ?_⟩
  intro x
  have hcoord : ∀ i : Fin m, ‖P x i - f x i‖ < δ := by
    intro i
    have h2 : ‖G i x - f x i‖ < δ := by
      rw [hGeq i x]
      simpa using hgnear i x
    simpa [P, PiLp.toLp_apply] using h2
  calc dist (P x) (f x) = ‖P x - f x‖ := dist_eq_norm _ _
    _ ≤ ∑ i, ‖(P x - f x) i‖ := norm_le_sum_norm_coord m _
    _ = ∑ i, ‖P x i - f x i‖ := by simp
    _ ≤ ∑ _i : Fin m, δ := Finset.sum_le_sum fun i _ => le_of_lt (hcoord i)
    _ = (m : ℝ) * δ := by simp [Finset.sum_const, Finset.card_univ]
    _ = (m : ℝ) * (ε / ((m : ℝ) + 1)) := by rw [hδdef]
    _ < ε := by
      have hlt : (m : ℝ) / ((m : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      calc (m : ℝ) * (ε / ((m : ℝ) + 1)) = ε * ((m : ℝ) / ((m : ℝ) + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
        _ = ε := by ring

end Work.Conn.Approx
