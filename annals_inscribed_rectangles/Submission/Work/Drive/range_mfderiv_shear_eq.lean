import Mathlib
import Submission.Work.Drive.shear_param_directions
import Submission.Work.Drive.shear_fderiv
import Submission.Work.Drive.projTimesLine

/-!
# The range of the class derivative of the sheared family does not depend on the shear

`Work.Drive.shear q` is the clamped cross-shear of the parameter square
(`Submission/Work/Drive/encodedShear.lean`).  The point of the present file is that *precomposing a
class map `A : 𝔼² → ℝP³` with the shear does not change the **range** of its derivative*:

`range (mfderiv (q' ↦ A (shear q' u)) q) = range (mfderiv A (shear q u))`,

provided `A` is `C^∞` and its derivative annihilates the first (resp. second) coordinate direction at
every point whose first (resp. second) coordinate is `0` or `1`.

The two hypotheses are exactly the *boundary clamping* of the class map: the shear of the square fixes
the two coordinate directions at the corresponding pair of faces.  The proof is elementary:

* the chain rule writes the derivative of the composite as `D ∘ E`, where `D` is the derivative of `A`
  and `E` the parameter derivative of `q' ↦ shear q' u`;
* `Work.Drive.shear_param_directions` shows that `hb (u 0) • e₀` and `hb (u 1) • e₁` lie in
  `range E`, and `hb x` vanishes exactly at `x ∈ {0,1}`;
* the coordinate `i` of the sheared point equals `uᵢ` as soon as `hb uᵢ = 0` (the shear moves a
  coordinate by a multiple of `hb` of *that* coordinate), and in that case `A`'s hypothesis applies and
  the corresponding basis vector lies in `ker D`;
* hence at every point `u` the two basis directions `e₀`, `e₁` lie in `range E ⊔ ker D`, and for
  linear maps this means `range (D ∘ E) = range D`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. Elementary helpers -/

/-- The parabola bump vanishes exactly at the two ends of the unit interval (no box hypothesis). -/
private lemma range_mfderiv_shear_hb_eq_zero_iff {x : ℝ} : hb x = 0 ↔ x = 0 ∨ x = 1 := by
  unfold hb
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

/-- A vector of `𝔼²` is the sum of its two coordinates against the standard basis. -/
private lemma range_mfderiv_shear_eq_smul_single (v : EuclideanSpace ℝ (Fin 2)) :
    v = v 0 • (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2))
      + v 1 • (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;> simp

/-- The two standard basis vectors of `𝔼²` span it. -/
private lemma range_mfderiv_shear_span_pair_top :
    Submodule.span ℝ ({(EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)),
      (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2))} :
        Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [range_mfderiv_shear_eq_smul_single v]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- **Linear algebra.**  If the range of `E` together with the kernel of `D` fill the intermediate
space, then `D` and `D ∘ E` have the same range. -/
private lemma range_mfderiv_shear_range_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (D : V →L[ℝ] W) (E : U →L[ℝ] V)
    (h : (E : U →ₗ[ℝ] V).range ⊔ (D : V →ₗ[ℝ] W).ker = ⊤) :
    ((D : V →ₗ[ℝ] W).comp (E : U →ₗ[ℝ] V)).range = (D : V →ₗ[ℝ] W).range := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨x, rfl⟩
    exact ⟨(E : U →ₗ[ℝ] V) x, rfl⟩
  · intro w hw
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
    obtain ⟨m, hm, k, hk, hmk⟩ := (Submodule.sup_eq_top_iff _ _).mp h v
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hm
    refine LinearMap.mem_range.mpr ⟨x, ?_⟩
    rw [LinearMap.comp_apply, ← hv, hmk, ← hx, map_add, LinearMap.mem_ker.mp hk, add_zero]

/-! ## 2. The theorem -/

private abbrev RMSE2 := EuclideanSpace ℝ (Fin 2)
private abbrev RMSE3 := EuclideanSpace ℝ (Fin 3)
private abbrev RMSE4 := EuclideanSpace ℝ (Fin 4)

theorem range_mfderiv_shear_eq
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) A →
    (∀ y : EuclideanSpace ℝ (Fin 2), (y 0 = 0 ∨ y 0 = 1) →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A y
        (EuclideanSpace.single 0 1) = 0) →
    (∀ y : EuclideanSpace ℝ (Fin 2), (y 1 = 0 ∨ y 1 = 1) →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A y
        (EuclideanSpace.single 1 1) = 0) →
    (u : EuclideanSpace ℝ (Fin 2)) → (q : EuclideanSpace ℝ (Fin 4)) →
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (fun q' : EuclideanSpace ℝ (Fin 4) => A (Work.Drive.shear q' u)) q).range =
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A (Work.Drive.shear q u)).range := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
    Work.Drive.projCharted 3
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
    Work.Drive.isManifold_projCharted 3
  intro hA hA0 hA1 u q
  -- name the two derivatives at the *concrete* types `𝔼²`, `𝔼³`
  let D : RMSE2 →L[ℝ] RMSE3 :=
    mfderiv (modelWithCornersSelf ℝ RMSE2) (modelWithCornersSelf ℝ RMSE3) A (shear q u)
  let E : RMSE4 →L[ℝ] RMSE2 :=
    mfderiv (modelWithCornersSelf ℝ RMSE4) (modelWithCornersSelf ℝ RMSE2)
      (fun q' : RMSE4 => shear q' u) q
  have hDdef : D = mfderiv (modelWithCornersSelf ℝ RMSE2) (modelWithCornersSelf ℝ RMSE3)
      A (shear q u) := rfl
  have hEdef : E = mfderiv (modelWithCornersSelf ℝ RMSE4) (modelWithCornersSelf ℝ RMSE2)
      (fun q' : RMSE4 => shear q' u) q := rfl
  -- the parameter map `q' ↦ shear q' u` is smooth, hence differentiable
  have hshearDiff : DifferentiableAt ℝ
      (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u) q := by
    have hfun : (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u)
        = fun q' => spdPhiT u (ballClamp q') := by
      funext q'
      exact (spdPhiT_ballClamp q' u).symm
    rw [hfun]
    exact (spdDifferentiableAt_PhiT u (ballClamp q)).comp q
      (spdHasFDerivAt_ballClamp q).differentiableAt
  have hL' : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u) q :=
    hshearDiff.mdifferentiableAt
  have hAd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A (shear q u) :=
    hA.mdifferentiableAt (by simp)
  -- the chain rule
  have hchain : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u)) q =
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A (shear q u)).comp
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u) q) := by
    simpa [Function.comp_def] using
      (mfderiv_comp (f := fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u) (g := A) q hAd hL')
  -- the boundary hypotheses, at the point `shear q u`
  have hker0 : ((shear q u) 0 = 0 ∨ (shear q u) 0 = 1) →
      (EuclideanSpace.single 0 (1 : ℝ) : RMSE2) ∈ D.ker := fun hy =>
    LinearMap.mem_ker.mpr (hA0 (shear q u) hy)
  have hker1 : ((shear q u) 1 = 0 ∨ (shear q u) 1 = 1) →
      (EuclideanSpace.single 1 (1 : ℝ) : RMSE2) ∈ D.ker := fun hy =>
    LinearMap.mem_ker.mpr (hA1 (shear q u) hy)
  -- the two parameter directions of the shear lie in the range of `E`
  have hE0 : hb (u 0) • (EuclideanSpace.single 0 (1 : ℝ) : RMSE2) ∈ E.range := by
    have h := (shear_param_directions q u).1
    rw [spdSpanRangeApply_eq_range] at h
    simpa only [hEdef, mfderiv_eq_fderiv] using h
  have hE1 : hb (u 1) • (EuclideanSpace.single 1 (1 : ℝ) : RMSE2) ∈ E.range := by
    have h := (shear_param_directions q u).2
    rw [spdSpanRangeApply_eq_range] at h
    simpa only [hEdef, mfderiv_eq_fderiv] using h
  -- the range of `E` together with the kernel of `D` fill `𝔼²`
  have hsup : E.range ⊔ D.ker = ⊤ := by
    rw [eq_top_iff, ← range_mfderiv_shear_span_pair_top]
    refine Submodule.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · -- the first basis direction
      by_cases h0 : hb (u 0) = 0
      · -- the sheared point keeps the first coordinate `u 0 ∈ {0,1}`: `e₀ ∈ ker D`
        have hshear0 : (shear q u) 0 = u 0 := by
          rw [shear_apply_zero, h0, mul_zero, add_zero]
        have hp : (shear q u) 0 = 0 ∨ (shear q u) 0 = 1 := by
          rcases range_mfderiv_shear_hb_eq_zero_iff.mp h0 with h | h
          · exact Or.inl (by rw [hshear0, h])
          · exact Or.inr (by rw [hshear0, h])
        have hker : (EuclideanSpace.single 0 (1 : ℝ) : RMSE2) ∈ D.ker := hker0 hp
        exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, _, hker, by simp⟩
      · -- `e₀ = (hb (u 0))⁻¹ • (hb (u 0) • e₀)` lies in the range
        have hmem : (EuclideanSpace.single 0 (1 : ℝ) : RMSE2) ∈ E.range := by
          have h := Submodule.smul_mem _ (hb (u 0))⁻¹ hE0
          simpa [smul_smul, inv_mul_cancel₀ h0] using h
        exact Submodule.mem_sup.mpr ⟨_, hmem, 0, Submodule.zero_mem _, by simp⟩
    · -- the second basis direction
      by_cases h1 : hb (u 1) = 0
      · have hshear1 : (shear q u) 1 = u 1 := by
          rw [shear_apply_one, h1, mul_zero, add_zero]
        have hp : (shear q u) 1 = 0 ∨ (shear q u) 1 = 1 := by
          rcases range_mfderiv_shear_hb_eq_zero_iff.mp h1 with h | h
          · exact Or.inl (by rw [hshear1, h])
          · exact Or.inr (by rw [hshear1, h])
        have hker : (EuclideanSpace.single 1 (1 : ℝ) : RMSE2) ∈ D.ker := hker1 hp
        exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, _, hker, by simp⟩
      · have hmem : (EuclideanSpace.single 1 (1 : ℝ) : RMSE2) ∈ E.range := by
          have h := Submodule.smul_mem _ (hb (u 1))⁻¹ hE1
          simpa [smul_smul, inv_mul_cancel₀ h1] using h
        exact Submodule.mem_sup.mpr ⟨_, hmem, 0, Submodule.zero_mem _, by simp⟩
  have hfinal : ((D : RMSE2 →ₗ[ℝ] RMSE3).comp (E : RMSE4 →ₗ[ℝ] RMSE2)).range =
      (D : RMSE2 →ₗ[ℝ] RMSE3).range := range_mfderiv_shear_range_comp D E hsup
  rw [hchain]
  exact hfinal

end

end Work.Drive
