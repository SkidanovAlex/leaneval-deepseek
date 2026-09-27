import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.finite_nearStab_compact

/-!
# The orbit map of a lattice homomorphism is coarsely proper (reverse direction)

For `f : Γ ≃* Λ` an isomorphism of lattices in `PO n 1`, a compact set `K` of `ℍⁿ` (in the chart
model `E n`) and a section `γof : ℍⁿ → Γ` which brings `X ⊆ ℍⁿ` into `K` (i.e.
`(γof u)⁻¹ • u ∈ K` for `u ∈ X`), the map `u ↦ f (γof u) • 0` is coarsely injective *in reverse*:
points of `X` whose images are within distance `M` are within a distance `C` depending only on `M`.

The argument is elementary.  Let `A = f (γof u)`, `B = f (γof v)` as elements of `PO n 1`; the
hypothesis says `hdist (A • 0) (B • 0) ≤ M`, i.e. `hdist 0 ((A⁻¹ * B) • 0) ≤ M`.  Since
`A⁻¹ * B = f ((γof u)⁻¹ * γof v)`, the element `h = (γof u)⁻¹ * γof v` lies in the near-set
`{g : Γ | hdist 0 (f g • 0) ≤ M}`, which is *finite* because it is the `f`-preimage of the finite
near-stabiliser of `Λ` (`Work.Mostow.finite_nearStab`).  Over that finite set `hdist 0 (g • 0)` is
bounded by a constant `C₀` depending only on `M`.

Finally, writing `w = (γof v)⁻¹ • v ∈ K` we have
`(γof u)⁻¹ • v = h • w`, and the triangle inequality gives
`hdist u v ≤ hdist ((γof u)⁻¹ • u, 0) + hdist (0, (γof u)⁻¹ • v) ≤ B + (C₀ + B) = C₀ + 2B`,
where `B` bounds `hdist 0` on the compact set `K`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

/-- Triangle inequality with the isometry pushforward: `hdist 0 (a • u) ≤ hdist 0 (a • 0) + hdist 0 u`. -/
theorem orbitReverse_hdist_zero_smul_le {n : ℕ} (hI : Work.Mostow.HypIsoData n) (a : PO n 1)
    (u : E n) :
    hdist (0 : E n) (a • u) ≤ hdist (0 : E n) (a • (0 : E n)) + hdist (0 : E n) u := by
  have ht := hI.triangle (0 : E n) (a • (0 : E n)) (a • u)
  rwa [hI.isom_smul a (0 : E n) u] at ht

/-- The displacement of `0` by `a⁻¹ * b` is the distance between the images of `0` by `a` and by `b`. -/
theorem orbitReverse_hdist_zero_inv_mul_smul {n : ℕ} (hA : Work.Mostow.POBasic n)
    (hI : Work.Mostow.HypIsoData n) (a b : PO n 1) :
    hdist (0 : E n) ((a⁻¹ * b) • (0 : E n)) = hdist (a • (0 : E n)) (b • (0 : E n)) := by
  have h1 : a • ((a⁻¹ * b) • (0 : E n)) = b • (0 : E n) := by
    rw [← hA.mul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hI.isom_smul a (0 : E n) ((a⁻¹ * b) • (0 : E n)), h1]

/-- `g` undoes its own inverse: `g • (g⁻¹ • u) = u` for `g` in a subgroup. -/
theorem orbitReverse_smul_coe_inv_smul {n : ℕ} (hA : Work.Mostow.POBasic n)
    {Γ : Subgroup (PO n 1)} (g : Γ) (u : E n) :
    ((g : Γ) : PO n 1) • ((((g⁻¹ : Γ)) : PO n 1) • u) = u := by
  rw [← hA.mul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, hA.one_smul]

/-- Decomposition of `a⁻¹ • v` along the orbit of `b`: `a⁻¹ • v = (a⁻¹ * b) • (b⁻¹ • v)`. -/
theorem orbitReverse_decomp {n : ℕ} (hA : Work.Mostow.POBasic n)
    {Γ : Subgroup (PO n 1)} (a b : Γ) (v : E n) :
    ((((a⁻¹ : Γ)) : PO n 1)) • v
      = ((((a⁻¹ * b : Γ)) : PO n 1)) • ((((b⁻¹ : Γ)) : PO n 1) • v) := by
  rw [Subgroup.coe_mul, hA.mul_smul, orbitReverse_smul_coe_inv_smul hA b v]

theorem orbitReverse {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hΓdisc : IsDiscrete (SetLike.coe Γ)) (hΛdisc : IsDiscrete (SetLike.coe Λ)) (f : Γ ≃* Λ)
    {X : Set (Submission.Mostow.E n)} {K : Set (Submission.Mostow.E n)} (hK : IsCompact K)
    (γof : Submission.Mostow.E n → Γ)
    (hγof : ∀ u : Submission.Mostow.E n, u ∈ X →
      (((γof u)⁻¹ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K)
    {M : ℝ} :
    ∃ C : ℝ, ∀ u v : Submission.Mostow.E n, u ∈ X → v ∈ X →
      Submission.Mostow.hdist
        (((f (γof u) : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n))
        (((f (γof v) : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) ≤ M →
      Submission.Mostow.hdist u v ≤ C := by
  -- a bound for `hdist 0` on the compact set `K`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ w ∈ K, hdist (0 : Submission.Mostow.E n) w ≤ B := by
    obtain ⟨B, hB⟩ := hK.bddAbove_image
      (hI.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact ⟨B, fun w hw => hB ⟨w, hw, rfl⟩⟩
  -- the near-set inside `Γ` is the `f`-preimage of the finite near-stabiliser of `Λ`
  have hSfin : {g : Γ | hdist (0 : Submission.Mostow.E n)
      (((f g : Λ) : PO n 1) • (0 : Submission.Mostow.E n)) ≤ M}.Finite :=
    Set.Finite.preimage (fun a _ b _ hab => f.injective hab) (finite_nearStab hA hI hΛdisc M)
  -- hence a uniform bound for `hdist 0 (g • 0)` on that near-set
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ g : Γ,
      hdist (0 : Submission.Mostow.E n) (((f g : Λ) : PO n 1) • (0 : Submission.Mostow.E n)) ≤ M →
      hdist (0 : Submission.Mostow.E n) ((g : PO n 1) • (0 : Submission.Mostow.E n)) ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := (hSfin.image (fun g : Γ =>
      hdist (0 : Submission.Mostow.E n) ((g : PO n 1) • (0 : Submission.Mostow.E n)))).bddAbove
    exact ⟨C₀, fun g hg => hC₀ ⟨g, hg, rfl⟩⟩
  refine ⟨C₀ + 2 * B, ?_⟩
  intro u v hu hv hMuv
  have hKu : (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K := hγof u hu
  have hKv : (((γof v)⁻¹ : Γ) : PO n 1) • v ∈ K := hγof v hv
  -- the group element `(γof u)⁻¹ * γof v` lies in the near-set
  have hMh : hdist (0 : E n)
      (((f ((γof u)⁻¹ * γof v) : Λ) : PO n 1) • (0 : E n)) ≤ M := by
    have hcoe : ((f ((γof u)⁻¹ * γof v) : Λ) : PO n 1)
        = ((((f (γof u) : Λ) : PO n 1)))⁻¹ * (((f (γof v) : Λ) : PO n 1)) := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, orbitReverse_hdist_zero_inv_mul_smul hA hI
      (((f (γof u) : Λ) : PO n 1)) (((f (γof v) : Λ) : PO n 1))]
    exact hMuv
  have hdec : (((γof u)⁻¹ : Γ) : PO n 1) • v
      = ((((γof u)⁻¹ * γof v : Γ)) : PO n 1) • ((((γof v)⁻¹ : Γ)) : PO n 1) • v :=
    orbitReverse_decomp hA (γof u) (γof v) v
  have hb1 : hdist ((((γof u)⁻¹ : Γ) : PO n 1) • u) (0 : E n) ≤ B :=
    calc hdist ((((γof u)⁻¹ : Γ) : PO n 1) • u) (0 : E n)
        = hdist (0 : E n) ((((γof u)⁻¹ : Γ) : PO n 1) • u) := hI.symm _ _
      _ ≤ B := hB _ hKu
  have hb2 : hdist (0 : E n) ((((γof u)⁻¹ : Γ) : PO n 1) • v) ≤ C₀ + B := by
    rw [hdec]
    have h1 := orbitReverse_hdist_zero_smul_le hI (((γof u)⁻¹ * γof v : Γ) : PO n 1)
      ((((γof v)⁻¹ : Γ) : PO n 1) • v)
    have h2 : hdist (0 : E n) ((((γof u)⁻¹ * γof v : Γ) : PO n 1) • (0 : E n)) ≤ C₀ :=
      hC₀ ((γof u)⁻¹ * γof v) hMh
    have h3 : hdist (0 : E n) ((((γof v)⁻¹ : Γ) : PO n 1) • v) ≤ B := hB _ hKv
    linarith
  have hA1 : hdist u v ≤ hdist ((((γof u)⁻¹ : Γ) : PO n 1) • u) (0 : E n)
      + hdist (0 : E n) ((((γof u)⁻¹ : Γ) : PO n 1) • v) := by
    rw [← hI.isom_smul ((((γof u)⁻¹ : Γ) : PO n 1)) u v]
    exact hI.triangle _ _ _
  linarith

end Work.Mostow
