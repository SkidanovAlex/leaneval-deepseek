import Mathlib
import Submission.Work.Projection.Basic

/-!
# The coordinate packing `ℝ^{2n+1} × ℝ → ℝ^{2n+2}`

We construct a continuous linear map `coordPack n` sending a pair `(z, t)` to the vector in
`ℝ^{2n+2}` whose first `2n+1` coordinates are those of `z` and whose last coordinate is `t`.  It is
an isomorphism onto its image (in fact a linear bijection), hence injective, and it is compatible
with Whitney's projection `projVec u`:

  `projVec u (coordPack n (z, t)) = z - t • u`.

This is the elementary linear-algebra input used to turn an (immersive) map into `ℝ^{2n+1}` into a
map into `ℝ^{2n+1} × ℝ ≅ ℝ^{2n+2}` in the proof of the strong Whitney embedding theorem.
-/

open scoped Manifold ContDiff

namespace Work.Noncompact

/-- The coordinate packing `(z, t) ↦ (z, t)`, i.e. the linear map whose `i`-th coordinate is the
`i`-th coordinate of `z` when `i < 2n+1` and is `t` for `i = 2n+1`. -/
noncomputable def coordPack (n : ℕ) :
    (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2*n+2)) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2*n+2) => ℝ)).symm :
      (Fin (2*n+2) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2*n+2))) ∘L
    (ContinuousLinearMap.pi fun i : Fin (2*n+2) =>
      if h : (i : ℕ) < 2*n+1 then
        (ContinuousLinearMap.proj (⟨i, h⟩ : Fin (2*n+1))) ∘L
          ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2*n+1) => ℝ)) :
              EuclideanSpace ℝ (Fin (2*n+1)) →L[ℝ] (Fin (2*n+1) → ℝ)) ∘L
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ)
      else ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ)

/-- Unfolding of the coordinate packing in the `PiLp`-coordinate model: the underlying function of
`coordPack n (z,t)` is the coordinate-wise description. -/
lemma packSymm_apply (n : ℕ) (x : Fin (2*n+2) → ℝ) (i : Fin (2*n+2)) :
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2*n+2) => ℝ)).symm :
        (Fin (2*n+2) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2*n+2))) x) i = x i := rfl

lemma coordPack_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin (2*n+1))) (t : ℝ) (i : Fin (2*n+2)) :
    coordPack n (z, t) i = if h : (i : ℕ) < 2*n+1 then z ⟨i, h⟩ else t := by
  rw [coordPack, ContinuousLinearMap.comp_apply]
  rw [packSymm_apply]
  rw [ContinuousLinearMap.pi_apply]
  rw [DFunLike.dite_apply]
  split_ifs with h
  · simp
  · simp

@[simp] lemma coordPack_castSucc (n : ℕ) (z : EuclideanSpace ℝ (Fin (2*n+1))) (t : ℝ)
    (i : Fin (2*n+1)) : coordPack n (z, t) (Fin.castSucc i) = z i := by
  rw [coordPack_apply]
  have hlt : ((Fin.castSucc i : Fin (2*n+2)) : ℕ) < 2*n+1 := by
    simpa [Fin.val_castSucc] using i.isLt
  rw [dif_pos hlt]
  exact congrArg z (Fin.eta i hlt)

@[simp] lemma coordPack_last (n : ℕ) (z : EuclideanSpace ℝ (Fin (2*n+1))) (t : ℝ) :
    coordPack n (z, t) (Fin.last (2*n+1)) = t := by
  rw [coordPack_apply]
  rw [dif_neg (by rw [Fin.val_last]; exact Nat.lt_irrefl _)]

lemma coordPack_injective (n : ℕ) : Function.Injective (coordPack n) := by
  intro a b h
  obtain ⟨z, t⟩ := a
  obtain ⟨z', t'⟩ := b
  have h1 : z = z' := by
    ext i
    have hh := congrArg (fun w : EuclideanSpace ℝ (Fin (2*n+2)) => w (Fin.castSucc i)) h
    rw [coordPack_castSucc, coordPack_castSucc] at hh
    exact hh
  have h2 : t = t' := by
    have hh := congrArg (fun w : EuclideanSpace ℝ (Fin (2*n+2)) => w (Fin.last (2*n+1))) h
    rw [coordPack_last, coordPack_last] at hh
    exact hh
  rw [h1, h2]

/-- Whitney's projection of a packed vector: `projVec u (coordPack n (z,t)) = z - t • u`. -/
lemma projVec_coordPack (n : ℕ) (u z : EuclideanSpace ℝ (Fin (2*n+1))) (t : ℝ) :
    Work.Projection.projVec u (coordPack n (z, t)) = z - t • u := by
  ext i
  rw [Work.Projection.projVec_apply, coordPack_castSucc, coordPack_last]
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply]
  ring

/-- There is a continuous linear map identifying `ℝ^{2n+1} × ℝ` with `ℝ^{2n+2}` which is injective
and compatible with Whitney's projection `projVec u`: `projVec u (P (z,t)) = z - t • u`.  Witness:
the coordinate packing `(z,t) ↦ (z, t)` sending the pair to the vector with first `2n+1`
coordinates those of `z` and last coordinate `t` (e.g. built with `ContinuousLinearMap.pi`,
`ContinuousLinearMap.proj`, `PiLp.continuousLinearEquiv`; then `P (z,t) i =
if (i:ℕ) < 2*n+1 then z ⟨i,_⟩ else t`). -/
theorem exists_pack_data (n : ℕ) :
    ∃ P : (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (2*n+2)),
      Function.Injective P ∧
      (∀ (u : EuclideanSpace ℝ (Fin (2*n+1))) (z : EuclideanSpace ℝ (Fin (2*n+1))) (t : ℝ),
        Work.Projection.projVec u (P (z, t)) = z - t • u) :=
  ⟨coordPack n, coordPack_injective n, fun u z t => projVec_coordPack n u z t⟩

end Work.Noncompact
