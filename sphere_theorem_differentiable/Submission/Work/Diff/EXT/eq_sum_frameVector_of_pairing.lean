import Mathlib
import Submission.Work.Diff.EXT.ricCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **Coordinates from pairings.**  Let `b` be a basis of `V` indexed by `Fin n`, and let
`ip : V → V → ℝ` be additive and homogeneous in its first argument, symmetric, and positive
definite.  Then `b` is recovered from the pairings: with `Γ i j = ip (b i) (b j)` the Gram matrix
and `v k = ip w (b k)`, one has `w = Σ k, (Γ⁻¹ *ᵥ v) k • b k`. -/
lemma eq_sum_basis_of_pairing_gram
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin n) ℝ V) (ip : V → V → ℝ)
    (hadd : ∀ x y z, ip (x + y) z = ip x z + ip y z)
    (hsmul : ∀ (c : ℝ) x z, ip (c • x) z = c * ip x z)
    (hsymm : ∀ x y, ip x y = ip y x)
    (hpos : ∀ x, x ≠ 0 → 0 < ip x x)
    (w : V) :
    w = ∑ k, (Matrix.mulVec (Matrix.of (fun i j => ip (b i) (b j)))⁻¹
        (fun k => ip w (b k))) k • b k := by
  classical
  -- `ip` is additive and homogeneous in its second argument, by symmetry.
  have hadd2 : ∀ x y z, ip x (y + z) = ip x y + ip x z := fun x y z => by
    rw [hsymm x (y + z), hadd y z x, hsymm y x, hsymm z x]
  have hsmul2 : ∀ (c : ℝ) x z, ip x (c • z) = c * ip x z := fun c x z => by
    rw [hsymm x (c • z), hsmul c z x, hsymm z x]
  -- package `ip` as a bilinear form
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => ip x y) (fun x y z => hadd x y z)
      (fun c x z => hsmul c x z) (fun x y z => hadd2 x y z) (fun c x z => hsmul2 c x z)
  have hB : ∀ x y, B x y = ip x y := fun x y => rfl
  have hBsymm : ∀ x y, B x y = B y x :=
    fun x y => (hB x y).trans ((hsymm x y).trans (hB y x).symm)
  -- coordinates in the basis
  let Φ : (Fin n → ℝ) ≃ₗ[ℝ] V := b.equivFun.symm
  have hΦ : ∀ x : Fin n → ℝ, Φ x = ∑ i, x i • b i := fun x =>
    Module.Basis.equivFun_symm_apply b x
  let Γ : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => ip (b i) (b j))
  have hΓ : ∀ i j : Fin n, Γ i j = ip (b i) (b j) := fun i j => rfl
  -- the defining property of the Gram matrix
  have hK : ∀ (z : Fin n → ℝ) (j : Fin n), Matrix.mulVec Γ z j = B (b j) (Φ z) := by
    intro z j
    have h1 : Matrix.mulVec Γ z j = ∑ i, z i * ip (b j) (b i) := by
      rw [Matrix.mulVec_apply, dotProduct]
      exact Finset.sum_congr rfl (fun i _ => by rw [mul_comm, Matrix.row_apply, hΓ j i])
    have h2 : B (b j) (Φ z) = ∑ i, z i * ip (b j) (b i) := by
      rw [hΦ, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, hB, smul_eq_mul])
    rw [h1, h2]
  -- hence `Γ` is invertible
  have hinj : Function.Injective (Matrix.mulVec Γ) := by
    intro x y hxy
    have hz : Matrix.mulVec Γ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hzero : ∀ j : Fin n, B (b j) (Φ (x - y)) = 0 := fun j => by
      rw [← hK (x - y) j, hz, Pi.zero_apply]
    have h2 : ∀ u : V, B u (Φ (x - y)) = ∑ i, (x - y) i * B u (b i) := by
      intro u
      rw [hΦ (x - y), map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
    have hself : B (Φ (x - y)) (Φ (x - y)) = 0 := by
      rw [h2 (Φ (x - y)), Finset.sum_eq_zero]
      intro i _
      rw [hBsymm, hzero i, mul_zero]
    have hmem : Φ (x - y) = 0 := by
      by_contra hne
      have hp' : 0 < B (Φ (x - y)) (Φ (x - y)) := by rw [hB]; exact hpos _ hne
      rw [hself] at hp'
      exact lt_irrefl 0 hp'
    have hxy' : x - y = 0 := by
      apply Φ.injective
      rw [hmem, map_zero]
    exact sub_eq_zero.mp hxy'
  have hunit : IsUnit Γ := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit Γ.det := (Matrix.isUnit_iff_isUnit_det Γ).mp hunit
  -- coordinates of `w` and the pairing vector
  let a : Fin n → ℝ := b.equivFun w
  have hwa : Φ a = w := LinearEquiv.symm_apply_apply b.equivFun w
  have hv : (fun k => ip w (b k)) = Matrix.mulVec Γ a := by
    funext k
    rw [hK a k, ← hwa, ← hB]
    exact hBsymm _ _
  have hgoal : Matrix.mulVec Γ⁻¹ (fun k => ip w (b k)) = a := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Γ hdet, Matrix.one_mulVec]
  have hsum : (∑ k, a k • b k) = w := by
    rw [← Module.Basis.equivFun_symm_apply b a, hwa]
  rw [hgoal, hsum]


/-- **A tangent vector is determined by its pairings with the chart frame.**  Writing `σ_k` for
the chart frame vectors `frameVector x₀ p (bb k)`, the Gram matrix `Γ_{ij} = g.inner p (σ_i) (σ_j)`
is invertible and, for every `w`, the vector `Σ_k (Γ⁻¹ *ᵥ (fun k => g.inner p w (σ_k)))_k • σ_k`
equals `w`. -/
theorem eq_sum_frameVector_of_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {g : Submission.Diff.SMet I M} {x₀ p : M} (hp : p ∈ (chartAt H x₀).source)
    (w : TangentSpace I p) :
    w = ∑ k, (Matrix.mulVec (Matrix.of (fun i j =>
        g.inner p (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E i))
          (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E j))))⁻¹
      (fun k => g.inner p w (Submission.Geodesic.frameVector (I := I) x₀ p
        (Module.finBasis ℝ E k)))) k
      • Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E k) := by
  classical
  haveI : Bundle.Trivialization.IsLinear ℝ (trivializationAt E (TangentSpace I) x₀) := inferInstance
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp
  let L : E ≃ₗ[ℝ] TangentSpace I p :=
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) x₀) p hb).symm
  have hL : ∀ v : E, L v = Submission.Geodesic.frameVector (I := I) x₀ p v := by
    intro v
    rw [Bundle.Trivialization.linearEquivAt_symm_apply]
    exact (Bundle.Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) x₀) hb v).symm
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    (Module.finBasis ℝ E).map L
  have hbk : ∀ k : Fin (Module.finrank ℝ E),
      b k = Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E k) := by
    intro k
    show ((Module.finBasis ℝ E).map L) k = _
    rw [Module.Basis.map_apply]
    exact hL _
  have hgen := eq_sum_basis_of_pairing_gram b (fun v w => g.inner p v w)
    (fun x y z => by simp) (fun c x z => by simp) (fun x y => g.symm p x y)
    (fun x hx => g.pos p x hx) w
  simpa only [hbk] using hgen


end Work.Diff.EXT
