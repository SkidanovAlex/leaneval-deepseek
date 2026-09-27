import Mathlib
import Submission.Work.Drive.N2.FieldData

/-!
# Non-vanishing of the ambient auxiliary field along a retracted embedding

Let `e : M → ℝ^N` be a smooth map of a smooth `n`-manifold, `π : ℝ^N → M` a smooth
retraction of an open set `U ∋ e x₀` onto `M` (so `π (e x) = x`), `f : M → ℝ` smooth with
`d f x₀ ≠ 0`.  Then, with `E = e ∘ π` and `G = f ∘ π`, the ambient field `auxField E G` (that
is `(dE)ᵀ ∇G`) does not vanish at `e x₀`.

The proof is the identity `G ∘ E ∘ e = f`: differentiating it gives
`dG(e x₀) ∘ dE(e x₀) ∘ de(x₀) = df(x₀) ≠ 0`, so `dG(e x₀) ∘ dE(e x₀) ≠ 0`; since
`auxField E G z = (dE z)ᵀ ∇G z`, vanishing at `e x₀` would force `dG(e x₀) (dE(e x₀) w) = 0`
for all `w`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

/-- Pairing the auxiliary field `auxField E G z = (dE z)ᵀ ∇G z` with a vector `w` gives the
derivative of `G` in the direction `dE z w`. -/
lemma inner_auxField {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) (z w : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (auxField E G z) w = fderiv ℝ G z (fderiv ℝ E z w) := by
  rw [auxField, grad, ContinuousLinearMap.adjoint_inner_left,
    InnerProductSpace.toDual_symm_apply]

theorem auxField_retraction_ne_zero {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (himm : ∀ x, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N))) e x))
    (U : Set (EuclideanSpace ℝ (Fin N))) (hUopen : IsOpen U) (π : EuclideanSpace ℝ (Fin N) → M)
    (hπsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) π U)
    (hπe : ∀ x, π (e x) = x) (x₀ : M) (hU : e x₀ ∈ U)
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hmf : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ ℝ) f x₀ ≠ 0) :
    auxField (fun z => e (π z)) (fun z => f (π z)) (e x₀) ≠ 0 := by
  set E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun z => e (π z) with hEdef
  set G : EuclideanSpace ℝ (Fin N) → ℝ := fun z => f (π z) with hGdef
  have hEG : E (e x₀) = e x₀ := by simp [hEdef, hπe]
  -- smoothness of `π` at `e x₀`
  have hπ_ca : ContMDiffAt (𝓡 N) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) π (e x₀) :=
    hπsm.contMDiffAt (hUopen.mem_nhds hU)
  have he_ca : ContMDiffAt (𝓡 n) (𝓡 N) ((⊤ : ℕ∞) : WithTop ℕ∞) e x₀ := he.contMDiffAt
  -- the same, with the point `π (e x₀) = x₀` written in the shape produced by the chain rule
  have he_ca' : ContMDiffAt (𝓡 n) (𝓡 N) ((⊤ : ℕ∞) : WithTop ℕ∞) e (π (e x₀)) := by
    rw [hπe x₀]; exact he_ca
  have hf_ca' : ContMDiffAt (𝓡 n) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      f (π (e x₀)) := by
    rw [hπe x₀]; exact hf.contMDiffAt
  have he_dif : MDifferentiableAt (𝓡 n) (𝓡 N) e x₀ :=
    he_ca.mdifferentiableAt (by simp)
  have hE_ca : ContMDiffAt (𝓡 N) (𝓡 N) ((⊤ : ℕ∞) : WithTop ℕ∞) E (e x₀) := by
    rw [hEdef]
    exact he_ca'.comp (e x₀) hπ_ca
  have hE_dif : MDifferentiableAt (𝓡 N) (𝓡 N) E (e x₀) :=
    hE_ca.mdifferentiableAt (by simp)
  have hG_ca : ContMDiffAt (𝓡 N) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      G (e x₀) := by
    rw [hGdef]
    exact hf_ca'.comp (e x₀) hπ_ca
  have hG_dif : MDifferentiableAt (𝓡 N) (modelWithCornersSelf ℝ ℝ) G (E (e x₀)) := by
    rw [hEG]; exact hG_ca.mdifferentiableAt (by simp)
  have hΦ_dif : MDifferentiableAt (𝓡 n) (𝓡 N) (fun x => E (e x)) x₀ :=
    (hE_ca.comp x₀ he_ca).mdifferentiableAt (by simp)
  -- `G ∘ E ∘ e = f`
  have hcon : (fun x : M => G (E (e x))) = f := by
    funext x
    simp [hEdef, hGdef, hπe]
  -- identification of the manifold derivative with the Fréchet derivative
  have hGmf : mfderiv (𝓡 N) (modelWithCornersSelf ℝ ℝ) G (E (e x₀)) = fderiv ℝ G (e x₀) := by
    rw [hEG]; exact mfderiv_eq_fderiv
  have hEmf : mfderiv (𝓡 N) (𝓡 N) E (e x₀) = fderiv ℝ E (e x₀) := mfderiv_eq_fderiv
  -- transport `hmf` to the composite `G ∘ E ∘ e`
  have hne : mfderiv (𝓡 n) (modelWithCornersSelf ℝ ℝ) (fun x => G (E (e x))) x₀ ≠ 0 := by
    rw [← hcon] at hmf
    exact hmf
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hne
  set w : EuclideanSpace ℝ (Fin N) := (mfderiv (𝓡 n) (𝓡 N) e x₀) v with hw
  -- the pointwise chain rule
  have hc1 : (mfderiv (𝓡 n) (modelWithCornersSelf ℝ ℝ) (fun x => G (E (e x))) x₀) v
      = (mfderiv (𝓡 N) (modelWithCornersSelf ℝ ℝ) G (E (e x₀)))
          ((mfderiv (𝓡 n) (𝓡 N) (fun x => E (e x)) x₀) v) :=
    mfderiv_comp_apply (f := fun x => E (e x)) x₀ hG_dif hΦ_dif v
  rw [hc1] at hv
  have hc2 : (mfderiv (𝓡 n) (𝓡 N) (fun x => E (e x)) x₀) v
      = (mfderiv (𝓡 N) (𝓡 N) E (e x₀)) w := by
    have h := mfderiv_comp_apply (f := e) x₀ hE_dif he_dif v
    rw [hw]
    exact h
  rw [hc2] at hv
  -- hence `dG(e x₀) (dE(e x₀) w) ≠ 0`
  have hvR : (fderiv ℝ G (e x₀) (fderiv ℝ E (e x₀) w) : ℝ) ≠ 0 := by
    rw [hGmf, hEmf] at hv
    exact hv
  -- if the auxiliary field vanished, the above pairing would vanish too
  intro haux
  have hinner := inner_auxField E G (e x₀) w
  rw [haux, inner_zero_left] at hinner
  exact hvR hinner.symm

end Work.Drive.N2
