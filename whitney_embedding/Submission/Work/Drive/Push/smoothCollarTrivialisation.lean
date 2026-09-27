import Mathlib
import Submission.Work.Whitney.CutPush.BigonData
import Submission.Work.Drive.Push.planeTransverse
import Submission.Work.Drive.Push.planeTransverseAvoiding
import Submission.Work.Drive.Push.localGraphFunction

set_option maxHeartbeats 4000000

namespace Work.Drive.Push

open scoped Manifold ContDiff
open Metric

/-- **A flattened image gives the trivialisation.**  If a global `C^∞` diffeomorphism `S` of
`ℝ^{2n}` (with inverse `S'`) carries `f '' U` into the zero section of a linear splitting `L` of
`ℝ^{2n}` onto `ℝⁿ × ℝⁿ`, then `β := (L ∘ S).₁`, `θ := (L ∘ S).₂` and `Ψ := S' ∘ L.symm` are a
trivialisation with `θ (f x) = 0` for `x ∈ U`.  (This is
`Work.Whitney.CutPush.trivialisation_of_flat_image`, reproduced here so that this file does not
import a module that carries an unfinished statement.) -/
private theorem trivialisation_of_flat_image' {n : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (U : Set M)
    (S S' : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hS' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S')
    (hSS' : ∀ y, S' (S y) = y) (hS'S : ∀ y, S (S' y) = y)
    (L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hflat : ∀ x ∈ U, (L (S (f x))).2 = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (L (S y)).1) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (L (S y)).2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => S' (L.symm z)) ∧
    (∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ((fun y => (L (S y)).1) (S' (L.symm z)), (fun y => (L (S y)).2) (S' (L.symm z))) = z) ∧
    (∀ y : EuclideanSpace ℝ (Fin (2 * n)),
      S' (L.symm ((fun y => (L (S y)).1) y, (fun y => (L (S y)).2) y)) = y) ∧
    (∀ x : M, x ∈ U → (fun y => (L (S y)).2) (f x) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ContinuousLinearEquiv.contDiff L).fst.comp hS
  · exact (ContinuousLinearEquiv.contDiff L).snd.comp hS
  · exact hS'.comp (ContinuousLinearEquiv.contDiff L.symm)
  · intro z
    have h1 : (fun y => (L (S y)).1) (S' (L.symm z)) = (L (S (S' (L.symm z)))).1 := rfl
    have h2 : (fun y => (L (S y)).2) (S' (L.symm z)) = (L (S (S' (L.symm z)))).2 := rfl
    rw [h1, h2, hS'S, ContinuousLinearEquiv.apply_symm_apply]
  · intro y
    have h : ((fun y => (L (S y)).1) y, (fun y => (L (S y)).2) y) = L (S y) := rfl
    rw [h, ContinuousLinearEquiv.symm_apply_apply, hSS']
  · intro x hx
    simpa using hflat x hx

/-- **The smooth-arc collar trivialisation** (the trivialisation half of the smooth residual of
`Work.Drive.hasPushSignedSmooth`, which is retained by
`Work.Drive.Push.collarConfinementSmooth`).

For the bigon data of `Work.Whitney.CutPush.bigon_confinement`, with the second arc `γ₂` SMOOTH on
`ℝ` and IMMERSIVE on `[0,1]` — exactly the situation of `Work.Drive.HasPushSignedSmooth` — there is
an open collar `U ∋ p₂, q₂` with `closure U ⊆ W` and a *slab trivialisation* `(β, θ, Ψ)` of
`ℝ^{2n}` with `θ ∘ f ≡ 0` on `U`.

The originally intended route (whole-tube flattening along the spine `δ := γ₂`, via
`Work.Whitney.CutPush.tube_flattening`) is *not* the route used here: the statement only asks for a
collar `U` around the two *points* `p₂, q₂` (not around the arc), and `W` only enters through
`closure U ⊆ W`.  So the proof localises at the two double points:

* (`Work.Drive.Push.planeTransverse`, `planeTransverseAvoiding`) there is an `n`-plane
  `H ≤ ℝ^{2n}` transversal to both tangent planes `range (mfderiv f p₂)` and
  `range (mfderiv f q₂)` and not containing `f p₂ - f q₂`;
* build a linear splitting `L : ℝ^{2n} ≃L ℝⁿ × ℝⁿ` with `ker L.1 = H` (orthogonal projections +
  `LinearEquiv.ofFinrankEq`); then `x ↦ (L (f x)).1` is a local diffeomorphism at `p₂` and at `q₂`;
* (`Work.Drive.Push.localGraphFunction`) near each of the two points the image of `f` is the graph
  of a globally smooth function of `(L (f ·)).1`, on a neighbourhood whose `L.1`-image is a small
  ball; `L.1 (f p₂) ≠ L.1 (f q₂)`, so the two balls can be taken disjoint;
* the bump-weighted sum `h̃ := χ_p · h_p + χ_q · h_q` of the two graph functions is then globally
  `C^∞` and agrees with the correct graph function on each of the two neighbourhoods, and the
  fibre-wise translation `S y = L.symm ((L y).1, (L y).2 - h̃ ((L y).1))` (with inverse
  `S' y = L.symm ((L y).1, (L y).2 + h̃ ((L y).1))`) is a global `C^∞` diffeomorphism of `ℝ^{2n}`
  carrying `f '' U` into `ker L.2`;
* the trivialisation is read off from `(S, S', L)` (`trivialisation_of_flat_image'` below).

Neither `γ₂` nor the `OppositeType` framing hypothesis nor the arc-injectivity is used: the
statement (as requested) is a weakening of the collar statement, and this proof establishes it in
full. -/
theorem smoothCollarTrivialisation {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M)
    (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (h : Work.Whitney.CutPush.HasBigonData n M f W p₁ p₂ q₁ q₂ γ₁ γ₂)
    (hγ₂sm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t)) :
    ∃ (U : Set M) (β θ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
      (Ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ closure U ⊆ W ∧ p₂ ∈ U ∧ q₂ ∈ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), (β (Ψ z), θ (Ψ z)) = z) ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Ψ (β y, θ y) = y) ∧
      (∀ x : M, x ∈ U → θ (f x) = 0) := by
  classical
  have hf := h.smooth
  -- --------------------------------------------------------- step 1: the tangent planes
  set Vp : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range with hVp
  set Vq : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range with hVq
  have hfinVp : Module.finrank ℝ Vp = n := by
    have hker : LinearMap.ker ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂ :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro v w hvw
      exact h.immersed p₂ hvw
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p₂) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    have hrank := LinearMap.finrank_range_add_finrank_ker
      ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂ :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).toLinearMap
    rw [hker, finrank_bot, add_zero] at hrank
    have hE : Module.finrank ℝ (TangentSpace (𝓡 n) p₂) = n := by
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [hE] at hrank
    rw [hVp]
    exact hrank
  have hfinVq : Module.finrank ℝ Vq = n := by
    have hker : LinearMap.ker ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂ :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro v w hvw
      exact h.immersed q₂ hvw
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) q₂) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    have hrank := LinearMap.finrank_range_add_finrank_ker
      ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂ :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).toLinearMap
    rw [hker, finrank_bot, add_zero] at hrank
    have hE : Module.finrank ℝ (TangentSpace (𝓡 n) q₂) = n := by
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [hE] at hrank
    rw [hVq]
    exact hrank
  -- ------------------------------------ step 2: a plane transversal to both and avoiding `z`
  obtain ⟨H₁, hH₁fin, hH₁Vp, hH₁Vq⟩ := planeTransverse Vp Vq hfinVp hfinVq
  have hne : f p₂ - f q₂ ≠ 0 := by
    rw [sub_ne_zero]
    intro hcontra
    have hp₁q₁ : f p₁ = f q₁ := by rw [h.val₁₂, h.val₃₄]; exact hcontra
    rcases h.clean p₁ q₁ h.mem₁ h.mem₃ hp₁q₁ with h1 | h1 | h1 | h1 | h1
    · exact h.ne₁₃ h1
    · exact h.ne₂₃ h1.2.symm
    · exact h.ne₁₂ h1.1
    · exact h.ne₁₃ h1.1
    · exact h.ne₁₄ h1.1
  obtain ⟨H, hHfin, hHVp, hHVq, HzH⟩ :=
    planeTransverseAvoiding H₁ Vp Vq hH₁fin hfinVp hfinVq hH₁Vp hH₁Vq (f p₂ - f q₂) hne
  -- ------------------------------------------------------ step 3: the splitting `L`
  have hfinHorth : Module.finrank ℝ Hᗮ = n := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) H
    have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [hE, hHfin] at h
    omega
  have hcardn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  let e : Hᗮ ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofFinrankEq Hᗮ _ (by rw [hfinHorth, hcardn])).toContinuousLinearEquiv
  let σ : H ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofFinrankEq H _ (by rw [hHfin, hcardn])).toContinuousLinearEquiv
  let π : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (e : Hᗮ →L[ℝ] EuclideanSpace ℝ (Fin n)).comp Hᗮ.orthogonalProjectionOnto
  let ρ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (σ : H →L[ℝ] EuclideanSpace ℝ (Fin n)).comp H.orthogonalProjectionOnto
  have hπ_apply : ∀ y, π y = e (Hᗮ.orthogonalProjectionOnto y) := fun y => rfl
  have hρ_apply : ∀ y, ρ y = σ (H.orthogonalProjectionOnto y) := fun y => rfl
  have hkerπ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), π y = 0 ↔ y ∈ H := by
    intro y
    rw [hπ_apply]
    constructor
    · intro h1
      have h2 : Hᗮ.orthogonalProjectionOnto y = 0 := e.injective (by rw [h1, map_zero])
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at h2
      exact h2
    · intro hy
      have h2 : Hᗮ.orthogonalProjectionOnto y = 0 := by
        rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
        exact hy
      rw [h2, map_zero]
  have hdecomp : ∀ y : EuclideanSpace ℝ (Fin (2 * n)),
      ((Hᗮ.orthogonalProjectionOnto y : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n))) +
      ((H.orthogonalProjectionOnto y : H) : EuclideanSpace ℝ (Fin (2 * n))) = y := by
    intro y
    rw [Submodule.coe_orthogonalProjectionOnto_apply Hᗮ y,
      Submodule.coe_orthogonalProjectionOnto_apply H y]
    exact (add_comm _ _).trans (Submodule.starProjection_add_starProjection_orthogonal y)
  let Linv : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) :=
    ContinuousLinearMap.coprod
      ((Hᗮ.subtypeL : Hᗮ →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).comp
        (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] Hᗮ))
      ((H.subtypeL : H →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).comp
        (σ.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] H))
  have hLinv_apply : ∀ u v : EuclideanSpace ℝ (Fin n),
      Linv (u, v) = ((e.symm u : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n))) +
        ((σ.symm v : H) : EuclideanSpace ℝ (Fin (2 * n))) := by
    intro u v
    rfl
  have hleft : Function.LeftInverse Linv (π.prod ρ) := by
    intro y
    rw [show (π.prod ρ) y = (π y, ρ y) from rfl, hLinv_apply, hπ_apply, hρ_apply,
      e.symm_apply_apply, σ.symm_apply_apply]
    exact hdecomp y
  have hright : Function.RightInverse Linv (π.prod ρ) := by
    intro z
    obtain ⟨u, v⟩ := z
    have hπ1 : Hᗮ.orthogonalProjectionOnto ((σ.symm v : H) : EuclideanSpace ℝ (Fin (2 * n)))
        = 0 := by
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
      exact (σ.symm v).2
    have hπ2 : Hᗮ.orthogonalProjectionOnto ((e.symm u : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n)))
        = e.symm u :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    have hρ1 : H.orthogonalProjectionOnto ((e.symm u : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n)))
        = 0 := by
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact (e.symm u).2
    have hρ2 : H.orthogonalProjectionOnto ((σ.symm v : H) : EuclideanSpace ℝ (Fin (2 * n)))
        = σ.symm v :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    rw [hLinv_apply,
      show (π.prod ρ) (((e.symm u : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n))) +
          ((σ.symm v : H) : EuclideanSpace ℝ (Fin (2 * n)))) =
        (π (((e.symm u : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n))) +
            ((σ.symm v : H) : EuclideanSpace ℝ (Fin (2 * n)))),
          ρ (((e.symm u : Hᗮ) : EuclideanSpace ℝ (Fin (2 * n))) +
            ((σ.symm v : H) : EuclideanSpace ℝ (Fin (2 * n))))) from rfl]
    simp only [hπ_apply, hρ_apply, map_add, hπ1, hπ2, hρ1, hρ2, map_zero, zero_add, add_zero,
      ContinuousLinearEquiv.apply_symm_apply]
  let L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearEquiv.equivOfInverse (π.prod ρ) Linv hleft hright
  have hL_fst : ∀ y, (L y).1 = π y := by
    intro y
    simp only [L, ContinuousLinearEquiv.equivOfInverse_apply, ContinuousLinearMap.prod_apply]
  have hkerL1 : ∀ y, (L y).1 = 0 ↔ y ∈ H := by
    intro y
    rw [hL_fst y]
    exact hkerπ y
  have htransOf : ∀ (x₀ : M) (Vx : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      Vx = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀).range →
      H ⊓ Vx = ⊥ → ∀ v : EuclideanSpace ℝ (Fin n),
      (L (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀ v)).1 = 0 → v = 0 := by
    intro x₀ Vx hVx hHVx v hv
    have hm : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀ v ∈ H :=
      (hkerL1 _).mp hv
    have hplane : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀ v ∈
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀).range :=
      ⟨v, rfl⟩
    have hboth : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀ v ∈ H ⊓ Vx :=
      ⟨hm, by rwa [hVx]⟩
    rw [hHVx] at hboth
    have hzero : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀ v = 0 := by
      exact (Submodule.mem_bot ℝ).mp hboth
    exact h.immersed x₀ (hzero.trans (map_zero _).symm)
  have htransP := htransOf p₂ Vp hVp hHVp
  have htransQ := htransOf q₂ Vq hVq hHVq
  -- ------------------------------------------------- step 4: the local graph data
  set up : EuclideanSpace ℝ (Fin n) := (L (f p₂)).1 with hup
  set uq : EuclideanSpace ℝ (Fin n) := (L (f q₂)).1 with huq
  have hupuq : up ≠ uq := by
    intro heq
    have h2 : (L (f p₂)).1 = (L (f q₂)).1 := by rw [← hup, ← huq]; exact heq
    have h3 : (L (f p₂) - L (f q₂)).1 = 0 := by
      rw [Prod.fst_sub, h2, sub_self]
    have h1 : (L (f p₂ - f q₂)).1 = 0 := by
      rw [map_sub]
      exact h3
    exact HzH ((hkerL1 _).mp h1)
  set ε : ℝ := dist up uq / 8 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (dist_pos.mpr hupuq) (by norm_num)
  obtain ⟨Op, hp, hOpopen, hp₂Op, hpball, hpsm, hpgr⟩ :=
    localGraphFunction f hf p₂ L htransP ε hε
  obtain ⟨Oq, hq, hOqopen, hq₂Oq, hqball, hqsm, hqgr⟩ :=
    localGraphFunction f hf q₂ L htransQ ε hε
  -- shrink into `W` (compact Hausdorff ⟹ regular)
  obtain ⟨Wp, hWpopen, hWpsub, hWpcl⟩ :=
    IsCompact.exists_isOpen_closure_subset (isCompact_singleton : IsCompact ({p₂} : Set M))
      (by rw [nhdsSet_singleton]; exact h.isOpen_W.mem_nhds h.mem₂)
  obtain ⟨Wq, hWqopen, hWqsub, hWqcl⟩ :=
    IsCompact.exists_isOpen_closure_subset (isCompact_singleton : IsCompact ({q₂} : Set M))
      (by rw [nhdsSet_singleton]; exact h.isOpen_W.mem_nhds h.mem₄)
  have hp₂Wp : p₂ ∈ Wp := hWpsub (Set.mem_singleton p₂)
  have hq₂Wq : q₂ ∈ Wq := hWqsub (Set.mem_singleton q₂)
  set Op' : Set M := Op ∩ Wp with hOp'
  set Oq' : Set M := Oq ∩ Wq with hOq'
  have hOp'open : IsOpen Op' := hOpopen.inter hWpopen
  have hOq'open : IsOpen Oq' := hOqopen.inter hWqopen
  have hp₂Op' : p₂ ∈ Op' := ⟨hp₂Op, hp₂Wp⟩
  have hq₂Oq' : q₂ ∈ Oq' := ⟨hq₂Oq, hq₂Wq⟩
  set U : Set M := Op' ∪ Oq' with hUdef
  -- ------------------------------------------------------- step 5: the bump functions
  let χp : ContDiffBump up := ⟨2 * ε, 3 * ε, by linarith, by linarith⟩
  let χq : ContDiffBump uq := ⟨2 * ε, 3 * ε, by linarith, by linarith⟩
  have hχp1 : ∀ x ∈ Op', χp ((L (f x)).1) = 1 := by
    intro x hx
    refine χp.one_of_mem_closedBall ?_
    have h := Metric.mem_ball.mp (hpball x hx.1)
    rw [Metric.mem_closedBall]
    linarith
  have hχq0 : ∀ x ∈ Op', χq ((L (f x)).1) = 0 := by
    intro x hx
    refine χq.zero_of_le_dist ?_
    have h2 : dist ((L (f x)).1) up < ε := Metric.mem_ball.mp (hpball x hx.1)
    have h1 : dist uq up ≤ dist uq ((L (f x)).1) + dist ((L (f x)).1) up :=
      dist_triangle _ _ _
    have h3 : 3 * ε < dist uq ((L (f x)).1) := by
      rw [hεdef] at h2 ⊢
      have hdu : dist uq up = dist up uq := dist_comm _ _
      rw [hdu] at h1
      linarith
    simpa [dist_comm] using le_of_lt h3
  have hχq1 : ∀ x ∈ Oq', χq ((L (f x)).1) = 1 := by
    intro x hx
    refine χq.one_of_mem_closedBall ?_
    have h := Metric.mem_ball.mp (hqball x hx.1)
    rw [Metric.mem_closedBall]
    linarith
  have hχp0 : ∀ x ∈ Oq', χp ((L (f x)).1) = 0 := by
    intro x hx
    refine χp.zero_of_le_dist ?_
    have h2 : dist ((L (f x)).1) uq < ε := Metric.mem_ball.mp (hqball x hx.1)
    have h1 : dist up uq ≤ dist up ((L (f x)).1) + dist ((L (f x)).1) uq :=
      dist_triangle _ _ _
    have h3 : 3 * ε < dist up ((L (f x)).1) := by
      rw [hεdef] at h2 ⊢
      linarith
    simpa [dist_comm] using le_of_lt h3
  -- --------------------------------------------------------------- step 6: the shear
  set htil : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => χp u • hp u + χq u • hq u with htilde
  have hhm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) htil := by
    rw [htilde]
    exact ((χp.contDiff).smul hpsm).add ((χq.contDiff).smul hqsm)
  set S : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => L.symm ((L y).1, (L y).2 - htil ((L y).1)) with hSdef
  set S' : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => L.symm ((L y).1, (L y).2 + htil ((L y).1)) with hS'def
  have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => (L y).1) :=
    ContinuousLinearMap.contDiff ((ContinuousLinearMap.fst ℝ
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))).comp
      (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
  have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => (L y).2) :=
    ContinuousLinearMap.contDiff ((ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))).comp
      (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
  have hSsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := by
    rw [hSdef]
    exact (ContinuousLinearEquiv.contDiff L.symm).comp (hc1.prodMk (hc2.sub (hhm.comp hc1)))
  have hS'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S' := by
    rw [hS'def]
    exact (ContinuousLinearEquiv.contDiff L.symm).comp (hc1.prodMk (hc2.add (hhm.comp hc1)))
  have hSS' : ∀ y, S' (S y) = y := by
    intro y
    rw [hSdef, hS'def]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [sub_add_cancel, ContinuousLinearEquiv.symm_apply_apply]
  have hS'S : ∀ y, S (S' y) = y := by
    intro y
    rw [hSdef, hS'def]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
  have hflat : ∀ x : M, x ∈ U → (L (S (f x))).2 = 0 := by
    intro x hx
    rw [hUdef] at hx
    have hxh : (L (f x)).2 = htil ((L (f x)).1) := by
      rcases hx with hx | hx
      · have h1 : htil ((L (f x)).1) = hp ((L (f x)).1) := by
          rw [htilde]
          show χp ((L (f x)).1) • hp ((L (f x)).1) + χq ((L (f x)).1) • hq ((L (f x)).1)
            = hp ((L (f x)).1)
          rw [hχp1 x hx, hχq0 x hx]
          simp
        rw [h1, hpgr x hx.1]
      · have h1 : htil ((L (f x)).1) = hq ((L (f x)).1) := by
          rw [htilde]
          show χp ((L (f x)).1) • hp ((L (f x)).1) + χq ((L (f x)).1) • hq ((L (f x)).1)
            = hq ((L (f x)).1)
          rw [hχq1 x hx, hχp0 x hx]
          simp
        rw [h1, hqgr x hx.1]
    rw [hSdef, ContinuousLinearEquiv.apply_symm_apply]
    exact sub_eq_zero.mpr hxh
  -- -------------------------------------------------------- step 7: the trivialisation
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact hOp'open.union hOq'open
  have hUcl : closure U ⊆ W := by
    rw [hUdef, closure_union]
    refine Set.union_subset ?_ ?_
    · refine (closure_mono ?_).trans hWpcl
      rw [hOp']
      exact Set.inter_subset_right
    · refine (closure_mono ?_).trans hWqcl
      rw [hOq']
      exact Set.inter_subset_right
  obtain ⟨hβ, hθ, hΨ, hinv₁, hinv₂, hzero⟩ :=
    trivialisation_of_flat_image' f U S S' hSsm hS'sm hSS' hS'S L hflat
  exact ⟨U, fun y => (L (S y)).1, fun y => (L (S y)).2, fun z => S' (L.symm z),
    hUopen, hUcl, Or.inl hp₂Op', Or.inr hq₂Oq', hβ, hθ, hΨ, hinv₁, hinv₂, hzero⟩


end Work.Drive.Push
