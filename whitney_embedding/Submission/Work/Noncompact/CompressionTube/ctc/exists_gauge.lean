import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **The linear gauge between two transverse functions.**  Two smooth functions `ψ₁ ψ₂ : M → ℝ^{n-1}`
vanishing on the line `γ` and transverse to `g` along it at `γ s₀` have differentials at `γ s₀`
whose kernels coincide; hence there is an injective linear `A` on `ℝ^{n-1}` with
`A ∘ dψ₂ (γ s₀) = dψ₁ (γ s₀)`. -/
theorem exists_gauge {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ)
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s)
    {ψ₁ ψ₂ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (h₁ : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder ψ₁)
    (h₂ : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder ψ₂)
    (h₁0 : ∀ s : ℝ, ψ₁ (γ s) = 0) (h₂0 : ∀ s : ℝ, ψ₂ (γ s) = 0) (s₀ : ℝ)
    (hT₁ : Work.Noncompact.CompressionTube.Transverse γ g ψ₁ s₀)
    (hT₂ : Work.Noncompact.CompressionTube.Transverse γ g ψ₂ s₀) :
    ∃ A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)),
      Function.Injective A ∧
      (∀ v : TangentSpace (Work.Noncompact.CompressionTube.MC n) (γ s₀),
        A (mfderiv (Work.Noncompact.CompressionTube.MC n)
            (Work.Noncompact.CompressionTube.MC (n - 1)) ψ₂ (γ s₀) v) =
        mfderiv (Work.Noncompact.CompressionTube.MC n)
          (Work.Noncompact.CompressionTube.MC (n - 1)) ψ₁ (γ s₀) v) := by
  classical
  -- the two differentials at the base point, and the differential of `g`
  let L₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ₁ (γ s₀)
  let L₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    mfderiv (MC n) (MC (n - 1)) ψ₂ (γ s₀)
  let Lg : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (MC n) MCreal g (γ s₀)
  let vel : EuclideanSpace ℝ (Fin n) := mfderiv MCreal (MC n) γ s₀ 1
  -- the velocity of `γ` is killed by both differentials, and is not killed by `dg`
  have hvel₁ : L₁ vel = 0 := mfderiv_velocity_eq_zero hγ h₁ h₁0 s₀
  have hvel₂ : L₂ vel = 0 := mfderiv_velocity_eq_zero hγ h₂ h₂0 s₀
  have hvelg : Lg vel = 1 := mfderiv_g_velocity hgcore hγ hg s₀
  -- the map `v ↦ (dψ₂ v, dg v)` is injective (this is the transversality of `ψ₂`)
  let Φ : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := L₂.prod Lg
  have hΦapply : ∀ v : EuclideanSpace ℝ (Fin n), Φ v = (L₂ v, Lg v) := fun v => rfl
  have hΦinj : Function.Injective Φ := by
    intro v w hvw
    have h : Φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 : L₂ (v - w) = 0 := by
      simpa [hΦapply (v - w)] using congrArg Prod.fst h
    have h2 : Lg (v - w) = 0 := by
      simpa [hΦapply (v - w)] using congrArg Prod.snd h
    exact sub_eq_zero.mp (hT₂ (v - w) h1 h2)
  -- the domain and the target of `Φ` have the same dimension
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace,
      Module.finrank_self, Fintype.card_fin, Fintype.card_fin]
    omega
  have hΦinjL : Function.Injective Φ.toLinearMap := hΦinj
  -- hence `Φ` is a linear equivalence
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
    Φ.toLinearMap.linearEquivOfInjective hΦinjL hdim
  have heapp : ∀ y : EuclideanSpace ℝ (Fin n), e y = Φ y := by
    intro y
    show (Φ.toLinearMap.linearEquivOfInjective hΦinjL hdim) y = Φ y
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  -- a section of `dψ₂`, sending `u` to the unique `v` with `dψ₂ v = u`, `dg v = 0`
  let S : EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    e.symm.toLinearMap.comp (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n - 1))) ℝ)
  have hSapply : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), S u = e.symm (u, 0) := fun u => rfl
  -- the gauge and its continuous version
  let Aₗ : EuclideanSpace ℝ (Fin (n - 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    L₁.toLinearMap.comp S
  let A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    Aₗ.toContinuousLinearMap
  have hAapply : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), A u = Aₗ u := fun u => rfl
  -- `S` is a right inverse of `dψ₂`
  have heS : ∀ u : EuclideanSpace ℝ (Fin (n - 1)), e (S u) = (u, 0) := by
    intro u
    rw [hSapply u, LinearEquiv.apply_symm_apply]
  have hvel_e : e vel = (0, 1) := by
    rw [heapp vel, hΦapply vel, hvel₂, hvelg]
  -- the decomposition of a tangent vector along the velocity
  have hvec : ∀ v : EuclideanSpace ℝ (Fin n), S (L₂ v) + Lg v • vel = v := by
    intro v
    apply e.injective
    rw [map_add, map_smul, heS (L₂ v), hvel_e, heapp v, hΦapply v]
    simp
  refine ⟨A, ?_, ?_⟩
  · -- injectivity of the gauge
    intro x y hxy
    have hz : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz' : Aₗ (x - y) = 0 := by rw [← hAapply (x - y)]; exact hz
    have hL1 : L₁ (S (x - y)) = 0 := hz'
    have hLg : Lg (S (x - y)) = 0 := by
      have h := congrArg Prod.snd (heS (x - y))
      rw [heapp (S (x - y)), hΦapply (S (x - y))] at h
      simpa using h
    have hS0 : S (x - y) = 0 := hT₁ (S (x - y)) hL1 hLg
    have hxy0 : x - y = 0 := by
      have h := congrArg Prod.fst (heS (x - y))
      rw [heapp (S (x - y)), hΦapply (S (x - y)), hS0] at h
      simpa using h.symm
    exact sub_eq_zero.mp hxy0
  · -- the defining property of the gauge
    intro v
    change A (L₂ v) = L₁ v
    have h1 : A (L₂ v) = Aₗ (L₂ v) := rfl
    have h2 : Aₗ (L₂ v) = L₁ (S (L₂ v)) := rfl
    have h3 : L₁ v = L₁ (S (L₂ v)) := by
      conv_lhs => rw [← hvec v]
      rw [map_add, map_smul, hvel₁, smul_zero, add_zero]
    rw [h1, h2]
    exact h3.symm

end Work.Noncompact.CompressionTube
