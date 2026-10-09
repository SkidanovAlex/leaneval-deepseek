import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
import Submission.Work.SSGRoute.kerSuccCocycle_naturality
import Submission.Work.AbsoluteGalois.sectionCocycle_mem_Z2
import Submission.Work.AbsoluteGalois.pullbackCocycle_mem_Z2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option linter.style.haveILetI false

/-- The kernel-valued section cocycle only depends on `ρ σ` and `ρ τ`: for `u, v ∈ ker ρ`,
`kerSuccCocycle (σ u) (τ v) = kerSuccCocycle σ τ`. -/
theorem kerSuccCocycle_eq_of_mem_ker {G : Type*} [Group G] {H : Type*} [Group H]
    (p : ℕ) (m i j : ℕ) (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) (h1 : s 1 = 1)
    (σ τ u v : H) (hu : u ∈ ρ.ker) (hv : v ∈ ρ.ker) :
    kerSuccCocycle p G m i j ρ s hs (σ * u) (τ * v) =
      kerSuccCocycle p G m i j ρ s hs σ τ := by
  have hu1 : ρ u = 1 := MonoidHom.mem_ker.mp hu
  have hv1 : ρ v = 1 := MonoidHom.mem_ker.mp hv
  simp only [kerSuccCocycle, kerSuccCocycleMul, map_mul, hu1, hv1, mul_one]

/-- The section cocycle, pulled back to `H` along `ρ`, satisfies the `2`-cocycle identity for
the conjugation action of `σ` by `s (ρ σ)`. -/
theorem kerSuccCocycle_cocycle_conj {G : Type*} [Group G] {H : Type*} [Group H]
    (p : ℕ) (m i j : ℕ) (ρ : H →* flowGroup p G m i j)
    (s : flowGroup p G m i j → flowGroup p G m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p G m i j (s x) = x) (h1 : s 1 = 1) :
    ∀ σ τ υ : H,
      Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j) (s (ρ σ))
          (Additive.toMul (kerSuccCocycle p G m i j ρ s hs τ υ)))
        - kerSuccCocycle p G m i j ρ s hs (σ * τ) υ
        + kerSuccCocycle p G m i j ρ s hs σ (τ * υ)
        - kerSuccCocycle p G m i j ρ s hs σ τ = 0 := by
  intro σ τ υ
  have hcomm : ∀ a b : ↥(flowGroupSucc p G m i j).ker, a * b = b * a :=
    fun a b => (flowGroupSucc_ker_isMulCommutative p G m i j).is_comm.comm a b
  have hpb := pullbackCocycle_sectionCocycle_eq p G m i j ρ s hs
  have hst : ∀ x y : H,
      (Work.AbsoluteGalois.sectionCocycle (flowGroupSucc p G m i j) s hs (ρ x, ρ y)).toMul
        = kerSuccCocycleMul p G m i j ρ s hs x y := by
    intro x y
    have h := congrFun hpb (x, y)
    simp only [Work.AbsoluteGalois.pullbackCocycle_apply] at h
    rw [h, kerSuccCocycle, toMul_ofMul]
  have key := Work.AbsoluteGalois.sectionCocycle_mul_eq
    (flowGroupSucc p G m i j) s hs h1 hcomm (ρ σ) (ρ τ) (ρ υ)
  have h2 : (Work.AbsoluteGalois.sectionCocycle (flowGroupSucc p G m i j) s hs (ρ σ * ρ τ, ρ υ)).toMul
      = kerSuccCocycleMul p G m i j ρ s hs (σ * τ) υ := by
    rw [← map_mul ρ σ τ]; exact hst (σ * τ) υ
  have h3 : (Work.AbsoluteGalois.sectionCocycle (flowGroupSucc p G m i j) s hs (ρ σ, ρ τ * ρ υ)).toMul
      = kerSuccCocycleMul p G m i j ρ s hs σ (τ * υ) := by
    rw [← map_mul ρ τ υ]; exact hst σ (τ * υ)
  rw [hst σ τ, h2, hst τ υ, h3] at key
  simp only [kerSuccCocycle, toMul_ofMul] at key ⊢
  have hconj : Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j) (s (ρ σ))
        (kerSuccCocycleMul p G m i j ρ s hs τ υ))
      = Additive.ofMul (kerSuccCocycleMul p G m i j ρ s hs σ τ)
        + Additive.ofMul (kerSuccCocycleMul p G m i j ρ s hs (σ * τ) υ)
        - Additive.ofMul (kerSuccCocycleMul p G m i j ρ s hs σ (τ * υ)) := by
    rw [← ofMul_mul, ← ofMul_div]
    congr 1
    rw [key, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  letI : CommGroup ↥(flowGroupSucc p G m i j).ker :=
    { (inferInstance : Group _) with mul_comm := hcomm }
  abel

theorem isCocycle2_isLocConst2_transported_cocycle (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (hflow : ∀ σ : SSGRoute.GalQ,
      Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m i j (φ σ) =
        AlgEquiv.restrictNormalHom K σ)
    (e : Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker ≃+
          Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)
    (he : ∀ (g : K ≃ₐ[ℚ] K) (x : Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker),
      e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
        (Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
        ((SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2)) (Additive.toMul x))) = g • e x)
    (s : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j →
      Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x) (h1 : s 1 = 1) :
    SSGRoute.IsCocycle2 (AlgEquiv.restrictNormalHom K)
        (fun σ τ => e (Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ))
      ∧ SSGRoute.IsLocConst2
        (fun σ τ => e (Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ)) := by
  refine ⟨?_, ?_⟩
  · intro g h l
    have hsr : (s (φ g)).right = AlgEquiv.restrictNormalHom K g := by
      rw [← flowGroupSucc_right p (K ≃ₐ[ℚ] K) m i j (s (φ g)), hs]
      exact hflow g
    have hconj : Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j) (s (φ g))
          (Additive.toMul (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs h l)))
        = Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
          ((SemidirectProduct.mk 1 (AlgEquiv.restrictNormalHom K g) :
            flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2))
          (Additive.toMul (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs h l))) := by
      congr 1
      rw [show s (φ g) = SemidirectProduct.mk (s (φ g)).left (s (φ g)).right from rfl, hsr]
      exact kerSucc_conj_eq_mk_one p (K ≃ₐ[ℚ] K) i j m (s (φ g)).left
        (AlgEquiv.restrictNormalHom K g) (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs h l)
    have hB := kerSuccCocycle_cocycle_conj p m i j φ s hs h1 g h l
    rw [hconj] at hB
    have key := congrArg e hB
    simp only [map_sub, map_add, map_zero] at key
    rw [he (AlgEquiv.restrictNormalHom K g)
      (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs h l)] at key
    exact key
  · refine ⟨φ.ker, hopen, ?_⟩
    intro g h u v hu hv
    show e (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs (g * u) (h * v))
      = e (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs g h)
    exact congrArg e (kerSuccCocycle_eq_of_mem_ker p m i j φ s hs h1 g h u v hu hv)

end Work.SSGRoute
