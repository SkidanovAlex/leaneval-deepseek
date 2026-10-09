import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-! ## Factoring a homomorphism through the restriction map to `Gal(K/ℚ)`

The abstract group-theoretic core of `local_factorisation`: if `φ : G₁ →* G₃` lies over
`res : G₁ →* G₂` (i.e. `q ∘ φ = res` for the projection `q : G₃ →* G₂`) and if `φ` kills
`D ∩ ker res`, then `φ|_D` factors through `res`, i.e. there is a homomorphism
`φA : D.map res →* G₃` with `φA ⟨res σ, _⟩ = φ σ` for all `σ ∈ D`.  The second part of the
conclusion records that `φA` is a *section* of `q` over `D.map res`.
-/

theorem exists_factor_map_of_kill {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (D : Subgroup G₁) (res : G₁ →* G₂) (φ : G₁ →* G₃) (q : G₃ →* G₂)
    (hkill : ∀ σ ∈ D, res σ = 1 → φ σ = 1)
    (hquot : ∀ σ : G₁, q (φ σ) = res σ) :
    ∃ φA : ↥(D.map res) →* G₃,
      (∀ σ : ↥D, φA ⟨res σ, Subgroup.mem_map_of_mem res σ.2⟩ = φ σ) ∧
      (∀ h : ↥(D.map res), q (φA h) = (h : G₂)) := by
  classical
  -- the restriction map, viewed as a surjection `↥D ↠ ↥(D.map res)`
  let f : ↥D →* ↥(D.map res) :=
    (res.comp D.subtype).codRestrict (D.map res) (fun x => Subgroup.mem_map_of_mem res x.2)
  have hfsurj : Function.Surjective f := by
    intro h
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp h.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxeq⟩
  have hcomp : ∀ σ : ↥D, (f σ : G₂) = res (σ : G₁) := fun σ => rfl
  -- `φ|_D`
  let g : ↥D →* G₃ := φ.comp D.subtype
  have hle : f.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx1 : res (x : G₁) = 1 := by
      have h' : (f x : G₂) = 1 := by rw [hx]; rfl
      rwa [hcomp x] at h'
    exact hkill (x : G₁) x.2 hx1
  refine ⟨(f.liftOfSurjective hfsurj) ⟨g, hle⟩, ?_, ?_⟩
  · intro σ
    have h1 : ((f.liftOfSurjective hfsurj) ⟨g, hle⟩) (f σ) = g σ :=
      MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hfsurj)
        (Function.rightInverse_surjInv hfsurj) ⟨g, hle⟩ σ
    have h2 : f σ = ⟨res (σ : G₁), Subgroup.mem_map_of_mem res σ.2⟩ :=
      Subtype.ext (hcomp σ)
    rw [← h2, h1]
    rfl
  · intro h
    obtain ⟨x, rfl⟩ := hfsurj h
    have h1 : ((f.liftOfSurjective hfsurj) ⟨g, hle⟩) (f x) = g x :=
      MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hfsurj)
        (Function.rightInverse_surjInv hfsurj) ⟨g, hle⟩ x
    rw [h1]
    have hgx : g x = φ (x : G₁) := rfl
    rw [hgx, hquot (x : G₁), hcomp x]

/-- `σ` lies in the kernel of the restriction `Gal(Ω/F) →* Gal(K/F)` exactly when it fixes `K`
pointwise. -/
theorem res_eq_one_iff_mem_fixingSubgroup_lf {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] (K : IntermediateField F Ω) [Normal F K] (σ : Ω ≃ₐ[F] Ω) :
    (AlgEquiv.restrictNormalHom K σ = 1) ↔ σ ∈ K.fixingSubgroup := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]

/-- **`local_factorisation`** (Schmidt–Wingberg Step 1a, the local factorisation of a Scholz
solution): for a place `A` over `Ram(K/ℚ) ∪ {p}`, the Scholz condition (i) says that `φ` is
trivial on `D_A ∩ Gal(ℚ̄/K)`, so `φ|_{D_A}` factors through the restriction map
`D_A →* Gal(K/ℚ)`; the resulting homomorphism `φA` on the image subgroup is a section of the
projection `Γ_m(τ) ↠ Gal(K/ℚ)`. -/
theorem local_factorisation (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A) :
    ∃ φA : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) →*
        Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j,
      (∀ σ : ↥(SSGRoute.decomp ℚ A),
          φA ⟨AlgEquiv.restrictNormalHom K (σ : SSGRoute.GalQ),
              Subgroup.mem_map_of_mem _ σ.2⟩ = φ (σ : SSGRoute.GalQ)) ∧
      (∀ h : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)),
          Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m i j (φA h)
            = (h : K ≃ₐ[ℚ] K)) := by
  classical
  obtain ⟨φA, h1, h2⟩ := exists_factor_map_of_kill (SSGRoute.decomp ℚ A)
    (AlgEquiv.restrictNormalHom K) φ (flowQuot p (K ≃ₐ[ℚ] K) m i j)
    (fun σ hσ hσ1 => hφ.2.1 A hA σ hσ
      ((@res_eq_one_iff_mem_fixingSubgroup_lf ℚ SSGRoute.QBar _ _ _ K ‹Normal ℚ K› σ).mp hσ1))
    (fun σ => hφ.1.2.2 σ)
  exact ⟨φA, h1, h2⟩

end Work.SSGRoute
