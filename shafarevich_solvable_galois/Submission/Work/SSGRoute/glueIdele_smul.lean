import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_idele_defs
import Submission.Work.SSGRoute.level_decomp_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Equivariance of the gluing construction `glueIdele`

For a finite `Gal(K/k)`-stable set `S` of places and a transversal `R` of the
`Gal(K/k)`-orbits, the gluing map `glueIdele` assembles the local data
`a : ∏_{w ∈ R} Hom_{D_w}(res_w M, B_w^S)` into an idèle in the level `𝕀_K^S`.
It is the `Gal(K/k)`-equivariant (in `m : M.V`) map exhibiting the surjectivity
of `thetaL0Map`; the present file proves this equivariance,
`glueIdele ((M.ρ τ) m) = τ • glueIdele m`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-! ## Generic transport helpers -/

/-- Cancelling two mutually inverse transports of a local unit along an equality of places. -/
theorem cast_self_symm_units {L : Type} [Field L] [NumberField L] {a b : NK.GlobalCFT.Place L}
    (h : a = b) (x : (NK.GlobalCFT.Place.localField L b)ˣ) : h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

/-- Two transported local units agree as soon as they are heterogeneously equal and land in the
same target place. -/
theorem eq_cast_of_heq_units {L : Type} [Field L] [NumberField L] {a b v : NK.GlobalCFT.Place L}
    (hx : a = v) (hy : b = v) {x : (NK.GlobalCFT.Place.localField L a)ˣ}
    {y : (NK.GlobalCFT.Place.localField L b)ˣ} (h : HEq x y) : hx ▸ x = hy ▸ y := by
  subst hx; subst hy; exact eq_of_heq h

/-! ## Transport of `glueAt` in its arguments -/

/-- `glueAt` depends on the representative `w ∈ R` only through its underlying place, so that
representatives of the same orbit give heterogeneously equal values. -/
theorem glueAt_w_heq (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) {w w' : R} (h : w = w') (σ : K ≃ₐ[k] K) :
    HEq (glueAt k K R hR M S a w σ m) (glueAt k K R hR M S a w' σ m) := by
  cases h; rfl

/-- Transport of `glueAt` in the Galois element. -/
theorem glueAt_cast_sigma (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (w : R) {σ σ' : K ≃ₐ[k] K} (h : σ = σ') :
    glueAt k K R hR M S a w σ' m
      = (congrArg (fun s : K ≃ₐ[k] K => s • w.1) h) ▸ glueAt k K R hR M S a w σ m := by
  cases h; rfl

/-- The value of `glueAt` at `τ * σ` applied to `(M.ρ τ) m` is the corresponding local value. -/
theorem glueAt_mul_rho (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (w : R) (τ σ : K ≃ₐ[k] K) :
    glueAt k K R hR M S a w (τ * σ) ((M.ρ τ) m)
      = NK.HassePrinciple.actVal (τ * σ) w.1
          (toLocal k K w.1
            ((Rep.Hom.hom (BOfIncl k K w.1 S)) ((a w) ((M.ρ σ⁻¹) m)))) := by
  rw [glueAt]
  congr 1
  congr 1
  have h1 : (M.ρ (τ * σ)⁻¹) ((M.ρ τ) m) = (M.ρ ((τ * σ)⁻¹ * τ)) m := by
    rw [map_mul]; rfl
  rw [h1]
  rw [show (τ * σ)⁻¹ * τ = σ⁻¹ by group]

/-! ## The two component computations -/

/-- **The component of the translate `τ • glueIdele m` at `v`**, computed by pulling the
component at `τ⁻¹ • v` back to the representative place of `v`. -/
theorem smul_glueIdele_apply (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (hS : S.carrier.Finite)
    (a : ∀ w : R, Rep.res (decompK (k := k) w.1).subtype M ⟶ BOf k K w.1 S)
    (m : M.V) (τ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K) :
    (τ • glueIdele k K R hR M S hS a m) v
      = ((mul_smul τ (reprσ k K R hR (τ⁻¹ • v))
            (reprW k K R hR (τ⁻¹ • v)).1).trans
          ((congrArg (fun p => τ • p) (reprσ_smul_reprW k K R hR (τ⁻¹ • v))).trans
            (smul_inv_smul τ v)))
        ▸ NK.HassePrinciple.actVal (τ * reprσ k K R hR (τ⁻¹ • v))
            (reprW k K R hR (τ⁻¹ • v)).1
            (localVal k K R hR M S a m (τ⁻¹ • v)) := by
  rw [NK.HassePrinciple.smul_apply_eq_of_eq (smul_inv_smul τ v)
    (glueIdele k K R hR M S hS a m)]
  rw [glueIdele_eq_glueAt k K R hR M S hS a m (τ⁻¹ • v)]
  have hY : glueAt k K R hR M S a (reprW k K R hR (τ⁻¹ • v))
        (reprσ k K R hR (τ⁻¹ • v)) m
      = NK.HassePrinciple.actVal (reprσ k K R hR (τ⁻¹ • v))
          (reprW k K R hR (τ⁻¹ • v)).1
          (localVal k K R hR M S a m (τ⁻¹ • v)) := rfl
  rw [hY]
  rw [NK.HassePrinciple.actVal_cast (reprσ_smul_reprW k K R hR (τ⁻¹ • v))]
  have hcomp : NK.HassePrinciple.actVal τ
        (reprσ k K R hR (τ⁻¹ • v) • (reprW k K R hR (τ⁻¹ • v)).1)
        (NK.HassePrinciple.actVal (reprσ k K R hR (τ⁻¹ • v))
          (reprW k K R hR (τ⁻¹ • v)).1
          (localVal k K R hR M S a m (τ⁻¹ • v)))
      = (mul_smul τ (reprσ k K R hR (τ⁻¹ • v))
          (reprW k K R hR (τ⁻¹ • v)).1)
        ▸ NK.HassePrinciple.actVal (τ * reprσ k K R hR (τ⁻¹ • v))
            (reprW k K R hR (τ⁻¹ • v)).1
            (localVal k K R hR M S a m (τ⁻¹ • v)) := by
    conv_rhs => rw [NK.HassePrinciple.actVal_comp τ (reprσ k K R hR (τ⁻¹ • v))
      (reprW k K R hR (τ⁻¹ • v)).1 (localVal k K R hR M S a m (τ⁻¹ • v))]
    exact (cast_self_symm_units _ _).symm
  rw [hcomp]
  simp only [NK.HassePrinciple.cast_cast]

/-! ## The main equivariance -/

theorem glueIdele_smul (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (S : NK.HassePrinciple.GStableSet k K)
    (hS : S.carrier.Finite)
    (a : ∀ w : R, Rep.res (SSGRoute.PTExt.decompK (k := k) w.1).subtype M ⟶
      Work.SSGRoute.BOf k K w.1 S)
    (m : M.V) (τ : K ≃ₐ[k] K) :
    Work.SSGRoute.glueIdele k K R hR M S hS a ((M.ρ τ) m)
      = τ • Work.SSGRoute.glueIdele k K R hR M S hS a m := by
  apply NK.GlobalCFT.Idele.ext
  intro v
  rw [smul_glueIdele_apply k K R hR M S hS a m τ v]
  rw [localVal]
  rw [← glueAt_mul_rho k K R hR M S a m (reprW k K R hR (τ⁻¹ • v)) τ
      (reprσ k K R hR (τ⁻¹ • v))]
  rw [glueIdele_eq_glueAt]
  have hσ₁ : (τ * reprσ k K R hR (τ⁻¹ • v)) • (reprW k K R hR v).1 = v := by
    rw [mul_smul, reprσ_smul_inv_eq k K R hR v τ, smul_inv_smul]
  have hd : ((τ * reprσ k K R hR (τ⁻¹ • v))⁻¹ * reprσ k K R hR v)
      • (reprW k K R hR v).1 = (reprW k K R hR v).1 := by
    rw [mul_smul, reprσ_smul_reprW k K R hR v]
    exact inv_smul_eq_iff.mpr hσ₁.symm
  have hσ : (τ * reprσ k K R hR (τ⁻¹ • v)) *
      ((τ * reprσ k K R hR (τ⁻¹ • v))⁻¹ * reprσ k K R hR v)
      = reprσ k K R hR v := by group
  rw [glueAt_cast_sigma k K R hR M S a ((M.ρ τ) m) (reprW k K R hR v) hσ]
  rw [glueAt_coset k K R hR M S a ((M.ρ τ) m) (reprW k K R hR v)
      (τ * reprσ k K R hR (τ⁻¹ • v))
      ⟨(τ * reprσ k K R hR (τ⁻¹ • v))⁻¹ * reprσ k K R hR v, hd⟩]
  simp only [NK.HassePrinciple.cast_cast]
  apply eq_cast_of_heq_units
  exact glueAt_w_heq k K R hR M S a ((M.ρ τ) m)
    (reprW_smul_inv k K R hR v τ).symm (τ * reprσ k K R hR (τ⁻¹ • v))

end

end Work.SSGRoute
