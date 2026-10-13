import Mathlib
import Submission.Work.DSAMR.Defs
import Submission.Work.DSAMR.ECBase

/-!
# The two homotopy-construction steps for `Work.DSAMR.exists_coaug_lift`

`ec_step_proved` is the descending-induction step and `ec_final_proved` the degree-`0` endgame of the
almost-null-homotopy argument (node **AMR** of the MIX2 design).  The main theorem
`Work.DSAMR.exists_coaug_lift` combines them.
-/

open CategoryTheory Limits

namespace Work.DSAMR
universe u

/-- **Induction step** of the almost-null-homotopy construction (see the docstring of
`Work.DSAMR.exists_coaug_lift`): from a level-`j+1` datum with loss `t ^ m` produce a level-`j` datum
with loss `t ^ (m+1)`. -/
theorem ec_step_proved {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W) (ϖ : ℕ → W)
    (I : Ideal W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} (e : ModuleCat.of W W ⟶ K.X 0)
    (hK : Work.DSAMR.AlmostAcycZ ϖ I K e)
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : DSMap.Mix.IsBddFinFree P)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (t j m : ℕ)
    (hprev : ∃ h1 : P.X (((j:ℤ)+1)+1) ⟶ (ModuleCat.restrictScalars ψ).obj (K.X ((j:ℤ)+1)),
      ∀ y : P.X (((j:ℤ)+1)+1), (P.d (((j:ℤ)+1)+1) (((j:ℤ)+1)+1+1)).hom y = 0 →
        ϖ t ^ m • (show K.X (((j:ℤ)+1)+1) from (ρ.f (((j:ℤ)+1)+1)) y) -
          (K.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom (show K.X ((j:ℤ)+1) from h1 y)
            ∈ I • (⊤ : Submodule W (K.X (((j:ℤ)+1)+1)))) :
    ∃ h0 : P.X ((j:ℤ)+1) ⟶ (ModuleCat.restrictScalars ψ).obj (K.X (j:ℤ)),
      ∀ y : P.X ((j:ℤ)+1), (P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom y = 0 →
        ϖ t ^ (m+1) • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) y) -
          (K.d (j:ℤ) ((j:ℤ)+1)).hom (show K.X (j:ℤ) from h0 y)
            ∈ I • (⊤ : Submodule W (K.X ((j:ℤ)+1))) := by
  classical
  obtain ⟨h1, hrel⟩ := hprev
  haveI hfree : Module.Free A (P.X ((j:ℤ)+1)) := (hP.1 ((j:ℤ)+1)).1
  set b := Module.Free.chooseBasis A (P.X ((j:ℤ)+1)) with hb
  -- values on the basis, in the restricted module
  have key : ∀ i, ∃ y : (ModuleCat.restrictScalars ψ).obj (K.X (j:ℤ)),
      ϖ t • (ϖ t ^ m • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) (b i)) -
        (show K.X ((j:ℤ)+1) from h1 ((P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom (b i)))) -
      (K.d (j:ℤ) ((j:ℤ)+1)).hom (show K.X (j:ℤ) from y)
        ∈ I • (⊤ : Submodule W (K.X ((j:ℤ)+1))) := by
    intro i
    have hcyc : (P.d (((j:ℤ)+1)+1) (((j:ℤ)+1)+1+1)).hom
        ((P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom (b i)) = 0 := d_d_apply P _ _
    have hrel' := hrel _ hcyc
    have hdz : (K.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom
        (ϖ t ^ m • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) (b i)) -
          (show K.X ((j:ℤ)+1) from h1 ((P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom (b i))))
        ∈ I • (⊤ : Submodule W (K.X (((j:ℤ)+1)+1))) := by
      rw [map_sub, map_smul, rho_comm_apply ψ ρ ((j:ℤ)+1) (b i)]
      exact hrel'
    obtain ⟨y, hy⟩ := hK.2.2 j _ hdz t
    exact ⟨(show ↑((ModuleCat.restrictScalars ψ).obj (K.X (j:ℤ))) from y), hy⟩
  choose yval hyval using key
  -- the linear maps
  set h0lin : P.X ((j:ℤ)+1) →ₗ[A] (ModuleCat.restrictScalars ψ).obj (K.X (j:ℤ)) :=
    b.constr A yval with hh0
  set Phi : P.X ((j:ℤ)+1) →ₗ[A] (ModuleCat.restrictScalars ψ).obj (K.X ((j:ℤ)+1)) :=
    b.constr A (fun i => ϖ t • (ϖ t ^ m • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) (b i)) -
        (show K.X ((j:ℤ)+1) from h1 ((P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom (b i)))) -
      (K.d (j:ℤ) ((j:ℤ)+1)).hom (show K.X (j:ℤ) from yval i)) with hPhi
  have hpsiM : ∀ (a : A) (x : (ModuleCat.restrictScalars ψ).obj (K.X ((j:ℤ)+1))),
      a • x = ψ a • x := fun a x => rfl
  set Psi : P.X ((j:ℤ)+1) →ₗ[A] (ModuleCat.restrictScalars ψ).obj (K.X ((j:ℤ)+1)) :=
    (smulLin ψ hpsiM (ϖ t ^ (m+1))).comp (ρ.f ((j:ℤ)+1)).hom -
      (((ModuleCat.restrictScalars ψ).map (K.d (j:ℤ) ((j:ℤ)+1))).hom.comp h0lin) -
      (smulLin ψ hpsiM (ϖ t)).comp
        (h1.hom.comp (P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom) with hPsi
  have h0_b : ∀ i, h0lin (b i) = yval i := fun i => Module.Basis.constr_basis b A yval i
  have hPhi_b : ∀ i, Phi (b i) =
      ϖ t • (ϖ t ^ m • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) (b i)) -
        (show K.X ((j:ℤ)+1) from h1 ((P.d ((j:ℤ)+1) (((j:ℤ)+1)+1)).hom (b i)))) -
      (K.d (j:ℤ) ((j:ℤ)+1)).hom (show K.X (j:ℤ) from yval i) := by
    intro i
    rw [hPhi]
    exact Module.Basis.constr_basis b A _ i
  have hPsiPhi : Psi = Phi := by
    apply b.ext
    intro i
    rw [hPhi_b i, hPsi]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, smulLin_apply,
      ModuleCat.restrictScalars.map_apply, h0_b i]
    exact pow_succ_smul_sub_sub (ϖ t) m _ _ _
  have hmem : ∀ x : P.X ((j:ℤ)+1), Psi x ∈ I • (⊤ : Submodule W (K.X ((j:ℤ)+1))) :=
    fun x => linmem ψ (fun a n => rfl) b _ Psi
      (fun i => by rw [hPsiPhi, hPhi_b i]; exact hyval i) x
  refine ⟨(ConcreteCategory.ofHom (C := ModuleCat.{u} A) h0lin :
      P.X ((j:ℤ)+1) ⟶ (ModuleCat.restrictScalars ψ).obj (K.X (j:ℤ))), fun y hy => ?_⟩
  have h := hmem y
  have h' : Psi y = ϖ t ^ (m+1) • (show K.X ((j:ℤ)+1) from (ρ.f ((j:ℤ)+1)) y) -
      (K.d (j:ℤ) ((j:ℤ)+1)).hom (show K.X (j:ℤ) from h0lin y) := by
    rw [hPsi]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, smulLin_apply,
      ModuleCat.restrictScalars.map_apply, hy, map_zero, smul_zero, sub_zero]
    rfl
  rw [h'] at h
  exact h

/-- **Final (degree `0`) step** of the almost-null-homotopy construction: from the level-`1` datum
with loss `t ^ N` produce an `A`-linear `h : P^0 → W` with `ϖ t ^ (N+1) • ρ^0 x - e (h x) ∈ I·K^0` for
every cocycle `x`. -/
theorem ec_final_proved {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W) (ϖ : ℕ → W)
    (I : Ideal W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} (e : ModuleCat.of W W ⟶ K.X 0)
    (hK : Work.DSAMR.AlmostAcycZ ϖ I K e)
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : DSMap.Mix.IsBddFinFree P)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (t N : ℕ)
    (h1 : P.X 1 ⟶ (ModuleCat.restrictScalars ψ).obj (K.X 0))
    (hrel1 : ∀ y : P.X 1, (P.d 1 2).hom y = 0 →
      ϖ t ^ N • (show K.X 1 from (ρ.f 1) y) -
        (K.d 0 1).hom (show K.X 0 from h1 y) ∈ I • (⊤ : Submodule W (K.X 1))) :
    ∃ h : P.X 0 ⟶ (ModuleCat.restrictScalars ψ).obj (ModuleCat.of W W),
      ∀ x : P.X 0, (P.d 0 1).hom x = 0 →
        ϖ t ^ (N+1) • (show K.X 0 from (ρ.f 0) x) -
          e.hom (show W from h x) ∈ I • (⊤ : Submodule W (K.X 0)) := by
  classical
  haveI hfree : Module.Free A (P.X 0) := (hP.1 0).1
  set b := Module.Free.chooseBasis A (P.X 0) with hb
  have key : ∀ i, ∃ w : (ModuleCat.restrictScalars ψ).obj (ModuleCat.of W W),
      ϖ t • (ϖ t ^ N • (show K.X 0 from (ρ.f 0) (b i)) -
        (show K.X 0 from h1 ((P.d 0 1).hom (b i)))) -
      e.hom (show W from w) ∈ I • (⊤ : Submodule W (K.X 0)) := by
    intro i
    have hcyc : (P.d 1 2).hom ((P.d 0 1).hom (b i)) = 0 := d_d_apply P 0 (b i)
    have hrel' := hrel1 _ hcyc
    have hdz : (K.d 0 1).hom (ϖ t ^ N • (show K.X 0 from (ρ.f 0) (b i)) -
        (show K.X 0 from h1 ((P.d 0 1).hom (b i)))) ∈ I • (⊤ : Submodule W (K.X 1)) := by
      rw [map_sub, map_smul, rho_comm_apply_zero ψ ρ (b i)]
      exact hrel'
    obtain ⟨w, hw⟩ := hK.2.1 _ hdz t
    exact ⟨(show ↑((ModuleCat.restrictScalars ψ).obj (ModuleCat.of W W)) from w), hw⟩
  choose wval hwval using key
  set h0lin : P.X 0 →ₗ[A] (ModuleCat.restrictScalars ψ).obj (ModuleCat.of W W) :=
    b.constr A wval with hh0
  set Phi : P.X 0 →ₗ[A] (ModuleCat.restrictScalars ψ).obj (K.X 0) :=
    b.constr A (fun i => ϖ t • (ϖ t ^ N • (show K.X 0 from (ρ.f 0) (b i)) -
        (show K.X 0 from h1 ((P.d 0 1).hom (b i)))) - e.hom (show W from wval i)) with hPhi
  have hpsiK : ∀ (a : A) (x : (ModuleCat.restrictScalars ψ).obj (K.X 0)),
      a • x = ψ a • x := fun a x => rfl
  set Psi : P.X 0 →ₗ[A] (ModuleCat.restrictScalars ψ).obj (K.X 0) :=
    (smulLin ψ hpsiK (ϖ t ^ (N+1))).comp (ρ.f 0).hom -
      (((ModuleCat.restrictScalars ψ).map e).hom.comp h0lin) -
      (smulLin ψ hpsiK (ϖ t)).comp (h1.hom.comp (P.d 0 1).hom) with hPsi
  have h0_b : ∀ i, h0lin (b i) = wval i := fun i => Module.Basis.constr_basis b A wval i
  have hPhi_b : ∀ i, Phi (b i) =
      ϖ t • (ϖ t ^ N • (show K.X 0 from (ρ.f 0) (b i)) -
        (show K.X 0 from h1 ((P.d 0 1).hom (b i)))) - e.hom (show W from wval i) := by
    intro i
    rw [hPhi]
    exact Module.Basis.constr_basis b A _ i
  have hPsiPhi : Psi = Phi := by
    apply b.ext
    intro i
    rw [hPhi_b i, hPsi]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, smulLin_apply,
      ModuleCat.restrictScalars.map_apply, h0_b i]
    exact pow_succ_smul_sub_sub (ϖ t) N _ _ _
  have hmem : ∀ x : P.X 0, Psi x ∈ I • (⊤ : Submodule W (K.X 0)) :=
    fun x => linmem ψ (fun a n => rfl) b _ Psi
      (fun i => by rw [hPsiPhi, hPhi_b i]; exact hwval i) x
  refine ⟨(ConcreteCategory.ofHom (C := ModuleCat.{u} A) h0lin :
      P.X 0 ⟶ (ModuleCat.restrictScalars ψ).obj (ModuleCat.of W W)), fun x hx => ?_⟩
  have h := hmem x
  have h' : Psi x = ϖ t ^ (N+1) • (show K.X 0 from (ρ.f 0) x) -
      e.hom (show W from h0lin x) := by
    rw [hPsi]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, smulLin_apply,
      ModuleCat.restrictScalars.map_apply, hx, map_zero, smul_zero, sub_zero]
    rfl
  rw [h'] at h
  exact h

end Work.DSAMR
