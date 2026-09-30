import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.S0SubspaceRat
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.free_and_vanishing_ball_compl
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.EMFG.kOneComparison
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMODD

noncomputable section

namespace KTwoAux

variable {𝕜 : Type} [Field 𝕜]

abbrev VR : ℤ × ℤ := Work.Pi6.vr 2

theorem subsingleton_tensor_right_p {M N : Type} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] [Subsingleton N] : Subsingleton (TensorProduct 𝕜 M N) := by
  have h0 : ∀ (m : M) (n : N), m ⊗ₜ[𝕜] n = 0 := fun m n => by
    rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
  have key : ∀ x : TensorProduct 𝕜 M N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | add a b ha hb => rw [ha, hb, add_zero]
    | tmul a b => exact h0 a b
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem linearEquiv_of_finrank_one_p {M : Type} [AddCommGroup M] [Module 𝕜 M]
    (h : Module.finrank 𝕜 M = 1) : Nonempty (M ≃ₗ[𝕜] 𝕜) := by
  haveI : FiniteDimensional 𝕜 M := FiniteDimensional.of_finrank_pos (by rw [h]; norm_num)
  have b : Module.Basis (Fin (Module.finrank 𝕜 M)) 𝕜 M := Module.finBasis 𝕜 M
  rw [h] at b
  exact ⟨b.equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) 𝕜 𝕜⟩

theorem exists_linearEquiv_coe_one_p {N : Type} [AddCommGroup N] [Module 𝕜 N]
    (hN : Module.finrank 𝕜 N = 1) {u : N} (hu : u ≠ 0) : ∃ ρ : N ≃ₗ[𝕜] 𝕜, ρ u = 1 := by
  haveI : FiniteDimensional 𝕜 N :=
    FiniteDimensional.of_finrank_pos (by rw [hN]; norm_num)
  have hinj : Function.Injective (LinearMap.toSpanSingleton 𝕜 N u) := by
    intro a b hab
    have hab' : a • u = b • u := by simpa [LinearMap.toSpanSingleton_apply] using hab
    have h : (a - b) • u = 0 := by rw [sub_smul, hab', sub_self]
    rcases smul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hu
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton 𝕜 N u) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := LinearMap.toSpanSingleton 𝕜 N u)
      (by rw [Module.finrank_self 𝕜, hN])).mp hinj
  let σ : 𝕜 ≃ₗ[𝕜] N := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨σ.symm, ?_⟩
  have hσ : σ 1 = u := by
    show (LinearEquiv.ofBijective (LinearMap.toSpanSingleton 𝕜 N u) ⟨hinj, hsurj⟩) 1 = u
    rw [LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hσ, LinearEquiv.symm_apply_apply]

theorem exists_tmul_eq_of_finrank_one_p {M N : Type} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (hN : Module.finrank 𝕜 N = 1) {u : N} (hu : u ≠ 0)
    (z : TensorProduct 𝕜 M N) : ∃ m : M, z = m ⊗ₜ[𝕜] u := by
  obtain ⟨ρ, hρ⟩ := exists_linearEquiv_coe_one_p hN hu
  let L : TensorProduct 𝕜 M N ≃ₗ[𝕜] M :=
    (TensorProduct.congr (LinearEquiv.refl 𝕜 M) ρ) ≪≫ₗ (TensorProduct.rid 𝕜 M)
  have hL : ∀ m : M, L (m ⊗ₜ[𝕜] u) = m := by
    intro m
    show (TensorProduct.rid 𝕜 M)
      ((TensorProduct.congr (LinearEquiv.refl 𝕜 M) ρ) (m ⊗ₜ[𝕜] u)) = m
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hρ, TensorProduct.rid_tmul, one_smul]
  have key : ∀ m : M, L.symm m = m ⊗ₜ[𝕜] u := fun m =>
    L.injective (by rw [LinearEquiv.apply_symm_apply, hL m])
  exact ⟨L z, by rw [← key (L z), LinearEquiv.symm_apply_apply]⟩

theorem iso_of_finrank_one_p (M : ModuleCat 𝕜) (h : Module.finrank 𝕜 (M : Type) = 1) :
    Nonempty (M ≅ ModuleCat.of 𝕜 𝕜) := by
  obtain ⟨e⟩ := linearEquiv_of_finrank_one_p (M := (M : Type)) h
  exact ⟨LinearEquiv.toModuleIso e⟩

theorem isZero_of_finrank_zero_p (M : ModuleCat 𝕜) [FiniteDimensional 𝕜 (M : Type)]
    (h : Module.finrank 𝕜 (M : Type) = 0) : IsZero M := by
  haveI : Subsingleton (M : Type) := Module.finrank_zero_iff.mp h
  exact ModuleCat.isZero_of_subsingleton M

theorem iso_inv_hom_hom_p {M N : ModuleCat 𝕜} (e : M ≅ N) (x : M) :
    e.inv.hom (e.hom.hom x) = x := by
  have h := e.toLinearEquiv.symm_apply_apply x
  simpa using h

theorem iso_hom_inv_hom_p {M N : ModuleCat 𝕜} (e : M ≅ N) (x : N) :
    e.hom.hom (e.inv.hom x) = x := by
  have h := e.toLinearEquiv.apply_symm_apply x
  simpa using h

theorem iso_inv_injective_p {M N : ModuleCat 𝕜} (e : M ≅ N) : Function.Injective e.inv.hom := by
  intro x y h
  have h' := congrArg e.hom.hom h
  rwa [iso_hom_inv_hom_p e x, iso_hom_inv_hom_p e y] at h'

theorem one_ne_zero_of_iso_p {X : Type} [TopologicalSpace X]
    (h : Nonempty (Work.Pi6.Coh 𝕜 X 0 ≅ ModuleCat.of 𝕜 𝕜)) : Work.Pi6.one 𝕜 X ≠ 0 := by
  intro hone
  obtain ⟨e⟩ := h
  have hsub : Subsingleton (Work.Pi6.Coh 𝕜 X 0) := ⟨fun a b => by
    have ha : Work.Pi6.cup 𝕜 X 0 0 a (Work.Pi6.one 𝕜 X) = a :=
      Work.Cohomology.cupH'_one_right 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 0 a
    have hb : Work.Pi6.cup 𝕜 X 0 0 b (Work.Pi6.one 𝕜 X) = b :=
      Work.Cohomology.cupH'_one_right 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 0 b
    rw [← ha, ← hb, hone]
    simp⟩
  have h10 : (1 : 𝕜) = 0 := by
    have h := Subsingleton.elim (e.toLinearEquiv.symm 1) (e.toLinearEquiv.symm 0)
    rw [map_zero] at h
    simpa using congrArg e.toLinearEquiv h
  exact one_ne_zero h10

/-- Rows `q ≤ 1` of a `CohSS` are stable from page `3` on, inside the box `s + q ≤ M`. -/
theorem rowStable_p (S : Work.Pi6.CohSS 𝕜) (M : ℕ)
    (h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))))
    (s q : ℕ) (hq : q ≤ 1) (hsq : s + q ≤ M) (r : ℕ) (hr : 3 ≤ r) :
    Nonempty (S.E r ((s : ℤ), (q : ℤ)) ≅ S.E (r + 1) ((s : ℤ), (q : ℤ))) := by
  let a : ℤ × ℤ := ((s : ℤ), (q : ℤ))
  have hout : IsZero (S.E r (a + Work.Pi6.vr r)) := by
    refine S.quad r _ (Or.inr ?_)
    simp only [a, Work.Pi6.vr, Prod.snd_add, Prod.snd_sub, Prod.snd_ofNat]
    omega
  have hsrc : IsZero (S.E r (a - Work.Pi6.vr r)) := by
    by_cases hrs : r ≤ s
    · have heq : a - Work.Pi6.vr r
          = (((s - r : ℕ) : ℤ), ((q + r - 1 : ℕ) : ℤ)) := by
        simp only [a, Work.Pi6.vr, Prod.mk_sub_mk, Prod.fst_ofNat]
        ext <;> push_cast <;> omega
      rw [heq]
      have h := S.isZero_two_of (((s - r : ℕ) : ℤ), ((q + r - 1 : ℕ) : ℤ))
        (h2 (s - r) (q + r - 1) (by omega) (by omega)) (r - 2)
      simpa [show r - 2 + 2 = r from by omega] using h
    · refine S.quad r _ (Or.inl ?_)
      simp only [a, Work.Pi6.vr, Prod.fst_sub, Prod.fst_ofNat]
      omega
  have hd0 : S.d r a (a + Work.Pi6.vr r) = 0 := hout.eq_of_tgt _ _
  have hd1 : S.d r (a - Work.Pi6.vr r) a = 0 := hsrc.eq_of_src _ _
  let φ : S.E r a →ₗ[𝕜] S.E (r + 1) a :=
    { toFun := fun x => S.proj r a ⟨x, by rw [hd0]; rfl⟩
      map_add' := fun x y => by rw [← map_add]; rfl
      map_smul' := fun c x => by rw [← map_smul]; rfl }
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have hxy' : S.proj r a ⟨x, by rw [hd0]; rfl⟩ = S.proj r a ⟨y, by rw [hd0]; rfl⟩ := hxy
      have hzero : S.proj r a (⟨x, by rw [hd0]; rfl⟩ - ⟨y, by rw [hd0]; rfl⟩) = 0 := by
        rw [map_sub, hxy', sub_self]
      have hmem := (S.proj_ker r a (by omega)
        (⟨x, by rw [hd0]; rfl⟩ - ⟨y, by rw [hd0]; rfl⟩)).mp hzero
      rw [hd1] at hmem
      obtain ⟨w, hw⟩ := hmem
      have h0 : x - y = 0 := by simpa using hw.symm
      exact sub_eq_zero.mp h0
    · intro y
      obtain ⟨x, hx⟩ := S.proj_surj r a (by omega) y
      exact ⟨x.1, (congrArg (S.proj r a) (Subtype.ext rfl)).trans hx⟩
  exact ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective φ hbij)⟩

theorem e3_stable_p (S : Work.Pi6.CohSS 𝕜) (M : ℕ)
    (h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))))
    (s q : ℕ) (hq : q ≤ 1) (hsq : s + q ≤ M) (k : ℕ) :
    Nonempty (S.E (k + 3) ((s : ℤ), (q : ℤ)) ≅ S.E 3 ((s : ℤ), (q : ℤ))) := by
  induction k with
  | zero => exact ⟨Iso.refl _⟩
  | succ k ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨e'⟩ := rowStable_p S M h2 s q hq hsq (k + 3) (by omega)
      exact ⟨e'.symm ≪≫ e⟩

/-- **The third page of a two-row spectral sequence with acyclic total space vanishes on the two
rows.** -/
theorem e3_isZero_p {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (M : ℕ) (hM : 1 ≤ M) (S : Work.Pi6.CohSS 𝕜)
    (hS : Work.Pi6.IsSerreMSS S p e₀ M)
    (h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))))
    (hE : ∀ n : ℕ, 1 ≤ n → n ≤ M → Subsingleton (Work.Pi6.Coh 𝕜 E n)) :
    (∀ n : ℕ, 1 ≤ n → n ≤ M → IsZero (S.E 3 ((n : ℤ), (0 : ℤ)))) ∧
      (∀ n : ℕ, n + 1 ≤ M → IsZero (S.E 3 ((n : ℤ), (1 : ℤ)))) := by
  obtain ⟨e2, hmul, hconv0, hconvdim, hbot, hcol⟩ := hS
  constructor
  · intro n hn1 hnM
    have hz := hconv0 n hn1 hnM (hE n hn1 hnM) n 0 (by omega)
    rw [show n + 2 = (n - 1) + 3 from by omega] at hz
    obtain ⟨e⟩ := e3_stable_p S M h2 n 0 (by omega) (by omega) (n - 1)
    exact IsZero.of_iso hz e.symm
  · intro n hnM
    have hz := hconv0 (n + 1) (by omega) hnM (hE (n + 1) (by omega) hnM) n 1 (by omega)
    rw [show (n + 1) + 2 = n + 3 from by omega] at hz
    obtain ⟨e⟩ := e3_stable_p S M h2 n 1 (by omega) (by omega) n
    exact IsZero.of_iso hz e.symm

/-- `IsZero` of a page term transports along an equality of bidegrees. -/
theorem isZero_congr_p (S : Work.Pi6.CohSS 𝕜) (r : ℕ) {a b : ℤ × ℤ} (h : a = b)
    (ha : IsZero (S.E r a)) : IsZero (S.E r b) :=
  IsZero.of_iso ha (eqToIso (congrArg (S.E r) h)).symm

-- index identity
example (m : ℕ) : (((m : ℤ)), (1 : ℤ)) = ((((m + 2 : ℕ) : ℤ), (0 : ℤ)) - Work.Pi6.vr 2) := by
  simp only [Work.Pi6.vr, Prod.mk_sub_mk]
  ext <;> push_cast <;> omega

/-- **`d₂` is injective on the row `1`** (nothing maps into it). -/
theorem dTwo_inj_p (S : Work.Pi6.CohSS 𝕜) (M : ℕ)
    (h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))))
    (h31 : ∀ n : ℕ, n + 1 ≤ M → IsZero (S.E 3 ((n : ℤ), (1 : ℤ))))
    (n : ℕ) (hn : n + 2 ≤ M) :
    Function.Injective (S.d 2 ((n : ℤ), (1 : ℤ)) (((n + 2 : ℕ) : ℤ), (0 : ℤ))).hom := by
  intro x y hxy
  let a : ℤ × ℤ := ((n : ℤ), (1 : ℤ))
  haveI : Subsingleton (S.E 3 a) := ModuleCat.subsingleton_of_isZero (h31 n (by omega))
  have hsrc : IsZero (S.E 2 (a - Work.Pi6.vr 2)) := by
    by_cases hsmall : (n : ℤ) - 2 < 0
    · refine S.quad 2 _ (Or.inl ?_)
      simp only [a, Work.Pi6.vr, Prod.fst_sub]
      omega
    · have hnat : IsZero (S.E 2 (((n - 2 : ℕ) : ℤ), (2 : ℤ))) :=
        S.isZero_two_of (((n - 2 : ℕ) : ℤ), ((2 : ℕ) : ℤ))
          (h2 (n - 2) 2 (by omega) (by omega)) 0
      refine isZero_congr_p S 2 ?_ hnat
      simp only [a, Work.Pi6.vr, Prod.mk_sub_mk]
      ext <;> push_cast <;> omega
  have hd1 : S.d 2 (a - Work.Pi6.vr 2) a = 0 := hsrc.eq_of_src _ _
  have hcyc : (S.d 2 a (a + Work.Pi6.vr 2)).hom (x - y) = 0 := by
    have h : (S.d 2 a (a + Work.Pi6.vr 2)).hom x = (S.d 2 a (a + Work.Pi6.vr 2)).hom y := hxy
    rw [map_sub, h, sub_self]
  have hzero : S.proj 2 a ⟨x - y, hcyc⟩ = 0 := Subsingleton.elim _ _
  have hmem := (S.proj_ker 2 a (by norm_num) ⟨x - y, hcyc⟩).mp hzero
  rw [hd1] at hmem
  obtain ⟨w, hw⟩ := hmem
  have h0 : x - y = 0 := by simpa using hw.symm
  exact sub_eq_zero.mp h0

/-- **`d₂` is surjective onto the row `0`** (its cokernel vanishes). -/
theorem dTwo_surj_p (S : Work.Pi6.CohSS 𝕜) (M : ℕ)
    (h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))))
    (h30 : ∀ n : ℕ, 1 ≤ n → n ≤ M → IsZero (S.E 3 ((n : ℤ), (0 : ℤ))))
    (n : ℕ) (hn : n + 2 ≤ M) :
    Function.Surjective (S.d 2 ((n : ℤ), (1 : ℤ)) (((n + 2 : ℕ) : ℤ), (0 : ℤ))).hom := by
  intro y
  haveI : Subsingleton (S.E 3 (((n + 2 : ℕ) : ℤ), (0 : ℤ))) :=
    ModuleCat.subsingleton_of_isZero (h30 (n + 2) (by omega) (by omega))
  have hout : IsZero (S.E 2 ((((n + 2 : ℕ) : ℤ), (0 : ℤ)) + Work.Pi6.vr 2)) := by
    refine S.quad 2 _ (Or.inr ?_)
    simp only [Work.Pi6.vr, Prod.snd_add, Prod.snd_sub, Prod.snd_ofNat]
    omega
  have hcyc : (S.d 2 (((n + 2 : ℕ) : ℤ), (0 : ℤ))
      ((((n + 2 : ℕ) : ℤ), (0 : ℤ)) + Work.Pi6.vr 2)).hom y = 0 := by
    rw [S.d_eq_zero_of_isZero hout]
    rfl
  have hzero : S.proj 2 (((n + 2 : ℕ) : ℤ), (0 : ℤ)) ⟨y, hcyc⟩ = 0 := Subsingleton.elim _ _
  have hmem := (S.proj_ker 2 (((n + 2 : ℕ) : ℤ), (0 : ℤ)) (by norm_num) ⟨y, hcyc⟩).mp hzero
  rw [show ((((n + 2 : ℕ) : ℤ), (0 : ℤ)) - Work.Pi6.vr 2) =
      (((n : ℤ)), (1 : ℤ)) from by
    simp only [Work.Pi6.vr, Prod.mk_sub_mk]
    ext <;> push_cast <;> omega] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

/-- **`d₂` is an isomorphism from the row `1` to the row `0` in the range.** -/
theorem dTwo_iso_m_p (S : Work.Pi6.CohSS 𝕜) (M : ℕ)
    (h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))))
    (h30 : ∀ n : ℕ, 1 ≤ n → n ≤ M → IsZero (S.E 3 ((n : ℤ), (0 : ℤ))))
    (h31 : ∀ n : ℕ, n + 1 ≤ M → IsZero (S.E 3 ((n : ℤ), (1 : ℤ))))
    (m : ℕ) (hm : m + 2 ≤ M) :
    Nonempty (S.E 2 ((m : ℤ), (1 : ℤ)) ≅ S.E 2 (((m + 2 : ℕ) : ℤ), (0 : ℤ))) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective _
    ⟨dTwo_inj_p S M h2 h31 m hm, dTwo_surj_p S M h2 h30 m hm⟩)⟩

/-- If a bidegree has no incoming and no outgoing differential at page `2`, then `E₂ = E₃` there. -/
theorem e2_iso_e3_p (S : Work.Pi6.CohSS 𝕜) (a : ℤ × ℤ)
    (hsrc : IsZero (S.E 2 (a - Work.Pi6.vr 2))) (hout : IsZero (S.E 2 (a + Work.Pi6.vr 2))) :
    Nonempty (S.E 2 a ≅ S.E 3 a) := by
  have hd0 : S.d 2 a (a + Work.Pi6.vr 2) = 0 := hout.eq_of_tgt _ _
  have hd1 : S.d 2 (a - Work.Pi6.vr 2) a = 0 := hsrc.eq_of_src _ _
  let φ : S.E 2 a →ₗ[𝕜] S.E 3 a :=
    { toFun := fun x => S.proj 2 a ⟨x, by rw [hd0]; rfl⟩
      map_add' := fun x y => by rw [← map_add]; rfl
      map_smul' := fun c x => by rw [← map_smul]; rfl }
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have hxy' : S.proj 2 a ⟨x, by rw [hd0]; rfl⟩ = S.proj 2 a ⟨y, by rw [hd0]; rfl⟩ := hxy
      have hzero : S.proj 2 a (⟨x, by rw [hd0]; rfl⟩ - ⟨y, by rw [hd0]; rfl⟩) = 0 := by
        rw [map_sub, hxy', sub_self]
      have hmem := (S.proj_ker 2 a (by norm_num)
        (⟨x, by rw [hd0]; rfl⟩ - ⟨y, by rw [hd0]; rfl⟩)).mp hzero
      rw [hd1] at hmem
      obtain ⟨w, hw⟩ := hmem
      have h0 : x - y = 0 := by simpa using hw.symm
      exact sub_eq_zero.mp h0
    · intro y
      obtain ⟨x, hx⟩ := S.proj_surj 2 a (by norm_num) y
      exact ⟨x.1, (congrArg (S.proj 2 a) (Subtype.ext rfl)).trans hx⟩
  exact ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective φ hbij)⟩

/-- **The abstract two-row forcing argument.** -/
theorem twoRow_main_p {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (M : ℕ) (hM : 2 ≤ M) (S : Work.Pi6.CohSS 𝕜)
    (hS : Work.Pi6.IsSerreMSS S p e₀ M)
    (hF0 : Nonempty (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0 ≅ ModuleCat.of 𝕜 𝕜))
    (hF1 : Nonempty (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1 ≅ ModuleCat.of 𝕜 𝕜))
    (hFq : ∀ q : ℕ, 2 ≤ q → q ≤ M →
      IsZero (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (hB0 : Nonempty (Work.Pi6.Coh 𝕜 B 0 ≅ ModuleCat.of 𝕜 𝕜))
    (hBfin : ∀ s : ℕ, s ≤ M → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B s))
    (hE : ∀ n : ℕ, 1 ≤ n → n ≤ M → Subsingleton (Work.Pi6.Coh 𝕜 E n))
    (hE0 : Nonempty (Work.Pi6.Coh 𝕜 E 0 ≅ ModuleCat.of 𝕜 𝕜)) :
    ∃ w : Work.Pi6.Coh 𝕜 B 2,
      (∀ k : ℕ, 2 * k ≤ M → Work.Pi6.cpow w k ≠ 0) ∧
      (∀ q : ℕ, q ≤ M → Even q → Nonempty (Work.Pi6.Coh 𝕜 B q ≅ ModuleCat.of 𝕜 𝕜)) ∧
      (∀ q : ℕ, q ≤ M → Odd q → IsZero (Work.Pi6.Coh 𝕜 B q)) := by
  obtain ⟨e2, hmul, hconv0, hconvdim, hbot, hcol⟩ := hS
  -- rows `q ≥ 2` vanish at `E₂`
  have h2 : ∀ s q : ℕ, 2 ≤ q → s + q ≤ M → IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
    intro s q hq hsq
    haveI : Subsingleton (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :=
      ModuleCat.subsingleton_of_isZero (hFq q hq (by omega))
    exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
      (e2 s q (by omega) (by omega))
  obtain ⟨h30, h31⟩ := e3_isZero_p p e₀ M (by omega) S ⟨e2, hmul, hconv0, hconvdim, hbot, hcol⟩ h2 hE
  -- dimensions of the fibre and of `H⁰(B)`
  have hF0fin : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) = 1 := by
    obtain ⟨e⟩ := hF0
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_self]
  have hF1fin : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1) = 1 := by
    obtain ⟨e⟩ := hF1
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_self]
  have hB0fin : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 B 0) = 1 := by
    obtain ⟨e⟩ := hB0
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_self]
  -- the row `0` and row `1` dimensions are those of the base
  have hA0 : ∀ n : ℕ, n ≤ M →
      Module.finrank 𝕜 ↥(S.E 2 ((n : ℤ), (0 : ℤ))) = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) := by
    intro n hn
    haveI : FiniteDimensional 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) := hBfin n hn
    calc Module.finrank 𝕜 ↥(S.E 2 ((n : ℤ), (0 : ℤ)))
        = Module.finrank 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B n)
            (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0)) :=
          LinearEquiv.finrank_eq (e2 n 0 hn (by omega)).toLinearEquiv
      _ = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) *
            Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) :=
          Module.finrank_tensorProduct
      _ = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) * 1 := by rw [hF0fin]
      _ = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) := by rw [mul_one]
  have hA1 : ∀ n : ℕ, n ≤ M →
      Module.finrank 𝕜 ↥(S.E 2 ((n : ℤ), (1 : ℤ))) = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) := by
    intro n hn
    haveI : FiniteDimensional 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) := hBfin n hn
    calc Module.finrank 𝕜 ↥(S.E 2 ((n : ℤ), (1 : ℤ)))
        = Module.finrank 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B n)
            (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1)) :=
          LinearEquiv.finrank_eq (e2 n 1 hn (by omega)).toLinearEquiv
      _ = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) *
            Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1) :=
          Module.finrank_tensorProduct
      _ = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) * 1 := by rw [hF1fin]
      _ = Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) := by rw [mul_one]
  -- `dim H⁰(E) = 1`
  have hE0fin : Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 E 0) = 1 := by
    obtain ⟨e⟩ := hE0
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_self]
  have hconv0' : Module.finrank 𝕜 ↥(S.E 2 ((0 : ℤ), (0 : ℤ))) = 1 := by
    have h := hconvdim 0 (by omega)
    simp only [Nat.zero_add, Finset.sum_range_one] at h
    exact h.trans hE0fin
  -- the dimension recursion
  have hdim : ∀ n : ℕ, n ≤ M →
      Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B n) = (if Even n then 1 else 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases n with _ | _ | m
      · have h0 : Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B 0) = 1 := by
          rw [← hA0 0 (by omega)]
          exact hconv0'
        rw [h0, if_pos (show Even 0 from ⟨0, rfl⟩)]
      · have h1 : Module.finrank 𝕜 ↥(Work.Pi6.Coh 𝕜 B 1) = 0 := by
          rw [← hA0 1 (by omega)]
          obtain ⟨e3⟩ := e2_iso_e3_p S ((1 : ℤ), (0 : ℤ))
            (S.quad 2 _ (Or.inl (by simp [Work.Pi6.vr])))
            (S.quad 2 _ (Or.inr (by simp [Work.Pi6.vr])))
          haveI : Subsingleton ↥(S.E 3 ((1 : ℤ), (0 : ℤ))) :=
            ModuleCat.subsingleton_of_isZero (h30 1 (by omega) (by omega))
          exact (LinearEquiv.finrank_eq e3.toLinearEquiv).trans
            Module.finrank_zero_of_subsingleton
        rw [h1, if_neg (show ¬ Even 1 from by rintro ⟨j, hj⟩; omega)]
      · obtain ⟨eiso⟩ := dTwo_iso_m_p S M h2 h30 h31 m (by omega)
        rw [← hA0 (m + 2) hn, ← LinearEquiv.finrank_eq eiso.toLinearEquiv, hA1 m (by omega),
          ih m (by omega) (by omega)]
        have hev : Even (m + 2) ↔ Even m := by
          constructor
          · rintro ⟨j, hj⟩; exact ⟨j - 1, by omega⟩
          · rintro ⟨j, hj⟩; exact ⟨j + 1, by omega⟩
        by_cases hpar : Even m
        · rw [if_pos hpar, if_pos (hev.mpr hpar)]
        · rw [if_neg hpar, if_neg (fun h => hpar (hev.mp h))]
  -- cup unit laws in the `Coh` notation
  have cupR : ∀ (n : ℕ) (x : Work.Pi6.Coh 𝕜 B n),
      Work.Pi6.cup 𝕜 B n 0 x (Work.Pi6.one 𝕜 B) = x := fun n x =>
    Work.Cohomology.cupH'_one_right 𝕜 (TopCat.toSSet.obj (TopCat.of B)) n x
  have cupRf : ∀ (n : ℕ) (x : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) n),
      Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) n 0 x
        (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) = x := fun n x =>
    Work.Cohomology.cupH'_one_right 𝕜
      (TopCat.toSSet.obj (TopCat.of (Work.StemsB.fibre p (p e₀)))) n x
  -- a generator of `H¹` of the fibre
  obtain ⟨φ1⟩ := hF1
  let v : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1 := φ1.inv.hom 1
  have hv : v ≠ 0 := by
    intro h
    have h1 : φ1.hom.hom v = 1 := iso_hom_inv_hom_p φ1 1
    rw [h, map_zero] at h1
    exact one_ne_zero h1.symm
  have hu : Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) ≠ 0 := one_ne_zero_of_iso_p hF0
  have huB : Work.Pi6.one 𝕜 B ≠ 0 := one_ne_zero_of_iso_p hB0
  have cupL₁ : Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 1
      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) v = v :=
    Work.Cohomology.cupH'_one_left 𝕜
      (TopCat.toSSet.obj (TopCat.of (Work.StemsB.fibre p (p e₀)))) 1 v
  have cupU : Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 0
      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))
      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) =
      Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) :=
    cupRf 0 (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))
  -- the class `1 ⊗ v` in `E₂^{0,1}`
  have hu₀ : (e2 0 1 (by omega) (by omega)).inv.hom
      (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v) ≠ 0 := by
    intro h
    have h2 : Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v = 0 :=
      iso_inv_injective_p (e2 0 1 (by omega) (by omega)) (by rw [h, map_zero])
    exact tmul_ne_zero_of_ne_zero huB hv h2
  -- division of `H²(B) ⊗ H⁰(F)` by the unit of `H⁰(F)`
  obtain ⟨ρ, hρ⟩ := exists_linearEquiv_coe_one_p hF0fin hu
  let L : TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B 2)
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) ≃ₗ[𝕜] (Work.Pi6.Coh 𝕜 B 2) :=
    (TensorProduct.congr (LinearEquiv.refl 𝕜 (Work.Pi6.Coh 𝕜 B 2)) ρ) ≪≫ₗ
      (TensorProduct.rid 𝕜 (Work.Pi6.Coh 𝕜 B 2))
  have hL : ∀ m : Work.Pi6.Coh 𝕜 B 2,
      L (m ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) = m := by
    intro m
    show (TensorProduct.rid 𝕜 (Work.Pi6.Coh 𝕜 B 2))
      ((TensorProduct.congr (LinearEquiv.refl 𝕜 (Work.Pi6.Coh 𝕜 B 2)) ρ)
        (m ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) = m
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hρ, TensorProduct.rid_tmul, one_smul]
  let w : Work.Pi6.Coh 𝕜 B 2 :=
    L ((e2 2 0 (by omega) (by omega)).hom.hom
      ((S.d 2 ((0 : ℤ), (1 : ℤ))
        (((0 : ℤ), (1 : ℤ)) + VR)).hom
        ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v))))
  have hwU : (e2 2 0 (by omega) (by omega)).inv.hom
      (w ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) =
      (S.d 2 ((0 : ℤ), (1 : ℤ))
        (((0 : ℤ), (1 : ℤ)) + VR)).hom
        ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v)) := by
    have hkey : L.symm w =
        w ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) :=
      L.injective (by rw [LinearEquiv.apply_symm_apply, hL w])
    have hmem : w ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) =
        (e2 2 0 (by omega) (by omega)).hom.hom
          ((S.d 2 ((0 : ℤ), (1 : ℤ))
            (((0 : ℤ), (1 : ℤ)) + VR)).hom
            ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v))) := by
      rw [← hkey]
      exact LinearEquiv.symm_apply_apply L _
    rw [hmem]
    exact iso_inv_hom_hom_p (e2 2 0 (by omega) (by omega)) _
  have hwU_ne : (e2 2 0 (by omega) (by omega)).inv.hom
      (w ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) ≠ 0 := by
    rw [hwU]
    intro h
    have hinj := dTwo_inj_p S M h2 h31 0 (by omega)
    have h1 : (S.d 2 ((0 : ℤ), (1 : ℤ))
        (((0 : ℤ), (1 : ℤ)) + VR)).hom
        ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v)) =
        (S.d 2 ((0 : ℤ), (1 : ℤ))
          (((0 : ℤ), (1 : ℤ)) + VR)).hom
          (0 : S.E 2 ((0 : ℤ), (1 : ℤ))) := by
      rw [h, map_zero]
    exact hu₀ (hinj h1)
  have hpow : ∀ k : ℕ, 2 * k ≤ M → Work.Pi6.cpow w k ≠ 0 := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa [Work.Pi6.cpow] using huB
    | succ k ih =>
        intro hk
        have hk' : 2 * k ≤ M := by omega
        have hab : (((2 * k : ℕ) : ℤ), (1 : ℤ)) =
            ((((2 * k : ℕ) : ℤ), (0 : ℤ)) + ((0 : ℤ), (1 : ℤ))) := by
          ext <;> simp
        have hXk : (e2 (2 * k) 0 (by omega) (by omega)).inv.hom
            (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) ≠ 0 := by
          intro h
          exact tmul_ne_zero_of_ne_zero (ih hk') hu
            (iso_inv_injective_p (e2 (2 * k) 0 (by omega) (by omega)) (by rw [h, map_zero]))
        -- `Y = X_k · u₀` is nonzero
        have hYne : S.mul 2 (((2 * k : ℕ) : ℤ), (0 : ℤ))
            ((0 : ℤ), (1 : ℤ)) (((2 * k : ℕ) : ℤ), (1 : ℤ))
            hab.symm
            ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
              (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))))
            ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v)) ≠ 0 := by
          have hm := hmul (2 * k) 0 0 1 (Work.Pi6.cpow w k)
            (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) (Work.Pi6.one 𝕜 B) v
            (by omega) (by omega)
          intro h
          have h2 : (-1 : 𝕜) ^ (0 * 0) •
              (e2 ((2 * k + 0 : ℕ)) ((0 + 1 : ℕ)) (by omega) (by omega)).inv.hom
                (Work.Pi6.cup 𝕜 B (2 * k) 0 (Work.Pi6.cpow w k) (Work.Pi6.one 𝕜 B) ⊗ₜ[𝕜]
                  Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 1
                    (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) v) = 0 := hm.symm.trans h
          rcases smul_eq_zero.mp h2 with h3 | h3
          · rw [Nat.mul_zero, pow_zero] at h3
            exact one_ne_zero h3
          · have hc1 : Work.Pi6.cup 𝕜 B (2 * k) 0 (Work.Pi6.cpow w k)
                (Work.Pi6.one 𝕜 B) ≠ 0 := by
              rw [cupR (2 * k) (Work.Pi6.cpow w k)]
              exact ih hk'
            have hc2 : Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 1
                (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) v ≠ 0 := by
              rw [cupL₁]
              exact hv
            exact tmul_ne_zero_of_ne_zero hc1 hc2
              (iso_inv_injective_p (e2 ((2 * k + 0 : ℕ)) ((0 + 1 : ℕ)) (by omega) (by omega))
                (by rw [h3, map_zero]))
        -- the differential of `Y` is `X_{k+1}`
        by_contra hcon
        have hdY : (S.d 2 (((2 * k : ℕ) : ℤ), (1 : ℤ))
            ((((2 * k : ℕ) : ℤ), (1 : ℤ)) + VR)).hom
            (S.mul 2 (((2 * k : ℕ) : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))
              (((2 * k : ℕ) : ℤ), (1 : ℤ)) hab.symm
              ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
                (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))))
              ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v))) = 0 := by
          have hleib := S.leibniz 2 (((2 * k : ℕ) : ℤ), (0 : ℤ))
            ((0 : ℤ), (1 : ℤ)) (((2 * k : ℕ) : ℤ), (1 : ℤ)) hab.symm
            ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
              (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))))
            ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v)) (by norm_num)
          rw [hleib]
          have hdx : (S.d 2 (((2 * k : ℕ) : ℤ), (0 : ℤ))
              ((((2 * k : ℕ) : ℤ), (0 : ℤ)) + VR)).hom
              ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
                (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) = 0 := by
            rw [S.d_eq_zero_of_isZero (r := 2) (a := (((2 * k : ℕ) : ℤ), (0 : ℤ)))
              (b := ((((2 * k : ℕ) : ℤ), (0 : ℤ)) + VR))
              (S.quad 2 _ (Or.inr (by
                simp only [VR, Work.Pi6.vr, Prod.snd_add, Prod.snd_sub, Prod.snd_ofNat]
                omega)))]
            rfl
          simp only [hdx, LinearMap.map_zero, LinearMap.zero_apply, zero_add]
          have hsign : ((-1 : 𝕜) ^ (Int.natAbs (((2 * k : ℕ) : ℤ) + (0 : ℤ)))) = 1 := by
            have h1 : (((2 * k : ℕ) : ℤ) + (0 : ℤ)) = ((2 * k : ℕ) : ℤ) := by simp
            rw [h1, Int.natAbs_natCast]
            exact Even.neg_one_pow ⟨k, by ring⟩
          rw [hsign, one_smul, ← hwU]
          have hm2 := hmul (2 * k) 0 2 0 (Work.Pi6.cpow w k)
            (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) w
            (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))) (by omega) (by omega)
          have hstep1 : S.mul 2 (((2 * k : ℕ) : ℤ), (0 : ℤ)) (((2 : ℕ) : ℤ), ((0 : ℕ) : ℤ))
              (((2 * k + 2 : ℕ) : ℤ), (0 : ℤ)) (by ext <;> simp)
              ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
                (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))))
              ((e2 2 0 (by omega) (by omega)).inv.hom
                (w ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) =
              (-1 : 𝕜) ^ (0 * 2) •
                (e2 ((2 * k + 2 : ℕ)) ((0 + 0 : ℕ)) (by omega) (by omega)).inv.hom
                  (Work.Pi6.cup 𝕜 B (2 * k) 2 (Work.Pi6.cpow w k) w ⊗ₜ[𝕜]
                    Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 0
                      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))
                      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) := hm2
          have hstep2 : (-1 : 𝕜) ^ (0 * 2) •
                (e2 ((2 * k + 2 : ℕ)) ((0 + 0 : ℕ)) (by omega) (by omega)).inv.hom
                  (Work.Pi6.cup 𝕜 B (2 * k) 2 (Work.Pi6.cpow w k) w ⊗ₜ[𝕜]
                    Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 0
                      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))
                      (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) = 0 := by
            rw [show (-1 : 𝕜) ^ (0 * 2) = 1 from by rw [Nat.zero_mul, pow_zero], one_smul]
            rw [cupU]
            rw [show Work.Pi6.cup 𝕜 B (2 * k) 2 (Work.Pi6.cpow w k) w =
                Work.Pi6.cpow w (k + 1) from rfl]
            rw [hcon, TensorProduct.zero_tmul, map_zero]
          exact hstep1.trans hstep2
        have hdY' : (S.d 2 (((2 * k : ℕ) : ℤ), (1 : ℤ))
            (((2 * k + 2 : ℕ) : ℤ), (0 : ℤ))).hom
            (S.mul 2 (((2 * k : ℕ) : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))
              (((2 * k : ℕ) : ℤ), (1 : ℤ)) hab.symm
              ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
                (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))))
              ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v))) = 0 := hdY
        have hinj := dTwo_inj_p S M h2 h31 (2 * k) (by omega)
        have h0 : (S.d 2 (((2 * k : ℕ) : ℤ), (1 : ℤ))
            (((2 * k + 2 : ℕ) : ℤ), (0 : ℤ))).hom
            (S.mul 2 (((2 * k : ℕ) : ℤ), (0 : ℤ)) ((0 : ℤ), (1 : ℤ))
              (((2 * k : ℕ) : ℤ), (1 : ℤ)) hab.symm
              ((e2 (2 * k) 0 (by omega) (by omega)).inv.hom
                (Work.Pi6.cpow w k ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))))
              ((e2 0 1 (by omega) (by omega)).inv.hom (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] v))) =
            (S.d 2 (((2 * k : ℕ) : ℤ), (1 : ℤ))
              (((2 * k + 2 : ℕ) : ℤ), (0 : ℤ))).hom
              (0 : S.E 2 (((2 * k : ℕ) : ℤ), (1 : ℤ))) := by
          rw [hdY', map_zero]
        exact hYne (hinj h0)
  exact ⟨w, hpow,
    (fun q hq hq' => iso_of_finrank_one_p _ (by rw [hdim q hq, if_pos hq'])),
    (fun q hq hq' => by
      haveI := hBfin q hq
      exact isZero_of_finrank_zero_p (Work.Pi6.Coh 𝕜 B q) (by
        rw [hdim q hq]
        exact ite_eq_right (fun h => (Nat.not_even_iff_odd.mpr hq') h)))⟩

/-- **Finiteness of the integral homology of the path–loop fibration of a `K(ℤ,2)` range model.** -/
theorem fgPathLoop (N : ℕ) (hN : 3 ≤ N) (W : Type) [TopologicalSpace W] (w₀ : W)
    (hW : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N W w₀) :
    (∀ i : ℕ, i ≤ N - 1 → Module.Finite ℤ (Work.PiS.HZ (Work.StemsB.PathSpace W w₀) i)) ∧
      (∀ i : ℕ, i ≤ N - 1 → Module.Finite ℤ
        (Work.PiS.HZ (Work.StemsB.fibre (Work.StemsB.evalOne W w₀) w₀) i)) ∧
      (∀ i : ℕ, i ≤ N - 1 → Module.Finite ℤ (Work.PiS.HZ W i)) := by
  refine ⟨?_, ?_, ?_⟩
  · haveI : ContractibleSpace (Work.StemsB.PathSpace W w₀) :=
      Work.StemsB.contractible_pathSpace W w₀
    intro i hi
    exact Work.EMFG.fgUpTo_of_contractible (Work.StemsB.PathSpace W w₀) (N - 1) i hi
  · intro i hi
    have hloop : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) (N - 1) (Path w₀ w₀)
        (Path.refl w₀) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := ℤ) (m := 2) (M := N) (by norm_num) w₀ hW
    obtain ⟨e⟩ := Work.EMFG.kOneComparison ℤ (N - 1) (Path w₀ w₀) (Path.refl w₀) hloop
      (Work.Serre.Sph 1) Work.Serre.sphOneBase (Work.EMFG.sphOne_isEMSpaceUpTo (N - 1)) i hi
    obtain ⟨eh⟩ := Work.Cohomology.homologyIsoOfHomeomorph
      (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne W w₀) w₀))
      (Y := TopCat.of (Path w₀ w₀)) (Work.StemsB.fibreEvalOneHomeo W w₀) i
    haveI : Module.Finite ℤ ↥(Work.PiS.HZ (Work.Serre.Sph 1) i) :=
      Work.EMFG.fgUpTo_sphOne (N - 1) i hi
    exact Module.Finite.equiv (e.symm ≪≫ eh.symm).toLinearEquiv
  · intro i hi
    have hW' : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1 + 1) W w₀ := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
      exact hW
    exact Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo ℤ 2 (by norm_num) (N - 1) W w₀ hW' i hi

/-- **`H⁰` of a `K(ℤ,2)` range model is `𝕜`.** -/
theorem baseZero (𝕜 : Type) [Field 𝕜] (N : ℕ) (W : Type) [TopologicalSpace W]
    (w₀ : W) (hW : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N W w₀) :
    Nonempty (Work.Pi6.Coh 𝕜 W 0 ≅ ModuleCat.of 𝕜 𝕜) := by
  have hp0 : Subsingleton (HomotopyGroup (Fin 0) W w₀) :=
    hW.2 0 (by omega) (Or.inl (by norm_num))
  haveI hZ : Subsingleton (ZerothHomotopy W) := by
    refine ⟨fun a b => ?_⟩
    have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := W) (x := w₀))
      (Subsingleton.elim ((HomotopyGroup.pi0EquivZerothHomotopy (X := W) (x := w₀)).symm a)
        ((HomotopyGroup.pi0EquivZerothHomotopy (X := W) (x := w₀)).symm b))
    simpa using h1
  haveI : PathConnectedSpace W :=
    pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk w₀⟩, hZ⟩
  exact Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of W)

end KTwoAux

/-- **The mod-`𝕜` cohomology of a range model of `K(ℤ,2)` is that of `ℂP^∞`.** For a field `𝕜` and a range model `W` of `K(ℤ,2)` through `N`, the cohomology `H^{*}(W;𝕜)` has a generator in degree `2` whose powers are non-zero, is one dimensional in even degrees and vanishes in odd degrees, as far as the range allows (`≤ N - 1`).

The proof is the Serre spectral sequence of the path–loop fibration `ΩW → PW → W` (`Work.StemsB.isSerreFibration_evalOne`, `Work.StemsB.contractible_pathSpace`), over the range `N - 1` (so that both `ΩW` — a range model of `K(ℤ,1)` through `N - 1` by `Work.Stems.isEMSpaceUpTo_loop'` — and `W` have finitely generated integral homology through `N - 1`, hence finite dimensional mod-`𝕜` cohomology, by `hfin`). The fibre's mod-`𝕜` cohomology is `𝕜, 𝕜, 0, …` in the range by `hOne`. With the total space contractible, the transgression `d₂ : H^{2k}(W)⊗H¹(ΩW) → H^{2k+2}(W)` is bijective, which gives the dimensions; the powers are non-zero because for a generator `v` of `H¹(ΩW)` the class `v ⊗ w^k ∈ E₂^{2k,1}` has `d₂(v ⊗ w^k) = ± w^{k+1}` and `E_∞^{2k,1} = 0` (the total space is acyclic in total degree `2k+1`), so `d₂` is injective on that line. The hypotheses `hOne` and `hfin` are the two externally proved inputs (`Work.Pi6.EMODD.kOneMod` and `Work.Pi6.EMODD.finDimField`); `MSSHolds` supplies the spectral sequence and the toolkit of `Submission/Work/Pi6/EMM2/SSKit.lean` the page algebra. -/
theorem kTwoRing (𝕜 : Type) [Field 𝕜] (hM : Work.Pi6.MSSHolds)
    (hOne : ∀ (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
      Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N W w₀ →
      (Nonempty (Work.Pi6.Coh 𝕜 W 0 ≅ ModuleCat.of 𝕜 𝕜)) ∧
      (Nonempty (Work.Pi6.Coh 𝕜 W 1 ≅ ModuleCat.of 𝕜 𝕜)) ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ N → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 W q)))
    (hfin : ∀ (A : Type) [TopologicalSpace A] (N : ℕ),
      (∀ i : ℕ, i ≤ N → Module.Finite ℤ (Work.PiS.HZ A i)) →
      ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 A q))
    (N : ℕ) (hN : 3 ≤ N) (W : Type) [TopologicalSpace W] (w₀ : W)
    (hW : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N W w₀) :
    ∃ w : Work.Pi6.Coh 𝕜 W 2,
      (∀ k : ℕ, 2 * k ≤ N - 1 → Work.Pi6.cpow w k ≠ 0) ∧
      (∀ q : ℕ, q ≤ N - 1 → Even q → Nonempty (Work.Pi6.Coh 𝕜 W q ≅ ModuleCat.of 𝕜 𝕜)) ∧
      (∀ q : ℕ, q ≤ N - 1 → Odd q → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 W q)) := by
  obtain ⟨hFGtot, hFGfib, hFGbase⟩ := KTwoAux.fgPathLoop N hN W w₀ hW
  haveI hContr : ContractibleSpace (Work.StemsB.PathSpace W w₀) :=
    Work.StemsB.contractible_pathSpace W w₀
  -- the loop space is a range model of `K(ℤ,1)` through `N - 1`
  have hloop : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) (N - 1) (Path w₀ w₀)
      (Path.refl w₀) :=
    Work.Stems.isEMSpaceUpTo_loop' (A := ℤ) (m := 2) (M := N) (by norm_num) w₀ hW
  obtain ⟨hP0, hP1, hPq⟩ := hOne (N - 1) (Path w₀ w₀) (Path.refl w₀) hloop
  have hhomeo : ∀ q : ℕ, Work.Pi6.Coh 𝕜 (Path w₀ w₀) q ≅
      Work.Pi6.Coh 𝕜 (Work.StemsB.fibre (Work.StemsB.evalOne W w₀) w₀) q := fun q =>
    Work.StemsB.cohomologyIsoOfHomeomorph 𝕜 (Work.StemsB.fibreEvalOneHomeo W w₀) q
  -- the Serre spectral sequence of the path–loop fibration
  obtain ⟨S, hS⟩ := hM 𝕜 (Work.StemsB.PathSpace W w₀) W (Work.StemsB.evalOne W w₀)
    (Work.StemsB.constPath W w₀) (N - 1)
    (Work.StemsB.isSerreFibration_evalOne W w₀)
    ⟨hW.2 0 (by omega) (Or.inl (by norm_num)), hW.2 1 (by omega) (Or.inl (by norm_num))⟩
    (fun q hq => hfin (Work.StemsB.fibre (Work.StemsB.evalOne W w₀) w₀) (N - 1)
      (fun i hi => hFGfib i hi) q hq)
    (fun s hs => hfin W (N - 1) (fun i hi => hFGbase i hi) s hs)
  refine KTwoAux.twoRow_main_p (Work.StemsB.evalOne W w₀) (Work.StemsB.constPath W w₀)
    (N - 1) (by omega) S hS ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨(hhomeo 0).symm ≪≫ hP0.some⟩
  · exact ⟨(hhomeo 1).symm ≪≫ hP1.some⟩
  · intro q hq1 hq2
    exact IsZero.of_iso (hPq q hq1 hq2) (hhomeo q).symm
  · exact KTwoAux.baseZero 𝕜 N W w₀ hW
  · intro s hs
    exact hfin W (N - 1) (fun i hi => hFGbase i hi) s hs
  · intro n hn1 hn2
    haveI : ContractibleSpace (TopCat.of (Work.StemsB.PathSpace W w₀)) := hContr
    have h := Work.Cohomology.contractible 𝕜 (TopCat.of (Work.StemsB.PathSpace W w₀)) (n - 1)
    rw [Nat.sub_add_cancel hn1] at h
    exact ModuleCat.subsingleton_of_isZero h
  · haveI : PathConnectedSpace (Work.StemsB.PathSpace W w₀) := inferInstance
    exact Work.Cohomology.singularCohomology_zero 𝕜
      (TopCat.of (Work.StemsB.PathSpace W w₀))

end

end Work.Pi6.EMODD
