import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.GenericKernelReduction.algEquiv_eq_one_of_fixes_iSup
import Submission.Work.GenericKernelReduction.canonical_of_splitEmbeddingSolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical
open Work.FieldTheory

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **Combination of solutions with pairwise coprime kernels.**  If a family of split embedding
problems over `ℚ` with kernels `A i` (pairwise coprime orders) all have proper solutions inside
`AlgebraicClosure ℚ` with the *canonical* `↥L`-algebra structure on the solution field
(`CanonicalSplitEmbeddingSolvedInClosure`), then so does the split embedding problem with kernel
`∀ i, A i` and the product action `piAction φ`. -/
theorem canonical_pi {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (hcop : Pairwise fun i j => Nat.Coprime (Nat.card (A i)) (Nat.card (A j)))
    (φ : ∀ i, (L ≃ₐ[ℚ] L) →* MulAut (A i))
    (h : ∀ i, CanonicalSplitEmbeddingSolvedInClosure L (A i) (φ i)) :
    CanonicalSplitEmbeddingSolvedInClosure L (∀ i, A i) (piAction φ) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- ## The degenerate case of an empty index type
    haveI : IsEmpty ι := hι
    have hbij : Function.Bijective (SemidirectProduct.rightHom :
        (∀ i, A i) ⋊[piAction φ] (L ≃ₐ[ℚ] L) → (L ≃ₐ[ℚ] L)) := by
      refine ⟨fun x y hxy => ?_, SemidirectProduct.rightHom_surjective⟩
      apply SemidirectProduct.ext
      · exact Subsingleton.elim _ _
      · exact hxy
    refine ⟨L, le_rfl, inferInstance, inferInstance, inferInstance, ?_, inferInstance,
      inferInstance, fun y => rfl, MulEquiv.ofBijective SemidirectProduct.rightHom hbij, ?_⟩
    · -- `IsScalarTower ℚ ↥L ↥L`
      exact IsScalarTower.of_algebraMap_eq fun q => by simp
    · intro g x
      simp
  · -- ## The main case
    haveI : Nonempty ι := hι
    choose M hLM hfd hgal alg hST hfdL hgalL coef e he using h
    haveI hfdpi : ∀ i, FiniteDimensional ℚ (M i) := hfd
    haveI hgalpi : ∀ i, IsGalois ℚ (M i) := hgal
    let Ms := ⨆ i, M i
    have hle : ∀ i, M i ≤ Ms := fun i => le_iSup (fun j => M j) i
    have hLMs : L ≤ Ms := (hLM (Classical.arbitrary ι)).trans (hle _)
    haveI hfdMs : FiniteDimensional ℚ Ms :=
      IntermediateField.finiteDimensional_iSup_of_finite (t := M)
    haveI hgalMs : IsGalois ℚ Ms :=
      isGalois_iff.mpr ⟨inferInstance,
        IntermediateField.normal_iSup ℚ (AlgebraicClosure ℚ) M (h := fun i => (hgal i).to_normal)⟩
    -- the canonical `↥L`-algebra structure on `↥Ms`
    letI algMs : Algebra ↥L ↥Ms := (IntermediateField.inclusion hLMs).toRingHom.toAlgebra
    haveI hSTMs : IsScalarTower ℚ ↥L ↥Ms :=
      IsScalarTower.of_algebraMap_eq fun q => by apply Subtype.ext; rfl
    haveI hfdLMs : FiniteDimensional ↥L ↥Ms :=
      Module.Finite.of_restrictScalars_finite ℚ ↥L ↥Ms
    haveI hgalLMs : IsGalois ↥L ↥Ms :=
      isGalois_iff.mpr ⟨Algebra.isSeparable_tower_top_of_isSeparable ℚ ↥L ↥Ms,
        Normal.tower_top_of_normal ℚ ↥L ↥Ms⟩
    have coefMs : ∀ y : ↥L, (algebraMap ↥L ↥Ms y : AlgebraicClosure ℚ) = y := fun y => rfl
    -- ## Restriction maps
    let As : ∀ i, IntermediateField ℚ ↥Ms := fun i => (M i).restrict (hle i)
    have hnormM : ∀ i, Normal ℚ (M i) := fun i => (hgal i).to_normal
    have hnormAs : ∀ i, Normal ℚ ↥(As i) := fun i =>
      Normal.of_algEquiv (IntermediateField.restrictAlgEquiv (hle i)) (h := hnormM i)
    let restr : ∀ i, (↥Ms ≃ₐ[ℚ] ↥Ms) →* (↥(M i) ≃ₐ[ℚ] ↥(M i)) := fun i =>
      (algEquivAutMulEquiv (IntermediateField.restrictAlgEquiv (hle i))).toMonoidHom.comp
        (@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥(As i) _ _ _ _ (hnormAs i))
    have hrestr : ∀ (i : ι) (σ : ↥Ms ≃ₐ[ℚ] ↥Ms) (y : ↥(M i)),
        IntermediateField.inclusion (hle i) ((restr i σ) y)
          = σ (IntermediateField.inclusion (hle i) y) := by
      intro i σ y
      have h1 : (restr i σ) y = (IntermediateField.restrictAlgEquiv (hle i)).symm
          ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥(As i) _ _ _ _ (hnormAs i)) σ
            ((IntermediateField.restrictAlgEquiv (hle i)) y)) := rfl
      have h2 : IntermediateField.inclusion (hle i)
          ((IntermediateField.restrictAlgEquiv (hle i)).symm
            ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥(As i) _ _ _ _ (hnormAs i)) σ
              ((IntermediateField.restrictAlgEquiv (hle i)) y)))
          = ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥(As i) _ _ _ _ (hnormAs i)) σ
              ((IntermediateField.restrictAlgEquiv (hle i)) y)) := by
        apply Subtype.ext
        exact congr_arg (fun z : ↥(As i) => (z : AlgebraicClosure ℚ))
          (AlgEquiv.apply_symm_apply (IntermediateField.restrictAlgEquiv (hle i))
            ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥(As i) _ _ _ _ (hnormAs i)) σ
              ((IntermediateField.restrictAlgEquiv (hle i)) y)))
      rw [h1, h2]
      have h3 : (((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥(As i) _ _ _ _ (hnormAs i)) σ)
          ((IntermediateField.restrictAlgEquiv (hle i)) y) : ↥Ms)
          = σ ((((IntermediateField.restrictAlgEquiv (hle i)) y) : ↥Ms)) :=
        @AlgEquiv.restrictNormalHom_apply ℚ _ ↥Ms _ _ (As i) (hnormAs i) σ
          ((IntermediateField.restrictAlgEquiv (hle i)) y)
      rw [h3]
      exact congrArg σ (Subtype.ext rfl)
    -- the restriction to `L`
    let NL : IntermediateField ℚ ↥Ms := L.restrict hLMs
    have hnormNL : Normal ℚ ↥NL :=
      Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hLMs)
        (h := (inferInstance : Normal ℚ L))
    let Lpart : (↥Ms ≃ₐ[ℚ] ↥Ms) →* (↥L ≃ₐ[ℚ] ↥L) :=
      (algEquivAutMulEquiv (IntermediateField.restrictAlgEquiv hLMs)).toMonoidHom.comp
        (@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥NL _ _ _ _ hnormNL)
    have hLpart : ∀ (σ : ↥Ms ≃ₐ[ℚ] ↥Ms) (x : ↥L),
        IntermediateField.inclusion hLMs ((Lpart σ) x)
          = σ (IntermediateField.inclusion hLMs x) := by
      intro σ x
      have h1 : (Lpart σ) x = (IntermediateField.restrictAlgEquiv hLMs).symm
          ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥NL _ _ _ _ hnormNL) σ
            ((IntermediateField.restrictAlgEquiv hLMs) x)) := rfl
      have h2 : IntermediateField.inclusion hLMs
          ((IntermediateField.restrictAlgEquiv hLMs).symm
            ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥NL _ _ _ _ hnormNL) σ
              ((IntermediateField.restrictAlgEquiv hLMs) x)))
          = ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥NL _ _ _ _ hnormNL) σ
              ((IntermediateField.restrictAlgEquiv hLMs) x)) := by
        apply Subtype.ext
        exact congr_arg (fun z : ↥NL => (z : AlgebraicClosure ℚ))
          (AlgEquiv.apply_symm_apply (IntermediateField.restrictAlgEquiv hLMs)
            ((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥NL _ _ _ _ hnormNL) σ
              ((IntermediateField.restrictAlgEquiv hLMs) x)))
      rw [h1, h2]
      have h3 : (((@AlgEquiv.restrictNormalHom ℚ _ ↥Ms _ _ ↥NL _ _ _ _ hnormNL) σ)
          ((IntermediateField.restrictAlgEquiv hLMs) x) : ↥Ms)
          = σ ((((IntermediateField.restrictAlgEquiv hLMs) x) : ↥Ms)) :=
        @AlgEquiv.restrictNormalHom_apply ℚ _ ↥Ms _ _ NL hnormNL σ
          ((IntermediateField.restrictAlgEquiv hLMs) x)
      rw [h3]
      exact congrArg σ (Subtype.ext rfl)
    -- ## The "restriction" homomorphism `rho`
    let rho : (↥Ms ≃ₐ[ℚ] ↥Ms) →* (∀ i, A i ⋊[φ i] (↥L ≃ₐ[ℚ] ↥L)) :=
      MonoidHom.pi fun i => (e i).symm.toMonoidHom.comp (restr i)
    have hrho_apply : ∀ (σ : ↥Ms ≃ₐ[ℚ] ↥Ms) (i : ι), rho σ i = (e i).symm (restr i σ) :=
      fun σ i => rfl
    -- ## The key compatibility of the `G`-parts
    have key : ∀ (σ : ↥Ms ≃ₐ[ℚ] ↥Ms) (i : ι),
        SemidirectProduct.rightHom (rho σ i) = Lpart σ := by
      intro σ i
      rw [hrho_apply]
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      have hhe : (restr i σ) (algebraMap ↥L ↥(M i) x)
          = algebraMap ↥L ↥(M i)
              (SemidirectProduct.rightHom ((e i).symm (restr i σ)) x) := by
        have h := he i ((e i).symm (restr i σ)) x
        rwa [MulEquiv.apply_symm_apply] at h
      have hincl : IntermediateField.inclusion (hle i) (algebraMap ↥L ↥(M i) x)
          = IntermediateField.inclusion hLMs x := by
        apply Subtype.ext
        rw [show ((IntermediateField.inclusion hLMs x : ↥Ms) : AlgebraicClosure ℚ) = x from rfl]
        exact coef i x
      have h3 := hrestr i σ (algebraMap ↥L ↥(M i) x)
      rw [hincl] at h3
      have h4 := hLpart σ x
      rw [hhe] at h3
      have h5 : IntermediateField.inclusion (hle i)
            (algebraMap ↥L ↥(M i) (SemidirectProduct.rightHom ((e i).symm (restr i σ)) x))
          = IntermediateField.inclusion hLMs ((Lpart σ) x) := h3.trans h4.symm
      have h6 := congr_arg (fun z : ↥Ms => (z : AlgebraicClosure ℚ)) h5
      simpa only [IntermediateField.coe_inclusion, coef i] using h6
    -- ## The homomorphism `Phi`
    let Phi : (↥Ms ≃ₐ[ℚ] ↥Ms) →* ((∀ i, A i) ⋊[piAction φ] (↥L ≃ₐ[ℚ] ↥L)) :=
      MonoidHom.mk' (fun σ => ⟨fun i => (rho σ i).left, Lpart σ⟩) (by
        intro σ τ
        apply SemidirectProduct.ext
        · change (fun i => (rho (σ * τ) i).left)
            = (fun i => (rho σ i).left) * (piAction φ (Lpart σ)) (fun i => (rho τ i).left)
          funext i
          show (rho (σ * τ) i).left = (rho σ i).left * (φ i (Lpart σ)) ((rho τ i).left)
          rw [show rho (σ * τ) i = rho σ i * rho τ i from by rw [map_mul]; rfl]
          rw [SemidirectProduct.mul_left]
          rw [show SemidirectProduct.right (rho σ i) = Lpart σ from key σ i]
        · change Lpart (σ * τ) = Lpart σ * Lpart τ
          rw [map_mul])
    have hPhi_apply : ∀ σ : ↥Ms ≃ₐ[ℚ] ↥Ms, Phi σ = ⟨fun i => (rho σ i).left, Lpart σ⟩ :=
      fun σ => rfl
    -- ## Injectivity of `Phi`
    have hPhi_inj : Function.Injective Phi := by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      have hright : Lpart σ = 1 := by
        have h := congr_arg SemidirectProduct.right hσ
        rw [hPhi_apply σ] at h
        simpa using h
      have hleft : ∀ i, (rho σ i).left = 1 := by
        intro i
        have h := congr_arg SemidirectProduct.left hσ
        rw [hPhi_apply σ] at h
        simpa using congr_fun h i
      have hrho : ∀ i, rho σ i = 1 := by
        intro i
        apply SemidirectProduct.ext
        · exact hleft i
        · show SemidirectProduct.right (rho σ i) = 1
          rw [show SemidirectProduct.right (rho σ i) = Lpart σ from key σ i, hright]
      have hre : ∀ i, restr i σ = 1 := by
        intro i
        have h := congr_arg (fun x => e i x) (hrho i)
        rw [show rho σ i = (e i).symm (restr i σ) from hrho_apply σ i] at h
        simpa using h
      have hfix : ∀ i (y : ↥(M i)),
          σ ⟨(y : AlgebraicClosure ℚ), hle i y.2⟩
            = ⟨(y : AlgebraicClosure ℚ), hle i y.2⟩ := by
        intro i y
        have h1 : (restr i σ) y = y := by
          have h := congr_arg (fun f => f y) (hre i)
          simpa using h
        have h2 := hrestr i σ y
        rw [h1] at h2
        exact h2.symm
      exact algEquiv_eq_one_of_fixes_iSup M σ hfix
    -- ## The cardinality bound
    haveI : Finite ((∀ i, A i) ⋊[piAction φ] (↥L ≃ₐ[ℚ] ↥L)) :=
      Finite.of_equiv ((∀ i, A i) × (↥L ≃ₐ[ℚ] ↥L))
        (SemidirectProduct.equivProd (N := ∀ i, A i) (G := ↥L ≃ₐ[ℚ] ↥L) (φ := piAction φ)).symm
    haveI : Module.Free ↥L ↥Ms := Module.Free.of_divisionRing _ _
    have hcard : Nat.card ((∀ i, A i) ⋊[piAction φ] (↥L ≃ₐ[ℚ] ↥L))
        ≤ Nat.card (↥Ms ≃ₐ[ℚ] ↥Ms) := by
      rw [Nat.card_congr (SemidirectProduct.equivProd (φ := piAction φ)),
        Nat.card_prod, Nat.card_pi,
        IsGalois.card_aut_eq_finrank ℚ ↥L, IsGalois.card_aut_eq_finrank ℚ ↥Ms,
        ← Module.finrank_mul_finrank ℚ ↥L ↥Ms, mul_comm (Module.finrank ℚ ↥L)]
      refine Nat.mul_le_mul_right _ (Nat.le_of_dvd (Module.finrank_pos (R := ↥L) (M := ↥Ms)) ?_)
      have hB : (0 : ℕ) < Module.finrank ℚ ↥L := Module.finrank_pos (R := ℚ) (M := ↥L)
      have hdvd : ∀ i, Nat.card (A i) ∣ Module.finrank ↥L ↥Ms := by
        intro i
        have hsurj : Function.Surjective (restr i) :=
          (algEquivAutMulEquiv (IntermediateField.restrictAlgEquiv (hle i))).surjective.comp
            (@AlgEquiv.restrictNormalHom_surjective ℚ _ ↥(As i) _ _ ↥Ms _ _ _ _
              (hnormAs i) (inferInstance))
        have h1 : Nat.card (↥(M i) ≃ₐ[ℚ] ↥(M i)) ∣ Nat.card (↥Ms ≃ₐ[ℚ] ↥Ms) :=
          Subgroup.card_dvd_of_surjective (f := restr i) hsurj
        rw [IsGalois.card_aut_eq_finrank ℚ ↥(M i), IsGalois.card_aut_eq_finrank ℚ ↥Ms] at h1
        have h2 : Module.finrank ℚ ↥(M i) = Nat.card (A i) * Module.finrank ℚ ↥L := by
          rw [← IsGalois.card_aut_eq_finrank ℚ ↥(M i), ← Nat.card_congr (e i).toEquiv,
            Nat.card_congr (SemidirectProduct.equivProd (φ := φ i)), Nat.card_prod,
            IsGalois.card_aut_eq_finrank ℚ ↥L]
        have h3 : Module.finrank ℚ ↥Ms = Module.finrank ↥L ↥Ms * Module.finrank ℚ ↥L := by
          rw [← Module.finrank_mul_finrank ℚ ↥L ↥Ms, mul_comm (Module.finrank ↥L ↥Ms)]
        rw [h2, h3] at h1
        exact Nat.dvd_of_mul_dvd_mul_right hB h1
      have hcop' : Pairwise (Function.onFun IsCoprime fun i => (Nat.card (A i) : ℤ)) :=
        fun i j hij => (hcop hij).isCoprime
      have key2 := Fintype.prod_dvd_of_coprime hcop'
        (fun i => Int.natCast_dvd_natCast.mpr (hdvd i))
      rw [← Nat.cast_prod] at key2
      exact Int.natCast_dvd_natCast.mp key2
    have hPhi_bij : Function.Bijective Phi := hPhi_inj.bijective_of_nat_card_le hcard
    refine ⟨Ms, hLMs, hfdMs, hgalMs, algMs, hSTMs, hfdLMs, hgalLMs, coefMs,
      (MulEquiv.ofBijective Phi hPhi_bij).symm, ?_⟩
    intro g x
    have h1 : Lpart ((MulEquiv.ofBijective Phi hPhi_bij).symm g)
        = SemidirectProduct.rightHom g := by
      have h := MulEquiv.apply_symm_apply (MulEquiv.ofBijective Phi hPhi_bij) g
      have h' : Phi ((MulEquiv.ofBijective Phi hPhi_bij).symm g) = g := h
      have h2 := congr_arg SemidirectProduct.right h'
      rw [hPhi_apply] at h2
      simpa using h2
    have h2 := hLpart ((MulEquiv.ofBijective Phi hPhi_bij).symm g) x
    rw [h1] at h2
    exact h2.symm

/-- **Combination of solutions with pairwise coprime kernels.**  This is
`Work.GenericKernelReduction.splitEmbeddingSolvedInClosure_pi`, proved by first pushing every
individual solution to the canonical `↥L`-algebra structure
(`Work.GenericKernelReduction.canonical_of_splitEmbeddingSolvable`) and then combining the
canonical solutions (`Work.GenericKernelReduction.canonical_pi`). -/
theorem splitEmbeddingSolvedInClosure_pi {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (hcop : Pairwise fun i j => Nat.Coprime (Nat.card (A i)) (Nat.card (A j)))
    (φ : ∀ i, (L ≃ₐ[ℚ] L) →* MulAut (A i))
    (h : ∀ i, Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L (A i) (φ i)) :
    Work.GenericKernelReduction.SplitEmbeddingSolvedInClosure L (∀ i, A i)
      (Work.GenericKernelReduction.piAction φ) :=
  splitEmbeddingSolvedInClosure_of_canonical (canonical_pi A hcop φ fun i =>
    canonical_of_splitEmbeddingSolvable (splitEmbeddingSolvable_of_inClosure (h i)))

end Work.GenericKernelReduction
