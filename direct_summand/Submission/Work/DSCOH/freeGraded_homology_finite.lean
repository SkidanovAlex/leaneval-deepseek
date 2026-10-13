import Mathlib
import Submission.Work.DSCOH.ChartFree
import Submission.Work.DSCOH.ProdLocIsoBase
import Submission.Work.DSCOH.prodLocIso_resAt
import Submission.Work.DSCOH.map_prodLocIso_degZero
import Submission.Work.DSCOH.homologyEquivKerQuot
import Submission.Work.DSCOH.finite_quot_of_data

open MvPolynomial CategoryTheory

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## Localizing a finite product of copies of the polynomial ring

The vocabulary below (`prodLocIso` for the localization of a finite product of copies of the
polynomial ring, its computation rules, and the product `degZeroProd` of the degree-zero parts of
the shifts) lives in `Submission.Work.DSCOH.ProdLocIsoBase`, imported above. -/

/-! ## The product of the degree-zero parts as a product of modules -/

noncomputable def degZeroProdEquiv {r : ℕ} (d : Fin r → ℕ) (S : Finset (Fin n)) :
    degZeroProd (A := A) (n := n) d S ≃ₗ[A]
      (∀ j : Fin r, degZero (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) S) where
  toFun x := fun j => ⟨x.1 j, (mem_degZeroProd.mp x.2) j⟩
  invFun y := ⟨fun j => (y j).1, by
    rw [mem_degZeroProd]
    exact fun j => (y j).2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := funext fun j => Subtype.ext rfl
  map_add' x y := funext fun j => Subtype.ext rfl
  map_smul' a x := funext fun j => Subtype.ext rfl

noncomputable def degZeroProdProj {r : ℕ} (d : Fin r → ℕ) (S : Finset (Fin n)) (j : Fin r) :
    degZeroProd (A := A) (n := n) d S →ₗ[A]
      degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) S :=
  (LinearMap.proj (R := A)
    (φ := fun j : Fin r => degZero (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) (d j)) S) j).comp
    (degZeroProdEquiv (A := A) (n := n) d S).toLinearMap

/-! ## The degree-zero part of the free module -/

noncomputable def degZeroIso {r : ℕ} (d : Fin r → ℕ) (S : Finset (Fin n)) :
    degZero (A := A) (n := n) (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d) S
      ≃ₗ[A] degZeroProd (A := A) (n := n) d S where
  toFun y := ⟨(prodLocIso (A := A) (n := n) S r).restrictScalars A y.1, by
    rw [← map_prodLocIso_degZero (A := A) (n := n) d S]
    exact Submodule.mem_map_of_mem y.2⟩
  invFun z := ⟨((prodLocIso (A := A) (n := n) S r).restrictScalars A).symm z.1, by
    have hz : z.1 ∈ Submodule.map
        ((prodLocIso (A := A) (n := n) S r).restrictScalars A).toLinearMap
        (degZero (A := A) (n := n) (M := Fin r → Poly A n)
          (freeGraded (A := A) (n := n) d) S) := by
      rw [map_prodLocIso_degZero (A := A) (n := n) d S]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hz
    have hys : ((prodLocIso (A := A) (n := n) S r).restrictScalars A).symm z.1 = y := by
      rw [← hyz]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hys]
    exact hy⟩
  left_inv y := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv z := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  map_add' y y' := Subtype.ext (by simp)
  map_smul' a y := Subtype.ext (by simp)

noncomputable def dZiso {r : ℕ} (d : Fin r → ℕ) (S : Finset (Fin n)) (j : Fin r) :
    degZero (A := A) (n := n) (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d) S
      →ₗ[A] degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) S :=
  (degZeroProdProj (A := A) (n := n) d S j).comp
    (degZeroIso (A := A) (n := n) d S).toLinearMap

/-! ## The transition maps on the degree-zero parts -/

noncomputable def resAtDZ {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {S T : Finset (Fin n)} (h : S ⊆ T) : degZero (A := A) (M := M) ℳ S →ₗ[A]
      degZero (A := A) (M := M) ℳ T :=
  degPartRestrict (A := A) (M := M) ℳ (resAt (A := A) (M := M) h)
    (fun x hx => resAt_degZero (A := A) (n := n) (M := M) (ℳ := ℳ) h x hx)

lemma resAtDZ_apply {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {S T : Finset (Fin n)} (h : S ⊆ T) (x : degZero (A := A) (M := M) ℳ S) :
    (resAtDZ (A := A) (n := n) ℳ h x : locAt (A := A) (M := M) T)
      = resAt (A := A) (M := M) h x.1 := rfl

/-! ## The naturality of the degree-zero iso in the chart -/

lemma dZiso_resAtDZ {r : ℕ} (d : Fin r → ℕ) {S T : Finset (Fin n)}
    (h : S ⊆ T) (j : Fin r)
    (y : degZero (A := A) (n := n) (M := Fin r → Poly A n)
      (freeGraded (A := A) (n := n) d) S) :
    dZiso (A := A) (n := n) d T j
        (resAtDZ (A := A) (n := n) (freeGraded (A := A) (n := n) d) h y)
      = resAtDZ (A := A) (n := n) (shift (A := A) (n := n) (d j)) h
          (dZiso (A := A) (n := n) d S j y) := by
  apply Subtype.ext
  show (((prodLocIso (A := A) (n := n) T r)
      (resAt (A := A) (n := n) (M := Fin r → Poly A n) h y.1))) j
      = resAt (A := A) (n := n) (M := Poly A n) h
          (((prodLocIso (A := A) (n := n) S r) y.1) j)
  exact congrFun (prodLocIso_resAt (A := A) (n := n) h y.1) j

noncomputable def piCommLinearEquiv (R : Type*) [Semiring R] {ι κ : Type*}
    (X : ι → κ → Type*) [∀ i k, AddCommMonoid (X i k)] [∀ i k, Module R (X i k)] :
    (∀ i, ∀ k, X i k) ≃ₗ[R] (∀ k, ∀ i, X i k) where
  toFun f := fun k i => f i k
  invFun f := fun i k => f k i
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := rfl

noncomputable def PhiLE {r : ℕ} (d : Fin r → ℕ) (q : ℕ) :
    CechTerm (A := A) (n := n) (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d) q
      ≃ₗ[A] (∀ j : Fin r, CechTerm (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) q) :=
  (LinearEquiv.piCongrRight (fun S' : {S : Finset (Fin n) // S.card = q + 1} =>
      (degZeroIso (A := A) (n := n) d S'.1) ≪≫ₗ (degZeroProdEquiv (A := A) (n := n) d S'.1))) ≪≫ₗ
    piCommLinearEquiv A (fun (S' : {S : Finset (Fin n) // S.card = q + 1}) (j : Fin r) =>
      degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) S'.1)

lemma PhiLE_apply {r : ℕ} (d : Fin r → ℕ) (q : ℕ)
    (x : CechTerm (A := A) (n := n) (M := Fin r → Poly A n)
      (freeGraded (A := A) (n := n) d) q)
    (j : Fin r) (S' : {S : Finset (Fin n) // S.card = q + 1}) :
    PhiLE (A := A) (n := n) d q x j S' = dZiso (A := A) (n := n) d S'.1 j (x S') := rfl

lemma cechDiffComp_eq_sum {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) (T : {S : Finset (Fin n) // S.card = q + 1 + 1}) :
    cechDiffComp (A := A) (n := n) (M := M) ℳ q T =
      ∑ i ∈ T.1.attach, (-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card •
        (resAtDZ (A := A) (n := n) ℳ (Finset.erase_subset i.1 T.1)).comp
          (LinearMap.proj (R := A)
            (φ := fun S : {S : Finset (Fin n) // S.card = q + 1} => degZero (A := A) (M := M) ℳ S.1)
            ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩) := rfl

lemma cechDiffComp_apply {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) (T : {S : Finset (Fin n) // S.card = q + 1 + 1})
    (x : CechTerm (A := A) (n := n) (M := M) ℳ q) :
    cechDiffComp (A := A) (n := n) (M := M) ℳ q T x =
      ∑ i ∈ T.1.attach, (-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card •
        resAtDZ (A := A) (n := n) ℳ (Finset.erase_subset i.1 T.1)
          (x ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩) := by
  rw [cechDiffComp_eq_sum (A := A) (n := n) ℳ q T, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem PhiLE_cechDiff {r : ℕ} (d : Fin r → ℕ) (q : ℕ) :
    (PhiLE (A := A) (n := n) d (q + 1)).toLinearMap.comp
        (cechDiff (A := A) (n := n) (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d) q)
      = (LinearMap.pi (fun j : Fin r =>
          (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) q).comp
            (LinearMap.proj (R := A) (φ := fun j : Fin r =>
              CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) q) j))).comp
        (PhiLE (A := A) (n := n) d q).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  refine funext fun j => ?_
  refine funext fun T => ?_
  show dZiso (A := A) (n := n) d T.1 j
      ((cechDiff (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) q) x T)
    = (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) q)
        ((PhiLE (A := A) (n := n) d q) x j) T
  simp only [cechDiff, LinearMap.pi_apply]
  rw [cechDiffComp_apply (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d) q T x,
    cechDiffComp_apply (M := Poly A n) (shift (A := A) (n := n) (d j)) q T
      ((PhiLE (A := A) (n := n) d q) x j)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_zsmul]
  rw [PhiLE_apply]
  exact congrArg (fun z => (-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card • z)
    (dZiso_resAtDZ (A := A) (n := n) d (Finset.erase_subset i.1 T.1) j
      (x ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩))


/-! ## Differentials of the chart Čech complex -/

lemma chartCech_d_next {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (q : ℕ) :
    (((chartCech (A := A) (n := n) (M := M) ℳ).d q (q + 1)).hom)
      = cechDiff (A := A) (n := n) (M := M) ℳ q := by
  simp only [chartCech, chartCechOf, CochainComplex.of_d]
  rfl

lemma chartCech_d_zero {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {i j : ℕ} (h : i + 1 ≠ j) :
    (((chartCech (A := A) (n := n) (M := M) ℳ).d i j).hom) = 0 := by
  rw [chartCech, chartCechOf]
  simp only [CochainComplex.of.d, dif_neg h, ModuleCat.hom_zero]

lemma PhiLE_cechDiff_apply {r : ℕ} (d : Fin r → ℕ) (q : ℕ)
    (x : CechTerm (A := A) (n := n) (M := Fin r → Poly A n)
      (freeGraded (A := A) (n := n) d) q) (j : Fin r) :
    (PhiLE (A := A) (n := n) d (q + 1)
        (cechDiff (A := A) (n := n) (M := Fin r → Poly A n)
          (freeGraded (A := A) (n := n) d) q x)) j
      = cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) q
          ((PhiLE (A := A) (n := n) d q) x j) := by
  have h := LinearMap.congr_fun (PhiLE_cechDiff (A := A) (n := n) d q) x
  have h2 := congrFun h j
  simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply] at h2
  exact h2

lemma mem_ker_iff_PhiLE_mem {r : ℕ} (d : Fin r → ℕ) (q : ℕ)
    (x : CechTerm (A := A) (n := n) (M := Fin r → Poly A n)
      (freeGraded (A := A) (n := n) d) q) :
    x ∈ LinearMap.ker (cechDiff (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) q) ↔
      PhiLE (A := A) (n := n) d q x ∈ Submodule.pi Set.univ
        (fun j : Fin r => LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
          (shift (A := A) (n := n) (d j)) q)) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    rw [Submodule.mem_pi]
    intro j _
    rw [LinearMap.mem_ker]
    rw [← PhiLE_cechDiff_apply (A := A) (n := n) d q x j, hx]
    exact congrFun (LinearEquiv.map_zero (PhiLE (A := A) (n := n) d (q + 1))) j
  · intro hx
    rw [← (PhiLE (A := A) (n := n) d (q + 1)).map_eq_zero_iff]
    funext j
    rw [PhiLE_cechDiff_apply (A := A) (n := n) d q x j, Pi.zero_apply]
    exact LinearMap.mem_ker.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))

theorem fghf_aux {A : Type*} [CommRing A] {n : ℕ}
    (hshift : ∀ (d q : ℕ), Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology q))
    (r : ℕ) (d : Fin r → ℕ) (q : ℕ) :
    Module.Finite A ((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
      (freeGraded (A := A) (n := n) d)).homology q) := by
  classical
  rcases q with _ | q'
  · -- q = 0
    set K : Submodule A ↥((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).X 0) :=
      LinearMap.ker (((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).d 0 (0 + 1)).hom) with hK
    set I : Submodule A ↥((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).X 0) :=
      LinearMap.range (((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).d (0 - 1) 0).hom) with hI
    set Kj : (j : Fin r) → Submodule A ↥((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).X 0) :=
      fun j => LinearMap.ker (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d 0 (0 + 1)).hom) with hKj
    set Ij : (j : Fin r) → Submodule A ↥((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).X 0) :=
      fun j => LinearMap.range (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d (0 - 1) 0).hom) with hIj
    have hK_eq : K = LinearMap.ker (cechDiff (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) 0) := by
      rw [hK, chartCech_d_next (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) 0]
      rfl
    have hKj_eq : Kj = fun j => LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) 0) := by
      funext j
      show LinearMap.ker (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d 0 (0 + 1)).hom) = _
      rw [chartCech_d_next (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) 0]
      rfl
    have hIz : I = ⊥ := by
      rw [hI, chartCech_d_zero (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) (i := 0 - 1) (j := 0) (by omega),
        LinearMap.range_zero]
    have hIjz : Ij = fun _ => ⊥ := by
      funext j
      show LinearMap.range (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d (0 - 1) 0).hom) = ⊥
      rw [chartCech_d_zero (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) (i := 0 - 1) (j := 0) (by omega),
        LinearMap.range_zero]
    have hKiff : ∀ x, x ∈ K ↔ (PhiLE (A := A) (n := n) d 0) x ∈ Submodule.pi Set.univ Kj := by
      intro x
      rw [hK_eq, hKj_eq]
      exact mem_ker_iff_PhiLE_mem (A := A) (n := n) d 0 x
    have hIiff : ∀ x ∈ K, (PhiLE (A := A) (n := n) d 0) x ∈ Submodule.pi Set.univ Ij ↔ x ∈ I := by
      intro x hx
      have hbot_mem : ∀ y : (j : Fin r) → CechTerm (A := A) (n := n) (M := Poly A n)
          (shift (A := A) (n := n) (d j)) 0, y ∈ Submodule.pi Set.univ Ij ↔ y = 0 := by
        intro y
        rw [hIjz]
        constructor
        · intro hy
          funext j
          exact (Submodule.mem_bot (R := A)).mp
            ((Submodule.mem_pi.mp hy) j (Set.mem_univ j))
        · intro hy j _
          rw [hy]
          exact Submodule.zero_mem _
      have hIbot_mem : ∀ y : ↥((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
          (freeGraded (A := A) (n := n) d)).X 0), y ∈ I ↔ y = 0 := by
        intro y
        rw [hIz]
        exact Submodule.mem_bot A
      rw [hbot_mem ((PhiLE (A := A) (n := n) d 0) x), hIbot_mem x]
      exact (PhiLE (A := A) (n := n) d 0).map_eq_zero_iff
    have hfin : ∀ j, Module.Finite A (↥(Kj j) ⧸ Submodule.comap (Kj j).subtype (Ij j)) := by
      intro j
      haveI := hshift (d j) 0
      exact Module.Finite.equiv (Classical.choice (homologyEquivKerQuot (A := A)
        (chartCech (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j))) 0))
    have hquot : Module.Finite A (↥K ⧸ Submodule.comap K.subtype I) :=
      finite_quot_of_data (PhiLE (A := A) (n := n) d 0) K Kj I Ij hKiff hIiff hfin
    haveI := hquot
    exact Module.Finite.equiv
      (Classical.choice (homologyEquivKerQuot (A := A) (chartCech (A := A) (n := n)
        (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d)) 0)).symm
  · -- q = q' + 1
    set K : Submodule A ↥((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).X (q' + 1)) :=
      LinearMap.ker (((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).d (q' + 1) ((q' + 1) + 1)).hom) with hK
    set I : Submodule A ↥((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).X (q' + 1)) :=
      LinearMap.range (((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d)).d ((q' + 1) - 1) (q' + 1)).hom) with hI
    set Kj : (j : Fin r) → Submodule A ↥((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).X (q' + 1)) :=
      fun j => LinearMap.ker (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d (q' + 1) ((q' + 1) + 1)).hom) with hKj
    set Ij : (j : Fin r) → Submodule A ↥((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).X (q' + 1)) :=
      fun j => LinearMap.range (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d ((q' + 1) - 1) (q' + 1)).hom) with hIj
    have hK_eq : K = LinearMap.ker (cechDiff (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) (q' + 1)) := by
      rw [hK, chartCech_d_next (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) (q' + 1)]
      rfl
    have hKj_eq : Kj = fun j => LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) (q' + 1)) := by
      funext j
      show LinearMap.ker (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d (q' + 1) ((q' + 1) + 1)).hom) = _
      rw [chartCech_d_next (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) (q' + 1)]
      rfl
    have hI_eq : I = LinearMap.range (cechDiff (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) q') := by
      rw [hI]
      exact congrArg LinearMap.range (chartCech_d_next (A := A) (n := n) (M := Fin r → Poly A n)
        (freeGraded (A := A) (n := n) d) q')
    have hIj_eq : Ij = fun j => LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) q') := by
      funext j
      show LinearMap.range (((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j))).d ((q' + 1) - 1) (q' + 1)).hom) = _
      exact congrArg LinearMap.range (chartCech_d_next (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) q')
    have hKiff : ∀ x, x ∈ K ↔ (PhiLE (A := A) (n := n) d (q' + 1)) x ∈
        Submodule.pi Set.univ Kj := by
      intro x
      rw [hK_eq, hKj_eq]
      exact mem_ker_iff_PhiLE_mem (A := A) (n := n) d (q' + 1) x
    have hIiff : ∀ x ∈ K, (PhiLE (A := A) (n := n) d (q' + 1)) x ∈
        Submodule.pi Set.univ Ij ↔ x ∈ I := by
      intro x hx
      rw [hI_eq, hIj_eq]
      constructor
      · intro hmem
        have hmem' : ∀ j, ∃ y, cechDiff (A := A) (n := n) (M := Poly A n)
            (shift (A := A) (n := n) (d j)) q' y =
              ((PhiLE (A := A) (n := n) d (q' + 1)) x) j :=
          fun j => Submodule.mem_pi.mp hmem j (Set.mem_univ j)
        choose y hy using hmem'
        obtain ⟨z, hz⟩ := (PhiLE (A := A) (n := n) d q').surjective y
        refine ⟨z, ?_⟩
        apply (PhiLE (A := A) (n := n) d (q' + 1)).injective
        funext j
        simpa only [PhiLE_cechDiff_apply, hz] using hy j
      · intro hxI
        obtain ⟨z, hz⟩ := hxI
        intro j _
        dsimp only
        rw [← hz]
        refine ⟨((PhiLE (A := A) (n := n) d q') z) j, ?_⟩
        exact (PhiLE_cechDiff_apply (A := A) (n := n) d q' z j).symm
    have hfin : ∀ j, Module.Finite A (↥(Kj j) ⧸ Submodule.comap (Kj j).subtype (Ij j)) := by
      intro j
      haveI := hshift (d j) (q' + 1)
      exact Module.Finite.equiv (Classical.choice (homologyEquivKerQuot (A := A)
        (chartCech (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)))
        (q' + 1)))
    have hquot : Module.Finite A (↥K ⧸ Submodule.comap K.subtype I) :=
      finite_quot_of_data (PhiLE (A := A) (n := n) d (q' + 1)) K Kj I Ij hKiff hIiff hfin
    haveI := hquot
    exact Module.Finite.equiv
      (Classical.choice (homologyEquivKerQuot (A := A) (chartCech (A := A) (n := n)
        (M := Fin r → Poly A n) (freeGraded (A := A) (n := n) d)) (q' + 1))).symm


/-- **Finiteness of the chart Čech cohomology of a finite free graded module.** -/
theorem freeGraded_homology_finite {A : Type*} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    (hshift : ∀ (d q : ℕ), Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology q))
    (r : ℕ) (d : Fin r → ℕ) (q : ℕ) :
    Module.Finite A ((chartCech (A := A) (n := n) (M := Fin r → Poly A n)
      (freeGraded (A := A) (n := n) d)).homology q) :=
  fghf_aux hshift r d q

end Work.DSCOH
