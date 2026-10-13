import Mathlib
import Submission.Work.DSEQ0.exists_cech_cup
import Submission.Work.DSG4a.CechBaseChange

namespace Work.DSEQ0

universe a

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

set_option maxHeartbeats 800000

variable {A : Type a} [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
  (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} [Finite ι] (U : ι → X.Opens)

/-- The ℤ-graded Čech complex `cechZ` is `cech.extend ComplexShape.embeddingUpNat`.
For `i ≥ 0`, `extendXIso` identifies its term in degree `i` with degree `i.toNat` of the
ℕ-graded complex. -/
noncomputable def isoZ (i : ℤ) (hi : 0 ≤ i) :
    (DSMap.cechZ A X f U).X i ≅ (DSMap.cech A X f U).X i.toNat :=
  (DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := i.toNat)
    (Int.toNat_of_nonneg hi)

/-- The cup product on nonnegative degrees, transported to the ℤ-graded complex. -/
noncomputable def cupPos
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    (DSMap.cechZ A X f U).X i →ₗ[A] (DSMap.cechZ A X f U).X j →ₗ[A] (DSMap.cechZ A X f U).X (i+j) :=
  let hsum : 0 ≤ i + j := by omega
  let hh : i.toNat + j.toNat = (i+j).toNat := by omega
  let k : (DSMap.cech A X f U).X (i.toNat + j.toNat) →ₗ[A] (DSMap.cechZ A X f U).X (i+j) :=
    ((isoZ X f U (i+j) hsum).inv.hom).comp (((DSMap.cech A X f U).XIsoOfEq hh).hom.hom)
  LinearMap.compl₁₂
    ((LinearMap.llcomp A ((DSMap.cech A X f U).X j.toNat)
        ((DSMap.cech A X f U).X (i.toNat + j.toNat)) ((DSMap.cechZ A X f U).X (i+j)) k).comp
      (cup i.toNat j.toNat))
    ((isoZ X f U i hi).hom.hom) ((isoZ X f U j hj).hom.hom)

/-- The candidate extension of the cup product to the ℤ-graded Čech complex: it agrees with
`cup` on nonnegative degrees (via `isoZ`) and is zero as soon as one degree is negative. -/
noncomputable def psiCup
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) : (DSMap.cechZ A X f U).X i →ₗ[A] (DSMap.cechZ A X f U).X j →ₗ[A]
      (DSMap.cechZ A X f U).X (i+j) :=
  if h : 0 ≤ i ∧ 0 ≤ j then cupPos X f U cup i j h.1 h.2 else 0

/-- Evaluation of `cupPos`. -/
lemma cupPos_apply
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (cupPos X f U cup i j hi hj) x y
      = (isoZ X f U (i+j) (by omega)).inv.hom
          (((DSMap.cech A X f U).XIsoOfEq
              (by omega : i.toNat + j.toNat = (i+j).toNat)).hom.hom
            ((cup i.toNat j.toNat) ((isoZ X f U i hi).hom.hom x)
              ((isoZ X f U j hj).hom.hom y))) := by
  simp only [cupPos, LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.llcomp_apply]

/-- `cechZ` differential at successive nonnegative degrees. -/
lemma cechZ_d_succ (k : ℤ) (hk : 0 ≤ k) :
    (DSMap.cechZ A X f U).d k (k+1) =
      (isoZ X f U k hk).hom ≫ (DSMap.cech A X f U).d k.toNat ((k+1).toNat) ≫
        (isoZ X f U (k+1) (by omega : (0:ℤ) ≤ k+1)).inv := by
  unfold DSMap.cechZ
  rw [HomologicalComplex.extend_d_eq (DSMap.cech A X f U) ComplexShape.embeddingUpNat
      (hi := Int.toNat_of_nonneg hk) (hj := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k+1))]
  rfl

lemma cup_XIsoOfEq (C : CochainComplex (ModuleCat.{a} A) ℕ)
    (cup : ∀ p q : ℕ, C.X p →ₗ[A] C.X q →ₗ[A] C.X (p+q))
    {p p' q q' : ℕ} (h1 : p' = p) (h2 : q' = q) (h : p' + q' = p + q)
    (z : ↥(C.X p')) (w : ↥(C.X q')) :
    (C.XIsoOfEq h).hom ((cup p' q') z w)
      = (cup p q) ((C.XIsoOfEq h1).hom z) ((C.XIsoOfEq h2).hom w) := by
  subst h1; subst h2
  have hh : h = rfl := Subsingleton.elim h rfl
  rw [hh, HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- `isoZ` is natural with respect to index transports. -/
lemma isoZ_inv_comp_XIsoOfEq (k k' : ℤ) (h : k = k') (hk : 0 ≤ k) (hk' : 0 ≤ k')
    (h2 : k.toNat = k'.toNat) :
    (isoZ X f U k hk).inv ≫ ((DSMap.cechZ A X f U).XIsoOfEq h).hom =
      ((DSMap.cech A X f U).XIsoOfEq h2).hom ≫ (isoZ X f U k' hk').inv := by
  subst h
  have h2r : h2 = rfl := Subsingleton.elim h2 rfl
  simp only [h2r, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  exact congrArg (fun p => (isoZ X f U k p).inv) (Subsingleton.elim hk hk')

lemma XIsoOfEq_hom_isoZ_inv_apply (k k' : ℤ) (h : k = k') (hk : 0 ≤ k) (hk' : 0 ≤ k')
    (h2 : k.toNat = k'.toNat) (z : ↥((DSMap.cech A X f U).X k.toNat)) :
    ((DSMap.cechZ A X f U).XIsoOfEq h).hom ((isoZ X f U k hk).inv.hom z)
      = (isoZ X f U k' hk').inv.hom (((DSMap.cech A X f U).XIsoOfEq h2).hom z) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (isoZ_inv_comp_XIsoOfEq X f U k k' h hk hk' h2)) z

lemma isoZ_hom_d (i : ℤ) (hi : 0 ≤ i) (x : ↥((DSMap.cechZ A X f U).X i)) :
    (isoZ X f U (i+1) (by omega)).hom.hom
        (((DSMap.cechZ A X f U).d i (i+1)).hom x)
      = ((DSMap.cech A X f U).d i.toNat ((i+1).toNat)).hom
          ((isoZ X f U i hi).hom.hom x) := by
  rw [cechZ_d_succ X f U i hi]
  simp only [ModuleCat.hom_comp, ModuleCat.comp_apply, LinearMap.comp_apply]
  rw [Iso.inv_hom_id_apply]

lemma d_comp_XIsoOfEq_hom_apply {p₁ p₂ p₃ : ℕ} (h : p₂ = p₃)
    (x : ↥((DSMap.cech A X f U).X p₁)) :
    ((DSMap.cech A X f U).XIsoOfEq h).hom (((DSMap.cech A X f U).d p₁ p₂).hom x)
      = ((DSMap.cech A X f U).d p₁ p₃).hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.d_comp_XIsoOfEq_hom (DSMap.cech A X f U) h p₁)) x

lemma XIsoOfEq_hom_comp_apply (C : CochainComplex (ModuleCat.{a} A) ℕ) {p q r : ℕ}
    (h1 : p = q) (h2 : q = r) (x : ↥(C.X p)) :
    (C.XIsoOfEq h2).hom ((C.XIsoOfEq h1).hom x) = (C.XIsoOfEq (h1.trans h2)).hom x := by
  rw [← ModuleCat.comp_apply, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]

lemma XIsoOfEq_self_apply {p : ℕ} (e : p = p) (z : ↥((DSMap.cech A X f U).X p)) :
    ((DSMap.cech A X f U).XIsoOfEq e).hom z = z := by
  rw [show e = rfl from Subsingleton.elim _ _]
  simp

lemma psiCup_pos_apply
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (psiCup X f U cup i j) x y = (cupPos X f U cup i j hi hj) x y := by
  rw [psiCup, dif_pos (show 0 ≤ i ∧ 0 ≤ j from ⟨hi, hj⟩)]

lemma lhs_reduce
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    ((isoZ X f U (i+j+1) (by omega)).hom)
      ((((DSMap.cechZ A X f U).d (i+j) (i+j+1)).hom) (((psiCup X f U cup i j) x) y))
      = ((DSMap.cech A X f U).d (i.toNat + j.toNat) ((i+j+1).toNat))
          ((cup i.toNat j.toNat) ((isoZ X f U i hi).hom.hom x)
            ((isoZ X f U j hj).hom.hom y)) := by
  have hsum : 0 ≤ i + j := by omega
  rw [psiCup, dif_pos (show 0 ≤ i ∧ 0 ≤ j from ⟨hi, hj⟩)]
  rw [cupPos_apply X f U cup i j hi hj]
  rw [cechZ_d_succ X f U (i+j) hsum]
  simp only [ModuleCat.hom_comp, ModuleCat.comp_apply, LinearMap.comp_apply]
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.XIsoOfEq_hom_comp_d (DSMap.cech A X f U)
      (by omega : i.toNat + j.toNat = (i+j).toNat) ((i+j+1).toNat))) _

lemma rhs1_reduce
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    ((isoZ X f U (i+j+1) (by omega)).hom)
      (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
        (((psiCup X f U cup (i + 1) j)
          ((((DSMap.cechZ A X f U).d i (i + 1)).hom x))) y))
      = ((DSMap.cech A X f U).XIsoOfEq
            (by omega : (i+1).toNat + j.toNat = (i+j+1).toNat)).hom
          ((cup (i+1).toNat j.toNat)
            (((DSMap.cech A X f U).d i.toNat ((i+1).toNat)).hom
              ((isoZ X f U i hi).hom.hom x))
            ((isoZ X f U j hj).hom.hom y)) := by
  have h1 : 0 ≤ i+1 := by omega
  have hsum : 0 ≤ (i+1)+j := by omega
  rw [psiCup, dif_pos (show 0 ≤ i+1 ∧ 0 ≤ j from ⟨h1, hj⟩)]
  rw [cupPos_apply X f U cup (i+1) j h1 hj]
  rw [isoZ_hom_d X f U i hi x]
  rw [XIsoOfEq_hom_isoZ_inv_apply X f U (i+1+j) (i+j+1) (by omega : i+1+j = i+j+1)
        (by omega) (by omega) (by omega : (i+1+j).toNat = (i+j+1).toNat)]
  rw [Iso.inv_hom_id_apply]
  rw [XIsoOfEq_hom_comp_apply]

lemma leibniz_C
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (hcup : ∀ (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).d (p + q) (p + q + 1)).hom ((cup p q) a b)
          = ((DSMap.cech A X f U).XIsoOfEq (by omega : (p + 1) + q = (p + q) + 1)).hom
              ((cup (p + 1) q) (((DSMap.cech A X f U).d p (p + 1)).hom a) b)
            + (-1 : A) ^ p • (cup p (q + 1)) a (((DSMap.cech A X f U).d q (q + 1)).hom b))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x₀ : ↥((DSMap.cech A X f U).X i.toNat)) (y₀ : ↥((DSMap.cech A X f U).X j.toNat)) :
    (((DSMap.cech A X f U).d (i.toNat + j.toNat) ((i+j+1).toNat)).hom)
        ((cup i.toNat j.toNat) x₀ y₀)
      = (((DSMap.cech A X f U).XIsoOfEq
            (show (i+1).toNat + j.toNat = (i+j+1).toNat by omega)).hom)
          ((cup (i+1).toNat j.toNat)
            ((((DSMap.cech A X f U).d i.toNat ((i+1).toNat)).hom) x₀) y₀)
        + (-1 : A) ^ i.natAbs •
          (((DSMap.cech A X f U).XIsoOfEq
            (show i.toNat + (j+1).toNat = (i+j+1).toNat by omega)).hom)
            ((cup i.toNat (j+1).toNat) x₀
              ((((DSMap.cech A X f U).d j.toNat ((j+1).toNat)).hom) y₀)) := by
  have hsign : i.natAbs = i.toNat := by omega
  rw [hsign]
  rw [← LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.d_comp_XIsoOfEq_hom (DSMap.cech A X f U)
      (show i.toNat + j.toNat + 1 = (i+j+1).toNat by omega) (i.toNat + j.toNat)))
      ((cup i.toNat j.toNat) x₀ y₀)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hcup i.toNat j.toNat x₀ y₀]
  have hb1 : ((DSMap.cech A X f U).XIsoOfEq
        (show (i+1).toNat + j.toNat = (i.toNat+1) + j.toNat by omega)).hom
      ((cup (i+1).toNat j.toNat)
        ((((DSMap.cech A X f U).d i.toNat ((i+1).toNat)).hom) x₀) y₀)
      = (cup (i.toNat+1) j.toNat)
        ((((DSMap.cech A X f U).d i.toNat (i.toNat+1)).hom) x₀) y₀ := by
    rw [cup_XIsoOfEq (DSMap.cech A X f U) cup
      (show (i+1).toNat = i.toNat+1 by omega) (rfl : j.toNat = j.toNat)]
    rw [d_comp_XIsoOfEq_hom_apply]
    rfl
  have hb2 : ((DSMap.cech A X f U).XIsoOfEq
        (show i.toNat + (j+1).toNat = i.toNat + (j.toNat+1) by omega)).hom
      ((cup i.toNat (j+1).toNat) x₀
        ((((DSMap.cech A X f U).d j.toNat ((j+1).toNat)).hom) y₀))
      = (cup i.toNat (j.toNat+1)) x₀
        ((((DSMap.cech A X f U).d j.toNat (j.toNat+1)).hom) y₀) := by
    rw [cup_XIsoOfEq (DSMap.cech A X f U) cup
      (rfl : i.toNat = i.toNat) (show (j+1).toNat = j.toNat+1 by omega)]
    rw [d_comp_XIsoOfEq_hom_apply]
    rfl
  rw [map_add, map_smul]
  congr 1
  · rw [XIsoOfEq_hom_comp_apply, ← hb1, XIsoOfEq_hom_comp_apply]
  · rw [← hb2, XIsoOfEq_hom_comp_apply]

lemma rhs2_reduce
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    ((isoZ X f U (i+j+1) (by omega)).hom)
      (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
        (((psiCup X f U cup i (j + 1)) x)
          ((((DSMap.cechZ A X f U).d j (j + 1)).hom y))))
      = ((DSMap.cech A X f U).XIsoOfEq
            (by omega : i.toNat + (j+1).toNat = (i+j+1).toNat)).hom
          ((cup i.toNat (j+1).toNat) ((isoZ X f U i hi).hom.hom x)
            (((DSMap.cech A X f U).d j.toNat ((j+1).toNat)).hom
              ((isoZ X f U j hj).hom.hom y))) := by
  have h1 : 0 ≤ j+1 := by omega
  have hsum : 0 ≤ i+(j+1) := by omega
  rw [psiCup, dif_pos (show 0 ≤ i ∧ 0 ≤ j+1 from ⟨hi, h1⟩)]
  rw [cupPos_apply X f U cup i (j+1) hi h1]
  rw [isoZ_hom_d X f U j hj y]
  rw [XIsoOfEq_hom_isoZ_inv_apply X f U (i+(j+1)) (i+j+1) (by omega : i+(j+1) = i+j+1)
        (by omega) (by omega) (by omega : (i+(j+1)).toNat = (i+j+1).toNat)]
  rw [Iso.inv_hom_id_apply]
  rw [XIsoOfEq_hom_comp_apply]

lemma leibniz_pos
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (hcup : ∀ (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).d (p + q) (p + q + 1)).hom ((cup p q) a b)
          = ((DSMap.cech A X f U).XIsoOfEq (by omega : (p + 1) + q = (p + q) + 1)).hom
              ((cup (p + 1) q) (((DSMap.cech A X f U).d p (p + 1)).hom a) b)
            + (-1 : A) ^ p • (cup p (q + 1)) a (((DSMap.cech A X f U).d q (q + 1)).hom b))
    (i j : ℤ) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (((DSMap.cechZ A X f U).d (i + j) (i + j + 1)).hom) (((psiCup X f U cup i j) x) y)
      = ((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
          (((psiCup X f U cup (i + 1) j) (((DSMap.cechZ A X f U).d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
          (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
            ((psiCup X f U cup i (j + 1) x) (((DSMap.cechZ A X f U).d j (j + 1)).hom y))) := by
  have key : ((isoZ X f U (i+j+1) (by omega)).hom)
      ((((DSMap.cechZ A X f U).d (i + j) (i + j + 1)).hom) (((psiCup X f U cup i j) x) y))
      = ((isoZ X f U (i+j+1) (by omega)).hom)
          (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((psiCup X f U cup (i + 1) j) (((DSMap.cechZ A X f U).d i (i + 1)).hom x)) y)
            + (-1 : A) ^ i.natAbs •
              (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((psiCup X f U cup i (j + 1) x) (((DSMap.cechZ A X f U).d j (j + 1)).hom y)))) := by
    rw [lhs_reduce X f U cup i j hi hj x y]
    rw [map_add, map_smul]
    rw [rhs1_reduce X f U cup i j hi hj x y]
    rw [rhs2_reduce X f U cup i j hi hj x y]
    rw [leibniz_C X f U cup hcup i j hi hj ((isoZ X f U i hi).hom.hom x)
          ((isoZ X f U j hj).hom.hom y)]
  have h2 := congrArg (fun w => (isoZ X f U (i+j+1) (by omega)).inv.hom w) key
  simpa only [Iso.hom_inv_id_apply] using h2

lemma isZero_cechZ_neg (k : ℤ) (hk : k < 0) : IsZero ((DSMap.cechZ A X f U).X k) := by
  unfold DSMap.cechZ
  refine HomologicalComplex.isZero_extend_X (DSMap.cech A X f U)
    ComplexShape.embeddingUpNat k ?_
  intro n h
  have h' : (n : ℤ) = k := h
  have : (0:ℤ) ≤ (n:ℤ) := Int.natCast_nonneg n
  omega

lemma leibniz_neg_left
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hik : i < 0)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (((DSMap.cechZ A X f U).d (i + j) (i + j + 1)).hom) (((psiCup X f U cup i j) x) y)
      = ((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
          (((psiCup X f U cup (i + 1) j) (((DSMap.cechZ A X f U).d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
          (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
            ((psiCup X f U cup i (j + 1) x) (((DSMap.cechZ A X f U).d j (j + 1)).hom y))) := by
  have hsub : Subsingleton ↥((DSMap.cechZ A X f U).X i) :=
    ModuleCat.subsingleton_of_isZero (isZero_cechZ_neg X f U i hik)
  have hx : x = 0 := Subsingleton.elim x 0
  have hx0 : (((DSMap.cechZ A X f U).d i (i + 1)).hom) x = 0 := by rw [hx, map_zero]
  have h1 : (psiCup X f U cup i j) = 0 := by
    rw [psiCup, dif_neg (by omega : ¬(0 ≤ i ∧ 0 ≤ j))]
  have h2 : (psiCup X f U cup i (j + 1)) = 0 := by
    rw [psiCup, dif_neg (by omega : ¬(0 ≤ i ∧ 0 ≤ (j+1)))]
  rw [h1, h2, hx0]
  simp

lemma leibniz_neg_right
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (i j : ℤ) (hjk : j < 0)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (((DSMap.cechZ A X f U).d (i + j) (i + j + 1)).hom) (((psiCup X f U cup i j) x) y)
      = ((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
          (((psiCup X f U cup (i + 1) j) (((DSMap.cechZ A X f U).d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
          (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
            ((psiCup X f U cup i (j + 1) x) (((DSMap.cechZ A X f U).d j (j + 1)).hom y))) := by
  have hsub : Subsingleton ↥((DSMap.cechZ A X f U).X j) :=
    ModuleCat.subsingleton_of_isZero (isZero_cechZ_neg X f U j hjk)
  have hy : y = 0 := Subsingleton.elim y 0
  have hy0 : (((DSMap.cechZ A X f U).d j (j + 1)).hom) y = 0 := by rw [hy, map_zero]
  have h1 : (psiCup X f U cup i j) = 0 := by
    rw [psiCup, dif_neg (by omega : ¬(0 ≤ i ∧ 0 ≤ j))]
  have h2 : (psiCup X f U cup (i + 1) j) = 0 := by
    rw [psiCup, dif_neg (by omega : ¬(0 ≤ (i+1) ∧ 0 ≤ j))]
  rw [h1, h2, hy0]
  simp

lemma leibniz_cup
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (hcup : ∀ (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).d (p + q) (p + q + 1)).hom ((cup p q) a b)
          = ((DSMap.cech A X f U).XIsoOfEq (by omega : (p + 1) + q = (p + q) + 1)).hom
              ((cup (p + 1) q) (((DSMap.cech A X f U).d p (p + 1)).hom a) b)
            + (-1 : A) ^ p • (cup p (q + 1)) a (((DSMap.cech A X f U).d q (q + 1)).hom b))
    (i j : ℤ)
    (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (((DSMap.cechZ A X f U).d (i + j) (i + j + 1)).hom) (((psiCup X f U cup i j) x) y)
      = ((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
          (((psiCup X f U cup (i + 1) j) (((DSMap.cechZ A X f U).d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
          (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
            ((psiCup X f U cup i (j + 1) x) (((DSMap.cechZ A X f U).d j (j + 1)).hom y))) := by
  rcases lt_or_ge i 0 with hi | hi
  · exact leibniz_neg_left X f U cup i j hi x y
  · rcases lt_or_ge j 0 with hj | hj
    · exact leibniz_neg_right X f U cup i j hj x y
    · exact leibniz_pos X f U cup hcup i j hi hj x y

lemma unit_cup
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (hunit : ∀ (q : ℕ) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).XIsoOfEq (Nat.zero_add q)).hom
          ((cup 0 q) ((DSMap.coaug0 A X f U).hom 1) b) = b)
    (j : ℤ) (y : ↥((DSMap.cechZ A X f U).X j)) :
    (((DSMap.cechZ A X f U).XIsoOfEq (by omega : (0 : ℤ) + j = j)).hom)
      ((psiCup X f U cup 0 j (Work.DSG4a.coaugZElem A X f U)) y) = y := by
  have h0 : (0:ℤ) ≤ 0 := le_refl 0
  by_cases hj : 0 ≤ j
  · have hcoe : (isoZ X f U 0 h0).hom.hom (Work.DSG4a.coaugZElem A X f U)
        = (DSMap.coaug0 A X f U).hom 1 := by
      rw [show Work.DSG4a.coaugZElem A X f U =
          ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv
            ((DSMap.coaug0 A X f U) 1) from rfl]
      rw [show isoZ X f U 0 h0 = (DSMap.cech A X f U).extendXIso
        ComplexShape.embeddingUpNat (i := 0) rfl from rfl]
      exact Iso.inv_hom_id_apply _ _
    have hunit' : ∀ (e : (0:ℤ).toNat + j.toNat = j.toNat)
        (b : ↥((DSMap.cech A X f U).X j.toNat)),
        ((DSMap.cech A X f U).XIsoOfEq e).hom
          ((cup (0:ℤ).toNat j.toNat) ((DSMap.coaug0 A X f U).hom 1) b) = b := by
      intro e b
      rw [show e = Nat.zero_add j.toNat from Subsingleton.elim _ _]
      exact hunit j.toNat b
    rw [psiCup, dif_pos (show 0 ≤ (0:ℤ) ∧ 0 ≤ j from ⟨h0, hj⟩)]
    rw [cupPos_apply X f U cup 0 j h0 hj (Work.DSG4a.coaugZElem A X f U) y]
    rw [hcoe]
    rw [XIsoOfEq_hom_isoZ_inv_apply X f U (0+j) j (by omega : 0+j = j) (by omega) hj
          (by omega : (0+j).toNat = j.toNat)]
    rw [XIsoOfEq_hom_comp_apply]
    rw [hunit' _ _, Iso.hom_inv_id_apply]
  · have hjk : j < 0 := by omega
    have hsub : Subsingleton ↥((DSMap.cechZ A X f U).X j) :=
      ModuleCat.subsingleton_of_isZero (isZero_cechZ_neg X f U j hjk)
    have hy : y = 0 := Subsingleton.elim y 0
    have h1 : (psiCup X f U cup 0 j) = 0 := by
      rw [psiCup, dif_neg (by omega : ¬(0 ≤ (0:ℤ) ∧ 0 ≤ j))]
    rw [h1, hy]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma cup_extends
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (p q : ℕ) (x : ↥((DSMap.cech A X f U).X p)) (y : ↥((DSMap.cech A X f U).X q)) :
    (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := p+q) rfl).hom)
      ((psiCup X f U cup (p : ℤ) (q : ℤ))
        (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv x)
        (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv y))
      = (cup p q) x y := by
  have hp : 0 ≤ (p:ℤ) := Int.natCast_nonneg p
  have hq : 0 ≤ (q:ℤ) := Int.natCast_nonneg q
  have hpq : 0 ≤ (p:ℤ)+(q:ℤ) := by omega
  rw [show ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := p+q) rfl)
      = isoZ X f U ((p:ℤ)+(q:ℤ)) hpq from rfl]
  rw [show (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv x)
      = ((isoZ X f U (p:ℤ) hp).inv.hom) x from rfl]
  rw [show (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv y)
      = ((isoZ X f U (q:ℤ) hq).inv.hom) y from rfl]
  rw [psiCup, dif_pos (show 0 ≤ (p:ℤ) ∧ 0 ≤ (q:ℤ) from ⟨hp, hq⟩)]
  rw [cupPos_apply X f U cup (p:ℤ) (q:ℤ) hp hq
      ((isoZ X f U (p:ℤ) hp).inv.hom x) ((isoZ X f U (q:ℤ) hq).inv.hom y)]
  simp only [Iso.inv_hom_id_apply]
  refine (Iso.inv_hom_id_apply (isoZ X f U ((p:ℤ)+(q:ℤ)) hpq) _).trans ?_
  exact XIsoOfEq_self_apply X f U _ _

end

set_option maxHeartbeats 1000000 in
theorem exists_cechZ_cup_extension {A : Type a} [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
      (DSMap.cech A X f U).X (p + q))
    (hcup : ∀ (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).d (p + q) (p + q + 1)).hom ((cup p q) a b)
          = ((DSMap.cech A X f U).XIsoOfEq (by omega : (p + 1) + q = (p + q) + 1)).hom
              ((cup (p + 1) q) (((DSMap.cech A X f U).d p (p + 1)).hom a) b)
            + (-1 : A) ^ p • (cup p (q + 1)) a (((DSMap.cech A X f U).d q (q + 1)).hom b))
    (hunit : ∀ (q : ℕ) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).XIsoOfEq (Nat.zero_add q)).hom
          ((cup 0 q) ((DSMap.coaug0 A X f U).hom 1) b) = b) :
    ∃ ψ : ∀ i j : ℤ, ↥((DSMap.cechZ A X f U).X i) →ₗ[A] ↥((DSMap.cechZ A X f U).X j) →ₗ[A]
        ↥((DSMap.cechZ A X f U).X (i + j)),
      (∀ (i j : ℤ) (x : ↥((DSMap.cechZ A X f U).X i)) (y : ↥((DSMap.cechZ A X f U).X j)),
        ((DSMap.cechZ A X f U).d (i + j) (i + j + 1)).hom ((ψ i j x) y)
          = ((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((ψ (i + 1) j) (((DSMap.cechZ A X f U).d i (i + 1)).hom x)) y)
            + (-1 : A) ^ i.natAbs •
              (((DSMap.cechZ A X f U).XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((ψ i (j + 1) x) (((DSMap.cechZ A X f U).d j (j + 1)).hom y)))) ∧
      (∀ (j : ℤ) (y : ↥((DSMap.cechZ A X f U).X j)),
        ((DSMap.cechZ A X f U).XIsoOfEq (by omega : (0 : ℤ) + j = j)).hom
          ((ψ 0 j (Work.DSG4a.coaugZElem A X f U)) y) = y) ∧
      (∀ (p q : ℕ) (x : ↥((DSMap.cech A X f U).X p)) (y : ↥((DSMap.cech A X f U).X q)),
        (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := p+q) rfl).hom)
          ((ψ (p : ℤ) (q : ℤ))
            (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv x)
            (((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv y))
          = (cup p q) x y) := by
  refine ⟨psiCup X f U cup, ?_, ?_, ?_⟩
  · intro i j x y
    exact leibniz_cup X f U cup hcup i j x y
  · intro j y
    exact unit_cup X f U cup hunit j y
  · intro p q x y
    exact cup_extends X f U cup p q x y

end Work.DSEQ0
