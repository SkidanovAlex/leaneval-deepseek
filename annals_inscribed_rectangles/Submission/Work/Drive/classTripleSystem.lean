import Mathlib
import Submission.Work.Drive.tripleParity322
import Submission.Work.Drive.even_ncard_tripleMeetFam_zero_one
import Submission.Work.Drive.squareSystemForm
import Submission.Work.Drive.qform_bilinear
import Submission.Work.Drive.qform_kernel
import Submission.Work.Drive.contDiff_qform
import Submission.Work.Drive.genericRegularizationSquare

/-!
# The "class system" of three plane parameters, and its zeros

`Work.Drive.qform` is the globally smooth model of the class equality on `ℝP³` (see
`Submission/Work/Drive/squareSystemForm.lean`).  This file builds, out of the three lifts `V k` of the
class maps of a triple of plane presentations, the **class system**

`classSystem V A p y = (qform (A p 0 (V 0 y₀)) (A p 1 (V 1 y₁)), qform (A p 0 (V 0 y₀)) (A p 2 (V 2 y₂)))`

of the *perturbed* configuration (`A p k` is the perturbation of the `k`-th class), and proves that its
zeros are exactly the triples `y` at which the three perturbed classes coincide
(`classSystem_eq_zero_iff`).  Together with the parametric-Sard statement of
`Submission/Work/Drive/genericRegularizationSquare.lean` this is the genericity engine of the lead's
`L5`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

noncomputable section

/-! ## 0. The named components of `qform_bilinear` -/

lemma qform_add_left (v v' w : Eucl 3) : qform (v + v') w = qform v w + qform v' w :=
  (qform_bilinear v v' w w 0).1

lemma qform_add_right (v w w' : Eucl 3) : qform v (w + w') = qform v w + qform v w' :=
  (qform_bilinear v v w w' 0).2.1

lemma qform_smul_left (c : ℝ) (v w : Eucl 3) : qform (c • v) w = c • qform v w :=
  (qform_bilinear v v w w c).2.2.1

lemma qform_smul_right (c : ℝ) (v w : Eucl 3) : qform v (c • w) = c • qform v w :=
  (qform_bilinear v v w w c).2.2.2.1

lemma qform_antisymm' (v w : Eucl 3) : qform v w = - qform w v :=
  (qform_bilinear v v w w 0).2.2.2.2.1

lemma qform_self (v : Eucl 3) : qform v v = 0 :=
  (qform_bilinear v v v v 0).2.2.2.2.2

lemma qform_eq_zero_of_smul (v : Eucl 3) (a : ℝ) : qform v (a • v) = 0 := by
  rw [qform_smul_right, qform_self, smul_zero]

/-- `qform v w = 0` whenever `w` lies in the line spanned by `v`. -/
lemma qform_eq_zero_of_mem_span {v w : Eucl 3} (h : w ∈ Submodule.span ℝ ({v} : Set (Eucl 3))) :
    qform v w = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
  exact qform_eq_zero_of_smul v a

/-! ## 1. The six plane coordinates as three plane parameters -/

/-- The `i`-th coordinate of the `k`-th plane parameter, as a coordinate of `Tgt 6`. -/
def parC (k : Fin 3) (i : Fin 2) : Fin 6 := finProdFinEquiv (m := 3) (n := 2) (k, i)

lemma parC_injective {k k' : Fin 3} {i i' : Fin 2} (h : parC k i = parC k' i') : k = k' ∧ i = i' :=
  Prod.ext_iff.mp ((finProdFinEquiv (m := 3) (n := 2)).injective h)

lemma parC_surjective (j : Fin 6) : ∃ (k : Fin 3) (i : Fin 2), parC k i = j := by
  refine ⟨((finProdFinEquiv (m := 3) (n := 2)).symm j).1,
    ((finProdFinEquiv (m := 3) (n := 2)).symm j).2, ?_⟩
  show finProdFinEquiv (m := 3) (n := 2) ((finProdFinEquiv (m := 3) (n := 2)).symm j) = j
  exact (finProdFinEquiv (m := 3) (n := 2)).apply_symm_apply j

/-- The `k`-th plane parameter of a point of the `Tgt 6`-space of plane parameters. -/
def parOf (y : Tgt 6) (k : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => y (parC k i))

@[simp] lemma parOf_apply (y : Tgt 6) (k : Fin 3) (i : Fin 2) : parOf y k i = y (parC k i) := by
  simp only [parOf, WithLp.ofLp_toLp]

lemma parOf_mem_tgtBox {y : Tgt 6} (hy : y ∈ tgtBox 6) (k : Fin 3) : parOf y k ∈ tgtBox 2 :=
  fun i => by rw [parOf_apply]; exact hy (parC k i)

lemma mem_tgtBox_six {y : Tgt 6} (hy : ∀ k, parOf y k ∈ tgtBox 2) : y ∈ tgtBox 6 := by
  intro j
  obtain ⟨k, i, rfl⟩ := parC_surjective j
  rw [← parOf_apply]
  exact hy k i

/-! ## 2. The class system -/

/-- **The class system** of a triple of lifts `V k` and a family of perturbations `A` of the three
classes: the pair of the `qform`-differences of the three perturbed lift values, stacked by
`Work.Drive.pair33`.  Its zeros are the triples of plane parameters at which the three *perturbed*
classes coincide. -/
def classSystem {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3)
    (p : EuclideanSpace ℝ (Fin m)) (y : Tgt 6) : Tgt 6 :=
  pair33 (qform (A p 0 (V 0 (parOf y 0))) (A p 1 (V 1 (parOf y 1))))
    (qform (A p 0 (V 0 (parOf y 0))) (A p 2 (V 2 (parOf y 2))))

lemma pair33_eq_zero_iff {a b : EuclideanSpace ℝ (Fin 3)} : pair33 a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i
      have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 6) => z (Fin.castAdd 3 i)) h
      rw [pair33_apply_fst] at h1
      exact h1
    · ext i
      have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 6) => z (Fin.natAdd 3 i)) h
      rw [pair33_apply_snd] at h1
      exact h1
  · rintro ⟨rfl, rfl⟩
    ext j
    by_cases hj : j.val < 3
    · rw [pair33_apply_lt _ _ hj]; rfl
    · rw [pair33_apply_ge _ _ hj]; rfl

/-- **The zeros of the class system.**  If the perturbations `A p k` are injective and the lift values
`V k (parOf y k)` are non-zero, then `y` is a zero of the class system exactly when the three perturbed
lift values are pairwise proportional. -/
theorem classSystem_eq_zero_iff {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3)
    (p : EuclideanSpace ℝ (Fin m)) (y : Tgt 6)
    (hVne : ∀ k, V k (parOf y k) ≠ 0) (hAinj : ∀ k, Function.Injective (A p k)) :
    classSystem V A p y = 0 ↔
      (∃ a : ℝ, a • A p 0 (V 0 (parOf y 0)) = A p 1 (V 1 (parOf y 1)))
      ∧ (∃ a : ℝ, a • A p 0 (V 0 (parOf y 0)) = A p 2 (V 2 (parOf y 2))) := by
  have hne : ∀ k, A p k (V k (parOf y k)) ≠ 0 := fun k h =>
    hVne k ((hAinj k) (by simpa using h))
  rw [classSystem, pair33_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Submodule.mem_span_singleton.mp ((qform_kernel _ _ (hne 0)).mp h1),
      Submodule.mem_span_singleton.mp ((qform_kernel _ _ (hne 0)).mp h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨qform_eq_zero_of_mem_span (Submodule.mem_span_singleton.mpr h1),
      qform_eq_zero_of_mem_span (Submodule.mem_span_singleton.mpr h2)⟩

/-! ## 3. Smoothness of the class system -/

/-- Composing the bilinear form `qform` with two smooth maps is smooth. -/
lemma contDiff_qform_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u w : E → Eucl 3} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => qform (u x) (w x)) := by
  rw [contDiff_piLp (p := 2)]
  intro k
  simp only [qform_ofLp, cross_apply, imagPart_ofLp]
  fin_cases k <;> simp <;> fun_prop

/-- The plane parameter map `y ↦ parOf y k` is smooth. -/
lemma contDiff_parOf (k : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Tgt 6 => parOf y k) := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun y : Tgt 6 => WithLp.toLp 2 (fun i : Fin 2 => y (parC k i)))
  fun_prop

/-- **Smoothness of the class system.** -/
lemma contDiff_classSystem {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3)
    (hV : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V k))
    (hA : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin m) × Eucl 3 => A z.1 k z.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => classSystem V A x.1 x.2) := by
  have hv : ∀ k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => A x.1 k (V k (parOf x.2 k))) := by
    intro k
    have hpar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => parOf x.2 k) :=
      (contDiff_parOf k).comp contDiff_snd
    have hVk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => V k (parOf x.2 k)) :=
      (hV k).comp hpar
    have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => (x.1, V k (parOf x.2 k))) :=
      contDiff_fst.prodMk hVk
    exact (hA k).comp hpair
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 =>
        qform (A x.1 0 (V 0 (parOf x.2 0))) (A x.1 1 (V 1 (parOf x.2 1)))) :=
    contDiff_qform_comp (u := fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 =>
        A x.1 0 (V 0 (parOf x.2 0)))
      (w := fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => A x.1 1 (V 1 (parOf x.2 1)))
      (hv 0) (hv 1)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 =>
        qform (A x.1 0 (V 0 (parOf x.2 0))) (A x.1 2 (V 2 (parOf x.2 2)))) :=
    contDiff_qform_comp (u := fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 =>
        A x.1 0 (V 0 (parOf x.2 0)))
      (w := fun x : EuclideanSpace ℝ (Fin m) × Tgt 6 => A x.1 2 (V 2 (parOf x.2 2)))
      (hv 0) (hv 2)
  exact ETM.contDiff_pair33 h1 h2

/-- The same, in the form in which the parametric-Sard statement consumes it (the parameter fixed). -/
lemma contDiff_classSystem_fixed {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3)
    (hV : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V k))
    (hA : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin m) × Eucl 3 => A z.1 k z.2))
    (p : EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Tgt 6 => classSystem V A p y) := by
  have hv : ∀ k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Tgt 6 => A p k (V k (parOf y k))) := by
    intro k
    have hVk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Tgt 6 => V k (parOf y k)) :=
      (hV k).comp (contDiff_parOf k)
    have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Tgt 6 => (p, V k (parOf y k))) :=
      contDiff_const.prodMk hVk
    exact (hA k).comp hpair
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Tgt 6 => qform (A p 0 (V 0 (parOf y 0))) (A p 1 (V 1 (parOf y 1)))) :=
    (by
      have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl 3 × Eucl 3 => qform z.1 z.2) :=
        contDiff_qform
      exact hq.comp ((hv 0).prodMk (hv 1)))
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Tgt 6 => qform (A p 0 (V 0 (parOf y 0))) (A p 2 (V 2 (parOf y 2)))) :=
    (by
      have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl 3 × Eucl 3 => qform z.1 z.2) :=
        contDiff_qform
      exact hq.comp ((hv 0).prodMk (hv 2)))
  exact ETM.contDiff_pair33 h1 h2

/-! ## 4. `qform` as a linear map, and the bijectivity of `pair33` -/

/-- `qform v` as a linear map in the second slot. -/
def qformRight (v : Eucl 3) : Eucl 3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun := qform v
  map_add' a b := by
    change qform v (a + b) = qform v a + qform v b
    rw [qform_add_right]
  map_smul' c a := by
    change qform v (c • a) = c • qform v a
    rw [qform_smul_right]

/-- `qform · v` as a linear map in the first slot. -/
def qformLeft (v : Eucl 3) : Eucl 3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun := fun u => qform u v
  map_add' a b := by
    change qform (a + b) v = qform a v + qform b v
    rw [qform_add_left]
  map_smul' c a := by
    change qform (c • a) v = c • qform a v
    rw [qform_smul_left]

@[simp] lemma qformRight_apply (v w : Eucl 3) : qformRight v w = qform v w := rfl
@[simp] lemma qformLeft_apply (v u : Eucl 3) : qformLeft v u = qform u v := rfl

lemma qformRight_ker (v : Eucl 3) (hv : v ≠ 0) :
    (qformRight v).ker = Submodule.span ℝ ({v} : Set (Eucl 3)) := by
  ext w
  rw [LinearMap.mem_ker, qformRight_apply]
  exact qform_kernel v w hv

/-- **`pair33` is injective.** -/
lemma pair33_injective : Function.Injective
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => pair33 p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have ha : a = a' := by
    ext i
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 6) => z (Fin.castAdd 3 i)) h
    rw [pair33_apply_fst, pair33_apply_fst] at h1
    exact h1
  have hb : b = b' := by
    ext i
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 6) => z (Fin.natAdd 3 i)) h
    rw [pair33_apply_snd, pair33_apply_snd] at h1
    exact h1
  rw [ha, hb]

end

end Work.Drive
