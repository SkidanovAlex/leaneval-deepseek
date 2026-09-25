/-
# Regularity of the formal adjoint `pertAdj A φ f`

The formal adjoint of the perturbed `∂̄`-operator (see `Work.NN.Assemble.pertDefs`) is built out
of the coefficient family `F_j = pertCoef f j` of a `(0,1)`-form `f`, the derivatives of `A`, the
first derivatives of the weight `φ`, and the first derivatives of `F_j`.  Here we record that

* every one of the building blocks is `C^∞` as soon as `A`, `φ` and `f` are, and
* every one of them has compact support as soon as `f` does.

The two ingredients for the second point are: the `fderiv` of a compactly supported function is
compactly supported (`HasCompactSupport.fderiv`) and vanishes outside `tsupport`
(`fderiv_of_notMem_tsupport`); hence `z ↦ fderiv ℝ F_j z (V z)` is compactly supported for *any*
`V`, in particular for `V = A · e_j`.
-/
import Mathlib
import Submission.Work.NN.Assemble.pertDefs

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Work.NN.Assemble

/-! ### Smoothness of the building blocks -/

/-- A smooth function has a smooth `fderiv` applied to a constant vector. -/
lemma contDiff_fderiv_apply_const {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Cn n → E} (hu : ∀ m : ℕ, ContDiff ℝ m u) (v : Cn n) :
    ∀ m : ℕ, ContDiff ℝ m (fun z => fderiv ℝ u z v) := by
  intro m
  have hfd : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ u) :=
    (hu (m + 1)).fderiv_right (m := (m : WithTop ℕ∞)) (by simp)
  exact hfd.clm_apply (contDiff_const (c := v))

/-- A smooth function has a smooth `fderiv` applied to a smooth vector field. -/
lemma contDiff_fderiv_apply_varying {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Cn n → E} {V : Cn n → Cn n}
    (hu : ∀ m : ℕ, ContDiff ℝ m u) (hV : ∀ m : ℕ, ContDiff ℝ m V) :
    ∀ m : ℕ, ContDiff ℝ m (fun z => fderiv ℝ u z (V z)) := by
  intro m
  have hfd : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ u) :=
    (hu (m + 1)).fderiv_right (m := (m : WithTop ℕ∞)) (by simp)
  exact hfd.clm_apply (hV m)

/-- `∂_j u` (flat model) is smooth when `u` is. -/
lemma contDiff_dCoord_all {n : ℕ} {u : Cn n → ℂ} (hu : ∀ m : ℕ, ContDiff ℝ m u) (j : Fin n) :
    ∀ m : ℕ, ContDiff ℝ m (fun z => Work.CR.Flat.dCoord j u z) := by
  intro m
  have h1 := contDiff_fderiv_apply_const hu (Pi.single j (1 : ℂ)) m
  have h2 := contDiff_fderiv_apply_const hu (Pi.single j (Complex.I : ℂ)) m
  have h3 : ContDiff ℝ m
      (fun z => (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single j (1 : ℂ))
        - Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ)))) :=
    contDiff_const.mul (h1.sub (contDiff_const.mul h2))
  simpa only [Work.CR.Flat.dCoord] using h3

/-- `∂_j φ` (flat model) is smooth when the real weight `φ` is. -/
lemma contDiff_dPh_all {n : ℕ} {φ : Cn n → ℝ} (hφ : ∀ m : ℕ, ContDiff ℝ m φ) (j : Fin n) :
    ∀ m : ℕ, ContDiff ℝ m (fun z => dPh j φ z) := by
  intro m
  have h1 : ContDiff ℝ m (fun z => (fderiv ℝ φ z (Pi.single j (1 : ℂ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_fderiv_apply_const (u := φ) hφ (Pi.single j (1 : ℂ)) m)
  have h2 : ContDiff ℝ m (fun z => (fderiv ℝ φ z (Pi.single j (Complex.I : ℂ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_fderiv_apply_const (u := φ) hφ (Pi.single j (Complex.I : ℂ)) m)
  have h3 : ContDiff ℝ m
      (fun z => (1 / 2 : ℂ) * ((fderiv ℝ φ z (Pi.single j (1 : ℂ)) : ℂ)
        - Complex.I * (fderiv ℝ φ z (Pi.single j (Complex.I : ℂ)) : ℂ))) :=
    contDiff_const.mul (h1.sub (contDiff_const.mul h2))
  simpa only [dPh] using h3

/-- The divergence `pertDiv A j` is smooth when `A` is. -/
lemma contDiff_pertDiv {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} (hA : ∀ m : ℕ, ContDiff ℝ m A)
    (j : Fin n) : ∀ m : ℕ, ContDiff ℝ m (pertDiv A j) := by
  intro m
  have hcoord : ∀ k : Fin n, ∀ m : ℕ, ContDiff ℝ m (fun z => A z (eb n j) k) := by
    intro k m
    have hW : ContDiff ℝ m (fun z => A z (eb n j)) := (hA m).clm_apply contDiff_const
    exact (contDiff_apply ℝ ℂ k).comp hW
  have hd : ContDiff ℝ m
      (fun z => ∑ k, (Work.CR.Flat.dCoord k (fun z' => A z' (eb n j) k) z).re) :=
    ContDiff.sum (s := Finset.univ) (fun k _ =>
      Complex.reCLM.contDiff.comp (contDiff_dCoord_all (hcoord k) k m))
  have hd' : ContDiff ℝ m
      (fun z => ((∑ k, (Work.CR.Flat.dCoord k (fun z' => A z' (eb n j) k) z).re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hd
  have h4 : ContDiff ℝ m (fun z : Cn n =>
      (2 : ℂ) * ((∑ k, (Work.CR.Flat.dCoord k (fun z' => A z' (eb n j) k) z).re : ℝ) : ℂ)) :=
    (contDiff_const (c := (2 : ℂ))).mul hd'
  show ContDiff ℝ m (fun z : Cn n =>
      (2 : ℂ) * ((∑ k, (Work.CR.Flat.dCoord k (fun z' => A z' (eb n j) k) z).re : ℝ) : ℂ))
  exact h4

/-! ### Compact support of the building blocks -/

/-- `fderiv ℝ u · V` has compact support when `u` does, for any `V` whatsoever. -/
lemma hasCompactSupport_fderiv_apply_varying {n : ℕ} {u : Cn n → ℂ} (hu : HasCompactSupport u)
    (V : Cn n → Cn n) : HasCompactSupport (fun z => fderiv ℝ u z (V z)) := by
  refine (hu.fderiv ℝ).mono' ?_
  intro z hz
  refine subset_tsupport _ (Function.mem_support.mpr fun h0 => hz ?_)
  simp [h0]

/-- `∂_j u` (flat model) has compact support when `u` does. -/
lemma hasCompactSupport_dCoord_flat {n : ℕ} {u : Cn n → ℂ} (hu : HasCompactSupport u)
    (j : Fin n) : HasCompactSupport (fun z => Work.CR.Flat.dCoord j u z) := by
  have h := (hu.fderiv ℝ).comp_left
    (g := fun L : Cn n →L[ℝ] ℂ =>
      (1 / 2 : ℂ) * (L (Pi.single j (1 : ℂ)) - Complex.I * L (Pi.single j (Complex.I : ℂ))))
    (by simp)
  simpa only [Work.CR.Flat.dCoord, Function.comp_def] using h

/-- A finite sum of compactly supported functions is compactly supported. -/
lemma hasCompactSupport_sum_univ {ι X Y : Type*} [TopologicalSpace X] [AddCommMonoid Y]
    {s : Finset ι} {F : ι → X → Y} (h : ∀ i ∈ s, HasCompactSupport (F i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, F i x) := by
  have hF : HasCompactSupport (∑ i ∈ s, F i) := HasCompactSupport.finset_sum h
  refine hF.mono ?_
  intro x hx
  simp only [Function.mem_support, Finset.sum_apply] at hx ⊢
  exact hx

/-! ### The theorem -/

/-- The formal adjoint function `pertAdj A φ f` is smooth and compactly supported when `A` and `φ` are smooth and `f` is smooth with compact support. -/
theorem pertAdjRegular {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {φ : Cn n → ℝ}
    (hA : ∀ m : ℕ, ContDiff ℝ m A) (hφ : ∀ m : ℕ, ContDiff ℝ m φ)
    {f : Cn n → Cn n →L[ℝ] ℂ} (hf : ∀ m : ℕ, ContDiff ℝ m f) (hfs : HasCompactSupport f) :
    (∀ m : ℕ, ContDiff ℝ m (pertAdj A φ f)) ∧ HasCompactSupport (pertAdj A φ f) := by
  have hg : ∀ j : Fin n, ∀ m : ℕ, ContDiff ℝ m (pertCoef f j) := fun j => contDiff_pertCoef hf j
  have hgc : ∀ j : Fin n, HasCompactSupport (pertCoef f j) :=
    fun j => hasCompactSupport_pertCoef hfs j
  have hAvec : ∀ j : Fin n, ∀ m : ℕ, ContDiff ℝ m (fun z => A z (eb n j)) :=
    fun j m => (hA m).clm_apply contDiff_const
  have hpert : pertAdj A φ f = (fun z : Cn n => dbarSt φ (pertCoef f) z + (Complex.I / 2) * ∑ j,
      ((fderiv ℝ (pertCoef f j) z) (A z (eb n j))
        + pertCoef f j z * pertDiv A j z
        - pertCoef f j z * ((fderiv ℝ φ z (A z (eb n j)) : ℝ) : ℂ))) := rfl
  rw [hpert]
  constructor
  · intro m
    have hdc : ∀ j : Fin n, ContDiff ℝ m (fun z => Work.CR.Flat.dCoord j (pertCoef f j) z) :=
      fun j => contDiff_dCoord_all (hg j) j m
    have hdph : ∀ j : Fin n, ContDiff ℝ m (fun z => dPh j φ z) := fun j => contDiff_dPh_all hφ j m
    have hT1 : ∀ j : Fin n,
        ContDiff ℝ m (fun z => (fderiv ℝ (pertCoef f j) z) (A z (eb n j))) :=
      fun j => contDiff_fderiv_apply_varying (hg j) (hAvec j) m
    have hT2 : ∀ j : Fin n, ContDiff ℝ m (fun z => pertCoef f j z * pertDiv A j z) :=
      fun j => (hg j m).mul (contDiff_pertDiv hA j m)
    have hT3 : ∀ j : Fin n,
        ContDiff ℝ m (fun z => pertCoef f j z * ((fderiv ℝ φ z (A z (eb n j)) : ℝ) : ℂ)) :=
      fun j => (hg j m).mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_fderiv_apply_varying hφ (hAvec j) m))
    have hdbar : ContDiff ℝ m (fun z => dbarSt φ (pertCoef f) z) := by
      have hinner : ContDiff ℝ m (fun z => ∑ j,
          (Work.CR.Flat.dCoord j (pertCoef f j) z - pertCoef f j z * dPh j φ z)) :=
        ContDiff.sum (s := Finset.univ) (fun j _ => (hdc j).sub ((hg j m).mul (hdph j)))
      simpa only [dbarSt] using hinner.neg
    have hsum : ContDiff ℝ m (fun z => ∑ j,
        ((fderiv ℝ (pertCoef f j) z) (A z (eb n j))
          + pertCoef f j z * pertDiv A j z
          - pertCoef f j z * ((fderiv ℝ φ z (A z (eb n j)) : ℝ) : ℂ))) :=
      ContDiff.sum (s := Finset.univ) (fun j _ => ((hT1 j).add (hT2 j)).sub (hT3 j))
    exact hdbar.add ((contDiff_const (c := (Complex.I / 2))).mul hsum)
  · have hdc : ∀ j : Fin n,
        HasCompactSupport (fun z => Work.CR.Flat.dCoord j (pertCoef f j) z) :=
      fun j => hasCompactSupport_dCoord_flat (hgc j) j
    have hdph : ∀ j : Fin n, HasCompactSupport (fun z => pertCoef f j z * dPh j φ z) :=
      fun j => (hgc j).mul_right
    have hT1 : ∀ j : Fin n,
        HasCompactSupport (fun z => (fderiv ℝ (pertCoef f j) z) (A z (eb n j))) :=
      fun j => hasCompactSupport_fderiv_apply_varying (hgc j) (fun z => A z (eb n j))
    have hT2 : ∀ j : Fin n, HasCompactSupport (fun z => pertCoef f j z * pertDiv A j z) :=
      fun j => (hgc j).mul_right
    have hT3 : ∀ j : Fin n,
        HasCompactSupport (fun z => pertCoef f j z * ((fderiv ℝ φ z (A z (eb n j)) : ℝ) : ℂ)) :=
      fun j => (hgc j).mul_right
    have hdbar : HasCompactSupport (fun z => dbarSt φ (pertCoef f) z) := by
      have hinner : HasCompactSupport (fun z : Cn n => -∑ j,
          (Work.CR.Flat.dCoord j (pertCoef f j) z - pertCoef f j z * dPh j φ z)) :=
        (hasCompactSupport_sum_univ (s := Finset.univ)
          (fun j _ => (hdc j).sub (hdph j))).comp_left (g := fun w : ℂ => -w) (by simp)
      simpa only [dbarSt] using hinner
    have hsum : HasCompactSupport (fun z => ∑ j,
        ((fderiv ℝ (pertCoef f j) z) (A z (eb n j))
          + pertCoef f j z * pertDiv A j z
          - pertCoef f j z * ((fderiv ℝ φ z (A z (eb n j)) : ℝ) : ℂ))) :=
      hasCompactSupport_sum_univ (s := Finset.univ)
        (fun j _ => ((hT1 j).add (hT2 j)).sub (hT3 j))
    exact hdbar.add hsum.mul_left

end Work.NN.Assemble
