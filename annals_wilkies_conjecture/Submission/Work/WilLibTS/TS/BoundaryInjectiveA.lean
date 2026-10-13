import Mathlib
import Submission.Work.WilLibTS.TS.CompactPeakRatio

namespace Work.WilLibTS.TS

open Set Metric Complex
open scoped Topology
noncomputable section
namespace Wiener
open scoped BigOperators ComplexConjugate Topology
open Set Filter

abbrev Poly := AddMonoidAlgebra ℂ ℤ

noncomputable def weight (n : ℤ) : ℝ := 1+|(n : ℝ)|
lemma weight_pos (n : ℤ) : 0 < weight n := by dsimp [weight]; positivity
lemma one_le_weight (n : ℤ) : 1 ≤ weight n := by simp [weight]
lemma weight_add_le (n m : ℤ) : weight (n+m) ≤ weight n*weight m := by
  dsimp [weight]
  rw [Int.cast_add]
  have h := abs_add_le (n : ℝ) (m : ℝ)
  have hnm : 0 ≤ |(n : ℝ)| * |(m : ℝ)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

noncomputable def wnorm (p : Poly) : ℝ := p.coeff.sum (fun n z => weight n*‖z‖)

lemma wnorm_eq_sum (p : Poly) {s : Finset ℤ} (hs : p.coeff.support ⊆ s) :
    wnorm p = ∑ n ∈ s, weight n*‖p.coeff n‖ :=
  Finsupp.sum_of_support_subset p.coeff hs _ (by simp)

lemma wnorm_nonneg (p : Poly) : 0 ≤ wnorm p := by
  unfold wnorm Finsupp.sum
  exact Finset.sum_nonneg fun n _ => mul_nonneg (weight_pos n).le (norm_nonneg _)

lemma wnorm_zero : wnorm 0 = 0 := by simp [wnorm]

lemma wnorm_add_le (p q : Poly) : wnorm (p+q) ≤ wnorm p+wnorm q := by
  classical
  let s := p.coeff.support ∪ q.coeff.support
  have hp : p.coeff.support ⊆ s := Finset.subset_union_left
  have hq : q.coeff.support ⊆ s := Finset.subset_union_right
  have hpq : (p+q).coeff.support ⊆ s := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  rw [wnorm_eq_sum _ hpq,wnorm_eq_sum _ hp,wnorm_eq_sum _ hq,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  calc weight n*‖p.coeff n+q.coeff n‖ ≤ weight n*(‖p.coeff n‖+‖q.coeff n‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (weight_pos n).le
    _ = _ := by ring

lemma wnorm_neg (p : Poly) : wnorm (-p) = wnorm p := by
  simp [wnorm,Finsupp.sum_neg_index]

lemma wnorm_eq_zero {p : Poly} (hp : wnorm p = 0) : p = 0 := by
  classical
  have hz : ∀ n ∈ p.coeff.support, weight n*‖p.coeff n‖ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun n _ => mul_nonneg (weight_pos n).le (norm_nonneg _))).mp hp
  apply AddMonoidAlgebra.ext
  ext n
  by_cases hn : n ∈ p.coeff.support
  · exact norm_eq_zero.mp ((mul_eq_zero.mp (hz n hn)).resolve_left (weight_pos n).ne')
  · simpa using Finsupp.notMem_support_iff.mp hn

lemma wnorm_single (n : ℤ) (z : ℂ) : wnorm (.single n z) = weight n*‖z‖ := by
  unfold wnorm
  rw [AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

lemma wnorm_sum_le {ι : Type*} (s : Finset ι) (p : ι → Poly) :
    wnorm (∑ i ∈ s, p i) ≤ ∑ i ∈ s, wnorm (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (wnorm_add_le _ _).trans (add_le_add (le_refl _) ih)

lemma wnorm_mul_le (p q : Poly) : wnorm (p*q) ≤ wnorm p*wnorm q := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  calc
    _ ≤ ∑ n ∈ p.coeff.support,
        ∑ m ∈ q.coeff.support, wnorm (.single (n+m) (p.coeff n*q.coeff m)) :=
      (wnorm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => wnorm_sum_le _ _)
    _ ≤ ∑ n ∈ p.coeff.support,
        ∑ m ∈ q.coeff.support, (weight n*‖p.coeff n‖)*(weight m*‖q.coeff m‖) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro m _
      rw [wnorm_single,norm_mul]
      calc _ ≤ (weight n*weight m)*(‖p.coeff n‖*‖q.coeff m‖) :=
              mul_le_mul_of_nonneg_right (weight_add_le n m) (by positivity)
        _ = _ := by ring
    _ = wnorm p*wnorm q := by simp only [wnorm,Finsupp.sum,Finset.sum_mul_sum]

noncomputable def ringNorm : RingNorm Poly where
  toFun := wnorm
  map_zero' := wnorm_zero
  add_le' := wnorm_add_le
  neg' := wnorm_neg
  mul_le' := wnorm_mul_le
  eq_zero_of_map_eq_zero' := fun _ => wnorm_eq_zero

noncomputable instance : NormedCommRing Poly where
  toNormedRing := ringNorm.toNormedRing
  mul_comm := mul_comm

lemma norm_def (p : Poly) : ‖p‖ = wnorm p := rfl

lemma wnorm_smul (c : ℂ) (p : Poly) : wnorm (c • p) = ‖c‖*wnorm p := by
  unfold wnorm
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (by simp)]
  simp only [norm_mul,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

noncomputable instance : NormedAlgebra ℂ Poly where
  toAlgebra := inferInstance
  norm_smul_le c p := (wnorm_smul c p).le

noncomputable instance : NormOneClass Poly where
  norm_one := by
    change wnorm (1 : Poly) = 1
    rw [AddMonoidAlgebra.one_def,wnorm_single]
    simp [weight]

abbrev Space := UniformSpace.Completion Poly

example : NormedCommRing Space := inferInstance
example : NormedAlgebra ℂ Space := inferInstance
example : CompleteSpace Space := inferInstance

section Modes
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def modesLinear (v : ℤ → F) : Poly →ₗ[ℂ] F :=
  (Finsupp.linearCombination ℂ v).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

lemma modesLinear_apply (v : ℤ → F) (p : Poly) :
    modesLinear v p = p.coeff.sum (fun n z => z • v n) := rfl

lemma modesLinear_bound (v : ℤ → F) {C : ℝ} (hv : ∀ n, ‖v n‖ ≤ C*weight n)
    (p : Poly) : ‖modesLinear v p‖ ≤ C*‖p‖ := by
  simp only [modesLinear_apply,norm_def,wnorm,Finsupp.sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_smul]
  calc ‖p.coeff n‖*‖v n‖ ≤ ‖p.coeff n‖*(C*weight n) :=
        mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)
    _ = _ := by ring

def modesCLM (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) : Poly →L[ℂ] F :=
  (modesLinear v).mkContinuous C (modesLinear_bound v hv)

variable [CompleteSpace F]
def fromModes (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) : Space →L[ℂ] F :=
  (modesCLM v C hv).extend UniformSpace.Completion.toComplL

lemma fromModes_coe (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) (p : Poly) :
    fromModes v C hv (p : Space) = p.coeff.sum (fun n z => z • v n) :=
  (modesCLM v C hv).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe Poly) p

lemma fromModes_bound (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) (f : Space) :
    ‖fromModes v C hv f‖ ≤ C*‖f‖ := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih p =>
    rw [fromModes_coe,UniformSpace.Completion.norm_coe]
    exact modesLinear_bound v hv p

lemma fromModes_single (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n)
    (n : ℤ) (z : ℂ) :
    fromModes v C hv ((AddMonoidAlgebra.single n z : Poly) : Space) = z • v n := by
  rw [fromModes_coe,AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)
end Modes

instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev Circle := AddCircle (1 : ℝ)

def boundary : Space →L[ℂ] C(Circle,ℂ) :=
  fromModes (fun n => fourier n) 1 (fun n => by simpa only [fourier_norm,one_mul] using one_le_weight n)

lemma boundary_coe (p : Poly) :
    boundary (p : Space) = p.coeff.sum (fun n z => z • fourier n) :=
  fromModes_coe _ _ _ _

lemma boundary_single (n : ℤ) (z : ℂ) :
    boundary ((AddMonoidAlgebra.single n z : Poly) : Space) = z • fourier n :=
  fromModes_single _ _ _ _ _

lemma boundary_norm_le (f : Space) : ‖boundary f‖ ≤ ‖f‖ := by
  simpa only [boundary,one_mul] using fromModes_bound (fun n => (fourier n : C(Circle,ℂ))) 1 (fun n => by simpa only [fourier_norm,one_mul] using one_le_weight n) f

lemma boundary_one : boundary 1 = 1 := by
  rw [← UniformSpace.Completion.coe_one]
  change boundary ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = 1
  rw [boundary_single,one_smul]
  ext; exact fourier_zero

lemma boundary_poly_mul (p q : Poly) : boundary ((p*q : Poly) : Space) =
    boundary (p : Space)*boundary (q : Space) := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  change boundary ((UniformSpace.Completion.toComplL : Poly →L[ℂ] Space) (∑ a ∈ p.coeff.support,
    ∑ b ∈ q.coeff.support, AddMonoidAlgebra.single (a+b) (p.coeff a*q.coeff b))) = _
  simp only [map_sum]
  change (∑ a ∈ p.coeff.support, ∑ b ∈ q.coeff.support,
    boundary ((AddMonoidAlgebra.single (a+b) (p.coeff a*q.coeff b) : Poly) : Space)) = _
  simp_rw [boundary_single]
  rw [boundary_coe,boundary_coe]
  simp only [Finsupp.sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  ext θ
  simp only [ContinuousMap.smul_apply,smul_eq_mul,ContinuousMap.mul_apply,fourier_add]
  ring

lemma boundary_mul (f g : Space) : boundary (f*g) = boundary f*boundary g := by
  induction f,g using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p q => simpa only [← UniformSpace.Completion.coe_mul] using boundary_poly_mul p q

def boundaryAlgHom : Space →ₐ[ℂ] C(Circle,ℂ) where
  toFun := boundary
  map_one' := boundary_one
  map_mul' := boundary_mul
  map_zero' := map_zero boundary
  map_add' := map_add boundary
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,map_smul,boundary_one]

lemma poly_expansion (p : Poly) :
    (p : Space) = ∑ n ∈ p.coeff.support, ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  change (UniformSpace.Completion.toComplL : Poly →L[ℂ] Space) (∑ n ∈ p.coeff.support,
    AddMonoidAlgebra.single n (p.coeff n)) = _
  exact map_sum _ _ _

lemma continuous_eq_of_single {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : Space → F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p : Poly, f (p : Space) = g (p : Space)) : f = g := by
  ext x
  exact UniformSpace.Completion.denseRange_coe.induction_on x (isClosed_eq hf hg) h

def conjPoly : Poly →ₗ[ℝ] Poly :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℝ (fun n : ℤ => -n)).comp
      ((Finsupp.mapRange.linearMap Complex.conjCLE.toLinearMap).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap))

lemma conjPoly_coeff (p : Poly) :
    (conjPoly p).coeff = (p.coeff.mapRange (starRingEnd ℂ) (map_zero _)).mapDomain (fun n => -n) := rfl

lemma conjPoly_single (n : ℤ) (z : ℂ) :
    conjPoly (.single n z) = .single (-n) (conj z) := by
  apply AddMonoidAlgebra.ext
  rw [conjPoly_coeff]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.mapRange_single,Finsupp.mapDomain_single]

lemma conjPoly_norm (p : Poly) : ‖conjPoly p‖ = ‖p‖ := by
  change wnorm (conjPoly p) = wnorm p
  unfold wnorm
  rw [conjPoly_coeff,Finsupp.sum_mapDomain_index_inj (neg_injective : Function.Injective (fun n : ℤ => -n)),
    Finsupp.sum_mapRange_index (by simp)]
  simp [weight]

def conjugate : Space →L[ℝ] Space :=
  ((UniformSpace.Completion.toComplL : Poly →L[ℝ] Space).comp
    (conjPoly.mkContinuous 1 (by intro p; simp [conjPoly_norm]))).extend
      UniformSpace.Completion.toComplL

lemma conjugate_coe (p : Poly) : conjugate (p : Space) = (conjPoly p : Space) := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe Poly) p

lemma conjugate_single (n : ℤ) (z : ℂ) :
    conjugate ((AddMonoidAlgebra.single n z : Poly) : Space) =
      ((AddMonoidAlgebra.single (-n) (conj z) : Poly) : Space) := by
  rw [conjugate_coe,conjPoly_single]

lemma conjugate_norm (f : Space) : ‖conjugate f‖ = ‖f‖ := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p => rw [conjugate_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe,conjPoly_norm]

lemma conjugate_involutive : Function.Involutive conjugate := by
  intro f
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_id
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,neg_neg,starRingEnd_self_apply]

lemma boundary_conjugate (f : Space) (θ : Circle) :
    boundary (conjugate f) θ = conj (boundary f θ) := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,boundary_single,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,map_mul]
    apply Finset.sum_congr rfl
    intro _ _
    rw [fourier_neg]

def multiplier (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) : Space →L[ℂ] Space :=
  fromModes (fun n => ((AddMonoidAlgebra.single n (σ n) : Poly) : Space)) C (by
    intro n
    rw [UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
    calc weight n*‖σ n‖ ≤ weight n*C := mul_le_mul_of_nonneg_left (hσ n) (weight_pos n).le
      _ = C*weight n := mul_comm _ _)

lemma multiplier_single (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) (n : ℤ) (z : ℂ) :
    multiplier σ C hσ ((AddMonoidAlgebra.single n z : Poly) : Space) =
      ((AddMonoidAlgebra.single n (z*σ n) : Poly) : Space) := by
  rw [multiplier,fromModes_single]
  rw [← UniformSpace.Completion.coe_smul]
  congr 1
  apply AddMonoidAlgebra.ext
  ext m
  simp only [AddMonoidAlgebra.coeff_smul,AddMonoidAlgebra.coeff_single,Finsupp.smul_apply,
    Finsupp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

lemma multiplier_bound (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) (f : Space) :
    ‖multiplier σ C hσ f‖ ≤ C*‖f‖ := fromModes_bound _ _ _ _

def hilbertSymbol (n : ℤ) : ℂ := if 0 < n then Complex.I else if n < 0 then -Complex.I else 0

lemma hilbertSymbol_bound (n : ℤ) : ‖hilbertSymbol n‖ ≤ 1 := by
  unfold hilbertSymbol
  split_ifs <;> simp

lemma hilbertSymbol_neg (n : ℤ) : hilbertSymbol (-n) = conj (hilbertSymbol n) := by
  unfold hilbertSymbol
  split_ifs <;> simp_all
  all_goals omega

def hilbert : Space →L[ℂ] Space := multiplier hilbertSymbol 1 hilbertSymbol_bound

lemma hilbert_norm (f : Space) : ‖hilbert f‖ ≤ ‖f‖ := by
  simpa only [hilbert,one_mul] using multiplier_bound hilbertSymbol 1 hilbertSymbol_bound f

lemma hilbert_conjugate (f : Space) : hilbert (conjugate f) = conjugate (hilbert f) := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,hilbert,multiplier_single]
    apply Finset.sum_congr rfl
    intro _ _
    rw [hilbertSymbol_neg,map_mul]

def realSubspace : Submodule ℝ Space := LinearMap.ker (conjugate.toLinearMap-LinearMap.id)

lemma mem_realSubspace {f : Space} : f ∈ realSubspace ↔ conjugate f = f := by
  simp [realSubspace,sub_eq_zero]

lemma realSubspace_closed : IsClosed (realSubspace : Set Space) := by
  change IsClosed {f : Space | conjugate f - f = 0}
  exact isClosed_eq (by fun_prop) continuous_const

instance : CompleteSpace realSubspace := realSubspace_closed.completeSpace_coe

lemma real_boundary {f : Space} (hf : f ∈ realSubspace) (θ : Circle) : (boundary f θ).im = 0 := by
  have h := boundary_conjugate f θ
  rw [mem_realSubspace.mp hf] at h
  exact (Complex.conj_eq_iff_im).mp h.symm

lemma hilbert_real {f : Space} (hf : f ∈ realSubspace) : hilbert f ∈ realSubspace := by
  rw [mem_realSubspace,← hilbert_conjugate,mem_realSubspace.mp hf]

abbrev ClosedDisc := Metric.closedBall (0 : ℂ) 1

def schwarzMode (n : ℤ) (z : ℂ) : ℂ :=
  if 0 < n then Complex.I * (2*z^n.toNat-1) else Complex.I

lemma schwarzMode_continuous (n : ℤ) : Continuous (schwarzMode n) := by
  unfold schwarzMode
  split_ifs <;> fun_prop

lemma schwarzMode_differentiable (n : ℤ) : Differentiable ℂ (schwarzMode n) := by
  unfold schwarzMode
  split_ifs <;> fun_prop

lemma schwarzMode_bound (n : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖schwarzMode n z‖ ≤ 3 := by
  unfold schwarzMode
  split_ifs
  · rw [norm_mul,Complex.norm_I,one_mul]
    calc ‖2*z^n.toNat-1‖ ≤ ‖2*z^n.toNat‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2*‖z‖^n.toNat+1 := by simp
      _ ≤ 3 := by have := (pow_le_one₀ (n := n.toNat) (norm_nonneg z) hz); linarith
  · simp

