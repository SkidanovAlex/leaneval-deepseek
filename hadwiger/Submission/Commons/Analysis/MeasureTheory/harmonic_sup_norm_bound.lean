import Mathlib
import Submission.Commons.Analysis.MeasureTheory.sphere_restriction_pairing_pos
import Submission.Commons.Algebra.MvPolynomial.exists_harmonic_orthonormal_basis
import Submission.Commons.Analysis.MeasureTheory.sphere_linearIsometry_measurePreserving
import Submission.Commons.Analysis.MeasureTheory.sphere_isometry_measurableEquiv_measurePreserving
import Submission.Commons.Analysis.MeasureTheory.cosine_harmonic_scalar
import Submission.Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule
import Submission.Commons.Algebra.MvPolynomial.finrank_harmHom_add
import Submission.Commons.Algebra.Binomial.harmonic_dim_arith

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Commons.Analysis.MeasureTheory

open Commons.Algebra.MvPolynomial (harmHom harmBilin harmPair mem_harmHom harmBilin_apply
  harmBilin_isSymm harmBilin_pos eval_smul_sphere lapLM lapLM_apply)

private abbrev hE (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev hS (n : ℕ) := Metric.sphere (0 : hE n) 1

private def hev {n : ℕ} (θ : hS n) (P : MvPolynomial (Fin n) ℝ) : ℝ :=
  MvPolynomial.eval (fun l : Fin n => (θ : hE n) l) P

@[simp] private lemma hev_def {n : ℕ} (θ : hS n) (P : MvPolynomial (Fin n) ℝ) :
    hev θ P = MvPolynomial.eval (fun l : Fin n => (θ : hE n) l) P := rfl

private lemma hev_add {n : ℕ} (θ : hS n) (P Q : MvPolynomial (Fin n) ℝ) :
    hev θ (P + Q) = hev θ P + hev θ Q := MvPolynomial.eval_add

private lemma hev_smul {n : ℕ} (θ : hS n) (c : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    hev θ (c • P) = c * hev θ P :=
  eval_smul_sphere n c P θ

private lemma hev_sum {n : ℕ} {ι : Type*} (θ : hS n) (s : Finset ι)
    (F : ι → MvPolynomial (Fin n) ℝ) :
    hev θ (∑ i ∈ s, F i) = ∑ i ∈ s, hev θ (F i) :=
  MvPolynomial.eval_sum s F _

/-! ### The `L²`-pairing on `harmHom` -/

private lemma hb_symm {n k : ℕ} [Nonempty (Fin n)] (x y : harmHom n k) :
    harmBilin n k x y = harmBilin n k y x :=
  (harmBilin_isSymm (n := n) (k := k)).eq x y

private lemma hb_integral {n k : ℕ} [Nonempty (Fin n)] (x y : harmHom n k) :
    harmBilin n k x y =
      ∫ θ : hS n, hev θ (x : MvPolynomial (Fin n) ℝ) * hev θ (y : MvPolynomial (Fin n) ℝ)
        ∂(volume.toSphere : Measure (hS n)) := by
  rw [harmBilin_apply]
  rfl

private lemma hb_self_eq_zero {n k : ℕ} [Nonempty (Fin n)] (x : harmHom n k)
    (h : harmBilin n k x x = 0) : x = 0 := by
  by_contra hx
  exact absurd h (ne_of_gt (harmBilin_pos x hx))

private lemma hb_eq_of_forall {n k : ℕ} [Nonempty (Fin n)] {x y : harmHom n k}
    (h : ∀ f : harmHom n k, harmBilin n k x f = harmBilin n k y f) : x = y := by
  have h0 : (x - y) = 0 := by
    apply hb_self_eq_zero
    have hxy := h (x - y)
    have hsym := hb_symm x y
    simp only [map_sub, LinearMap.sub_apply] at hxy ⊢
    linarith
  exact sub_eq_zero.mp h0

/-! ### Expansion in an orthonormal basis -/

private lemma hb_basis_apply {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (l : Fin d) (c : Fin d → ℝ) :
    harmBilin n k (b l) (∑ i, c i • b i) = c l := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · rw [horth l l, if_pos rfl, mul_one]
  · intro i _ hi
    rw [horth l i, if_neg (Ne.symm hi), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

private lemma harm_sum_apply {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k) (c : Fin d → ℝ) (w : harmHom n k) :
    harmBilin n k (∑ i, c i • b i) w = ∑ i, c i * harmBilin n k (b i) w := by
  rw [map_sum]
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

private lemma hb_basis_pairing {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (c : Fin d → ℝ) :
    harmBilin n k (∑ i, c i • b i) (∑ j, c j • b j) = ∑ j, (c j) ^ 2 := by
  rw [harm_sum_apply b c (∑ j, c j • b j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb_basis_apply b horth i c]
  ring

private lemma hb_expand {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (f : harmHom n k) :
    f = ∑ j, harmBilin n k (b j) f • b j := by
  let z : harmHom n k := f - ∑ j, harmBilin n k (b j) f • b j
  have hz : ∀ l : Fin d, harmBilin n k (b l) z = 0 := by
    intro l
    have hbl : harmBilin n k (b l) (∑ j, harmBilin n k (b j) f • b j) =
        harmBilin n k (b l) f := hb_basis_apply b horth l (fun j => harmBilin n k (b j) f)
    simp only [z, map_sub, LinearMap.sub_apply, hbl, sub_self]
  have hzz : harmBilin n k z z = 0 := by
    have hzmem : z ∈ Submodule.span ℝ (Set.range b) := by rw [hspan]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hzmem
    obtain ⟨c, hc⟩ := hzmem
    have h1 : harmBilin n k z z = ∑ i, c i * harmBilin n k (b i) z := by
      nth_rewrite 1 [hc.symm]
      rw [harm_sum_apply b c z]
    rw [h1]
    simp [hz]
  have : z = 0 := hb_self_eq_zero z hzz
  exact sub_eq_zero.mp this

private lemma hev_expand {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (f : harmHom n k) (θ : hS n) :
    hev θ (f : MvPolynomial (Fin n) ℝ) =
      ∑ j, harmBilin n k (b j) f * hev θ (b j : MvPolynomial (Fin n) ℝ) := by
  have hcoe : ((∑ j, harmBilin n k (b j) f • b j : harmHom n k) : MvPolynomial (Fin n) ℝ)
      = ∑ j, harmBilin n k (b j) f • (b j : MvPolynomial (Fin n) ℝ) := by
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Submodule.coe_smul]
  have hf := hb_expand b horth hspan f
  have heq : hev θ (f : MvPolynomial (Fin n) ℝ)
      = hev θ ((∑ j, harmBilin n k (b j) f • b j : harmHom n k) : MvPolynomial (Fin n) ℝ) :=
    congrArg (fun x : harmHom n k => hev θ (x : MvPolynomial (Fin n) ℝ)) hf
  rw [heq, hcoe, hev_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hev_smul]

private lemma hb_sum_coeff_sq {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (f : harmHom n k) :
    ∑ j, (harmBilin n k (b j) f) ^ 2 = harmBilin n k f f := by
  have hff : harmBilin n k f f = ∑ j, (harmBilin n k (b j) f) ^ 2 := by
    have hf := hb_expand b horth hspan f
    conv_lhs => rw [hf]
    rw [hb_basis_pairing b horth (fun j => harmBilin n k (b j) f)]
  exact hff.symm

private lemma hev_sq_le {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (f : harmHom n k) (θ : hS n) :
    (hev θ (f : MvPolynomial (Fin n) ℝ)) ^ 2 ≤
      harmBilin n k f f *
        (∑ j, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2) := by
  rw [hev_expand b horth hspan f θ]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin d => harmBilin n k (b j) f)
    (fun j : Fin d => hev θ (b j : MvPolynomial (Fin n) ℝ))
  rw [hb_sum_coeff_sq b horth hspan f] at hcs
  exact hcs

/-! ### The reproducing vector and the kernel diagonal -/

private noncomputable def hR {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k) (θ : hS n) : harmHom n k :=
  ∑ j, hev θ (b j : MvPolynomial (Fin n) ℝ) • b j

private noncomputable def hK {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k) (θ : hS n) : ℝ :=
  ∑ j, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2

private lemma hb_reproduce {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (θ : hS n) (f : harmHom n k) :
    harmBilin n k (hR b θ) f = hev θ (f : MvPolynomial (Fin n) ℝ) := by
  have hRval : hR b θ = ∑ j, hev θ (b j : MvPolynomial (Fin n) ℝ) • b j := rfl
  rw [hRval, harm_sum_apply b (fun j => hev θ (b j : MvPolynomial (Fin n) ℝ)) f,
      hev_expand b horth hspan f θ]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma hb_R_self {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (θ : hS n) :
    harmBilin n k (hR b θ) (hR b θ) = hK b θ := by
  have hRval : hR b θ = ∑ j, hev θ (b j : MvPolynomial (Fin n) ℝ) • b j := rfl
  rw [hRval, hb_basis_pairing b horth (fun j => hev θ (b j : MvPolynomial (Fin n) ℝ))]
  rfl

private lemma hK_eq {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (θ : hS n) :
    hK b θ = harmBilin n k (hR b θ) (hR b θ) := (hb_R_self b horth θ).symm

/-! ### Rotation invariance of the kernel diagonal -/

private noncomputable def sphMap {n : ℕ} (A : hE n ≃ₗᵢ[ℝ] hE n) (θ : hS n) : hS n :=
  ⟨A (θ : hE n), mem_sphere_zero_iff_norm.mpr (by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.mp θ.2)⟩

@[simp] private lemma sphMap_val {n : ℕ} (A : hE n ≃ₗᵢ[ℝ] hE n) (θ : hS n) :
    ((sphMap A θ : hS n) : hE n) = A (θ : hE n) := rfl

private lemma hsubstA_mem_harmHom {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n)
    {P : MvPolynomial (Fin n) ℝ} (hP : P ∈ harmHom n k) :
    Fh2.substA n A P ∈ harmHom n k := by
  rw [mem_harmHom] at hP ⊢
  refine ⟨Fh2.substA_mem_homogeneous n A hP.1, ?_⟩
  rw [lapLM_apply, Fh2.substA_lap]
  have h0 : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 := by
    rw [← lapLM_apply]; exact hP.2
  rw [h0]
  simp [Fh2.substA]

private noncomputable def hTA {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n) :
    harmHom n k → harmHom n k :=
  fun f => ⟨Fh2.substA n A (f : MvPolynomial (Fin n) ℝ), hsubstA_mem_harmHom A f.2⟩

private lemma hTA_val {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n)
    (f : harmHom n k) :
    ((hTA A f : harmHom n k) : MvPolynomial (Fin n) ℝ) =
      Fh2.substA n A (f : MvPolynomial (Fin n) ℝ) := rfl

private lemma hTA_add {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n)
    (f g : harmHom n k) : hTA A (f + g) = hTA A f + hTA A g := by
  apply Subtype.ext
  simp only [hTA, Submodule.coe_add, Fh2.substA_add]

private lemma hTA_smul {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n)
    (c : ℝ) (f : harmHom n k) : hTA A (c • f) = c • hTA A f := by
  apply Subtype.ext
  simp only [hTA, Submodule.coe_smul, Fh2.substA_smul]

private noncomputable def hTALin {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n) :
    harmHom n k →ₗ[ℝ] harmHom n k where
  toFun := hTA A
  map_add' := hTA_add A
  map_smul' := hTA_smul A

private lemma hev_hTA {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n)
    (f : harmHom n k) (θ : hS n) :
    hev θ ((hTA A f : harmHom n k) : MvPolynomial (Fin n) ℝ) =
      hev (sphMap A θ) (f : MvPolynomial (Fin n) ℝ) := by
  rw [hTA_val]
  show MvPolynomial.eval (fun l : Fin n => (θ : hE n) l)
        (Fh2.substA n A (f : MvPolynomial (Fin n) ℝ))
      = MvPolynomial.eval (fun l : Fin n => ((sphMap A θ : hS n) : hE n) l)
        (f : MvPolynomial (Fin n) ℝ)
  rw [FhCHS5.substA_eval_coord n A (f : MvPolynomial (Fin n) ℝ) θ]
  rfl

private lemma hb_TA {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n)
    (f g : harmHom n k) : harmBilin n k (hTA A f) (hTA A g) = harmBilin n k f g := by
  obtain ⟨e, hmp, he⟩ :=
    Commons.Analysis.MeasureTheory.sphere_isometry_measurableEquiv_measurePreserving A
  rw [hb_integral, hb_integral]
  have h1 : (fun θ : hS n => hev θ ((hTA A f : harmHom n k) : MvPolynomial (Fin n) ℝ) *
        hev θ ((hTA A g : harmHom n k) : MvPolynomial (Fin n) ℝ))
      = fun θ : hS n =>
          (fun η : hS n => hev η (f : MvPolynomial (Fin n) ℝ) *
            hev η (g : MvPolynomial (Fin n) ℝ)) (e θ) := by
    funext θ
    rw [hev_hTA A f θ, hev_hTA A g θ]
    have hf' : hev (sphMap A θ) (f : MvPolynomial (Fin n) ℝ)
        = hev (e θ) (f : MvPolynomial (Fin n) ℝ) :=
      congrArg (fun v : hE n => MvPolynomial.eval (fun l : Fin n => v l)
        (f : MvPolynomial (Fin n) ℝ)) (he θ).symm
    have hg' : hev (sphMap A θ) (g : MvPolynomial (Fin n) ℝ)
        = hev (e θ) (g : MvPolynomial (Fin n) ℝ) :=
      congrArg (fun v : hE n => MvPolynomial.eval (fun l : Fin n => v l)
        (g : MvPolynomial (Fin n) ℝ)) (he θ).symm
    rw [hf', hg']
  rw [h1, hmp.integral_comp'
    (fun η : hS n => hev η (f : MvPolynomial (Fin n) ℝ) *
      hev η (g : MvPolynomial (Fin n) ℝ))]

private lemma hTA_orth {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n) {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0) :
    ∀ i j : Fin d, harmBilin n k (hTA A (b i)) (hTA A (b j)) =
      if i = j then (1 : ℝ) else 0 :=
  fun i j => by rw [hb_TA A (b i) (b j)]; exact horth i j

private lemma hTALin_inj {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n) :
    Function.Injective (hTALin (k := k) A) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker] at hf
  have hf' : hTA A f = 0 := hf
  have h1 : harmBilin n k f f = 0 := by
    rw [← hb_TA A f f, hf']
    simp
  exact hb_self_eq_zero f h1

private theorem harmHom_finiteDimensional {n k : ℕ} : Module.Finite ℝ (harmHom n k) := by
  haveI : Module.Finite ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :=
    Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
  exact Submodule.finiteDimensional_of_le (S₁ := harmHom n k)
    (S₂ := MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) inf_le_left

private lemma hTALin_surj {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n) :
    Function.Surjective (hTALin (k := k) A) := by
  haveI := harmHom_finiteDimensional (n := n) (k := k)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (hTALin_inj (k := k) A)

private lemma hTA_span {n k : ℕ} [Nonempty (Fin n)] (A : hE n ≃ₗᵢ[ℝ] hE n) {d : ℕ}
    (b : Fin d → harmHom n k)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) :
    Submodule.span ℝ (Set.range (fun j => hTA A (b j))) = ⊤ := by
  have hrange : Set.range (fun j => hTA A (b j)) = (hTALin (k := k) A) '' Set.range b := by
    ext x; constructor
    · rintro ⟨j, rfl⟩; exact ⟨b j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
  rw [hrange, ← Submodule.map_span (hTALin (k := k) A) (Set.range b), hspan, Submodule.map_top,
    LinearMap.range_eq_top.mpr (hTALin_surj (k := k) A)]

private lemma hK_invariant {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤)
    (A : hE n ≃ₗᵢ[ℝ] hE n) (θ : hS n) :
    hK b (sphMap A θ) = hK b θ := by
  have hb'orth := hTA_orth A b horth
  have hb'span := hTA_span A b hspan
  have h1 : hK b (sphMap A θ) = hK (fun j => hTA A (b j)) θ := by
    simp only [hK]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hev_hTA A (b j) θ]
  have h2 : hK (fun j => hTA A (b j)) θ = hK b θ := by
    rw [hK_eq (fun j => hTA A (b j)) hb'orth θ, hK_eq b horth θ]
    have hReq : hR (fun j => hTA A (b j)) θ = hR b θ := by
      apply hb_eq_of_forall
      intro f
      rw [hb_reproduce (fun j => hTA A (b j)) hb'orth hb'span θ f,
        hb_reproduce b horth hspan θ f]
    rw [hReq]
  rw [h1, h2]

private lemma hK_const {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (θ θ' : hS n) :
    hK b θ = hK b θ' := by
  obtain ⟨A, hA⟩ := Fh1.exists_isometry_unit (θ : hE n) (θ' : hE n)
    (mem_sphere_zero_iff_norm.mp θ.2) (mem_sphere_zero_iff_norm.mp θ'.2)
  have hthis : sphMap A θ = θ' := by
    apply Subtype.ext
    simp only [sphMap_val]
    exact hA
  rw [← hthis, hK_invariant b horth hspan A θ]

/-! ### The kernel diagonal integrates to the dimension -/

private lemma hK_integral {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0) :
    (∫ θ : hS n, hK b θ ∂(volume.toSphere : Measure (hS n))) = (d : ℝ) := by
  have hint : ∀ j : Fin d, Integrable
      (fun θ : hS n => (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2)
      (volume.toSphere : Measure (hS n)) := by
    intro j
    have hc : Continuous (fun θ : hS n => (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2) :=
      (Commons.Algebra.MvPolynomial.continuous_eval_sphere n
        (b j : MvPolynomial (Fin n) ℝ)).pow 2
    exact Commons.Analysis.MeasureTheory.continuous_integrable_sphere _ hc
  have h1 : (∫ θ : hS n, hK b θ ∂(volume.toSphere : Measure (hS n)))
      = ∫ θ : hS n, ∑ j : Fin d, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2
        ∂(volume.toSphere : Measure (hS n)) := rfl
  rw [h1, integral_finsetSum Finset.univ (fun j _ => hint j)]
  have h2 : ∀ j : Fin d,
      (∫ θ : hS n, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2
        ∂(volume.toSphere : Measure (hS n))) = 1 := by
    intro j
    have key : (∫ θ : hS n, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2
          ∂(volume.toSphere : Measure (hS n))) = harmBilin n k (b j) (b j) := by
      rw [hb_integral (b j) (b j)]
      congr 1
      ext θ
      ring
    rw [key, horth j j, if_pos rfl]
  have h3 : (∑ j : Fin d, (∫ θ : hS n, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2
        ∂(volume.toSphere : Measure (hS n)))) = ∑ j : Fin d, (1 : ℝ) :=
    Finset.sum_congr rfl (fun j _ => h2 j)
  rw [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

private lemma hmeasure_nonneg (n : ℕ) :
    0 ≤ (volume.toSphere : Measure (hS n)).real Set.univ := by
  change 0 ≤ ((volume.toSphere : Measure (hS n)) Set.univ).toReal
  exact ENNReal.toReal_nonneg

private lemma hK_mul_measure {n k : ℕ} [Nonempty (Fin n)] {d : ℕ}
    (b : Fin d → harmHom n k)
    (horth : ∀ i j : Fin d, harmBilin n k (b i) (b j) = if i = j then (1 : ℝ) else 0)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) (θ₀ : hS n) :
    hK b θ₀ * (volume.toSphere : Measure (hS n)).real Set.univ = (d : ℝ) := by
  have hconst : ∀ θ : hS n, hK b θ = hK b θ₀ := fun θ => hK_const b horth hspan θ θ₀
  have hInt : (∫ θ : hS n, hK b θ ∂(volume.toSphere : Measure (hS n)))
      = hK b θ₀ * (volume.toSphere : Measure (hS n)).real Set.univ := by
    rw [show (∫ θ : hS n, hK b θ ∂(volume.toSphere : Measure (hS n)))
        = ∫ θ : hS n, hK b θ₀ ∂(volume.toSphere : Measure (hS n)) from by
          apply integral_congr_ae
          filter_upwards with θ
          exact hconst θ]
    rw [integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← hInt, hK_integral b horth]

/-! ### The pointwise bound -/

private lemma eval_sq_mul_measure_le {n k : ℕ} [Nonempty (Fin n)]
    (Y : MvPolynomial (Fin n) ℝ) (hY : Y ∈ harmHom n k) (θ : hS n) :
    (hev θ Y) ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ
      ≤ (Module.finrank ℝ (harmHom n k) : ℝ) *
        (∫ θ' : hS n, (hev θ' Y) ^ 2 ∂(volume.toSphere : Measure (hS n))) := by
  obtain ⟨b, horth, hspan⟩ :=
    Commons.Algebra.MvPolynomial.exists_orthonormalBasis_harmHom (n := n) (k := k)
  let f : harmHom n k := ⟨Y, hY⟩
  have hcs : (hev θ (f : MvPolynomial (Fin n) ℝ)) ^ 2 ≤
      harmBilin n k f f * hK b θ := by
    have h := hev_sq_le b horth hspan f θ
    have hk : (∑ j, (hev θ (b j : MvPolynomial (Fin n) ℝ)) ^ 2) = hK b θ := rfl
    rw [hk] at h
    exact h
  have hm := hmeasure_nonneg n
  have hmul0 : (hev θ (f : MvPolynomial (Fin n) ℝ)) ^ 2 *
      (volume.toSphere : Measure (hS n)).real Set.univ
      ≤ (harmBilin n k f f * hK b θ) * (volume.toSphere : Measure (hS n)).real Set.univ :=
    mul_le_mul_of_nonneg_right hcs hm
  rw [mul_assoc, hK_mul_measure b horth hspan θ] at hmul0
  have hbff : harmBilin n k f f =
      ∫ θ' : hS n, (hev θ' Y) ^ 2 ∂(volume.toSphere : Measure (hS n)) := by
    rw [hb_integral f f]
    congr 1
    ext θ'
    ring
  calc (hev θ Y) ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ
      = (hev θ (f : MvPolynomial (Fin n) ℝ)) ^ 2 *
        (volume.toSphere : Measure (hS n)).real Set.univ := rfl
    _ ≤ harmBilin n k f f * (Module.finrank ℝ (harmHom n k) : ℝ) := hmul0
    _ = (Module.finrank ℝ (harmHom n k) : ℝ) *
        (∫ θ' : hS n, (hev θ' Y) ^ 2 ∂(volume.toSphere : Measure (hS n))) := by
        rw [hbff, mul_comm]

/-! ### The size of the harmonic homogeneous summand -/

private def hConst (n : ℕ) : ℝ := 2 * (n : ℝ) ^ (n - 2) + (n : ℝ)

private lemma hConst_pos {n : ℕ} (hn : 1 ≤ n) : 0 < hConst n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (n - 2) := one_le_pow₀ hn1
  unfold hConst
  nlinarith

private lemma harmHom_finrank_bound {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) :
    ∀ k : ℕ, (Module.finrank ℝ (harmHom n k) : ℝ)
      ≤ hConst n * ((k : ℝ) + 1) ^ (n - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hKpos := hConst_pos hn1
  have hK1 : (1 : ℝ) ≤ hConst n := by
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (n - 2) := one_le_pow₀ hn1'
    unfold hConst
    nlinarith
  intro k
  haveI : Module.Finite ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :=
    Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
  haveI := harmHom_finiteDimensional (n := n) (k := k)
  by_cases hk : 2 ≤ k
  · have hD2 := Commons.Algebra.MvPolynomial.finrank_harmHom_add n k hk
    simp only [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule] at hD2
    have harith : n + (k - 2) - 1 = n + k - 3 := by omega
    rw [harith] at hD2
    have hd : Module.finrank ℝ (harmHom n k)
        = (n + k - 1).choose k - (n + k - 3).choose (k - 2) := by omega
    rw [hd]
    have hcast : (((n + k - 1).choose k - (n + k - 3).choose (k - 2) : ℕ) : ℝ)
        ≤ 2 * (n : ℝ) ^ (n - 2) * ((k : ℝ) + 1) ^ (n - 2) :=
      Commons.Algebra.Binomial.harmonic_dim_arith n k hn hk
    have hXnn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ (n - 2) := by positivity
    calc (((n + k - 1).choose k - (n + k - 3).choose (k - 2) : ℕ) : ℝ)
        ≤ 2 * (n : ℝ) ^ (n - 2) * ((k : ℝ) + 1) ^ (n - 2) := hcast
      _ ≤ hConst n * ((k : ℝ) + 1) ^ (n - 2) := by
          have hle2 : 2 * (n : ℝ) ^ (n - 2) ≤ hConst n := by
            have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
            unfold hConst
            linarith
          exact mul_le_mul_of_nonneg_right hle2 hXnn
  · push_neg at hk
    haveI : Module.Finite ℝ ↥(MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :=
      Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
    have hle_hom : Module.finrank ℝ (harmHom n k)
        ≤ Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :=
      Submodule.finrank_mono inf_le_left
    rw [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule] at hle_hom
    interval_cases k
    · have h1 : Module.finrank ℝ (harmHom n 0) ≤ 1 := by simpa using hle_hom
      have h2 : (Module.finrank ℝ (harmHom n 0) : ℝ) ≤ 1 := by exact_mod_cast h1
      have h3 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
      rw [h3, one_pow]
      linarith [h2, hK1]
    · have h1 : Module.finrank ℝ (harmHom n 1) ≤ n := by simpa using hle_hom
      have h2 : (Module.finrank ℝ (harmHom n 1) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have h3 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
      rw [h3]
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 2) := one_le_pow₀ (by norm_num)
      have h4 : (n : ℝ) ≤ hConst n := by
        unfold hConst
        have h1' : (1 : ℝ) ≤ (n : ℝ) ^ (n - 2) := one_le_pow₀ hn1'
        nlinarith
      calc (Module.finrank ℝ (harmHom n 1) : ℝ) ≤ (n : ℝ) := h2
        _ = (n : ℝ) * 1 := (mul_one _).symm
        _ ≤ hConst n * (2 : ℝ) ^ (n - 2) :=
            mul_le_mul h4 h2n (by norm_num) (le_of_lt hKpos)

private lemma harmHom_finrank_bound_one :
    ∀ k : ℕ, (Module.finrank ℝ (harmHom 1 k) : ℝ) * ((k : ℝ) + 1) ≤ 2 := by
  intro k
  haveI := harmHom_finiteDimensional (n := 1) (k := k)
  by_cases hk : 2 ≤ k
  · have hD2 := Commons.Algebra.MvPolynomial.finrank_harmHom_add 1 k hk
    simp only [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule] at hD2
    have e1 : (1 : ℕ) + (k - 2) - 1 = k - 2 := by omega
    have e2 : (1 : ℕ) + k - 1 = k := by omega
    rw [e1, e2, Nat.choose_self, Nat.choose_self] at hD2
    have hd : Module.finrank ℝ (harmHom 1 k) = 0 := by omega
    rw [hd]
    norm_num
  · push_neg at hk
    haveI : Module.Finite ℝ ↥(MvPolynomial.homogeneousSubmodule (Fin 1) ℝ k) :=
      Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
    have hle_hom : Module.finrank ℝ (harmHom 1 k)
        ≤ Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin 1) ℝ k) :=
      Submodule.finrank_mono inf_le_left
    rw [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule] at hle_hom
    interval_cases k
    · have h1 : Module.finrank ℝ (harmHom 1 0) ≤ 1 := by simpa using hle_hom
      have h2 : (Module.finrank ℝ (harmHom 1 0) : ℝ) ≤ 1 := by exact_mod_cast h1
      have h3 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
      rw [h3, mul_one]
      linarith
    · have h1 : Module.finrank ℝ (harmHom 1 1) ≤ 1 := by simpa using hle_hom
      have h2 : (Module.finrank ℝ (harmHom 1 1) : ℝ) ≤ 1 := by exact_mod_cast h1
      have h3 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
      rw [h3]
      linarith

/-! ### Elementary final estimates -/

private lemma abs_le_of_sq_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b := by
  have := sq_le_sq.mp h
  rwa [abs_of_nonneg hb] at this

private lemma const_le_sq_mul (K m : ℝ) (hm : 0 < m) (hK : 0 ≤ K + 2) :
    K ≤ (Real.sqrt ((K + 2) / m) + 1) ^ 2 * m := by
  have h1 : (0 : ℝ) ≤ (K + 2) / m := div_nonneg hK (le_of_lt hm)
  have hsq : (Real.sqrt ((K + 2) / m)) ^ 2 = (K + 2) / m := Real.sq_sqrt h1
  have hnn : 0 ≤ Real.sqrt ((K + 2) / m) := Real.sqrt_nonneg _
  have hle : (Real.sqrt ((K + 2) / m)) ^ 2 ≤ (Real.sqrt ((K + 2) / m) + 1) ^ 2 := by
    nlinarith [hnn]
  have h2 : (K + 2) / m ≤ (Real.sqrt ((K + 2) / m) + 1) ^ 2 :=
    hsq.symm.trans_le hle
  have h3 : (K + 2) ≤ (Real.sqrt ((K + 2) / m) + 1) ^ 2 * m :=
    calc (K + 2) = (K + 2) / m * m := (div_mul_cancel₀ (K + 2) (ne_of_gt hm)).symm
      _ ≤ (Real.sqrt ((K + 2) / m) + 1) ^ 2 * m := mul_le_mul_of_nonneg_right h2 (le_of_lt hm)
  linarith

private lemma rpow_half_sq (x : ℝ) (hx : 0 < x) (a : ℕ) :
    (x ^ ((a : ℝ) / 2)) ^ 2 = x ^ a := by
  rw [pow_two, ← Real.rpow_add hx]
  have : ((a : ℝ) / 2) + ((a : ℝ) / 2) = (a : ℝ) := by ring
  rw [this, Real.rpow_natCast]

private lemma rpow_neg_half_sq (x : ℝ) (hx : 0 < x) :
    (x ^ ((-1 : ℝ) / 2)) ^ 2 = 1 / x := by
  rw [show ((-1 : ℝ) / 2) = -(1 / 2) by norm_num]
  rw [pow_two, ← Real.rpow_add hx]
  have : (-(1 / 2 : ℝ)) + (-(1 / 2)) = -1 := by norm_num
  rw [this, Real.rpow_neg_one, inv_eq_one_div]

/-- **Bound on the sup-norm of an `L²`-normalised harmonic homogeneous polynomial.** -/
theorem harmonic_sup_norm_bound
    {n : ℕ} [Nonempty (Fin n)] :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (Y : MvPolynomial (Fin n) ℝ),
      Y ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Y)) = 0 →
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) Y)^2
        ∂MeasureTheory.volume.toSphere) = 1 →
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) Y|
          ≤ C * ((k : ℝ) + 1) ^ (((n : ℝ) - 2) / 2) := by
  haveI : Nontrivial (hE n) := by infer_instance
  have hmpos : 0 < (volume.toSphere : Measure (hS n)).real Set.univ := by
    have hne : (volume.toSphere : Measure (hS n)) ≠ 0 :=
      Measure.toSphere_ne_zero (volume : Measure (hE n))
    change 0 < ((volume.toSphere : Measure (hS n)) Set.univ).toReal
    exact ENNReal.toReal_pos (ne_of_gt (Measure.measure_univ_pos.mpr hne)) (measure_ne_top _ _)
  by_cases hn2 : 2 ≤ n
  · have hn1 : 1 ≤ n := by omega
    have hK2 : (0 : ℝ) ≤ hConst n + 2 := by
      have := hConst_pos hn1
      linarith
    set C : ℝ :=
      Real.sqrt ((hConst n + 2) / (volume.toSphere : Measure (hS n)).real Set.univ) + 1 with hCdef
    have hCpos : 0 < C := by rw [hCdef]; positivity
    have hCsq : hConst n ≤ C ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ := by
      have h := const_le_sq_mul (hConst n) ((volume.toSphere : Measure (hS n)).real Set.univ)
        hmpos hK2
      rw [hCdef]
      exact h
    refine ⟨C, hCpos, ?_⟩
    intro k Y hYhom hYlap hYnorm θ
    have hmem : Y ∈ harmHom n k :=
      mem_harmHom.mpr ⟨hYhom, by rw [lapLM_apply]; exact hYlap⟩
    have hbase := eval_sq_mul_measure_le (n := n) (k := k) Y hmem θ
    have hInt : (∫ θ' : hS n, (hev θ' Y) ^ 2 ∂(volume.toSphere : Measure (hS n))) = 1 := hYnorm
    rw [hInt, mul_one] at hbase
    have hXnn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ (n - 2) := by positivity
    have hkey : (hev θ Y) ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ
        ≤ hConst n * ((k : ℝ) + 1) ^ (n - 2) :=
      le_trans hbase (harmHom_finrank_bound hn2 k)
    have h1 : (hev θ Y) ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ
        ≤ (C ^ 2 * ((k : ℝ) + 1) ^ (n - 2)) *
          (volume.toSphere : Measure (hS n)).real Set.univ := by
      calc (hev θ Y) ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ
          ≤ hConst n * ((k : ℝ) + 1) ^ (n - 2) := hkey
        _ ≤ (C ^ 2 * (volume.toSphere : Measure (hS n)).real Set.univ) *
              ((k : ℝ) + 1) ^ (n - 2) := mul_le_mul_of_nonneg_right hCsq hXnn
        _ = (C ^ 2 * ((k : ℝ) + 1) ^ (n - 2)) *
              (volume.toSphere : Measure (hS n)).real Set.univ := by ring
    have h2 : (hev θ Y) ^ 2 ≤ C ^ 2 * ((k : ℝ) + 1) ^ (n - 2) :=
      le_of_mul_le_mul_right h1 hmpos
    have hexp : ((n : ℝ) - 2) / 2 = (((n - 2 : ℕ) : ℝ)) / 2 := by
      rw [Nat.cast_sub hn2]; norm_num
    have hr2 : (((k : ℝ) + 1) ^ (((n : ℝ) - 2) / 2)) ^ 2 = ((k : ℝ) + 1) ^ (n - 2) := by
      rw [hexp]
      exact rpow_half_sq _ (by positivity) (n - 2)
    have h3 : (hev θ Y) ^ 2 ≤ (C * ((k : ℝ) + 1) ^ (((n : ℝ) - 2) / 2)) ^ 2 := by
      rw [mul_pow, hr2]
      exact h2
    have hg := abs_le_of_sq_le_sq (by positivity) h3
    exact hg
  · have hn1 : n = 1 := by
      have hpos : 0 < n := by
        obtain ⟨i⟩ := ‹Nonempty (Fin n)›
        exact Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.2
      omega
    subst hn1
    set C : ℝ :=
      Real.sqrt ((hConst 1 + 2) / (volume.toSphere : Measure (hS 1)).real Set.univ) + 1 with hCdef
    have hCpos : 0 < C := by rw [hCdef]; positivity
    have hCsq : (2 : ℝ) ≤ C ^ 2 * (volume.toSphere : Measure (hS 1)).real Set.univ := by
      have h := const_le_sq_mul (hConst 1) ((volume.toSphere : Measure (hS 1)).real Set.univ)
        hmpos (by norm_num [hConst])
      have h2 : (2 : ℝ) ≤ hConst 1 := by norm_num [hConst]
      have h3 : hConst 1 ≤ C ^ 2 * (volume.toSphere : Measure (hS 1)).real Set.univ := by
        rw [hCdef]
        exact h
      linarith
    refine ⟨C, hCpos, ?_⟩
    intro k Y hYhom hYlap hYnorm θ
    have hmem : Y ∈ harmHom 1 k :=
      mem_harmHom.mpr ⟨hYhom, by rw [lapLM_apply]; exact hYlap⟩
    have hbase := eval_sq_mul_measure_le (n := 1) (k := k) Y hmem θ
    have hInt : (∫ θ' : hS 1, (hev θ' Y) ^ 2 ∂(volume.toSphere : Measure (hS 1))) = 1 := hYnorm
    rw [hInt, mul_one] at hbase
    have hk1 : 0 < (k : ℝ) + 1 := by positivity
    have hd := harmHom_finrank_bound_one k
    have hkey : (hev θ Y) ^ 2 * ((k : ℝ) + 1) * (volume.toSphere : Measure (hS 1)).real Set.univ
        ≤ 2 := by
      calc (hev θ Y) ^ 2 * ((k : ℝ) + 1) * (volume.toSphere : Measure (hS 1)).real Set.univ
          = ((hev θ Y) ^ 2 * (volume.toSphere : Measure (hS 1)).real Set.univ) *
              ((k : ℝ) + 1) := by ring
        _ ≤ (Module.finrank ℝ (harmHom 1 k) : ℝ) * ((k : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hbase hk1.le
        _ ≤ 2 := hd
    have h4 : (hev θ Y) ^ 2 * ((k : ℝ) + 1) ≤ C ^ 2 := by
      have h5 : (hev θ Y) ^ 2 * ((k : ℝ) + 1) *
          (volume.toSphere : Measure (hS 1)).real Set.univ ≤ C ^ 2 *
          (volume.toSphere : Measure (hS 1)).real Set.univ := le_trans hkey hCsq
      exact le_of_mul_le_mul_right h5 hmpos
    have h5 : (hev θ Y) ^ 2 ≤ C ^ 2 / ((k : ℝ) + 1) := (le_div_iff₀ hk1).mpr h4
    have hexp : ((1 : ℝ) - 2) / 2 = (-1 : ℝ) / 2 := by norm_num
    have hr2 : (((k : ℝ) + 1) ^ (((1 : ℝ) - 2) / 2)) ^ 2 = 1 / ((k : ℝ) + 1) := by
      rw [hexp]
      exact rpow_neg_half_sq _ (by positivity)
    have h6 : (hev θ Y) ^ 2 ≤ (C * ((k : ℝ) + 1) ^ (((1 : ℝ) - 2) / 2)) ^ 2 := by
      rw [mul_pow, hr2, mul_one_div]
      exact h5
    have hg := abs_le_of_sq_le_sq (by positivity) h6
    simpa only [hev_def, Nat.cast_one] using hg

end Commons.Analysis.MeasureTheory
