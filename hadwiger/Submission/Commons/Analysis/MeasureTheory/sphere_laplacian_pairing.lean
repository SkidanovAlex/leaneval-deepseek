import Mathlib
import Submission.Commons.Algebra.MvPolynomial.gradient_eval
import Submission.Commons.Algebra.MvPolynomial.homogeneous_eval_smul
import Submission.Commons.Algebra.MvPolynomial.partialDeriv2_eval
import Submission.Commons.Algebra.MvPolynomial.contDiff_eval
import Submission.Commons.Analysis.Calculus.contDiffOn_fderiv_apply
import Submission.Commons.Analysis.Calculus.contDiff_of_contDiffOn_compl_zero
import Submission.Commons.Analysis.InnerProductSpace.fderiv_norm_single
import Submission.Commons.Analysis.Real.integral_Ioi_deriv_mul_pow_boundary
import Submission.Commons.Analysis.MeasureTheory.integral_divergence_eq_zero_euclidean
import Submission.Commons.Analysis.MeasureTheory.integral_radial_mul_homogeneous
import Submission.Commons.Analysis.MeasureTheory.polar_integral

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open MeasureTheory Metric Filter
open Commons.Analysis.InnerProductSpace

namespace Commons.Analysis.MeasureTheory

namespace SphereLapPairing

variable {n : ℕ}


abbrev Ep (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `i`-th standard basis vector of `EuclideanSpace ℝ (Fin n)`. -/
def evec {n : ℕ} (i : Fin n) : Ep n := EuclideanSpace.single i 1

lemma evec_apply {n : ℕ} (i j : Fin n) : (evec i : Ep n) j = if j = i then 1 else 0 := by
  simp [evec]

lemma sum_coord_smul_evec {n : ℕ} (x : Ep n) : (∑ i : Fin n, x i • evec i) = x := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  simpa [evec, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h

/-- The `i`-th partial derivative of `f` at `x`. -/
def pD {n : ℕ} (i : Fin n) (f : Ep n → ℝ) (x : Ep n) : ℝ := fderiv ℝ f x (evec i)

lemma pD_apply {n : ℕ} (i : Fin n) (f : Ep n → ℝ) (x : Ep n) :
    pD i f x = fderiv ℝ f x (evec i) := rfl

lemma pD_add {n : ℕ} (i : Fin n) {f g : Ep n → ℝ} {x : Ep n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pD i (fun y => f y + g y) x = pD i f x + pD i g x := by
  have h1 : (fun y : Ep n => f y + g y) = f + g := by funext y; rfl
  unfold pD
  rw [h1, fderiv_add hf hg]
  rfl

lemma pD_sub {n : ℕ} (i : Fin n) {f g : Ep n → ℝ} {x : Ep n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pD i (fun y => f y - g y) x = pD i f x - pD i g x := by
  have h1 : (fun y : Ep n => f y - g y) = f - g := by funext y; rfl
  unfold pD
  rw [h1, fderiv_sub hf hg]
  rfl

lemma pD_mul {n : ℕ} (i : Fin n) {f g : Ep n → ℝ} {x : Ep n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pD i (fun y => f y * g y) x = pD i f x * g x + f x * pD i g x := by
  have h1 : (fun y : Ep n => f y * g y) = f * g := by funext y; rfl
  unfold pD
  rw [h1, fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma pD_const_mul {n : ℕ} (i : Fin n) (c : ℝ) {f : Ep n → ℝ} {x : Ep n}
    (hf : DifferentiableAt ℝ f x) :
    pD i (fun y => c * f y) x = c * pD i f x := by
  have h1 : (fun y : Ep n => c * f y) = c • f := by funext y; simp
  unfold pD
  rw [h1, fderiv_const_smul hf c]
  simp [smul_eq_mul]

lemma pD_const {n : ℕ} (i : Fin n) (c : ℝ) (x : Ep n) :
    pD i (fun _ : Ep n => c) x = 0 := by
  simp [pD]

/-- Chain rule for `∂ᵢ f` along a scaling, for `f` homogeneous of degree `d`. -/
lemma pD_smul_of_homogeneous {n : ℕ} {d : ℕ} {f : Ep n → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ y : Ep n, f (t • y) = t ^ d * f y)
    {t : ℝ} (ht : 0 < t) (x : Ep n) (hd : DifferentiableAt ℝ f (t • x))
    (hd' : DifferentiableAt ℝ f x) (i : Fin n) :
    t * pD i f (t • x) = t ^ d * pD i f x := by
  have hg : (fun y : Ep n => f (t • y)) = (fun y : Ep n => t ^ d * f y) := by
    funext y; exact hf t ht y
  have hinner : HasFDerivAt (fun y : Ep n => t • y) (t • (1 : Ep n →L[ℝ] Ep n)) x := by
    have h := ContinuousLinearMap.hasFDerivAt (t • (1 : Ep n →L[ℝ] Ep n)) (x := x)
    convert h using 1
    ext y; simp
  have hcomp : fderiv ℝ (fun y : Ep n => f (t • y)) x
      = (fderiv ℝ f (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n)) :=
    (hd.hasFDerivAt.comp x hinner).fderiv
  have hright : fderiv ℝ (fun y : Ep n => t ^ d * f y) x = (t ^ d) • (fderiv ℝ f x) := by
    have h1 : (fun y : Ep n => t ^ d * f y) = (t ^ d) • f := by funext y; simp
    rw [h1, fderiv_const_smul hd' (t ^ d)]
  have hL : ((fderiv ℝ f (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n))) (evec i)
      = t * pD i f (t • x) := by
    simp [pD, ContinuousLinearMap.comp_apply, smul_eq_mul]
  have hR : ((t ^ d) • (fderiv ℝ f x)) (evec i) = t ^ d * pD i f x := by
    simp [pD, smul_eq_mul]
  calc t * pD i f (t • x)
      = ((fderiv ℝ f (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n))) (evec i) := hL.symm
    _ = (fderiv ℝ (fun y : Ep n => f (t • y)) x) (evec i) := by rw [hcomp]
    _ = (fderiv ℝ (fun y : Ep n => t ^ d * f y) x) (evec i) := by rw [hg]
    _ = ((t ^ d) • (fderiv ℝ f x)) (evec i) := by rw [hright]
    _ = t ^ d * pD i f x := hR

/-- Euler's relation: `∑ᵢ xᵢ ∂ᵢ f x = d f x` for `f` homogeneous of degree `d`. -/
lemma sum_coord_mul_pD_of_homogeneous {n : ℕ} {d : ℕ} {f : Ep n → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ y : Ep n, f (t • y) = t ^ d * f y)
    (x : Ep n) (hd : DifferentiableAt ℝ f x) :
    (∑ i : Fin n, x i * pD i f x) = d * f x := by
  have hinner : HasDerivAt (fun t : ℝ => t • x) (((1:ℝ)) • x) 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const x
  have hd' : HasFDerivAt f (fderiv ℝ f (((1:ℝ)) • x)) (((1:ℝ)) • x) := by
    simpa [one_smul] using hd.hasFDerivAt
  have houter : HasDerivAt (fun t : ℝ => f (t • x)) ((fderiv ℝ f x) x) 1 := by
    have h := hd'.comp_hasDerivAt 1 hinner
    simpa [Function.comp_def, one_smul] using h
  have hmem : Set.Ioi (0:ℝ) ∈ 𝓝 (1:ℝ) := Ioi_mem_nhds (by norm_num)
  have hagree : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] fun t => t ^ d * f x := by
    filter_upwards [hmem] with t ht
    exact hf t ht x
  have htarget : HasDerivAt (fun t : ℝ => t ^ d * f x) ((d : ℝ) * f x) 1 := by
    simpa using (hasDerivAt_pow d (1:ℝ)).mul_const (f x)
  have hderiv2 : HasDerivAt (fun t : ℝ => f (t • x)) ((d : ℝ) * f x) 1 :=
    htarget.congr_of_eventuallyEq hagree
  have hval : (fderiv ℝ f x) x = (d : ℝ) * f x := houter.unique hderiv2
  have hgen := congrArg (fun z : Ep n => (fderiv ℝ f x) z) (sum_coord_smul_evec x).symm
  have hexp : (fderiv ℝ f x) x = ∑ i : Fin n, x i * pD i f x := by
    rw [hgen, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    simp [pD, smul_eq_mul]
  rw [← hexp, hval]


/-- Coordinate divergence, in the trace form used by the divergence theorem. -/
def divE {n : ℕ} (V : Ep n → Ep n) (x : Ep n) : ℝ := ∑ i : Fin n, (fderiv ℝ V x (evec i)) i

/-- Coordinate Laplacian: `∑ᵢ ∂ᵢ∂ᵢ f`. -/
def lapG {n : ℕ} (f : Ep n → ℝ) (x : Ep n) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (evec i)) x (evec i)

lemma lapG_eq {n : ℕ} (f : Ep n → ℝ) (x : Ep n) :
    lapG f x = ∑ i : Fin n, pD i (fun y => pD i f y) x := rfl

lemma coord_proj {n : ℕ} (i : Fin n) :
    (EuclideanSpace.proj (𝕜 := ℝ) i : Ep n →L[ℝ] ℝ) = fun v : Ep n => v i := by
  funext v; rw [EuclideanSpace.coe_proj]

lemma fderiv_coord {n : ℕ} (V : Ep n → Ep n) (x : Ep n) (hV : DifferentiableAt ℝ V x) (i : Fin n) :
    (fderiv ℝ V x (evec i)) i = pD i (fun y => (V y) i) x := by
  have h2 : (fun y : Ep n => (V y) i) = (EuclideanSpace.proj (𝕜 := ℝ) i : Ep n →L[ℝ] ℝ) ∘ V := by
    rw [coord_proj]; rfl
  have h1 : fderiv ℝ (fun y : Ep n => (V y) i) x
      = (EuclideanSpace.proj (𝕜 := ℝ) i : Ep n →L[ℝ] ℝ) ∘L fderiv ℝ V x := by
    rw [h2, fderiv_comp x]
    · rw [(ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i : Ep n →L[ℝ] ℝ)).fderiv]
    · exact (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i)).differentiableAt
    · exact hV
  rw [pD, h1]
  simp [coord_proj]

/-- Divergence of `f • V`. -/
lemma divE_smul {n : ℕ} (f : Ep n → ℝ) (V : Ep n → Ep n) (x : Ep n)
    (hf : DifferentiableAt ℝ f x) (hV : DifferentiableAt ℝ V x) :
    divE (fun y => f y • V y) x = f x * divE V x + ∑ i : Fin n, pD i f x * (V x) i := by
  rw [divE]
  have hderiv : fderiv ℝ (fun y : Ep n => f y • V y) x
      = f x • fderiv ℝ V x + (fderiv ℝ f x).smulRight (V x) := by
    have h1 : (fun y : Ep n => f y • V y) = f • V := rfl
    rw [h1, fderiv_smul hf hV]
  have hterm : ∀ i : Fin n, (fderiv ℝ (fun y : Ep n => f y • V y) x (evec i)) i
      = f x * (fderiv ℝ V x (evec i)) i + pD i f x * (V x) i := by
    intro i
    rw [hderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, PiLp.add_apply]
    rw [pD]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [divE]

/-- The vector field `G ∇Y - Y ∇G` written in coordinates. -/
def Wf {n : ℕ} (G Yf : Ep n → ℝ) (x : Ep n) : Ep n :=
  ∑ i : Fin n, (G x * pD i Yf x - Yf x * pD i G x) • evec i

lemma Wf_coord {n : ℕ} (G Yf : Ep n → ℝ) (x : Ep n) (j : Fin n) :
    (Wf G Yf x) j = G x * pD j Yf x - Yf x * pD j G x := by
  unfold Wf
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  have h1 : ∀ i : Fin n, ((G x * pD i Yf x - Yf x * pD i G x) • evec i : Ep n).ofLp j
      = (G x * pD i Yf x - Yf x * pD i G x) * (if j = i then 1 else 0) := by
    intro i
    rw [PiLp.smul_apply, evec_apply]
    simp
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  simp

lemma fderiv_smul_mul {n : ℕ} {f g : Ep n → ℝ} {x : Ep n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    pD j (fun y => f y * g y) x = pD j f x * g x + f x * pD j g x := by
  have h1 : (fun y : Ep n => f y * g y) = f * g := rfl
  unfold pD
  rw [h1, fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, pD]
  ring

lemma divE_Wf {n : ℕ} (G Yf : Ep n → ℝ) (x : Ep n)
    (hG : DifferentiableAt ℝ G x) (hYf : DifferentiableAt ℝ Yf x)
    (hGY : ∀ j : Fin n, DifferentiableAt ℝ (fun y => pD j G y) x)
    (hYY : ∀ j : Fin n, DifferentiableAt ℝ (fun y => pD j Yf y) x) :
    divE (Wf G Yf) x = G x * lapG Yf x - Yf x * lapG G x := by
  have hW : DifferentiableAt ℝ (Wf G Yf) x := by
    have h1 : Wf G Yf = fun y : Ep n => ∑ i : Fin n, (G y * pD i Yf y - Yf y * pD i G y) • evec i := rfl
    rw [h1]
    exact DifferentiableAt.fun_sum (fun i _ =>
      ((hG.mul (hYY i)).sub (hYf.mul (hGY i))).smul_const (evec i))
  rw [divE]
  have hterm : ∀ j : Fin n, (fderiv ℝ (Wf G Yf) x (evec j)) j
      = G x * fderiv ℝ (fun y => fderiv ℝ Yf y (evec j)) x (evec j)
        - Yf x * fderiv ℝ (fun y => fderiv ℝ G y (evec j)) x (evec j) := by
    intro j
    rw [fderiv_coord _ _ hW j]
    have hfun : (fun y : Ep n => (Wf G Yf y) j)
        = fun y => G y * pD j Yf y - Yf y * pD j G y := by
      funext y; rw [Wf_coord]
    rw [hfun]
    change (fderiv ℝ (fun y : Ep n => G y * pD j Yf y - Yf y * pD j G y) x) (evec j) = _
    have hd1 : DifferentiableAt ℝ (fun y : Ep n => G y * pD j Yf y) x := hG.mul (hYY j)
    have hd2 : DifferentiableAt ℝ (fun y : Ep n => Yf y * pD j G y) x := hYf.mul (hGY j)
    have hf1 : (fun y : Ep n => G y * pD j Yf y - Yf y * pD j G y)
        = (fun y : Ep n => G y * pD j Yf y) - (fun y : Ep n => Yf y * pD j G y) := by
      funext y; rfl
    rw [hf1, fderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply]
    have hm1 : (fderiv ℝ (fun y : Ep n => G y * pD j Yf y) x) (evec j)
        = G x * (fderiv ℝ (fun y : Ep n => pD j Yf y) x) (evec j)
          + (fderiv ℝ G x) (evec j) * (fderiv ℝ Yf x) (evec j) := by
      have h2 : (fun y : Ep n => G y * pD j Yf y) = G * (fun y => pD j Yf y) := by
        funext y; rfl
      rw [h2, fderiv_mul hG (hYY j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, pD]
      ring
    have hm2 : (fderiv ℝ (fun y : Ep n => Yf y * pD j G y) x) (evec j)
        = Yf x * (fderiv ℝ (fun y : Ep n => pD j G y) x) (evec j)
          + (fderiv ℝ Yf x) (evec j) * (fderiv ℝ G x) (evec j) := by
      have h2 : (fun y : Ep n => Yf y * pD j G y) = Yf * (fun y => pD j G y) := by
        funext y; rfl
      rw [h2, fderiv_mul hYf (hGY j)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, pD]
      ring
    rw [hm1, hm2]
    simp only [pD]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rfl


/-- Homogeneity (in multiplied form) of the coordinates of the field `Wf`. -/
lemma Wf_coord_smul {n : ℕ} {k : ℕ} {G Yf : Ep n → ℝ}
    (hG : ∀ t : ℝ, 0 < t → ∀ y : Ep n, G (t • y) = G y)
    (hY : ∀ t : ℝ, 0 < t → ∀ y : Ep n, Yf (t • y) = t ^ k * Yf y)
    {t : ℝ} (ht : 0 < t) (x : Ep n)
    (hdG : DifferentiableAt ℝ G (t • x)) (hdG' : DifferentiableAt ℝ G x)
    (hdY : DifferentiableAt ℝ Yf (t • x)) (hdY' : DifferentiableAt ℝ Yf x) (j : Fin n) :
    t * (Wf G Yf (t • x)) j = t ^ k * (Wf G Yf x) j := by
  rw [Wf_coord, Wf_coord]
  have h1 : G (t • x) = G x := hG t ht x
  have h2 : Yf (t • x) = t ^ k * Yf x := hY t ht x
  have h3 : t * pD j Yf (t • x) = t ^ k * pD j Yf x :=
    pD_smul_of_homogeneous hY ht x hdY hdY' j
  have hG' : ∀ s : ℝ, 0 < s → ∀ y : Ep n, G (s • y) = s ^ 0 * G y :=
    fun s hs y => by rw [pow_zero, one_mul]; exact hG s hs y
  have h4 : t * pD j G (t • x) = t ^ 0 * pD j G x :=
    pD_smul_of_homogeneous hG' ht x hdG hdG' j
  rw [h1, h2]
  have h4' : t * pD j G (t • x) = pD j G x := by simpa using h4
  rw [show t * (G x * pD j Yf (t • x) - t ^ k * Yf x * pD j G (t • x))
      = G x * (t * pD j Yf (t • x)) - t ^ k * Yf x * (t * pD j G (t • x)) by ring]
  rw [h3, h4']
  ring

/-- Homogeneity of the coordinates of `Wf` in direct form (degree `k - 1`). -/
lemma Wf_coord_smul' {n : ℕ} {k : ℕ} (hk : 1 ≤ k) {G Yf : Ep n → ℝ}
    (hG : ∀ t : ℝ, 0 < t → ∀ y : Ep n, G (t • y) = G y)
    (hY : ∀ t : ℝ, 0 < t → ∀ y : Ep n, Yf (t • y) = t ^ k * Yf y)
    {t : ℝ} (ht : 0 < t) (x : Ep n)
    (hdG : DifferentiableAt ℝ G (t • x)) (hdG' : DifferentiableAt ℝ G x)
    (hdY : DifferentiableAt ℝ Yf (t • x)) (hdY' : DifferentiableAt ℝ Yf x) (j : Fin n) :
    (Wf G Yf (t • x)) j = t ^ (k - 1) * (Wf G Yf x) j := by
  have h := Wf_coord_smul hG hY ht x hdG hdG' hdY hdY' j
  have htne : t ≠ 0 := ne_of_gt ht
  have hpow : t ^ k = t ^ (k - 1) * t := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have h2 : t * (Wf G Yf (t • x)) j = t * (t ^ (k - 1) * (Wf G Yf x) j) := by
    rw [h, hpow]; ring
  exact mul_left_cancel₀ htne h2

/-- Homogeneity of the field `Wf` as a vector, degree `k - 1`. -/
lemma Wf_smul {n : ℕ} {k : ℕ} (hk : 1 ≤ k) {G Yf : Ep n → ℝ}
    (hG : ∀ t : ℝ, 0 < t → ∀ y : Ep n, G (t • y) = G y)
    (hY : ∀ t : ℝ, 0 < t → ∀ y : Ep n, Yf (t • y) = t ^ k * Yf y)
    {t : ℝ} (ht : 0 < t) (x : Ep n)
    (hdG : DifferentiableAt ℝ G (t • x)) (hdG' : DifferentiableAt ℝ G x)
    (hdY : DifferentiableAt ℝ Yf (t • x)) (hdY' : DifferentiableAt ℝ Yf x) :
    Wf G Yf (t • x) = t ^ (k - 1) • Wf G Yf x := by
  conv_lhs => rw [← sum_coord_smul_evec (Wf G Yf (t • x))]
  conv_rhs => rw [← sum_coord_smul_evec (Wf G Yf x)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Wf_coord_smul' hk hG hY ht x hdG hdG' hdY hdY' j, smul_smul]

/-- Homogeneity of `‖·‖ • Wf`, degree `k`. -/
lemma Wf_norm_smul {n : ℕ} {k : ℕ} (hk : 1 ≤ k) {G Yf : Ep n → ℝ}
    (hG : ∀ t : ℝ, 0 < t → ∀ y : Ep n, G (t • y) = G y)
    (hY : ∀ t : ℝ, 0 < t → ∀ y : Ep n, Yf (t • y) = t ^ k * Yf y)
    {t : ℝ} (ht : 0 < t) (x : Ep n)
    (hdG : DifferentiableAt ℝ G (t • x)) (hdG' : DifferentiableAt ℝ G x)
    (hdY : DifferentiableAt ℝ Yf (t • x)) (hdY' : DifferentiableAt ℝ Yf x) :
    ‖t • x‖ • Wf G Yf (t • x) = t ^ k • (‖x‖ • Wf G Yf x) := by
  rw [Wf_smul hk hG hY ht x hdG hdG' hdY hdY', norm_smul, Real.norm_eq_abs,
    abs_of_pos ht, smul_smul, smul_smul]
  congr 1
  have hpow : t ^ k = t * t ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ']
  rw [hpow]
  ring

/-- Divergence of a homogeneous vector field is homogeneous of degree `m - 1`. -/
lemma divE_smul_of_homogeneous {n : ℕ} {m : ℕ} {V : Ep n → Ep n}
    (hV : ∀ t : ℝ, 0 < t → ∀ y : Ep n, V (t • y) = t ^ m • V y)
    {t : ℝ} (ht : 0 < t) (x : Ep n)
    (hd : DifferentiableAt ℝ V (t • x)) (hd' : DifferentiableAt ℝ V x) :
    t * divE V (t • x) = t ^ m * divE V x := by
  have hinner : HasFDerivAt (fun y : Ep n => t • y) (t • (1 : Ep n →L[ℝ] Ep n)) x := by
    have h := ContinuousLinearMap.hasFDerivAt (t • (1 : Ep n →L[ℝ] Ep n)) (x := x)
    convert h using 1
    ext y; simp
  have hchain : fderiv ℝ (fun y : Ep n => V (t • y)) x
      = (fderiv ℝ V (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n)) :=
    (hd.hasFDerivAt.comp x hinner).fderiv
  have hcomp : fderiv ℝ (fun y : Ep n => t ^ m • V y) x = (t ^ m) • (fderiv ℝ V x) := by
    have h2 : (fun y : Ep n => t ^ m • V y) = (t ^ m) • V := rfl
    rw [h2, fderiv_const_smul hd' (t ^ m)]
  have heq : (fun y : Ep n => V (t • y)) = fun y => t ^ m • V y := by
    funext y; exact hV t ht y
  have key : fderiv ℝ (fun y : Ep n => V (t • y)) x = (t ^ m) • (fderiv ℝ V x) := by
    rw [heq, hcomp]
  have hkey : ∀ j : Fin n, (((fderiv ℝ V (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n))) (evec j)) j
      = (((t ^ m) • (fderiv ℝ V x)) (evec j)) j := by
    intro j
    rw [← hchain, key]
  rw [divE, divE, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := hkey j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul] at h
  simpa [mul_comm] using h


/-- Divergence of `‖·‖ • V`. -/
lemma divE_norm_smul {n : ℕ} (V : Ep n → Ep n) (x : Ep n) (hx : x ≠ 0)
    (hV : DifferentiableAt ℝ V x) :
    divE (fun y => ‖y‖ • V y) x = ‖x‖ * divE V x + (∑ i : Fin n, x i * (V x) i) / ‖x‖ := by
  have hnorm : DifferentiableAt ℝ (fun y : Ep n => ‖y‖) x :=
    (contDiffAt_norm ℝ hx).differentiableAt one_ne_zero
  rw [divE_smul (fun y : Ep n => ‖y‖) V x hnorm hV]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [pD, evec, fderiv_norm_single i x hx]
  ring

/-- Euler relation for the field `Wf`: `∑ᵢ xᵢ (Wf x)ᵢ = k · G x · Yf x`. -/
lemma dot_Wf {n : ℕ} {k : ℕ} {G Yf : Ep n → ℝ}
    (hG : ∀ t : ℝ, 0 < t → ∀ y : Ep n, G (t • y) = G y)
    (hY : ∀ t : ℝ, 0 < t → ∀ y : Ep n, Yf (t • y) = t ^ k * Yf y)
    (x : Ep n) (hdG : DifferentiableAt ℝ G x) (hdY : DifferentiableAt ℝ Yf x) :
    (∑ i : Fin n, x i * (Wf G Yf x) i) = k * G x * Yf x := by
  have h1 : (∑ i : Fin n, x i * pD i Yf x) = k * Yf x :=
    sum_coord_mul_pD_of_homogeneous hY x hdY
  have hG' : ∀ t : ℝ, 0 < t → ∀ y : Ep n, G (t • y) = t ^ 0 * G y :=
    fun s hs y => by rw [pow_zero, one_mul]; exact hG s hs y
  have h2 : (∑ i : Fin n, x i * pD i G x) = 0 := by
    simpa using sum_coord_mul_pD_of_homogeneous hG' x hdG
  have hpoint : ∀ i : Fin n, x i * (Wf G Yf x) i
      = G x * (x i * pD i Yf x) - Yf x * (x i * pD i G x) := by
    intro i; rw [Wf_coord]; ring
  rw [Finset.sum_congr rfl (fun i _ => hpoint i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, h1, h2]
  ring


/-- Partial derivative of `ψ ∘ ‖·‖`. -/
lemma pD_comp_norm {n : ℕ} (ψ : ℝ → ℝ) {x : Ep n} (hψ : DifferentiableAt ℝ ψ ‖x‖)
    (i : Fin n) (hx : x ≠ 0) :
    pD i (fun y : Ep n => ψ ‖y‖) x = deriv ψ ‖x‖ * (x i / ‖x‖) := by
  have hnorm : DifferentiableAt ℝ (fun y : Ep n => ‖y‖) x :=
    (contDiffAt_norm ℝ hx).differentiableAt one_ne_zero
  have hderiv : HasFDerivAt (fun y : Ep n => ψ ‖y‖)
      ((fderiv ℝ ψ ‖x‖) ∘L (fderiv ℝ (fun y : Ep n => ‖y‖) x)) x :=
    (hψ.hasFDerivAt).comp x hnorm.hasFDerivAt
  rw [pD, hderiv.fderiv, ContinuousLinearMap.comp_apply, evec, fderiv_norm_single i x hx]
  have h1 : (fderiv ℝ ψ ‖x‖) (x i / ‖x‖) = (x i / ‖x‖) * deriv ψ ‖x‖ := by
    have h2 : (x i / ‖x‖) = (x i / ‖x‖) • (1:ℝ) := by simp
    conv_lhs => rw [h2]
    rw [map_smul, fderiv_apply_one_eq_deriv, smul_eq_mul]
  rw [h1]
  ring

/-- The coordinate Laplacian of the polynomial function attached to a harmonic polynomial vanishes. -/
lemma lapG_eval_eq_zero {n : ℕ} (Y : MvPolynomial (Fin n) ℝ)
    (hYhar : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Y)) = 0) (x : Ep n) :
    lapG (fun z : Ep n => MvPolynomial.eval (fun i => z i) Y) x = 0 := by
  simp only [lapG, evec]
  rw [Commons.Algebra.MvPolynomial.partialDeriv2_eval Y x, hYhar]
  simp


/-- For `G` smooth off the origin, the map `y ↦ fderiv G y v` is differentiable off the origin. -/
lemma differentiableAt_fderiv_apply {n : ℕ} {G : Ep n → ℝ}
    (h : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0}) {x : Ep n} (hx : x ≠ 0) (v : Ep n) :
    DifferentiableAt ℝ (fun y : Ep n => fderiv ℝ G y v) x := by
  set s : Set (Ep n) := {x : Ep n | x ≠ 0} with hs
  have hso : IsOpen s := isOpen_ne
  have hxs : x ∈ s := hx
  have h1 := contDiffOn_fderivWithin_apply (𝕜 := ℝ) (n := ⊤) (m := ⊤) (s := s) (f := G)
    h hso.uniqueDiffOn (le_refl ⊤)
  have hmap : ContDiffOn ℝ ⊤ (fun y : Ep n => (y, v)) s := by fun_prop
  have h2 : ContDiffOn ℝ ⊤ (fun y : Ep n => (fderivWithin ℝ G s y) v) s :=
    h1.comp hmap (by intro y hy; exact ⟨hy, trivial⟩)
  have h3 : DifferentiableAt ℝ (fun y : Ep n => (fderivWithin ℝ G s y) v) x :=
    (h2 x hxs).differentiableWithinAt (by simp) |>.differentiableAt (hso.mem_nhds hxs)
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hso.mem_nhds hxs] with y hy
  exact congrArg (fun L : Ep n →L[ℝ] ℝ => L v) (fderivWithin_of_isOpen hso hy).symm



/-! ## The fixed smooth cutoff on the positive half-line -/

/-- A fixed `C^∞` cutoff on the real line, supported in `[1, 3]` and positive on `(1, 3)`. -/
def cutPhi (r : ℝ) : ℝ := Real.smoothTransition (r - 1) * Real.smoothTransition (3 - r)

lemma cutPhi_contDiff : ContDiff ℝ ∞ cutPhi := by
  unfold cutPhi
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => Real.smoothTransition (r - 1)) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub (contDiff_const (c := (1:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => Real.smoothTransition (3 - r)) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const (c := (3:ℝ))).sub contDiff_id)
  simpa [cutPhi] using h1.mul h2

lemma cutPhi_nonneg (r : ℝ) : 0 ≤ cutPhi r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma cutPhi_eq_zero_of_le_one {r : ℝ} (h : r ≤ 1) : cutPhi r = 0 := by
  unfold cutPhi
  rw [Real.smoothTransition.zero_of_nonpos (x := r - 1) (by linarith), zero_mul]

lemma cutPhi_eq_zero_of_three_le {r : ℝ} (h : 3 ≤ r) : cutPhi r = 0 := by
  unfold cutPhi
  rw [Real.smoothTransition.zero_of_nonpos (x := 3 - r) (by linarith), mul_zero]

lemma cutPhi_pos_of_mem {r : ℝ} (h1 : 1 < r) (h2 : r < 3) : 0 < cutPhi r := by
  unfold cutPhi
  exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
    (Real.smoothTransition.pos_of_pos (by linarith))

lemma cutPhi_hasCompactSupport : HasCompactSupport cutPhi := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1:ℝ) 3) isCompact_Icc ?_
  intro r hr
  simp only [Function.mem_support] at hr
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    exact hr (cutPhi_eq_zero_of_le_one (by linarith))
  · by_contra h
    exact hr (cutPhi_eq_zero_of_three_le (by linarith))

lemma cutPhi_mul_rpow_hasCompactSupport (M : ℕ) :
    HasCompactSupport (fun r : ℝ => cutPhi r * r ^ M) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1:ℝ) 3) isCompact_Icc ?_
  intro r hr
  simp only [Function.mem_support] at hr
  have hphi : cutPhi r ≠ 0 := fun h => hr (by rw [h, zero_mul])
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    exact hphi (cutPhi_eq_zero_of_le_one (by linarith))
  · by_contra h
    exact hphi (cutPhi_eq_zero_of_three_le (by linarith))

lemma continuous_cutPhi : Continuous cutPhi := cutPhi_contDiff.continuous

lemma cutPhi_mul_rpow_continuous (M : ℕ) :
    Continuous (fun r : ℝ => cutPhi r * r ^ M) :=
  continuous_cutPhi.mul (continuous_id.pow M)

/-- The radial integral of the cutoff against `r^M` is positive. -/
lemma cutPhi_rpow_integral_pos (M : ℕ) :
    0 < ∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ M := by
  rw [show (∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ M)
      = ∫ r, cutPhi r * r ^ M ∂(volume.restrict (Set.Ioi (0 : ℝ))) from rfl]
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg]
  · have hsub : Set.Ioo (1:ℝ) 2 ⊆ Function.support (fun r : ℝ => cutPhi r * r ^ M) := by
      intro r hr
      simp only [Set.mem_Ioo] at hr
      simp only [Function.mem_support]
      have h1 : 0 < cutPhi r := cutPhi_pos_of_mem hr.1 (by linarith)
      have h2 : 0 < r ^ M := pow_pos (by linarith) M
      positivity
    have hmeas : volume.restrict (Set.Ioi (0:ℝ)) (Set.Ioo (1:ℝ) 2) = 1 := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo (1:ℝ) 2 ∩ Set.Ioi 0 = Set.Ioo (1:ℝ) 2 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
        constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, by linarith [h.1]⟩
      rw [hinter, Real.volume_Ioo]
      norm_num
    calc 0 < (volume.restrict (Set.Ioi (0:ℝ))) (Set.Ioo (1:ℝ) 2) := by rw [hmeas]; norm_num
      _ ≤ _ := measure_mono hsub
  · intro r
    show 0 ≤ cutPhi r * r ^ M
    by_cases h : r ≤ 1
    · rw [cutPhi_eq_zero_of_le_one h, zero_mul]
    · have hr : 0 < r := lt_of_le_of_lt (by norm_num) (not_le.mp h)
      exact mul_nonneg (cutPhi_nonneg r) (pow_nonneg hr.le M)
  · exact (cutPhi_mul_rpow_continuous M).integrable_of_hasCompactSupport
      (cutPhi_mul_rpow_hasCompactSupport M)


/-! ## Smoothness and differentiability of the auxiliary objects -/

lemma differentiableAt_of_contDiffOn_compl_zero {G : Ep n → ℝ}
    (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0}) {x : Ep n} (hx : x ≠ 0) :
    DifferentiableAt ℝ G x :=
  (hG.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt (by simp)

lemma contDiffOn_fderiv_apply_compl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Ep n → F} (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0}) (v : Ep n) :
    ContDiffOn ℝ ⊤ (fun y : Ep n => fderiv ℝ G y v) {x : Ep n | x ≠ 0} :=
  Commons.Analysis.Calculus.contDiffOn_fderiv_apply hG isOpen_ne v

lemma differentiableAt_fderiv_apply_of_contDiff {G : Ep n → ℝ} (hG : ContDiff ℝ ⊤ G)
    (v : Ep n) (x : Ep n) :
    DifferentiableAt ℝ (fun y : Ep n => fderiv ℝ G y v) x :=
  (((Commons.Analysis.Calculus.contDiffOn_fderiv_apply hG.contDiffOn isOpen_univ v).differentiableOn
      (by simp)).differentiableAt (by simp))

lemma differentiableAt_fderiv_apply_compl {G : Ep n → ℝ}
    (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0}) {x : Ep n} (hx : x ≠ 0) (v : Ep n) :
    DifferentiableAt ℝ (fun y : Ep n => fderiv ℝ G y v) x :=
  (differentiableAt_fderiv_apply hG hx v)

/-- `lapG G` is `C^∞` off the origin. -/
lemma contDiffOn_lapG {G : Ep n → ℝ}
    (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0}) :
    ContDiffOn ℝ ⊤ (fun x : Ep n => lapG G x) {x : Ep n | x ≠ 0} := by
  have hsum : ContDiffOn ℝ ⊤ (fun y : Ep n => ∑ i : Fin n,
      fderiv ℝ (fun z : Ep n => fderiv ℝ G z (evec i)) y (evec i))
      {x : Ep n | x ≠ 0} :=
    ContDiffOn.sum (fun i _ => contDiffOn_fderiv_apply_compl
      (contDiffOn_fderiv_apply_compl hG (evec i)) (evec i))
  refine hsum.congr (fun y _ => ?_)
  simp only [lapG]

/-- `Wf G Yf` is `C^∞` off the origin. -/
lemma contDiffOn_Wf {G : Ep n → ℝ} (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0})
    {Yf : Ep n → ℝ} (hYf : ContDiff ℝ ⊤ Yf) :
    ContDiffOn ℝ ⊤ (Wf G Yf) {x : Ep n | x ≠ 0} := by
  have hYfOn : ContDiffOn ℝ ⊤ Yf {x : Ep n | x ≠ 0} := hYf.contDiffOn
  have hterm : ∀ i : Fin n, ContDiffOn ℝ ⊤ (fun y : Ep n =>
      (G y * pD i Yf y - Yf y * pD i G y) • evec i) {x : Ep n | x ≠ 0} := by
    intro i
    have h1 : ContDiffOn ℝ ⊤ (fun y : Ep n => G y * pD i Yf y - Yf y * pD i G y)
        {x : Ep n | x ≠ 0} :=
      (hG.mul (contDiffOn_fderiv_apply_compl hYfOn (evec i))).sub
        (hYfOn.mul (contDiffOn_fderiv_apply_compl hG (evec i)))
    exact h1.smul (contDiffOn_const (c := evec i))
  have hsum : ContDiffOn ℝ ⊤ (fun y : Ep n => ∑ i : Fin n,
      (G y * pD i Yf y - Yf y * pD i G y) • evec i) {x : Ep n | x ≠ 0} :=
    ContDiffOn.sum (fun i _ => hterm i)
  refine hsum.congr (fun y _ => ?_)
  simp only [Wf]

/-- The coordinate divergence of `Wf G Yf` is `C^∞` off the origin. -/
lemma contDiffOn_divE_Wf {G : Ep n → ℝ} (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0})
    {Yf : Ep n → ℝ} (hYf : ContDiff ℝ ⊤ Yf) :
    ContDiffOn ℝ ⊤ (fun y : Ep n => divE (Wf G Yf) y) {x : Ep n | x ≠ 0} := by
  have hW := contDiffOn_Wf hG hYf
  have hterm : ∀ i : Fin n, ContDiffOn ℝ ⊤ (fun y : Ep n =>
      (fderiv ℝ (Wf G Yf) y (evec i)) i) {x : Ep n | x ≠ 0} := by
    intro i
    have h1 := contDiffOn_fderiv_apply_compl hW (evec i)
    have hg := ContinuousLinearMap.contDiff (n := ⊤)
      (EuclideanSpace.proj (𝕜 := ℝ) i : Ep n →L[ℝ] ℝ)
    simpa only [coord_proj, Function.comp_def] using hg.comp_contDiffOn h1
  have hsum : ContDiffOn ℝ ⊤ (fun y : Ep n => ∑ i : Fin n,
      (fderiv ℝ (Wf G Yf) y (evec i)) i) {x : Ep n | x ≠ 0} :=
    ContDiffOn.sum (fun i _ => hterm i)
  simpa [divE] using hsum

/-- Pointwise identity `div (Wf G Yf) = -Yf * lapG G` for harmonic `Yf`. -/
lemma divE_Wf_eq_neg {G : Ep n → ℝ} (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0})
    {Yf : Ep n → ℝ} (hYf : ContDiff ℝ ⊤ Yf)
    (hYf_lap : ∀ x : Ep n, lapG Yf x = 0) {x : Ep n} (hx : x ≠ 0) :
    divE (Wf G Yf) x = - (Yf x * lapG G x) := by
  have hGx : DifferentiableAt ℝ G x := differentiableAt_of_contDiffOn_compl_zero hG hx
  have hYfx : DifferentiableAt ℝ Yf x := (hYf.differentiable (by simp)).differentiableAt
  have hGY : ∀ j : Fin n, DifferentiableAt ℝ (fun y : Ep n => pD j G y) x :=
    fun j => differentiableAt_fderiv_apply hG hx (evec j)
  have hYY : ∀ j : Fin n, DifferentiableAt ℝ (fun y : Ep n => pD j Yf y) x :=
    fun j => differentiableAt_fderiv_apply_of_contDiff hYf (evec j) x
  rw [divE_Wf G Yf x hGx hYfx hGY hYY, hYf_lap x]
  ring


/-! ## The cutoff field `χ • W` and its divergence -/

/-- `r ↦ r * cutPhi r`: the radial profile of the cutoff; it vanishes near `0`. -/
def cutPsi (r : ℝ) : ℝ := r * cutPhi r

lemma cutPsi_contDiff : ContDiff ℝ ∞ cutPsi :=
  contDiff_id.mul cutPhi_contDiff

lemma cutPsi_eq_zero_of_le_one {r : ℝ} (h : r ≤ 1) : cutPsi r = 0 := by
  simp [cutPsi, cutPhi_eq_zero_of_le_one h]

lemma cutPsi_eq_zero_of_three_le {r : ℝ} (h : 3 ≤ r) : cutPsi r = 0 := by
  simp [cutPsi, cutPhi_eq_zero_of_three_le h]

lemma cutPsi_hasCompactSupport : HasCompactSupport cutPsi := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1:ℝ) 3) isCompact_Icc ?_
  intro r hr
  simp only [Function.mem_support] at hr
  have hphi : cutPhi r ≠ 0 := fun h => hr (by simp [cutPsi, h])
  exact ⟨by by_contra hh; exact hphi (cutPhi_eq_zero_of_le_one (by linarith)),
         by by_contra hh; exact hphi (cutPhi_eq_zero_of_three_le (by linarith))⟩

lemma continuous_cutPsi : Continuous cutPsi := cutPsi_contDiff.continuous

lemma hasCompactSupport_deriv_cutPsi : HasCompactSupport (deriv cutPsi) :=
  cutPsi_hasCompactSupport.deriv

/-- The cutoff vector field `x ↦ ψ(‖x‖) • W x`. -/
def cutField (W : Ep n → Ep n) (x : Ep n) : Ep n := cutPsi ‖x‖ • W x

lemma cutField_contDiffOn {W : Ep n → Ep n}
    (hW : ContDiffOn ℝ ∞ W {x : Ep n | x ≠ 0}) :
    ContDiffOn ℝ ∞ (cutField W) {x : Ep n | x ≠ 0} := by
  have hnorm : ContDiffOn ℝ ∞ (fun x : Ep n => ‖x‖) {x : Ep n | x ≠ 0} :=
    ContDiffOn.norm ℝ (contDiffOn_id (s := {x : Ep n | x ≠ 0}) (n := ∞)) (fun x hx => hx)
  have hpsi : ContDiffOn ℝ ∞ (fun x : Ep n => cutPsi ‖x‖) {x : Ep n | x ≠ 0} :=
    cutPsi_contDiff.comp_contDiffOn hnorm
  exact hpsi.smul hW

lemma cutField_contDiff {W : Ep n → Ep n} (hW : ContDiffOn ℝ ∞ W {x : Ep n | x ≠ 0}) :
    ContDiff ℝ 1 (cutField W) := by
  refine Commons.Analysis.Calculus.contDiff_of_contDiffOn_compl_zero (n := (1 : WithTop ℕ∞)) ?_ ?_
  · exact (cutField_contDiffOn hW).of_le (by norm_num)
  · filter_upwards [Metric.ball_mem_nhds (0 : Ep n) zero_lt_one] with x hx
    have hx1 : ‖x‖ ≤ 1 := by
      have h := Metric.mem_ball.mp hx
      rw [dist_eq_norm, sub_zero] at h
      linarith
    simp only [cutField]
    rw [cutPsi_eq_zero_of_le_one hx1, zero_smul]

lemma cutField_hasCompactSupport (W : Ep n → Ep n) : HasCompactSupport (cutField W) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : Ep n) 3) (isCompact_closedBall 0 3) ?_
  intro x hx
  simp only [Function.mem_support] at hx
  have hpsi : cutPsi ‖x‖ ≠ 0 := fun h => hx (by simp [cutField, h])
  have h3 : ‖x‖ ≤ 3 := by
    by_contra h
    exact hpsi (cutPsi_eq_zero_of_three_le (le_of_lt (not_le.mp h)))
  simpa only [Metric.mem_closedBall, dist_zero_right] using h3

/-- The divergence of the cutoff field integrates to zero. -/
lemma integral_divE_cutField [Nonempty (Fin n)] {W : Ep n → Ep n}
    (hW : ContDiffOn ℝ ∞ W {x : Ep n | x ≠ 0}) :
    (∫ x : Ep n, divE (cutField W) x) = 0 :=
  Commons.Analysis.MeasureTheory.integral_divergence_eq_zero_euclidean (cutField W)
    (cutField_contDiff hW) (cutField_hasCompactSupport W)

/-- `‖x‖ * div W x` is the "degree `m`" companion of a degree-`m` field `W`. -/
def h1fun (W : Ep n → Ep n) (x : Ep n) : ℝ := ‖x‖ * divE W x

/-- `⟨x, W x⟩ / ‖x‖`, the "degree `m`" companion of a degree-`m` field `W`. -/
def h4fun (W : Ep n → Ep n) (x : Ep n) : ℝ := (‖x‖)⁻¹ * ∑ i : Fin n, x i * (W x) i

lemma divE_smul_homogeneous_of_ne {m : ℕ} {V : Ep n → Ep n}
    (hV : ∀ (t : ℝ), 0 < t → ∀ x : Ep n, x ≠ 0 → V (t • x) = t ^ m • V x)
    {t : ℝ} (ht : 0 < t) {x : Ep n} (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ V (t • x)) (hd' : DifferentiableAt ℝ V x) :
    t * divE V (t • x) = t ^ m * divE V x := by
  have hinner : HasFDerivAt (fun y : Ep n => t • y) (t • (1 : Ep n →L[ℝ] Ep n)) x := by
    have h := ContinuousLinearMap.hasFDerivAt (t • (1 : Ep n →L[ℝ] Ep n)) (x := x)
    convert h using 1
    ext y; simp
  have hchain : fderiv ℝ (fun y : Ep n => V (t • y)) x
      = (fderiv ℝ V (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n)) :=
    (hd.hasFDerivAt.comp x hinner).fderiv
  have heq : (fun y : Ep n => V (t • y)) =ᶠ[𝓝 x] (fun y : Ep n => t ^ m • V y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact hV t ht y hy
  have hcomp : fderiv ℝ (fun y : Ep n => t ^ m • V y) x = (t ^ m) • (fderiv ℝ V x) := by
    have h2 : (fun y : Ep n => t ^ m • V y) = (t ^ m) • V := rfl
    rw [h2, fderiv_const_smul hd' (t ^ m)]
  have key : fderiv ℝ (fun y : Ep n => V (t • y)) x = (t ^ m) • (fderiv ℝ V x) := by
    rw [heq.fderiv_eq, hcomp]
  have hkey : ∀ j : Fin n, (((fderiv ℝ V (t • x)) ∘L (t • (1 : Ep n →L[ℝ] Ep n))) (evec j)) j
      = (((t ^ m) • (fderiv ℝ V x)) (evec j)) j := by
    intro j
    rw [← hchain, key]
  rw [divE, divE, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := hkey j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul] at h
  simpa [mul_comm] using h

lemma h1fun_smul_of_homogeneous {m : ℕ} {V : Ep n → Ep n}
    (hV : ∀ (t : ℝ), 0 < t → ∀ x : Ep n, x ≠ 0 → V (t • x) = t ^ m • V x)
    {t : ℝ} (ht : 0 < t) {x : Ep n} (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ V (t • x)) (hd' : DifferentiableAt ℝ V x) :
    h1fun V (t • x) = t ^ m * h1fun V x := by
  have hdiv : t * divE V (t • x) = t ^ m * divE V x :=
    divE_smul_homogeneous_of_ne (V := V) (m := m) hV ht hx hd hd'
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have h2 : ‖x‖ * (t * divE V (t • x)) = ‖x‖ * (t ^ m * divE V x) := by rw [hdiv]
  rw [h1fun, hnorm]
  calc (t * ‖x‖) * divE V (t • x) = ‖x‖ * (t * divE V (t • x)) := by ring
    _ = ‖x‖ * (t ^ m * divE V x) := h2
    _ = t ^ m * (‖x‖ * divE V x) := by ring

lemma h4fun_smul_of_homogeneous {m : ℕ} {V : Ep n → Ep n}
    (hV : ∀ (t : ℝ), 0 < t → ∀ x : Ep n, x ≠ 0 → V (t • x) = t ^ m • V x)
    {t : ℝ} (ht : 0 < t) {x : Ep n} (hx : x ≠ 0) :
    h4fun V (t • x) = t ^ m * h4fun V x := by
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hcoord : ∀ i : Fin n, (t • x : Ep n) i * (V (t • x)) i
      = t ^ (m + 1) * (x i * (V x) i) := by
    intro i
    rw [hV t ht x hx, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [h4fun, h4fun, hnorm]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i), ← Finset.mul_sum]
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have htne : t ≠ 0 := ne_of_gt ht
  field_simp
  ring

/-- Pointwise computation of the divergence of the cutoff field. -/
lemma divE_cutField {W : Ep n → Ep n} {x : Ep n} (hx : x ≠ 0)
    (hdpsi : DifferentiableAt ℝ (fun y : Ep n => cutPsi ‖y‖) x)
    (hdW : DifferentiableAt ℝ W x) :
    divE (cutField W) x = cutPhi ‖x‖ * h1fun W x + deriv cutPsi ‖x‖ * h4fun W x := by
  have hpsi_diff : DifferentiableAt ℝ cutPsi ‖x‖ :=
    (cutPsi_contDiff.differentiable (by simp)).differentiableAt
  have hterm : ∀ i : Fin n, pD i (fun y : Ep n => cutPsi ‖y‖) x * (W x) i
      = deriv cutPsi ‖x‖ * ((x i / ‖x‖) * (W x) i) := by
    intro i
    rw [pD_comp_norm cutPsi hpsi_diff i hx]
    ring
  have hsum : (∑ i : Fin n, pD i (fun y : Ep n => cutPsi ‖y‖) x * (W x) i)
      = deriv cutPsi ‖x‖ * h4fun W x := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    congr 1
    rw [h4fun, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_eq_inv_mul]
    ring
  have hfst : cutPsi ‖x‖ * divE W x = cutPhi ‖x‖ * h1fun W x := by
    rw [h1fun, cutPsi]
    ring
  change divE (fun y : Ep n => cutPsi ‖y‖ • W y) x = _
  rw [divE_smul (fun y : Ep n => cutPsi ‖y‖) W x hdpsi hdW, hsum, hfst]


/-! ## Continuity and compact support of the two integrands -/

lemma continuous_of_continuousOn_compl_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Ep n → F} (h : ContinuousOn f {x : Ep n | x ≠ 0})
    (h0 : Filter.EventuallyEq (nhds (0 : Ep n)) f (fun _ => 0)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    exact (continuousAt_const (x := (0 : Ep n)) (y := (0 : F))).congr_of_eventuallyEq h0
  · exact h.continuousAt (isOpen_ne.mem_nhds hx)

lemma differentiableAt_cutPsi_comp_norm {x : Ep n} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : Ep n => cutPsi ‖y‖) x := by
  have hnorm : ContDiffOn ℝ ∞ (fun y : Ep n => ‖y‖) {x : Ep n | x ≠ 0} :=
    ContDiffOn.norm ℝ (contDiffOn_id (s := {x : Ep n | x ≠ 0}) (n := ∞)) (fun x hx => hx)
  exact ((cutPsi_contDiff.comp_contDiffOn hnorm).contDiffAt
    (isOpen_ne.mem_nhds hx)).differentiableAt (by simp)

lemma deriv_cutPsi_eq_zero_of_lt_one {r : ℝ} (hr : r < 1) : deriv cutPsi r = 0 := by
  have h : cutPsi =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds r (show (0:ℝ) < (1 - r)/2 by linarith)] with s hs
    have hs1 : s < 1 := by
      have h2 := Metric.mem_ball.mp hs
      rw [dist_eq_norm, Real.norm_eq_abs] at h2
      rcases abs_lt.mp h2 with ⟨h2a, h2b⟩
      linarith
    exact cutPsi_eq_zero_of_le_one hs1.le
  rw [h.deriv_eq, deriv_const]

lemma deriv_cutPsi_eq_zero_of_three_lt {r : ℝ} (hr : 3 < r) : deriv cutPsi r = 0 := by
  have h : cutPsi =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds r (show (0:ℝ) < (r - 3)/2 by linarith)] with s hs
    have hs3 : 3 ≤ s := by
      have h2 := Metric.mem_ball.mp hs
      rw [dist_eq_norm, Real.norm_eq_abs] at h2
      rcases abs_lt.mp h2 with ⟨h2a, h2b⟩
      linarith
    exact cutPsi_eq_zero_of_three_le hs3
  rw [h.deriv_eq, deriv_const]

lemma continuous_deriv_cutPsi : Continuous (deriv cutPsi) :=
  cutPsi_contDiff.continuous_deriv (by simp)

lemma continuous_cutPhi_mul_h1 {V : Ep n → Ep n}
    (hVc : ContinuousOn (fun x : Ep n => divE V x) {x : Ep n | x ≠ 0}) :
    Continuous (fun x : Ep n => cutPhi ‖x‖ * h1fun V x) := by
  refine continuous_of_continuousOn_compl_zero ?_ ?_
  · have hphi : ContinuousOn (fun x : Ep n => cutPhi ‖x‖) {x : Ep n | x ≠ 0} :=
      (cutPhi_contDiff.continuous.comp continuous_norm).continuousOn
    have hn : ContinuousOn (fun x : Ep n => h1fun V x) {x : Ep n | x ≠ 0} := by
      have h : ContinuousOn (fun x : Ep n => ‖x‖ * divE V x) {x : Ep n | x ≠ 0} :=
        continuous_norm.continuousOn.mul hVc
      simpa only [h1fun] using h
    exact hphi.mul hn
  · filter_upwards [Metric.ball_mem_nhds (0 : Ep n) zero_lt_one] with x hx
    have hx1 : ‖x‖ ≤ 1 := by
      have h := Metric.mem_ball.mp hx
      rw [dist_eq_norm, sub_zero] at h
      linarith
    simp only [h1fun]
    rw [cutPhi_eq_zero_of_le_one hx1, zero_mul]

lemma hasCompactSupport_cutPhi_mul_h1 (V : Ep n → Ep n) :
    HasCompactSupport (fun x : Ep n => cutPhi ‖x‖ * h1fun V x) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : Ep n) 3) (isCompact_closedBall 0 3) ?_
  intro x hx
  simp only [Function.mem_support] at hx
  simp only [h1fun] at hx
  have hphi : cutPhi ‖x‖ ≠ 0 := fun h => hx (by rw [h, zero_mul])
  have h3 : ‖x‖ ≤ 3 := by
    by_contra h
    exact hphi (cutPhi_eq_zero_of_three_le (le_of_lt (not_le.mp h)))
  simpa only [Metric.mem_closedBall, dist_zero_right] using h3

lemma continuous_deriv_cutPsi_mul_h4 {V : Ep n → Ep n}
    (hVc : ContinuousOn V {x : Ep n | x ≠ 0}) :
    Continuous (fun x : Ep n => deriv cutPsi ‖x‖ * h4fun V x) := by
  refine continuous_of_continuousOn_compl_zero ?_ ?_
  · have h1 : ContinuousOn (fun x : Ep n => deriv cutPsi ‖x‖) {x : Ep n | x ≠ 0} :=
      (continuous_deriv_cutPsi.comp continuous_norm).continuousOn
    have h2 : ContinuousOn (fun x : Ep n => h4fun V x) {x : Ep n | x ≠ 0} := by
      have hinv : ContinuousOn (fun x : Ep n => (‖x‖)⁻¹) {x : Ep n | x ≠ 0} :=
        ContinuousOn.comp (continuousOn_inv₀ (G₀ := ℝ)) (continuous_norm.continuousOn)
          (fun x hx => by simpa using hx)
      have hsum : ContinuousOn (fun x : Ep n => ∑ i : Fin n, x i * (V x) i)
          {x : Ep n | x ≠ 0} := by
        refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
        have hxi : ContinuousOn (fun x : Ep n => x i) {x : Ep n | x ≠ 0} :=
          (ContinuousLinearMap.continuous (EuclideanSpace.proj (𝕜 := ℝ) i)).continuousOn
        have hVi : ContinuousOn (fun x : Ep n => (V x) i) {x : Ep n | x ≠ 0} := by
          have h := (ContinuousLinearMap.continuous
            (EuclideanSpace.proj (𝕜 := ℝ) i : Ep n →L[ℝ] ℝ)).comp_continuousOn hVc
          simpa only [Function.comp_def, coord_proj] using h
        exact hxi.mul hVi
      have hprod : ContinuousOn (fun x : Ep n => (‖x‖)⁻¹ * ∑ i : Fin n, x i * (V x) i)
          {x : Ep n | x ≠ 0} := hinv.mul hsum
      simpa only [h4fun] using hprod
    exact h1.mul h2
  · filter_upwards [Metric.ball_mem_nhds (0 : Ep n) zero_lt_one] with x hx
    have hx1 : ‖x‖ < 1 := by
      have h := Metric.mem_ball.mp hx
      rwa [dist_eq_norm, sub_zero] at h
    rw [deriv_cutPsi_eq_zero_of_lt_one hx1, zero_mul]

lemma hasCompactSupport_deriv_cutPsi_mul_h4 (V : Ep n → Ep n) :
    HasCompactSupport (fun x : Ep n => deriv cutPsi ‖x‖ * h4fun V x) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : Ep n) 3) (isCompact_closedBall 0 3) ?_
  intro x hx
  simp only [Function.mem_support] at hx
  have hder : deriv cutPsi ‖x‖ ≠ 0 := fun h => hx (by rw [h, zero_mul])
  have h3 : ‖x‖ ≤ 3 := by
    by_contra h
    exact hder (deriv_cutPsi_eq_zero_of_three_lt (not_le.mp h))
  simpa only [Metric.mem_closedBall, dist_zero_right] using h3


lemma ne_zero_of_mem_sphere {θ : Metric.sphere (0 : Ep n) 1} : (θ : Ep n) ≠ 0 := by
  intro h
  have h2 := mem_sphere_zero_iff_norm.mp θ.2
  rw [h, norm_zero] at h2
  norm_num at h2

/-- The core identity: the spherical integral of `div (Wf G Yf)` equals
`(n - 1 + (k - 1)) * k` times the spherical integral of `G * Yf`. -/
theorem sphere_divE_Wf [Nonempty (Fin n)] {k : ℕ} (hk : 1 ≤ k)
    {G : Ep n → ℝ} (hG : ContDiffOn ℝ ⊤ G {x : Ep n | x ≠ 0})
    (hGs : ∀ (t : ℝ), 0 < t → ∀ x : Ep n, G (t • x) = G x)
    {Yf : Ep n → ℝ} (hYf : ContDiff ℝ ⊤ Yf)
    (hYs : ∀ (t : ℝ), 0 < t → ∀ x : Ep n, Yf (t • x) = t ^ k * Yf x) :
    (∫ θ : Metric.sphere (0 : Ep n) 1, divE (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
      = ((n - 1 + (k - 1) : ℕ) : ℝ) * (k : ℝ) *
        (∫ θ : Metric.sphere (0 : Ep n) 1, G (θ : Ep n) * Yf (θ : Ep n) ∂volume.toSphere) := by
  classical
  -- smoothness / differentiability facts
  have hWsm : ContDiffOn ℝ ∞ (Wf G Yf) {x : Ep n | x ≠ 0} := (contDiffOn_Wf hG hYf).of_le le_top
  have hdivsm : ContDiffOn ℝ ∞ (fun x : Ep n => divE (Wf G Yf) x) {x : Ep n | x ≠ 0} :=
    (contDiffOn_divE_Wf hG hYf).of_le le_top
  have hWcont : ContinuousOn (Wf G Yf) {x : Ep n | x ≠ 0} := hWsm.continuousOn
  have hdivcont : ContinuousOn (fun x : Ep n => divE (Wf G Yf) x) {x : Ep n | x ≠ 0} :=
    hdivsm.continuousOn
  have hWdiff : ∀ x : Ep n, x ≠ 0 → DifferentiableAt ℝ (Wf G Yf) x :=
    fun x hx => (hWsm.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt (by simp)
  have hYfdiff : ∀ x : Ep n, DifferentiableAt ℝ Yf x :=
    fun x => (hYf.differentiable (by simp)).differentiableAt
  have hWhom : ∀ (t : ℝ), 0 < t → ∀ x : Ep n, x ≠ 0 →
      Wf G Yf (t • x) = t ^ (k - 1) • Wf G Yf x := by
    intro t ht x hx
    have htx : t • x ≠ 0 := by
      intro h
      rcases smul_eq_zero.mp h with h' | h'
      · exact (ne_of_gt ht) h'
      · exact hx h'
    exact Wf_smul hk hGs hYs ht x (differentiableAt_of_contDiffOn_compl_zero hG htx)
      (differentiableAt_of_contDiffOn_compl_zero hG hx) (hYfdiff (t • x)) (hYfdiff x)
  -- integrability of the two pieces of the divergence of the cutoff field
  have hAint : Integrable (fun x : Ep n => cutPhi ‖x‖ * h1fun (Wf G Yf) x) volume :=
    (continuous_cutPhi_mul_h1 hdivcont).integrable_of_hasCompactSupport
      (hasCompactSupport_cutPhi_mul_h1 _)
  have hBint : Integrable (fun x : Ep n => deriv cutPsi ‖x‖ * h4fun (Wf G Yf) x) volume :=
    (continuous_deriv_cutPsi_mul_h4 hWcont).integrable_of_hasCompactSupport
      (hasCompactSupport_deriv_cutPsi_mul_h4 _)
  have hae : ∀ᵐ x ∂(volume : Measure (Ep n)), x ≠ 0 := by
    rw [MeasureTheory.ae_iff, show {x : Ep n | ¬ x ≠ 0} = {0} by ext x; simp]
    exact measure_singleton 0
  -- the divergence of the cutoff field splits into the two pieces, and integrates to zero
  have hdivdecomp : (∫ x : Ep n, divE (cutField (Wf G Yf)) x)
      = (∫ x : Ep n, cutPhi ‖x‖ * h1fun (Wf G Yf) x)
        + ∫ x : Ep n, deriv cutPsi ‖x‖ * h4fun (Wf G Yf) x := by
    calc (∫ x : Ep n, divE (cutField (Wf G Yf)) x)
        = ∫ x : Ep n, (cutPhi ‖x‖ * h1fun (Wf G Yf) x
            + deriv cutPsi ‖x‖ * h4fun (Wf G Yf) x) := by
          apply integral_congr_ae
          filter_upwards [hae] with x hx
          have := divE_cutField (W := Wf G Yf) hx (differentiableAt_cutPsi_comp_norm hx)
            (hWdiff x hx)
          simpa only [cutField] using this
      _ = _ + _ := integral_add hAint hBint
  have hzero : (∫ x : Ep n, divE (cutField (Wf G Yf)) x) = 0 := integral_divE_cutField hWsm
  have hAB : (∫ x : Ep n, cutPhi ‖x‖ * h1fun (Wf G Yf) x)
      + (∫ x : Ep n, deriv cutPsi ‖x‖ * h4fun (Wf G Yf) x) = 0 := by
    rw [← hdivdecomp, hzero]
  -- homogeneity of the two scalar companions
  have h1hom : ∀ (t : ℝ) (x : Ep n), 0 < t → x ≠ 0 →
      h1fun (Wf G Yf) (t • x) = t ^ (k - 1) * h1fun (Wf G Yf) x := by
    intro t x ht hx
    have htx : t • x ≠ 0 := by
      intro h
      rcases smul_eq_zero.mp h with h' | h'
      · exact (ne_of_gt ht) h'
      · exact hx h'
    exact h1fun_smul_of_homogeneous hWhom ht hx (hWdiff (t • x) htx) (hWdiff x hx)
  have h4hom : ∀ (t : ℝ) (x : Ep n), 0 < t → x ≠ 0 →
      h4fun (Wf G Yf) (t • x) = t ^ (k - 1) * h4fun (Wf G Yf) x := by
    intro t x ht hx
    exact h4fun_smul_of_homogeneous hWhom ht hx
  -- radial factorisation of the two integrals
  have hArad := integral_radial_mul_homogeneous (n := n) cutPhi cutPhi_contDiff.continuous
    cutPhi_hasCompactSupport (h1fun (Wf G Yf)) (k - 1) h1hom hAint
  have hBrad := integral_radial_mul_homogeneous (n := n) (deriv cutPsi) continuous_deriv_cutPsi
    hasCompactSupport_deriv_cutPsi (h4fun (Wf G Yf)) (k - 1) h4hom hBint
  -- spherical integrals of the companions
  have hsph1 : (∫ θ : Metric.sphere (0 : Ep n) 1, h1fun (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
      = (∫ θ : Metric.sphere (0 : Ep n) 1,
          divE (Wf G Yf) (θ : Ep n) ∂volume.toSphere) := by
    apply integral_congr_ae
    filter_upwards with θ
    rw [h1fun, mem_sphere_zero_iff_norm.mp θ.2, one_mul]
  have hsph4 : (∫ θ : Metric.sphere (0 : Ep n) 1, h4fun (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
      = (k : ℝ) * (∫ θ : Metric.sphere (0 : Ep n) 1,
          G (θ : Ep n) * Yf (θ : Ep n) ∂volume.toSphere) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with θ
    have hθ : (θ : Ep n) ≠ 0 := ne_zero_of_mem_sphere
    have hdot := dot_Wf hGs hYs (θ : Ep n) (differentiableAt_of_contDiffOn_compl_zero hG hθ)
      (hYfdiff (θ : Ep n))
    rw [h4fun, mem_sphere_zero_iff_norm.mp θ.2, inv_one, one_mul, hdot]
    ring
  -- the integration by parts
  have hcd : ContDiff ℝ 1 cutPsi := cutPsi_contDiff.of_le (by simp)
  have hIBP : (∫ r in Set.Ioi (0 : ℝ), deriv cutPsi r * r ^ (n - 1 + (k - 1)))
      = -((((n - 1 + (k - 1) : ℕ)) : ℝ)
          * ∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1))) := by
    have h := Commons.Analysis.Real.integral_Ioi_deriv_mul_pow_boundary
      (n - 1 + (k - 1)) cutPsi hcd cutPsi_hasCompactSupport
    rw [cutPsi_eq_zero_of_le_one (show (0:ℝ) ≤ 1 by norm_num), zero_mul, neg_zero,
      zero_sub] at h
    rw [h]
    by_cases hM0 : n - 1 + (k - 1) = 0
    · rw [hM0]; simp
    · have hM1 : 1 ≤ n - 1 + (k - 1) := Nat.one_le_iff_ne_zero.mpr hM0
      have heq : (∫ r in Set.Ioi (0 : ℝ), cutPsi r * r ^ (n - 1 + (k - 1) - 1))
          = (∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        show cutPsi r * r ^ (n - 1 + (k - 1) - 1) = cutPhi r * r ^ (n - 1 + (k - 1))
        rw [cutPsi]
        calc (r * cutPhi r) * r ^ (n - 1 + (k - 1) - 1)
            = cutPhi r * (r * r ^ (n - 1 + (k - 1) - 1)) := by ring
          _ = cutPhi r * r ^ (n - 1 + (k - 1)) := by
                rw [← pow_succ', Nat.sub_add_cancel hM1]
      rw [heq]
  -- final assembly
  have hABval : ((∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1)))
        * (∫ θ : Metric.sphere (0 : Ep n) 1, divE (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
      + (-((((n - 1 + (k - 1) : ℕ)) : ℝ)
          * ∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1))))
        * ((k : ℝ) * (∫ θ : Metric.sphere (0 : Ep n) 1,
            G (θ : Ep n) * Yf (θ : Ep n) ∂volume.toSphere))) = 0 := by
    calc (∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1)))
          * (∫ θ : Metric.sphere (0 : Ep n) 1, divE (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
        + (-((((n - 1 + (k - 1) : ℕ)) : ℝ)
            * ∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1))))
          * ((k : ℝ) * (∫ θ : Metric.sphere (0 : Ep n) 1,
              G (θ : Ep n) * Yf (θ : Ep n) ∂volume.toSphere))
        = (∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1)))
            * (∫ θ : Metric.sphere (0 : Ep n) 1,
                h1fun (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
          + (-((((n - 1 + (k - 1) : ℕ)) : ℝ)
              * ∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1))))
            * (∫ θ : Metric.sphere (0 : Ep n) 1,
                h4fun (Wf G Yf) (θ : Ep n) ∂volume.toSphere) := by
            rw [← hsph1, ← hsph4]
      _ = (∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1)))
            * (∫ θ : Metric.sphere (0 : Ep n) 1,
                h1fun (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
          + (∫ r in Set.Ioi (0 : ℝ), deriv cutPsi r * r ^ (n - 1 + (k - 1)))
            * (∫ θ : Metric.sphere (0 : Ep n) 1,
                h4fun (Wf G Yf) (θ : Ep n) ∂volume.toSphere) := by
            rw [← hIBP]
      _ = (∫ x : Ep n, cutPhi ‖x‖ * h1fun (Wf G Yf) x)
          + (∫ x : Ep n, deriv cutPsi ‖x‖ * h4fun (Wf G Yf) x) := by
            rw [← hArad, ← hBrad]
      _ = 0 := hAB
  have hCpos : 0 < ∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1)) :=
    cutPhi_rpow_integral_pos _
  have hmain : (∫ θ : Metric.sphere (0 : Ep n) 1, divE (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
      = ((n - 1 + (k - 1) : ℕ) : ℝ) * (k : ℝ) *
        (∫ θ : Metric.sphere (0 : Ep n) 1, G (θ : Ep n) * Yf (θ : Ep n) ∂volume.toSphere) := by
    have hfac : (∫ r in Set.Ioi (0 : ℝ), cutPhi r * r ^ (n - 1 + (k - 1))) *
        ((∫ θ : Metric.sphere (0 : Ep n) 1, divE (Wf G Yf) (θ : Ep n) ∂volume.toSphere)
          - ((n - 1 + (k - 1) : ℕ) : ℝ) * (k : ℝ)
            * (∫ θ : Metric.sphere (0 : Ep n) 1,
                G (θ : Ep n) * Yf (θ : Ep n) ∂volume.toSphere)) = 0 := by
      linear_combination hABval
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left (ne_of_gt hCpos))
  exact hmain

end SphereLapPairing

open SphereLapPairing

theorem sphere_laplacian_pairing
    {n : ℕ} [Nonempty (Fin n)]
    (G : EuclideanSpace ℝ (Fin n) → ℝ)
    (hGsmooth : ContDiffOn ℝ ⊤ G {x : EuclideanSpace ℝ (Fin n) | x ≠ 0})
    (hG0 : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)), 0 < t → G (t • x) = G x)
    (Y : MvPolynomial (Fin n) ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hYhom : Y ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hYhar : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Y)) = 0) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∑ i : Fin n, fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ G y (EuclideanSpace.single i 1)) (θ : EuclideanSpace ℝ (Fin n))
          (EuclideanSpace.single i 1)) *
        MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y
      ∂MeasureTheory.volume.toSphere)
    = -((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2)) *
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        G (θ : EuclideanSpace ℝ (Fin n)) *
        MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y
      ∂MeasureTheory.volume.toSphere) := by
  classical
  set Yf : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => MvPolynomial.eval (fun i => x i) Y with hYf
  have hYf_smooth : ContDiff ℝ ⊤ Yf := by
    rw [hYf]
    exact Commons.Algebra.MvPolynomial.contDiff_eval Y
  have hYf_hom : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)), 0 < t → Yf (t • x) = t ^ k * Yf x := by
    intro t x ht
    rw [hYf]
    exact Commons.Algebra.MvPolynomial.homogeneous_eval_smul Y hYhom t x
  have hYf_lap : ∀ x : EuclideanSpace ℝ (Fin n), lapG Yf x = 0 := by
    intro x
    rw [hYf]
    exact lapG_eval_eq_zero Y hYhar x
  have hcore := sphere_divE_Wf hk hGsmooth (fun t ht x => hG0 t x ht) hYf_smooth
    (fun t ht x => hYf_hom t x ht)
  have hn1 : 1 ≤ n := by
    have h : 0 < n := by
      have h2 := Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin n))
      simpa using h2
    omega
  have hMcast : (((n - 1 + (k - 1) : ℕ)) : ℝ) * (k : ℝ)
      = (k : ℝ) * ((k : ℝ) + (n : ℝ) - 2) := by
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; norm_num
    have h2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; norm_num
    rw [Nat.cast_add, h1, h2]
    ring
  -- identification of the two integrands
  have hLI : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∑ i : Fin n, fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ G y (EuclideanSpace.single i 1)) (θ : EuclideanSpace ℝ (Fin n))
          (EuclideanSpace.single i 1)) *
        MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y
      ∂MeasureTheory.volume.toSphere)
      = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          lapG G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
        ∂MeasureTheory.volume.toSphere) := by
    apply integral_congr_ae
    filter_upwards with θ
    rw [hYf]
    rfl
  have hLI2 : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
      ∂MeasureTheory.volume.toSphere)
      = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          G (θ : EuclideanSpace ℝ (Fin n)) *
          MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y
        ∂MeasureTheory.volume.toSphere) := by
    apply integral_congr_ae
    filter_upwards with θ
    rw [hYf]
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      lapG G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
        = - divE (Wf G Yf) (θ : EuclideanSpace ℝ (Fin n)) := by
    intro θ
    have hθ : (θ : EuclideanSpace ℝ (Fin n)) ≠ 0 := ne_zero_of_mem_sphere
    have h := divE_Wf_eq_neg hGsmooth hYf_smooth hYf_lap hθ
    rw [h]
    ring
  have hstep : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        lapG G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
      ∂MeasureTheory.volume.toSphere)
      = - (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            divE (Wf G Yf) (θ : EuclideanSpace ℝ (Fin n)) ∂MeasureTheory.volume.toSphere) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with θ
    exact hpt θ
  calc (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∑ i : Fin n, fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ G y (EuclideanSpace.single i 1)) (θ : EuclideanSpace ℝ (Fin n))
          (EuclideanSpace.single i 1)) *
        MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y
      ∂MeasureTheory.volume.toSphere)
      = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          lapG G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
        ∂MeasureTheory.volume.toSphere) := hLI
    _ = - (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            divE (Wf G Yf) (θ : EuclideanSpace ℝ (Fin n))
              ∂MeasureTheory.volume.toSphere) := hstep
    _ = - (((((n - 1 + (k - 1) : ℕ)) : ℝ) * (k : ℝ)) *
            (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
                ∂MeasureTheory.volume.toSphere)) := by rw [hcore]
    _ = -((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2)) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            G (θ : EuclideanSpace ℝ (Fin n)) * Yf (θ : EuclideanSpace ℝ (Fin n))
              ∂MeasureTheory.volume.toSphere) := by
          rw [hMcast]
          ring
    _ = -((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2)) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            G (θ : EuclideanSpace ℝ (Fin n)) *
            MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y
              ∂MeasureTheory.volume.toSphere) := by rw [hLI2]


end Commons.Analysis.MeasureTheory
