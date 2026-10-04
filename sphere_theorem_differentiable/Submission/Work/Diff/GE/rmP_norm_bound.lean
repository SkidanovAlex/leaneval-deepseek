import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.dRmPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bound `|Rm(u,b,c,d)| ≤ |Rm| |u| |b| |c| |d|`

The frozen pointwise curvature form `Submission.Diff.rmP g x u b c d = ⟪R(u,b)d, c⟫` is
`C^∞(M)`-multilinear in its four arguments; expanding it in the `g`-orthonormal frame
`onFrame g x` and applying Cauchy–Schwarz to the resulting four-fold coefficient sum gives the
pointwise bound `|rmP g x u b c d| ≤ |Rm| |u| |b| |c| |d|`, the `(0,4)`-tensor analogue of
`Work.Diff.GE.covRm_norm_bound`.

The proof has three inputs:

* `rmP_sum_fst/snd/thd/fth` (multilinearity of `rmP` over finite sums, in
  `Submission.Work.Diff.GE.dRmPhi`) and Parseval in the orthonormal frame
  (`Work.Diff.GE.sum_inner_smul_eq_self`) give the expansion
  `rmP (∑ αᵢeᵢ) (∑ βⱼeⱼ) (∑ γₖeₖ) (∑ δₗeₗ) = ∑ αᵢβⱼγₖδₗ Rᵢⱼₖₗ`;
* `sum4_coeff_sq_le`: Cauchy–Schwarz for the four-fold contraction with a rank-one coefficient
  tensor, `(∑ Cᵢⱼₖₗ Aᵢⱼₖₗ)² ≤ (∑ Aᵢⱼₖₗ²)(∑ Cᵢⱼₖₗ²)` with `∑ Cᵢⱼₖₗ² = (∑αᵢ²)(∑βⱼ²)(∑γₖ²)(∑δₗ²)`;
* Parseval, `∑ i, ⟪eᵢ,u⟫² = ⟪u,u⟫`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Parseval in a `g`-orthonormal frame -/

/-- **Parseval in a `g`-orthonormal frame.**  `∑ i, ⟪eᵢ,u⟫ * ⟪eᵢ,u⟫ = ⟪u,u⟫`. -/
theorem isONFrame_parseval_sq (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (u : TangentSpace I x) :
    (∑ i, g.inner x (e i) u * g.inner x (e i) u) = g.inner x u u := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact he i j
  have hsum : ∀ c : TangentSpace I x, (∑ i, g.inner x (e i) c • e i) = c :=
    fun c => sum_inner_smul_eq_self g x hn e he c
  have h := Orthonormal.inner_sum hon (fun i => g.inner x (e i) u) (fun i => g.inner x (e i) u)
    Finset.univ
  calc (∑ i, g.inner x (e i) u * g.inner x (e i) u)
      = ∑ i, (starRingEnd ℝ) (g.inner x (e i) u) * g.inner x (e i) u :=
        Finset.sum_congr rfl (fun i _ => by simp)
    _ = inner ℝ (∑ i, g.inner x (e i) u • e i) (∑ i, g.inner x (e i) u • e i) := h.symm
    _ = inner ℝ u u := by rw [hsum u]
    _ = g.inner x u u := rfl

/-- Parseval for the chosen frame `onFrame g x`, in the squared form used below. -/
theorem onFrame_parseval_sq (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (u : TangentSpace I x) :
    (∑ i, (g.inner x (onFrame g x i) u) ^ 2) = g.inner x u u := by
  rw [← isONFrame_parseval_sq g x hn (onFrame g x) (isONFrame_onFrame g x) u]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Expansion of `rmP` in a frame** (with the scalar coefficients extracted). -/
theorem rmP_sum_four_extracted (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A B C D : Fin (Module.finrank ℝ E) → ℝ) :
    rmP g x (∑ i, A i • e i) (∑ j, B j • e j) (∑ k, C k • e k) (∑ l, D l • e l)
      = ∑ i, A i * (∑ j, B j * (∑ k, C k * (∑ l, D l * rmP g x (e i) (e j) (e k) (e l)))) := by
  rw [rmP_sum_fst hLC g x Finset.univ A e (∑ j, B j • e j) (∑ k, C k • e k)
    (∑ l, D l • e l)]
  simp only [show ∀ i : Fin (Module.finrank ℝ E),
      rmP g x (e i) (∑ j, B j • e j) (∑ k, C k • e k) (∑ l, D l • e l)
        = ∑ j, B j * rmP g x (e i) (e j) (∑ k, C k • e k) (∑ l, D l • e l) from
    fun i => rmP_sum_snd hLC g x Finset.univ B e (e i) (∑ k, C k • e k) (∑ l, D l • e l)]
  simp only [show ∀ i j : Fin (Module.finrank ℝ E),
      rmP g x (e i) (e j) (∑ k, C k • e k) (∑ l, D l • e l)
        = ∑ k, C k * rmP g x (e i) (e j) (e k) (∑ l, D l • e l) from
    fun i j => rmP_sum_thd hLC g x Finset.univ C e (e i) (e j) (∑ l, D l • e l)]
  simp only [show ∀ i j k : Fin (Module.finrank ℝ E),
      rmP g x (e i) (e j) (e k) (∑ l, D l • e l)
        = ∑ l, D l * rmP g x (e i) (e j) (e k) (e l) from
    fun i j k => rmP_sum_fth hLC g x Finset.univ D e (e i) (e j) (e k)]

/-- **Expansion of `rmP` in a frame.** -/
theorem rmP_sum_four (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A B C D : Fin (Module.finrank ℝ E) → ℝ) :
    rmP g x (∑ i, A i • e i) (∑ j, B j • e j) (∑ k, C k • e k) (∑ l, D l • e l)
      = ∑ i, ∑ j, ∑ k, ∑ l,
          (A i * B j * C k * D l) * rmP g x (e i) (e j) (e k) (e l) := by
  rw [rmP_sum_four_extracted hLC g x e A B C D]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Expansion of `rmP` evaluated on the vectors themselves, in the chosen frame. -/
theorem rmP_expansion (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hn : 0 < Module.finrank ℝ E) (u b c d : TangentSpace I x) :
    rmP g x u b c d
      = ∑ i, ∑ j, ∑ k, ∑ l,
          ((g.inner x (onFrame g x i) u) * (g.inner x (onFrame g x j) b)
            * (g.inner x (onFrame g x k) c) * (g.inner x (onFrame g x l) d))
          * rmP g x (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l) := by
  have he : IsONFrame g x (onFrame g x) := isONFrame_onFrame g x
  have h1 := rmP_sum_four hLC g x (onFrame g x)
    (fun i => g.inner x (onFrame g x i) u) (fun j => g.inner x (onFrame g x j) b)
    (fun k => g.inner x (onFrame g x k) c) (fun l => g.inner x (onFrame g x l) d)
  rw [sum_inner_smul_eq_self g x hn (onFrame g x) he u,
    sum_inner_smul_eq_self g x hn (onFrame g x) he b,
    sum_inner_smul_eq_self g x hn (onFrame g x) he c,
    sum_inner_smul_eq_self g x hn (onFrame g x) he d] at h1
  exact h1

/-! ## The four-fold Cauchy–Schwarz bound -/

/-- Flattening of a four-fold finite sum over `Fin n` into a single sum over the product type. -/
theorem sum4_flat {N : Type*} [AddCommMonoid N] {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → N) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l)
      = ∑ p : ((Fin n × Fin n) × Fin n) × Fin n, F p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => ∑ k, ∑ l, F p.1 p.2 k l),
    ← Fintype.sum_prod_type
      (f := fun p : (Fin n × Fin n) × Fin n => ∑ l, F p.1.1 p.1.2 p.2 l),
    ← Fintype.sum_prod_type
      (f := fun p : ((Fin n × Fin n) × Fin n) × Fin n => F p.1.1.1 p.1.1.2 p.1.2 p.2)]

/-- A product of two sums as a sum over the product index type. -/
theorem sum_prod_mul {α β : Type*} [Fintype α] [Fintype β] (F : α → ℝ) (G : β → ℝ) :
    (∑ p : α × β, F p.1 * G p.2) = (∑ a, F a) * (∑ b, G b) := by
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_mul_sum Finset.univ Finset.univ F G).symm

/-- A product of four sums. -/
theorem sum4_mul {n : ℕ} (f g h t : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i * g j * h k * t l)
      = (∑ i, f i) * ((∑ j, g j) * ((∑ k, h k) * (∑ l, t l))) := by
  rw [← Fintype.sum_prod_type
      (f := fun p : Fin n × Fin n => ∑ k, ∑ l, f p.1 * g p.2 * h k * t l),
    ← Fintype.sum_prod_type
      (f := fun p : (Fin n × Fin n) × Fin n => ∑ l, f p.1.1 * g p.1.2 * h p.2 * t l),
    ← Fintype.sum_prod_type
      (f := fun p : ((Fin n × Fin n) × Fin n) × Fin n =>
        f p.1.1.1 * g p.1.1.2 * h p.1.2 * t p.2)]
  rw [sum_prod_mul (F := fun q : (Fin n × Fin n) × Fin n => f q.1.1 * g q.1.2 * h q.2) (G := t)]
  rw [sum_prod_mul (F := fun q : Fin n × Fin n => f q.1 * g q.2) (G := h)]
  rw [sum_prod_mul (F := f) (G := g)]
  ring

/-- **Product identity for a rank-one coefficient tensor.** -/
theorem sum4_prod_sq {n : ℕ} (a b c d : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * c k * d l) ^ 2)
      = (∑ i, a i ^ 2) * ((∑ j, b j ^ 2) * ((∑ k, c k ^ 2) * (∑ l, d l ^ 2))) := by
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * c k * d l) ^ 2)
      = ∑ i, ∑ j, ∑ k, ∑ l, (a i ^ 2) * (b j ^ 2) * (c k ^ 2) * (d l ^ 2) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring]
  exact sum4_mul (fun i => a i ^ 2) (fun j => b j ^ 2) (fun k => c k ^ 2) (fun l => d l ^ 2)

/-- **Cauchy–Schwarz for the four-fold contraction with a rank-one coefficient tensor**: the
contraction of a curvature array `A` with the coefficients `aᵢbⱼcₖdₗ` is bounded by the product of
the `ℓ²` norms. -/
theorem sum4_coeff_sq_le {n : ℕ} (A : Curv4 n) (a b c d : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * c k * d l) * A i j k l) ^ 2
      ≤ (∑ i, ∑ j, ∑ k, ∑ l, A i j k l ^ 2) *
        ((∑ i, a i ^ 2) * ((∑ j, b j ^ 2) * ((∑ k, c k ^ 2) * (∑ l, d l ^ 2)))) := by
  rw [sum4_flat (fun i j k l => (a i * b j * c k * d l) * A i j k l),
    sum4_flat (fun i j k l => A i j k l ^ 2)]
  have hC : (∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
        (a p.1.1.1 * b p.1.1.2 * c p.1.2 * d p.2) ^ 2)
      = (∑ i, a i ^ 2) * ((∑ j, b j ^ 2) * ((∑ k, c k ^ 2) * (∑ l, d l ^ 2))) := by
    rw [← sum4_flat (fun i j k l => (a i * b j * c k * d l) ^ 2)]
    exact sum4_prod_sq a b c d
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : ((Fin n × Fin n) × Fin n) × Fin n =>
      a p.1.1.1 * b p.1.1.2 * c p.1.2 * d p.2)
    (fun p : ((Fin n × Fin n) × Fin n) × Fin n => A p.1.1.1 p.1.1.2 p.1.2 p.2)) ?_
  rw [mul_comm (∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
        (a p.1.1.1 * b p.1.1.2 * c p.1.2 * d p.2) ^ 2)
      (∑ p : ((Fin n × Fin n) × Fin n) × Fin n, A p.1.1.1 p.1.1.2 p.1.2 p.2 ^ 2)]
  rw [hC, ← sum4_flat (fun i j k l => A i j k l ^ 2)]

theorem rmP_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (g : Submission.Diff.SMet I M) (x : M) (u b c d : TangentSpace I x),
      |Submission.Diff.rmP g x u b c d|
        ≤ Real.sqrt (Submission.Diff.rmNormSq g x)
          * (Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
  intro g x u b c d
  by_cases hn : 0 < Module.finrank ℝ E
  · have hkey := rmP_expansion hLC g x hn u b c d
    have hSU := onFrame_parseval_sq g x hn u
    have hSB := onFrame_parseval_sq g x hn b
    have hSC := onFrame_parseval_sq g x hn c
    have hSD := onFrame_parseval_sq g x hn d
    have hR : 0 ≤ rmNormSq g x := by
      show 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, rmC g x i j k l ^ 2
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
    have hU : 0 ≤ g.inner x u u := by
      rw [← hSU]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hB : 0 ≤ g.inner x b b := by
      rw [← hSB]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hC : 0 ≤ g.inner x c c := by
      rw [← hSC]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hD : 0 ≤ g.inner x d d := by
      rw [← hSD]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hcs := sum4_coeff_sq_le (A := rmC g x)
      (a := fun i => g.inner x (onFrame g x i) u)
      (b := fun j => g.inner x (onFrame g x j) b)
      (c := fun k => g.inner x (onFrame g x k) c)
      (d := fun l => g.inner x (onFrame g x l) d)
    have hsq : (rmP g x u b c d) ^ 2
        ≤ rmNormSq g x * (g.inner x u u * (g.inner x b b * (g.inner x c c * g.inner x d d))) := by
      rw [hkey]
      refine le_trans hcs ?_
      rw [hSU, hSB, hSC, hSD]
      exact le_rfl
    have hsqrt : Real.sqrt (rmNormSq g x *
          (g.inner x u u * (g.inner x b b * (g.inner x c c * g.inner x d d))))
        = Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x u u) * (Real.sqrt (g.inner x b b) *
            (Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))) := by
      rw [Real.sqrt_mul hR, Real.sqrt_mul hU, Real.sqrt_mul hB, Real.sqrt_mul hC]
    calc |rmP g x u b c d| = Real.sqrt ((rmP g x u b c d) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (rmNormSq g x *
            (g.inner x u u * (g.inner x b b * (g.inner x c c * g.inner x d d)))) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x u u) * (Real.sqrt (g.inner x b b) *
            (Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))) := hsqrt
      _ = Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x b b)
            * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by ring
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hzero : ∀ v : E, v = 0 := finrank_zero_iff_forall_zero.mp h0
    have hu : u = 0 := hzero u
    have hb : b = 0 := hzero b
    have hc : c = 0 := hzero c
    have hd : d = 0 := hzero d
    rw [hu, hb, hc, hd]
    simp [Submission.Diff.rmP]

end Work.Diff.GE
