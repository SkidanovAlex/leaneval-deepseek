import Mathlib
import Submission.Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis
import Submission.Work.Diff.GE.evol_scal_kit
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.frobSq_rot
import Submission.Work.Diff.GE.scal_rot_defs
import Submission.Work.Diff.GE.rmNormSq_eq_N4_of_basis
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.GE.laplAt_eq_sum_invGram
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.GE.ricNormSq_eq_ricSq_rmFrame
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.continuous_flow_quantities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

namespace ScalK

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The coordinate frame spans the tangent space -/

/-- At every point of the chart at `x₀`, the coordinate frame `cFrame x₀ ·` is a basis. -/
theorem cFrame_span (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℝ E) ↦ cFrame (I := I) x₀ i p))
      = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w => ?_
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  set c := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w with hc
  have hspec : Submission.Geodesic.frameSection (I := I) x₀ c p
      = ∑ i : Fin (Module.finrank ℝ E), ((Module.finBasis ℝ E).coord i) c
          • cFrame (I := I) x₀ i p := by
    have h1 := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I)
      (b := Module.finBasis ℝ E) x₀ (Submission.Geodesic.frameSection (I := I) x₀ c) hp
    have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        (Submission.Geodesic.frameSection (I := I) x₀ c p) = c := by
      show (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p c) = c
      exact Trivialization.continuousLinearMapAt_symmL _ hb c
    have h3 := h1
    simp only [] at h3
    rw [h3, h2]
    rfl
  have hlhs : Submission.Geodesic.frameSection (I := I) x₀ c p = w :=
    (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hb w
  rw [← hlhs, hspec]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self i)

/-! ## The scalar curvature functional under a non-orthogonal change of frame -/

variable {n : ℕ}

/-- `Dc N R` as the trace of the flattened tensor against `N ⊗ N`. -/
lemma Dc_eq_trace (N : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    Dc N R = Matrix.trace (fsr_toM R * (Matrix.kronecker N N)ᵀ) := by
  rw [Dc, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, fsr_toM, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cyclic trace identity, right-associated. -/
lemma trace_cycle4 {m : Type*} [Fintype m] (A B C D : Matrix m m ℝ) :
    (A * (B * (C * D))).trace = (B * (C * (D * A))).trace := by
  rw [Matrix.trace_mul_comm A (B * (C * D))]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc]

/-- `Dc` transforms by conjugation of the matrix under a change of frame. -/
lemma Dc_rot (N A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    Dc N (rot A R) = Dc (Aᵀ * N * A) R := by
  have hk : Matrix.kronecker (Aᵀ * N * A) (Aᵀ * N * A)
      = Matrix.kronecker Aᵀ Aᵀ * Matrix.kronecker N N * Matrix.kronecker A A := by
    rw [← fsr_kron_mul (Aᵀ * N) A, ← fsr_kron_mul Aᵀ N]
  rw [Dc_eq_trace, Dc_eq_trace, fsr_toM_rot, hk, Matrix.transpose_mul, Matrix.transpose_mul,
    fsr_kron_tr Aᵀ, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  exact trace_cycle4 (Matrix.kronecker A A) (fsr_toM R) ((Matrix.kronecker A A)ᵀ)
    ((Matrix.kronecker N N)ᵀ)

/-- `Dc 1 R` is the scalar curvature functional `scalAlg R`. -/
lemma Dc_one (R : Curv4 n) : Dc (1 : Matrix (Fin n) (Fin n) ℝ) R = scalAlg R := by
  rw [Dc_eq_trace, fsr_kron_one, Matrix.transpose_one, Matrix.mul_one, Matrix.trace, scalAlg]
  simp only [Matrix.diag, fsr_toM, Fintype.sum_prod_type]

/-- **The scalar functional under a non-orthogonal frame change.**  If `A` is invertible, then
contracting `rot A R` with the inverse of the Gram matrix `A Aᵀ` gives `scalAlg R`. -/
theorem scalAlg_rot_eq_N2 (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (R : Curv4 n) :
    N2 (A * Aᵀ) (rot A R) = scalAlg R := by
  rw [N2_eq_Dc, Dc_rot]
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have h1 : Aᵀ * (A * Aᵀ)⁻¹ * A = 1 := by
    rw [Matrix.mul_inv_rev]
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul A hA, Matrix.mul_one, Matrix.mul_nonsing_inv Aᵀ hAt]
  rw [h1, Dc_one]

/-! ## The scalar curvature in a general basis -/

/-- The metric pairing of two linear combinations in an orthonormal family. -/
private lemma inner_sum_smul_sum_smul (g : Submission.Diff.SMet I M) (x : M) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → TangentSpace I x)
    (hv : ∀ k l, g.inner x (v k) (v l) = if k = l then 1 else 0) (a c : ι → ℝ) :
    g.inner x (∑ k, a k • v k) (∑ l, c l • v l) = ∑ k, a k * c k := by
  have hL : g.inner x (∑ k, a k • v k) = ∑ k, a k • g.inner x (v k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => map_smul (g.inner x) (a k) (v k))
  have hR : ∀ k, g.inner x (v k) (∑ l, c l • v l) = c k := by
    intro k
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun l _ => by rw [map_smul, hv k l, smul_eq_mul])]
    rw [Finset.sum_congr rfl (fun l _ => by rw [mul_ite, mul_one, mul_zero]),
      Fintype.sum_ite_eq k (fun l => c l)]
  rw [hL, sum_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [smul_apply, hR k, smul_eq_mul])

/-- **The scalar curvature in a general basis.**

For a smooth metric `g`, a point `x` and a family `e₁,…,eₙ` spanning `TₓM` with Gram matrix
`Γᵢⱼ = g(eᵢ,eⱼ)`, the scalar curvature is the contraction of the curvature components in `e`
with two inverse Gram matrices. -/
theorem scalAt_eq_N2_of_basis (hLC : Submission.Diff.LCSmooth I M)
    {g : Submission.Diff.SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    Submission.Diff.scalAt g x = N2 Γ (Submission.Diff.rmFrame g x e) := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) :=
      inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
    have hon : Orthonormal ℝ (Submission.Diff.onFrame g x) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show Inner.inner ℝ (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
            = g.inner x (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j) from rfl]
      exact isONFrame_onFrame g x i j
    have hcard : Fintype.card (Fin (Module.finrank ℝ E))
        = Module.finrank ℝ (TangentSpace I x) := by rw [Fintype.card_fin]; rfl
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon hcard
    have hbcoe : ⇑b = Submission.Diff.onFrame g x :=
      coe_basisOfOrthonormalOfCardEqFinrank hon hcard
    have honb : Orthonormal ℝ (⇑b) := by rw [hbcoe]; exact hon
    have hli : LinearIndependent ℝ e := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hb, finrank_top]
      exact hcard
    have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) := by rw [hb]
    let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      Module.Basis.mk hli hsp
    have hc : ⇑c = e := Module.Basis.coe_mk hli hsp
    let B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      (b.toMatrix ⇑c)ᵀ
    have hB_apply : ∀ i j, B i j = (b.repr (c i)) j := fun i j => by
      simp only [B, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    have hAe_b : ∀ i, e i = ∑ j, B i j • b j := by
      intro i
      have h1 : (∑ j, B i j • b j) = c i := by
        rw [show (∑ j, B i j • b j) = ∑ j, (b.repr (c i)) j • b j from
              Finset.sum_congr rfl (fun j _ => by rw [hB_apply i j])]
        exact b.sum_repr (c i)
      rw [h1, congrFun hc i]
    have hBunit : IsUnit B.det := by
      have h1 : c.toMatrix ⇑b * (b.toMatrix ⇑c) = 1 := by
        rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
      have hne : (b.toMatrix ⇑c).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse h1
      rw [show B.det = (b.toMatrix ⇑c).det from by simp only [B, Matrix.det_transpose]]
      exact isUnit_iff_ne_zero.mpr hne
    have hBBt : Γ = B * Bᵀ := by
      ext i j
      rw [hΓ i j, Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])]
      rw [hAe_b i, hAe_b j]
      exact inner_sum_smul_sum_smul g x (⇑b)
        (fun k l => by
          rw [show g.inner x (b k) (b l) = Inner.inner ℝ (b k) (b l) from rfl]
          exact (orthonormal_iff_ite.mp honb) k l)
        (fun k => B i k) (fun l => B j l)
    have hAe : ∀ i, e i = ∑ j, B i j • Submission.Diff.onFrame g x j := by
      intro i
      rw [hAe_b i]
      exact Finset.sum_congr rfl (fun j _ => by rw [congrFun hbcoe j])
    rw [show Submission.Diff.scalAt g x
        = scalAlg (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)) from rfl]
    rw [← scalAlg_rot_eq_N2 B hBunit (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)),
        ← rmFrame_eq_rot hLC g x (Submission.Diff.onFrame g x) e B hAe, ← hBBt]
  · -- degenerate case: the index type is empty
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp only [Submission.Diff.scalAt, Submission.Diff.rmC, scalAlg, N2, Finset.univ_eq_empty,
      Finset.sum_empty]

/-! ## Joint smoothness of `scalAt` along a jointly smooth family of metrics -/

/-- Joint smoothness of the general-basis contraction `N2`. -/
theorem N2_jointSmooth {n : ℕ} {Γ : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
    {R : ℝ × M → Curv4 n} {t₀ : ℝ} {x : M}
    (hΓ : ∀ i j, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ (Γ p)⁻¹ i j) t₀ x)
    (hR : ∀ i j k l, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ R p i j k l) t₀ x) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ N2 (Γ p) (R p)) t₀ x := by
  show ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ)) ∞ (fun p : ℝ × M ↦ N2 (Γ p) (R p)) (t₀, x)
  simp only [N2]
  refine ContMDiffAt.sum (fun i _ ↦ ?_)
  refine ContMDiffAt.sum (fun a _ ↦ ?_)
  refine ContMDiffAt.sum (fun j _ ↦ ?_)
  refine ContMDiffAt.sum (fun b _ ↦ ?_)
  exact ((hΓ i a).mul (hΓ j b)).mul (hR i j a b)

/-- **Joint smoothness of the scalar curvature along a jointly smooth family of metrics.** -/
theorem scalAt_jointSmoothAt (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.Diff.scalAt (G p.1) p.2) t₀ x₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ N2 (GramM (I := I) G x₀ p.1 p.2) (rmC4 (I := I) G x₀ p.1 p.2)) t₀ x₀ :=
    N2_jointSmooth (I := I) (M := M)
      (fun i j ↦ by
        simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ i j)
      (fun i j k l ↦ rmC4_jointSmooth (I := I) hLC hJ hG ht₀ x₀ i j k l)
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact scalAt_eq_N2_of_basis (I := I) hLC p.2
    (fun i ↦ cFrame (I := I) x₀ i p.2) (GramM (I := I) G x₀ p.1 p.2)
    (fun i j ↦ rfl) (cFrame_span (I := I) x₀ hp.2)

/-! ## The squared Ricci norm under a non-orthogonal change of frame -/

/-- The "Ricci array with respect to the Gram matrix `MᵀM`" of a curvature array. -/
noncomputable def ricG (M : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) : Fin n → Fin n → ℝ :=
  fun b d => ∑ a, ∑ c, (Mᵀ * M) a c * R a b c d

/-- The change of frame on a `(0,2)`-tensor array. -/
noncomputable def rot2 (M : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := fun i j => ∑ b, ∑ d, M i b * M j d * Q b d

/-- The Ricci array of a curvature array (in an orthonormal frame). -/
noncomputable def ricArr (R : Curv4 n) : Fin n → Fin n → ℝ := fun i j => ∑ k, R k i k j

lemma mul_sum4 (f g : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, f p q) * (∑ r, ∑ s, g r s) = ∑ r, ∑ s, ∑ p, ∑ q, f p q * g r s := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]

/-- A rank-one `4`-tensor is rotated to the rank-one tensor of the rotated factors. -/
lemma rot_rank1 (M : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Fin n → ℝ) :
    rot M (fun i j a b => Q i j * Q a b)
      = fun i j a b => (∑ p, ∑ q, M i p * M j q * Q p q)
          * (∑ p, ∑ q, M a p * M b q * Q p q) := by
  funext i j a b
  rw [rot, mul_sum4, fsr_bswap22]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ =>
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))))
  ring

/-- `ricSq` as a double contraction of the Ricci array. -/
lemma ricSq_eq_Dc (S : Curv4 n) :
    ricSq S = Dc 1 (fun i j a b => ricArr S i j * ricArr S a b) := by
  rw [Dc_one, scalAlg, ricSq]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [ricArr]
  ring

/-- The Ricci array of the rotated curvature is the rotation of the Gram-contracted Ricci. -/
lemma ric_of_rot (M : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j : Fin n) :
    (∑ k, rot M R k i k j) = rot2 M (ricG M R) i j := by
  simp only [rot2, ricG]
  calc ∑ k, rot M R k i k j
      = ∑ k, ∑ a, ∑ b, ∑ c, ∑ d,
          (M k a * M k c) * (M i b * M j d * R a b c d) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [rot]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          ring
    _ = ∑ k, ∑ a, ∑ c, ∑ b, ∑ d,
          (M k a * M k c) * (M i b * M j d * R a b c d) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ c, (M k a * M k c) *
          (∑ b, ∑ d, M i b * M j d * R a b c d) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ a, ∑ c, (∑ k, M k a * M k c) *
          (∑ b, ∑ d, M i b * M j d * R a b c d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ a, ∑ c, (Mᵀ * M) a c *
          (∑ b, ∑ d, M i b * M j d * R a b c d) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
          rw [show (∑ k, M k a * M k c) = (Mᵀ * M) a c from rfl]
    _ = ∑ b, ∑ d, M i b * M j d * (∑ a, ∑ c, (Mᵀ * M) a c * R a b c d) := by
          have hL : (∑ a, ∑ c, (Mᵀ*M) a c * (∑ b, ∑ d, M i b * M j d * R a b c d))
              = ∑ a, ∑ c, ∑ b, ∑ d, (Mᵀ*M) a c * (M i b * M j d * R a b c d) := by
            refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [Finset.mul_sum]
          have hR : (∑ b, ∑ d, M i b * M j d * (∑ a, ∑ c, (Mᵀ*M) a c * R a b c d))
              = ∑ b, ∑ d, ∑ a, ∑ c, (M i b * M j d) * ((Mᵀ*M) a c * R a b c d) := by
            refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun d _ => ?_))
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
          rw [hL, hR, fsr_bswap22]
          refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
            Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))))
          ring

/-- **The squared Ricci norm under a general change of frame.** -/
theorem ricSq_rot_eq_Dc (M : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    ricSq (rot M R) = Dc (Mᵀ * M) (fun i j a b => ricG M R i j * ricG M R a b) := by
  have hQ : ∀ i j, ricArr (rot M R) i j = rot2 M (ricG M R) i j := by
    intro i j
    rw [ricArr, ric_of_rot]
  have hfun : (fun i j a b => ricArr (rot M R) i j * ricArr (rot M R) a b)
      = rot M (fun i j a b => ricG M R i j * ricG M R a b) := by
    funext i j a b
    rw [hQ i j, hQ a b]
    simp only [rot2]
    exact congrFun (congrFun (congrFun (congrFun (rot_rank1 M (ricG M R)).symm i) j) a) b
  rw [ricSq_eq_Dc, hfun, Dc_rot, Matrix.mul_one]

/-! ## Existence of the change-of-basis matrix -/

/-- **The change-of-basis matrix from a basis to the chosen orthonormal frame.**  For a basis `e`
of `TₓM` (with Gram matrix `Γ` for `g`) there is a matrix `B` such that
`eᵢ = ∑ j B i j • b j` for `b = onFrame g x`, `B` is invertible, and `Γ = B * Bᵀ`. -/
theorem exists_change_of_basis (hLC : Submission.Diff.LCSmooth I M)
    {g : Submission.Diff.SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    ∃ B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ,
      IsUnit B.det ∧ Γ = B * Bᵀ ∧
        (∀ i, e i = ∑ j, B i j • Submission.Diff.onFrame g x j) := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) :=
      inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
    have hon : Orthonormal ℝ (Submission.Diff.onFrame g x) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show Inner.inner ℝ (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
            = g.inner x (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j) from rfl]
      exact isONFrame_onFrame g x i j
    have hcard : Fintype.card (Fin (Module.finrank ℝ E))
        = Module.finrank ℝ (TangentSpace I x) := by rw [Fintype.card_fin]; rfl
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon hcard
    have hbcoe : ⇑b = Submission.Diff.onFrame g x :=
      coe_basisOfOrthonormalOfCardEqFinrank hon hcard
    have honb : Orthonormal ℝ (⇑b) := by rw [hbcoe]; exact hon
    have hli : LinearIndependent ℝ e := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hb, finrank_top]
      exact hcard
    have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) := by rw [hb]
    let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      Module.Basis.mk hli hsp
    have hc : ⇑c = e := Module.Basis.coe_mk hli hsp
    let B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      (b.toMatrix ⇑c)ᵀ
    have hB_apply : ∀ i j, B i j = (b.repr (c i)) j := fun i j => by
      simp only [B, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    have hAe_b : ∀ i, e i = ∑ j, B i j • b j := by
      intro i
      have h1 : (∑ j, B i j • b j) = c i := by
        rw [show (∑ j, B i j • b j) = ∑ j, (b.repr (c i)) j • b j from
              Finset.sum_congr rfl (fun j _ => by rw [hB_apply i j])]
        exact b.sum_repr (c i)
      rw [h1, congrFun hc i]
    have hBunit : IsUnit B.det := by
      have h1 : c.toMatrix ⇑b * (b.toMatrix ⇑c) = 1 := by
        rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
      have hne : (b.toMatrix ⇑c).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse h1
      rw [show B.det = (b.toMatrix ⇑c).det from by simp only [B, Matrix.det_transpose]]
      exact isUnit_iff_ne_zero.mpr hne
    have hBBt : Γ = B * Bᵀ := by
      ext i j
      rw [hΓ i j, Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])]
      rw [hAe_b i, hAe_b j]
      exact inner_sum_smul_sum_smul g x (⇑b)
        (fun k l => by
          rw [show g.inner x (b k) (b l) = Inner.inner ℝ (b k) (b l) from rfl]
          exact (orthonormal_iff_ite.mp honb) k l)
        (fun k => B i k) (fun l => B j l)
    exact ⟨B, hBunit, hBBt, fun i => by
      rw [hAe_b i]
      exact Finset.sum_congr rfl (fun j _ => by rw [congrFun hbcoe j])⟩
  · -- degenerate case: the index type is empty
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    refine ⟨1, ?_, ?_, ?_⟩
    · rw [Matrix.det_one]; exact isUnit_one
    · exact Subsingleton.elim _ _
    · intro i; exact isEmptyElim i

/-- The inverse change: if `eᵢ = ∑ j, B i j • b j` with `B` invertible then
`bᵢ = ∑ j, (B⁻¹) i j • e j`. -/
lemma inv_change {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B.det) {b e : Fin n → V}
    (h : ∀ i, e i = ∑ j, B i j • b j) :
    ∀ i, b i = ∑ j, (B⁻¹) i j • e j := by
  intro i
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  symm
  calc ∑ j, (B⁻¹) i j • e j
      = ∑ j, (B⁻¹) i j • (∑ k, B j k • b k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [h j]
    _ = ∑ j, ∑ k, (B⁻¹) i j • (B j k • b k) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.smul_sum]
    _ = ∑ k, ∑ j, (B⁻¹) i j • (B j k • b k) := Finset.sum_comm
    _ = ∑ k, ∑ j, ((B⁻¹) i j * B j k) • b k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [smul_smul, mul_comm]
    _ = ∑ k, (∑ j, (B⁻¹) i j * B j k) • b k := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [Finset.sum_smul]
    _ = ∑ k, (B⁻¹ * B) i k • b k := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [Matrix.mul_apply]
    _ = ∑ k, (1 : Matrix (Fin n) (Fin n) ℝ) i k • b k := by rw [hinv]
    _ = b i := by
          rw [Finset.sum_eq_single i]
          · rw [Matrix.one_apply, if_pos rfl, one_smul]
          · intro k _ hk
            rw [Matrix.one_apply, if_neg (fun hki => hk hki.symm), zero_smul]
          · intro h'; exact absurd (Finset.mem_univ i) h'

/-- **The squared Ricci norm in a general basis.** -/
theorem ricNormSq_eq_of_basis (hLC : Submission.Diff.LCSmooth I M)
    {g : Submission.Diff.SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    Submission.Diff.ricNormSq g x = Dc Γ⁻¹
      (fun i j a b => (∑ p, ∑ q, Γ⁻¹ p q * Submission.Diff.rmFrame g x e p i q j)
        * (∑ p, ∑ q, Γ⁻¹ p q * Submission.Diff.rmFrame g x e p a q b)) := by
  obtain ⟨B, hBunit, hBBt, hAe⟩ := exists_change_of_basis hLC x e Γ hΓ hb
  have hMinv : ∀ i, Submission.Diff.onFrame g x i = ∑ j, (B⁻¹) i j • e j :=
    inv_change B hBunit hAe
  have hrot : Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)
      = rot (B⁻¹) (Submission.Diff.rmFrame g x e) :=
    rmFrame_eq_rot hLC g x e (Submission.Diff.onFrame g x) (B⁻¹) hMinv
  have hGam : (B⁻¹)ᵀ * B⁻¹ = Γ⁻¹ := by
    rw [hBBt, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rw [show Submission.Diff.ricNormSq g x
        = ricSq (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)) from rfl,
    hrot, ricSq_rot_eq_Dc]
  simp only [ricG]
  rw [hGam]

/-! ## Joint smoothness of `ricNormSq` along a jointly smooth family of metrics -/

/-- Joint smoothness of the general-basis double contraction `Dc`. -/
theorem Dc_jointSmooth {n : ℕ} {N : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
    {R : ℝ × M → Curv4 n} {t₀ : ℝ} {x : M}
    (hN : ∀ i j, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ N p i j) t₀ x)
    (hR : ∀ i j a b, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ R p i j a b) t₀ x) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ Dc (N p) (R p)) t₀ x := by
  show ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ)) ∞ (fun p : ℝ × M ↦ Dc (N p) (R p)) (t₀, x)
  simp only [Dc]
  refine ContMDiffAt.sum (fun i _ ↦ ?_)
  refine ContMDiffAt.sum (fun a _ ↦ ?_)
  refine ContMDiffAt.sum (fun j _ ↦ ?_)
  refine ContMDiffAt.sum (fun b _ ↦ ?_)
  exact ((hN i a).mul (hN j b)).mul (hR i j a b)

/-- **Joint smoothness of the squared Ricci norm along a jointly smooth family of metrics.** -/
theorem ricNormSq_jointSmoothAt (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.Diff.ricNormSq (G p.1) p.2) t₀ x₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hQ : ∀ i j : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ ∑ a, ∑ c, GramInv (I := I) G x₀ p.1 p.2 a c
          * rmC4 (I := I) G x₀ p.1 p.2 a i c j) t₀ x₀ := by
    intro i j
    refine ContMDiffAt.sum (fun a _ ↦ ?_)
    refine ContMDiffAt.sum (fun c _ ↦ ?_)
    have h1 : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ GramInv (I := I) G x₀ p.1 p.2 a c) t₀ x₀ := by
      simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ a c
    exact h1.mul (rmC4_jointSmooth (I := I) hLC hJ hG ht₀ x₀ a i c j)
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Dc (GramInv (I := I) G x₀ p.1 p.2)
        (fun i j a b ↦ (∑ a', ∑ c', GramInv (I := I) G x₀ p.1 p.2 a' c'
              * rmC4 (I := I) G x₀ p.1 p.2 a' i c' j)
          * (∑ a', ∑ c', GramInv (I := I) G x₀ p.1 p.2 a' c'
              * rmC4 (I := I) G x₀ p.1 p.2 a' a c' b))) t₀ x₀ :=
    Dc_jointSmooth (I := I) (M := M)
      (fun i j ↦ by
        simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ i j)
      (fun i j a b ↦ (hQ i j).mul (hQ a b))
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact (ricNormSq_eq_of_basis (I := I) hLC p.2 (fun i ↦ cFrame (I := I) x₀ i p.2)
    (GramM (I := I) G x₀ p.1 p.2) (fun i j ↦ rfl) (cFrame_span (I := I) x₀ hp.2))

end ScalK

/-! ## Continuity of the scalar-curvature quantities at the initial time

The two conjuncts are obtained from the joint smoothness of `(t,y) ↦ scalAt (G t) y` and
`(t,y) ↦ ricNormSq (G t) y` (`ScalK.scalAt_jointSmoothAt`, `ScalK.ricNormSq_jointSmoothAt`) and
from the continuity of the Laplace operator along a jointly smooth family
(`Work.Diff.GE.cfq_laplAt_continuousAt`), together with the time reparametrisation `t = τ²`
(`Work.Diff.GE.cfq_jointSmooth_sqFlow`, `Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq`)
which turns the half-open interval `[0,T)` into an open one. -/

theorem flowContAtZeroScal_of_isRicciFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    Work.Diff.GE.FlowContAtZeroScal (I := I) (M := M) := by
  intro G T hflow x
  by_cases hT : T ≤ 0
  · -- degenerate case: `[0,T)` is empty and continuity within the empty set is automatic
    have hempty : Set.Ico 0 T = ∅ := Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)
    rw [hempty]
    exact ⟨by simp [ContinuousWithinAt, nhdsWithin_empty],
      by simp [ContinuousWithinAt, nhdsWithin_empty]⟩
  · have hTpos : 0 < T := not_le.mp hT
    obtain ⟨ρ, hρpos, hρT⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 < T :=
      ⟨Real.sqrt T / 2, by positivity,
        by nlinarith [Real.sq_sqrt hTpos.le, Real.sq_sqrt (le_of_lt hTpos),
          Real.sqrt_pos.mpr hTpos]⟩
    have hJ : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
    have hsq : Submission.Diff.JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρpos hρT hflow.1
    have h0J : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρpos⟩
    -- joint smoothness of the scalar curvature and of `|Ric|²` along the reparametrised family
    have hscal : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ Submission.Diff.scalAt (Work.Diff.GE.cfq_sqFlow G p.1) p.2) 0 x :=
      ScalK.scalAt_jointSmoothAt (I := I) (M := M) hLC hJ hsq h0J x
    have hric : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ Submission.Diff.ricNormSq (Work.Diff.GE.cfq_sqFlow G p.1) p.2) 0 x :=
      ScalK.ricNormSq_jointSmoothAt (I := I) (M := M) hLC hJ hsq h0J x
    -- the corresponding continuities in the reparametrised time
    have hcont1 : ContinuousAt
        (fun τ : ℝ ↦ Submission.Diff.scalAt (Work.Diff.GE.cfq_sqFlow G τ) x) 0 :=
      Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M) hscal
    have hcont2 : ContinuousAt
        (fun τ : ℝ ↦ Submission.Diff.laplAt (Work.Diff.GE.cfq_sqFlow G τ)
            (fun y : M ↦ Submission.Diff.scalAt (Work.Diff.GE.cfq_sqFlow G τ) y) x
          + 2 * Submission.Diff.ricNormSq (Work.Diff.GE.cfq_sqFlow G τ) x) 0 :=
      (Work.Diff.GE.cfq_laplAt_continuousAt (I := I) (M := M) hLC hJ hsq h0J x hscal).add
        ((Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M) hric).const_mul 2)
    refine ⟨?_, ?_⟩
    · exact Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont1
        (fun s hs => by simp only [Work.Diff.GE.cfq_sqFlow, Real.sq_sqrt hs.1])
    · exact Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont2
        (fun s hs => by simp only [Work.Diff.GE.cfq_sqFlow, Real.sq_sqrt hs.1])

end Work.Diff.GE
