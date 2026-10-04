import Mathlib
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.GE.RL.covRm_linear_fst
import Submission.Work.Diff.GE.rmP_norm_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|(∇Rm)(v, ·, ·, ·, ·)|_ℓ² ≤ |v| · |∇Rm|`

The array `i j k l ↦ (∇Rm)(v, eᵢ, eⱼ, eₖ, eₗ)` at a point `x` (with `e = onFrame g x` a
`g`-orthonormal frame) is the image of `v` under the linear map `v ↦ dRmArr g x v`; its `ℓ²` norm is
therefore bounded by `|v|` times the Frobenius norm of that map, i.e. by
`√(g.inner x v v) * √(dRmNormSq g x)`.

The three ingredients are:

* Parseval's identity in the orthonormal frame `e`, which gives both `∑ i, ⟪eᵢ,v⟫² = ⟪v,v⟫` and the
  expansion `v = ∑ i ⟪eᵢ,v⟫ • eᵢ`;
* the `ℝ`-linearity of `covRm` in its direction slot (`RL.CovRmLinFst g`), which turns
  `covRm g x v …` into `∑ i, ⟪eᵢ,v⟫ * covRm g x (eᵢ) …`;
* the four-fold Cauchy–Schwarz inequality for the flattened index.

The reduction `dRmArr_le_of_CovRmLinFst` performs all of this *without* any separation hypothesis on
`M`; its only input is the direction-linearity of `covRm`.  In the present library that input is
available under `[T2Space M]`, where it is `Work.Diff.GE.RL.covRm_linear_fst` (used below for
`dRmArr_norm_le_t2`); the T2-free version of the same input is
`Work.Diff.GE.covRxnA.covRm_linear_dir_noT2`.
-/

namespace Work.Diff.GE.covRxnA

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Main

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-! ## Parseval in an orthonormal frame (no separation hypothesis needed) -/

/-- **Parseval's identity in a `g`-orthonormal frame**: `∑ i ⟪eᵢ,v⟫ • eᵢ = v`. -/
private theorem parseval_expand (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) : ∑ i, g.inner x (e i) v • e i = v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
  classical
  have hconv : ∀ a b : TangentSpace I x, Inner.inner ℝ a b = g.inner x a b := fun a b => rfl
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hconv (e i) (e j)]
    exact he i j
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
  have hb : (b : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
    coe_basisOfOrthonormalOfCardEqFinrank hon _
  have honb : Orthonormal ℝ (b : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
    rw [hb]; exact hon
  have h := (b.toOrthonormalBasis honb).sum_repr' v
  have hco : (b.toOrthonormalBasis honb : Fin (Module.finrank ℝ E) → TangentSpace I x) = e := by
    rw [Module.Basis.coe_toOrthonormalBasis]; exact hb
  rw [hco] at h
  refine Eq.trans ?_ h
  exact Finset.sum_congr rfl fun i _ => by
    rw [show Inner.inner ℝ (e i) v = g.inner x (e i) v from rfl]

/-- **Parseval's identity, squared form**: `∑ i ⟪eᵢ,v⟫² = ⟪v,v⟫` in a `g`-orthonormal frame. -/
private theorem parseval_sq (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) : ∑ i, (g.inner x (e i) v) ^ 2 = g.inner x v v := by
  have hexp := parseval_expand (I := I) (M := M) g x hn e he v
  have h1 : g.inner x (∑ i, g.inner x (e i) v • e i) v
      = ∑ i, g.inner x (e i) v * g.inner x (e i) v := by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  suffices h : g.inner x v v = ∑ i, (g.inner x (e i) v) ^ 2 by exact h.symm
  calc g.inner x v v
      = g.inner x (∑ i, g.inner x (e i) v • e i) v := by rw [hexp]
    _ = ∑ i, g.inner x (e i) v * g.inner x (e i) v := h1
    _ = ∑ i, (g.inner x (e i) v) ^ 2 := Finset.sum_congr rfl fun i _ => by ring

/-! ## The four-fold Cauchy–Schwarz (pure algebra) -/

/-- **Cauchy–Schwarz for the four-fold array `m ↦ F m`.**  Flattening the quadruple index to a
product type turns this into a double sum of the single-index inequality
`Finset.sum_mul_sq_le_sq_mul_sq`. -/
private theorem quad_cauchy_fin {n : ℕ} (f : Fin n → ℝ)
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, f m * F m i j k l) ^ 2
      ≤ (∑ m, f m ^ 2) * (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (F m i j k l) ^ 2) := by
  have hL : ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, f m * F m i j k l) ^ 2
      = ∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
          (∑ m, f m * F m p.1.1.1 p.1.1.2 p.1.2 p.2) ^ 2 :=
    Work.Diff.GE.sum4_flat (N := ℝ) (n := n)
      (fun i j k l => (∑ m, f m * F m i j k l) ^ 2)
  have hR : ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (F m i j k l) ^ 2
      = ∑ m, ∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
          (F m p.1.1.1 p.1.1.2 p.1.2 p.2) ^ 2 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    exact Work.Diff.GE.sum4_flat (N := ℝ) (n := n) (fun i j k l => (F m i j k l) ^ 2)
  rw [hL, hR]
  calc ∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
        (∑ m, f m * F m p.1.1.1 p.1.1.2 p.1.2 p.2) ^ 2
      ≤ ∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
          (∑ m, f m ^ 2) * (∑ m, (F m p.1.1.1 p.1.1.2 p.1.2 p.2) ^ 2) :=
        Finset.sum_le_sum fun p _ =>
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f
            (fun m => F m p.1.1.1 p.1.1.2 p.1.2 p.2)
    _ = (∑ m, f m ^ 2) * (∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
          ∑ m, (F m p.1.1.1 p.1.1.2 p.1.2 p.2) ^ 2) := by
        rw [Finset.mul_sum]
    _ = (∑ m, f m ^ 2) * (∑ m, ∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
          (F m p.1.1.1 p.1.1.2 p.1.2 p.2) ^ 2) := by
        rw [Finset.sum_comm]

/-! ## Direction-linearity gives the frame expansion of `∇Rm` -/

/-- The finite-sum form of the `ℝ`-linearity of `covRm` in its direction argument. -/
private theorem covRm_finset_sum (g : SMet I M) (hlin : RL.CovRmLinFst g)
    (x : M) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x)
    (a b c' d : TangentSpace I x) :
    covRm g x (∑ i ∈ s, c i • u i) a b c' d
      = ∑ i ∈ s, c i * covRm g x (u i) a b c' d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : covRm g x (0 : TangentSpace I x) a b c' d = 0 := by
        have h := hlin x 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x) a b c' d
        simpa using h
      simpa using h0
  | insert i s hi ih =>
      have h := hlin x (c i) 1 (u i) (∑ j ∈ s, c j • u j) a b c' d
      rw [one_smul] at h
      rw [Finset.sum_insert hi, h, ih, Finset.sum_insert hi, one_mul]

/-- **Expansion of `∇Rm` in the direction slot**, in an orthonormal frame. -/
private theorem covRm_expand_dir (g : SMet I M) (hlin : RL.CovRmLinFst g) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (v a b c d : TangentSpace I x)
    (hexp : ∑ m, g.inner x (e m) v • e m = v) :
    covRm g x v a b c d = ∑ m, g.inner x (e m) v * covRm g x (e m) a b c d := by
  conv_lhs => rw [← hexp]
  exact covRm_finset_sum (I := I) (M := M) g hlin x Finset.univ
    (fun m => g.inner x (e m) v) e a b c d

/-! ## The main reduction -/

/-- **The `ℓ²` norm of the array `(∇Rm)(v, ·, ·, ·, ·)` is bounded by `|v| |∇Rm|`**, from the
`ℝ`-linearity of `covRm` in its direction slot alone.  No separation hypothesis on `M` is used. -/
theorem dRmArr_le_of_CovRmLinFst (g : SMet I M) (hlin : RL.CovRmLinFst g) (x : M)
    (v : TangentSpace I x) :
    Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
        (covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l)) ^ 2)
      ≤ Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) := by
  by_cases hpos : 0 < Module.finrank ℝ E
  · set e : Fin (Module.finrank ℝ E) → TangentSpace I x := onFrame g x with he_def
    have he : IsONFrame g x e := by
      rw [he_def]; exact Work.Diff.L.onFrame_isONFrame g x
    have hexp : ∑ m, g.inner x (e m) v • e m = v :=
      parseval_expand (I := I) (M := M) g x hpos e he v
    have hpar : ∑ m, (g.inner x (e m) v) ^ 2 = g.inner x v v :=
      parseval_sq (I := I) (M := M) g x hpos e he v
    have hcs := quad_cauchy_fin (n := Module.finrank ℝ E) (fun m => g.inner x (e m) v)
      (fun m i j k l => covRm g x (e m) (e i) (e j) (e k) (e l))
    have hexpand : ∀ i j k l, covRm g x v (e i) (e j) (e k) (e l)
        = ∑ m, g.inner x (e m) v * covRm g x (e m) (e i) (e j) (e k) (e l) :=
      fun i j k l => covRm_expand_dir (I := I) (M := M) g hlin x e v (e i) (e j) (e k) (e l) hexp
    have hL : ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x v (e i) (e j) (e k) (e l)) ^ 2
        = ∑ i, ∑ j, ∑ k, ∑ l,
            (∑ m, g.inner x (e m) v * covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hexpand i j k l]
    have hkey : ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x v (e i) (e j) (e k) (e l)) ^ 2
        ≤ g.inner x v v * dRmNormSq g x := by
      rw [hL]
      refine le_trans hcs ?_
      rw [hpar]
      exact le_of_eq (by rw [Submission.Diff.dRmNormSq])
    have hnonneg : 0 ≤ g.inner x v v := by
      rw [← hpar]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    exact le_trans (Real.sqrt_le_sqrt hkey)
      (le_of_eq (Real.sqrt_mul hnonneg (dRmNormSq g x)))
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hpos
    simp [Submission.Diff.dRmNormSq, h0]

/-- **The requested bound, in the setting where the direction-linearity of `∇Rm` is available
in the library** (i.e. under `[T2Space M]`, from `Work.Diff.GE.RL.covRm_linear_fst`). -/
theorem dRmArr_norm_le_t2 [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v : TangentSpace I x) :
    Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
        (Submission.Diff.covRm g x v (Submission.Diff.onFrame g x i)
          (Submission.Diff.onFrame g x j) (Submission.Diff.onFrame g x k)
          (Submission.Diff.onFrame g x l)) ^ 2)
      ≤ Real.sqrt (g.inner x v v) * Real.sqrt (Submission.Diff.dRmNormSq g x) :=
  dRmArr_le_of_CovRmLinFst g (RL.covRm_linear_fst (I := I) (M := M) hLC g) x v

end Main

end Work.Diff.GE.covRxnA
