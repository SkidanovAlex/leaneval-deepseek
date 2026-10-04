import Mathlib
import Submission.Work.Diff.GE.Api
import Submission.Work.Diff.GE.frame_family_defs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.frameFamily_at_self
import Submission.Work.Diff.GE.isONFrame_frameFamily
import Submission.Work.Diff.GE.ricAt_eq_sum_frame
import Submission.Work.Diff.GE.gs_self
import Submission.Work.Diff.GE.gs_isON_of_posDef
import Submission.Work.Diff.GE.linearIndependent_of_isONFrame
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]



/-! ## Elementary algebra of the curvature array

The `(1,1)`-Ricci contraction `ricAt` is bounded by the Frobenius norm of the curvature array.  We
only need a universal (not sharp) constant, which is why the estimate below loses two powers of `n`:
each row entry is bounded by `frobSq` and the resulting `n²` terms are summed. -/

/-- The Frobenius norm of a curvature array is nonnegative. -/
theorem uniformBound_frobSq_nonneg {n : ℕ} (R : Curv4 n) : 0 ≤ frobSq R := by
  rw [frobSq]
  positivity

/-- Each entry of the Ricci contraction of an array is bounded by `n^2` times the Frobenius norm. -/
theorem uniformBound_ricEntry_le_frobSq {n : ℕ} (R : Curv4 n) (i j : Fin n) :
    (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) ^ 2 * frobSq R := by
  have step1 : (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) * ∑ k, (R k i k j) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin n => R k i k j)
    simpa [Finset.card_univ, Fintype.card_fin] using h
  have hsingle : ∀ k : Fin n, (R k i k j) ^ 2 ≤ frobSq R := by
    intro k
    have hs1 : (R k i k j) ^ 2 ≤ ∑ a : Fin n, (R a i k j) ^ 2 :=
      Finset.single_le_sum (f := fun a : Fin n => (R a i k j) ^ 2) (fun a _ => sq_nonneg _)
        (Finset.mem_univ k)
    have hs2 : ∑ a : Fin n, (R a i k j) ^ 2 ≤ ∑ a : Fin n, ∑ b : Fin n, (R a b k j) ^ 2 :=
      Finset.sum_le_sum fun a _ =>
        Finset.single_le_sum (f := fun b : Fin n => (R a b k j) ^ 2) (fun b _ => sq_nonneg _)
          (Finset.mem_univ i)
    have hs3 : ∑ a : Fin n, ∑ b : Fin n, (R a b k j) ^ 2
        ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, (R a b c j) ^ 2 :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        Finset.single_le_sum (f := fun c : Fin n => (R a b c j) ^ 2) (fun c _ => sq_nonneg _)
          (Finset.mem_univ k)
    have hs4 : ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, (R a b c j) ^ 2
        ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, (R a b c d) ^ 2 :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
        Finset.single_le_sum (f := fun d : Fin n => (R a b c d) ^ 2) (fun d _ => sq_nonneg _)
          (Finset.mem_univ j)
    rw [frobSq]
    linarith [hs1, hs2, hs3, hs4]
  have hsum : ∑ k : Fin n, (R k i k j) ^ 2 ≤ (n : ℝ) * frobSq R := by
    calc ∑ k : Fin n, (R k i k j) ^ 2 ≤ ∑ _k : Fin n, frobSq R :=
          Finset.sum_le_sum fun k _ => hsingle k
      _ = (n : ℝ) * frobSq R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) * ∑ k, (R k i k j) ^ 2 := step1
    _ ≤ (n : ℝ) * ((n : ℝ) * frobSq R) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
    _ = (n : ℝ) ^ 2 * frobSq R := by ring

/-- A row of the Ricci contraction is bounded by `n^3` times the Frobenius norm. -/
theorem uniformBound_ricRow_le_frobSq {n : ℕ} (R : Curv4 n) (i : Fin n) :
    ∑ j, (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) ^ 3 * frobSq R := by
  have h1 : ∀ j : Fin n, (∑ k, R k i k j) ^ 2 ≤ (n : ℝ) ^ 2 * frobSq R :=
    fun j => uniformBound_ricEntry_le_frobSq R i j
  calc ∑ j : Fin n, (∑ k, R k i k j) ^ 2 ≤ ∑ _j : Fin n, (n : ℝ) ^ 2 * frobSq R :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = (n : ℝ) * ((n : ℝ) ^ 2 * frobSq R) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) ^ 3 * frobSq R := by ring

/-! ## Bilinearity of the frozen Ricci contraction -/

/-- `ricAt` is additive in its second argument (for a smooth connection). -/
theorem uniformBound_ricAt_add_snd {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M) (u v₁ v₂ : TangentSpace I x) :
    ricAt (lcOf g) x u (v₁ + v₂) = ricAt (lcOf g) x u v₁ + ricAt (lcOf g) x u v₂ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  unfold ricAt
  rw [Finset.sum_congr rfl (fun k _ => ?_), Finset.sum_add_distrib]
  exact (congrArg ((Module.finBasis ℝ E).coord k)
      (rmVec_add_right (lcOf g) hcov x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v₁ v₂)).trans
    (((Module.finBasis ℝ E).coord k).map_add
      (rmVec (lcOf g) x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v₁)
      (rmVec (lcOf g) x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v₂))

/-- `ricAt` is homogeneous in its second argument (for a smooth connection). -/
theorem uniformBound_ricAt_smul_snd {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M) (c : ℝ) (u v : TangentSpace I x) :
    ricAt (lcOf g) x u (c • v) = c * ricAt (lcOf g) x u v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  unfold ricAt
  rw [Finset.sum_congr rfl (fun k _ => ?_), ← Finset.mul_sum]
  exact (congrArg ((Module.finBasis ℝ E).coord k)
      (rmVec_smul_right (lcOf g) hcov x c ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v)).trans
    ((((Module.finBasis ℝ E).coord k).map_smul c
      (rmVec (lcOf g) x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v)).trans (by simp))

/-- `ricAt` is additive in its first argument (for a smooth connection). -/
theorem uniformBound_ricAt_add_fst {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M) (u₁ u₂ v : TangentSpace I x) :
    ricAt (lcOf g) x (u₁ + u₂) v = ricAt (lcOf g) x u₁ v + ricAt (lcOf g) x u₂ v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  unfold ricAt
  rw [Finset.sum_congr rfl (fun k _ => ?_), Finset.sum_add_distrib]
  exact (congrArg ((Module.finBasis ℝ E).coord k)
      (rmVec_add_middle (lcOf g) hcov x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u₁ u₂ v)).trans
    (((Module.finBasis ℝ E).coord k).map_add
      (rmVec (lcOf g) x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u₁ v)
      (rmVec (lcOf g) x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u₂ v))

/-- `ricAt` is homogeneous in its first argument (for a smooth connection). -/
theorem uniformBound_ricAt_smul_fst {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M) (c : ℝ) (u v : TangentSpace I x) :
    ricAt (lcOf g) x (c • u) v = c * ricAt (lcOf g) x u v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  unfold ricAt
  rw [Finset.sum_congr rfl (fun k _ => ?_), ← Finset.mul_sum]
  exact (congrArg ((Module.finBasis ℝ E).coord k)
      (rmVec_smul_middle (lcOf g) hcov x c ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v)).trans
    ((((Module.finBasis ℝ E).coord k).map_smul c
      (rmVec (lcOf g) x ((Module.finBasis ℝ E k : E) : TangentSpace I x) u v)).trans (by simp))

/-- `ricAt` of the zero vector. -/
theorem uniformBound_ricAt_zero_snd {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M) (u : TangentSpace I x) :
    ricAt (lcOf g) x u (0 : TangentSpace I x) = 0 := by
  have h := uniformBound_ricAt_add_snd hcov x u (0 : TangentSpace I x) 0
  rw [add_zero] at h
  linarith

/-- `ricAt` of the zero vector in the first slot. -/
theorem uniformBound_ricAt_zero_fst {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M) (v : TangentSpace I x) :
    ricAt (lcOf g) x (0 : TangentSpace I x) v = 0 := by
  have h := uniformBound_ricAt_add_fst hcov x (0 : TangentSpace I x) 0 v
  rw [add_zero] at h
  linarith

/-- `ricAt` evaluated at a linear combination of the second argument. -/
theorem uniformBound_ricAt_sum {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → TangentSpace I x) (u : TangentSpace I x) :
    ricAt (lcOf g) x u (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i * ricAt (lcOf g) x u (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, uniformBound_ricAt_zero_snd hcov]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, uniformBound_ricAt_add_snd hcov,
        uniformBound_ricAt_smul_snd hcov, ih]

/-- `ricAt` evaluated at a linear combination of the first argument. -/
theorem uniformBound_ricAt_sum_fst {g : SMet I M}
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (x : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → TangentSpace I x) (v : TangentSpace I x) :
    ricAt (lcOf g) x (∑ i ∈ s, c i • w i) v = ∑ i ∈ s, c i * ricAt (lcOf g) x (w i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, uniformBound_ricAt_zero_fst hcov]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, uniformBound_ricAt_add_fst hcov,
        uniformBound_ricAt_smul_fst hcov, ih]

/-! ## The inner product of two linear combinations of an orthonormal frame -/

/-- For a `g`-orthonormal frame `e`, the inner product of two linear combinations is the sum of the
products of the coefficients. -/
theorem uniformBound_inner_sum_smul {g : SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (c c' : Fin (Module.finrank ℝ E) → ℝ) :
    g.inner x (∑ j, c j • e j) (∑ j, c' j • e j) = ∑ j, c j * c' j := by
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ k, c k * g.inner x (e k) (e j)) = c j := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [he j j]; simp
    · intro k _ hk
      rw [he k j, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hinner j]
  ring

/-- The squared norm of a linear combination. -/
theorem uniformBound_inner_self_sum_smul {g : SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    g.inner x (∑ j, c j • e j) (∑ j, c j • e j) = ∑ j, (c j) ^ 2 := by
  rw [uniformBound_inner_sum_smul x e he c c]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Linearity of the metric pairing in its **second** argument, in the form needed for the frame
computation: expanding the second vector in terms of a family `w` turns the pairing into the sum of
the products with the coefficients. -/
theorem uniformBound_inner_sum_smul_snd {g' : SMet I M} (x : M) (a : TangentSpace I x)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    g'.inner x a (∑ l, c l • w l) = ∑ l, c l * g'.inner x a (w l) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]

/-! ## The frozen Ricci contraction in the chosen orthonormal frame -/

/-- **The frozen trace `ricAt` is the metric trace in an orthonormal frame**: the trace of the
endomorphism `w ↦ R(w,u)v` is independent of the basis in which it is computed. -/
theorem uniformBound_ricAt_eq_sum_frame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (u v : TangentSpace I x) :
    ricAt (lcOf g) x u v = ∑ m, rmP g x (e m) u (e m) v := by
  by_cases hn : Module.finrank ℝ E = 0
  · haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hn]; infer_instance
    unfold ricAt
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    obtain ⟨hcovne, -, -⟩ := hLC g
    obtain ⟨hcov⟩ := hcovne
    have hconv : ∀ a b : TangentSpace I x, Inner.inner ℝ a b = g.inner x a b := fun a b => rfl
    let T : E →ₗ[ℝ] E :=
      { toFun := fun w => rmVec (lcOf g) x w u v
        map_add' := fun a b => rmVec_add_left (lcOf g) hcov x a b u v
        map_smul' := fun c a => rmVec_smul_left (lcOf g) hcov x c a u v }
    have hleft : ricAt (lcOf g) x u v
        = ∑ i, (Module.finBasis ℝ E).coord i (T ((Module.finBasis ℝ E) i)) := rfl
    have hmatrix : (∑ i, (Module.finBasis ℝ E).coord i (T ((Module.finBasis ℝ E) i)))
        = Matrix.trace (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T) := by
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
    have htrace : Matrix.trace (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T)
        = LinearMap.trace ℝ E T :=
      (LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) T).symm
    have hbridge : LinearMap.trace ℝ E T = LinearMap.trace ℝ (TangentSpace I x) T := rfl
    have hnpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hn
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hnpos
    have hon : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [hconv (e i) (e j)]
      exact he i j
    let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
    have hc : (c : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
      coe_basisOfOrthonormalOfCardEqFinrank hon _
    have honc : Orthonormal ℝ (c : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
      rw [hc]; exact hon
    have hsuminner : LinearMap.trace ℝ (TangentSpace I x) T
        = ∑ i, Inner.inner ℝ (e i) (T (e i)) := by
      have h := LinearMap.trace_eq_sum_inner T (c.toOrthonormalBasis honc)
      rw [Module.Basis.coe_toOrthonormalBasis c honc, hc] at h
      exact h
    have hfinal : (∑ i, Inner.inner ℝ (e i) (T (e i))) = ∑ i, rmP g x (e i) u (e i) v := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hconv (e i) (T (e i)), g.symm x (e i) (T (e i))]
      rfl
    exact hleft.trans (hmatrix.trans (htrace.trans (hbridge.trans (hsuminner.trans hfinal))))

/-- The frozen trace `ricAt` in the orthonormal frame `onFrame g x` is the corresponding row of the
curvature array `rmC g x`. -/
theorem uniformBound_ricAt_eq_rmC (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ricAt (lcOf g) x (onFrame g x i) (onFrame g x j) = ∑ m, rmC g x m i m j := by
  rw [uniformBound_ricAt_eq_sum_frame hLC g x (onFrame g x) (isONFrame_onFrame g x)
    (onFrame g x i) (onFrame g x j)]
  exact Finset.sum_congr rfl fun m _ => rfl

/-- **The velocity of the Gram–Schmidt frame is bounded by the curvature.** -/
theorem uniformBound_frameEdot_inner_le (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (G t).inner x (frameEdot G t x i) (frameEdot G t x i)
      ≤ 4 * (Module.finrank ℝ E : ℝ) ^ 3 * rmNormSq (G t) x := by
  classical
  set b := onFrame (G t) x with hb
  have hON : IsONFrame (G t) x b := isONFrame_onFrame (G t) x
  set coef : Fin (Module.finrank ℝ E) → ℝ := fun j =>
    if j = i then ricAt (lcOf (G t)) x (b i) (b i)
    else if j.val < i.val then 2 * ricAt (lcOf (G t)) x (b i) (b j) else 0 with hcoef
  have hA : (ricAt (lcOf (G t)) x (b i) (b i)) • b i
      = ∑ j, (if j = i then ricAt (lcOf (G t)) x (b i) (b i) else 0) • b j := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro j _ hj; rw [if_neg hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hB : (∑ j, if j.val < i.val
        then (2 * ricAt (lcOf (G t)) x (b i) (b j)) • b j else 0)
      = ∑ j, (if j.val < i.val then 2 * ricAt (lcOf (G t)) x (b i) (b j) else 0) • b j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.val < i.val
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, zero_smul]
  have hdecomp : frameEdot G t x i = ∑ j, coef j • b j := by
    have h1 : frameEdot G t x i
        = (ricAt (lcOf (G t)) x (b i) (b i)) • b i
          + ∑ j, if j.val < i.val
              then (2 * ricAt (lcOf (G t)) x (b i) (b j)) • b j else 0 := by
      simp only [frameEdot, hb]
    have hgoal : ∀ j : Fin (Module.finrank ℝ E),
        (if j = i then ricAt (lcOf (G t)) x (b i) (b i) else 0) • b j
          + (if j.val < i.val then 2 * ricAt (lcOf (G t)) x (b i) (b j) else 0) • b j
        = (if j = i then ricAt (lcOf (G t)) x (b i) (b i)
            else if j.val < i.val then 2 * ricAt (lcOf (G t)) x (b i) (b j) else 0) • b j := by
      intro j
      by_cases hji : j = i
      · simp only [hji, ↓reduceIte, lt_irrefl, ↓reduceDIte, zero_smul, add_zero]
      · by_cases hj : j.val < i.val
        · simp only [hji, hj, ↓reduceIte, ↓reduceDIte, zero_smul, zero_add]
        · simp only [hji, hj, ↓reduceIte, ↓reduceDIte, zero_smul, zero_add, add_zero]
    rw [h1, hA, hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hcoef]
    exact hgoal j

  rw [hdecomp, uniformBound_inner_self_sum_smul x b hON coef]
  have hcle : ∀ j, (coef j) ^ 2
      ≤ 4 * (ricAt (lcOf (G t)) x (b i) (b j)) ^ 2 := by
    intro j
    have hcoe : coef j = (if j = i then ricAt (lcOf (G t)) x (b i) (b i)
        else if j.val < i.val then 2 * ricAt (lcOf (G t)) x (b i) (b j) else 0) := by
      rw [hcoef]
    rw [hcoe]
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte, lt_irrefl, ↓reduceDIte, zero_smul, add_zero]
      nlinarith [sq_nonneg (ricAt (lcOf (G t)) x (b i) (b i))]
    · by_cases hj : j.val < i.val
      · simp only [hji, hj, ↓reduceIte, ↓reduceDIte, zero_smul, zero_add]
        nlinarith [sq_nonneg (ricAt (lcOf (G t)) x (b i) (b j))]
      · simp only [hji, hj, ↓reduceIte, ↓reduceDIte, zero_smul, zero_add, add_zero]
        nlinarith [sq_nonneg (ricAt (lcOf (G t)) x (b i) (b j))]
  have hrow := uniformBound_ricRow_le_frobSq (rmC (G t) x) i
  have hric : (∑ j, (ricAt (lcOf (G t)) x (b i) (b j)) ^ 2)
      = ∑ j, (∑ m, rmC (G t) x m i m j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [uniformBound_ricAt_eq_rmC hLC (G t) x i j]
  calc ∑ j, (coef j) ^ 2 ≤ ∑ j, 4 * (ricAt (lcOf (G t)) x (b i) (b j)) ^ 2 :=
        Finset.sum_le_sum fun j _ => hcle j
    _ = 4 * ∑ j, (ricAt (lcOf (G t)) x (b i) (b j)) ^ 2 := by rw [Finset.mul_sum]
    _ = 4 * ∑ j, (∑ m, rmC (G t) x m i m j) ^ 2 := by rw [hric]
    _ ≤ 4 * ((Module.finrank ℝ E : ℝ) ^ 3 * frobSq (rmC (G t) x)) :=
        mul_le_mul_of_nonneg_left hrow (by norm_num)
    _ = 4 * (Module.finrank ℝ E : ℝ) ^ 3 * rmNormSq (G t) x := by
        rw [rmNormSq]; ring


/-! ## Derivatives of the metric pairing along the flow

These are the two special cases of the product rule that the frame computation needs: a *fixed*
first argument against a moving second one, and the quadratic case of a single moving curve. The
identity `∂ₛ g = -2 Ric` of the Ricci flow (`IsRicciFlow`) provides the derivative of the metric
itself. -/

variable {T : ℝ} {G : ℝ → SMet I M}

/-- `s ↦ (G s).inner x a (V s)` with a *fixed* first argument. -/
theorem uniformBound_pairing_const_fst (hflow : IsRicciFlow G T) (t : ℝ) (ht : t ∈ Set.Ico 0 T)
    (x : M) (a : TangentSpace I x) (hnt : 0 < Module.finrank ℝ E) {V : ℝ → TangentSpace I x}
    {V' : TangentSpace I x} (hV : HasDerivWithinAt V V' (Set.Ico 0 T) t) :
    HasDerivWithinAt (fun s ↦ (G s).inner x a (V s))
      (-2 * ricAt (lcOf (G t)) x a (V t) + (G t).inner x a V') (Set.Ico 0 T) t := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  set b := onFrame (G t) x with hb
  have hON : IsONFrame (G t) x b := isONFrame_onFrame (G t) x
  have hc : ∀ l : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s ↦ (G t).inner x (b l) (V s)) ((G t).inner x (b l) V')
        (Set.Ico 0 T) t := by
    intro l
    have hcomp := (ContinuousLinearMap.hasFDerivAt ((G t).inner x (b l))).comp_hasDerivWithinAt t hV
    simpa only [Function.comp_def] using hcomp
  have hnu : ∀ l : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s ↦ (G s).inner x a (b l)) (-2 * ricAt (lcOf (G t)) x a (b l))
        (Set.Ico 0 T) t :=
    fun l => hflow.2 t ht x a (b l)
  have hexp : ∀ s, (G s).inner x a (V s)
      = ∑ l, (G t).inner x (b l) (V s) * (G s).inner x a (b l) := by
    intro s
    conv_lhs => rw [← sum_inner_smul_eq_self (G t) x hnt b hON (V s)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  have hterm : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      HasDerivWithinAt (fun s ↦ (G t).inner x (b l) (V s) * (G s).inner x a (b l))
        ((G t).inner x (b l) V' * (G t).inner x a (b l)
          + (G t).inner x (b l) (V t) * (-2 * ricAt (lcOf (G t)) x a (b l)))
        (Set.Ico 0 T) t :=
    fun l _ => (hc l).mul (hnu l)
  have hsum : HasDerivWithinAt
      (fun s ↦ ∑ l, (G t).inner x (b l) (V s) * (G s).inner x a (b l))
      (∑ l, ((G t).inner x (b l) V' * (G t).inner x a (b l)
        + (G t).inner x (b l) (V t) * (-2 * ricAt (lcOf (G t)) x a (b l))))
      (Set.Ico 0 T) t := by
    have h := HasDerivWithinAt.sum (u := Finset.univ) hterm
    have hfun : (∑ l : Fin (Module.finrank ℝ E),
          (fun s ↦ (G t).inner x (b l) (V s) * (G s).inner x a (b l)))
        = fun s ↦ ∑ l, (G t).inner x (b l) (V s) * (G s).inner x a (b l) := by
      funext s
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hcov : ContMDiffCovariantDerivative (lcOf (G t)) ∞ :=
    (Work.EXT.lcSmooth_noBoundary (I := I) (M := M) (G t)).1.some
  have hval : (∑ l, ((G t).inner x (b l) V' * (G t).inner x a (b l)
        + (G t).inner x (b l) (V t) * (-2 * ricAt (lcOf (G t)) x a (b l))))
      = -2 * ricAt (lcOf (G t)) x a (V t) + (G t).inner x a V' := by
    have h1 : (∑ l, (G t).inner x (b l) (V t) * (-2 * ricAt (lcOf (G t)) x a (b l)))
        = -2 * ricAt (lcOf (G t)) x a (V t) := by
      have h3 : (∑ l, (G t).inner x (b l) (V t) * (-2 * ricAt (lcOf (G t)) x a (b l)))
          = -2 * ∑ l, (G t).inner x (b l) (V t) * ricAt (lcOf (G t)) x a (b l) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      have h2 := uniformBound_ricAt_sum hcov x (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => (G t).inner x (b l) (V t)) b a
      rw [h3, ← h2, sum_inner_smul_eq_self (G t) x hnt b hON (V t)]
    have h3 : (∑ l, (G t).inner x (b l) V' * (G t).inner x a (b l))
        = (G t).inner x a V' := by
      rw [← uniformBound_inner_sum_smul_snd (g' := G t) x a
            (fun l => (G t).inner x (b l) V') b,
        sum_inner_smul_eq_self (G t) x hnt b hON V']
    rw [Finset.sum_add_distrib, h1, h3]
    ring
  have hmain := hsum.congr (fun s _ => (hexp s)) (hexp t)
  exact hmain.congr_deriv hval

/-- `s ↦ (G s).inner x (U s) (U s)` for a single moving curve. -/
theorem uniformBound_pairing_self (hflow : IsRicciFlow G T) (t : ℝ) (ht : t ∈ Set.Ico 0 T)
    (x : M) (hnt : 0 < Module.finrank ℝ E) {U : ℝ → TangentSpace I x} {U' : TangentSpace I x}
    (hU : HasDerivWithinAt U U' (Set.Ico 0 T) t) :
    HasDerivWithinAt (fun s ↦ (G s).inner x (U s) (U s))
      (-2 * ricAt (lcOf (G t)) x (U t) (U t) + (G t).inner x U' (U t) + (G t).inner x (U t) U')
      (Set.Ico 0 T) t := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  set b := onFrame (G t) x with hb
  have hON : IsONFrame (G t) x b := isONFrame_onFrame (G t) x
  have hc : ∀ l : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s ↦ (G t).inner x (b l) (U s)) ((G t).inner x (b l) U')
        (Set.Ico 0 T) t := by
    intro l
    have hcomp := (ContinuousLinearMap.hasFDerivAt ((G t).inner x (b l))).comp_hasDerivWithinAt t hU
    simpa only [Function.comp_def] using hcomp
  have hpair : ∀ l : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s ↦ (G s).inner x (b l) (U s))
        (-2 * ricAt (lcOf (G t)) x (b l) (U t) + (G t).inner x (b l) U') (Set.Ico 0 T) t :=
    fun l => uniformBound_pairing_const_fst hflow t ht x (b l) hnt hU
  have hexp : ∀ s, (G s).inner x (U s) (U s)
      = ∑ l, (G t).inner x (b l) (U s) * (G s).inner x (b l) (U s) := by
    intro s
    have hL : (G s).inner x (U s) (U s)
        = (G s).inner x (U s) (∑ l, (G t).inner x (b l) (U s) • b l) := by
      rw [sum_inner_smul_eq_self (G t) x hnt b hON (U s)]
    rw [hL, uniformBound_inner_sum_smul_snd (g' := G s) x (U s)
      (fun l => (G t).inner x (b l) (U s)) b]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(G s).symm x (U s) (b l)]
  have hterm : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      HasDerivWithinAt (fun s ↦ (G t).inner x (b l) (U s) * (G s).inner x (b l) (U s))
        ((G t).inner x (b l) U' * (G t).inner x (b l) (U t)
          + (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)
              + (G t).inner x (b l) U'))
        (Set.Ico 0 T) t :=
    fun l _ => (hc l).mul (hpair l)
  have hsum : HasDerivWithinAt
      (fun s ↦ ∑ l, (G t).inner x (b l) (U s) * (G s).inner x (b l) (U s))
      (∑ l, ((G t).inner x (b l) U' * (G t).inner x (b l) (U t)
        + (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)
            + (G t).inner x (b l) U')))
      (Set.Ico 0 T) t := by
    have h := HasDerivWithinAt.sum (u := Finset.univ) hterm
    have hfun : (∑ l : Fin (Module.finrank ℝ E),
          (fun s ↦ (G t).inner x (b l) (U s) * (G s).inner x (b l) (U s)))
        = fun s ↦ ∑ l, (G t).inner x (b l) (U s) * (G s).inner x (b l) (U s) := by
      funext s
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hcov : ContMDiffCovariantDerivative (lcOf (G t)) ∞ :=
    (Work.EXT.lcSmooth_noBoundary (I := I) (M := M) (G t)).1.some
  have hval : (∑ l, ((G t).inner x (b l) U' * (G t).inner x (b l) (U t)
        + (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)
            + (G t).inner x (b l) U')))
      = -2 * ricAt (lcOf (G t)) x (U t) (U t) + (G t).inner x U' (U t)
        + (G t).inner x (U t) U' := by
    have h1 : (∑ l, (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)))
        = -2 * ricAt (lcOf (G t)) x (U t) (U t) := by
      have h3 : (∑ l, (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)))
          = -2 * ∑ l, (G t).inner x (b l) (U t) * ricAt (lcOf (G t)) x (b l) (U t) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      have h2 := uniformBound_ricAt_sum_fst hcov x (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => (G t).inner x (b l) (U t)) b (U t)
      rw [h3, ← h2, sum_inner_smul_eq_self (G t) x hnt b hON (U t)]
    have h4 : (∑ l, (G t).inner x (b l) U' * (G t).inner x (b l) (U t))
        = (G t).inner x U' (U t) := by
      rw [← uniformBound_inner_sum_smul (g := G t) x b hON
            (fun l => (G t).inner x (b l) U') (fun l => (G t).inner x (b l) (U t)),
        sum_inner_smul_eq_self (G t) x hnt b hON U',
        sum_inner_smul_eq_self (G t) x hnt b hON (U t)]
    have h5 : (∑ l, (G t).inner x (b l) (U t) * (G t).inner x (b l) U')
        = (G t).inner x (U t) U' := by
      rw [← uniformBound_inner_sum_smul (g := G t) x b hON
            (fun l => (G t).inner x (b l) (U t)) (fun l => (G t).inner x (b l) U'),
        sum_inner_smul_eq_self (G t) x hnt b hON (U t),
        sum_inner_smul_eq_self (G t) x hnt b hON U']
    have hB : (∑ l, (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)
          + (G t).inner x (b l) U'))
        = (∑ l, (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)))
          + (∑ l, (G t).inner x (b l) (U t) * (G t).inner x (b l) U') := by
      calc (∑ l, (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)
              + (G t).inner x (b l) U'))
          = ∑ l, ((G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t))
              + (G t).inner x (b l) (U t) * (G t).inner x (b l) U') :=
            Finset.sum_congr rfl (fun l _ => by ring)
        _ = (∑ l, (G t).inner x (b l) (U t) * (-2 * ricAt (lcOf (G t)) x (b l) (U t)))
              + (∑ l, (G t).inner x (b l) (U t) * (G t).inner x (b l) U') :=
            Finset.sum_add_distrib
    rw [Finset.sum_add_distrib, h4, hB, h1, h5]
    ring
  have hmain := hsum.congr (fun s _ => (hexp s)) (hexp t)
  exact hmain.congr_deriv hval

/-! ## The model-space structure on the tangent spaces

`TangentSpace I x` is a type synonym for the model space `E`, which type class inference does not
unfold; the instances below provide the model-space structure (and its compatible module structure)
on the fibres, so that `HasDerivWithinAt` for curves in `TangentSpace I x` can be manipulated as
usual.  They are the model-space structures, so they agree with the ones induced by any
`RiemannianBundle` instance; the high priorities keep the module structure coherent with the scalar
action used by the definitions of this area. -/

noncomputable scoped instance (priority := 50) instUB_NAG (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  (inferInstanceAs (NormedAddCommGroup E) : NormedAddCommGroup E)

noncomputable scoped instance (priority := 50) instUB_NS (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  (inferInstanceAs (NormedSpace ℝ E) : NormedSpace ℝ E)

noncomputable scoped instance (priority := 3000) instUB_Module (x : M) : Module ℝ (TangentSpace I x) :=
  (inferInstanceAs (Module ℝ E) : Module ℝ E)

noncomputable scoped instance (priority := 3000) instUB_CSMul (x : M) : ContinuousSMul ℝ (TangentSpace I x) :=
  (inferInstanceAs (ContinuousSMul ℝ E) : ContinuousSMul ℝ E)

noncomputable scoped instance (priority := 3000) instUB_BSMul (x : M) : IsBoundedSMul ℝ (TangentSpace I x) :=
  (inferInstanceAs (IsBoundedSMul ℝ E) : IsBoundedSMul ℝ E)

noncomputable scoped instance (priority := 3000) instUB_STower (x : M) : IsScalarTower ℝ ℝ (TangentSpace I x) :=
  (inferInstanceAs (IsScalarTower ℝ ℝ E) : IsScalarTower ℝ ℝ E)

/-! ## The frame family: orthonormality and the time derivative

These are the two facts the uniform frame family needs: the Gram–Schmidt family
`frameFamily G t x s` is `G s`-orthonormal for *every* `s` (because `onFrame (G t) x` is linearly
independent), and it is differentiable at `s = t` with the explicit Uhlenbeck derivative
`frameEdot G t x`. -/

/-- A base frame vector is a unit vector for the metric `G t`. -/
theorem uniformBound_frameB_onFrame_self {t : ℝ} (x : M) (i : Fin (Module.finrank ℝ E)) :
    frameB G x t (onFrame (G t) x i) (onFrame (G t) x i) = 1 := by
  rw [frameB]
  simpa using isONFrame_onFrame (G t) x i i

/-- Two distinct base frame vectors are orthogonal for the metric `G t`. -/
theorem uniformBound_frameB_onFrame_eq_zero {t : ℝ} (x : M)
    {i j : Fin (Module.finrank ℝ E)} (hij : i ≠ j) :
    frameB G x t (onFrame (G t) x i) (onFrame (G t) x j) = 0 := by
  rw [frameB, isONFrame_onFrame (G t) x i j, ite_eq_right hij]

/-- A base frame vector is orthogonal to the Uhlenbeck derivative of a vector of smaller index. -/
theorem uniformBound_frameB_onFrame_frameEdot_eq_zero {t : ℝ} (x : M)
    {i j : Fin (Module.finrank ℝ E)} (hji : j.val < i.val) :
    frameB G x t (onFrame (G t) x i) (frameEdot G t x j) = 0 := by
  have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hzero : ∀ l : Fin (Module.finrank ℝ E), l.val < j.val →
      frameB G x t (onFrame (G t) x i) (onFrame (G t) x l) = 0 :=
    fun l _ => uniformBound_frameB_onFrame_eq_zero (G := G) x (Fin.ne_of_val_ne (by omega))
  rw [frameEdot, frameB, map_add, map_smul, map_sum]
  rw [show (G t).inner x (onFrame (G t) x i) (onFrame (G t) x j) = 0 from by
        rw [← frameB]; exact uniformBound_frameB_onFrame_eq_zero (G := G) x hij]
  rw [smul_zero, zero_add]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hlj : l.val < j.val
  · rw [ite_eq_left hlj, map_smul,
      show (G t).inner x (onFrame (G t) x i) (onFrame (G t) x l) = 0 from by
        rw [← frameB]; exact hzero l hlj, smul_zero]
  · rw [ite_eq_right hlj]
    exact map_zero _

/-- The explicit expansion of `frameEdot` in the frame `onFrame (G t) x`. -/
theorem uniformBound_frameEdot_expand (t : ℝ) (x : M) (i : Fin (Module.finrank ℝ E)) :
    frameEdot G t x i =
      (ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x i)) • (onFrame (G t) x i)
        + ∑ j : Fin (Module.finrank ℝ E),
            if j.val < i.val then
              (2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j)) • (onFrame (G t) x j)
            else 0 := rfl

/-- **The Gram–Schmidt family is orthonormal** (for the metric `G s`), for *every* `s`. -/
theorem uniformBound_isONFrame_frameFamily (G : ℝ → SMet I M) (t s : ℝ) (x : M) :
    IsONFrame (G s) x (frameFamily G t x s) := by
  have hadd₁ : ∀ u v w : TangentSpace I x,
      frameB G x s (u + v) w = frameB G x s u w + frameB G x s v w := by
    intro u v w
    show (G s).inner x (u + v) w = (G s).inner x u w + (G s).inner x v w
    rw [map_add, add_apply]
  have hsmul₁ : ∀ (c : ℝ) (u w : TangentSpace I x),
      frameB G x s (c • u) w = c * frameB G x s u w := by
    intro c u w
    show (G s).inner x (c • u) w = c * (G s).inner x u w
    rw [map_smul, smul_apply, smul_eq_mul]
  have hadd₂ : ∀ u v w : TangentSpace I x,
      frameB G x s u (v + w) = frameB G x s u v + frameB G x s u w := by
    intro u v w
    show (G s).inner x u (v + w) = (G s).inner x u v + (G s).inner x u w
    rw [map_add]
  have hsmul₂ : ∀ (c : ℝ) (u v : TangentSpace I x),
      frameB G x s u (c • v) = c * frameB G x s u v := by
    intro c u v
    show (G s).inner x u (c • v) = c * (G s).inner x u v
    rw [map_smul, smul_eq_mul]
  have hsymm : ∀ u v : TangentSpace I x, frameB G x s u v = frameB G x s v u := by
    intro u v
    show (G s).inner x u v = (G s).inner x v u
    exact (G s).symm x u v
  have hpos : ∀ u : TangentSpace I x, u ≠ 0 → 0 < frameB G x s u u := by
    intro u hu0
    show 0 < (G s).inner x u u
    exact (G s).pos x u hu0
  have hind : LinearIndependent ℝ (onFrame (G t) x) :=
    linearIndependent_of_isONFrame (G t) x _ (isONFrame_onFrame (G t) x)
  exact gs_isON_of_posDef (frameB G x s) (onFrame (G t) x)
    hadd₁ hsmul₁ hadd₂ hsmul₂ hsymm hpos hind

set_option maxHeartbeats 1600000 in
/-- **The Gram–Schmidt family of a Ricci flow is differentiable in time at `t`**, with derivative
the explicit Uhlenbeck derivative `frameEdot`. -/
theorem uniformBound_hasDerivWithinAt_frameFamily
    (hflow : IsRicciFlow G T) {t : ℝ} (ht : t ∈ Set.Ico 0 T) (x : M)
    (hnt : 0 < Module.finrank ℝ E) :
    ∀ i : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s : ℝ => frameFamily G t x s i) (frameEdot G t x i)
        (Set.Ico 0 T) t := by
  classical
  have hagree : ∀ i : Fin (Module.finrank ℝ E), frameFamily G t x t i = onFrame (G t) x i :=
    fun i => congrFun (frameFamily_at_t G t x) i
  have key : ∀ i : Fin (Module.finrank ℝ E),
      (∀ j, j.val < i.val → HasDerivWithinAt (fun s : ℝ => frameFamily G t x s j)
          (frameEdot G t x j) (Set.Ico 0 T) t) →
      HasDerivWithinAt (fun s : ℝ => frameFamily G t x s i) (frameEdot G t x i) (Set.Ico 0 T) t := by
    intro i ih
    set D1 : Fin (Module.finrank ℝ E) → ℝ := fun j =>
      -2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (frameFamily G t x t j)
        + frameB G x t (onFrame (G t) x i) (frameEdot G t x j) with hD1def
    set UDot : TangentSpace I x := -(∑ j : Fin (Module.finrank ℝ E),
        (if j.val < i.val then
          frameB G x t (onFrame (G t) x i) (frameFamily G t x t j) • (frameEdot G t x j)
            + (D1 j) • (frameFamily G t x t j)
        else 0)) with hUDotdef
    have hD1d : ∀ j, j.val < i.val →
        HasDerivWithinAt (fun s => frameB G x s (onFrame (G t) x i) (frameFamily G t x s j))
          (D1 j) (Set.Ico 0 T) t := by
      intro j hj
      have h := uniformBound_pairing_const_fst (G := G) (T := T) hflow t ht x
        (onFrame (G t) x i) hnt (ih j hj)
      rw [hD1def]
      exact h
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        HasDerivWithinAt (fun s => (if j.val < i.val then
            frameB G x s (onFrame (G t) x i) (frameFamily G t x s j) • (frameFamily G t x s j)
          else 0))
          (if j.val < i.val then
            frameB G x t (onFrame (G t) x i) (frameFamily G t x t j) • (frameEdot G t x j)
              + (D1 j) • (frameFamily G t x t j)
          else 0) (Set.Ico 0 T) t := by
      intro j _
      by_cases hj : j.val < i.val
      · simp only [ite_eq_left hj]
        exact (hD1d j hj).smul (ih j hj)
      · simp only [ite_eq_right hj]
        exact hasDerivWithinAt_const t (Set.Ico 0 T) (0 : TangentSpace I x)
    have hsum' : HasDerivWithinAt (fun s => ∑ j : Fin (Module.finrank ℝ E),
        (if j.val < i.val then
          frameB G x s (onFrame (G t) x i) (frameFamily G t x s j) • (frameFamily G t x s j)
        else 0))
        (∑ j : Fin (Module.finrank ℝ E),
          (if j.val < i.val then
            frameB G x t (onFrame (G t) x i) (frameFamily G t x t j) • (frameEdot G t x j)
              + (D1 j) • (frameFamily G t x t j)
          else 0)) (Set.Ico 0 T) t :=
      HasDerivWithinAt.fun_sum hterm
    have hfun : (fun s => frameU G t x s i) =
        fun s => onFrame (G t) x i - ∑ j : Fin (Module.finrank ℝ E),
          (if j.val < i.val then
            frameB G x s (onFrame (G t) x i) (frameFamily G t x s j) • (frameFamily G t x s j)
          else 0) := by
      funext s
      rw [frameU, gsU]
      try rfl
    have hU : HasDerivWithinAt (fun s => frameU G t x s i) UDot (Set.Ico 0 T) t := by
      have h0 := (hasDerivWithinAt_const t (Set.Ico 0 T) (onFrame (G t) x i)).sub hsum'
      rw [hUDotdef]
      have h2 := h0.congr_deriv (by rw [zero_sub])
      exact h2.congr (fun s _ => congrFun hfun s) (congrFun hfun t)
    have hD1val : ∀ j, j.val < i.val → D1 j
        = -2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j) := by
      intro j hj
      rw [hD1def]
      beta_reduce
      rw [hagree j,
        show frameB G x t (onFrame (G t) x i) (frameEdot G t x j) = 0 from
          uniformBound_frameB_onFrame_frameEdot_eq_zero (G := G) x hj,
        add_zero]
    have hUDotval : UDot = ∑ j : Fin (Module.finrank ℝ E),
        (if j.val < i.val then
          (2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j)) • (onFrame (G t) x j)
        else 0) := by
      have h1 : (∑ j : Fin (Module.finrank ℝ E), (if j.val < i.val then
            frameB G x t (onFrame (G t) x i) (frameFamily G t x t j) • (frameEdot G t x j)
              + (D1 j) • (frameFamily G t x t j) else 0))
          = ∑ j : Fin (Module.finrank ℝ E), (if j.val < i.val then
              -((2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                • (onFrame (G t) x j)) else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j.val < i.val
        · rw [ite_eq_left hj, ite_eq_left hj, hD1val j hj, hagree j]
          rw [show frameB G x t (onFrame (G t) x i) (onFrame (G t) x j) = 0 from
              uniformBound_frameB_onFrame_eq_zero (G := G) x (Fin.ne_of_val_ne (by omega)),
            zero_smul, zero_add]
          rw [show (-2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                • (onFrame (G t) x j)
              = -((2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                • (onFrame (G t) x j)) from by
            rw [neg_mul, neg_smul]]
        · rw [ite_eq_right hj, ite_eq_right hj]
      calc UDot = -(∑ j : Fin (Module.finrank ℝ E), (if j.val < i.val then
              -((2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                • (onFrame (G t) x j)) else 0)) := by
            rw [hUDotdef, h1]
        _ = -(-(∑ j : Fin (Module.finrank ℝ E), (if j.val < i.val then
              (2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                • (onFrame (G t) x j) else 0))) := by
            congr 1
            rw [show (∑ j : Fin (Module.finrank ℝ E), (if j.val < i.val then
                  -((2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                    • (onFrame (G t) x j)) else 0))
                = ∑ j : Fin (Module.finrank ℝ E), -(if j.val < i.val then
                  (2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                    • (onFrame (G t) x j) else 0) from
              Finset.sum_congr rfl (fun j _ => by by_cases hj : j.val < i.val <;> simp [hj])]
            rw [Finset.sum_neg_distrib]
        _ = ∑ j : Fin (Module.finrank ℝ E), (if j.val < i.val then
              (2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x j))
                • (onFrame (G t) x j) else 0) := by
            rw [neg_neg]
    have hz2 : frameB G x t (onFrame (G t) x i) UDot = 0 := by
      rw [frameB, hUDotdef, map_neg, map_sum, neg_eq_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j.val < i.val
      · rw [ite_eq_left hj, map_add, map_smul, map_smul]
        rw [show (G t).inner x (onFrame (G t) x i) (frameEdot G t x j) = 0 from by
              rw [← frameB]; exact uniformBound_frameB_onFrame_frameEdot_eq_zero (G := G) x hj]
        rw [show (G t).inner x (onFrame (G t) x i) (frameFamily G t x t j) = 0 from by
              rw [hagree j, ← frameB]
              exact uniformBound_frameB_onFrame_eq_zero (G := G) x (Fin.ne_of_val_ne (by omega))]
        simp only [smul_zero, add_zero]
      · rw [ite_eq_right hj]
        exact map_zero _
    have hz1 : frameB G x t UDot (onFrame (G t) x i) = 0 := by
      rw [show frameB G x t UDot (onFrame (G t) x i) = frameB G x t (onFrame (G t) x i) UDot from by
            rw [frameB, frameB, (G t).symm x UDot (onFrame (G t) x i)]]
      exact hz2
    set G1 : ℝ := -2 * ricAt (lcOf (G t)) x (frameU G t x t i) (frameU G t x t i)
      + frameB G x t UDot (frameU G t x t i) + frameB G x t (frameU G t x t i) UDot with hG1def
    have hG1d : HasDerivWithinAt (fun s => frameB G x s (frameU G t x s i) (frameU G t x s i))
        G1 (Set.Ico 0 T) t := by
      have h := uniformBound_pairing_self (G := G) (T := T) hflow t ht x hnt hU
      rw [hG1def]
      exact h
    have hUval : frameU G t x t i = onFrame (G t) x i := frameU_at_t (G := G) t x i
    have hunit : frameB G x t (frameU G t x t i) (frameU G t x t i) = 1 := by
      rw [hUval]; exact uniformBound_frameB_onFrame_self (G := G) x i
    have hG1val : G1 = -2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x i) := by
      rw [hG1def, hUval, hz2, hz1, add_zero, add_zero]
    have hsqrt : Real.sqrt (frameB G x t (frameU G t x t i) (frameU G t x t i)) = 1 := by
      rw [hunit, Real.sqrt_one]
    have hne : Real.sqrt (frameB G x t (frameU G t x t i) (frameU G t x t i)) ≠ 0 := by
      rw [hsqrt]; norm_num
    have hsqrtd := hG1d.sqrt (by rw [hunit]; norm_num)
    have hinvd := hsqrtd.inv hne
    have hprod := hinvd.smul hU
    have hcoef : -((-2 * ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x i)) / (2 * 1)) / 1 ^ 2
        = ricAt (lcOf (G t)) x (onFrame (G t) x i) (onFrame (G t) x i) := by ring
    have hval : ((Real.sqrt (frameB G x t (frameU G t x t i) (frameU G t x t i)))⁻¹ • UDot
          + (-(G1 / (2 * Real.sqrt (frameB G x t (frameU G t x t i) (frameU G t x t i))))
              / (Real.sqrt (frameB G x t (frameU G t x t i) (frameU G t x t i))) ^ 2)
            • (frameU G t x t i)) = frameEdot G t x i := by
      rw [hsqrt, hG1val, hcoef, hUval, hUDotval, uniformBound_frameEdot_expand,
        inv_one, one_smul, add_comm]
    have hmain : HasDerivWithinAt (fun s => frameFamily G t x s i) (frameEdot G t x i)
        (Set.Ico 0 T) t := by
      have hcongr := hprod.congr (fun s _ => frameFamily_eq G t x s i) (frameFamily_eq G t x t i)
      exact hcongr.congr_deriv hval
    exact hmain
  exact WellFounded.fix (InvImage.wf (fun i : Fin (Module.finrank ℝ E) => i.val) wellFounded_lt) key

/-- **A family of orthonormal frames along a Ricci flow with a *uniform* bound on its velocity.**

There is a universal constant `K` such that for every Ricci flow `G` on `[0,T)`, every
`t ∈ [0,T)` and every `x : M` there is a family of frames `e s` at `x`, orthonormal for `G s` for
`s` near `t` inside the flow interval, differentiable at `t` and with
`|∂ₛ eᵢ|²_{G t} ≤ K |Rm(G t)|²`.

The point (as opposed to `exists_ON_frame_family`) is that `K` does not depend on `t` or `x`: this
is what makes the final constant in `Work.Diff.GE.evol_drm_normsq` universal.  It is achieved by
Gram–Schmidt (in the metric `G s`) *of the frame `onFrame (G t) x`*, which is orthonormal at `s = t`
with Gram matrix the identity, so that the derivative of the frame is a universal multiple of `Ric`
and hence of `Rm`. -/
theorem exists_ON_frame_family_uniformBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
          (edot : Fin (Module.finrank ℝ E) → TangentSpace I x),
          (∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) ∧
          (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) ∧
          (∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x) := by
  classical
  refine ⟨4 * (Module.finrank ℝ E : ℝ) ^ 3, by positivity, ?_⟩
  intro G T hflow t ht x
  by_cases hnt : 0 < Module.finrank ℝ E
  · refine ⟨frameFamily G t x, frameEdot G t x, ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun s => uniformBound_isONFrame_frameFamily G t s x
    · exact uniformBound_hasDerivWithinAt_frameFamily (G := G) (T := T) hflow ht x hnt
    · intro i
      exact uniformBound_frameEdot_inner_le (Work.EXT.lcSmooth_noBoundary (I := I) (M := M)) G t x i
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hnt
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    refine ⟨fun _ _ => 0, fun _ => 0, ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun s => by intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i

end Work.Diff.GE
