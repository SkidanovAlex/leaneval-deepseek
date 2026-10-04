import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Helper lemmas for the moving-frame derivative of the curvature components

This module collects the (proved) elementary facts used to differentiate
`s ↦ rmP (G s) x (a s) (b s) (c s) (d s)`, where `rmP g x a b c d = g(R(a,b)d, c)` is the
frozen curvature-component definition of `Submission.Diff.Grad`.

Nothing here is `sorry`-free-by-fiat: every lemma is proved.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Finset

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Multilinearity of `rmP`, in finite-sum form -/

lemma rmP_sum_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (b c d : TangentSpace I x) :
    rmP g x (∑ i, a i • f i) b c d = ∑ i, a i * rmP g x (f i) b c d := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x v b c d
      map_add' := fun v w => Work.Diff.GE.rmP_add_fst g hLC x v w b c d
      map_smul' := fun r v => by
        rw [Work.Diff.GE.rmP_smul_fst g hLC x r v b c d]; rfl }
  have h := map_sum T (fun i => a i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma rmP_sum_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (b : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a c d : TangentSpace I x) :
    rmP g x a (∑ i, b i • f i) c d = ∑ i, b i * rmP g x a (f i) c d := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x a v c d
      map_add' := fun v w => Work.Diff.GE.rmP_add_snd g hLC x a v w c d
      map_smul' := fun r v => by
        rw [Work.Diff.GE.rmP_smul_snd g hLC x r a v c d]; rfl }
  have h := map_sum T (fun i => b i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma rmP_sum_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b d : TangentSpace I x) :
    rmP g x a b (∑ i, c i • f i) d = ∑ i, c i * rmP g x a b (f i) d := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x a b v d
      map_add' := fun v w => Work.Diff.GE.rmP_add_thd g hLC x a b v w d
      map_smul' := fun r v => by
        rw [Work.Diff.GE.rmP_smul_thd g hLC x r a b v d]; rfl }
  have h := map_sum T (fun i => c i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma rmP_sum_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (d : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c : TangentSpace I x) :
    rmP g x a b c (∑ i, d i • f i) = ∑ i, d i * rmP g x a b c (f i) := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x a b c v
      map_add' := fun v w => Work.Diff.GE.rmP_add_fth g hLC x a b c v w
      map_smul' := fun r v => by
        rw [Work.Diff.GE.rmP_smul_fth g hLC x r a b c v]; rfl }
  have h := map_sum T (fun i => d i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma rmP_expand2 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (c d : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A B : TangentSpace I x) :
    rmP g x A B (∑ r, c r • f r) (∑ u, d u • f u)
      = ∑ r, ∑ u, c r * (d u * rmP g x A B (f r) (f u)) := by
  rw [rmP_sum_thd hLC g x c f]
  apply Finset.sum_congr rfl; intro r _
  rw [rmP_sum_fth hLC g x d f, Finset.mul_sum]

lemma rmP_expand3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (b c d : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : TangentSpace I x) :
    rmP g x A (∑ q, b q • f q) (∑ r, c r • f r) (∑ u, d u • f u)
      = ∑ q, ∑ r, ∑ u, b q * (c r * (d u * rmP g x A (f q) (f r) (f u))) := by
  rw [rmP_sum_snd hLC g x b f]
  apply Finset.sum_congr rfl; intro q _
  rw [rmP_expand2 hLC g x c d f A (f q)]
  simp only [Finset.mul_sum]

lemma rmP_expand4 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    rmP g x (∑ p, a p • f p) (∑ q, b q • f q) (∑ r, c r • f r) (∑ u, d u • f u)
      = ∑ p, ∑ q, ∑ r, ∑ u,
          a p * (b q * (c r * (d u * rmP g x (f p) (f q) (f r) (f u)))) := by
  rw [rmP_sum_fst hLC g x a f]
  apply Finset.sum_congr rfl; intro p _
  rw [rmP_expand3 hLC g x b c d f (f p)]
  simp only [Finset.mul_sum]

lemma sum4_delta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j, d i j = if i = j then (1 : ℝ) else 0)
    (Dc : ι → ι → ι → ι → ℝ) (i j k l : ι) :
    ∑ p, ∑ q, ∑ r, ∑ u, d p i * (d q j * (d r k * (d u l * Dc p q r u)))
      = Dc i j k l := by
  simp only [hd]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ j) h)]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ k) h)]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ l) h)]
  simp

lemma sum3_delta_qru {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j, d i j = if i = j then (1 : ℝ) else 0)
    (c : ι → ℝ) (P : ι → ι → ι → ι → ℝ) (j k l : ι) :
    ∑ p, ∑ q, ∑ r, ∑ u, c p * (d q j * (d r k * (d u l * P p q r u)))
      = ∑ p, c p * P p j k l := by
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [hd]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ j) h)]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ k) h)]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ l) h)]
  simp

lemma sum3_delta_pru {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j, d i j = if i = j then (1 : ℝ) else 0)
    (c : ι → ℝ) (P : ι → ι → ι → ι → ℝ) (i k l : ι) :
    ∑ p, ∑ q, ∑ r, ∑ u, d p i * (c q * (d r k * (d u l * P p q r u)))
      = ∑ q, c q * P i q k l := by
  simp only [hd]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ i) h)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ k) h)]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ l) h)]
  simp

lemma sum3_delta_pqu {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j, d i j = if i = j then (1 : ℝ) else 0)
    (c : ι → ℝ) (P : ι → ι → ι → ι → ℝ) (i j l : ι) :
    ∑ p, ∑ q, ∑ r, ∑ u, d p i * (d q j * (c r * (d u l * P p q r u)))
      = ∑ r, c r * P i j r l := by
  simp only [hd]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ j) h)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ l) h)]
  simp

lemma sum3_delta_pqr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (hd : ∀ i j, d i j = if i = j then (1 : ℝ) else 0)
    (c : ι → ℝ) (P : ι → ι → ι → ι → ℝ) (i j k : ι) :
    ∑ p, ∑ q, ∑ r, ∑ u, d p i * (d q j * (d r k * (c u * P p q r u)))
      = ∑ u, c u * P i j k u := by
  simp only [hd]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ j) h)]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ k) h)]
  simp



/-- A `4`-nested sum of products, differentiated with `HasDerivAt.sum`. -/
theorem hasDerivAt_sum4 {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℝ}
    (b : ι → ι → ι → ι → ℝ → ℝ) (b' : ι → ι → ι → ι → ℝ)
    (hb : ∀ p q r u, HasDerivAt (b p q r u) (b' p q r u) t) :
    HasDerivAt (fun s => ∑ p, ∑ q, ∑ r, ∑ u, b p q r u s)
      (∑ p, ∑ q, ∑ r, ∑ u, b' p q r u) t := by
  have hraw := HasDerivAt.sum (u := Finset.univ) (fun p _ =>
      HasDerivAt.sum (u := Finset.univ) (fun q _ =>
        HasDerivAt.sum (u := Finset.univ) (fun r _ =>
          HasDerivAt.sum (u := Finset.univ) (fun u _ => hb p q r u))))
  convert hraw using 1
  funext s
  simp only [Finset.sum_apply]

/-- Derivative of `s ↦ ⟨u, X s⟩` for the (fixed) metric `G t`. -/
theorem hasDerivAt_inner_moving {G : ℝ → SMet I M} {t : ℝ} {x : M}
    {u : TangentSpace I x} {X : ℝ → E} {X' : E}
    (hX : HasDerivAt X X' t) :
    HasDerivAt (fun s => (G t).inner x u (X s)) ((G t).inner x u X') t := by
  let L : E →L[ℝ] ℝ :=
    { toFun := fun v => (G t).inner x u v
      map_add' := fun a b => map_add ((G t).inner x u) a b
      map_smul' := fun r a => map_smul ((G t).inner x u) r a }
  have h := (ContinuousLinearMap.hasFDerivAt L).comp t hX.hasFDerivAt
  refine h.hasDerivAt.congr_deriv ?_
  have h2 : (L ∘SL ContinuousLinearMap.toSpanSingleton ℝ X') 1 = L X' := by simp
  rw [h2]
  rfl

/-- Coefficient identity: `⟨f p, ∑ q, Md i q • f q⟩ = Md i p` for an orthonormal frame `f`. -/
theorem inner_frame_sum {G : ℝ → SMet I M} {t : ℝ} {x : M}
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (hon : ∀ i j, (G t).inner x (f i) (f j) = if i = j then (1 : ℝ) else 0)
    (Md : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (i p : Fin (Module.finrank ℝ E)) :
    (G t).inner x (f p) (∑ q, Md i q • f q) = Md i p := by
  rw [show (G t).inner x (f p) (∑ q, Md i q • f q)
        = ∑ q, Md i q * (G t).inner x (f p) (f q) from by
      simp only [map_sum, map_smul, smul_eq_mul]]
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [hon, Ne.symm hb])
        (fun hh => absurd (Finset.mem_univ p) hh)]
  simp [hon]

/-- Collapse of the four-nested "product-rule" sum into the target form
`Dc i j k l + ∑ p (Md i p * P p j k l + Md j p * P i p k l + Md k p * P i j p l + Md l p * P i j k p)`.
This is the bridge between the product-rule expansion of `∂ₜ` and the `Xact`-shaped correction
term of Hamilton's curvature evolution. -/
theorem collapse_bridge (d : Fin n → Fin n → ℝ)
    (hd : ∀ i j, d i j = if i = j then (1:ℝ) else 0)
    (Md : Fin n → Fin n → ℝ) (P : Fin n → Fin n → Fin n → Fin n → ℝ)
    (Dc : Fin n → Fin n → Fin n → Fin n → ℝ) (i j k l : Fin n) :
    (∑ p, ∑ q, ∑ r, ∑ u,
      (Md i p * (d q j * (d r k * (d u l * P p q r u)))
      + d p i * (Md j q * (d r k * (d u l * P p q r u))
        + d q j * (Md k r * (d u l * P p q r u) + d r k * (Md l u * P p q r u + d u l * Dc p q r u)))))
    = Dc i j k l + ∑ p, (Md i p * P p j k l + Md j p * P i p k l
        + Md k p * P i j p l + Md l p * P i j k p) := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  rw [sum3_delta_qru d hd (fun p => Md i p) P j k l]
  rw [sum3_delta_pru d hd (fun q => Md j q) P i k l]
  rw [sum3_delta_pqu d hd (fun r => Md k r) P i j l]
  rw [sum3_delta_pqr d hd (fun u => Md l u) P i j k]
  rw [sum4_delta d hd Dc i j k l]
  ring

end Work.Diff.Evol
