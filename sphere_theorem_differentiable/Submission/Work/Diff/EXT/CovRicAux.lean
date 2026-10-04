import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.Evol.RicDeriv
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.RL.covRm_linear_fst
import Submission.Work.Diff.GE.covRxn.dRmArr_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|∇Ric| ≤ n |∇Rm| |v| |a| |b|`

In a `g`-orthonormal frame `e`, `(∇_v Ric)(a,b) = ∑_m (∇_v Rm)(e_m, a, e_m, b)` (hypothesis
`hsum`).  Expanding `a` and `b` in the frame and applying Cauchy–Schwarz bounds `|∇Ric|` by
`|∇Rm| |v| |a| |b|` with a constant depending only on the dimension.
-/

set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Elementary tools -/

/-- **Parseval's identity**, squared form, in an orthonormal frame. -/
theorem parseval_sq_frame (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) : ∑ i, (g.inner x v (e i)) ^ 2 = g.inner x v v := by
  have hexp := Work.Diff.GE.sum_smul_inner_eq_self (I := I) (M := M) g x hn e he v
  have h2 : g.inner x v (∑ i, g.inner x v (e i) • e i)
      = ∑ i, g.inner x v (e i) * g.inner x v (e i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have h3 : g.inner x v v = g.inner x v (∑ i, g.inner x v (e i) • e i) := by rw [hexp]
  refine (show g.inner x v v = ∑ i, (g.inner x v (e i)) ^ 2 from ?_).symm
  rw [h3, h2]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Chain rule shape of Cauchy–Schwarz with a flat vector: `(∑ x)² ≤ n ∑ x²`. -/
theorem sq_sum_le_card_mul {n : ℕ} (z : Fin n → ℝ) :
    (∑ m, z m) ^ 2 ≤ (n : ℝ) * ∑ m, (z m) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ)) z
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_mul, one_pow] using h

/-- **Cauchy–Schwarz for a three-index product.** -/
theorem abs_sum3_mul_le (n : ℕ) (α β : Fin n → ℝ) (R : Fin n → Fin n → Fin n → ℝ) :
    |∑ m, ∑ i, ∑ j, α i * β j * R m i j|
      ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (α i) ^ 2) * Real.sqrt (∑ j, (β j) ^ 2)
        * Real.sqrt (∑ m, ∑ i, ∑ j, (R m i j) ^ 2) := by
  have hA : 0 ≤ ∑ i, (α i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ j, (β j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hD : 0 ≤ ∑ m, ∑ i, ∑ j, (R m i j) ^ 2 :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- reorganise as a sum over `i` of `α i` times the trace in `(m,j)`
  have hre : (∑ m, ∑ i, ∑ j, α i * β j * R m i j)
      = ∑ i, α i * (∑ m, ∑ j, β j * R m i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- Cauchy-Schwarz in `i`
  have h1 : (∑ i, α i * (∑ m, ∑ j, β j * R m i j)) ^ 2
      ≤ (∑ i, (α i) ^ 2) * (∑ i, (∑ m, ∑ j, β j * R m i j) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ α _
  -- Cauchy-Schwarz in `j` and in `m`, for each `i`
  have h2 : ∀ i, (∑ m, ∑ j, β j * R m i j) ^ 2
      ≤ ((n : ℝ) * (∑ j, (β j) ^ 2)) * (∑ m, ∑ j, (R m i j) ^ 2) := by
    intro i
    have hswap : (∑ m, ∑ j, β j * R m i j) = ∑ j, β j * (∑ m, R m i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    rw [hswap]
    have hj := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ β (fun j => ∑ m, R m i j)
    have hm : ∀ j, (∑ m, R m i j) ^ 2 ≤ (n : ℝ) * ∑ m, (R m i j) ^ 2 := fun j => sq_sum_le_card_mul _
    have hm2 : (∑ j, (∑ m, R m i j) ^ 2) ≤ (n : ℝ) * (∑ j, ∑ m, (R m i j) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hm j
    have hswap2 : (∑ j, ∑ m, (R m i j) ^ 2) = ∑ m, ∑ j, (R m i j) ^ 2 := Finset.sum_comm ..
    calc (∑ j, β j * (∑ m, R m i j)) ^ 2
        ≤ (∑ j, (β j) ^ 2) * (∑ j, (∑ m, R m i j) ^ 2) := hj
      _ ≤ (∑ j, (β j) ^ 2) * ((n : ℝ) * (∑ j, ∑ m, (R m i j) ^ 2)) :=
          mul_le_mul_of_nonneg_left hm2 hB
      _ = ((n : ℝ) * (∑ j, (β j) ^ 2)) * (∑ m, ∑ j, (R m i j) ^ 2) := by rw [hswap2]; ring
  have h3 : (∑ i, (∑ m, ∑ j, β j * R m i j) ^ 2)
      ≤ ((n : ℝ) * (∑ j, (β j) ^ 2)) * (∑ i, ∑ m, ∑ j, (R m i j) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => h2 i
  -- combine
  have hmain : (∑ m, ∑ i, ∑ j, α i * β j * R m i j) ^ 2
      ≤ (∑ i, (α i) ^ 2) * (((n : ℝ) * (∑ j, (β j) ^ 2))
          * (∑ m, ∑ i, ∑ j, (R m i j) ^ 2)) := by
    rw [hre]
    calc (∑ i, α i * (∑ m, ∑ j, β j * R m i j)) ^ 2
        ≤ (∑ i, (α i) ^ 2) * (∑ i, (∑ m, ∑ j, β j * R m i j) ^ 2) := h1
      _ ≤ (∑ i, (α i) ^ 2) * (((n : ℝ) * (∑ j, (β j) ^ 2))
            * (∑ i, ∑ m, ∑ j, (R m i j) ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 hA
      _ = (∑ i, (α i) ^ 2) * (((n : ℝ) * (∑ j, (β j) ^ 2))
            * (∑ m, ∑ i, ∑ j, (R m i j) ^ 2)) := by
          rw [Finset.sum_comm]
  have habs : |∑ m, ∑ i, ∑ j, α i * β j * R m i j|
      = Real.sqrt ((∑ m, ∑ i, ∑ j, α i * β j * R m i j) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs]
  have h1' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfinal : Real.sqrt ((∑ i, (α i) ^ 2) * (((n : ℝ) * (∑ j, (β j) ^ 2))
        * (∑ m, ∑ i, ∑ j, (R m i j) ^ 2)))
      = Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (α i) ^ 2) * Real.sqrt (∑ j, (β j) ^ 2)
        * Real.sqrt (∑ m, ∑ i, ∑ j, (R m i j) ^ 2) := by
    rw [Real.sqrt_mul hA, Real.sqrt_mul (mul_nonneg h1' hB), Real.sqrt_mul h1']
    ring
  exact le_trans (Real.sqrt_le_sqrt hmain) (le_of_eq hfinal)

/-- Finset form of the linearity of `∇Rm` in its third argument. -/
theorem covRm_sum_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) (v a c' d : TangentSpace I x) :
    covRm g x v a (∑ i ∈ s, c i • u i) c' d = ∑ i ∈ s, c i * covRm g x v a (u i) c' d := by
  classical
  have hlin := Work.Diff.GE.covRm_linear_thd (I := I) (M := M) hLC g x
  induction s using Finset.induction_on with
  | empty =>
      have h0 : covRm g x v a (0 : TangentSpace I x) c' d = 0 := by
        have h := hlin v a 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x) c' d
        simpa using h
      simpa using h0
  | insert i s hi ih =>
      have h := hlin v a (c i) 1 (u i) (∑ j ∈ s, c j • u j) c' d
      rw [one_smul] at h
      rw [Finset.sum_insert hi, h, ih, Finset.sum_insert hi, one_mul]

/-- Finset form of the linearity of `∇Rm` in its fifth argument. -/
theorem covRm_sum_fith (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) (v a b c' : TangentSpace I x) :
    covRm g x v a b c' (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * covRm g x v a b c' (u i) := by
  classical
  have hlin := Work.Diff.GE.Kato3.covRm_linear_fith (I := I) (M := M) hLC g x
  induction s using Finset.induction_on with
  | empty =>
      have h0 : covRm g x v a b c' (0 : TangentSpace I x) = 0 := by
        have h := hlin v a b c' 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x)
        simpa using h
      simpa using h0
  | insert i s hi ih =>
      have h := hlin v a b c' (c i) 1 (u i) (∑ j ∈ s, c j • u j)
      rw [one_smul] at h
      rw [Finset.sum_insert hi, h, ih, Finset.sum_insert hi, one_mul]

/-- **The `∇Ric` bound.**  From the trace identity `hsum`,
`|(∇_v Ric)(a,b)| ≤ n √|∇Rm|² √⟪v,v⟫ √⟪a,a⟫ √⟪b,b⟫`. -/
theorem covRic_bound_of_trace
    (hLC : LCSmooth I M)
    (hsum : ∀ (g : SMet I M) (x : M) (v a b : TangentSpace I x),
      Work.Diff.Evol.covRic g x v a b
        = ∑ m, covRm g x v (onFrame g x m) a (onFrame g x m) b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SMet I M) (x : M) (v a b : TangentSpace I x),
      |Work.Diff.Evol.covRic g x v a b| ≤ C * Real.sqrt (dRmNormSq g x)
        * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
  classical
  refine ⟨(Module.finrank ℝ E : ℝ), Nat.cast_nonneg _, ?_⟩
  intro g x v a b
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := onFrame g x with hedef
  set F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E)
      → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b c d => (covRm g x v (e a) (e b) (e c) (e d)) ^ 2 with hFdef
  by_cases hn : 0 < Module.finrank ℝ E
  · have he : IsONFrame g x e := by
      rw [hedef]; exact Work.Diff.GE.isONFrame_onFrame g x
    have hexpa : ∑ i, g.inner x a (e i) • e i = a := by
      rw [hedef]
      exact Work.Diff.GE.sum_smul_inner_eq_self g x hn _ (Work.Diff.GE.isONFrame_onFrame g x) a
    have hexpb : ∑ j, g.inner x b (e j) • e j = b := by
      rw [hedef]
      exact Work.Diff.GE.sum_smul_inner_eq_self g x hn _ (Work.Diff.GE.isONFrame_onFrame g x) b
    have hAa : ∑ i, (g.inner x a (e i)) ^ 2 = g.inner x a a :=
      parseval_sq_frame (I := I) (M := M) g x hn e he a
    have hBb : ∑ j, (g.inner x b (e j)) ^ 2 = g.inner x b b :=
      parseval_sq_frame (I := I) (M := M) g x hn e he b
    -- the trace identity, expanded in the frame
    have htrace : Work.Diff.Evol.covRic g x v a b
        = ∑ m, ∑ i, ∑ j, g.inner x a (e i) * g.inner x b (e j)
            * covRm g x v (e m) (e i) (e m) (e j) := by
      rw [hsum g x v a b]
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [← hexpa]
      rw [covRm_sum_thd (I := I) (M := M) hLC g x Finset.univ (fun i => g.inner x a (e i)) e
          v (e m) (e m) b]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_lhs => rw [← hexpb]
      rw [covRm_sum_fith (I := I) (M := M) hLC g x Finset.univ (fun j => g.inner x b (e j)) e
          v (e m) (e i) (e m)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    -- Cauchy-Schwarz
    have hcs := abs_sum3_mul_le (Module.finrank ℝ E) (fun i => g.inner x a (e i))
      (fun j => g.inner x b (e j)) (fun m i j => covRm g x v (e m) (e i) (e m) (e j))
    -- the diagonal bound
    have hdiag : (∑ m, ∑ i, ∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2)
        ≤ (Module.finrank ℝ E : ℝ) * ∑ a₁, ∑ b₁, ∑ c₁, ∑ d₁, F a₁ b₁ c₁ d₁ := by
      have hstep : ∀ m i, (∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2)
          ≤ (Module.finrank ℝ E : ℝ) * (∑ c, ∑ d, F m i c d) := by
        intro m i
        have h1 : ∀ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2 ≤ ∑ c, ∑ d, F m i c d := by
          intro j
          show F m i m j ≤ ∑ c, ∑ d, F m i c d
          calc F m i m j ≤ ∑ d, F m i m d :=
                Finset.single_le_sum (f := fun d => F m i m d) (fun d _ => sq_nonneg _)
                  (Finset.mem_univ j)
            _ ≤ ∑ c, ∑ d, F m i c d :=
                Finset.single_le_sum (f := fun c => ∑ d, F m i c d)
                  (fun c _ => Finset.sum_nonneg fun d _ => sq_nonneg _) (Finset.mem_univ m)
        calc (∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2)
            = ∑ j, F m i m j := rfl
          _ ≤ ∑ j, (∑ c, ∑ d, F m i c d) := Finset.sum_le_sum fun j _ => h1 j
          _ = (Module.finrank ℝ E : ℝ) * (∑ c, ∑ d, F m i c d) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (∑ m, ∑ i, ∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2)
          = ∑ m, ∑ i, ∑ j, F m i m j := rfl
        _ ≤ ∑ m, ∑ i, (Module.finrank ℝ E : ℝ) * (∑ c, ∑ d, F m i c d) :=
            Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i _ => hstep m i
        _ = (Module.finrank ℝ E : ℝ) * ∑ a₁, ∑ b₁, ∑ c₁, ∑ d₁, F a₁ b₁ c₁ d₁ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
    -- `√|∇Rm|² ≤ √⟪v,v⟫ √dRmNormSq`
    have hD4 : Real.sqrt (∑ a₁, ∑ b₁, ∑ c₁, ∑ d₁, F a₁ b₁ c₁ d₁)
        ≤ Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) := by
      have h : Real.sqrt (∑ a₁, ∑ b₁, ∑ c₁, ∑ d₁,
          (covRm g x v (e a₁) (e b₁) (e c₁) (e d₁)) ^ 2)
          ≤ Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) :=
        Work.Diff.GE.covRxn.dRmArr_norm_le_t2 (I := I) (M := M) hLC g x v
      simpa [hFdef] using h
    -- combine
    have hLHS : |Work.Diff.Evol.covRic g x v a b|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (∑ i, (g.inner x a (e i)) ^ 2)
          * Real.sqrt (∑ j, (g.inner x b (e j)) ^ 2)
          * Real.sqrt (∑ m, ∑ i, ∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2) := by
      rw [htrace]; exact hcs
    have hD3 : Real.sqrt (∑ m, ∑ i, ∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2)
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x)) := by
      calc Real.sqrt (∑ m, ∑ i, ∑ j, (covRm g x v (e m) (e i) (e m) (e j)) ^ 2)
          ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) * ∑ a₁, ∑ b₁, ∑ c₁, ∑ d₁, F a₁ b₁ c₁ d₁) :=
            Real.sqrt_le_sqrt hdiag
        _ = Real.sqrt (Module.finrank ℝ E : ℝ)
              * Real.sqrt (∑ a₁, ∑ b₁, ∑ c₁, ∑ d₁, F a₁ b₁ c₁ d₁) :=
            Real.sqrt_mul (Nat.cast_nonneg _) _
        _ ≤ Real.sqrt (Module.finrank ℝ E : ℝ)
              * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x)) :=
            mul_le_mul_of_nonneg_left hD4 (Real.sqrt_nonneg _)
    refine le_trans hLHS ?_
    refine le_trans (mul_le_mul_of_nonneg_left hD3 (by positivity)) ?_
    rw [hAa, hBb]
    have hs : Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (Module.finrank ℝ E : ℝ)
        = (Module.finrank ℝ E : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
    refine le_of_eq ?_
    calc Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b)
          * (Real.sqrt (Module.finrank ℝ E : ℝ)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x)))
        = (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (Module.finrank ℝ E : ℝ))
          * Real.sqrt (dRmNormSq g x) * Real.sqrt (g.inner x v v)
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by ring
      _ = (Module.finrank ℝ E : ℝ) * Real.sqrt (dRmNormSq g x) * Real.sqrt (g.inner x v v)
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by rw [hs]
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hC : (Module.finrank ℝ E : ℝ) = 0 := by rw [h0]; norm_num
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    rw [hsum g x v a b, hC]
    simp

end Work.Diff.EXT
