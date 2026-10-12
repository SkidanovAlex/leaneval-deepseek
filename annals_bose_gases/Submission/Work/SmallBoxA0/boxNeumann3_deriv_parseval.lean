import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.acube_mode_deriv_ibp_sine
import Submission.Work.SmallBoxA0.boxNeumann_deriv_parseval
import Submission.Work.SmallBoxA0.boxParseval_mixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric Set Filter
open scoped Real BigOperators Topology ContDiff
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## Rewriting the mixed modes at a specific coordinate choice -/

lemma mixedMode_decide_true {ℓ : ℝ} {p : Prop} [Decidable p] (hp : p) (k : ℕ) (x : ℝ) :
    mixedMode ℓ (decide p) k x = Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) := by
  unfold mixedMode
  rw [if_pos (by rw [decide_eq_true_eq]; exact hp)]

lemma mixedMode_decide_false {ℓ : ℝ} {p : Prop} [Decidable p] (hp : ¬p) (k : ℕ) (x : ℝ) :
    mixedMode ℓ (decide p) k x = Real.cos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) := by
  unfold mixedMode
  rw [if_neg (fun h => hp (by rw [decide_eq_true_eq] at h; exact h))]

lemma mixedWgt_decide_false {ℓ : ℝ} {p : Prop} [Decidable p] (hp : ¬p) (k : ℕ) :
    mixedWgt ℓ (decide p) k = mixedWgt ℓ false k := by
  unfold mixedWgt
  rw [if_neg (fun h => hp (by rw [decide_eq_true_eq] at h; exact h))]
  simp

lemma mixedWgt_eq_half {ℓ : ℝ} (b : Bool) {k : ℕ} (hk : k ≠ 0) : mixedWgt ℓ b k = ℓ / 2 := by
  cases b <;> simp [mixedWgt, hk]

/-- The mixed product mode with the sine slot in coordinate `m` splits into the `m`-th
sine factor times the product of the remaining cosine factors. -/
lemma prod_mixed_split {s : ℝ} (m : Fin 3) (k : Fin 3 → ℕ) (x : ℝ³) :
    (∏ i : Fin 3, mixedMode s (decide (i = m)) (k i) (x i))
      = (∏ i ∈ Finset.univ.erase m, boxNeumann s (k i) (x i)) *
          Real.sin (((k m : ℝ) * Real.pi / s) * (x m + s / 2)) := by
  rw [← Finset.prod_erase_mul Finset.univ
    (f := fun i => mixedMode s (decide (i = m)) (k i) (x i)) (Finset.mem_univ m)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ m := Finset.ne_of_mem_erase hi
    rw [mixedMode_decide_false (p := i = m) hne]
    rfl
  · rw [mixedMode_decide_true (p := m = m) rfl]

/-! ## The `ℝ³` form of the mixed Parseval -/

theorem acube_parseval_mixed {s : ℝ} (hs : 0 < s) (ε : Fin 3 → Bool) {F : ℝ³ → ℝ}
    (hF : Continuous F) :
    HasSum (fun k : Fin 3 → ℕ =>
        (∫ x in acube s, F x * ∏ i : Fin 3, mixedMode s (ε i) (k i) (x i)) ^ 2
          / ∏ i : Fin 3, mixedWgt s (ε i) (k i))
      (∫ x in acube s, (F x) ^ 2) := by
  have hmp : MeasurePreserving (⇑cgEuc3)
      ((volume : Measure (Fin 3 → ℝ)).restrict (acubeF s))
      ((volume : Measure ℝ³).restrict (acube s)) :=
    ⟨cgEuc3.measurable, by rw [← acube_restrict_eq_map s]⟩
  have hemb : MeasurableEmbedding (⇑cgEuc3) := cgEuc3.measurableEmbedding
  have hset : Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(s / 2)) (s / 2)) = acubeF s := by
    have h1 : (-(s / 2) : ℝ) = -s / 2 := by ring
    rw [h1, acubeF_eq_pi s]
  have hcont : Continuous (fun y : Fin 3 → ℝ => F (cgEuc3 y)) :=
    hF.comp (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm.continuous
  have hbase := boxParseval_mixed 3 s hs ε (fun y : Fin 3 → ℝ => F (cgEuc3 y)) hcont
  rw [hset] at hbase
  have hL : (∫ y in acubeF s, (F (cgEuc3 y)) ^ 2) = ∫ x in acube s, (F x) ^ 2 :=
    hmp.integral_comp hemb (fun x : ℝ³ => (F x) ^ 2)
  have hk : ∀ k : Fin 3 → ℕ,
      (∫ y in acubeF s, F (cgEuc3 y) * ∏ i : Fin 3, mixedMode s (ε i) (k i) (y i))
        = ∫ x in acube s, F x * ∏ i : Fin 3, mixedMode s (ε i) (k i) (x i) := by
    intro k
    have h1 := hmp.integral_comp hemb
      (fun x : ℝ³ => F x * ∏ i : Fin 3, mixedMode s (ε i) (k i) (x i))
    simpa only [cgEuc3, MeasurableEquiv.coe_toLp, WithLp.ofLp_toLp] using h1
  rw [← hL]
  refine hbase.congr_fun (fun k => ?_)
  rw [hk k]

/-! ## The target: the `boxNeumann3` derivative (Dirichlet-form) Parseval identity -/

lemma boxNeumann3_deriv_parseval {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ} (hg : ContDiff ℝ 2 g) :
    (∫ x in acube s, ∑ m : Fin 3, (fderiv ℝ g x (kcStdBasis m)) ^ 2)
      = ∑' k : Fin 3 → ℕ, (∑ m : Fin 3, ((k m : ℝ) * π / s) ^ 2) *
          ((∏ m : Fin 3, (if k m = 0 then 1 / s else 2 / s)) *
            (∫ x in acube s, g x * boxNeumann3 s k x) ^ 2) := by
  classical
  have hdf : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hcont : ∀ m : Fin 3, Continuous (fun x : ℝ³ => fderiv ℝ g x (kcStdBasis m)) :=
    fun m => hdf.clm_apply continuous_const
  have hK : IsCompact (acube s) := acube_compact hs
  set c : (Fin 3 → ℕ) → ℝ := fun k => ∫ x in acube s, g x * boxNeumann3 s k x with hc
  set N : (Fin 3 → ℕ) → ℝ := fun k => ∏ i : Fin 3, mixedWgt s false (k i) with hN
  set d : Fin 3 → (Fin 3 → ℕ) → ℝ :=
    fun m k => ((k m : ℝ) * π / s) ^ 2 * (c k ^ 2 / N k) with hd
  -- the Fourier coefficient of `∂_m g` against the mixed mode
  have hcoeff : ∀ (m : Fin 3) (k : Fin 3 → ℕ),
      (∫ x in acube s, fderiv ℝ g x (kcStdBasis m) *
          ∏ i : Fin 3, mixedMode s (decide (i = m)) (k i) (x i))
        = -(((k m : ℝ) * π / s)) * c k := by
    intro m k
    rw [hc]
    rw [integral_congr_ae (Eventually.of_forall (fun x => by rw [prod_mixed_split m k]))]
    exact acube_mode_deriv_ibp_sine hs m k hg
  -- the weight of the `m`-th mixed Parseval equals the full cosine weight when `k m ≠ 0`
  have hW : ∀ (m : Fin 3) (k : Fin 3 → ℕ), k m ≠ 0 →
      (∏ i : Fin 3, mixedWgt s (decide (i = m)) (k i)) = N k := by
    intro m k hkm
    rw [hN]
    simp only
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = m
    · rw [hi]
      rw [mixedWgt_eq_half (decide (m = m)) hkm, mixedWgt_eq_half false hkm]
    · exact mixedWgt_decide_false (ℓ := s) (p := i = m) hi (k i)
  -- each `∫ (∂_m g)²` is the corresponding `d m`-series
  have hsum_m : ∀ m : Fin 3,
      HasSum (d m) (∫ x in acube s, (fderiv ℝ g x (kcStdBasis m)) ^ 2) := by
    intro m
    have hbase := acube_parseval_mixed (s := s) hs (fun i : Fin 3 => decide (i = m))
      (F := fun x : ℝ³ => fderiv ℝ g x (kcStdBasis m)) (hcont m)
    refine hbase.congr_fun (fun k => ?_)
    simp only [hd]
    rw [hcoeff m k]
    by_cases hkm : k m = 0
    · have hA : ((k m : ℝ) * π / s) = 0 := by rw [hkm]; simp
      rw [hA]
      simp
    · rw [hW m k hkm]
      ring
  have hsm : ∀ m : Fin 3, Summable (d m) := fun m => (hsum_m m).summable
  have hLHS : (∫ x in acube s, ∑ m : Fin 3, (fderiv ℝ g x (kcStdBasis m)) ^ 2)
      = ∑ m : Fin 3, ∫ x in acube s, (fderiv ℝ g x (kcStdBasis m)) ^ 2 := by
    rw [integral_finsetSum]
    intro m _
    exact ContinuousOn.integrableOn_compact hK ((hcont m).pow 2).continuousOn
  have hswap : (∑ m : Fin 3, ∑' k, d m k) = ∑' k, ∑ m : Fin 3, d m k := by
    have h0 : Summable (d 0) := hsm 0
    have h1 : Summable (d 1) := hsm 1
    have h2 : Summable (d 2) := hsm 2
    have h12 : (∑' k, (d 1 k + d 2 k)) = ∑' k, d 1 k + ∑' k, d 2 k :=
      Summable.tsum_add h1 h2
    have hall : (∑' k, (d 0 k + (d 1 k + d 2 k)))
        = ∑' k, d 0 k + ∑' k, (d 1 k + d 2 k) := Summable.tsum_add h0 (h1.add h2)
    rw [Fin.sum_univ_three, add_assoc, ← h12, ← hall]
    apply tsum_congr
    intro k
    rw [Fin.sum_univ_three]
    ring
  have hNinv : ∀ k : Fin 3 → ℕ,
      (∏ i : Fin 3, (if k i = 0 then (1 : ℝ) / s else 2 / s))
        = (∏ i : Fin 3, mixedWgt s false (k i))⁻¹ := by
    intro k
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [inv_mixedWgt]
    simp
  rw [hLHS]
  calc ∑ m : Fin 3, ∫ x in acube s, (fderiv ℝ g x (kcStdBasis m)) ^ 2
      = ∑ m : Fin 3, ∑' k, d m k := by
        apply Finset.sum_congr rfl
        intro m _
        exact ((hsum_m m).tsum_eq).symm
    _ = ∑' k, ∑ m : Fin 3, d m k := hswap
    _ = ∑' k : Fin 3 → ℕ, (∑ m : Fin 3, ((k m : ℝ) * π / s) ^ 2) *
          ((∏ m : Fin 3, (if k m = 0 then 1 / s else 2 / s)) *
            (∫ x in acube s, g x * boxNeumann3 s k x) ^ 2) := by
        apply tsum_congr
        intro k
        simp only [hd, hc, hN]
        rw [← Finset.sum_mul, hNinv k, div_eq_inv_mul]

end Work.SmallBoxA0
