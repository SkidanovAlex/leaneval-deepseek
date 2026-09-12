import Mathlib
import ChallengeDeps
import Submission.Work.Dani.EscapeConvert
import Submission.Commons.Analysis.Measure.volume_bad_union_le
import Submission.Commons.Analysis.Measure.linearForm_level_volume_zero
import Submission.Commons.Analysis.Measure.measurePreserving_pi_comm
import Submission.Commons.Analysis.Measure.columns_level_volume_zero
import Submission.Commons.Analysis.Real.geom_bound_two_scale
import Submission.Commons.Analysis.ENNReal.tsum_ofReal_mul_geometric

/-!
# The measure-theoretic half of conjunct 2 (Step B: Borel–Cantelli)

`Submission.EscapeConvert` converts the geometric bad event for the plane `x = graphPlane c` at
time `t` into an *integer* diophantine event for the matrix `c` with parameters
`A ≈ e^{t(1/ℓ − ε)}`, `δ ≈ e^{−t(1/(d−ℓ)+ε)}`.  This file supplies **Step B**: the
cylinder-measure bound and Borel–Cantelli argument showing that for almost every `c` only
finitely many integer times are bad, plus (for almost every `c`) the absence of a rational point
on `graphPlane c`.

Module `Submission.Work.Dani.EscapeMeasure`, namespace `Submission.EscapeMeasure`.
-/

noncomputable section

open LinearSubspaces Module Real MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.EscapeMeasure

/-- The unit box `[0,1)^{ℓ×m}`. -/
def box (l m : ℕ) : Set (Fin l → Fin m → ℝ) := {c | ∀ i j, c i j ∈ Set.Ico (0:ℝ) 1}

/-- The uniform angle constant `√(2 + ℓm)` dominating `√(2 + cterm l c)` on the box. -/
noncomputable def angleConst (l m : ℕ) : ℝ := Real.sqrt (2 + (l : ℝ) * (m : ℝ))

/-- The coefficient bound `A_n = 2e^{(n+1)(1/ℓ−ε)}` of the integer event. -/
noncomputable def rateA (l : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  2 * Real.exp (((n : ℝ) + 1) * (1 / (l : ℝ) - ε))

/-- The accuracy `δ_n = √(2+ℓm)·e^{−n(1/(d−ℓ)+ε)}` of the integer event. -/
noncomputable def rateD (l m : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  angleConst l m * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε)))

/-- The geometric series constant `K` of the Borel–Cantelli bound. -/
noncomputable def geomK (l m : ℕ) (ε : ℝ) : ℝ :=
  5 ^ l * Real.exp (1 - (l : ℝ) * ε) * (2 * angleConst l m) ^ m

/-- The geometric series ratio `r = e^{−ε(ℓ+m)}` of the Borel–Cantelli bound. -/
noncomputable def geomR (l m : ℕ) (ε : ℝ) : ℝ := Real.exp (-(ε * ((l : ℝ) + (m : ℝ))))

/-- The integer diophantine event with coefficient bound `A` and accuracy `δ`. -/
def badEvent (l m : ℕ) (A δ : ℝ) : Set (Fin l → Fin m → ℝ) :=
  {c | (∃ a : Fin l → ℤ, (∃ i, a i ≠ 0) ∧ (∀ i, |(a i : ℝ)| ≤ A) ∧
      ∃ b : Fin m → ℤ, ∀ j, |(∑ i, (a i : ℝ) * c i j) - (b j : ℝ)| < δ) ∧
    (∀ i j, c i j ∈ Set.Ico (0:ℝ) 1)}

theorem volume_badEvent_le {l m : ℕ} {A δ : ℝ} (hA : 0 ≤ A) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    volume (badEvent l m A δ) ≤ ENNReal.ofReal (((2 * A + 1) ^ l) * ((2 * δ) ^ m)) :=
  Commons.Analysis.Measure.volume_bad_union_le hA hδ0 hδ1

theorem badEvent_mono {l m : ℕ} {A A' δ δ' : ℝ} (hA : A ≤ A') (hδ : δ ≤ δ') :
    badEvent l m A δ ⊆ badEvent l m A' δ' := by
  rintro c ⟨⟨a, ha0, hAb, b, hb⟩, hbox⟩
  exact ⟨⟨a, ha0, fun i => le_trans (hAb i) hA, b, fun j => lt_of_lt_of_le (hb j) hδ⟩, hbox⟩

theorem box_measurable (l m : ℕ) : MeasurableSet (box l m) := by
  rw [show box l m = Set.univ.pi (fun _ : Fin l => Set.univ.pi (fun _ : Fin m =>
    Set.Ico (0:ℝ) 1)) from by
    ext c; simp [box]]
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_box (l m : ℕ) : volume (box l m) = 1 := by
  rw [show box l m = Set.univ.pi (fun _ : Fin l => Set.univ.pi (fun _ : Fin m =>
    Set.Ico (0:ℝ) 1)) from by
    ext c; simp [box]]
  rw [MeasureTheory.volume_pi_pi]
  have h : ∀ _ : Fin l, volume (Set.univ.pi (fun _ : Fin m => Set.Ico (0:ℝ) 1)) = 1 := by
    intro _
    rw [MeasureTheory.volume_pi_pi]
    simp [Real.volume_Ico]
  rw [Finset.prod_congr rfl (fun i _ => h i)]
  simp


/-! ### The a.e. statements -/

/-- For large `n`, the accuracy `δ_n` is at most `1/2` (the hypothesis of the cylinder bound). -/
theorem eventually_rateD_le (l m : ℕ) {ε : ℝ} (hm : 0 < m) (hε0 : 0 ≤ ε) :
    ∀ᶠ n : ℕ in Filter.atTop, rateD l m ε n ≤ 1 / 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hCpos : 0 < angleConst l m := by rw [angleConst]; positivity
  have hB : 0 < 1 / (m : ℝ) + ε := by
    have : 0 < 1 / (m : ℝ) := by positivity
    linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log (2 * angleConst l m) / (1 / (m : ℝ) + ε))
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.log (2 * angleConst l m) ≤ (n : ℝ) * (1 / (m : ℝ) + ε) := by
    rw [div_le_iff₀ hB] at hN
    have := mul_le_mul_of_nonneg_right hnR hB.le
    linarith
  have h2 : Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))) ≤ (2 * angleConst l m)⁻¹ := by
    rw [Real.exp_neg]
    have hle : 2 * angleConst l m ≤ Real.exp ((n : ℝ) * (1 / (m : ℝ) + ε)) := by
      rw [← Real.exp_log (by positivity : (0:ℝ) < 2 * angleConst l m)]
      exact Real.exp_le_exp.mpr (by linarith)
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity : (0:ℝ) < 2 * angleConst l m)).mpr hle
  have hne : angleConst l m ≠ 0 := ne_of_gt hCpos
  calc rateD l m ε n = angleConst l m * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))) := rfl
    _ ≤ angleConst l m * (2 * angleConst l m)⁻¹ := mul_le_mul_of_nonneg_left h2 hCpos.le
    _ = 1 / 2 := by field_simp

/-- **Step B (Borel–Cantelli).**  For every rate `ε ∈ (0, 1/ℓ]` and almost every `c`, only
finitely many integer times are bad. -/
theorem escape_ae (l m : ℕ) (hl : 0 < l) (hm : 0 < m) {ε : ℝ} (hε0 : 0 < ε)
    (hεl : ε ≤ 1 / (l : ℝ)) :
    ∀ᵐ c ∂(volume : Measure (Fin l → Fin m → ℝ)),
      ∃ N : ℕ, ∀ n ≥ N, rateD l m ε n ≤ 1 / 2 ∧
        c ∉ badEvent l m (rateA l ε n) (rateD l m ε n) := by
  classical
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (eventually_rateD_le l m hm hε0.le)
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hCpos : 0 < angleConst l m := by rw [angleConst]; positivity
  have hr0 : 0 ≤ geomR l m ε := Real.exp_nonneg _
  have hr1 : geomR l m ε < 1 := by
    rw [geomR]
    refine Real.exp_lt_one_iff.mpr ?_
    have h1 : 0 < (l : ℝ) + (m : ℝ) := by linarith
    nlinarith [hε0, h1]
  set K : ℝ := geomK l m ε * (geomR l m ε) ^ N₁ with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg ?_ (pow_nonneg hr0 _)
    rw [geomK]
    positivity
  have hstep : ∀ n : ℕ,
      volume (badEvent l m (rateA l ε (n + N₁)) (rateD l m ε (n + N₁)))
        ≤ ENNReal.ofReal (K * (geomR l m ε) ^ n) := by
    intro n
    have hδ1 : rateD l m ε (n + N₁) ≤ 1 / 2 := hN₁ (n + N₁) (Nat.le_add_left N₁ n)
    have hvol := volume_badEvent_le (l := l) (m := m) (A := rateA l ε (n + N₁))
      (δ := rateD l m ε (n + N₁))
      (by rw [rateA]; positivity) (by rw [rateD]; positivity) hδ1
    refine le_trans hvol (ENNReal.ofReal_le_ofReal ?_)
    have hgeom := Commons.Analysis.Real.geom_bound_two_scale l m hl hm hε0.le hεl (n + N₁)
    calc (2 * rateA l ε (n + N₁) + 1) ^ l * (2 * rateD l m ε (n + N₁)) ^ m
        ≤ (5 ^ l * Real.exp (1 - (l : ℝ) * ε) * (2 * Real.sqrt (2 + (l : ℝ) * (m : ℝ))) ^ m) *
            (Real.exp (-(ε * ((l : ℝ) + (m : ℝ))))) ^ (n + N₁) := hgeom
      _ = K * (geomR l m ε) ^ n := by
          simp only [hKdef, geomK, geomR, angleConst, pow_add]
          ring
  have hsum_bound : (∑' n : ℕ,
      volume (badEvent l m (rateA l ε (n + N₁)) (rateD l m ε (n + N₁))))
      ≤ ENNReal.ofReal (K / (1 - geomR l m ε)) := by
    refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
    exact le_of_eq (Commons.Analysis.ENNReal.tsum_ofReal_mul_geometric hK0 hr0 hr1)
  have hne_top : (∑' n : ℕ,
      volume (badEvent l m (rateA l ε (n + N₁)) (rateD l m ε (n + N₁)))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum_bound
  have hbc : ∀ᵐ c ∂(volume : Measure (Fin l → Fin m → ℝ)),
      ∀ᶠ n : ℕ in Filter.atTop,
        c ∉ badEvent l m (rateA l ε (n + N₁)) (rateD l m ε (n + N₁)) :=
    MeasureTheory.ae_eventually_notMem hne_top
  filter_upwards [hbc] with c hc
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hc
  refine ⟨max (M + N₁) N₁, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : M + N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hMn : M ≤ n - N₁ := by omega
  refine ⟨hN₁ n hn1, ?_⟩
  have h := hM (n - N₁) hMn
  rwa [Nat.sub_add_cancel hn1] at h

/-- **The absence of a rational point, a.e.**  For almost every `c`, the graph plane
`graphPlane c` meets `ℤᵈ` only in `0` (equivalently, the linear system `∑ i, aᵢ c_{ij} = b_j`
has no non-trivial integer solution). -/
theorem noRationalPoint_ae (l m : ℕ) (hm : 0 < m) :
    ∀ᵐ c ∂(volume : Measure (Fin l → Fin m → ℝ)),
      ¬ ∃ a : Fin l → ℤ, (∃ i, a i ≠ 0) ∧ ∃ b : Fin m → ℤ,
        ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ) := by
  classical
  rw [MeasureTheory.ae_iff]
  have hset : {c : Fin l → Fin m → ℝ |
        ¬ ¬ ∃ a : Fin l → ℤ, (∃ i, a i ≠ 0) ∧ ∃ b : Fin m → ℤ,
          ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ)}
      = ⋃ (a : {a : Fin l → ℤ // ∃ i, a i ≠ 0}) (b : Fin m → ℤ),
          {c : Fin l → Fin m → ℝ |
            ∀ j, (∑ i, ((a : Fin l → ℤ) i : ℝ) * c i j) = (b j : ℝ)} := by
    ext c
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [hset]
  refine measure_iUnion_null fun a => ?_
  exact measure_iUnion_null fun b =>
    Commons.Analysis.Measure.columns_level_volume_zero hm (a : Fin l → ℤ) a.2 b

end Submission.EscapeMeasure

end
