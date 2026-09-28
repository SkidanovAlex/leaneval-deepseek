import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.bigW_le_pow

/-!
# Prelude for the per-residue-class lower bound `class_count_lower`

Basic topological and measure-theoretic facts about `Work.HP.coneRegion` used by the
lattice-point bounds `grid_coset_lower` / `grid_coset_upper`, plus the elementary
"norm one" bound for nonzero integer vectors.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise

namespace Work.HP.HP2

lemma continuous_rNorm_general {ι : Type*} [Fintype ι] :
    Continuous (fun v : ι → ℝ => Work.HP.rNorm v) := by
  simp only [Work.HP.rNorm]; fun_prop

lemma continuous_dotR_left {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Continuous (fun t => Work.HP.dotR v t) := by
  have h : (fun t : ι → ℝ => Work.HP.dotR v t) = fun t => ∑ i, v i * t i := rfl
  rw [h]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))

lemma continuous_dotR_veronese (d n : ℕ) (a : Work.HP.Mon d n → ℤ) :
    Continuous (fun x : Fin (n + 1) → ℝ => Work.HP.dotR (Work.HP.veronese d n x) (Work.HP.toR a)) := by
  have h : (fun x : Fin (n + 1) → ℝ => Work.HP.dotR (Work.HP.veronese d n x) (Work.HP.toR a))
      = fun x => ∑ μ : Work.HP.Mon d n, Work.HP.veronese d n x μ * (Work.HP.toR a) μ := rfl
  rw [h]
  apply continuous_finsetSum
  intro μ _
  refine Continuous.mul ?_ continuous_const
  simp only [Work.HP.veronese]
  exact continuous_finsetProd _ (fun i _ => (continuous_apply i).pow _)

lemma continuous_rNorm_veronese (d n : ℕ) :
    Continuous (fun x : Fin (n + 1) → ℝ => Work.HP.rNorm (Work.HP.veronese d n x)) := by
  have h : (fun x : Fin (n + 1) → ℝ => Work.HP.rNorm (Work.HP.veronese d n x))
      = fun x => Real.sqrt (∑ μ : Work.HP.Mon d n, (Work.HP.veronese d n x μ) ^ 2) := by
    funext x; rfl
  rw [h]
  refine Real.continuous_sqrt.comp ?_
  apply continuous_finsetSum
  intro μ _
  refine Continuous.pow ?_ 2
  simp only [Work.HP.veronese]
  exact continuous_finsetProd _ (fun i _ => (continuous_apply i).pow _)

lemma isClosed_Cgam {ι : Type*} [Fintype ι] (v : ι → ℝ) (α : ℝ) :
    IsClosed (Work.HP.Cgam v α) := by
  have h : Work.HP.Cgam v α = {t | |Work.HP.dotR v t| ≤ Work.HP.rNorm v * Work.HP.rNorm t / (2 * α)} := rfl
  rw [h]
  exact isClosed_le (continuous_abs.comp (continuous_dotR_left v))
    ((continuous_const.mul continuous_rNorm_general).div_const (2 * α))

theorem isClosed_coneRegion (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α T : ℝ) :
    IsClosed (Work.HP.coneRegion d n a α T) := by
  have h : Work.HP.coneRegion d n a α T
      = {x : Fin (n + 1) → ℝ | Work.HP.rNorm x ≤ T} ∩
        {x : Fin (n + 1) → ℝ |
          |Work.HP.dotR (Work.HP.veronese d n x) (Work.HP.toR a)|
            ≤ Work.HP.rNorm (Work.HP.veronese d n x) * Work.HP.rNorm (Work.HP.toR a) / (2 * α)} := by
    ext x
    simp only [Work.HP.coneRegion, Work.HP.Cgam, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  exact (isClosed_le (continuous_rNorm_general) continuous_const).inter
    (isClosed_le (continuous_abs.comp (continuous_dotR_veronese d n a))
      (((continuous_rNorm_veronese d n).mul continuous_const).div_const (2 * α)))

theorem isBounded_coneRegion (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α T : ℝ) :
    Bornology.IsBounded (Work.HP.coneRegion d n a α T) := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : Fin (n + 1) → ℝ)).mpr ⟨max T 0, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (le_max_right T 0)]
  intro i
  simp only [Real.dist_eq, Pi.zero_apply, sub_zero]
  refine le_trans (abs_apply_le_rNorm x i) ?_
  exact le_trans hx.1 (le_max_left T 0)

theorem mem_coneRegion_toR (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α T : ℝ)
    (v : Fin (n + 1) → ℤ) :
    Work.HP.toR v ∈ Work.HP.coneRegion d n a α T ↔
      Work.HP.eNorm v ≤ T ∧ Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.toR (Work.HP.veronese d n v)) α := by
  simp only [Work.HP.coneRegion, Set.mem_ofPred_eq, Work.HP.eNorm_eq_rNorm_toR,
    Work.HP.toR_veronese]

theorem coneRegion_mono (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α : ℝ) {T T' : ℝ} (h : T ≤ T') :
    Work.HP.coneRegion d n a α T ⊆ Work.HP.coneRegion d n a α T' := by
  intro x hx
  exact ⟨le_trans hx.1 h, hx.2⟩

theorem coneRegion_volume_div (d n : ℕ) (a : Work.HP.Mon d n → ℤ) {α R : ℝ}
    (hα : 0 < α) (hR : 0 < R) {k : ℕ} (hk : 0 < k) :
    (MeasureTheory.volume (Work.HP.coneRegion d n a α (R / (k : ℝ)))).toReal
      = (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal / (k : ℝ) ^ (n + 1) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hRk : 0 < R / (k : ℝ) := by positivity
  rw [Work.HP.volume_coneRegion d n a hα hRk, Work.HP.volume_coneRegion d n a hα hR]
  rw [div_pow]
  field_simp

theorem veronese_zero' (d n : ℕ) (hd : 1 ≤ d) :
    Work.HP.veronese d n (0 : Fin (n + 1) → ℝ) = 0 := by
  funext m
  obtain ⟨i, hi⟩ : ∃ i, (m.1 i : ℕ) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : ∑ i, (m.1 i : ℕ) = 0 := Finset.sum_eq_zero (fun i _ => h i)
    omega
  have h0 : (∏ i : Fin (n + 1), (0 : ℝ) ^ ((m.1 i : ℕ))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi)
  simpa [Work.HP.veronese] using h0

theorem Cgam_zero {ι : Type*} [Fintype ι] (α : ℝ) :
    Work.HP.Cgam (0 : ι → ℝ) α = Set.univ := by
  ext t
  simp only [Work.HP.Cgam, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  simp [Work.HP.dotR, Work.HP.rNorm]

theorem zero_mem_coneRegion (d n : ℕ) (hd : 1 ≤ d) (a : Work.HP.Mon d n → ℤ) {α T : ℝ}
    (hT : 0 ≤ T) : (0 : Fin (n + 1) → ℝ) ∈ Work.HP.coneRegion d n a α T := by
  refine ⟨?_, ?_⟩
  · simpa [Work.HP.rNorm] using hT
  · rw [veronese_zero' d n hd, Cgam_zero]
    exact Set.mem_univ _

theorem one_le_eNorm_of_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    1 ≤ Work.HP.eNorm v := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  have h3 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    have h2' : ((1 : ℤ) : ℝ) ≤ ((|v i| : ℤ) : ℝ) := by exact_mod_cast h2
    rwa [Int.cast_abs, Int.cast_one] at h2'
  have h1 : (1 : ℝ) ≤ ((v i : ℝ)) ^ 2 := by
    nlinarith [abs_nonneg ((v i : ℝ)), h3, sq_abs ((v i : ℝ))]
  have h2 : (1 : ℝ) ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    le_trans h1 (Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i))
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Work.HP.eNorm v := rfl

/-! ## Auxiliary facts for the assembly of `class_count_lower` -/

/-- `k^{-(n+1)} = 1/k^{n+1}`. -/
theorem rpow_neg_succ_inv (k n : ℕ) : (k : ℝ) ^ (-((n : ℝ) + 1)) = 1 / (k : ℝ) ^ (n + 1) := by
  rw [show -((n : ℝ) + 1) = -(((n + 1 : ℕ) : ℝ)) by push_cast; ring]
  rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_natCast, inv_eq_one_div]

/-- `2 ≤ bigW (wOf B)` eventually. -/
theorem two_le_bigW_wOf_eventually :
    ∀ᶠ B in atTop, 2 ≤ Work.HP.bigW (Work.HP.wOf B) := by
  filter_upwards [Work.HP.tendsto_wOf_atTop.eventually_ge_atTop 2] with B hB
  exact Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (Work.HP.one_le_bigW _))
    (Work.HP.prime_dvd_bigW Nat.prime_two hB)

/-- If `b` is primitive at every prime divisor of `W ≥ 2`, then `W` does not divide all
coordinates of `b`. -/
theorem not_forall_dvd_of_hprim {n : ℕ} (W : ℕ) (b : Fin (n + 1) → ℤ) (hW2 : 2 ≤ W)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ b i) :
    ¬ ∀ i, (W : ℤ) ∣ b i := by
  intro hall
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show W ≠ 1 by omega)
  obtain ⟨i, hi⟩ := hprim p hp hpdvd
  apply hi
  obtain ⟨c, hc⟩ := hall i
  obtain ⟨d, hd⟩ := hpdvd
  refine ⟨(d : ℤ) * c, ?_⟩
  have hd' : (W : ℤ) = (p : ℤ) * (d : ℤ) := by rw [hd]; push_cast; ring
  rw [hc, hd']
  ring

/-- Reindexing a filtered sum over `range (K+1)` as a filtered sum over `Icc 1 K`, when the
`k = 0` term vanishes. -/
theorem sum_range_filter_eq_sum_Icc {K : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (f : ℕ → ℝ) (h0 : f 0 = 0) :
    ∑ k ∈ (Finset.range (K + 1)).filter P, f k
      = ∑ k ∈ (Finset.Icc 1 K).filter P, f k := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have hrange : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  conv_lhs => rw [hrange]
  rw [Finset.sum_insert (by simp)]
  have hz : (if P 0 then f 0 else 0) = 0 := by rw [h0]; split <;> rfl
  rw [hz, zero_add]

/-- Splitting a sum over `Icc 1 b` at `c` (with `c ≤ b`). -/
theorem sum_Icc_split {a b c : ℕ} (hac : a ≤ c + 1) (hcb : c ≤ b) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc a b, f k
      = ∑ k ∈ Finset.Icc a c, f k + ∑ k ∈ Finset.Icc (c + 1) b, f k := by
  have hdisj : Disjoint (Finset.Icc a c) (Finset.Icc (c + 1) b) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  have hunion : Finset.Icc a b = Finset.Icc a c ∪ Finset.Icc (c + 1) b := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  rw [hunion, Finset.sum_union hdisj]

end Work.HP.HP2
