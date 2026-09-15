import ChallengeDeps
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.FUP.WeightOmega
import Submission.FUP.Dyadic
import Submission.FUP.Damping

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- `W_k = 2^k/k^s`, with the harmless convention `max k 1` so that the formula also makes
sense at `k = 0`. -/
noncomputable def Wk (s : ℝ) (k : ℕ) : ℝ := (2:ℝ)^k / (max (k:ℝ) 1)^s

lemma Wk_pos (s : ℝ) (k : ℕ) : 0 < Wk s k := by
  rw [Wk]
  exact div_pos (pow_pos (by norm_num) k)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) s)

lemma Wk_eq (s : ℝ) {k : ℕ} (hk : 1 ≤ k) : Wk s k = (2:ℝ)^k / (k:ℝ)^s := by
  rw [Wk, max_eq_left (by exact_mod_cast hk)]

lemma Wk_le_two_pow {s : ℝ} (hs : 0 < s) (k : ℕ) : Wk s k ≤ (2:ℝ)^k := by
  have hpos : 0 < (max (k:ℝ) 1)^s :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) s
  rw [Wk, div_le_iff₀ hpos]
  have h1 : (1:ℝ) ≤ (max (k:ℝ) 1)^s :=
    Real.one_le_rpow (le_max_right _ _) (le_of_lt hs)
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]

/-- The anchor for the width-`W_k` cube cover of `A_k`. -/
noncomputable def Rk (k : ℕ) : ℝ := (2:ℝ)^(k+2)

/-- The number of grid cells per coordinate: chosen so that `12·max(k,1)^s ≤ N_k`. -/
noncomputable def Nk (s : ℝ) (k : ℕ) : ℕ := ⌈12 * (max (k:ℝ) 1)^s⌉₊

lemma Nk_pos (s : ℝ) (k : ℕ) : 0 < Nk s k := by
  rw [Nk]
  apply Nat.ceil_pos.mpr
  have h : 0 < (max (k:ℝ) 1)^s :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) s
  linarith

lemma le_Nk (s : ℝ) (k : ℕ) : 12 * (max (k:ℝ) 1)^s ≤ (Nk s k : ℝ) :=
  Nat.le_ceil _

/-- The dyadic annulus `A_k = {2^k ≤ ‖x‖ ≤ 2^{k+1}}`. -/
def Ak (k : ℕ) : Set ℝᵈ := annulus ((2:ℝ)^k) ((2:ℝ)^(k+1))

lemma mem_Ak {k : ℕ} {x : ℝᵈ} : x ∈ Ak k ↔ (2:ℝ)^k ≤ ‖x‖ ∧ ‖x‖ ≤ (2:ℝ)^(k+1) := Iff.rfl

lemma Ak_subset_ball (k : ℕ) :
    (Ak k : Set ℝᵈ) ⊆ closedBall (0 : ℝᵈ) ((2:ℝ)^(k+1)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact (mem_Ak.mp hx).2

lemma Ak_subset_cube (k : ℕ) :
    (Ak k : Set ℝᵈ) ⊆ cube (-(2:ℝ)^(k+1)) ((2:ℝ)^(k+1)) := by
  intro x hx
  rw [mem_cube]
  intro i
  have h1 : |x i| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_apply_le_norm x i
  have h2 := (mem_Ak.mp hx).2
  constructor <;> linarith [abs_le.mp (le_trans h1 h2)]

/-- The coefficient `2^k/k^α` of the weight `ω_k`. -/
noncomputable def coefK (α : ℝ) (k : ℕ) : ℝ := (2:ℝ)^k / (max (k:ℝ) 1)^α

lemma coefK_nonneg (α : ℝ) (k : ℕ) : 0 ≤ coefK α k :=
  div_nonneg (by positivity) (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) α)

lemma coefK_pos (α : ℝ) (k : ℕ) : 0 < coefK α k :=
  div_pos (pow_pos (by norm_num) k)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) α)

/-- The weight `ω_k = -(2^k/k^α)·Ψ_k`. -/
noncomputable def omegaK (s α : ℝ) (k : ℕ) (Y : Set ℝᵈ) : ℝᵈ → ℝ :=
  fun x => (-(coefK α k)) • psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x

lemma omegaK_apply (s α : ℝ) (k : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) :
    omegaK s α k Y x = -(coefK α k) * psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k)
      Y (Ak k) x := by
  rw [omegaK, smul_eq_mul]

lemma omegaK_nonpos (s α : ℝ) (k : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) :
    omegaK s α k Y x ≤ 0 := by
  have h1 : 0 ≤ psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x :=
    psiK_nonneg (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x
  have h2 : 0 ≤ coefK α k := coefK_nonneg α k
  rw [omegaK_apply]
  nlinarith

lemma omegaK_contDiff (s α : ℝ) (k : ℕ) (Y : Set ℝᵈ) :
    ContDiff ℝ 3 (omegaK s α k Y) := by
  have hpsi : ContDiff ℝ 3 (psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k)) :=
    psiK_contDiff _ _ _ _ _ _
  exact hpsi.const_smul _

/-- The derivative of `Ψ_k` vanishes off `𝕐_k`. -/
lemma iteratedFDeriv_psiK_eq_zero_of_notMem_yCover (R W : ℝ) (hW : 0 < W) (N : ℕ)
    (Y A : Set ℝᵈ) {x : ℝᵈ} (hx : x ∉ yCover R W N Y A) {a : ℕ} (ha : a ≤ 3) :
    iteratedFDeriv ℝ a (psiK R W hW N Y A) x = 0 := by
  classical
  have hsum : psiK R W hW N Y A = fun x => ∑ j ∈ (Finset.univ.filter
      (fun j : Fin d → Fin N => (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
      coverBump R W hW N j x := rfl
  rw [hsum]
  have hterm : ∀ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
      (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
      iteratedFDeriv ℝ a (coverBump R W hW N j) x = 0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact iteratedFDeriv_coverBump_eq_zero_of_notMem R W hW N j
      (fun hmem => hx ⟨j, hj.2, hmem⟩) a
  have hcd : ∀ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
      (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
      ContDiff ℝ a (coverBump R W hW N j) :=
    fun j _ => (coverBump_contDiff R W hW N j).of_le (by exact_mod_cast ha)
  rw [iteratedFDeriv_sum hcd, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun j hj => hterm j hj)

lemma omegaK_eq_zero_of_notMem_yCover {s α : ℝ} {k : ℕ} {Y : Set ℝᵈ} {x : ℝᵈ}
    (hx : x ∉ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)) : omegaK s α k Y x = 0 := by
  rw [omegaK, psiK_eq_zero_of_notMem_yCover _ _ _ _ _ _ hx]
  simp

lemma iteratedFDeriv_omegaK_eq_zero_of_notMem_yCover {s α : ℝ} {k a : ℕ} (ha : a ≤ 3)
    {Y : Set ℝᵈ} {x : ℝᵈ} (hx : x ∉ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)) :
    iteratedFDeriv ℝ a (omegaK s α k Y) x = 0 := by
  have hf : ContDiffAt ℝ a (psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k)) x :=
    ((psiK_contDiff (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k)).of_le
      (by exact_mod_cast ha)).contDiffAt
  show iteratedFDeriv ℝ a (fun x => (-(coefK α k)) •
    psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x) x = 0
  rw [iteratedFDeriv_const_smul_apply' hf]
  rw [iteratedFDeriv_psiK_eq_zero_of_notMem_yCover (Rk k) (Wk s k) (Wk_pos s k) (Nk s k)
    Y (Ak k) hx ha]
  simp

/-- `𝕐_k` sits inside the annulus `{2^{k-1} ≤ ‖x‖ ≤ 2^{k+2}}` as long as the grid is fine
enough. -/
lemma yCover_subset_annulusRk {s : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1)) {Y : Set ℝᵈ} :
    yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k) ⊆
      (annulus ((2:ℝ)^(k-1)) ((2:ℝ)^(k+2)) : Set ℝᵈ) := by
  rintro z ⟨j, ⟨w, hwbox, _, hwA⟩, hzbox⟩
  have hdist : ‖z - w‖ ≤ Real.sqrt (d:ℝ) * Wk s k :=
    norm_sub_le_of_mem_coverBox (le_of_lt (Wk_pos s k)) hzbox hwbox
  have hwk : (2:ℝ)^k ≤ ‖w‖ := (mem_Ak.mp hwA).1
  have hwk'' : ‖w‖ ≤ (2:ℝ)^(k+1) := (mem_Ak.mp hwA).2
  have hb : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_succ, pow_succ]; ring
  have hka : (2:ℝ)^(k-1) * 2 = (2:ℝ)^k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have h2kpos : 0 < (2:ℝ)^(k-1) := pow_pos (by norm_num) _
  have h1 : (2:ℝ)^k - (2:ℝ)^(k-1) = (2:ℝ)^(k-1) := by linarith [hka]
  have hsub := abs_norm_sub_norm_le z w
  rw [abs_le] at hsub
  rw [mem_annulus]
  constructor
  · linarith [hsub.1, hdist, hwk, hW, h1]
  · have h3 : (2:ℝ)^(k+1) + (2:ℝ)^(k-1) ≤ (2:ℝ)^(k+2) := by
      have e1 : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
      nlinarith [hka, hb, h2kpos]
    linarith [hsub.2, hdist, hwk'', hW, h3]

lemma omegaK_eq_zero_of_norm_lt {s α : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1)) {Y : Set ℝᵈ} {x : ℝᵈ}
    (hx : ‖x‖ < (2:ℝ)^(k-1)) : omegaK s α k Y x = 0 := by
  refine omegaK_eq_zero_of_notMem_yCover (s := s) (α := α) (Y := Y) ?_
  intro hmem
  have h := yCover_subset_annulusRk (k := k) hk hW hmem
  rw [mem_annulus] at h
  linarith [h.1]

/-- The weight `ω = Σ_{k₀ ≤ k ≤ K} ω_k`. -/
noncomputable def omega (s α : ℝ) (k₀ K : ℕ) (Y : Set ℝᵈ) : ℝᵈ → ℝ :=
  fun x => ∑ k ∈ Finset.Icc k₀ K, omegaK s α k Y x

lemma omega_nonpos (s α : ℝ) (k₀ K : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) :
    omega s α k₀ K Y x ≤ 0 :=
  Finset.sum_nonpos fun k _ => omegaK_nonpos s α k Y x

lemma omega_contDiff (s α : ℝ) (k₀ K : ℕ) (Y : Set ℝᵈ) :
    ContDiff ℝ 3 (omega s α k₀ K Y) :=
  ContDiff.sum fun k _ => omegaK_contDiff s α k Y

lemma omega_eq_zero_of_norm_lt {s α : ℝ} {k₀ K : ℕ} (h1 : 1 ≤ k₀)
    (hW : ∀ k ∈ Finset.Icc k₀ K, Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1))
    {Y : Set ℝᵈ} {x : ℝᵈ} (hx : ‖x‖ < (2:ℝ)^(k₀-1)) : omega s α k₀ K Y x = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  refine omegaK_eq_zero_of_norm_lt (k := k) ?_ (hW k hk) ?_
  · have := (Finset.mem_Icc.mp hk).1; omega
  · have hmono : (2:ℝ)^(k₀-1) ≤ (2:ℝ)^(k-1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right (Finset.mem_Icc.mp hk).1 1)
    linarith

section LowerBound

lemma Ak_cover_h1 {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (2:ℝ)^(k+1) + Wk s k / 4 ≤ Rk k := by
  rw [Rk]
  have h : Wk s k ≤ (2:ℝ)^k := Wk_le_two_pow hs k
  have h2 : (2:ℝ)^(k+1) + (2:ℝ)^k / 4 ≤ (2:ℝ)^(k+2) := by
    have e1 : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
    have e2 : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_succ, pow_succ]; ring
    linarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
  linarith

lemma Ak_cover_h2 (s : ℝ) (k : ℕ) :
    (2:ℝ)^(k+1) + Rk k ≤ (Nk s k : ℝ) * (Wk s k / 2) := by
  rw [Rk]
  have hN : 12 * (max (k:ℝ) 1)^s ≤ (Nk s k : ℝ) := le_Nk s k
  have hpos : 0 < (max (k:ℝ) 1)^s :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) s
  have h2k : 0 < (2:ℝ)^k := pow_pos (by norm_num) k
  have key : (2:ℝ)^(k+1) + (2:ℝ)^(k+2) = 6 * (2:ℝ)^k := by
    have e1 : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
    have e2 : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_succ, pow_succ]; ring
    linarith
  rw [key]
  have hWeq : Wk s k / 2 = (2:ℝ)^k / (2 * (max (k:ℝ) 1)^s) := by
    rw [Wk]; field_simp
  rw [hWeq, mul_div_assoc']
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (max (k:ℝ) 1)^s)]
  nlinarith [hN, h2k, hpos]

/-- `Ψ_k ≥ 1` on `Y ∩ A_k`. -/
lemma one_le_psiK_Ak {s : ℝ} (hs : 0 < s) (k : ℕ) {Y : Set ℝᵈ} {x : ℝᵈ}
    (hx : x ∈ Y ∩ Ak k) :
    1 ≤ psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x :=
  one_le_psiK (Wk_pos s k) (Nk_pos s k) (Ak_cover_h1 hs k) (Ak_cover_h2 s k)
    (Ak_subset_cube k) hx

/-- On `Y ∩ A_k` the weight satisfies `ω_k ≤ -(2^k/k^α)`. -/
lemma omegaK_le_on_Y {s α : ℝ} (hs : 0 < s) (k : ℕ) {Y : Set ℝᵈ} {x : ℝᵈ}
    (hx : x ∈ Y ∩ Ak k) : omegaK s α k Y x ≤ -(coefK α k) := by
  have h1 : 1 ≤ psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x :=
    one_le_psiK_Ak hs k hx
  have h2 : 0 ≤ coefK α k := coefK_nonneg α k
  rw [omegaK_apply]
  nlinarith

/-- Dyadic decomposition: for `r ≥ 1` there is a unique `j` with `2^j ≤ r < 2^{j+1}`. -/
lemma exists_pow_le_lt {r : ℝ} (hr : 1 ≤ r) :
    ∃ j : ℕ, (2:ℝ)^j ≤ r ∧ r < (2:ℝ)^(j+1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (by norm_num : (1:ℝ) < 2)
  have hex : ∃ k, r < (2:ℝ)^k := ⟨n, hn⟩
  have hspec : r < (2:ℝ)^(Nat.find hex) := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hspec; simp at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact not_lt.mp (Nat.find_min hex (by omega))
  · rw [Nat.sub_add_cancel hpos]; exact hspec

/-- For `2^{k₀} ≤ r ≤ 2^{K+1}` there is a dyadic annulus index `k ∈ [k₀,K]` with
`r ∈ A_k`. -/
lemma exists_annulus_index {k₀ K : ℕ} {r : ℝ} (hkK : k₀ ≤ K) (hr1 : (2:ℝ)^k₀ ≤ r)
    (hr2 : r ≤ (2:ℝ)^(K+1)) :
    ∃ k ∈ Finset.Icc k₀ K, (2:ℝ)^k ≤ r ∧ r ≤ (2:ℝ)^(k+1) := by
  have hr1' : (1:ℝ) ≤ r := le_trans (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hr1
  obtain ⟨j, hj1, hj2⟩ := exists_pow_le_lt hr1'
  have hk0j : k₀ ≤ j := by
    by_contra h
    push Not at h
    have hle : (2:ℝ)^(j+1) ≤ (2:ℝ)^k₀ :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    linarith
  refine ⟨min j K, Finset.mem_Icc.mpr ⟨le_min hk0j hkK, min_le_right _ _⟩, ?_, ?_⟩
  · rcases lt_or_ge j K with h | h
    · rw [min_eq_left (le_of_lt h)]; exact hj1
    · rw [min_eq_right h]
      exact le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h) hj1
  · rcases lt_or_ge j K with h | h
    · rw [min_eq_left (le_of_lt h)]; exact le_of_lt hj2
    · rw [min_eq_right h]; exact hr2

end LowerBound

section YLowerBound

lemma log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

lemma log_two_gt_half : (1/2 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- `2^k/k^α` dominates `(1/20)·r/(log(2+r))^α` for `r ∈ A_k`, `k ≥ 1`, `0 < α ≤ 1`. -/
lemma coefK_ge_self {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr1 : (2:ℝ)^k ≤ r) (hr2 : r ≤ (2:ℝ)^(k+1)) :
    (1/20 : ℝ) * (r / (Real.log (2 + r))^α) ≤ coefK α k := by
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlog2 : 0 < Real.log 2 := log_two_pos
  have hlog2le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hrpos : 0 < r := lt_of_lt_of_le (pow_pos (by norm_num) k) hr1
  have hlogr : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have h2k : (0:ℝ) < (2:ℝ)^k := pow_pos (by norm_num) k
  -- `log (2+r) ≥ log (2^k) = k log 2`
  have hm : (2:ℝ)^k ≤ 2 + r := by linarith [hr1]
  have hlog : (k:ℝ) * Real.log 2 ≤ Real.log (2 + r) := by
    have := Real.log_le_log h2k hm
    rwa [Real.log_pow] at this
  have hden : ((k:ℝ) * Real.log 2)^α ≤ (Real.log (2 + r))^α :=
    Real.rpow_le_rpow (by positivity) hlog (le_of_lt hα)
  have hden2 : ((k:ℝ) * Real.log 2)^α = (k:ℝ)^α * (Real.log 2)^α :=
    Real.mul_rpow (le_of_lt hkR) (le_of_lt hlog2)
  -- `(log 2)^α ≥ 1/2`
  have hpow2 : (1/2 : ℝ) ≤ (Real.log 2)^α := by
    have h1 : (Real.log 2) ^ (1:ℝ) ≤ (Real.log 2) ^ α :=
      Real.rpow_le_rpow_of_exponent_ge hlog2 hlog2le1 hα1
    rw [Real.rpow_one] at h1
    linarith [log_two_gt_half]
  have hnum : r ≤ 2 * (2:ℝ)^k := by
    have e : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
    linarith
  rw [coefK, max_eq_left (by exact_mod_cast hk : (1:ℝ) ≤ k)]
  have hstep : (1/20 : ℝ) * (r / (Real.log (2 + r))^α) ≤
      (1/20 : ℝ) * (2 * (2:ℝ)^k / ((k:ℝ)^α * (Real.log 2)^α)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hden' : (k:ℝ)^α * (Real.log 2)^α ≤ (Real.log (2 + r))^α := by
      rw [← hden2]; exact hden
    exact div_le_div₀ (by positivity : (0:ℝ) ≤ 2 * (2:ℝ)^k) hnum
      (by positivity : (0:ℝ) < (k:ℝ)^α * (Real.log 2)^α) hden'
  refine hstep.trans ?_
  have hAle : (1/20 : ℝ) * (2 / (Real.log 2)^α) ≤ 1 := by
    have hl0 : (0:ℝ) < (Real.log 2)^α := Real.rpow_pos_of_pos hlog2 α
    rw [mul_div_assoc', div_le_iff₀ hl0]
    nlinarith [hpow2]
  calc (1/20 : ℝ) * (2 * (2:ℝ)^k / ((k:ℝ)^α * (Real.log 2)^α))
      = ((1/20 : ℝ) * (2 / (Real.log 2)^α)) * ((2:ℝ)^k / (k:ℝ)^α) := by
        field_simp
    _ ≤ 1 * ((2:ℝ)^k / (k:ℝ)^α) :=
        mul_le_mul_of_nonneg_right hAle (by positivity)
    _ = (2:ℝ)^k / (k:ℝ)^α := one_mul _

/-- **Lower bound for `ω` on `Y`.**  For `Y`-points inside the range of the dyadic annuli,
`ω` is at most `-(1/20)|x|/(log(2+|x|))^α` up to an additive constant depending only on `k₀`. -/
lemma omega_le_on_Y {s α : ℝ} {k₀ K : ℕ} (hs : 0 < s) (hα : 0 < α) (hα1 : α ≤ 1)
    (hk0 : 1 ≤ k₀) (hkK : k₀ ≤ K)
    {Y : Set ℝᵈ} {x : ℝᵈ} (hxY : x ∈ Y) (hxK : ‖x‖ ≤ (2:ℝ)^(K+1)) :
    omega s α k₀ K Y x ≤
      -(1/20) * (‖x‖ / (Real.log (2 + ‖x‖))^α)
        + (1/20) * ((2:ℝ)^k₀ / (Real.log 2)^α) := by
  rcases lt_or_ge ((2:ℝ)^k₀) ‖x‖ with hbig | hsmall
  · obtain ⟨k, hk, hk1, hk2⟩ := exists_annulus_index hkK (le_of_lt hbig) hxK
    have hxA : x ∈ Ak k := mem_Ak.mpr ⟨hk1, hk2⟩
    have hle : omega s α k₀ K Y x ≤ omegaK s α k Y x := by
      rw [omega, ← Finset.sum_erase_add _ _ hk]
      have hrest : ∑ j ∈ (Finset.Icc k₀ K).erase k, omegaK s α j Y x ≤ 0 :=
        Finset.sum_nonpos fun j _ => omegaK_nonpos s α j Y x
      linarith
    have h2 : omegaK s α k Y x ≤ -(coefK α k) :=
      omegaK_le_on_Y (s := s) (α := α) hs k ⟨hxY, hxA⟩
    have hkge1 : 1 ≤ k := le_trans hk0 (Finset.mem_Icc.mp hk).1
    have hcoef : (1/20 : ℝ) * (‖x‖ / (Real.log (2 + ‖x‖))^α) ≤ coefK α k :=
      coefK_ge_self hα hα1 hkge1 hk1 hk2
    have hC : (0:ℝ) ≤ (1/20) * ((2:ℝ)^k₀ / (Real.log 2)^α) := by positivity
    nlinarith [hle, h2, hcoef, hC]
  · have hlog2 : 0 < Real.log 2 := log_two_pos
    have hlogx : 0 < Real.log (2 + ‖x‖) := Real.log_pos (by linarith [norm_nonneg x])
    have hden : (Real.log 2)^α ≤ (Real.log (2 + ‖x‖))^α :=
      Real.rpow_le_rpow (le_of_lt hlog2)
        (Real.log_le_log (by norm_num) (by linarith [norm_nonneg x])) (le_of_lt hα)
    have h1 : (1/20 : ℝ) * (‖x‖ / (Real.log (2 + ‖x‖))^α) ≤
        (1/20 : ℝ) * ((2:ℝ)^k₀ / (Real.log 2)^α) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div₀ (by positivity : (0:ℝ) ≤ (2:ℝ)^k₀) hsmall
        (Real.rpow_pos_of_pos hlog2 α) hden
    have h0 : omega s α k₀ K Y x ≤ 0 := omega_nonpos s α k₀ K Y x
    nlinarith [h0, h1]

end YLowerBound

end Submission.FUP
