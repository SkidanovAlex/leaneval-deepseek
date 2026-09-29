import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.S0
import Submission.Work.TMC16Core.Assembly.uniform_of_sum_bounds_gen
import Submission.Work.TMC16Core.Core.irrat_blk_nr
import Submission.Work.TMC16Core.Core.blk_sep_base
import Submission.Work.TMC16Core.Core.irrat_block_gen
import Submission.Work.TMC16Core.Core.irrat_blk_shift
import Submission.Work.TMC16Core.Trig.shift_block_relaxed

/-!
# Uniformity of the `s = 0`, `H = q(n-1)` window (`Assembly.s0_uniform_q1`)

`W1s0 a U ∪ W2s0 a U H M` is a *shifted block*: with `φ k = a - 1 + k + s0c k`
(`s0c k = 0` for `k ≤ 2U`, `s0c k = M = m qₙ` otherwise) the union is `φ '' [1,H]`.
The three trigonometric input estimates (numerator, `θ`-sums and difference sums) are
obtained from the shifted block product estimate `Trig.shift_block_relaxed`, the
Lagrange-product assembly is `Assembly.uniform_of_sum_bounds_gen`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-! ## The block parametrisation of the window -/

/-- The shift of the `k`-th site of the block: `0` on the first window, `M` on the second. -/
def s0c (M : ℤ) (U : ℕ) (k : ℕ) : ℤ := if k ≤ 2 * U then 0 else M

/-- The block parametrisation of the `s = 0` window: `k ↦ a - 1 + k + s0c k`. -/
def s0phi (a M : ℤ) (U : ℕ) (k : ℕ) : ℤ := a - 1 + (k : ℤ) + s0c M U k

/-- The number of shifts used by the pair `(k,l)`. -/
def s0t (U : ℕ) (k l : ℕ) : ℤ :=
  (if k ≤ 2 * U then 0 else 1) + (if l ≤ 2 * U then 0 else 1)

lemma s0c_add (M : ℤ) (U k l : ℕ) : s0c M U k + s0c M U l = s0t U k l * M := by
  unfold s0c s0t
  split_ifs <;> ring

lemma s0t_nonneg (U k l : ℕ) : 0 ≤ s0t U k l := by
  unfold s0t; split_ifs <;> omega

lemma s0t_le_two (U k l : ℕ) : s0t U k l ≤ 2 := by
  unfold s0t; split_ifs <;> omega

lemma s0phi_sum (a M : ℤ) (U k l H : ℕ) :
    s0phi a M U k + s0phi a M U l + (H : ℤ) - 2
      = (2 * a + (k : ℤ) + (l : ℤ) + (H : ℤ) - 4) + s0t U k l * M := by
  unfold s0phi
  have h := s0c_add M U k l
  linarith [h]

lemma s0phi_le {a M : ℤ} {U k : ℕ} (hk : k ≤ 2 * U) : s0phi a M U k = a - 1 + (k : ℤ) := by
  simp [s0phi, s0c, hk]

lemma s0phi_gt {a M : ℤ} {U k : ℕ} (hk : 2 * U < k) :
    s0phi a M U k = a - 1 + (k : ℤ) + M := by
  simp only [s0phi, s0c, Nat.not_le.mpr hk, if_false]

lemma s0c_of_le {M : ℤ} {U k : ℕ} (hk : k ≤ 2 * U) : s0c M U k = 0 := by
  simp [s0c, hk]

lemma s0c_of_gt {M : ℤ} {U k : ℕ} (hk : 2 * U < k) : s0c M U k = M := by
  simp only [s0c, Nat.not_le.mpr hk, if_false]

lemma image_s0phi {a M : ℤ} {U H : ℕ} (h2U : 2 * U ≤ H) :
    (Finset.Icc 1 H).image (s0phi a M U) = W1s0 a U ∪ W2s0 a U H M := by
  refine Finset.ext fun x => ?_
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_union, W1s0, W2s0]
  constructor
  · rintro ⟨k, ⟨hk1, hkH⟩, rfl⟩
    by_cases hk : k ≤ 2 * U
    · left; rw [s0phi_le hk]; constructor <;> omega
    · right; rw [s0phi_gt (Nat.lt_of_not_le hk)]; constructor <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · set k := (x - a + 1).toNat with hkdef
      have hz : (k : ℤ) = x - a + 1 := by rw [hkdef]; exact Int.toNat_of_nonneg (by omega)
      have hk1 : 1 ≤ k := by omega
      have hkH : k ≤ H := by omega
      have hk2U : k ≤ 2 * U := by omega
      exact ⟨k, ⟨hk1, hkH⟩, by rw [s0phi_le hk2U, hz]; ring⟩
    · set k := (x - M - a + 1).toNat with hkdef
      have hz : (k : ℤ) = x - M - a + 1 := by rw [hkdef]; exact Int.toNat_of_nonneg (by omega)
      have hk1 : 1 ≤ k := by omega
      have hkH : k ≤ H := by omega
      have hk2U : 2 * U < k := by omega
      exact ⟨k, ⟨hk1, hkH⟩, by rw [s0phi_gt hk2U, hz]; ring⟩

lemma s0phi_injOn {a M m : ℤ} {U H n : ℕ} {q : ℕ → ℕ}
    (hHq : H < q n) (hM : M = m * (q n : ℤ)) :
    Set.InjOn (s0phi a M U) ↑(Finset.Icc 1 H) := by
  intro k hk l hl hkl
  simp only [Finset.mem_coe, Finset.mem_Icc] at hk hl
  have hc : (k : ℤ) + s0c M U k = (l : ℤ) + s0c M U l := by
    have h := hkl; unfold s0phi at h; linarith
  have hMabs : m ≠ 0 → (H:ℤ) < |M| := by
    intro hm
    have h1 : (1:ℤ) ≤ |m| := Int.one_le_abs hm
    have hqn0 : (0:ℤ) < (q n : ℤ) := by omega
    have hge : |M| = |m| * (q n : ℤ) := by rw [hM, abs_mul, abs_of_nonneg hqn0.le]
    rw [hge]; nlinarith
  by_cases hk2 : k ≤ 2 * U
  · by_cases hl2 : l ≤ 2 * U
    · rw [s0c, if_pos hk2, s0c, if_pos hl2] at hc; omega
    · rw [s0c, if_pos hk2, s0c, if_neg (not_le.mpr (Nat.lt_of_not_le hl2))] at hc
      have hMz : M = (k:ℤ) - (l:ℤ) := by linarith
      have hle : |M| ≤ (H:ℤ) := by rw [hMz, abs_le]; constructor <;> omega
      rcases eq_or_ne m 0 with hm | hm
      · rw [hM, hm] at hMz; simp at hMz; omega
      · have := hMabs hm; omega
  · by_cases hl2 : l ≤ 2 * U
    · rw [s0c, if_neg (not_le.mpr (Nat.lt_of_not_le hk2)), s0c, if_pos hl2] at hc
      have hMz : M = (l:ℤ) - (k:ℤ) := by linarith
      have hle : |M| ≤ (H:ℤ) := by rw [hMz, abs_le]; constructor <;> omega
      rcases eq_or_ne m 0 with hm | hm
      · rw [hM, hm] at hMz; simp at hMz; omega
      · have := hMabs hm; omega
    · rw [s0c, if_neg (not_le.mpr (Nat.lt_of_not_le hk2)),
          s0c, if_neg (not_le.mpr (Nat.lt_of_not_le hl2))] at hc; omega

lemma card_s0 {a M m : ℤ} {U H n : ℕ} {q : ℕ → ℕ}
    (h2U : 2 * U ≤ H) (hHq : H < q n) (hM : M = m * (q n : ℤ)) :
    (W1s0 a U ∪ W2s0 a U H M).card = H := by
  rw [← image_s0phi (a := a) (M := M) h2U]
  rw [Finset.card_image_of_injOn (s0phi_injOn hHq hM)]
  rw [Nat.card_Icc]
  omega

/-- Reindexing a sum over the window by the block parametrisation. -/
lemma sum_image_erase {φ : ℕ → ℤ} {H : ℕ}
    (hφ : Set.InjOn φ ↑(Finset.Icc 1 H)) {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.Icc 1 H)
    (f : ℤ → ℝ) :
    ∑ i ∈ ((Finset.Icc 1 H).image φ).erase (φ k₀), f i
      = ∑ k ∈ (Finset.Icc 1 H).erase k₀, f (φ k) := by
  have hset : ((Finset.Icc 1 H).image φ).erase (φ k₀)
      = ((Finset.Icc 1 H).erase k₀).image φ := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hne, a, ha, haeq⟩
      exact ⟨a, ⟨fun hcon => hne (by rw [← haeq, hcon]), ha⟩, haeq⟩
    · rintro ⟨a, ⟨hane, ha⟩, haeq⟩
      exact ⟨fun hcon => hane (hφ ha hk₀ (by rw [haeq, hcon])), a, ha, haeq⟩
  rw [hset]
  exact Finset.sum_image (hφ.mono (by
    intro a ha
    simp only [Finset.mem_coe, Finset.mem_erase] at ha ⊢
    exact ha.2))

/-! ## The shifted block estimate (delegated) and the elementary transfers -/

/-- `log |sin|`-sums over a set with the *minimal* point removed dominate those with an
arbitrary point removed (the removed minimal term is at most the other one). -/
lemma sum_erase_log_le {S : Finset ℤ} {g : ℤ → ℝ} {k k₀ : ℤ}
    (hk : k ∈ S) (hk₀ : k₀ ∈ S) (hmin : ∀ i ∈ S, g k₀ ≤ g i)
    (hg : ∀ i ∈ S, i ≠ k → 0 < g i) :
    ∑ i ∈ S.erase k, Real.log (g i) ≤ ∑ i ∈ S.erase k₀, Real.log (g i) := by
  rcases eq_or_ne k₀ k with h | h
  · rw [h]
  · rw [Finset.sum_erase_eq_sub hk, Finset.sum_erase_eq_sub hk₀]
    have h1 : 0 < g k₀ := hg k₀ hk₀ h
    have h2 : g k₀ ≤ g k := hmin k hk
    have h3 : Real.log (g k₀) ≤ Real.log (g k) := Real.log_le_log h1 h2
    linarith

/-- Lower-bound version: with a *uniform* lower bound `2c` on `g` the sum over an arbitrary
erased point is at least the sum over the minimal point plus `log (2c)`. -/
lemma sum_erase_log_ge {S : Finset ℤ} {g : ℤ → ℝ} {k k₀ : ℤ} {c : ℝ}
    (hk : k ∈ S) (hk₀ : k₀ ∈ S) (hc : 0 < c)
    (hg : ∀ i ∈ S, 2 * c ≤ g i) (hle1 : ∀ i ∈ S, g i ≤ 1) :
    ∑ i ∈ S.erase k, Real.log (g i) ≥ ∑ i ∈ S.erase k₀, Real.log (g i) + Real.log (2 * c) := by
  rw [Finset.sum_erase_eq_sub hk, Finset.sum_erase_eq_sub hk₀]
  have hc2 : 0 < 2 * c := by linarith
  have h1 : Real.log (2 * c) ≤ Real.log (g k₀) := Real.log_le_log hc2 (hg k₀ hk₀)
  have h2 : Real.log (g k) ≤ 0 := Real.log_nonpos (le_of_lt (lt_of_lt_of_le hc2 (hg k hk)))
    (hle1 k hk)
  linarith

/-- The factors of the shifted block different from the minimal one are bounded below by the
separation hypothesis, hence are strictly positive. -/
lemma abs_sin_block_pos {α : ℝ} {Q : ℕ} {c : ℕ → ℤ} {x : ℝ} {k₀ : ℕ}
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ Q → 1 ≤ l → l ≤ Q → k ≠ l →
      1 / (5 * (Q : ℝ)) ≤
        fracDist ((((k : ℤ) + c k - ((l : ℤ) + c l) : ℤ) : ℝ) * α))
    (hk₀ : k₀ ∈ Finset.Icc 1 Q)
    (hmin : ∀ k ∈ Finset.Icc 1 Q,
      |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| ≥
      |Real.sin (2 * Real.pi * (x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α / 2))|)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 Q) (hkne : k ≠ k₀) :
    0 < |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| := by
  set w : ℕ → ℝ := fun k => 2 * x + ((k : ℝ) + (c k : ℝ)) * α with hw
  have h2π : ∀ k : ℕ, |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))|
      = Basic.S (w k) := by
    intro k
    rw [Work.TMC16Core.Basic.S]
    congr 1
    simp only [hw]; ring_nf
  have hsep' : 1 / (5 * (Q : ℝ)) ≤ Basic.nn (w k - w k₀) := by
    have h := hsep k k₀ (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
      (Finset.mem_Icc.mp hk₀).1 (Finset.mem_Icc.mp hk₀).2 hkne
    rw [Work.TMC16Core.Core.fracDist_eq_nn] at h
    have hw' : (((k : ℤ) + c k - ((k₀ : ℤ) + c k₀) : ℤ) : ℝ) * α = w k - w k₀ := by
      simp only [hw]; push_cast; ring
    rwa [hw'] at h
  have hmin' : Basic.nn (w k₀) ≤ Basic.nn (w k) := by
    have h := hmin k hk
    rw [h2π k, h2π k₀] at h
    exact (Core.S_le_iff_nn_le_aux _ _).mp h
  have hnn : 1 / (10 * (Q : ℝ)) ≤ Basic.nn (w k) := by
    have hsub := Core.nn_sub_le_aux (w k) (w k₀)
    have h1 : (1/2) * (1/(5*(Q:ℝ))) ≤ (1/2) * Basic.nn (w k - w k₀) :=
      mul_le_mul_of_nonneg_left hsep' (by norm_num)
    have h2 : (1/2) * Basic.nn (w k - w k₀) ≤ Basic.nn (w k) := by nlinarith [hsub, hmin']
    have h3 : (1/2) * (1/(5*(Q:ℝ))) = 1/(10*(Q:ℝ)) := by ring
    linarith [h1, h2, h3]
  have hS : 2 * Basic.nn (w k) ≤ Basic.S (w k) := Core.two_mul_nn_le_S_aux (w k)
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h1 : 1 ≤ k₀ := (Finset.mem_Icc.mp hk₀).1
    have h2 : k₀ ≤ Q := (Finset.mem_Icc.mp hk₀).2
    have : (0:ℕ) < Q := by omega
    exact_mod_cast this
  rw [h2π k]
  have h4 : (0:ℝ) < 1 / (10 * (Q : ℝ)) := by positivity
  linarith [hnn, hS, h4]


/-! ## The elementary number-theoretic inputs -/

/-- `‖m qₙ α‖ ≤ 1/(10 qₙ)` under the hypothesis `10(|m|+1) qₙ ≤ q(n+1)`. -/
lemma m_Delta_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {m : ℤ}
    (hqpos : ∀ i, 0 < q i) (hΔpos : ∀ i, 0 < Δ i)
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ)) :
    (((m.natAbs : ℕ) : ℝ)) * Δ n ≤ 1 / (10 * (q n : ℝ)) := by
  rcases eq_or_ne m 0 with hm | hm
  · rw [hm]; simp
  · have hR : (10 : ℝ) * (((m.natAbs : ℕ) : ℝ) + 1) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
      have h := hmq hm
      rw [show (|m| : ℤ) = ((m.natAbs : ℕ) : ℤ) from (Int.natCast_natAbs m).symm] at h
      exact_mod_cast h
    have hqn : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
    have hqn1 : (0 : ℝ) < (q (n + 1) : ℝ) := by exact_mod_cast hqpos (n + 1)
    have hbound : (((m.natAbs : ℕ) : ℝ)) * (q n : ℝ) ≤ (q (n + 1) : ℝ) / 10 := by nlinarith
    have hΔn : (0 : ℝ) < Δ n := hΔpos n
    have hΔlt : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
    have hb2 : (((m.natAbs : ℕ) : ℝ)) ≤ (q (n + 1) : ℝ) / (10 * (q n : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 * (q n : ℝ))]
      nlinarith [hbound]
    calc (((m.natAbs : ℕ) : ℝ)) * Δ n ≤ ((q (n + 1) : ℝ) / (10 * (q n : ℝ))) * Δ n :=
          mul_le_mul_of_nonneg_right hb2 (le_of_lt hΔn)
      _ ≤ ((q (n + 1) : ℝ) / (10 * (q n : ℝ))) * (1 / (q (n + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_of_lt hΔlt) (by positivity)
      _ = 1 / (10 * (q n : ℝ)) := by field_simp

/-- Separation of the differences of two sites of the window: `Δ ≥ 1/(2H) - 1/(10 qₙ)`. -/
lemma s0_sep_q1 {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {a m M : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = q (n - 1)) (hHq : H < q n) (h2U : 2 * U ≤ H)
    (hM : M = m * (q n : ℤ))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    {i j : ℤ} (hi : i ∈ W1s0 a U ∪ W2s0 a U H M) (hj : j ∈ W1s0 a U ∪ W2s0 a U H M)
    (hij : i ≠ j) :
    1 / (2 * (H : ℝ)) - 1 / (10 * (q n : ℝ)) ≤ fracDist (((i - j : ℤ) : ℝ) * α) := by
  have hφ := s0phi_injOn (a := a) (M := M) (m := m) (U := U) (H := H) (n := n) (q := q)
    hHq hM
  rw [← image_s0phi (a := a) (M := M) (U := U) (H := H) h2U] at hi hj
  obtain ⟨k, hkI, hk⟩ := Finset.mem_image.mp hi
  obtain ⟨l, hlI, hl⟩ := Finset.mem_image.mp hj
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkI).1
  have hkH : k ≤ H := (Finset.mem_Icc.mp hkI).2
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hlI).1
  have hlH : l ≤ H := (Finset.mem_Icc.mp hlI).2
  have hsep0 := Core.sep_pair hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
    (Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest) (N := n - 1)
  have hbase : ∀ p r : ℕ, p ∈ Finset.Icc 1 H → r ∈ Finset.Icc 1 H → p ≠ r →
      1 / (2 * (H : ℝ)) ≤ fracDist ((((p : ℤ) - (r : ℤ) : ℤ) : ℝ) * α) := by
    intro p r hp hr hpr
    have h := hsep0 p r (Finset.mem_Icc.mp hp).1
      (by rw [← hH]; exact (Finset.mem_Icc.mp hp).2)
      (Finset.mem_Icc.mp hr).1 (by rw [← hH]; exact (Finset.mem_Icc.mp hr).2) hpr
    rwa [← hH] at h
  have hMle : fracDist (((M : ℤ) : ℝ) * α) ≤ 1 / (10 * (q n : ℝ)) := by
    have hm0 := m_Delta_le (α := α) (q := q) (Δ := Δ) (n := n) (m := m) hqpos hΔpos hΔup hmq
    have h1 : fracDist (((m * (q n : ℤ) : ℤ) : ℝ) * α)
        = Basic.nn (((m : ℝ) * ((q n : ℝ) * α))) := by
      rw [Work.TMC16Core.Core.fracDist_eq_nn]
      congr 1; push_cast; ring
    rw [hM, h1]
    calc Basic.nn ((m : ℝ) * ((q n : ℝ) * α))
        ≤ ((m.natAbs : ℕ) : ℝ) * Basic.nn ((q n : ℝ) * α) := Core.nn_intCast_mul_le m _
      _ = (((m.natAbs : ℕ) : ℝ)) * Δ n := by
          rw [show Basic.nn ((q n : ℝ) * α) = Δ n from by rw [hΔeq n]; rfl]
      _ ≤ _ := hm0
  have htri_gen : ∀ A B : ℤ, fracDist ((A : ℝ) * α)
      ≤ fracDist (((A + B : ℤ) : ℝ) * α) + fracDist ((B : ℝ) * α) := by
    intro A B
    rw [Work.TMC16Core.Core.fracDist_eq_nn, Work.TMC16Core.Core.fracDist_eq_nn,
      Work.TMC16Core.Core.fracDist_eq_nn]
    have h := Core.nn_sub_le_aux (((A + B : ℤ) : ℝ) * α) (((B : ℤ) : ℝ) * α)
    have hxy : (((A + B : ℤ) : ℝ) * α) - (((B : ℤ) : ℝ) * α) = ((A : ℝ) * α) := by
      push_cast; ring
    rwa [hxy] at h
  have hBcase : s0c M U k - s0c M U l = 0 ∨ s0c M U k - s0c M U l = M
      ∨ s0c M U k - s0c M U l = -M := by
    by_cases hk2 : k ≤ 2 * U
    · by_cases hl2 : l ≤ 2 * U
      · left; rw [s0c_of_le hk2, s0c_of_le hl2]; ring
      · right; right; rw [s0c_of_le hk2, s0c_of_gt (Nat.lt_of_not_le hl2)]; ring
    · by_cases hl2 : l ≤ 2 * U
      · right; left; rw [s0c_of_gt (Nat.lt_of_not_le hk2), s0c_of_le hl2]; ring
      · left; rw [s0c_of_gt (Nat.lt_of_not_le hk2), s0c_of_gt (Nat.lt_of_not_le hl2)]; ring
  have hBle : fracDist (((s0c M U k - s0c M U l : ℤ) : ℝ) * α) ≤ 1 / (10 * (q n : ℝ)) := by
    rcases hBcase with h | h | h
    · rw [h]
      simp only [Int.cast_zero, zero_mul, Work.TMC16Core.fracDist, round_zero, sub_zero,
        abs_zero]
      positivity
    · rw [h]; exact hMle
    · rw [h]
      have h1 : ((-M : ℤ) : ℝ) * α = -(((M : ℤ) : ℝ) * α) := by push_cast; ring
      rw [h1, Work.TMC16Core.Core.fracDist_neg]
      exact hMle
  have hdiff : ((i - j : ℤ) : ℝ) * α
      = ((((k : ℤ) + s0c M U k) - ((l : ℤ) + s0c M U l) : ℤ) : ℝ) * α := by
    rw [← hk, ← hl]
    unfold s0phi
    push_cast; ring
  rw [hdiff]
  have hpos : (0 : ℝ) ≤ 1 / (10 * (q n : ℝ)) := by positivity
  have hkl : k ≠ l := fun h => hij (by rw [← hk, ← hl, h])
  have hb := hbase k l hkI hlI hkl
  have ht := htri_gen ((k : ℤ) - (l : ℤ)) (s0c M U k - s0c M U l)
  have hcomb : (((k : ℤ) - (l : ℤ)) + (s0c M U k - s0c M U l) : ℤ)
      = (k : ℤ) + s0c M U k - ((l : ℤ) + s0c M U l) := by ring
  rw [hcomb] at ht
  linarith [hb, ht, hBle, hpos]

/-- The phase sums `2θ + (i+j+H-2)α` of the window are separated by `cθ`. -/
lemma s0_theta_le {α θ cθ : ℝ} {q : ℕ → ℕ} {n H U : ℕ} {a m M : ℤ}
    (hθC : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * (H : ℤ) + 8 →
      cθ ≤ fracDist (2 * θ + (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) * α))
    (hM : M = m * (q n : ℤ)) (ha : |a| ≤ 2 * (H : ℤ))
    {k l : ℕ} (hk : k ∈ Finset.Icc 1 H) (hl : l ∈ Finset.Icc 1 H) :
    cθ ≤ fracDist (2 * θ + (((s0phi a M U k + s0phi a M U l + (H : ℤ) - 2 : ℤ)) : ℝ) * α) := by
  have hkH : k ≤ H := (Finset.mem_Icc.mp hk).2
  have hlH : l ≤ H := (Finset.mem_Icc.mp hl).2
  have ha1 : -(2 * (H : ℤ)) ≤ a := (abs_le.mp ha).1
  have ha2 : a ≤ 2 * (H : ℤ) := (abs_le.mp ha).2
  have hj : |2 * a + (k : ℤ) + (l : ℤ) + (H : ℤ) - 4| ≤ 8 * (H : ℤ) + 8 := by
    rw [abs_le]; constructor <;> omega
  have hkey : s0phi a M U k + s0phi a M U l + (H : ℤ) - 2
      = (2 * a + (k : ℤ) + (l : ℤ) + (H : ℤ) - 4) + s0t U k l * m * (q n : ℤ) := by
    rw [s0phi_sum, hM]; ring
  rw [hkey]
  exact hθC (s0t U k l) (s0t_nonneg U k l) (s0t_le_two U k l) _ hj


/-- The difference of the two shifts is `0`, `M` or `-M`. -/
lemma s0c_diff_cases {M : ℤ} {U k l : ℕ} :
    s0c M U k - s0c M U l = 0 ∨ s0c M U k - s0c M U l = M
      ∨ s0c M U k - s0c M U l = -M := by
  by_cases hk2 : k ≤ 2 * U
  · by_cases hl2 : l ≤ 2 * U
    · left; rw [s0c_of_le hk2, s0c_of_le hl2]; ring
    · right; right; rw [s0c_of_le hk2, s0c_of_gt (Nat.lt_of_not_le hl2)]; ring
  · by_cases hl2 : l ≤ 2 * U
    · right; left; rw [s0c_of_gt (Nat.lt_of_not_le hk2), s0c_of_le hl2]; ring
    · left; rw [s0c_of_gt (Nat.lt_of_not_le hk2), s0c_of_gt (Nat.lt_of_not_le hl2)]; ring

/-- Reverse triangle inequality for the distance to `ℤ`: `‖Aα‖ ≤ ‖(A+B)α‖ + ‖Bα‖`. -/
lemma fracDist_add_lower {α : ℝ} (A B : ℤ) :
    fracDist ((A : ℝ) * α) ≤ fracDist (((A + B : ℤ) : ℝ) * α) + fracDist ((B : ℝ) * α) := by
  rw [Work.TMC16Core.Core.fracDist_eq_nn, Work.TMC16Core.Core.fracDist_eq_nn,
    Work.TMC16Core.Core.fracDist_eq_nn]
  have h := Core.nn_sub_le_aux (((A + B : ℤ) : ℝ) * α) (((B : ℤ) : ℝ) * α)
  have hxy : (((A + B : ℤ) : ℝ) * α) - (((B : ℤ) : ℝ) * α) = ((A : ℝ) * α) := by
    push_cast; ring
  rwa [hxy] at h

/-- `‖(s0c k - s0c l) α‖ ≤ 1/(10 qₙ)`. -/
lemma fracDist_s0c_diff_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {m : ℤ} {M : ℤ} {U : ℕ}
    (hqpos : ∀ i, 0 < q i) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hM : M = m * (q n : ℤ)) (k l : ℕ) :
    fracDist (((s0c M U k - s0c M U l : ℤ) : ℝ) * α) ≤ 1 / (10 * (q n : ℝ)) := by
  have hm0 := m_Delta_le (α := α) (q := q) (Δ := Δ) (n := n) (m := m) hqpos hΔpos hΔup hmq
  have hMle : fracDist (((M : ℤ) : ℝ) * α) ≤ 1 / (10 * (q n : ℝ)) := by
    have h1 : fracDist (((m * (q n : ℤ) : ℤ) : ℝ) * α)
        = Basic.nn (((m : ℝ) * ((q n : ℝ) * α))) := by
      rw [Work.TMC16Core.Core.fracDist_eq_nn]
      congr 1; push_cast; ring
    rw [hM, h1]
    calc Basic.nn ((m : ℝ) * ((q n : ℝ) * α))
        ≤ ((m.natAbs : ℕ) : ℝ) * Basic.nn ((q n : ℝ) * α) := Core.nn_intCast_mul_le m _
      _ = (((m.natAbs : ℕ) : ℝ)) * Δ n := by
          rw [show Basic.nn ((q n : ℝ) * α) = Δ n from by rw [hΔeq]; rfl]
      _ ≤ _ := hm0
  rcases s0c_diff_cases (M := M) (U := U) (k := k) (l := l) with h | h | h
  · rw [h]
    simp only [Int.cast_zero, zero_mul, Work.TMC16Core.fracDist, round_zero, sub_zero, abs_zero]
    positivity
  · rw [h]; exact hMle
  · rw [h]
    have h1 : (((-M : ℤ)) : ℝ) * α = -(((M : ℤ) : ℝ) * α) := by push_cast; ring
    rw [h1, Work.TMC16Core.Core.fracDist_neg]
    exact hMle

/-- Separation of the shifted block indices: `‖(k + c k) - (l + c l))α‖ ≥ 1/(5H)`. -/
lemma s0_sep_block {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {m M : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = q (n - 1)) (hHq : H < q n)
    (hM : M = m * (q n : ℤ))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    {k l : ℕ} (hk : k ∈ Finset.Icc 1 H) (hl : l ∈ Finset.Icc 1 H) (hkl : k ≠ l) :
    1 / (5 * (H : ℝ)) ≤
      fracDist ((((k : ℤ) + s0c M U k - ((l : ℤ) + s0c M U l) : ℤ) : ℝ) * α) := by
  have hH1 : 1 ≤ H := le_trans (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hqnpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hbase := Core.sep_pair hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
    (Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest) (N := n - 1)
  have hb : 1 / (2 * (H : ℝ)) ≤ fracDist ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * α) := by
    have h := hbase k l (Finset.mem_Icc.mp hk).1
      (by rw [← hH]; exact (Finset.mem_Icc.mp hk).2)
      (Finset.mem_Icc.mp hl).1 (by rw [← hH]; exact (Finset.mem_Icc.mp hl).2) hkl
    rwa [← hH] at h
  have hBle := fracDist_s0c_diff_le (α := α) (q := q) (Δ := Δ) (n := n) (m := m) (M := M)
    (U := U) hqpos hΔpos hΔeq hΔup hmq hM k l
  have ht := fracDist_add_lower (α := α) ((k : ℤ) - (l : ℤ)) (s0c M U k - s0c M U l)
  have hcomb : (((k : ℤ) - (l : ℤ)) + (s0c M U k - s0c M U l) : ℤ)
      = (k : ℤ) + s0c M U k - ((l : ℤ) + s0c M U l) := by ring
  rw [hcomb] at ht
  have hHqR : (H : ℝ) < (q n : ℝ) := by exact_mod_cast hHq
  have harith : 1 / (5 * (H : ℝ)) ≤ 1 / (2 * (H : ℝ)) - 1 / (10 * (q n : ℝ)) := by
    have h1 : (1 : ℝ) / (10 * (q n : ℝ)) ≤ 3 / (10 * (H : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 10 * (q n : ℝ))
        (by positivity : (0:ℝ) < 10 * (H : ℝ))]
      nlinarith [hHqR]
    have h2 : 1 / (2 * (H : ℝ)) - 3 / (10 * (H : ℝ)) = 1 / (5 * (H : ℝ)) := by ring
    linarith [h1, h2]
  linarith [hb, ht, hBle, harith]


/-- `fracDist(M α) ≤ |m| Δn` for `M = m qₙ`. -/
lemma fracDist_M_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ} {m M : ℤ}
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hM : M = m * (q n : ℤ)) :
    fracDist (((M : ℤ) : ℝ) * α) ≤ (((m.natAbs : ℕ) : ℝ)) * Δ n := by
  have h1 : fracDist (((m * (q n : ℤ) : ℤ) : ℝ) * α)
      = Basic.nn (((m : ℝ) * ((q n : ℝ) * α))) := by
    rw [Work.TMC16Core.Core.fracDist_eq_nn]
    congr 1; push_cast; ring
  rw [hM, h1]
  calc Basic.nn ((m : ℝ) * ((q n : ℝ) * α))
      ≤ ((m.natAbs : ℕ) : ℝ) * Basic.nn ((q n : ℝ) * α) := Core.nn_intCast_mul_le m _
    _ = (((m.natAbs : ℕ) : ℝ)) * Δ n := by
        rw [show Basic.nn ((q n : ℝ) * α) = Δ n from by rw [hΔeq]; rfl]

/-- **The shifted block product bound in the window.**  For every base point `ξ` there is a
minimiser `j₁` of the block with
`|∑_{i ∈ S.erase (φ j₁)} log|sin (π(ξ+iα))| + (H-1)log 2| ≤ 70 log H`. -/
lemma block_sum_bound {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {a m M : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = q (n - 1)) (hHq : H < q n) (hH2 : 2 ≤ H) (h2U : 2 * U ≤ H)
    (hM : M = m * (q n : ℤ))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (ξ : ℝ) :
    ∃ j₁ : ℕ, j₁ ∈ Finset.Icc 1 H ∧
      (∀ j ∈ Finset.Icc 1 H,
        |Real.sin (Real.pi * (ξ + ((s0phi a M U j : ℤ) : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + ((s0phi a M U j₁ : ℤ) : ℝ) * α))|) ∧
      |(∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
            Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
          + ((H : ℝ) - 1) * Real.log 2| ≤ 70 * Real.log H := by
  have hQ : 0 < H := by omega
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hQ
  have hqnpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  -- the minimiser over the block
  have hne : (Finset.Icc 1 H).Nonempty := ⟨1, by simp [Finset.mem_Icc]; omega⟩
  obtain ⟨j₁, hj₁, hj₁min⟩ := Finset.exists_min_image (Finset.Icc 1 H)
    (fun j => |Real.sin (Real.pi * (ξ + ((s0phi a M U j : ℤ) : ℝ) * α))|) hne
  refine ⟨j₁, hj₁, hj₁min, ?_⟩
  -- the base point of the shifted block estimate
  set X : ℝ := (ξ + (((a - 1 : ℤ)) : ℝ) * α) / 2 with hX
  have h2πk : ∀ j : ℕ,
      |Real.sin (2 * Real.pi * (X + ((j : ℝ) + (s0c M U j : ℝ)) * α / 2))|
        = |Real.sin (Real.pi * (ξ + ((s0phi a M U j : ℤ) : ℝ) * α))| := by
    intro j
    rw [hX]
    congr 1
    unfold s0phi
    push_cast
    ring
  have hmin' : ∀ j ∈ Finset.Icc 1 H,
      |Real.sin (2 * Real.pi * (X + ((j : ℝ) + (s0c M U j : ℝ)) * α / 2))| ≥
      |Real.sin (2 * Real.pi * (X + ((j₁ : ℝ) + (s0c M U j₁ : ℝ)) * α / 2))| := by
    intro j hj
    rw [h2πk j, h2πk j₁]
    exact hj₁min j hj
  -- the elementary hypotheses of the shifted block estimate
  have hD : 0 < Δ (n - 1) := hΔpos (n - 1)
  have hDr : 0 < Δ n := hΔpos n
  have happ : |(H : ℝ) * α - ((round ((H : ℝ) * α) : ℤ) : ℝ)| ≤ Δ (n - 1) := by
    have h1 : ((H : ℝ) * α) = ((q (n - 1) : ℕ) : ℝ) * α := by rw [hH]
    show fracDist ((H : ℝ) * α) ≤ Δ (n - 1)
    rw [h1, ← hΔeq (n - 1)]
  have hsep0 := Core.sep_pair hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
    (Core.blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest) (N := n - 1)
  have hsmall2 : (H : ℝ) * Δ (n - 1) < 1 := by
    have h := hΔup (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h
    have h1 : (H : ℝ) * Δ (n - 1) < (H : ℝ) * (1 / (q n : ℝ)) :=
      mul_lt_mul_of_pos_left h hHpos
    have h2 : (H : ℝ) * (1 / (q n : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hqnpos]
      exact_mod_cast hHq
    linarith
  have hsep2 : ∀ k l : ℕ, 1 ≤ k → k ≤ H → 1 ≤ l → l ≤ H → k ≠ l →
      1 / (2 * (H : ℝ)) ≤ fracDist ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * α) := by
    intro k l hk1 hkH hl1 hlH hkl
    have h := hsep0 k l hk1 (by rw [← hH]; exact hkH) hl1 (by rw [← hH]; exact hlH) hkl
    rwa [← hH] at h
  have hcop : Nat.Coprime (round ((H : ℝ) * α)).natAbs H :=
    Core.coprime_sep_gen hQ hD happ hsep2 hsmall2
  have hMle : fracDist (((M : ℤ) : ℝ) * α) ≤ (((m.natAbs : ℕ) : ℝ)) * Δ n :=
    fracDist_M_le (α := α) (q := q) (Δ := Δ) (n := n) (m := m) (M := M) hΔeq hM
  have hsh : ∀ k l : ℕ, 1 ≤ k → k ≤ H → 1 ≤ l → l ≤ H →
      fracDist (((s0c M U k - s0c M U l : ℤ) : ℝ) * α) ≤ (((m.natAbs : ℕ) : ℝ)) * Δ n := by
    intro k l _ _ _ _
    rcases s0c_diff_cases (M := M) (U := U) (k := k) (l := l) with h | h | h
    · rw [h]
      simp only [Int.cast_zero, zero_mul, Work.TMC16Core.fracDist, round_zero, sub_zero, abs_zero]
      have : (0 : ℝ) ≤ (((m.natAbs : ℕ) : ℝ)) * Δ n := by positivity
      exact this
    · rw [h]; exact hMle
    · rw [h]
      have h1 : (((-M : ℤ)) : ℝ) * α = -(((M : ℤ) : ℝ) * α) := by push_cast; ring
      rw [h1, Work.TMC16Core.Core.fracDist_neg]
      exact hMle
  have hm0 := m_Delta_le (α := α) (q := q) (Δ := Δ) (n := n) (m := m) hqpos hΔpos hΔup hmq
  have hHqR : (H : ℝ) < (q n : ℝ) := by exact_mod_cast hHq
  have hsmall : (H : ℝ) * (Δ (n - 1) + (((m.natAbs : ℕ) : ℝ)) * Δ n) ≤ 3 / 2 := by
    have h3 : (H : ℝ) * (1 / (10 * (q n : ℝ))) ≤ 1 / 10 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 10 * (q n : ℝ))]
      nlinarith [hHqR]
    have h4 : (H : ℝ) * ((((m.natAbs : ℕ) : ℝ)) * Δ n) ≤ (H : ℝ) * (1 / (10 * (q n : ℝ))) :=
      mul_le_mul_of_nonneg_left hm0 (le_of_lt hHpos)
    linarith [hsmall2, h4, h3]
  have hsepB : ∀ k l : ℕ, 1 ≤ k → k ≤ H → 1 ≤ l → l ≤ H → k ≠ l →
      1 / (5 * (H : ℝ)) ≤
        fracDist ((((k : ℤ) + s0c M U k - ((l : ℤ) + s0c M U l) : ℤ) : ℝ) * α) := by
    intro k l hk1 hkH hl1 hlH hkl
    have hkI : k ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hk1, hkH⟩
    have hlI : l ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hl1, hlH⟩
    exact s0_sep_block hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hH hHq hM hmq hkI hlI hkl
  -- the shifted block estimate
  have hlem := Work.TMC16Core.Trig.shift_block_relaxed (α := α) (q := H) (Δ := Δ (n - 1))
    (Δr := Δ n) (c := s0c M U) (A := m.natAbs) (p := round ((H : ℝ) * α))
    hQ hD hDr hcop happ hsh hsmall hsepB X hj₁ hmin'
  -- positivity of the removed-block factors
  have hpos : ∀ j ∈ (Finset.Icc 1 H).erase j₁,
      0 < |Real.sin (2 * Real.pi * (X + ((j : ℝ) + (s0c M U j : ℝ)) * α / 2))| :=
    fun j hj => abs_sin_block_pos hsepB hj₁ hmin' (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj)
  have hprod : ∏ j ∈ (Finset.Icc 1 H).erase j₁,
        |Real.sin (2 * Real.pi * (X + ((j : ℝ) + (s0c M U j : ℝ)) * α / 2))|
      = ∏ j ∈ (Finset.Icc 1 H).erase j₁,
        |Real.sin (Real.pi * (ξ + ((s0phi a M U j : ℤ) : ℝ) * α))| :=
    Finset.prod_congr rfl (fun j _ => h2πk j)
  have hlog : Real.log (∏ j ∈ (Finset.Icc 1 H).erase j₁,
        |Real.sin (Real.pi * (ξ + ((s0phi a M U j : ℤ) : ℝ) * α))|)
      = ∑ j ∈ (Finset.Icc 1 H).erase j₁,
        Real.log |Real.sin (Real.pi * (ξ + ((s0phi a M U j : ℤ) : ℝ) * α))| :=
    Real.log_prod (fun j hj => ne_of_gt (by rw [← h2πk j]; exact hpos j hj))
  have hinj : Set.InjOn (s0phi a M U) ↑(Finset.Icc 1 H) :=
    s0phi_injOn (a := a) (M := M) (m := m) (U := U) (H := H) (n := n) (q := q) hHq hM
  have hre := sum_image_erase (φ := s0phi a M U) (H := H) hinj hj₁
    (fun i => Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|)
  rw [hprod] at hlem
  rw [hlog] at hlem
  rw [← hre] at hlem
  exact hlem


/-- The phase `2θ' + (i+j)α` is `2θ + (i+j+H-2)α`. -/
private lemma two_theta'_add {θ α : ℝ} {H : ℕ} {θ' : ℝ}
    (hθ' : θ' = θ + ((H : ℝ) - 2) / 2 * α) (i j : ℤ) :
    2 * θ' + ((i + j : ℤ) : ℝ) * α = 2 * θ + (((i + j + (H : ℤ) - 2 : ℤ)) : ℝ) * α := by
  rw [hθ']; push_cast; ring

theorem s0_uniform_q1 {α θ ε cθ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n H U : ℕ} {a m : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 3 ≤ n) (hH : H = q (n - 1)) (hH2 : 2 ≤ H) (h2U : 2 * U ≤ H)
    (ha : |a| ≤ 2 * (H : ℤ))
    (hmq : m ≠ 0 → 10 * (|m| + 1) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hcθ : 0 < cθ) (hcθ1 : cθ ≤ 1 / 2)
    (hθC : ∀ t : ℤ, 0 ≤ t → t ≤ 2 → ∀ j : ℤ, |j| ≤ 8 * (H : ℤ) + 8 →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (((j + t * m * (q n : ℤ) : ℤ)) : ℝ) * α))
    (hbudget : 300 * Real.log (H : ℝ) + 8 * Real.log (1 / cθ) + 2 * Real.log (2 * (H : ℝ))
      < ((H : ℝ) - 1) * ε) :
    Work.TMC16Core.Uniform ε
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
          Work.TMC16Core.Assembly.W2s0 a U H (m * (q n : ℤ))} =>
        θ + (((j : ℤ) : ℝ) + (((H : ℝ) - 2) / 2)) * α) := by
  set M : ℤ := m * (q n : ℤ) with hM
  set S : Finset ℤ := W1s0 a U ∪ W2s0 a U H M with hS
  set θ' : ℝ := θ + ((H : ℝ) - 2) / 2 * α with hθ'
  have hHq : H < q n := by rw [hH]; exact hmono (by omega)
  have hcard : S.card = H := by
    rw [hS]
    exact card_s0 (a := a) (M := M) (m := m) (U := U) (H := H) (n := n) (q := q) h2U hHq hM
  have hinj : Set.InjOn (s0phi a M U) ↑(Finset.Icc 1 H) :=
    s0phi_injOn (a := a) (M := M) (m := m) (U := U) (H := H) (n := n) (q := q) hHq hM
  have hSimg : S = (Finset.Icc 1 H).image (s0phi a M U) := by
    rw [hS]
    exact (image_s0phi (a := a) (M := M) (U := U) (H := H) h2U).symm
  set csep : ℝ := 1 / (2 * (H : ℝ)) - 1 / (10 * (q n : ℝ)) with hcsep
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    have : (0 : ℕ) < H := by omega
    exact_mod_cast this
  have hHqR : (H : ℝ) < (q n : ℝ) := by exact_mod_cast hHq
  have hcseppos : 0 < csep := by
    rw [hcsep]
    have hqnR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
    have h10 : (0 : ℝ) < 10 * (q n : ℝ) := by linarith
    have h2H : (0 : ℝ) < 2 * (H : ℝ) := by linarith
    have h : (1 : ℝ) / (10 * (q n : ℝ)) < 1 / (2 * (H : ℝ)) := by
      rw [div_lt_div_iff₀ h10 h2H]
      nlinarith [hHqR]
    linarith
  have hsepfun : ∀ i j : ℤ, i ∈ S → j ∈ S → i ≠ j →
      csep ≤ fracDist (((i - j : ℤ) : ℝ) * α) := by
    intro i j hi hj hij
    rw [hcsep]
    rw [hS] at hi hj
    exact s0_sep_q1 (a := a) (M := M) (m := m) (U := U) (H := H) (n := n) (q := q)
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hH hHq h2U hM hmq hi hj hij
  have hmem_iff : ∀ i : ℤ, i ∈ S ↔ ∃ j ∈ Finset.Icc 1 H, s0phi a M U j = i := by
    intro i; rw [hSimg]; exact Finset.mem_image
  -- cosines are distinct
  have hcos : ∀ i : ℤ, i ∈ S → ∀ j : ℤ, j ∈ S → i ≠ j →
      Real.cos (2 * Real.pi * (θ' + (i : ℝ) * α))
        ≠ Real.cos (2 * Real.pi * (θ' + (j : ℝ) * α)) := by
    intro i hi j hj hij hcon
    rw [Real.cos_eq_cos_iff] at hcon
    obtain ⟨k, hk | hk⟩ := hcon
    · have h2 : θ' + (j : ℝ) * α = (k : ℝ) + (θ' + (i : ℝ) * α) := by
        have h4 : (2 * Real.pi) * (θ' + (j : ℝ) * α)
            = (2 * Real.pi) * ((k : ℝ) + (θ' + (i : ℝ) * α)) := by
          linear_combination hk
        exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h4
      have h4 : ((j - i : ℤ) : ℝ) * α = (k : ℝ) := by
        have hexp : (((j - i : ℤ)) : ℝ) * α = (j : ℝ) * α - (i : ℝ) * α := by push_cast; ring
        rw [hexp]
        linarith [h2]
      have h5 : fracDist (((j - i : ℤ) : ℝ) * α) = 0 := by
        rw [h4, Work.TMC16Core.Core.fracDist_intCast]
      have h6 : fracDist (((i - j : ℤ) : ℝ) * α) = 0 := by
        have h7 : (((i - j : ℤ)) : ℝ) * α = -((((j - i : ℤ)) : ℝ) * α) := by push_cast; ring
        rw [h7, Work.TMC16Core.Core.fracDist_neg, h5]
      have h8 := hsepfun i j hi hj hij
      rw [h6] at h8
      linarith [hcseppos, h8]
    · have hdiv : θ' + (j : ℝ) * α = (k : ℝ) - (θ' + (i : ℝ) * α) := by
        have h4 : (2 * Real.pi) * (θ' + (j : ℝ) * α)
            = (2 * Real.pi) * ((k : ℝ) - (θ' + (i : ℝ) * α)) := by
          linear_combination hk
        exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h4
      have h2 : 2 * θ' + ((i + j : ℤ) : ℝ) * α = (k : ℝ) := by
        have hexp : (((i + j : ℤ)) : ℝ) * α = (i : ℝ) * α + (j : ℝ) * α := by push_cast; ring
        rw [hexp]
        linarith [hdiv]
      obtain ⟨ki, hki, hki_eq⟩ := (hmem_iff i).mp hi
      obtain ⟨kj, hkj, hkj_eq⟩ := (hmem_iff j).mp hj
      have hθ'le := s0_theta_le (α := α) (θ := θ) (cθ := cθ) (q := q) (n := n) (H := H)
        (U := U) (a := a) (m := m) (M := M) (hθC := hθC) hM ha hki hkj
      have h9 : 2 * θ' + ((i + j : ℤ) : ℝ) * α
          = 2 * θ + (((s0phi a M U ki + s0phi a M U kj + (H : ℤ) - 2 : ℤ)) : ℝ) * α := by
        rw [← hki_eq, ← hkj_eq]
        exact two_theta'_add hθ' (s0phi a M U ki) (s0phi a M U kj)
      rw [h9] at h2
      have h10 : fracDist (2 * θ + (((s0phi a M U ki + s0phi a M U kj + (H : ℤ) - 2 : ℤ)) : ℝ) * α)
          = 0 := by rw [h2, Work.TMC16Core.Core.fracDist_intCast]
      linarith [hcθ, hθ'le, h10]
  -- the three trigonometric bounds
  have hN : ∀ k : ℤ, k ∈ S → ∀ ξ : ℝ,
      (∀ i ∈ S.erase k, Real.sin (Real.pi * (ξ + (i : ℝ) * α)) ≠ 0) →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -(↑S.card - 1) * Real.log 2 + 70 * Real.log H := by
    intro k hkS ξ hnz
    obtain ⟨j₁, hj₁, hj₁min, hbnd⟩ := block_sum_bound (α := α) (q := q) (Δ := Δ)
      (n := n) (H := H) (U := U) (a := a) (m := m) (M := M)
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hH hHq hH2 h2U hM hmq ξ
    have hkimg : k ∈ (Finset.Icc 1 H).image (s0phi a M U) := by
      rw [← hSimg]; exact hkS
    have hk₀img : s0phi a M U j₁ ∈ (Finset.Icc 1 H).image (s0phi a M U) :=
      Finset.mem_image.mpr ⟨j₁, hj₁, rfl⟩
    have htr : ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase k,
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))| := by
      refine sum_erase_log_le hkimg hk₀img ?_ ?_
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact hj₁min j hj
      · intro i hi hine
        have hmain : i ∈ S.erase k := by
          rw [hSimg]; exact Finset.mem_erase.mpr ⟨hine, hi⟩
        exact abs_pos.mpr (hnz i hmain)
    have hb : ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
          Real.log |Real.sin (Real.pi * (ξ + (i : ℝ) * α))|
        ≤ -(((H : ℝ) - 1) * Real.log 2) + 70 * Real.log H := by
      have h := (abs_le.mp hbnd).2
      linarith [h]
    rw [← hSimg] at hb htr
    rw [hcard]
    linarith [htr, hb]
  have hD1 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (2 * θ' + ((i + k : ℤ) : ℝ) * α))|
        ≥ -(↑S.card - 1) * Real.log 2 - 70 * Real.log H + 2 * Real.log (2 * cθ) := by
    intro k hkS
    obtain ⟨kk, hkk, hkk_eq⟩ := (hmem_iff k).mp hkS
    set ξ₁ : ℝ := 2 * θ' + (k : ℝ) * α with hξ₁
    obtain ⟨j₁, hj₁, hj₁min, hbnd⟩ := block_sum_bound (α := α) (q := q) (Δ := Δ)
      (n := n) (H := H) (U := U) (a := a) (m := m) (M := M)
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hH hHq hH2 h2U hM hmq ξ₁
    have hkimg : k ∈ (Finset.Icc 1 H).image (s0phi a M U) := by
      rw [← hSimg]; exact hkS
    have hk₀img : s0phi a M U j₁ ∈ (Finset.Icc 1 H).image (s0phi a M U) :=
      Finset.mem_image.mpr ⟨j₁, hj₁, rfl⟩
    have hge : ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase k,
          Real.log |Real.sin (Real.pi * (ξ₁ + (i : ℝ) * α))|
        ≥ ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
          Real.log |Real.sin (Real.pi * (ξ₁ + (i : ℝ) * α))| + Real.log (2 * cθ) := by
      refine sum_erase_log_ge (c := cθ) hkimg hk₀img hcθ ?_ ?_
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        have hlt := s0_theta_le (α := α) (θ := θ) (cθ := cθ) (q := q) (n := n) (H := H)
          (U := U) (a := a) (m := m) (M := M) (hθC := hθC) hM ha hj hkk
        have harg : Real.pi * (ξ₁ + ((s0phi a M U j : ℤ) : ℝ) * α)
            = Real.pi * (2 * θ
                + (((s0phi a M U j + s0phi a M U kk + (H : ℤ) - 2 : ℤ)) : ℝ) * α) := by
          have h1 : ξ₁ + ((s0phi a M U j : ℤ) : ℝ) * α
              = 2 * θ' + (((s0phi a M U j + s0phi a M U kk : ℤ)) : ℝ) * α := by
            rw [hξ₁, ← hkk_eq]
            push_cast; ring
          rw [h1, two_theta'_add hθ' (s0phi a M U j) (s0phi a M U kk)]
        rw [harg]
        calc 2 * cθ ≤ 2 * fracDist (2 * θ
              + (((s0phi a M U j + s0phi a M U kk + (H : ℤ) - 2 : ℤ)) : ℝ) * α) := by
              linarith [hlt]
          _ ≤ |Real.sin (Real.pi * (2 * θ
              + (((s0phi a M U j + s0phi a M U kk + (H : ℤ) - 2 : ℤ)) : ℝ) * α))| :=
              Core.two_mul_fracDist_le_abs_sin _
      · intro i _
        exact Real.abs_sin_le_one _
    have hb : ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
          Real.log |Real.sin (Real.pi * (ξ₁ + (i : ℝ) * α))|
        ≥ -(((H : ℝ) - 1) * Real.log 2) - 70 * Real.log H := by
      have h := (abs_le.mp hbnd).1
      linarith [h]
    have hsum : ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (2 * θ' + ((i + k : ℤ) : ℝ) * α))|
        = ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (ξ₁ + (i : ℝ) * α))| := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show Real.pi * (2 * θ' + ((i + k : ℤ) : ℝ) * α)
            = Real.pi * (ξ₁ + (i : ℝ) * α) from by rw [hξ₁]; push_cast; ring]
    rw [hsum]
    rw [← hSimg] at hb hge
    rw [hcard]
    have hlogc : 2 * Real.log (2 * cθ) ≤ Real.log (2 * cθ) := by
      have h : Real.log (2 * cθ) ≤ 0 :=
        Real.log_nonpos (by linarith) (by linarith)
      linarith
    linarith [hge, hb, hlogc]
  have hD2 : ∀ k : ℤ, k ∈ S →
      ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        ≥ -(↑S.card - 1) * Real.log 2 - 70 * Real.log H + Real.log (2 * csep) := by
    intro k hkS
    obtain ⟨kk, hkk, hkk_eq⟩ := (hmem_iff k).mp hkS
    set ξ₂ : ℝ := -(k : ℝ) * α with hξ₂
    obtain ⟨j₁, hj₁, hj₁min, hbnd⟩ := block_sum_bound (α := α) (q := q) (Δ := Δ)
      (n := n) (H := H) (U := U) (a := a) (m := m) (M := M)
      hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hH hHq hH2 h2U hM hmq ξ₂
    have hkimg : k ∈ (Finset.Icc 1 H).image (s0phi a M U) := by
      rw [← hSimg]; exact hkS
    have hk₀img : s0phi a M U j₁ ∈ (Finset.Icc 1 H).image (s0phi a M U) :=
      Finset.mem_image.mpr ⟨j₁, hj₁, rfl⟩
    have hgk : Real.log |Real.sin (Real.pi * (ξ₂ + (k : ℝ) * α))| = 0 := by
      rw [hξ₂]
      have hz : Real.pi * (-(k : ℝ) * α + (k : ℝ) * α) = 0 := by ring
      rw [hz, Real.sin_zero, abs_zero, Real.log_zero]
    have hgφ : Real.log |Real.sin (Real.pi * (ξ₂ + ((s0phi a M U j₁ : ℤ) : ℝ) * α))| = 0 := by
      have h1 : |Real.sin (Real.pi * (ξ₂ + ((s0phi a M U j₁ : ℤ) : ℝ) * α))|
          ≤ |Real.sin (Real.pi * (ξ₂ + (k : ℝ) * α))| := by
        have := hj₁min kk hkk
        rw [hkk_eq] at this
        exact this
      have h2 : |Real.sin (Real.pi * (ξ₂ + (k : ℝ) * α))| = 0 := by
        rw [hξ₂]
        have hz : Real.pi * (-(k : ℝ) * α + (k : ℝ) * α) = 0 := by ring
        rw [hz, Real.sin_zero, abs_zero]
      have hnn : 0 ≤ |Real.sin (Real.pi * (ξ₂ + ((s0phi a M U j₁ : ℤ) : ℝ) * α))| :=
        abs_nonneg _
      have h3 : |Real.sin (Real.pi * (ξ₂ + ((s0phi a M U j₁ : ℤ) : ℝ) * α))| = 0 := by
        linarith [h1, h2, hnn]
      rw [h3, Real.log_zero]
    have hb : ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
          Real.log |Real.sin (Real.pi * (ξ₂ + (i : ℝ) * α))|
        ≥ -(((H : ℝ) - 1) * Real.log 2) - 70 * Real.log H := by
      have h := (abs_le.mp hbnd).1
      linarith [h]
    have heq : ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase (s0phi a M U j₁),
          Real.log |Real.sin (Real.pi * (ξ₂ + (i : ℝ) * α))|
        = ∑ i ∈ ((Finset.Icc 1 H).image (s0phi a M U)).erase k,
          Real.log |Real.sin (Real.pi * (ξ₂ + (i : ℝ) * α))| := by
      rw [Finset.sum_erase_eq_sub hk₀img, Finset.sum_erase_eq_sub hkimg, hgφ, hgk]
    rw [heq] at hb
    have hsum : ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|
        = ∑ i ∈ S.erase k, Real.log |Real.sin (Real.pi * (ξ₂ + (i : ℝ) * α))| := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show Real.pi * (((i - k : ℤ)) : ℝ) * α = Real.pi * (ξ₂ + (i : ℝ) * α) from by
        rw [hξ₂]; push_cast; ring]
    rw [hsum]
    rw [← hSimg] at hb
    rw [hcard]
    have hlogsep2 : Real.log (2 * csep) ≤ 0 := by
      refine Real.log_nonpos (by linarith [hcseppos]) ?_
      rw [hcsep]
      have h2c : 2 * (1 / (2 * (H:ℝ)) - 1 / (10 * (q n:ℝ))) = 1/(H:ℝ) - 1/(5*(q n:ℝ)) := by ring
      rw [h2c]
      have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast (by omega : 1 ≤ H)
      have h1H : 1/(H:ℝ) ≤ 1 := by
        rw [div_le_one hHpos]; linarith
      have hnn : 0 ≤ 1/(5*(q n:ℝ)) := by positivity
      linarith
    linarith [hb, hlogsep2]
  -- the budget
  have hbud : 2 * (70 * Real.log H) + 70 * Real.log H + 70 * Real.log H
      + 2 * Real.log (1 / (2 * cθ)) + Real.log (1 / (2 * csep)) < (↑S.card - 1) * ε := by
    rw [hcard]
    have hqnR : (0 : ℝ) < (q n : ℝ) := by linarith [hHqR]
    have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogc : 0 < Real.log (1 / cθ) := by
      have hone : (1 : ℝ) < 1 / cθ := by
        rw [lt_div_iff₀ hcθ]
        linarith
      exact Real.log_pos hone
    have hlogcθ : 2 * Real.log (1 / (2 * cθ)) = 2 * Real.log (1 / cθ) - 2 * Real.log 2 := by
      have hx0 : (1 / cθ) ≠ 0 := by rw [one_div]; exact inv_ne_zero (ne_of_gt hcθ)
      rw [show (1 : ℝ) / (2 * cθ) = (1 / cθ) / 2 from by ring]
      rw [Real.log_div hx0 (by norm_num)]
      ring
    have hlog2H : Real.log (2 * (H : ℝ)) = Real.log 2 + Real.log (H : ℝ) :=
      Real.log_mul (by norm_num) (by positivity)
    have h2c : 2 * (1 / (2 * (H:ℝ)) - 1 / (10 * (q n:ℝ))) = 1/(H:ℝ) - 1/(5*(q n:ℝ)) := by ring
    have hlt : 1/(5*(q n:ℝ)) < 1/(H:ℝ) := by
      rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 5*(q n:ℝ)) hHpos]
      linarith [hHqR]
    have h1 : 1 / (2 * csep) ≤ 5 / 4 * (H : ℝ) := by
      rw [hcsep, h2c]
      have h2cpos : (0:ℝ) < 1/(H:ℝ) - 1/(5*(q n:ℝ)) := by linarith
      rw [div_le_iff₀ h2cpos]
      have hexp : (5/4*(H:ℝ)) * (1/(H:ℝ) - 1/(5*(q n:ℝ))) = 5/4 - (1/(5*(q n:ℝ)))*(H:ℝ)*(5/4) := by
        field_simp
      rw [hexp]
      have h5 : (1/(5*(q n:ℝ)))*(H:ℝ) ≤ 1/5 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 5*(q n:ℝ))]
        linarith [hHqR]
      linarith
    have hlogsep : Real.log (1 / (2 * csep)) ≤ Real.log (H : ℝ) + Real.log (5 / 4) := by
      calc Real.log (1/(2*csep)) ≤ Real.log (5/4 * (H:ℝ)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log (5/4) + Real.log (H:ℝ) := Real.log_mul (by norm_num) (by positivity)
        _ = Real.log (H:ℝ) + Real.log (5/4) := by ring
    have hkey : 2 * (70 * Real.log H) + 70 * Real.log H + 70 * Real.log H
        + 2 * Real.log (1 / (2 * cθ)) + Real.log (1 / (2 * csep))
        ≤ 300 * Real.log (H : ℝ) + 8 * Real.log (1 / cθ) + 2 * Real.log (2 * (H : ℝ)) := by
      rw [hlogcθ, hlog2H]
      have h54 : Real.log (5 / 4) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
      nlinarith [hlogsep, hlogH, hlogc, hlog2, h54]
    exact lt_of_le_of_lt hkey hbudget
  -- assemble
  have hmain := uniform_of_sum_bounds_gen (S := S) (α := α) (θ := θ') (ε := ε) (cθ := cθ)
    (csep := csep) (A := 70 * Real.log H) (B := 70 * Real.log H) (C := 70 * Real.log H)
    hcos hN hD1 hD2 hcθ hcseppos hbud
  have hfun : (fun p : {p : ℤ // p ∈ S} => θ' + (p : ℝ) * α)
      = (fun p : {p : ℤ // p ∈ S} => θ + (((p : ℤ) : ℝ) + ((H : ℝ) - 2) / 2) * α) := by
    funext p
    rw [hθ']
    ring
  rw [hfun] at hmain
  rw [hS, hM] at hmain
  exact hmain

end

end Work.TMC16Core.Assembly
