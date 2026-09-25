import Mathlib
import Submission.Work.CR.Flat.Cauchy.dbar_schauder_iterate
import Submission.Work.NN.Final.oneshotClosedOnSelf

namespace Work.NN.Core

noncomputable section

open scoped NNReal ENNReal
open Set

open Work.CR.Flat

/-- **Closedness of a `(0,1)`-form on an open polydisc extends to its closure.**

If every component `f j` is `C¹` and the form satisfies the closedness identities
`∂̄_l (f j) = ∂̄_j (f l)` on the open polydisc `P(ρ)`, then the same identities hold at every
point of the closure of `P(ρ)`: for fixed `j`, `l` the equality set is closed (both sides are
continuous) and contains the (dense) open polydisc. -/
theorem Work.NN.Core.closedOnClosure_of_closedOn_polydisc {n : ℕ} {c : Fin n → ℂ} {ρ : Fin n → ℝ}
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ (1 : WithTop ℕ∞) (f j))
    (h : ∀ j l z, z ∈ polydisc c ρ → dbarCoord l (f j) z = dbarCoord j (f l) z) :
    ∀ j l z, z ∈ closure (polydisc c ρ) →
      dbarCoord l (f j) z = dbarCoord j (f l) z := by
  intro j l z hz
  have hcont₁ : Continuous (fun z : Fin n → ℂ => dbarCoord l (f j) z) := by
    rw [Polydisc.dbarCoord_eq_comp l (f j)]
    exact (Polydisc.dbarCoordPhi l).continuous.comp ((hf j).continuous_fderiv (by simp))
  have hcont₂ : Continuous (fun z : Fin n → ℂ => dbarCoord j (f l) z) := by
    rw [Polydisc.dbarCoord_eq_comp j (f l)]
    exact (Polydisc.dbarCoordPhi j).continuous.comp ((hf l).continuous_fderiv (by simp))
  exact closure_minimal (fun y hy => h j l y hy) (isClosed_eq hcont₁ hcont₂) hz

/-- The increasing sequence of multi-radii
`s m j = ρmax j - (ρmax j - r j / 2) · 2^{-m}`.  It starts at `r / 2` and increases to `ρmax`,
so it gives room to run the one-step (interior Schauder) estimate finitely many times
between the two polydiscs. -/
private def sseq {n : ℕ} (r0 ρmax : Fin n → ℝ) (m : ℕ) : Fin n → ℝ :=
  fun j => ρmax j - (ρmax j - r0 j) * (1 / 2 : ℝ) ^ m

private lemma sseq_zero {n : ℕ} (r0 ρmax : Fin n → ℝ) :
    sseq r0 ρmax 0 = r0 := by
  funext j
  simp [sseq]

private lemma sseq_lt {n : ℕ} {r0 ρmax : Fin n → ℝ} (hd : ∀ j, 0 < ρmax j - r0 j)
    (m : ℕ) (j : Fin n) : sseq r0 ρmax m j < sseq r0 ρmax (m + 1) j := by
  have hp : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
  have h2 : (1 / 2 : ℝ) ^ (m + 1) = (1 / 2 : ℝ) ^ m * (1 / 2) := pow_succ _ _
  simp only [sseq, h2]
  nlinarith [hd j, hp]

private lemma sseq_pos {n : ℕ} {r0 ρmax : Fin n → ℝ} (hd : ∀ j, 0 < ρmax j - r0 j)
    (hr : ∀ j, 0 < r0 j) (m : ℕ) (j : Fin n) : 0 < sseq r0 ρmax m j := by
  have hp : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [sseq]
  nlinarith [hd j, hr j, hp]

private lemma sseq_le {n : ℕ} {r0 ρmax : Fin n → ℝ} (hd : ∀ j, 0 < ρmax j - r0 j)
    (m : ℕ) (j : Fin n) : sseq r0 ρmax m j ≤ ρmax j := by
  have hp : 0 ≤ (1 / 2 : ℝ) ^ m := pow_nonneg (by norm_num) m
  simp only [sseq]
  nlinarith [hd j, hp]

/-- **The iterated interior Schauder estimate**, given the one-step estimate at every order in the
form needed here: the one-step estimate at step `m` relates the `C^{k-m+1,α}`-norm of `u` on
`P(sseq m)` to the `C^{k-m,α}`-norms of the data on `P(sseq (m+1))`, and only requires the
`(0,1)`-form `f` to be closed on the *closure* of the outer polydisc `P(sseq (m+1))`, not
globally. -/
private theorem iterate_of_oneshot {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r0 ρmax r : Fin n → ℝ}
    (hr0 : ∀ j, 0 < r0 j) (hmax : ∀ j, r0 j < ρmax j) (hmaxr : ∀ j, ρmax j < r j)
    {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (k : ℕ)
    (hone : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
        ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) u →
        (∀ j, ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) (f j)) →
        (∀ j l z, z ∈ closure (polydisc c (sseq r0 ρmax (m + 1))) →
          dbarCoord l (f j) z = dbarCoord j (f l) z) →
        (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < sseq r0 ρmax (m + 1) i) →
          dbarCoord j u z = f j z) →
        holderNorm (k - m + 1) α u (polydisc c (sseq r0 ρmax m))
          ≤ ENNReal.ofReal C *
              ((∑ j, holderNorm (k - m) α (f j) (polydisc c (sseq r0 ρmax (m + 1))))
                + holderNorm (k - m) α u (polydisc c (sseq r0 ρmax (m + 1))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) →
      (∀ j l z, z ∈ closure (polydisc c ρmax) →
        dbarCoord l (f j) z = dbarCoord j (f l) z) →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρmax i) → dbarCoord j u z = f j z) →
      holderNorm (k + 1) α u (polydisc c r0)
        ≤ ENNReal.ofReal C *
            ((∑ j, holderNorm k α (f j) (polydisc c ρmax))
              + (∑ j, holderNorm 0 α (f j) (polydisc c ρmax))
              + holderNorm 0 α u (polydisc c ρmax)) := by
  have hrpos : ∀ j, 0 < r0 j := hr0
  have hdpos : ∀ j, 0 < ρmax j - r0 j := fun j => by linarith [hmax j]
  let G : ℕ → ℝ := fun m => Classical.choose (hone m)
  have hGpos : ∀ m, 0 < G m := fun m => (Classical.choose_spec (hone m)).1
  have hGest : ∀ m : ℕ, ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
      ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) u →
      (∀ j, ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) (f j)) →
      (∀ j l z, z ∈ closure (polydisc c (sseq r0 ρmax (m + 1))) →
        dbarCoord l (f j) z = dbarCoord j (f l) z) →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < sseq r0 ρmax (m + 1) i) →
        dbarCoord j u z = f j z) →
      holderNorm (k - m + 1) α u (polydisc c (sseq r0 ρmax m))
        ≤ ENNReal.ofReal (G m) *
            ((∑ j, holderNorm (k - m) α (f j) (polydisc c (sseq r0 ρmax (m + 1))))
              + holderNorm (k - m) α u (polydisc c (sseq r0 ρmax (m + 1)))) :=
    fun m => (Classical.choose_spec (hone m)).2
  let Cm : ℝ := 1 + ∑ i ∈ Finset.range (k + 1), G i
  have hCmsum : 0 ≤ ∑ i ∈ Finset.range (k + 1), G i :=
    Finset.sum_nonneg fun i _ => (hGpos i).le
  have hCm0 : 0 ≤ Cm := by simp only [Cm]; linarith
  have hCm1 : 1 ≤ Cm := by simp only [Cm]; linarith
  have hCmG : ∀ m ≤ k, G m ≤ Cm := by
    intro m hm
    have h1 : G m ≤ ∑ i ∈ Finset.range (k + 1), G i :=
      Finset.single_le_sum (fun i _ => (hGpos i).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    simp only [Cm]; linarith
  let cCm : ℝ≥0∞ := ENNReal.ofReal Cm
  have hcCm1 : 1 ≤ cCm := by
    simp only [cCm]; exact ENNReal.one_le_ofReal.mpr hCm1
  have hcCm_pow : cCm ^ (k + 1) = ENNReal.ofReal (Cm ^ (k + 1)) := by
    simp only [cCm]; exact (ENNReal.ofReal_pow hCm0 (k + 1)).symm
  have hCpos : 0 < Cm ^ (k + 1) * ((k : ℝ) + 1) + 1 := by
    have h1 : (0 : ℝ) ≤ Cm ^ (k + 1) := pow_nonneg hCm0 _
    have h2 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith [mul_nonneg h1 h2]
  refine ⟨Cm ^ (k + 1) * ((k : ℝ) + 1) + 1, hCpos, ?_⟩
  intro u f hu hf hclosed heq
  let S : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (polydisc c ρmax)
  let S0 : ℝ≥0∞ := ∑ j, holderNorm 0 α (f j) (polydisc c ρmax)
  let U : ℝ≥0∞ := holderNorm 0 α u (polydisc c ρmax)
  let X : ℕ → ℝ≥0∞ := fun m => ∑ j, holderNorm (k - m) α (f j) (polydisc c (sseq r0 ρmax (m + 1)))
  let T : ℕ → ℝ≥0∞ := fun m => ∑ t ∈ Finset.range (k + 1 - m), X (m + t)
  -- every intermediate datum is dominated by the top order on the outer polydisc
  have hX_le : ∀ t ≤ k, X t ≤ S := by
    intro t ht
    refine Finset.sum_le_sum fun j _ => ?_
    refine le_trans (holderNorm_mono_k (Nat.sub_le k t) α (f j)
      (polydisc c (sseq r0 ρmax (t + 1)))) ?_
    exact holderNorm_mono_set (isOpen_polydisc c ρmax) (isOpen_polydisc c (sseq r0 ρmax (t + 1)))
      (polydisc_mono fun i => sseq_le hdpos (t + 1) i) k α (f j)
  -- the recursion for the tail sums
  have hT : ∀ m ≤ k, T m = X m + T (m + 1) := by
    intro m hm
    have h1 : k + 1 - m = (k - m) + 1 := by omega
    have h2 : k + 1 - (m + 1) = k - m := by omega
    simp only [T, h1, h2]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [Finset.sum_congr rfl fun t _ => by
      rw [show m + (t + 1) = (m + 1) + t by omega]]
    exact add_comm _ _
  -- the chain of one-step estimates, going down in regularity and up in radius
  have hkey : ∀ m, m ≤ k + 1 → holderNorm (k + 1 - m) α u (polydisc c (sseq r0 ρmax m))
      ≤ cCm ^ (k + 1 - m) * (T m + U) := by
    intro m hm
    refine Nat.decreasingInduction (n := k + 1) (motive := fun m _ =>
      holderNorm (k + 1 - m) α u (polydisc c (sseq r0 ρmax m))
        ≤ cCm ^ (k + 1 - m) * (T m + U)) ?_ ?_ hm
    · intro m hmk' ih
      have hmk : m ≤ k := by omega
      have heq1 : k - m + 1 = k + 1 - m := by omega
      have heq2 : k + 1 - (m + 1) = k - m := by omega
      have hle1 : k - m + 1 ≤ k + 1 := by omega
      have hregu : ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) u := hu.of_le (by exact_mod_cast hle1)
      have hregf : ∀ j, ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) (f j) := fun j =>
        (hf j).of_le (by exact_mod_cast hle1)
      have heq' : ∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < sseq r0 ρmax (m + 1) i) →
          dbarCoord j u z = f j z :=
        fun j z hz => heq j z (fun i => lt_of_lt_of_le (hz i) (sseq_le hdpos (m + 1) i))
      have hcl' : ∀ j l z, z ∈ closure (polydisc c (sseq r0 ρmax (m + 1))) →
          dbarCoord l (f j) z = dbarCoord j (f l) z :=
        fun j l z hz => hclosed j l z
          (closure_mono (polydisc_mono fun i => sseq_le hdpos (m + 1) i) hz)
      have hDm := hGest m u f hregu hregf hcl' heq'
      rw [heq1] at hDm
      have hih : holderNorm (k - m) α u (polydisc c (sseq r0 ρmax (m + 1)))
          ≤ cCm ^ (k - m) * (T (m + 1) + U) := by
        have h := ih
        rw [heq2] at h
        exact h
      have hGle : ENNReal.ofReal (G m) ≤ cCm := by
        simp only [cCm]; exact ENNReal.ofReal_le_ofReal (hCmG m hmk)
      have hpows : cCm ≤ cCm ^ (k - m + 1) := by
        have h := pow_le_pow_right₀ hcCm1 (show 1 ≤ k - m + 1 by omega)
        simpa using h
      calc holderNorm (k + 1 - m) α u (polydisc c (sseq r0 ρmax m))
          ≤ ENNReal.ofReal (G m) * (X m + holderNorm (k - m) α u
              (polydisc c (sseq r0 ρmax (m + 1)))) := hDm
        _ ≤ cCm * (X m + cCm ^ (k - m) * (T (m + 1) + U)) := by
            refine le_trans (mul_le_mul_of_nonneg_right hGle (zero_le : (0 : ℝ≥0∞) ≤ _)) ?_
            exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hih)
              (zero_le : (0 : ℝ≥0∞) ≤ cCm)
        _ = cCm * X m + cCm ^ (k - m + 1) * (T (m + 1) + U) := by
            rw [pow_succ]; ring
        _ ≤ cCm ^ (k - m + 1) * X m + cCm ^ (k - m + 1) * (T (m + 1) + U) := by
            refine add_le_add ?_ le_rfl
            exact mul_le_mul_of_nonneg_right hpows (zero_le : (0 : ℝ≥0∞) ≤ X m)
        _ = cCm ^ (k - m + 1) * (X m + (T (m + 1) + U)) := by ring
        _ = cCm ^ (k - m + 1) * (T m + U) := by
            rw [← add_assoc, ← hT m hmk]
        _ = cCm ^ (k + 1 - m) * (T m + U) := by rw [heq1]
    · -- base: the smallest order, on the largest polydisc
      have h0 : k + 1 - (k + 1) = 0 := by omega
      rw [h0]
      have hT' : T (k + 1) = 0 := by simp [T]
      rw [hT', pow_zero, zero_add, one_mul]
      exact holderNorm_mono_set (isOpen_polydisc c ρmax)
        (isOpen_polydisc c (sseq r0 ρmax (k + 1)))
        (polydisc_mono fun i => sseq_le hdpos (k + 1) i) 0 α u
  -- the tail sum at `0` is bounded by the top-order data
  have hT0 : T 0 ≤ ENNReal.ofReal ((k : ℝ) + 1) * S := by
    have h1 : T 0 = ∑ t ∈ Finset.range (k + 1), X t := by simp [T]
    rw [h1]
    calc ∑ t ∈ Finset.range (k + 1), X t ≤ ∑ _t ∈ Finset.range (k + 1), S :=
          Finset.sum_le_sum fun t ht => hX_le t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * S := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal ((k : ℝ) + 1) * S := by
          rw [← ENNReal.ofReal_natCast (k + 1)]
          congr 1
          push_cast
          ring
  -- comparing the `C^{0,α}` remainder with the top-order data
  have hSU : ENNReal.ofReal ((k : ℝ) + 1) * S + U
      ≤ ENNReal.ofReal ((k : ℝ) + 1) * (S + S0 + U) := by
    have hge1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((k : ℝ) + 1) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
    calc ENNReal.ofReal ((k : ℝ) + 1) * S + U
        ≤ ENNReal.ofReal ((k : ℝ) + 1) * S + ENNReal.ofReal ((k : ℝ) + 1) * U :=
          add_le_add le_rfl (by
            calc U = 1 * U := (one_mul U).symm
              _ ≤ ENNReal.ofReal ((k : ℝ) + 1) * U :=
                  mul_le_mul_of_nonneg_right hge1 (zero_le : (0 : ℝ≥0∞) ≤ U))
      _ = ENNReal.ofReal ((k : ℝ) + 1) * (S + U) := (mul_add _ _ _).symm
      _ ≤ ENNReal.ofReal ((k : ℝ) + 1) * (S + S0 + U) :=
          mul_le_mul_of_nonneg_left (by
            calc S + U ≤ S + (S0 + U) := add_le_add le_rfl (le_add_left le_rfl)
              _ = S + S0 + U := (add_assoc _ _ _).symm) (zero_le : (0 : ℝ≥0∞) ≤ _)
  have hkey0 : holderNorm (k + 1) α u (polydisc c r0)
      ≤ cCm ^ (k + 1) * (T 0 + U) := by
    have h := hkey 0 (Nat.zero_le _)
    simpa [sseq_zero, Nat.sub_zero] using h
  calc holderNorm (k + 1) α u (polydisc c r0)
      ≤ cCm ^ (k + 1) * (T 0 + U) := hkey0
    _ ≤ cCm ^ (k + 1) * (ENNReal.ofReal ((k : ℝ) + 1) * S + U) :=
        mul_le_mul_of_nonneg_left (add_le_add hT0 le_rfl) (zero_le : (0 : ℝ≥0∞) ≤ cCm ^ (k + 1))
    _ ≤ cCm ^ (k + 1) * (ENNReal.ofReal ((k : ℝ) + 1) * (S + S0 + U)) :=
        mul_le_mul_of_nonneg_left hSU (zero_le : (0 : ℝ≥0∞) ≤ cCm ^ (k + 1))
    _ = (cCm ^ (k + 1) * ENNReal.ofReal ((k : ℝ) + 1)) * (S + S0 + U) := by ring
    _ = ENNReal.ofReal (Cm ^ (k + 1) * ((k : ℝ) + 1)) * (S + S0 + U) := by
        have hmul : ENNReal.ofReal (Cm ^ (k + 1)) * ENNReal.ofReal ((k : ℝ) + 1)
            = ENNReal.ofReal (Cm ^ (k + 1) * ((k : ℝ) + 1)) :=
          (ENNReal.ofReal_mul (pow_nonneg hCm0 (k + 1))).symm
        rw [hcCm_pow, hmul]
    _ ≤ ENNReal.ofReal (Cm ^ (k + 1) * ((k : ℝ) + 1) + 1) * (S + S0 + U) :=
        mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one))
          (zero_le : (0 : ℝ≥0∞) ≤ S + S0 + U)

theorem schauderIterateGen {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r0 ρmax r : Fin n → ℝ}
    (hr0 : ∀ j, 0 < r0 j) (hmax : ∀ j, r0 j < ρmax j) (hmaxr : ∀ j, ρmax j < r j) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
        ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc c ρmax →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρmax i) →
          Work.CR.Flat.dbarCoord j u z = f j z) →
        Work.CR.Flat.holderNorm (k + 1) α u (Work.CR.Flat.polydisc c r0) ≤
          ENNReal.ofReal C *
            ((∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc c r))
              + (∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc c r))
              + Work.CR.Flat.holderNorm 0 α u (Work.CR.Flat.polydisc c ρmax)) := by
  have hrpos : ∀ j, 0 < r0 j := hr0
  have hdpos : ∀ j, 0 < ρmax j - r0 j := fun j => by linarith [hmax j]
  have hone : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
        ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) u →
        (∀ j, ContDiff ℝ ((k - m + 1 : ℕ) : ℕ∞) (f j)) →
        (∀ j l z, z ∈ closure (polydisc c (sseq r0 ρmax (m + 1))) →
          dbarCoord l (f j) z = dbarCoord j (f l) z) →
        (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < sseq r0 ρmax (m + 1) i) →
          dbarCoord j u z = f j z) →
        holderNorm (k - m + 1) α u (polydisc c (sseq r0 ρmax m))
          ≤ ENNReal.ofReal C *
              ((∑ j, holderNorm (k - m) α (f j) (polydisc c (sseq r0 ρmax (m + 1))))
                + holderNorm (k - m) α u (polydisc c (sseq r0 ρmax (m + 1)))) :=
    fun m => Work.NN.Final.oneshotClosedOnSelf hn (sseq_lt hdpos m) (sseq_pos hdpos hrpos (m + 1)) hα hα1 (k - m)
  obtain ⟨C, hCpos, hC⟩ := iterate_of_oneshot hn hr0 hmax hmaxr hα hα1 k hone
  refine ⟨C, hCpos, ?_⟩
  intro u f hu hf hcl heq
  have hf1 : ∀ j, ContDiff ℝ (1 : WithTop ℕ∞) (f j) := fun j =>
    (hf j).of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
  have hcl' : ∀ j l z, z ∈ closure (polydisc c ρmax) →
      dbarCoord l (f j) z = dbarCoord j (f l) z :=
    Work.NN.Core.closedOnClosure_of_closedOn_polydisc hf1 (fun j l z hz => (hcl j l z hz).symm)
  have hmain := hC u f hu hf hcl' heq
  have hmono : ∀ j, ρmax j ≤ r j := fun j => le_of_lt (hmaxr j)
  have hS : (∑ j, holderNorm k α (f j) (polydisc c ρmax)) ≤
      (∑ j, holderNorm k α (f j) (polydisc c r)) :=
    Finset.sum_le_sum fun j _ => holderNorm_mono_set (isOpen_polydisc c r)
      (isOpen_polydisc c ρmax) (polydisc_mono hmono) k α (f j)
  have hS0 : (∑ j, holderNorm 0 α (f j) (polydisc c ρmax)) ≤
      (∑ j, holderNorm 0 α (f j) (polydisc c r)) :=
    Finset.sum_le_sum fun j _ => holderNorm_mono_set (isOpen_polydisc c r)
      (isOpen_polydisc c ρmax) (polydisc_mono hmono) 0 α (f j)
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add hS hS0) le_rfl)
    (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal C)

end

end Work.NN.Core
