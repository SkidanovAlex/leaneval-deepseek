import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.scaleCount_le_sqrt
import Submission.Work.KMTAreas.A7rand.logN_scale_bound

/-!
# The small-scale condition is not the narrowness condition

The §7 (small-scale) tuples of area `A7` are indexed by the admissible scales of the index set
`I^{l,s₁,s₂} = {N : max(l₁,l₂), k₁, k₂ ≤ l_{(N)}}`, cut off at the two-scale split
`N ≤ splitCut ρ L = 2^{2^{u}}`, `u = uScale ρ L = ⌊2^{2ρL}⌋`, `L = smallL l₁ l₂ k₁ k₂`.

The *narrow* regime of the tuples is `k₁ + 2u ≤ Log N` (the functional calculus `bn-ident` needs
the frequency window `ℝ_{≤ -Log N + k₁}` of width `2^{k₁}/N` to sit inside the band `ℝ_{≤ -2u}` of
the model symbol).  Within the *small* scales the narrow regime is not guaranteed: it fails exactly
at the *top* of the small range of scales, and this file shows that where it fails both `N` and `L`
are bounded by an explicit constant depending only on `C₀` (and the assumed
`ρ ≤ 1/(4C₀)`).

The mechanism is the exponential gap between the two definitions of the split: the height scale
satisfies `L ≤ l_{(N)} = C₀ LogLog N = C₀ log₂ (R + 2)` with `R = Log N`, so by
`scaleCount_le_sqrt`

  `u = ⌊2^{2ρL}⌋ ≤ 2^{2ρC₀ log₂(R+2)} ≤ (R+2)^{1/2}`   (`2ρC₀ ≤ 1/2`),

while the failure of narrowness together with the index-set bound `k₁ ≤ l_{(N)}` forces

  `R < k₁ + 2u ≤ C₀ log₂ (R+2) + 2 √(R+2)`.

Since `log₂` grows slower than `√·`, this last inequality confines `R` to an explicit range
(`logN_scale_bound`), whence also `N ≤ 2^{R+1}` and `L ≤ C₀ log₂ (R+2)` are bounded.
-/

namespace Work.KMTAreas.A7rand

set_option maxHeartbeats 2000000

/-- **The quantitative core.**  Let `N ≥ 1` be a scale, `R = Log N = Nat.log 2 (max N 2)`,
`L = smallL l₁ l₂ k₁ k₂` and `k₁` both dominated by the height scale `l_{(N)} = heightScale C₀ N`,
and suppose the narrowness inequality `k₁ + 2 · uScale ρ L ≤ R` fails.  Then

* `N ≤ 2 ^ ((8C₀+8)² + 1)`, and
* `L ≤ C₀ · log₂ ((8C₀+8)² + 2)`.

Proof: `L ≤ heightScale C₀ N = C₀ · log₂ (R+2)`, so by `scaleCount_le_sqrt` (which uses
`ρ ≤ 1/(4C₀)`) we get `uScale ρ L ≤ √(R+2)`; the failure of narrowness and `k₁ ≤ heightScale C₀ N`
give `R < C₀ log₂(R+2) + 2√(R+2)`, and `logN_scale_bound` bounds `R`.  The two conclusions are then
immediate from `2^{Log N} ≤ N` resp. from monotonicity of `log₂`. -/
private theorem core (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / (4 * (C₀ : ℝ))) (N L k R : ℕ) (hRdef : R = Nat.log 2 (max N 2))
    (hLle : L ≤ Work.Analysis.EndVar.heightScale C₀ N)
    (hkle : k ≤ Work.Analysis.EndVar.heightScale C₀ N)
    (hlt : R < k + 2 * Work.KMTAreas.A7.uScale ρ L) :
    N ≤ 2 ^ ((8 * C₀ + 8) ^ 2 + 1) ∧ L ≤ C₀ * Nat.log 2 ((8 * C₀ + 8) ^ 2 + 2) := by
  -- `heightScale C₀ N = C₀ · log₂ (R + 2)`
  have hhs : Work.Analysis.EndVar.heightScale C₀ N = C₀ * Nat.log 2 (R + 2) := by
    unfold Work.Analysis.EndVar.heightScale Work.Analysis.EndVar.logLogN
    rw [hRdef]
  have hLle' : L ≤ C₀ * Nat.log 2 (R + 2) := by rw [← hhs]; exact hLle
  have hkle' : k ≤ C₀ * Nat.log 2 (R + 2) := by rw [← hhs]; exact hkle
  -- the scale count is dominated by `√(R+2)`
  have hsc := Work.KMTAreas.A7.scaleCount_le_sqrt ρ C₀ L R hC₀ hρ hρ1 hLle'
  have hsc' : ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) ≤ Real.sqrt ((R : ℝ) + 2) := by
    rw [Real.sqrt_eq_rpow]
    exact hsc
  -- the numerical input `R < C₀ log₂(R+2) + 2√(R+2)`
  have hnum : (R : ℝ) < (C₀ : ℝ) * (Nat.log 2 (R + 2) : ℝ) + 2 * Real.sqrt ((R : ℝ) + 2) := by
    have h1 : (R : ℝ) < (k : ℝ) + 2 * ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) := by
      exact_mod_cast hlt
    have h2 : (k : ℝ) + 2 * ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ)
        ≤ (C₀ : ℝ) * (Nat.log 2 (R + 2) : ℝ) + 2 * Real.sqrt ((R : ℝ) + 2) := by
      have hk' : (k : ℝ) ≤ (C₀ : ℝ) * (Nat.log 2 (R + 2) : ℝ) := by exact_mod_cast hkle'
      have hs' : 2 * ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) ≤ 2 * Real.sqrt ((R : ℝ) + 2) := by
        linarith
      linarith
    linarith
  have hRle : R ≤ (8 * C₀ + 8) ^ 2 := logN_scale_bound C₀ R hC₀ hnum
  constructor
  · -- `2 ^ R ≤ max N 2 < 2 ^ (R+1)`
    have hpow : max N 2 < 2 ^ (R + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
      rw [hRdef]
      simpa only [Nat.succ_eq_add_one] using h
    have hN : N ≤ 2 ^ (R + 1) := le_trans (le_max_left N 2) hpow.le
    exact le_trans hN (Nat.pow_le_pow_right (by norm_num) (by omega))
  · -- `L ≤ C₀ log₂ (R+2) ≤ C₀ log₂ (B+2)`
    have hlog : Nat.log 2 (R + 2) ≤ Nat.log 2 ((8 * C₀ + 8) ^ 2 + 2) :=
      Nat.log_mono_right (by omega)
    calc L ≤ C₀ * Nat.log 2 (R + 2) := hLle'
      _ ≤ C₀ * Nat.log 2 ((8 * C₀ + 8) ^ 2 + 2) := mul_le_mul_right hlog C₀

theorem smallCond_not_narrow_bounded (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / (4 * (C₀ : ℝ))) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ),
      Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n →
      ¬ (k₁ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)
            ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
      Nat.floor (a n) ≤ B ∧ Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ B := by
  refine ⟨max (2 ^ ((8 * C₀ + 8) ^ 2 + 1)) (C₀ * Nat.log 2 ((8 * C₀ + 8) ^ 2 + 2)), ?_⟩
  intro a l₁ l₂ k₁ k₂ n hcond hnot
  -- unpack the small-scale condition
  have hcond' := hcond
  unfold Work.KMTAreas.A7.smallCond Work.Analysis.EndVar.inIndexSet
    Work.KMTAreas.A7.mainRegime at hcond'
  rcases hcond' with ⟨⟨hlmax, hk1, hk2⟩, _, _, _⟩
  -- `(logN N).toNat = Nat.log 2 (max N 2)`
  have hRlog : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      = Nat.log 2 (max (Nat.floor (a n)) 2) := by
    unfold Work.Analysis.EndVar.logN
    simp
  -- the failure of the narrowness inequality, in ℕ
  have hlt : Nat.log 2 (max (Nat.floor (a n)) 2)
      < k₁ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) := by
    have h := hnot
    rw [hRlog] at h
    exact Nat.lt_of_not_le h
  -- the index set dominates `L = smallL l₁ l₂ k₁ k₂` by the height scale
  have hLle : Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂
      ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
    have h : ((Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ : ℕ) : ℤ)
        ≤ ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := by
      unfold Work.KMTAreas.A7.smallL
      simp only [Nat.cast_max]
      exact max_le hlmax (max_le hk1 hk2)
    exact_mod_cast h
  have hkle : k₁ ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
    exact_mod_cast hk1
  obtain ⟨hN, hL⟩ := core C₀ hC₀ ρ hρ hρ1 (Nat.floor (a n))
    (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) k₁ (Nat.log 2 (max (Nat.floor (a n)) 2)) rfl
    hLle hkle hlt
  exact ⟨le_trans hN (le_max_left _ _), le_trans hL (le_max_right _ _)⟩

end Work.KMTAreas.A7rand
