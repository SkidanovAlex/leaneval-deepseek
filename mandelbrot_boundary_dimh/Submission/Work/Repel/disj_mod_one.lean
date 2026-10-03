import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec

namespace Work.Repel

/-- Purely combinatorial core of `disj_mod_one`: if two points `ζa`, `ζb` have the same
`φ`-images up to a common nonzero factor `s` along the two arithmetic progressions
`ζa - ℕ`, `ζb - ℕ`, and the two sequences `wa`, `wb` are pointwise disjoint on the
positive indices, then `ζa` and `ζb` are not congruent modulo `1`.

Indeed, if `ζa = ζb + k` with `k ≥ 0` then `ζa - (k+1) = ζb - 1`, so `s * wa (k+1) = s * wb 1`;
if `k < 0` then `ζa - 1 = ζb - (1-k)`, so `s * wa 1 = s * wb (1-k)`.  In both cases
cancelling the nonzero `s` contradicts `hwdisj`. -/
lemma disj_mod_one_aux {s : ℂ} (hs : s ≠ 0) {wa wb : ℕ → ℂ}
    (hwdisj : ∀ i j, 1 ≤ i → 1 ≤ j → wa i ≠ wb j)
    {φ : ℂ → ℂ} {ζa ζb : ℂ}
    (hζa : ∀ j : ℕ, φ (ζa - (j : ℂ)) = s * wa j)
    (hζb : ∀ j : ℕ, φ (ζb - (j : ℂ)) = s * wb j) :
    ∀ k : ℤ, ζa ≠ ζb + k := by
  intro k hk
  rcases le_or_gt (0 : ℤ) k with hk0 | hk0
  · -- `0 ≤ k`: translate so that both sides are the same point `ζb - 1`
    have hn : (((k.toNat + 1 : ℕ)) : ℂ) = (k : ℂ) + 1 := by
      have hz : ((k.toNat + 1 : ℕ) : ℤ) = k + 1 := by
        have := Int.toNat_of_nonneg hk0
        omega
      exact_mod_cast hz
    have h1 : ζa - (((k.toNat + 1 : ℕ)) : ℂ) = ζb - ((1 : ℕ) : ℂ) := by
      rw [hn, hk]; push_cast; ring
    have ha := hζa (k.toNat + 1)
    have hb := hζb 1
    rw [h1] at ha
    have heq : wa (k.toNat + 1) = wb 1 := by
      have : s * wa (k.toNat + 1) = s * wb 1 := ha.symm.trans hb
      exact mul_left_cancel₀ hs this
    exact (hwdisj (k.toNat + 1) 1 (by omega) le_rfl) heq
  · -- `k < 0`: translate so that both sides are the same point `ζa - 1`
    set m : ℕ := (1 - k).toNat with hmdef
    have hmc : ((m : ℕ) : ℂ) = 1 - (k : ℂ) := by
      have hz : ((m : ℕ) : ℤ) = 1 - k := by
        rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz
    have h1 : ζa - ((1 : ℕ) : ℂ) = ζb - (m : ℂ) := by
      rw [hmc, hk]; push_cast; ring
    have ha := hζa 1
    have hb := hζb m
    rw [h1] at ha
    have heq : wa 1 = wb m := by
      have : s * wa 1 = s * wb m := ha.symm.trans hb
      exact mul_left_cancel₀ hs this
    have hm1 : 1 ≤ m := by rw [hmdef]; omega
    exact (hwdisj 1 m le_rfl hm1) heq

theorem disj_mod_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (hd : MandelDim.HornData d)
    (d₁ : MandelDim.ParabData (Work.Repel.g0germ d) (Work.Repel.Dg0germ d hd)) (s : ℂ) (hs : s ≠ 0)
    (wa wb : ℕ → ℂ) (hwdisj : ∀ i j, 1 ≤ i → 1 ≤ j → wa i ≠ wb j)
    (ζa ζb : ℂ) (hζa : ∀ j : ℕ, MandelDim.ParabData.φ d₁ (ζa - (j : ℂ)) = s * wa j)
    (hζb : ∀ j : ℕ, MandelDim.ParabData.φ d₁ (ζb - (j : ℂ)) = s * wb j) :
    ∀ k : ℤ, ζa ≠ ζb + k :=
  disj_mod_one_aux hs hwdisj hζa hζb

end Work.Repel
