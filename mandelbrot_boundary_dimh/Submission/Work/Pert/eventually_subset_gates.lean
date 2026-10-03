import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.eventually_subset_gates`: the gates swallow a fixed compact eventually.

As `Re (1/α) → +∞`, the two gate regions of §4.2

* `Qm ξ α = Qreg (some (ξ - 1/α)) (some (-ξ))` (the "lower" gate),
* `Qp ξ α = Qreg (some ξ) (some (-ξ + 1/α))` (the "upper" gate),

degenerate to the two limit cones `Qreg none (some (-ξ))` resp. `Qreg (some ξ) none`: the vertex
that depends on `α` (namely `ξ - 1/α` resp. `-ξ + 1/α`) recedes to infinity in the real direction,
so the corresponding `Qreg` condition becomes *vacuous* on any fixed bounded set, while the other
vertice is `∓ξ`, independent of `α`.  Consequently any fixed compact `K` lying in the two limit
cones is eventually contained in both gates.  The proof only needs the compactness to bound
`Re z` on `K`; no covering argument is required.

Membership lemmas for `MandelDim.Qreg` with the `Option` vertices spelled out.
-/

namespace Work.Pert

open MandelDim Complex Set Filter

private lemma mem_Qreg_none_some {z b : ℂ} :
    z ∈ MandelDim.Qreg none (some b) ↔ (z - b).re < |(z - b).im| := by
  simp [MandelDim.Qreg]

private lemma mem_Qreg_some_none {z a : ℂ} :
    z ∈ MandelDim.Qreg (some a) none ↔ -|(z - a).im| < (z - a).re := by
  simp [MandelDim.Qreg]

private lemma mem_Qreg_some_some {z a b : ℂ} :
    z ∈ MandelDim.Qreg (some a) (some b) ↔
      (-|(z - a).im| < (z - a).re ∧ (z - b).re < |(z - b).im|) := by
  simp [MandelDim.Qreg]

/-- **The gates swallow a fixed compact as `Re (1/α) → +∞`.**  If `K` lies in the two limit cones
`Qreg none (some (-ξ))` and `Qreg (some ξ) none`, then `K` is eventually contained in both `Qm ξ α`
and `Qp ξ α` along any filter on which `Re (1/α)` tends to `+∞`. -/
theorem eventually_subset_gates {K : Set ℂ} (hK : IsCompact K) {ξ : ℝ} (hξ : 0 < ξ)
    {ι : Type*} {l : Filter ι} {α : ι → ℂ}
    (hre : ∀ R : ℝ, ∀ᶠ n in l, R ≤ (1 / α n).re)
    (hm : K ⊆ MandelDim.Qreg none (some (-(ξ : ℂ))))
    (hp : K ⊆ MandelDim.Qreg (some (ξ : ℂ)) none) :
    (∀ᶠ n in l, K ⊆ Work.Pert.Qm ξ (α n)) ∧ (∀ᶠ n in l, K ⊆ Work.Pert.Qp ξ (α n)) := by
  have _hξ : 0 ≤ ξ := hξ.le
  -- `Re` is bounded on the compact `K`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ K, |z.re| ≤ C := by
    obtain ⟨a, ha⟩ := hK.image Complex.continuous_re |>.bddAbove
    obtain ⟨b, hb⟩ := hK.image Complex.continuous_re |>.bddBelow
    refine ⟨|a| + |b|, fun z hz => ?_⟩
    have h1 : z.re ≤ a := ha ⟨z, hz, rfl⟩
    have h2 : b ≤ z.re := hb ⟨z, hz, rfl⟩
    exact abs_le.mpr ⟨by linarith [neg_le_abs b, abs_nonneg a],
                      by linarith [le_abs_self a, abs_nonneg b]⟩
  -- `Re (1/α)` is eventually larger than `ξ + C + 1`
  have hb : ∀ᶠ n in l, ξ + C + 1 ≤ (1 / α n).re := hre (ξ + C + 1)
  constructor
  · -- the lower gate `Qm ξ α`: the `α`-dependent vertex `ξ - 1/α` runs to `-∞` in the real part
    filter_upwards [hb] with n hn z hz
    have hzC := hC z hz
    have hmz := (mem_Qreg_none_some.1 (hm hz))
    rw [Work.Pert.Qm, mem_Qreg_some_some]
    refine ⟨?_, by simpa using hmz⟩
    have hpos : 0 < (z - ((ξ : ℂ) - 1 / α n)).re := by
      rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re]
      linarith [neg_abs_le z.re]
    exact lt_of_le_of_lt (neg_nonpos.mpr (abs_nonneg _)) hpos
  · -- the upper gate `Qp ξ α`: the `α`-dependent vertex `-ξ + 1/α` runs to `+∞` in the real part
    filter_upwards [hb] with n hn z hz
    have hzC := hC z hz
    have hpz := (mem_Qreg_some_none.1 (hp hz))
    rw [Work.Pert.Qp, mem_Qreg_some_some]
    refine ⟨by simpa using hpz, ?_⟩
    have hneg : (z - (-(ξ : ℂ) + 1 / α n)).re < 0 := by
      rw [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [le_abs_self z.re]
    exact lt_of_lt_of_le hneg (abs_nonneg _)

end Work.Pert
