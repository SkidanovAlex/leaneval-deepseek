/-
# `Work.FTS.LocData.ZfarPointwise` — the two weighted pointwise bounds for `zfar L F_*`

`zfar L F_* = (1 - χ(·/L))·F_*` is the product of the `z`-only cut-off factor `G` and the
profile `F_* = Fstar α`.  Here we bound, for `z ≥ 1` (where `w(z) = (1+z)²/z²` is harmless),

* `|D_z^i(zfar L F_*) · w| ≤ 64·Kc·α·Γ/z` for `i ≤ 4` (`ZfarDzIterBound`),
* `|D_z^j D_θ^i(zfar L F_*) · w| ≤ 6400000·Kc·α·Γ/z` for `1 ≤ i`, `i + j ≤ 4`
  (`ZfarMixedBound`),

where `Kc` is any uniform bound for the iterated `D_z`-derivatives of the far factor
`1 - χ(·/L)` (available with `Kc ≥ 1` from `ZFBase.DzIter_oneSubChi_bound_uniform`).

Both proofs are the same: expand the `D_z`-iterate by the (binomial) Leibniz rule
`DzIter_mul_smoothQuad` into `∑_b (j.choose b)(D_z^b G · D_z^{j-b}(...))`, bound the first
factor by `Kc` and the second by the weighted derivative bound for the profile
(`ZFBase.DzIter_Fstar_w_le`, `ZFBase.mixed_Fstar_w_le`), and use
`∑_{b ≤ j} (j.choose b) = 2^j ≤ 16` for `j ≤ 4`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ZfarDzIterBound {Kc : ℝ}
    (hKc : ∀ (L : ℝ), 1 ≤ L → ∀ (c : ℕ), c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Kc)
    (hKc1 : 1 ≤ Kc)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (L : ℝ) (hL : 1 ≤ L)
    (z : ℝ) (hz1 : 1 ≤ z) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) (hi : i ≤ 4) :
    |Work.Spaces.DzIter i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      * Work.Spaces.w z| ≤ 64 * Kc * α * Work.Spaces.Gam α θ / z := by
  have hz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (by linarith)
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hzpos : 0 < z := by linarith
  set G0 : ℝ → ℝ := fun z => (1 : ℝ) - Work.Stability.chi (z / L) with hG0
  set G : ℝ → ℝ → ℝ := fun z _ => G0 z with hG
  set F : ℝ → ℝ → ℝ := Work.Construction.Fstar α with hF
  have hfun : Work.Stability.zfar L (Work.Construction.Fstar α) = fun z θ => G z θ * F z θ := by
    funext z θ
    rw [Work.Stability.zfar_apply]
  have hzfar : Work.Spaces.DzIter i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = Work.Spaces.DzIter i (fun z θ => G z θ * F z θ) := by rw [hfun]
  have hleib := Work.FTS.LocData.DzIter_mul_smoothQuad i G F hz
    (ZFBase.contDiffOn_slice_oneSubChi L) (ZFBase.contDiffOn_slice_Fstar α θ)
  rw [hzfar, hleib]
  have hterm : ∀ b ∈ Finset.range (i + 1),
      |(i.choose b : ℝ) * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|
        * |Work.Spaces.w z| ≤ (i.choose b : ℝ) * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb4 : b ≤ 4 := le_trans hbi hi
    have hib4 : i - b ≤ 4 := le_trans (Nat.sub_le i b) hi
    have hc0 : (0 : ℝ) ≤ (i.choose b : ℝ) := Nat.cast_nonneg _
    have hA : |Work.Spaces.DzIter b G z θ| ≤ Kc := hKc L hL b hb4 z hz θ
    have hB : |Work.Spaces.DzIter (i - b) F z θ * Work.Spaces.w z|
        ≤ 4 * α * Work.Spaces.Gam α θ / z := ZFBase.DzIter_Fstar_w_le α hα hα1 hib4 hz1 hθ
    have hBw : |Work.Spaces.DzIter (i - b) F z θ| * |Work.Spaces.w z|
        ≤ 4 * α * Work.Spaces.Gam α θ / z := by simpa only [abs_mul] using hB
    have heq : |(i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|
        * |Work.Spaces.w z|
        = (i.choose b : ℝ) * (|Work.Spaces.DzIter b G z θ|
            * (|Work.Spaces.DzIter (i - b) F z θ| * |Work.Spaces.w z|)) := by
      simp only [abs_mul, abs_of_nonneg hc0]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hA hBw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_trans (by norm_num) hKc1)) hc0
  calc |(∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
        * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)) * Work.Spaces.w z|
      = |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)| * |Work.Spaces.w z| := by
        rw [abs_mul]
    _ ≤ (∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|) * |Work.Spaces.w z| :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ * Work.Spaces.DzIter (i - b) F z θ)|
          * |Work.Spaces.w z| := by
        rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ Finset.range (i + 1),
          (i.choose b : ℝ) * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ i * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
    _ ≤ 64 * Kc * α * Work.Spaces.Gam α θ / z := by
        have h2i : (2 : ℝ) ^ i ≤ 16 := by
          calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hi
            _ = 16 := by norm_num
        have hX : 0 ≤ Kc * (4 * α * Work.Spaces.Gam α θ / z) := by positivity
        calc (2 : ℝ) ^ i * (Kc * (4 * α * Work.Spaces.Gam α θ / z))
            ≤ 16 * (Kc * (4 * α * Work.Spaces.Gam α θ / z)) :=
              mul_le_mul_of_nonneg_right h2i hX
          _ = 64 * Kc * α * Work.Spaces.Gam α θ / z := by ring

theorem ZfarMixedBound {Kc : ℝ}
    (hKc : ∀ (L : ℝ), 1 ≤ L → ∀ (c : ℕ), c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => (1 : ℝ) - Work.Stability.chi (z / L)) z θ| ≤ Kc)
    (hKc1 : 1 ≤ Kc)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (L : ℝ) (hL : 1 ≤ L)
    (z : ℝ) (hz1 : 1 ≤ z) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) (hi : 1 ≤ i) (j : ℕ) (hij : i + j ≤ 4) :
    |Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      * Work.Spaces.w z| ≤ 6400000 * Kc * α * Work.Spaces.Gam α θ / z := by
  have hz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (by linarith)
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hzpos : 0 < z := by linarith
  have hi4 : i ≤ 4 := by omega
  set G0 : ℝ → ℝ := fun z => (1 : ℝ) - Work.Stability.chi (z / L) with hG0
  set G : ℝ → ℝ → ℝ := fun z _ => G0 z with hG
  set F : ℝ → ℝ → ℝ := Work.Construction.Fstar α with hF
  have hfun : Work.Stability.zfar L (Work.Construction.Fstar α) = fun z θ => G z θ * F z θ := by
    funext z θ
    rw [Work.Stability.zfar_apply]
  have hDth : Work.Spaces.DthIter i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = fun z θ => G z θ * Work.Spaces.DthIter i F z θ := by
    rw [hfun]
    exact ZFBase.DthIter_mul_left_z i G0 F
  have hzfar : Work.Spaces.mixed j i (Work.Stability.zfar L (Work.Construction.Fstar α))
      = Work.Spaces.DzIter j (fun z θ => G z θ * Work.Spaces.DthIter i F z θ) := by
    rw [Work.Spaces.mixed, hDth]
  have hleib := Work.FTS.LocData.DzIter_mul_smoothQuad j G
    (fun z θ => Work.Spaces.DthIter i F z θ) hz
    (ZFBase.contDiffOn_slice_oneSubChi L) (ZFBase.contDiffOn_slice_DthIter_Fstar α i θ)
  rw [hzfar, hleib]
  have hterm : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
        * |Work.Spaces.w z|
        ≤ (j.choose b : ℝ) * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb4 : b ≤ 4 := by omega
    have hjb4 : j - b ≤ 4 := le_trans (Nat.sub_le j b) (by omega)
    have hc0 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
    have hA : |Work.Spaces.DzIter b G z θ| ≤ Kc := hKc L hL b hb4 z hz θ
    have hB : |Work.Spaces.mixed (j - b) i (Work.Construction.Fstar α) z θ * Work.Spaces.w z|
        ≤ 400000 * α * Work.Spaces.Gam α θ / z :=
      ZFBase.mixed_Fstar_w_le α hα hα1 hjb4 hi4 hz1 hθ
    have hBw : |Work.Spaces.DzIter (j - b)
          (fun z θ => Work.Spaces.DthIter i F z θ) z θ| * |Work.Spaces.w z|
        ≤ 400000 * α * Work.Spaces.Gam α θ / z := by
      have hB' : |Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter i F) z θ * Work.Spaces.w z|
          ≤ 400000 * α * Work.Spaces.Gam α θ / z := hB
      simpa only [abs_mul] using hB'
    have heq : |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
        * |Work.Spaces.w z|
        = (j.choose b : ℝ) * (|Work.Spaces.DzIter b G z θ|
            * (|Work.Spaces.DzIter (j - b)
                (fun z θ => Work.Spaces.DthIter i F z θ) z θ| * |Work.Spaces.w z|)) := by
      simp only [abs_mul, abs_of_nonneg hc0]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hA hBw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_trans (by norm_num) hKc1)) hc0
  calc |(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Spaces.DzIter b G z θ
          * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ))
        * Work.Spaces.w z|
      = |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
          * |Work.Spaces.w z| := by
        rw [abs_mul]
    _ ≤ (∑ b ∈ Finset.range (j + 1), |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|)
          * |Work.Spaces.w z| :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ b ∈ Finset.range (j + 1), |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b G z θ
            * Work.Spaces.DzIter (j - b) (fun z θ => Work.Spaces.DthIter i F z θ) z θ)|
          * |Work.Spaces.w z| := by
        rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ Finset.range (j + 1),
          (j.choose b : ℝ) * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ j * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 6400000 * Kc * α * Work.Spaces.Gam α θ / z := by
        have h2j : (2 : ℝ) ^ j ≤ 16 := by
          calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 16 := by norm_num
        have hX : 0 ≤ Kc * (400000 * α * Work.Spaces.Gam α θ / z) := by positivity
        calc (2 : ℝ) ^ j * (Kc * (400000 * α * Work.Spaces.Gam α θ / z))
            ≤ 16 * (Kc * (400000 * α * Work.Spaces.Gam α θ / z)) :=
              mul_le_mul_of_nonneg_right h2j hX
          _ = 6400000 * Kc * α * Work.Spaces.Gam α θ / z := by ring

end Work.FTS.LocData
