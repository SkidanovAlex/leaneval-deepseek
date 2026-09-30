import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- `IsFam` for the scaled-down family of grid points.  Each grid point `u ∈ Xg` is within
`3H/(2a)` of the position `xf u` of a pair of `S`, and the grid points are `503H/a`-separated;
pairs of `S` have positions `≥ X/(10a)` and their sources `q.1` satisfy `q.1 + H ≤ 10X`.  Then the
positions of the grid points form an `(X/a, H/a)`-family. -/
lemma sdlT_isfam_image {X H a : ℝ} {fam : Finset ℝ} {S : Finset (ℝ × ℕ)}
    {Xg : Finset ℝ} {xf : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (ha : 0 < a)
    (hXg : ∀ u ∈ Xg, ∃ q ∈ S, xf u = q.1 / (q.2 : ℝ))
    (hS : ∀ q ∈ S, q.1 ∈ fam ∧ a ≤ (q.2 : ℝ) ∧ X / (10 * a) ≤ q.1 / (q.2 : ℝ))
    (hfam : ∀ y ∈ fam, y + H ≤ 10 * X)
    (hsep : ∀ u ∈ Xg, ∀ v ∈ Xg, u ≠ v → 503 * H / a ≤ |u - v|)
    (hloc : ∀ u ∈ Xg, |xf u - u| ≤ 3 * H / (2 * a)) :
    Work.BMF.IsFam (X / a) (H / a) (Xg.image xf) := by
  unfold Work.BMF.IsFam
  constructor
  · -- each position `xf u = q.1 / q.2` of a pair `q ∈ S` lies in `[X/(10a), 10X/a - H/a]`
    intro x hx
    obtain ⟨u, huXg, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hqS, hqxf⟩ := hXg u huXg
    obtain ⟨hqfam, hqa, hqpos⟩ := hS q hqS
    have hq2pos : 0 < (q.2 : ℝ) := lt_of_lt_of_le ha hqa
    -- the position is positive, hence so is the source
    have hq1pos : 0 < q.1 := by
      have h : 0 < q.1 / (q.2 : ℝ) := lt_of_lt_of_le (by positivity) hqpos
      have h2 : 0 < q.1 / (q.2 : ℝ) * q.2 := mul_pos h hq2pos
      rwa [div_mul_cancel₀ q.1 (ne_of_gt hq2pos)] at h2
    constructor
    · -- `X/a/10 ≤ q.1/q.2`
      rw [hqxf, show X / a / 10 = X / (10 * a) by ring]
      exact hqpos
    · -- `q.1/q.2 + H/a ≤ 10X/a`
      rw [hqxf, show (10 : ℝ) * (X / a) = 10 * X / a by ring]
      have hle : q.1 / (q.2 : ℝ) ≤ q.1 / a :=
        div_le_div_of_nonneg_left hq1pos.le ha hqa
      have hfamq : q.1 + H ≤ 10 * X := hfam q.1 hqfam
      calc q.1 / (q.2 : ℝ) + H / a ≤ q.1 / a + H / a := add_le_add hle le_rfl
        _ = (q.1 + H) / a := by ring
        _ ≤ 10 * X / a := div_le_div_of_nonneg_right hfamq ha.le
  · -- two distinct positions are at distance at least `503H/a - 3H/a = 500H/a`
    intro x hx y hy hxy
    obtain ⟨u, huXg, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hvXg, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hxy (by rw [h])
    have h1 : |u - xf u| ≤ 3 * H / (2 * a) := by
      rw [abs_sub_comm]; exact hloc u huXg
    have h2 : |xf v - v| ≤ 3 * H / (2 * a) := hloc v hvXg
    have h4 : |u - v| ≤ |u - xf u| + |xf u - v| := abs_sub_le u (xf u) v
    have h5 : |xf u - v| ≤ |xf u - xf v| + |xf v - v| := abs_sub_le (xf u) (xf v) v
    have h8 : 503 * H / a - 3 * H / (2 * a) - 3 * H / (2 * a) ≤ |xf u - xf v| :=
      by linarith [hsep u huXg v hvXg huv, h4, h5, h1, h2]
    have h9 : 503 * H / a - 3 * H / (2 * a) - 3 * H / (2 * a) = 500 * (H / a) := by
      field_simp
      ring
    rw [← h9]
    exact h8

end Work.BMF.SD
