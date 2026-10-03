import Mathlib
import Submission.Work.Peluse.LadderP.p2Defs
import Submission.Work.Peluse.LadderP.p2classCard

/-!
## The class-fit lemma of the ladder's P2 node

For `c > 0`, `r < c` and `N ≥ 1`, the residue class `S_r = p2Cls c N r` of the window
`symIcc N` and its "support" `p2Sup c N r` (the image of `S_r` under the injective map
`x ↦ (x - r)/c`) satisfy

* `|p2Sup| ≤ |S_r|`,
* `|S_r| ≤ 4 |p2Sup| + 4`,
* and `M₁ M₂ ≤ |S_r|` whenever `M₁ M₂ ≤ N / c` in the reals.

The first two are the standing hypothesis scheme (`T.card ≤ S.card ≤ 4 T.card + 4`) of the
heart `p2Heart` applied with `T = p2Sup c N r` and `S = p2Cls c N r`: here the image map is
*injective on the class*, so in fact the two cardinalities are equal.  The third is the
hypothesis `M₁ M₂ ≤ |S|` of the heart, where the strict (real) fit `M₁ M₂ ≤ N / c` is turned
into the integer division bound `M₁ M₂ ≤ N / c.natAbs`, which the class-cardinality lower bound
`p2classCard` supplies.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The map `x ↦ (x - r)/c` is injective on the residue class `r` modulo `c` (`c ≠ 0`): two members
of the class differ by a multiple of `c`, so their quotients by `c` determine them. -/
lemma p2Sup_card_fit {c : ℤ} (hc : 0 < c) {N r : ℕ} :
    (p2Sup c N r).card = (p2Cls c N r).card := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [p2Sup]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  have hx'' : x ∈ p2Cls c N r := by simpa using hx
  have hy'' : y ∈ p2Cls c N r := by simpa using hy
  obtain ⟨-, hxc⟩ := Finset.mem_filter.mp hx''
  obtain ⟨-, hyc⟩ := Finset.mem_filter.mp hy''
  have hxq : (x - (r : ℤ)) / c = x / c := by
    have h2 := Int.emod_def x c
    rw [hxc] at h2
    have h3 : x - (r : ℤ) = c * (x / c) := by linarith
    rw [h3, Int.mul_ediv_cancel_left (x / c) hcne]
  have hyq : (y - (r : ℤ)) / c = y / c := by
    have h2 := Int.emod_def y c
    rw [hyc] at h2
    have h3 : y - (r : ℤ) = c * (y / c) := by linarith
    rw [h3, Int.mul_ediv_cancel_left (y / c) hcne]
  have hxy' : x / c = y / c := by rw [← hxq, ← hyq]; exact hxy
  have hx1 : x = (x / c) * c + (r : ℤ) := by
    have h := Int.emod_add_ediv_mul x c
    rw [hxc] at h
    linarith
  have hy1 : y = (y / c) * c + (r : ℤ) := by
    have h := Int.emod_add_ediv_mul y c
    rw [hyc] at h
    linarith
  rw [hx1, hy1, hxy']

theorem p2ClassFit {c : ℤ} (hc : 0 < c) {N M₁ M₂ : ℕ} (hN : 1 ≤ N)
    (hfit : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) {r : ℕ}
    (hr : r ∈ Finset.range c.natAbs) :
    (p2Sup c N r).card ≤ (p2Cls c N r).card ∧
      (p2Cls c N r).card ≤ 4 * (p2Sup c N r).card + 4 ∧
      (M₁ : ℝ) * (M₂ : ℝ) ≤ (((p2Cls c N r).card : ℕ) : ℝ) := by
  have hcard : (p2Sup c N r).card = (p2Cls c N r).card := p2Sup_card_fit hc
  -- the class-cardinality lower bound `N / c ≤ |S_r|`
  have hlow : (((N / c.natAbs : ℕ)) : ℝ) ≤ ((p2Cls c N r).card : ℝ) :=
    (p2classCard hc hN r hr).1
  -- the real fit `M₁ M₂ ≤ N / c` with `c` written as `c.natAbs`
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hAcast : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
    have h1 : ((c.natAbs : ℕ) : ℤ) = c := by rw [Int.natCast_natAbs, abs_of_pos hc]
    have h2 : (((c.natAbs : ℕ) : ℤ) : ℝ) = ((c : ℤ) : ℝ) := by rw [h1]
    simpa using h2
  have hApos : 0 < c.natAbs := by omega
  have hmulR : ((M₁ * M₂ : ℕ) : ℝ) * ((c.natAbs : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h : (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) ≤ (N : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hfit hcR.le
      rwa [div_mul_cancel₀ _ hcR.ne'] at h1
    have h2 : ((M₁ * M₂ : ℕ) : ℝ) * ((c.natAbs : ℕ) : ℝ) = (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) := by
      rw [hAcast]; push_cast; ring
    rw [h2]; exact h
  have hmulN : M₁ * M₂ * c.natAbs ≤ N := by
    rw [← Nat.cast_mul] at hmulR
    exact_mod_cast hmulR
  have hKN : M₁ * M₂ ≤ N / c.natAbs := (Nat.le_div_iff_mul_le hApos).mpr hmulN
  have hcast2 : ((M₁ * M₂ : ℕ) : ℝ) ≤ (((N / c.natAbs : ℕ)) : ℝ) := by exact_mod_cast hKN
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · calc (M₁ : ℝ) * (M₂ : ℝ) = ((M₁ * M₂ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((N / c.natAbs : ℕ)) : ℝ) := hcast2
      _ ≤ ((p2Cls c N r).card : ℝ) := hlow

end

end Work.Peluse.LadderP
