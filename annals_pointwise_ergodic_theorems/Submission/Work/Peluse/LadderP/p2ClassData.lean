import Mathlib
import Submission.Work.Peluse.LadderP.p2Defs
import Submission.Work.Peluse.LadderP.p2classCard

namespace Work.Peluse.LadderP

open Work.Peluse

/-- Membership in the symmetric window `symIcc N = [-N,N]`, as an absolute-value bound. -/
lemma mem_symIcc_natAbs {N : ℕ} {x : ℤ} : x ∈ symIcc N ↔ x.natAbs ≤ N := by
  rw [symIcc, Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs, Int.ofNat_le]

/-- The preimage `p2Sup c N r` of the residue class `p2Cls c N r` under the dilation
`ξ ↦ r + c ξ` is contained in the window `symIcc (N / c.natAbs + 2)`: if `y ∈ S_r` then
`y = c q + r` with `q = (y - r)/c`, `|q| c = |y - r| ≤ |y| + r ≤ N + (c - 1)`, so that
`|q| ≤ N / c + 1 ≤ N / c + 2`. -/
lemma p2Sup_natAbs_le {c : ℤ} (hc : 0 < c) (N : ℕ) :
    ∀ r : ℕ, r < c.natAbs → ∀ x ∈ p2Sup c N r, x.natAbs ≤ N / c.natAbs + 2 := by
  intro r hr x hx
  rw [p2Sup] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hyN, hymod⟩ := Finset.mem_filter.mp hy
  have hyN' : y.natAbs ≤ N := mem_symIcc_natAbs.mp hyN
  have hcne : c ≠ 0 := ne_of_gt hc
  have hApos : 0 < c.natAbs := by omega
  -- `y ≡ r (mod c)` and `0 ≤ r < c`
  have hrlt : (r : ℤ) < c := by
    have h := Int.emod_lt_of_pos y hc
    rw [← hymod]; exact h
  -- `c * (y / c) = y - r`
  have hyeq : c * (y / c) = y - (r : ℤ) := by
    have h := Int.emod_add_ediv_mul y c
    rw [hymod] at h
    linarith
  -- `(y - r)/c = y/c`
  have hdiv : (y - (r : ℤ)) / c = y / c := by
    conv_lhs => rw [← hyeq]
    rw [Int.mul_ediv_cancel_left (y / c) hcne]
  -- `|(y - r)/c| * c = |y - r|`
  have hmain : ((y - (r : ℤ)) / c).natAbs * c.natAbs = (y - (r : ℤ)).natAbs := by
    rw [hdiv, ← hyeq, Int.natAbs_mul, Nat.mul_comm]
  have hle : (y - (r : ℤ)).natAbs ≤ N + c.natAbs - 1 := by
    have h1 := Int.natAbs_sub_le y (r : ℤ)
    rw [Int.natAbs_natCast] at h1
    omega
  have hA : ((y - (r : ℤ)) / c).natAbs * c.natAbs ≤ N + c.natAbs - 1 := by
    rw [hmain]; exact hle
  have h1 : ((y - (r : ℤ)) / c).natAbs ≤ (N + c.natAbs - 1) / c.natAbs :=
    (Nat.le_div_iff_mul_le hApos).mpr hA
  have h2 : (N + c.natAbs - 1) / c.natAbs ≤ N / c.natAbs + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hApos]
    have hmod := Nat.div_add_mod N c.natAbs
    have hlt := Nat.mod_lt N hApos
    have hN : N ≤ c.natAbs * (N / c.natAbs + 1) := by nlinarith [hmod, hlt]
    omega
  omega

theorem p2ClassData {c : ℤ} (hc : 0 < c) {N M₁ M₂ : ℕ} (hN : 1 ≤ N)
    (hfit : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) (hM : 4 ≤ M₁ * M₂)
    {f : ℤ → ℂ} (hsup : Work.Peluse.SupportIn f N) {r : ℕ}
    (hr : r ∈ Finset.range c.natAbs) :
    Work.Peluse.SupportIn (p2ClsFn c r f) (N / c.natAbs + 2) ∧
      ((2 * (N / c.natAbs + 2) + 1 : ℕ) : ℝ) ≤ 4 * ((p2Cls c N r).card : ℝ) ∧
      1 ≤ N / c.natAbs + 2 := by
  have hr' : r < c.natAbs := Finset.mem_range.mp hr
  have hApos : 0 < c.natAbs := by omega
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hAcast : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
    have h1 : ((c.natAbs : ℕ) : ℤ) = c := by rw [Int.natCast_natAbs, abs_of_pos hc]
    have h2 : (((c.natAbs : ℕ) : ℤ) : ℝ) = ((c : ℤ) : ℝ) := by rw [h1]
    simpa using h2
  -- the real fit `M₁ M₂ ≤ N / c` becomes the integer fit `M₁ M₂ ≤ N / c.natAbs`
  have hmulR : ((M₁ * M₂ : ℕ) : ℝ) * ((c.natAbs : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h : (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) ≤ (N : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hfit hcR.le
      rwa [div_mul_cancel₀ _ hcR.ne'] at h1
    have h2 : ((M₁ * M₂ : ℕ) : ℝ) * ((c.natAbs : ℕ) : ℝ)
        = (M₁ : ℝ) * (M₂ : ℝ) * (c : ℝ) := by
      rw [hAcast]; push_cast; ring
    rw [h2]; exact h
  have hmulN : M₁ * M₂ * c.natAbs ≤ N := by
    rw [← Nat.cast_mul] at hmulR
    exact_mod_cast hmulR
  have hKN : M₁ * M₂ ≤ N / c.natAbs := (Nat.le_div_iff_mul_le hApos).mpr hmulN
  have hd4 : 4 ≤ N / c.natAbs := le_trans hM hKN
  -- the class-cardinality lower bound
  have hlow : (((N / c.natAbs : ℕ)) : ℝ) ≤ ((p2Cls c N r).card : ℝ) := by
    simpa [p2Cls] using (p2classCard hc hN r hr).1
  refine ⟨?_, ?_, ?_⟩
  · -- the class function is supported in `[-N/c-2, N/c+2]`
    intro x hx
    by_contra hf
    have hxmem : x ∈ p2Sup c N r := by
      by_contra h
      exact hf (p2Sup_support hc hr' hsup x h)
    have := p2Sup_natAbs_le hc N r hr' x hxmem
    omega
  · calc ((2 * (N / c.natAbs + 2) + 1 : ℕ) : ℝ)
        ≤ 4 * ((N / c.natAbs : ℕ) : ℝ) := by
          have h : 2 * (N / c.natAbs + 2) + 1 ≤ 4 * (N / c.natAbs) := by omega
          exact_mod_cast h
      _ ≤ 4 * ((p2Cls c N r).card : ℝ) :=
          mul_le_mul_of_nonneg_left hlow (by norm_num)
  · omega

end Work.Peluse.LadderP
