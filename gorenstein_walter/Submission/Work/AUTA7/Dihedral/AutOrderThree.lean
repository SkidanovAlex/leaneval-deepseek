import Mathlib

namespace Work.AUTA7.Dihedral

open DihedralGroup

/- Hint: `|MulAut (DihedralGroup 4)| = 8`: an automorphism is determined by the images of the
generators `r 1` (order 4, so `2` choices) and `sr 0` (order 2 outside `⟨r 1⟩`, so `4` choices);
use `MonoidHom.ext`/`Subgroup.closure_le` to show two automorphisms agreeing on `r 1` and `sr 0`
are equal. Hence `orderOf σ ∣ 8` and `orderOf σ ∣ 3` force `σ = 1` (`orderOf_eq_one_iff`). -/
theorem AutOrderThree {σ : MulAut (DihedralGroup 4)} (h : σ ^ 3 = 1) : σ = 1 := by
  -- `σ ^ 3 = 1` means `σ (σ (σ x)) = x` for every `x`.
  have hpow : ∀ x : DihedralGroup 4, σ (σ (σ x)) = x := by
    intro x
    have h' : σ * (σ * σ) = 1 := by rw [pow_three] at h; exact h
    simpa using DFunLike.congr_fun h' x
  -- `(σ (r 1)) ^ 2 ≠ 1`, since `(r 1) ^ 2 = r 2 ≠ 1` and `σ` is injective.
  have h2sq : ((σ (r 1)) : DihedralGroup 4)^2 ≠ 1 := by
    intro hcon
    have h1 : σ (r (2 : ZMod 4)) = 1 := by
      have hr2 : (r (2 : ZMod 4) : DihedralGroup 4) = (r 1) ^ 2 := by
        rw [DihedralGroup.r_one_pow]; simp
      rw [hr2, map_pow, hcon]
    have h2 : (r (2 : ZMod 4) : DihedralGroup 4) = 1 := σ.injective (by rw [h1, map_one])
    exact absurd h2 (by decide)
  -- Step A: `σ` fixes the rotation generator `r 1`.
  have hA : σ (r 1) = r 1 := by
    cases' hval : σ (r 1) with i i
    · -- `σ (r 1) = r i`; `(r i)^2 ≠ 1` forces `i = 1` or `i = 3`.
      have hne : ((r i : DihedralGroup 4))^2 ≠ 1 := by rw [← hval]; exact h2sq
      have hi : i = 1 ∨ i = 3 :=
        (by decide : ∀ i : ZMod 4, ((r i : DihedralGroup 4))^2 ≠ 1 → i = 1 ∨ i = 3) i hne
      rcases hi with hi1 | hi3
      · rw [hi1]
      · -- `i = 3` is impossible: it would give `σ (r 3) = r 1`, whence `σ³ (r 1) = r 3 ≠ r 1`.
        exfalso
        have hval3 : σ (r 1) = (r 3 : DihedralGroup 4) := by rw [hval, hi3]
        have hr3 : σ (r 3) = r 1 := by
          have h3 : (r 3 : DihedralGroup 4) = (r 1) ^ 3 := by
            rw [DihedralGroup.r_one_pow]; simp
          rw [h3, map_pow, hval3]
          decide
        have hcontra : (r 3 : DihedralGroup 4) = r 1 := by
          have hh := hpow (r 1)
          rw [hval3, hr3, hval3] at hh
          exact hh
        exact absurd hcontra (by decide)
    · -- `σ (r 1) = sr i` is impossible since `(sr i) ^ 2 = 1`.
      exfalso
      have hsq : ((sr i : DihedralGroup 4))^2 = 1 := by rw [pow_two, DihedralGroup.sr_mul_self]
      exact h2sq (by rw [hval]; exact hsq)
  -- Step B: `σ` fixes every rotation `r i`.
  have hrot : ∀ i : ZMod 4, σ (r i) = r i := by
    intro i
    have hi : (r i : DihedralGroup 4) = (r 1)^i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    calc σ (r i) = σ ((r 1)^i.val) := by rw [hi]
      _ = (σ (r 1))^i.val := map_pow σ (r 1) i.val
      _ = (r 1)^i.val := by rw [hA]
      _ = r i := by rw [hi]
  -- Step C: the image of the reflection `sr 0` is again a reflection `sr c`.
  obtain ⟨c, hc⟩ : ∃ c : ZMod 4, σ (sr 0) = sr c := by
    cases' hval : σ (sr 0) with i i
    · exfalso
      -- it cannot be a rotation, since `σ` fixes rotations and is injective
      have h1 : σ (sr 0) = σ (r i) := by rw [hval, hrot i]
      have h2 : (sr 0 : DihedralGroup 4) = r i := σ.injective h1
      cases h2
    · exact ⟨i, rfl⟩
  -- Step D: `σ (sr i) = sr (c + i)`.
  have href : ∀ i : ZMod 4, σ (sr i) = sr (c + i) := by
    intro i
    have h1 : (sr i : DihedralGroup 4) = r (-i) * sr 0 := by simp
    calc σ (sr i) = σ (r (-i) * sr 0) := by rw [h1]
      _ = σ (r (-i)) * σ (sr 0) := map_mul σ _ _
      _ = r (-i) * sr c := by rw [hrot (-i), hc]
      _ = sr (c + i) := by rw [DihedralGroup.r_mul_sr, sub_neg_eq_add]
  -- Step E: `σ³ (sr 0) = sr 0` together with Step D forces `c + c + c = 0`, hence `c = 0`.
  have hc0 : c = 0 := by
    have h3 : σ (σ (σ (sr 0))) = sr 0 := hpow _
    rw [hc, href c, href (c + c)] at h3
    exact (by decide : ∀ c : ZMod 4, c + (c + c) = 0 → c = 0) c (DihedralGroup.sr.inj h3)
  have hsr : ∀ i : ZMod 4, σ (sr i) = sr i := by
    intro i; rw [href i, hc0, zero_add]
  -- `σ` agrees with the identity on all elements.
  apply MulEquiv.ext
  intro x
  cases x with
  | r i => simpa using hrot i
  | sr i => simpa using hsr i

end Work.AUTA7.Dihedral
