import Mathlib

namespace Work.A3

/-- **Band split for a monotone function.**

If `g` is monotone (increasing) on the interval `[a,b]` and `m > 0`, then `[a,b]` splits into a
left part where `g ≤ -m`, a right part where `g ≥ m`, and a middle band where `|g| ≤ m`: there are
`a ≤ p ≤ q ≤ b` with `g x ≤ -m` for `x ∈ (a,p)`, `m ≤ g x` for `x ∈ (q,b)` and `|g x| ≤ m` for
`x ∈ (p,q)`.

The witnesses are `p = inf {x ∈ [a,b] : g x > -m}` and `q = sup {x ∈ [a,b] : g x < m}`
(with the obvious conventions when one of these sets is empty).  Continuity is not needed. -/
lemma exists_band_split_mono {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m) (g : ℝ → ℝ)
    (hcont : ContinuousOn g (Set.Icc a b)) (hmono : MonotoneOn g (Set.Icc a b)) :
    ∃ p q : ℝ, a ≤ p ∧ p ≤ q ∧ q ≤ b ∧
      (∀ x : ℝ, x ∈ Set.Ioo a p → g x ≤ -m) ∧
      (∀ x : ℝ, x ∈ Set.Ioo q b → m ≤ g x) ∧
      (∀ x : ℝ, x ∈ Set.Ioo p q → |g x| ≤ m) := by
  -- continuity is not used: only monotonicity and `0 < m` enter the argument
  have _ : ContinuousOn g (Set.Icc a b) := hcont
  let S : Set ℝ := {x | x ∈ Set.Icc a b ∧ -m < g x}
  let T : Set ℝ := {x | x ∈ Set.Icc a b ∧ g x < m}
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hTbdd : BddAbove T := ⟨b, fun x hx => hx.1.2⟩
  by_cases hSne : S.Nonempty
  · by_cases hTne : T.Nonempty
    · have hs0m : hSne.some ∈ S := hSne.some_mem
      have ht0m : hTne.some ∈ T := hTne.some_mem
      have hSb : sInf S ≤ b := le_trans (csInf_le hSbdd hs0m) hs0m.1.2
      have haT : a ≤ sSup T := le_trans ht0m.1.1 (le_csSup hTbdd ht0m)
      refine ⟨sInf S, sSup T, le_csInf hSne (fun x hx => hx.1.1), ?_,
        csSup_le hTne (fun x hx => hx.1.2), ?_, ?_, ?_⟩
      · -- `inf S ≤ sup T`: otherwise a point strictly between them would lie both outside `S` and
        -- outside `T`, forcing `m ≤ g y ≤ -m`.
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨y, hy1, hy2⟩ := exists_between hcon
        have hyab : y ∈ Set.Icc a b := ⟨le_trans haT hy1.le, le_trans hy2.le hSb⟩
        have hyS : y ∉ S := fun h => absurd (csInf_le hSbdd h) (not_le.mpr hy2)
        have hyT : y ∉ T := fun h => absurd (le_csSup hTbdd h) (not_le.mpr hy1)
        have h1 : g y ≤ -m := by
          by_contra h
          exact hyS ⟨hyab, lt_of_not_ge h⟩
        have h2 : m ≤ g y := by
          by_contra h
          exact hyT ⟨hyab, lt_of_not_ge h⟩
        linarith
      · -- `x ∈ (a, inf S)` implies `x ∉ S`, hence `g x ≤ -m`
        intro x hx
        rw [Set.mem_Ioo] at hx
        have hxb : x ≤ b := le_trans hx.2.le hSb
        have hxS : x ∉ S := fun h => absurd (csInf_le hSbdd h) (not_le.mpr hx.2)
        by_contra h
        exact hxS ⟨⟨le_of_lt hx.1, hxb⟩, lt_of_not_ge h⟩
      · -- `x ∈ (sup T, b)` implies `x ∉ T`, hence `m ≤ g x`
        intro x hx
        rw [Set.mem_Ioo] at hx
        have hax : a ≤ x := le_trans haT hx.1.le
        have hxT : x ∉ T := fun h => absurd (le_csSup hTbdd h) (not_le.mpr hx.1)
        by_contra h
        exact hxT ⟨⟨hax, le_of_lt hx.2⟩, lt_of_not_ge h⟩
      · -- middle band, by monotonicity with the witnesses `z ∈ S`, `w ∈ T`
        intro x hx
        rw [Set.mem_Ioo] at hx
        have hxab : x ∈ Set.Icc a b :=
          ⟨le_trans (le_csInf hSne (fun y hy => hy.1.1)) hx.1.le,
           le_trans hx.2.le (csSup_le hTne (fun y hy => hy.1.2))⟩
        obtain ⟨z, hzS, hzx⟩ := (csInf_lt_iff hSbdd hSne).mp hx.1
        obtain ⟨w, hwT, hxw⟩ := (lt_csSup_iff hTbdd hTne).mp hx.2
        have hlow : -m ≤ g x := le_of_lt (lt_of_lt_of_le hzS.2 (hmono hzS.1 hxab hzx.le))
        have hhigh : g x ≤ m := le_of_lt (lt_of_le_of_lt (hmono hxab hwT.1 hxw.le) hwT.2)
        exact abs_le.mpr ⟨hlow, hhigh⟩
    · -- `T` empty: `g ≥ m` on `[a,b]`, take `p = q = a`
      refine ⟨a, a, le_rfl, le_rfl, hab, ?_, ?_, ?_⟩
      · intro x hx
        rw [Set.mem_Ioo] at hx
        linarith
      · intro x hx
        rw [Set.mem_Ioo] at hx
        exact (by_contra fun h => hTne ⟨x, ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, lt_of_not_ge h⟩⟩ :
          m ≤ g x)
      · intro x hx
        rw [Set.mem_Ioo] at hx
        linarith
  · -- `S` empty: `g ≤ -m` on `[a,b]`, take `p = q = b`
    refine ⟨b, b, hab, le_rfl, le_rfl, ?_, ?_, ?_⟩
    · intro x hx
      rw [Set.mem_Ioo] at hx
      have hxS : x ∉ S := fun h => hSne ⟨x, h⟩
      by_contra h
      exact hxS ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, lt_of_not_ge h⟩
    · intro x hx
      rw [Set.mem_Ioo] at hx
      linarith
    · intro x hx
      rw [Set.mem_Ioo] at hx
      linarith

end Work.A3
