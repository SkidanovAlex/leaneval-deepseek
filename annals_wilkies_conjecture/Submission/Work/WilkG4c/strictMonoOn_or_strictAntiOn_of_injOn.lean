import Mathlib

namespace Work.WilkG4c

/-- **A continuous injective function on an interval is strictly monotone or strictly
antitone.** `K ⊆ ℝ` is order-convex, `f` is continuous at every point of `K` and injective on
`K`; then `f` is either strictly increasing or strictly decreasing on `K`. -/
theorem strictMonoOn_or_strictAntiOn_of_injOn {K : Set ℝ} {f : ℝ → ℝ}
    (hK : K.OrdConnected) (hcont : ∀ x ∈ K, ContinuousAt f x) (hinj : Set.InjOn f K) :
    StrictMonoOn f K ∨ StrictAntiOn f K := by
  by_cases hex : ∃ a ∈ K, ∃ b ∈ K, a < b
  · -- The interesting case: `K` contains two distinct points.
    obtain ⟨a, ha, b, hb, hab⟩ := hex
    -- On any closed subinterval of `K` the (strict) direction of `f` is the same: for every
    -- ordered pair `x < y` in `K`, the comparison `f x < f y` is equivalent to the reference
    -- comparison `f a < f b`.
    have key : ∀ x ∈ K, ∀ y ∈ K, x < y → (f x < f y ↔ f a < f b) := by
      intro x hx y hy hxy
      -- Work on the closed interval `[min a x, max b y]`, which is contained in `K` and
      -- contains all of `a, b, x, y`.
      set L : ℝ := min a x with hL
      set R : ℝ := max b y with hR
      have hLK : L ∈ K := by
        rw [hL]
        rcases min_choice a x with h | h <;> rw [h]
        · exact ha
        · exact hx
      have hRK : R ∈ K := by
        rw [hR]
        rcases max_choice b y with h | h <;> rw [h]
        · exact hb
        · exact hy
      have hLR : L ≤ R := by
        rw [hL, hR]
        exact le_trans (min_le_left a x) (le_trans (le_of_lt hab) (le_max_left b y))
      have hamem : a ∈ Set.Icc L R := by
        refine ⟨?_, ?_⟩
        · rw [hL]; exact min_le_left a x
        · rw [hR]; exact le_trans (le_of_lt hab) (le_max_left b y)
      have hbmem : b ∈ Set.Icc L R := by
        refine ⟨?_, ?_⟩
        · rw [hL]; exact le_trans (min_le_left a x) (le_of_lt hab)
        · rw [hR]; exact le_max_left b y
      have hxmem : x ∈ Set.Icc L R := by
        refine ⟨?_, ?_⟩
        · rw [hL]; exact min_le_right a x
        · rw [hR]; exact le_trans (le_of_lt hxy) (le_max_right b y)
      have hymem : y ∈ Set.Icc L R := by
        refine ⟨?_, ?_⟩
        · rw [hL]; exact le_trans (min_le_right a x) (le_of_lt hxy)
        · rw [hR]; exact le_max_right b y
      have hsub : Set.Icc L R ⊆ K := hK.out' hLK hRK
      have hcont' : ContinuousOn f (Set.Icc L R) :=
        fun z hz => (hcont z (hsub hz)).continuousWithinAt
      have hinj' : Set.InjOn f (Set.Icc L R) := hinj.mono hsub
      -- `f` is strictly monotone or strictly antitone on `[L, R]` by the intermediate value
      -- theorem, and this settles both comparisons at once.
      rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hLR hcont' hinj' with hmono | hanti
      · exact ⟨fun _ => hmono hamem hbmem hab, fun _ => hmono hxmem hymem hxy⟩
      · refine ⟨fun h1 => ?_, fun h2 => ?_⟩
        · exact absurd (hanti hxmem hymem hxy) (not_lt.mpr (le_of_lt h1))
        · exact absurd (hanti hamem hbmem hab) (not_lt.mpr (le_of_lt h2))
    have hne : f a ≠ f b := fun hfab => (ne_of_lt hab) (hinj ha hb hfab)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `f a < f b`: `f` is strictly increasing on `K`.
      left
      intro x hx y hy hxy
      exact (key x hx y hy hxy).2 hlt
    · -- `f b < f a`: `f` is strictly decreasing on `K`.
      right
      intro x hx y hy hxy
      have hxyne : f x ≠ f y := fun hxy' => (ne_of_lt hxy) (hinj hx hy hxy')
      rcases lt_or_gt_of_ne hxyne with h' | h'
      · exact absurd ((key x hx y hy hxy).1 h') (not_lt.mpr (le_of_lt hgt))
      · exact h'
  · -- `K` has at most one point, so both properties hold vacuously.
    push Not at hex
    left
    intro x hx y hy hxy
    exact absurd hxy (not_lt.mpr (hex x hx y hy))

end Work.WilkG4c
