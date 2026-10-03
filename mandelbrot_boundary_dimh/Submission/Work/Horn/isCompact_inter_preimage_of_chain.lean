import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Horn

/-- A compact set covered by an increasing sequence of open sets is contained in one
member of the sequence. -/
theorem exists_subset_of_isCompact_iUnion {V : ℕ → Set ℂ} (hVopen : ∀ n, IsOpen (V n))
    (hmono : ∀ n, V n ⊆ V (n + 1)) {L : Set ℂ} (hLc : IsCompact L) (hL : L ⊆ ⋃ n, V n) :
    ∃ N, L ⊆ V N := by
  have hVmono : Monotone V := monotone_nat_of_le_succ hmono
  obtain ⟨t, ht⟩ := hLc.elim_finite_subcover V hVopen hL
  refine ⟨t.sup id, fun y hy => ?_⟩
  have hy' := ht hy
  simp only [Set.mem_iUnion, exists_prop] at hy'
  obtain ⟨i, hi, hyi⟩ := hy'
  exact hVmono (Finset.le_sup (f := id) hi) hyi

/-- If `G` maps `V (n+1)` injectively onto `V n`, if the `V n` are an increasing open
cover of `B`, and if compact subsets of `V n` have compact preimages intersected with
`V (n+1)`, then compact subsets of `B` have compact preimages intersected with `B`. -/
theorem isCompact_inter_preimage_of_chain {G : ℂ → ℂ} {B L : Set ℂ} {V : ℕ → Set ℂ}
    (hVopen : ∀ n, IsOpen (V n)) (hmono : ∀ n, V n ⊆ V (n+1))
    (hcover : B = ⋃ n, V n)
    (honto : ∀ n, G '' (V (n+1)) = V n)
    (hinj : ∀ n, Set.InjOn G (V (n+1)))
    (hstep : ∀ n, ∀ L : Set ℂ, L ⊆ V n → IsCompact L → IsCompact (V (n+1) ∩ G ⁻¹' L))
    (hLsub : L ⊆ B) (hLc : IsCompact L) :
    IsCompact (B ∩ G ⁻¹' L) := by
  -- Membership in `B` is membership in some `V n`.
  have hB : ∀ x : ℂ, x ∈ B ↔ ∃ n, x ∈ V n := by
    intro x; rw [hcover]; exact Set.mem_iUnion
  -- Since the `V n` are increasing and `B = ⋃ V n`, `G` is injective on all of `B`:
  -- two points of `B` with the same image both lie in a common `V k`, hence in `V (k+1)`.
  have hinjB : Set.InjOn G B := by
    intro x hx y hy hxy
    obtain ⟨m, hm⟩ := (hB x).mp hx
    obtain ⟨m', hm'⟩ := (hB y).mp hy
    have hVmono : Monotone V := monotone_nat_of_le_succ hmono
    exact hinj (max m m')
      (hmono (max m m') (hVmono (le_max_left m m') hm))
      (hmono (max m m') (hVmono (le_max_right m m') hm')) hxy
  -- A compact subset of `B` already sits in one level.
  obtain ⟨N, hN⟩ := exists_subset_of_isCompact_iUnion hVopen hmono hLc (hcover ▸ hLsub)
  -- Key: `B ∩ G ⁻¹' L = V (N+1) ∩ G ⁻¹' L`, because for `x ∈ B` with `G x ∈ L ⊆ V N`
  -- there is `y ∈ V (N+1)` with `G y = G x`, and injectivity on `B` forces `y = x`.
  have hEq : B ∩ G ⁻¹' L = V (N + 1) ∩ G ⁻¹' L := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxB, hxL⟩
      have hGx : G x ∈ V N := hN hxL
      have hmem : G x ∈ G '' V (N + 1) := by rw [honto N]; exact hGx
      rw [Set.mem_image] at hmem
      obtain ⟨y, hyV, hyG⟩ := hmem
      have hyB : y ∈ B := (hB y).mpr ⟨N + 1, hyV⟩
      have hxy : x = y := hinjB hxB hyB (by rw [hyG])
      rw [hxy]
      exact ⟨hyV, by show G y ∈ L; rw [hyG]; exact hxL⟩
    · rintro x ⟨hxV, hxL⟩
      exact ⟨(hB x).mpr ⟨N + 1, hxV⟩, hxL⟩
  rw [hEq]
  exact hstep N L hN hLc

end Work.Horn
