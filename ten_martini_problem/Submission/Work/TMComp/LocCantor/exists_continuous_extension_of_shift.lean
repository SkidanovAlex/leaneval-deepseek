import Mathlib

namespace Work.TMComp.LocCantor

open scoped Topology

set_option linter.unusedVariables false

/-- Iterating the shift relation `f (x + α) = c * f x` along the orbit `x + j α`,
provided none of the points `x + j α` for `j ≤ n` lies in `Z`. -/
lemma shift_iterate {Z : Set ℝ} {α : ℝ} {c : ℂ} {f : ℝ → ℂ}
    (hrel : ∀ x : ℝ, x ∉ Z → x + α ∉ Z → f (x + α) = c * f x)
    (x : ℝ) (n : ℕ) (hx : ∀ j ≤ n, x + (j : ℝ) * α ∉ Z) :
    f (x + (n : ℝ) * α) = c ^ n * f x := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : f (x + (k : ℝ) * α) = c ^ k * f x :=
        ih (fun j hj => hx j (le_trans hj (Nat.le_succ k)))
      have hxx : (x + (k : ℝ) * α) + α = x + ((k + 1 : ℕ) : ℝ) * α := by
        push_cast; ring
      have hstep : f ((x + (k : ℝ) * α) + α) = c * f (x + (k : ℝ) * α) :=
        hrel (x + (k : ℝ) * α) (hx k (Nat.le_succ k)) (by
          rw [hxx]; exact hx (k + 1) le_rfl)
      rw [show x + ((k + 1 : ℕ) : ℝ) * α = (x + (k : ℝ) * α) + α by
            push_cast; ring,
        hstep, hk, ← mul_assoc, ← pow_succ']

theorem exists_continuous_extension_of_shift {Z : Set ℝ} {α : ℝ} {c : ℂ}
    (hα : Irrational α) (hZc : IsClosed Z)
    (hZd : ∀ z ∈ Z, ∃ ε > 0, ∀ y ∈ Z, |y - z| < ε → y = z)
    (hZexit : ∀ z ∈ Z, ∃ K : ℕ, 1 ≤ K ∧ z + (K : ℝ) * α ∉ Z)
    (hc : c ≠ 0) {f : ℝ → ℂ} (hf : ContinuousOn f Zᶜ)
    (hrel : ∀ x : ℝ, x ∉ Z → x + α ∉ Z → f (x + α) = c * f x) :
    ∃ g : ℝ → ℂ, Continuous g ∧ ∀ x ∉ Z, g x = f x := by
  classical
  have hZexit' : ∀ z : ℝ, ∃ K : ℕ, (z ∈ Z → 1 ≤ K) ∧ (z ∈ Z → z + (K : ℝ) * α ∉ Z) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨K, h1, h2⟩ := hZexit z hz
      exact ⟨K, fun _ => h1, fun _ => h2⟩
    · exact ⟨0, fun h => absurd h hz, fun h => absurd h hz⟩
  choose K _hK1 hK2 using hZexit'
  set g : ℝ → ℂ :=
    fun x => if hx : x ∈ Z then (c ^ (K x))⁻¹ * f (x + (K x : ℝ) * α) else f x with hg
  have hg_off : ∀ x, x ∉ Z → g x = f x := by
    intro x hx
    simp only [hg, dif_neg hx]
  refine ⟨g, ?_, hg_off⟩
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ Z
  · -- main case: `z ∈ Z`
    -- Each translate `z + j α` eventually misses `Z` along punctured neighbourhoods of `z`.
    have havoid : ∀ j : ℕ, ∀ᶠ x in 𝓝[≠] z, x + (j : ℝ) * α ∉ Z := by
      intro j
      by_cases hw : z + (j : ℝ) * α ∈ Z
      · obtain ⟨ε, hεpos, hε⟩ := hZd (z + (j : ℝ) * α) hw
        refine Filter.eventually_iff.mpr
          (mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
            ⟨Metric.ball z ε, Metric.ball_mem_nhds z hεpos, ?_⟩)
        intro x hx
        obtain ⟨hxball, hxne⟩ := hx
        rw [Metric.mem_ball, Real.dist_eq] at hxball
        intro hxZ
        have h_eq : x + (j : ℝ) * α = z + (j : ℝ) * α :=
          hε (x + (j : ℝ) * α) hxZ (by
            rw [show (x + (j : ℝ) * α) - (z + (j : ℝ) * α) = x - z by ring]
            exact hxball)
        have hxnez : x ≠ z := by simpa using hxne
        exact hxnez (add_right_cancel h_eq)
      · have hcont : Continuous (fun x : ℝ => x + (j : ℝ) * α) :=
          continuous_id.add_const _
        have hpre : (fun x : ℝ => x + (j : ℝ) * α) ⁻¹' Zᶜ ∈ 𝓝 z :=
          hcont.continuousAt.preimage_mem_nhds (hZc.compl_mem_nhds hw)
        exact Filter.eventually_iff.mpr (mem_nhdsWithin_of_mem_nhds hpre)
    -- Iterating the relation on punctured neighbourhoods.
    have hiter : ∀ n : ℕ, ∀ᶠ x in 𝓝[≠] z,
        (∀ j ≤ n, x + (j : ℝ) * α ∉ Z) ∧ f (x + (n : ℝ) * α) = c ^ n * f x := by
      intro n
      induction n with
      | zero =>
          filter_upwards [havoid 0] with x hx
          constructor
          · intro j hj
            rw [Nat.le_zero.mp hj]
            simpa using hx
          · simp
      | succ k ih =>
          filter_upwards [ih, havoid (k + 1)] with x hk hxk1
          obtain ⟨hkall, -⟩ := hk
          have hnew : ∀ j ≤ k + 1, x + (j : ℝ) * α ∉ Z := by
            intro j hj
            rcases lt_or_eq_of_le hj with hlt | heq
            · exact hkall j (Nat.lt_succ_iff.mp hlt)
            · subst heq; exact hxk1
          exact ⟨hnew, shift_iterate hrel x (k + 1) hnew⟩
    have hpunct : ∀ᶠ x in 𝓝[≠] z, g x = (c ^ (K z))⁻¹ * f (x + (K z : ℝ) * α) := by
      filter_upwards [hiter (K z)] with x hx
      obtain ⟨hav, hfeq⟩ := hx
      have hxZ : x ∉ Z := by simpa using hav 0 (Nat.zero_le (K z))
      rw [hg_off x hxZ, hfeq, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc), one_mul]
    set big : ℝ → ℂ := fun x => (c ^ (K z))⁻¹ * f (x + (K z : ℝ) * α) with hbig
    have hbig_z : big z = g z := by
      simp only [hbig, hg, dif_pos hz]
    have hcontbig : ContinuousAt big z := by
      have hmem : Zᶜ ∈ 𝓝 (z + (K z : ℝ) * α) := hZc.compl_mem_nhds (hK2 z hz)
      have hfat : ContinuousAt f (z + (K z : ℝ) * α) := hf.continuousAt hmem
      have hshift : ContinuousAt (fun x : ℝ => x + (K z : ℝ) * α) z :=
        (continuous_id.add_const _).continuousAt
      have hcomp : ContinuousAt (fun x : ℝ => f (x + (K z : ℝ) * α)) z :=
        hfat.comp (f := fun x : ℝ => x + (K z : ℝ) * α) (x := z) hshift
      exact hcomp.const_mul _
    have hagree : big =ᶠ[𝓝 z] g := by
      show ∀ᶠ x in 𝓝 z, big x = g x
      rw [Filter.eventually_iff]
      have hp : {x : ℝ | big x = g x} ∈ 𝓝[≠] z := by
        rw [← Filter.eventually_iff]
        exact hpunct.mono (fun x h => h.symm)
      obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hp
      refine Filter.mem_of_superset hU ?_
      intro x hx
      by_cases hxz : x = z
      · rw [hxz]; exact hbig_z
      · exact hUsub ⟨hx, by simpa using hxz⟩
    exact hcontbig.congr hagree
  · -- easy case: `z ∉ Z`
    have hmem : Zᶜ ∈ 𝓝 z := hZc.compl_mem_nhds hz
    have hfz : ContinuousAt f z := hf.continuousAt hmem
    have hagree : f =ᶠ[𝓝 z] g := by
      show ∀ᶠ x in 𝓝 z, f x = g x
      rw [Filter.eventually_iff]
      refine Filter.mem_of_superset hmem ?_
      intro x hx
      exact (hg_off x hx).symm
    exact hfz.congr hagree

end Work.TMComp.LocCantor
