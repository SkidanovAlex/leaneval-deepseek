import Mathlib

/-!
# Bounded periodic holomorphic functions on a strip are constant

If `T : ℂ → ℂ` is holomorphic on a vertical strip `{z | a < z.re ∧ z.re < b}` of width at least
`1` (`1 < b - a`), is invariant under `z ↦ z + 1` (where defined on the strip), and is bounded on
the strip, then `T` is constant.

The proof extends `T` to all of `ℂ` by translating every point back into the strip: because
`b - a > 1`, some integer translate `z - n` of any `z` lies in the strip. The translate is chosen
canonically as `n = ⌊z.re - b⌋ + 1`. The periodicity hypothesis shows the extension is well defined
and holomorphic, and it is bounded by the same bound as `T`. Liouville's theorem then forces it to
be constant.
-/

namespace Work.FatouL1

open Complex Filter
open scoped Topology

/-- The extension of `T` to all of `ℂ`: evaluate `T` at `z` shifted back into the strip by
`⌊z.re - b⌋ + 1`. -/
noncomputable def stripExt (T : ℂ → ℂ) (b : ℝ) (z : ℂ) : ℂ :=
  T (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ))

/-- Iterated periodicity along the natural numbers inside the strip. -/
private lemma periodic_nat_shift {a b : ℝ} {T : ℂ → ℂ}
    (hper : ∀ z : ℂ, a < z.re → z.re < b → a < (z + 1).re → (z + 1).re < b → T (z + 1) = T z) :
    ∀ (n : ℕ) (w : ℂ), a < w.re → w.re < b → a < (w + (n : ℂ)).re → (w + (n : ℂ)).re < b →
      T (w + (n : ℂ)) = T w := by
  intro n
  induction n with
  | zero => intro w h1 h2 h3 h4; simp
  | succ m ih =>
    intro w h1 h2 h3 h4
    have hstep : (w + ((m + 1 : ℕ) : ℂ)) = (w + (m : ℂ)) + 1 := by push_cast; ring
    have h3' : a < ((w + (m : ℂ)) + 1).re := hstep ▸ h3
    have h4' : ((w + (m : ℂ)) + 1).re < b := hstep ▸ h4
    have e1 : (w + (m : ℂ)).re = w.re + m := by simp
    have e2 : ((w + (m : ℂ)) + 1).re = w.re + (m + 1 : ℕ) := by
      rw [Complex.add_re, e1, Complex.one_re]; push_cast; ring
    have hmid : a < (w + (m : ℂ)).re ∧ (w + (m : ℂ)).re < b := by
      constructor
      · rw [e1]; have := h1; push_cast at *; linarith
      · rw [e1]; rw [e2] at h4'; push_cast at h4'; linarith
    have key : T ((w + (m : ℂ)) + 1) = T (w + (m : ℂ)) :=
      hper (w + (m : ℂ)) hmid.1 hmid.2
        (by rw [e2]; rw [e2] at h3'; push_cast at h3'; linarith) h4'
    rw [hstep, key]
    exact ih w h1 h2 hmid.1 hmid.2

/-- Periodicity along an arbitrary integer translate inside the strip. -/
private lemma periodic_int_shift {a b : ℝ} {T : ℂ → ℂ}
    (hper : ∀ z : ℂ, a < z.re → z.re < b → a < (z + 1).re → (z + 1).re < b → T (z + 1) = T z) :
    ∀ (k : ℤ) (w : ℂ), a < w.re → w.re < b → a < (w + (k : ℂ)).re → (w + (k : ℂ)).re < b →
      T (w + (k : ℂ)) = T w := by
  intro k w h1 h2 h3 h4
  obtain ⟨n, hk | hk⟩ := Int.eq_nat_or_neg k
  · rw [hk] at h3 h4 ⊢
    exact periodic_nat_shift hper n w h1 h2 (by simpa using h3) (by simpa using h4)
  · rw [hk] at h3 h4 ⊢
    have hc : ((-(↑n) : ℤ) : ℂ) = -(↑n : ℂ) := by push_cast; ring
    rw [hc] at h3 h4 ⊢
    have h3'' : a < (w - (n : ℂ)).re := by simpa [sub_eq_add_neg] using h3
    have h4'' : (w - (n : ℂ)).re < b := by simpa [sub_eq_add_neg] using h4
    have key := periodic_nat_shift hper n (w - (n : ℂ)) h3'' h4''
      (by simpa using h1) (by simpa using h2)
    have hw : (w - (n : ℂ)) + (n : ℂ) = w := by ring
    rw [hw] at key
    exact key.symm

/-- Two points of the strip differing by an integer have equal `T`-values. -/
private lemma periodic_int_eq {a b : ℝ} {T : ℂ → ℂ}
    (hper : ∀ z : ℂ, a < z.re → z.re < b → a < (z + 1).re → (z + 1).re < b → T (z + 1) = T z)
    {w₁ w₂ : ℂ} (h1 : a < w₁.re ∧ w₁.re < b) (h2 : a < w₂.re ∧ w₂.re < b)
    (hdiff : ∃ m : ℤ, w₁ = w₂ + (m : ℂ)) : T w₁ = T w₂ := by
  obtain ⟨m, rfl⟩ := hdiff
  exact periodic_int_shift hper m w₂ h2.1 h2.2 h1.1 h1.2

/-- The integer shift `⌊z.re - b⌋ + 1` moves `z` into the strip. -/
private lemma stripExt_shift_mem {a b : ℝ} (hab : 1 < b - a) (z : ℂ) :
    a < (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ)).re ∧
    (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ)).re < b := by
  have hfl : ((Int.floor (z.re - b) : ℤ) : ℝ) ≤ z.re - b := Int.floor_le (z.re - b)
  have hfu : z.re - b < ((Int.floor (z.re - b) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (z.re - b)
  have hre : (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ)).re
      = z.re - (((Int.floor (z.re - b) : ℤ) : ℝ) + 1) := by
    simp [Complex.sub_re, Complex.intCast_re, Int.cast_add, Int.cast_one]
  constructor <;> rw [hre] <;> linarith

/-- The extension `stripExt T b` is holomorphic on all of `ℂ`. -/
private lemma stripExt_differentiable {a b : ℝ} (hab : 1 < b - a) {T : ℂ → ℂ}
    (hper : ∀ z : ℂ, a < z.re → z.re < b → a < (z + 1).re → (z + 1).re < b → T (z + 1) = T z)
    (hhol : DifferentiableOn ℂ T {z : ℂ | a < z.re ∧ z.re < b}) :
    Differentiable ℂ (stripExt T b) := by
  intro z0
  set k : ℤ := Int.floor (z0.re - b) + 1 with hk
  have hDopen : IsOpen {z : ℂ | a < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hw0 : a < (z0 - (k : ℂ)).re ∧ (z0 - (k : ℂ)).re < b := by
    simpa only [hk] using stripExt_shift_mem (a := a) hab z0
  have hTdiff : DifferentiableAt ℂ T (z0 - (k : ℂ)) :=
    hhol.differentiableAt (hDopen.mem_nhds hw0)
  have hL : DifferentiableAt ℂ (fun z : ℂ => z - (k : ℂ)) z0 :=
    (differentiableAt_id (x := z0)).sub_const _
  have hTL : DifferentiableAt ℂ (fun z : ℂ => T (z - (k : ℂ))) z0 :=
    hTdiff.comp z0 hL
  have hU : {z : ℂ | z - (k : ℂ) ∈ {w : ℂ | a < w.re ∧ w.re < b}} ∈ 𝓝 z0 :=
    (IsOpen.preimage (continuous_id.sub continuous_const) hDopen).mem_nhds hw0
  have hev : stripExt T b =ᶠ[𝓝 z0] (fun z : ℂ => T (z - (k : ℂ))) := by
    filter_upwards [hU] with z hz
    have hmem := stripExt_shift_mem (a := a) hab z
    have hd : ∃ m : ℤ, (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ)) = (z - (k : ℂ)) + (m : ℂ) :=
      ⟨k - (Int.floor (z.re - b) + 1), by push_cast; ring⟩
    have key := periodic_int_eq hper hmem hz hd
    simpa only [stripExt] using key
  exact hTL.congr_of_eventuallyEq hev

theorem periodic_bounded_const {a b : ℝ} (hab : 1 < b - a) {T : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ T {z : ℂ | a < z.re ∧ z.re < b})
    (hper : ∀ z : ℂ, a < z.re → z.re < b → a < (z + 1).re → (z + 1).re < b → T (z + 1) = T z)
    (hbdd : ∃ M : ℝ, ∀ z : ℂ, a < z.re → z.re < b → ‖T z‖ ≤ M) :
    ∃ c : ℂ, ∀ z : ℂ, a < z.re → z.re < b → T z = c := by
  have hdiff : Differentiable ℂ (stripExt T b) := stripExt_differentiable hab hper hhol
  have hbdd' : Bornology.IsBounded (Set.range (stripExt T b)) := by
    obtain ⟨M, hM⟩ := hbdd
    refine isBounded_iff_forall_norm_le.2 ⟨max M 0, ?_⟩
    rintro y ⟨z, rfl⟩
    have hmem := stripExt_shift_mem (a := a) hab z
    have h := hM (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ)) hmem.1 hmem.2
    simpa only [stripExt] using h.trans (le_max_left M 0)
  obtain ⟨c, hc⟩ := Differentiable.exists_const_forall_eq_of_bounded hdiff hbdd'
  refine ⟨c, fun z hz1 hz2 => ?_⟩
  have hmem := stripExt_shift_mem (a := a) hab z
  have hkey : T (z - ((Int.floor (z.re - b) + 1 : ℤ) : ℂ)) = T z :=
    periodic_int_eq hper hmem ⟨hz1, hz2⟩ ⟨- (Int.floor (z.re - b) + 1), by push_cast; ring⟩
  rw [← hc z]
  simpa only [stripExt] using hkey.symm

end Work.FatouL1
