import Mathlib
import Submission.Work.ELRig.even_sign_changes
import Submission.Work.ELRig.side_of_odd_crossings

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# ELRig — the level-window shift bijection

`Work.ELRig.level_window_shift_bij`: for a curve `γ : ℝ → ℂ` with the integral periodicity
`γ (s + 1) = γ s + 1`, the level set `{Im γ = c}` inside the fundamental domain `[0,1)` is in
bijection — through a map that preserves *transversal crossings* of the level `c` — with the part
of the level set lying in the "window" `a ≤ Re γ < a + 1` of the real axis.

The proof is elementary and does not use the finiteness hypothesis: the bijection is

`Φ t = t + ⌈a - Re γ t⌉`,

the integral shift that moves `Re γ t` into `[a, a+1)`; its inverse on the window is the
"fundamental domain reduction" `t ↦ t - ⌊t⌋`.  Indeed

* `γ (t + k) = γ t + k` for every integer `k` (the integral periodicity of `γ`), so `Im γ` is
  invariant under integral shifts while `Re γ (t + k) = Re γ t + k`, which gives that `Φ` maps the
  level set of `[0,1)` into the window;
* `Φ (t - ⌊t⌋) = t` for `t` in the window (the ceiling of `a - Re γ (t - ⌊t⌋)` is `⌊t⌋` because
  `Re γ (t - ⌊t⌋) + ⌊t⌋ = Re γ t ∈ [a, a+1)`), which gives surjectivity;
* `Φ s - ⌊Φ s⌋ = s` for `s ∈ [0,1)`, which gives injectivity;
* the crossing predicate `Cross` is invariant under integral shifts of the argument, by the
  `1`-periodicity of `t ↦ Im γ t` (`Cross_shift_int`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.ELRig

open Set

/-! ## Invariance of the one-sided signs and of `Cross` under integral shifts -/

section PeriodicShift

variable {h : ℝ → ℝ} {c : ℝ}

lemma RPos_shift_int (hper : ∀ s : ℝ, h (s + 1) = h s) (k : ℤ) (x : ℝ) :
    RPos h c (x + k) ↔ RPos h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + k ∈ Set.Ioo (x + k) (x + k + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hshift_int hper k t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - k ∈ Set.Ioo x (x + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h (t - k) = h t := by
      have h4 := hshift_int hper k (t - k)
      have h5 : (t - (k : ℝ)) + (k : ℝ) = t := by ring
      rw [h5] at h4
      exact h4.symm
    rwa [h3] at h2

lemma RNeg_shift_int (hper : ∀ s : ℝ, h (s + 1) = h s) (k : ℤ) (x : ℝ) :
    RNeg h c (x + k) ↔ RNeg h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + k ∈ Set.Ioo (x + k) (x + k + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hshift_int hper k t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - k ∈ Set.Ioo x (x + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h (t - k) = h t := by
      have h4 := hshift_int hper k (t - k)
      have h5 : (t - (k : ℝ)) + (k : ℝ) = t := by ring
      rw [h5] at h4
      exact h4.symm
    rwa [h3] at h2

lemma LPos_shift_int (hper : ∀ s : ℝ, h (s + 1) = h s) (k : ℤ) (x : ℝ) :
    LPos h c (x + k) ↔ LPos h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + k ∈ Set.Ioo (x + k - ε) (x + k) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hshift_int hper k t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - k ∈ Set.Ioo (x - ε) x := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h (t - k) = h t := by
      have h4 := hshift_int hper k (t - k)
      have h5 : (t - (k : ℝ)) + (k : ℝ) = t := by ring
      rw [h5] at h4
      exact h4.symm
    rwa [h3] at h2

lemma LNeg_shift_int (hper : ∀ s : ℝ, h (s + 1) = h s) (k : ℤ) (x : ℝ) :
    LNeg h c (x + k) ↔ LNeg h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + k ∈ Set.Ioo (x + k - ε) (x + k) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hshift_int hper k t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - k ∈ Set.Ioo (x - ε) x := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h (t - k) = h t := by
      have h4 := hshift_int hper k (t - k)
      have h5 : (t - (k : ℝ)) + (k : ℝ) = t := by ring
      rw [h5] at h4
      exact h4.symm
    rwa [h3] at h2

/-- `Cross` is invariant under an integral shift of the argument, for a `1`-periodic function. -/
lemma Cross_shift_int (hper : ∀ s : ℝ, h (s + 1) = h s) (k : ℤ) (x : ℝ) :
    Cross h c (x + k) ↔ Cross h c x := by
  have h1 := RPos_shift_int (h := h) (c := c) hper k x
  have h2 := RNeg_shift_int (h := h) (c := c) hper k x
  have h3 := LPos_shift_int (h := h) (c := c) hper k x
  have h4 := LNeg_shift_int (h := h) (c := c) hper k x
  simp only [Cross]
  tauto

end PeriodicShift

/-! ## Integral shifts of the curve `γ` -/

section CurveShift

variable {γ : ℝ → ℂ}

/-- The integral periodicity `γ (s+1) = γ s + 1` gives `γ (t + k) = γ t + k` for every integer
`k`. -/
lemma gamma_shift_int (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (k : ℤ) (t : ℝ) :
    γ (t + k) = γ t + k := by
  have hp : Function.Periodic (fun x : ℝ => γ x - (x : ℂ)) 1 := by
    intro x
    show γ (x + 1) - ((x + 1 : ℝ) : ℂ) = γ x - (x : ℂ)
    rw [hper x]
    push_cast
    ring
  have h : (fun x : ℝ => γ x - (x : ℂ)) (t + (k : ℝ)) =
      (fun x : ℝ => γ x - (x : ℂ)) t := by
    have h2 := hp.zsmul k
    simpa using h2 t
  have h' : γ (t + (k : ℝ)) - (((t : ℝ) + (k : ℝ) : ℝ) : ℂ) = γ t - (t : ℂ) := h
  have h2 : γ (t + (k : ℝ)) =
      (γ t - (t : ℂ)) + (((t : ℝ) + (k : ℝ) : ℝ) : ℂ) := eq_add_of_sub_eq h'
  rw [h2]
  push_cast
  ring

/-- The imaginary part of `γ` is invariant under integral shifts of the parameter. -/
lemma im_shift_int (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (k : ℤ) (t : ℝ) :
    (γ (t + k)).im = (γ t).im := by
  rw [gamma_shift_int hper k t]
  simp

/-- The "window shift": the integral shift that moves `Re γ t` into the half open window
`[a, a+1)`. -/
noncomputable def ceilShift (γ : ℝ → ℂ) (a t : ℝ) : ℝ := t + (⌈a - (γ t).re⌉ : ℤ)

lemma ceilShift_re {γ : ℝ → ℂ} {a : ℝ} (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (t : ℝ) :
    (γ (ceilShift γ a t)).re = (γ t).re + (⌈a - (γ t).re⌉ : ℝ) := by
  have h := gamma_shift_int hper (⌈a - (γ t).re⌉) t
  simp only [ceilShift] at h ⊢
  rw [h]
  simp

lemma ceilShift_im {γ : ℝ → ℂ} {a : ℝ} (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (t : ℝ) :
    (γ (ceilShift γ a t)).im = (γ t).im := by
  have h := gamma_shift_int hper (⌈a - (γ t).re⌉) t
  simp only [ceilShift] at h ⊢
  rw [h]
  simp

/-- The window shift lands in the window: `a ≤ Re γ (ceilShift γ a t) < a + 1`. -/
lemma ceilShift_mem {γ : ℝ → ℂ} {a : ℝ} (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (t : ℝ) :
    a ≤ (γ (ceilShift γ a t)).re ∧ (γ (ceilShift γ a t)).re < a + 1 := by
  have h := ceilShift_re (γ := γ) (a := a) hper t
  have h1 : a - (γ t).re ≤ (⌈a - (γ t).re⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈a - (γ t).re⌉ : ℝ) < a - (γ t).re + 1 := Int.ceil_lt_add_one _
  constructor <;> linarith

end CurveShift

/-! ## The fundamental domain reduction -/

lemma floor_sub_floor_mem (t : ℝ) : t - ⌊t⌋ ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · have := Int.floor_le t; linarith
  · have := Int.lt_floor_add_one t; linarith

/-- The reduction `t ↦ t - ⌊t⌋` commutes with integral shifts. -/
lemma sub_floor_add_intCast (k : ℤ) (t : ℝ) :
    (t + (k : ℝ)) - ⌊t + (k : ℝ)⌋ = t - ⌊t⌋ := by
  rw [Int.floor_add_intCast t k]
  push_cast
  ring

/-! ## The bijection -/

theorem level_window_shift_bij {γ : ℝ → ℂ} {c a : ℝ}
    (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1)
    (hfin : ({s : ℝ | (γ s).im = c} ∩ Set.Ico (0 : ℝ) 1).Finite) :
    ∃ Φ : ℝ → ℝ,
      Set.BijOn Φ ({s : ℝ | (γ s).im = c} ∩ Set.Ico (0 : ℝ) 1)
        {s : ℝ | (γ s).im = c ∧ a ≤ (γ s).re ∧ (γ s).re < a + 1} ∧
      (∀ s ∈ ({s : ℝ | (γ s).im = c} ∩ Set.Ico (0 : ℝ) 1),
        (Work.ELRig.Cross (fun t : ℝ => (γ t).im) c s ↔
          Work.ELRig.Cross (fun t : ℝ => (γ t).im) c (Φ s))) := by
  classical
  have hhper : ∀ s : ℝ, (fun t : ℝ => (γ t).im) (s + 1) = (fun t : ℝ => (γ t).im) s := by
    intro s
    show (γ (s + 1)).im = (γ s).im
    rw [hper s]
    simp
  refine ⟨ceilShift γ a, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the window shift maps the level set of `[0,1)` into the window
    intro t ht
    exact ⟨by rw [ceilShift_im hper t]; exact ht.1,
      (ceilShift_mem hper t).1, (ceilShift_mem hper t).2⟩
  · -- injectivity: `s ↦ s - ⌊s⌋` is a left inverse on `[0,1)`
    intro s hs s' hs' h
    have hs0 : ⌊s⌋ = 0 := Int.floor_eq_zero_iff.mpr hs.2
    have hs'0 : ⌊s'⌋ = 0 := Int.floor_eq_zero_iff.mpr hs'.2
    have h1 : ceilShift γ a s - ⌊ceilShift γ a s⌋ = s := by
      have h2 : s + (⌈a - (γ s).re⌉ : ℝ) - ⌊s + (⌈a - (γ s).re⌉ : ℝ)⌋ = s - ⌊s⌋ :=
        sub_floor_add_intCast (⌈a - (γ s).re⌉) s
      simp only [ceilShift] at h2 ⊢
      rw [h2, hs0]
      ring
    have h1' : ceilShift γ a s' - ⌊ceilShift γ a s'⌋ = s' := by
      have h2 : s' + (⌈a - (γ s').re⌉ : ℝ) - ⌊s' + (⌈a - (γ s').re⌉ : ℝ)⌋ = s' - ⌊s'⌋ :=
        sub_floor_add_intCast (⌈a - (γ s').re⌉) s'
      simp only [ceilShift] at h2 ⊢
      rw [h2, hs'0]
      ring
    rw [← h1, ← h1', h]
  · -- surjectivity: the reduction of a point of the window is a preimage
    intro t ht
    have hn : (t - (⌊t⌋ : ℝ)) + (⌊t⌋ : ℝ) = t := by ring
    have hsh := gamma_shift_int hper ⌊t⌋ (t - (⌊t⌋ : ℝ))
    rw [hn] at hsh
    have him : (γ t).im = (γ (t - ⌊t⌋)).im := by
      rw [hsh]; simp
    have hre : (γ (t - ⌊t⌋)).re + (⌊t⌋ : ℝ) = (γ t).re := by
      have := congrArg Complex.re hsh
      simpa using this.symm
    have hceil : ⌈a - (γ (t - ⌊t⌋)).re⌉ = ⌊t⌋ := by
      rw [Int.ceil_eq_iff]
      constructor <;> linarith [hre, ht.2.1, ht.2.2]
    refine ⟨t - ⌊t⌋, ⟨?_, floor_sub_floor_mem t⟩, ?_⟩
    · rw [Set.mem_setOf_eq, ← him]; exact ht.1
    · simp only [ceilShift]
      rw [hceil]
      ring
  · -- the crossing predicate is preserved: `Φ s = s + ⌈a - Re γ s⌉`
    intro s hs
    rw [show ceilShift γ a s = s + (⌈a - (γ s).re⌉ : ℝ) from rfl]
    exact (Cross_shift_int (h := fun t : ℝ => (γ t).im) (c := c) hhper (⌈a - (γ s).re⌉) s).symm

end Work.ELRig
