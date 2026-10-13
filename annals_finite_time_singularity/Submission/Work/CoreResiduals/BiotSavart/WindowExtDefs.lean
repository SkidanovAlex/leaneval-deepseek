/-
# `WindowExtDefs` — the two-sided time-extension of a strip vorticity

The construction of `exists_windowExtension_of_stripBundle`: glue the strip vorticity `ω` to its
affine continuation `ω y 0 + t • ∂ₜω(y,0)` for `t ≤ 0` and `ω y S + (t-S) • ∂ₜω(y,S)` for `t ≥ S`.

This file defines the extension `windowExt` and the associated "slices of `∂ₜ`" `dtExt`, together
with the elementary case lemmas, the derivative lemma (`HasDerivAt_windowExt`), the vanishing of
`∂ₜω` at the strip endpoints off the support ball, and the support of the extension (which is
global in `t`).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.CoreResiduals.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- The two-sided time-extension of the vorticity `ω` beyond the strip `Icc 0 S`:
the strip value on `Icc 0 S`, the affine continuation with the endpoint time-derivative below `0`
and above `S`. -/
noncomputable def windowExt (ω : R3 → ℝ → R3) (S : ℝ) : R3 → ℝ → R3 :=
  fun y t => if t ≤ 0 then ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0
    else if t ≤ S then ω y t
    else ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S

/-- The "slices of `∂ₜ`" of the extension: `∂ₜω(·,0)` for `t ≤ 0`, `∂ₜω(·,t)` inside the strip and
`∂ₜω(·,S)` above.  It is the time derivative of `windowExt` (`timeDeriv_windowExt`). -/
noncomputable def dtExt (ω : R3 → ℝ → R3) (S : ℝ) : R3 → ℝ → R3 :=
  fun y t => if t ≤ 0 then FiniteTimeSingularity.timeDeriv ω y 0
    else if t ≤ S then FiniteTimeSingularity.timeDeriv ω y t
    else FiniteTimeSingularity.timeDeriv ω y S

variable {ω : R3 → ℝ → R3} {S : ℝ} {y : R3} {t : ℝ}

theorem windowExt_of_nonpos (ht : t ≤ 0) :
    windowExt ω S y t = ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0 := by
  unfold windowExt; rw [if_pos ht]

theorem windowExt_of_mem_Icc (ht : t ∈ Set.Icc (0:ℝ) S) : windowExt ω S y t = ω y t := by
  unfold windowExt
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp
  · rw [if_neg (not_le.mpr h), if_pos ht.2]

theorem windowExt_of_ge (hS : 0 < S) (ht : S ≤ t) :
    windowExt ω S y t = ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S := by
  unfold windowExt
  have h0 : ¬ t ≤ 0 := by linarith
  rw [if_neg h0]
  by_cases h : t ≤ S
  · rw [if_pos h]; have htS : t = S := le_antisymm h ht; rw [htS]; simp
  · rw [if_neg h]

theorem dtExt_of_nonpos (ht : t ≤ 0) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y 0 := by
  unfold dtExt; rw [if_pos ht]

theorem dtExt_of_mem_Icc (ht : t ∈ Set.Icc (0:ℝ) S) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y t := by
  unfold dtExt
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp
  · rw [if_neg (not_le.mpr h), if_pos ht.2]

theorem dtExt_of_ge (hS : 0 < S) (ht : S ≤ t) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y S := by
  unfold dtExt
  have h0 : ¬ t ≤ 0 := by linarith
  rw [if_neg h0]
  by_cases h : t ≤ S
  · rw [if_pos h]; have htS : t = S := le_antisymm h ht; rw [htS]
  · rw [if_neg h]

/-- `dtExt` is the composition of the `∂ₜ`-slice with the clamping map `t ↦ max 0 (min t S)`. -/
theorem dtExt_eq_clamp (hS : 0 < S) :
    dtExt ω S y t = FiniteTimeSingularity.timeDeriv ω y (max 0 (min t S)) := by
  by_cases h : t ≤ 0
  · rw [dtExt_of_nonpos h]
    congr 1
    rw [min_eq_left (by linarith : t ≤ S), max_eq_left h]
  · by_cases h2 : t ≤ S
    · rw [dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
      congr 1
      rw [min_eq_left h2, max_eq_right (le_of_lt (lt_of_not_ge h))]
    · rw [dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
      congr 1
      rw [min_eq_right (le_of_lt (lt_of_not_ge h2)), max_eq_right (le_of_lt hS)]

/-- **Differentiability of the extension.**  If the strip slices `s ↦ ω y s` are differentiable on
`Icc 0 S` with derivative `∂ₜω(y,·)`, then `windowExt ω S y ·` is differentiable everywhere, with
derivative `dtExt ω S y ·`.  The only non-trivial points are the junctions `0` and `S`, where the
one-sided derivatives agree (they are `∂ₜω(y,0)` resp. `∂ₜω(y,S)`). -/
theorem hasDerivAt_windowExt (hS : 0 < S)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    (y : R3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => windowExt ω S y s) (dtExt ω S y t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [dtExt_of_nonpos (le_of_lt ht)]
    have haff : HasDerivAt (fun s : ℝ => ω y 0 + s • FiniteTimeSingularity.timeDeriv ω y 0)
        (FiniteTimeSingularity.timeDeriv ω y 0) t := by
      have h1 : HasDerivAt (fun s : ℝ => s • FiniteTimeSingularity.timeDeriv ω y 0)
          ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y 0) t :=
        (hasDerivAt_id t).smul_const _
      simpa using h1.const_add (ω y 0)
    exact haff.congr_of_eventuallyEq (by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact windowExt_of_nonpos (le_of_lt hs))
  · rw [ht]
    rw [dtExt_of_nonpos (le_refl 0)]
    have haff : HasDerivAt (fun s : ℝ => ω y 0 + s • FiniteTimeSingularity.timeDeriv ω y 0)
        (FiniteTimeSingularity.timeDeriv ω y 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • FiniteTimeSingularity.timeDeriv ω y 0)
          ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y 0) 0 :=
        (hasDerivAt_id 0).smul_const _
      simpa using h1.const_add (ω y 0)
    have hL : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
        (FiniteTimeSingularity.timeDeriv ω y 0) (Set.Iic 0) 0 :=
      haff.hasDerivWithinAt.congr (fun s hs => windowExt_of_nonpos hs)
        (windowExt_of_nonpos (le_refl 0))
    have hR : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
        (FiniteTimeSingularity.timeDeriv ω y 0) (Set.Icc 0 S) 0 :=
      (hdiff 0 ⟨le_refl 0, le_of_lt hS⟩ y).hasDerivWithinAt.congr
        (fun s hs => windowExt_of_mem_Icc hs)
        (windowExt_of_mem_Icc ⟨le_refl 0, le_of_lt hS⟩)
    have hunion := hL.union hR
    have hset : Set.Iic (0:ℝ) ∪ Set.Icc (0:ℝ) S = Set.Iic S := by
      ext x; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro (h | ⟨h1, h2⟩) <;> linarith
      · intro hx
        by_cases h : x ≤ 0
        · exact Or.inl h
        · exact Or.inr ⟨le_of_lt (lt_of_not_ge h), hx⟩
    rw [hset] at hunion
    exact hunion.hasDerivAt
      (mem_of_superset (Iio_mem_nhds hS) (fun x hx => le_of_lt (Set.mem_Iio.mp hx)))
  · by_cases hts : t < S
    · rw [dtExt_of_mem_Icc ⟨le_of_lt ht, le_of_lt hts⟩]
      exact (hdiff t ⟨le_of_lt ht, le_of_lt hts⟩ y).congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhds ht hts] with s hs
        exact windowExt_of_mem_Icc ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
    · by_cases htS : t = S
      · rw [htS]
        rw [dtExt_of_ge hS (le_refl S)]
        have hL : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
            (FiniteTimeSingularity.timeDeriv ω y S) (Set.Icc 0 S) S :=
          (hdiff S ⟨le_of_lt hS, le_refl S⟩ y).hasDerivWithinAt.congr
            (fun s hs => windowExt_of_mem_Icc hs)
            (windowExt_of_mem_Icc ⟨le_of_lt hS, le_refl S⟩)
        have hR : HasDerivWithinAt (fun s : ℝ => windowExt ω S y s)
            (FiniteTimeSingularity.timeDeriv ω y S) (Set.Ici S) S := by
          have haff : HasDerivAt
              (fun s : ℝ => ω y S + (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
              (FiniteTimeSingularity.timeDeriv ω y S) S := by
            have h1 : HasDerivAt
                (fun s : ℝ => (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
                ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y S) S :=
              ((hasDerivAt_id S).sub_const S).smul_const _
            simpa using h1.const_add (ω y S)
          exact haff.hasDerivWithinAt.congr (fun s hs => windowExt_of_ge hS hs)
            (windowExt_of_ge hS (le_refl S))
        have hunion := hL.union hR
        have hset : Set.Icc (0:ℝ) S ∪ Set.Ici S = Set.Ici 0 := by
          ext x; simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
          constructor
          · rintro (⟨h1, h2⟩ | h)
            · exact h1
            · exact le_trans (le_of_lt hS) h
          · intro hx
            by_cases h : x ≤ S
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr (le_of_lt (lt_of_not_ge h))
        rw [hset] at hunion
        exact hunion.hasDerivAt
          (mem_of_superset (Ioi_mem_nhds hS) (fun x hx => le_of_lt (Set.mem_Ioi.mp hx)))
      · have hSt : S < t := lt_of_le_of_ne (le_of_not_gt hts) (Ne.symm htS)
        rw [dtExt_of_ge hS (le_of_lt hSt)]
        have haff : HasDerivAt
            (fun s : ℝ => ω y S + (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
            (FiniteTimeSingularity.timeDeriv ω y S) t := by
          have h1 : HasDerivAt
              (fun s : ℝ => (s - S) • FiniteTimeSingularity.timeDeriv ω y S)
              ((1:ℝ) • FiniteTimeSingularity.timeDeriv ω y S) t :=
            ((hasDerivAt_id t).sub_const S).smul_const _
          simpa using h1.const_add (ω y S)
        exact haff.congr_of_eventuallyEq (by
          filter_upwards [Ioi_mem_nhds hSt] with s hs
          exact windowExt_of_ge hS (le_of_lt hs))

/-- The time derivative of the extension is the glued `∂ₜ`-slice `dtExt`. -/
theorem timeDeriv_windowExt (hS : 0 < S)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    (y : R3) (t : ℝ) :
    FiniteTimeSingularity.timeDeriv (windowExt ω S) y t = dtExt ω S y t :=
  (hasDerivAt_windowExt hS hdiff y t).deriv

/-- **The `∂ₜ`-slice vanishes at the strip endpoints off the support ball.**  Off `closedBall 0 R`
the strip slice `s ↦ ω y s` is identically `0` on `Icc 0 S`; the two-sided derivative at `0` (resp.
`S`) is therefore `0` (the one-sided derivative within `Ici 0` resp. `Iic S` of the constant `0`). -/
theorem timeDeriv_eq_zero_of_notMem_closedBall {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S)
    (hsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    {y : R3} (hy : y ∉ Metric.closedBall 0 R) :
    FiniteTimeSingularity.timeDeriv ω y 0 = 0 ∧ FiniteTimeSingularity.timeDeriv ω y S = 0 := by
  have hstrip : ∀ s ∈ Set.Icc (0:ℝ) S, ω y s = 0 := by
    intro s hs; by_contra h; exact hy (hsupp s hs y h)
  constructor
  · have h1 : HasDerivWithinAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y 0)
        (Set.Ici 0) 0 :=
      (hdiff 0 ⟨le_refl 0, le_of_lt hS⟩ y).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun s : ℝ => ω y s) 0 (Set.Ici 0) 0 := by
      have hc : HasDerivWithinAt (fun _ : ℝ => (0:R3)) 0 (Set.Ici 0) 0 :=
        (hasDerivAt_const (x := (0:ℝ)) (c := (0:R3))).hasDerivWithinAt
      refine hc.congr_of_eventuallyEq ?_ ?_
      · show ∀ᶠ s in 𝓝[Set.Ici (0:ℝ)] (0:ℝ), ω y s = 0
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds hS] with s hs hsi
        exact hstrip s ⟨hsi, le_of_lt hs⟩
      · exact hstrip 0 ⟨le_refl 0, le_of_lt hS⟩
    rw [← h1.derivWithin (uniqueDiffWithinAt_Ici 0), h2.derivWithin (uniqueDiffWithinAt_Ici 0)]
  · have h1 : HasDerivWithinAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y S)
        (Set.Iic S) S :=
      (hdiff S ⟨le_of_lt hS, le_refl S⟩ y).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun s : ℝ => ω y s) 0 (Set.Iic S) S := by
      have hc : HasDerivWithinAt (fun _ : ℝ => (0:R3)) 0 (Set.Iic S) S :=
        (hasDerivAt_const (x := S) (c := (0:R3))).hasDerivWithinAt
      refine hc.congr_of_eventuallyEq ?_ ?_
      · show ∀ᶠ s in 𝓝[Set.Iic S] S, ω y s = 0
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Ioi_mem_nhds (show S / 2 < S by linarith)] with s hs hsi
        simp only [Set.mem_Ioi] at hs
        simp only [Set.mem_Iic] at hsi
        exact hstrip s ⟨by linarith, hsi⟩
      · exact hstrip S ⟨le_of_lt hS, le_refl S⟩
    rw [← h1.derivWithin (uniqueDiffWithinAt_Iic S), h2.derivWithin (uniqueDiffWithinAt_Iic S)]

/-- **The extension is supported in `closedBall 0 R`, globally in `t`.** -/
theorem windowExt_eq_zero_of_notMem_closedBall {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S)
    (hsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hdiff : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : R3,
      HasDerivAt (fun s : ℝ => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t)
    {y : R3} (hy : y ∉ Metric.closedBall 0 R) (t : ℝ) : windowExt ω S y t = 0 := by
  have hz := timeDeriv_eq_zero_of_notMem_closedBall hS hsupp hdiff hy
  have hω : ∀ s ∈ Set.Icc (0:ℝ) S, ω y s = 0 := by
    intro s hs; by_contra h; exact hy (hsupp s hs y h)
  by_cases h : t ≤ 0
  · rw [windowExt_of_nonpos h, hω 0 ⟨le_refl 0, le_of_lt hS⟩, hz.1]; simp
  · by_cases h2 : t ≤ S
    · rw [windowExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
      exact hω t ⟨le_of_lt (lt_of_not_ge h), h2⟩
    · rw [windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2)), hω S ⟨le_of_lt hS, le_refl S⟩, hz.2]
      simp

end Work.CoreResiduals.BiotSavart
