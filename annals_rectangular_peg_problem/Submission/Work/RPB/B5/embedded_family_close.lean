import Mathlib
import Submission.Work.RPB.B5.chord_linear_bound
import Submission.Work.RPB.B5.deriv_bounds_family
import Submission.Work.RPB.B5.separation_away_family

/-!
# `C¹`-small perturbations of an embedded **family** of closed curves

`embedded_of_close` shows that a single embedded immersed `2π`-periodic curve `γ : ℝ → ℂ` stays
embedded under every perturbations `η` with `‖η‖ < δ` and `‖deriv η‖ < δ`.  Here we prove the
`τ`-uniform version for a family `γ : ℝ → ℝ → ℂ`, jointly `C¹`, with every `τ`-slice for
`τ ∈ [0,1]` a `2π`-periodic immersion injective modulo `2π`.

The proof runs the argument of `embedded_of_close` with *exposed constants*: the tail
`embedded_close_of_bounds` produces the conclusion for every perturbation whose size is bounded by
`min (ε₁ / 2) (η₀ / π) / 2`, where

* `ε₁ > 0` lower-bounds `‖deriv (γ τ) t‖` and `ε₁ / 2` bounds the `t`-oscillation of `deriv (γ τ)`
  over steps of length `≤ δ` (uniform in `τ`), and
* `η₀ > 0` lower-bounds `‖γ τ (t + s) - γ τ t‖` for `|s| ∈ [δ, π]` (uniform in `τ`).

Those two uniform inputs are the family versions of `deriv_bounds` / `separation_away`, proved in
`deriv_bounds_family` and `separation_away_family`.  Because the final constant depends only on
`ε₁` and `η₀`, applying the tail to each `τ`-slice gives one constant working for all `τ`.
-/

namespace Work.RPB.B5

/-- Every real `t'` can be shifted by an integer multiple of `2π` into the window `[t, t + 2π)`. -/
private lemma shift_mem_Ico_two_pi (t t' : ℝ) :
    ∃ m : ℤ, t' + 2 * Real.pi * m ∈ Set.Ico t (t + 2 * Real.pi) := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  set y : ℝ := (t' - t) / (2 * Real.pi) with hy
  refine ⟨-⌊y⌋, ?_⟩
  have hfloor : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have hsub : t' + 2 * Real.pi * ((-⌊y⌋ : ℤ) : ℝ) - t = 2 * Real.pi * (y - (⌊y⌋ : ℝ)) := by
    have hthis : t' - t = 2 * Real.pi * y := by rw [hy]; field_simp
    rw [show t' + 2 * Real.pi * ((-⌊y⌋ : ℤ) : ℝ) - t
          = (t' - t) + 2 * Real.pi * (-(⌊y⌋ : ℝ)) by push_cast; ring, hthis]
    ring
  rw [Set.mem_Ico]
  have h1 : (0:ℝ) ≤ 2 * Real.pi * (y - (⌊y⌋ : ℝ)) :=
    mul_nonneg (le_of_lt h2pi) (sub_nonneg.mpr hfloor)
  have h2 : 2 * Real.pi * (y - (⌊y⌋ : ℝ)) < 2 * Real.pi := by
    simpa using mul_lt_mul_of_pos_left (show y - (⌊y⌋ : ℝ) < 1 by linarith) h2pi
  constructor <;> linarith

/-- The perturbation estimate of `embedded_of_close` with the constants of the key chord bound
exposed: any `2π`-periodic `C¹` perturbation `η` of `γ` with

`‖η t‖ < min (ε₁ / 2) (η₀ / π) / 2`  and  `‖deriv η t‖ < min (ε₁ / 2) (η₀ / π) / 2`

preserves both non-vanishing of the derivative and injectivity modulo `2π`.  The hypotheses
`hmin`, `huc` and `hsep` are exactly the three uniform inputs used to build the key chord bound
`c * |s| ≤ ‖γ (t + s) - γ t‖` for `|s| ≤ π`. -/
theorem embedded_close_of_bounds (γ : ℝ → ℂ) (hC1 : ContDiff ℝ 1 γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    {ε₁ δ η₀ : ℝ} (hε₁ : 0 < ε₁) (hδ : 0 < δ) (hη₀ : 0 < η₀)
    (hmin : ∀ t : ℝ, ε₁ ≤ ‖deriv γ t‖)
    (huc : ∀ t u : ℝ, |u| ≤ δ → ‖deriv γ (t + u) - deriv γ t‖ ≤ ε₁ / 2)
    (hsep : ∀ t : ℝ, ∀ s ∈ Set.Icc δ Real.pi, η₀ ≤ ‖γ (t + s) - γ t‖)
    (η : ℝ → ℂ) (hηper : ∀ t, η (t + 2 * Real.pi) = η t) (hηC1 : ContDiff ℝ 1 η)
    (_hηsup : ∀ t, ‖η t‖ < min (ε₁ / 2) (η₀ / Real.pi) / 2)
    (hηder : ∀ t, ‖deriv η t‖ < min (ε₁ / 2) (η₀ / Real.pi) / 2) :
    (∀ t, deriv (fun s => γ s + η s) t ≠ 0) ∧
      (∀ t t', γ t + η t = γ t' + η t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
  have hη₀π : 0 < η₀ / Real.pi := div_pos hη₀ Real.pi_pos
  have hcpos : 0 < min (ε₁ / 2) (η₀ / Real.pi) := lt_min (by linarith) hη₀π
  -- the key chord bound
  have hkey : ∀ t s : ℝ, |s| ≤ Real.pi →
      min (ε₁ / 2) (η₀ / Real.pi) * |s| ≤ ‖γ (t + s) - γ t‖ := by
    intro t s hs
    have hc1 : min (ε₁ / 2) (η₀ / Real.pi) ≤ ε₁ / 2 := min_le_left _ _
    have hc2 : min (ε₁ / 2) (η₀ / Real.pi) ≤ η₀ / Real.pi := min_le_right _ _
    rcases le_or_gt |s| δ with hsmall | hbig
    · calc min (ε₁ / 2) (η₀ / Real.pi) * |s| ≤ (ε₁ / 2) * |s| :=
            mul_le_mul_of_nonneg_right hc1 (abs_nonneg s)
        _ ≤ ‖γ (t + s) - γ t‖ := chord_linear_bound γ hC1 hε₁ hδ hmin huc t s hsmall
    · have hbound : (η₀ / Real.pi) * |s| ≤ η₀ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
        nlinarith [hs, hη₀.le]
      calc min (ε₁ / 2) (η₀ / Real.pi) * |s| ≤ (η₀ / Real.pi) * |s| :=
            mul_le_mul_of_nonneg_right hc2 (abs_nonneg s)
        _ ≤ η₀ := hbound
        _ ≤ ‖γ (t + s) - γ t‖ := by
            rcases le_or_gt 0 s with hspos | hsneg
            · have hsabs : |s| = s := abs_of_nonneg hspos
              exact hsep t s ⟨by rw [← hsabs]; exact le_of_lt hbig, by rw [← hsabs]; exact hs⟩
            · have hsabs : |s| = -s := abs_of_neg hsneg
              have hmem : -s ∈ Set.Icc δ Real.pi :=
                ⟨by rw [← hsabs]; exact le_of_lt hbig, by rw [← hsabs]; exact hs⟩
              have h := hsep (t + s) (-s) hmem
              rwa [show t + s + -s = t by ring, norm_sub_rev] at h
  refine ⟨?_, ?_⟩
  · -- `γ + η` is an immersion
    intro t
    have hdγ : DifferentiableAt ℝ γ t := (hC1.contDiffAt).differentiableAt (by norm_num)
    have hdη : DifferentiableAt ℝ η t := (hηC1.contDiffAt).differentiableAt (by norm_num)
    have hder : deriv (fun s => γ s + η s) t = deriv γ t + deriv η t := by
      have h1 : (fun s => γ s + η s) = γ + η := rfl
      rw [h1, deriv_add hdγ hdη]
    rw [hder]
    intro hzero
    have htri : ‖deriv γ t‖ ≤ ‖deriv γ t + deriv η t‖ + ‖deriv η t‖ := by
      have hh := norm_add_le (deriv γ t + deriv η t) (-(deriv η t))
      rw [show deriv γ t + deriv η t + -(deriv η t) = deriv γ t by ring, norm_neg] at hh
      exact hh
    rw [hzero, norm_zero, zero_add] at htri
    have hlt : min (ε₁ / 2) (η₀ / Real.pi) / 2 < ε₁ := by
      have h := min_le_left (ε₁ / 2) (η₀ / Real.pi); linarith
    linarith [hmin t, hηder t, htri, hlt]
  · -- `γ + η` is injective modulo `2π`
    intro t t' h
    set f : ℝ → ℂ := fun s => γ s + η s with hf
    have hfper : Function.Periodic f (2 * Real.pi) := by
      intro s
      simp only [f]
      rw [hper s, hηper s]
    have hft' : f t = f t' := by simpa [f] using h
    have hηlip : ∀ a b : ℝ, ‖η b - η a‖ ≤ (min (ε₁ / 2) (η₀ / Real.pi) / 2) * |b - a| := by
      intro a b
      have hd : ∀ x : ℝ, DifferentiableAt ℝ η x :=
        fun x => (hηC1.contDiffAt).differentiableAt (by norm_num)
      have hb : ∀ x : ℝ, ‖deriv η x‖ ≤ min (ε₁ / 2) (η₀ / Real.pi) / 2 :=
        fun x => le_of_lt (hηder x)
      have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
        (f := η) (x := a) (y := b) (C := min (ε₁ / 2) (η₀ / Real.pi) / 2)
        (fun x _ => hd x) (fun x _ => hb x) convex_univ (Set.mem_univ a) (Set.mem_univ b)
      simpa [Real.norm_eq_abs] using h
    -- a coincidence at a parameter gap `|s| ≤ π` forces `s = 0`
    have hstep : ∀ u s : ℝ, |s| ≤ Real.pi → f (u + s) = f u →
        min (ε₁ / 2) (η₀ / Real.pi) * |s| ≤ (min (ε₁ / 2) (η₀ / Real.pi) / 2) * |s| := by
      intro u s hs hfeq
      have h1 : min (ε₁ / 2) (η₀ / Real.pi) * |s| ≤ ‖γ (u + s) - γ u‖ := hkey u s hs
      have h2 : ‖γ (u + s) - γ u‖ ≤ (min (ε₁ / 2) (η₀ / Real.pi) / 2) * |s| := by
        have heq : γ (u + s) - γ u = η u - η (u + s) := by
          have hh := hfeq
          simp only [f] at hh
          linear_combination hh
        rw [heq]
        have h := hηlip (u + s) u
        rwa [show u - (u + s) = -s by ring, abs_neg] at h
      linarith
    obtain ⟨m₀, hm₀⟩ := shift_mem_Ico_two_pi t t'
    have hm₀' : t ≤ t' + 2 * Real.pi * m₀ ∧ t' + 2 * Real.pi * m₀ < t + 2 * Real.pi :=
      Set.mem_Ico.mp hm₀
    have hshift : f (t' + 2 * Real.pi * m₀) = f t' := by
      have hh := hfper.int_mul m₀ t'
      rwa [mul_comm ((m₀ : ℝ)) (2 * Real.pi)] at hh
    have hft'' : f (t' + 2 * Real.pi * m₀) = f t := by rw [hshift]; exact hft'.symm
    set s : ℝ := t' + 2 * Real.pi * m₀ - t with hsdef
    have hs0 : 0 ≤ s := by rw [hsdef]; linarith [hm₀'.1]
    have hs2pi : s < 2 * Real.pi := by rw [hsdef]; linarith [hm₀'.2]
    have hfs : f (t + s) = f t := by
      have : t + s = t' + 2 * Real.pi * m₀ := by rw [hsdef]; ring
      rw [this]; exact hft''
    by_cases hzero : s = 0
    · refine ⟨-m₀, ?_⟩
      have hsum : t' + 2 * Real.pi * m₀ - t = 0 := by rw [← hsdef]; exact hzero
      have ht' : t' = t - 2 * Real.pi * m₀ := by linarith
      rw [ht', show t - 2 * Real.pi * m₀ = t + 2 * Real.pi * (-(m₀ : ℝ)) by ring]
      push_cast
      ring
    · rcases le_or_gt s Real.pi with hle | hgt
      · have habs : |s| ≤ Real.pi := by rw [abs_of_nonneg hs0]; exact hle
        have hbad := hstep t s habs hfs
        have hpos : 0 < |s| := abs_pos.mpr hzero
        have hcle : min (ε₁ / 2) (η₀ / Real.pi) ≤ min (ε₁ / 2) (η₀ / Real.pi) / 2 :=
          le_of_mul_le_mul_right hbad hpos
        linarith [hcpos]
      · have hneg : s - 2 * Real.pi < 0 := by linarith
        have habs : |s - 2 * Real.pi| ≤ Real.pi := by rw [abs_of_neg hneg]; linarith
        have hfs' : f (t + (s - 2 * Real.pi)) = f t := by
          have hh := hfper (t + (s - 2 * Real.pi))
          rw [show t + (s - 2 * Real.pi) + 2 * Real.pi = t + s by ring, hfs] at hh
          exact hh.symm
        have hbad := hstep t (s - 2 * Real.pi) habs hfs'
        have hpos : 0 < |s - 2 * Real.pi| := abs_pos.mpr (by linarith)
        have hcle : min (ε₁ / 2) (η₀ / Real.pi) ≤ min (ε₁ / 2) (η₀ / Real.pi) / 2 :=
          le_of_mul_le_mul_right hbad hpos
        linarith [hcpos]

theorem embedded_family_close (γ : ℝ → ℝ → ℂ)
    (hsm : ContDiff ℝ 1 (fun z : ℝ × ℝ => γ z.1 z.2))
    (hper : ∀ τ t, γ τ (t + 2 * Real.pi) = γ τ t)
    (hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', γ τ t = γ τ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (γ τ) t ≠ 0) :
    ∃ δe > 0, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ η : ℝ → ℂ,
      (∀ t, η (t + 2 * Real.pi) = η t) → ContDiff ℝ 1 η →
      (∀ t, ‖η t‖ < δe) → (∀ t, ‖deriv η t‖ < δe) →
      (∀ t, deriv (fun s => γ τ s + η s) t ≠ 0) ∧
      (∀ t t', γ τ t + η t = γ τ t' + η t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
  -- uniform constants, the same for every `τ ∈ [0,1]`
  obtain ⟨ε₁, hε₁, δ, hδ, hδ1, hmin, huc⟩ := deriv_bounds_family γ hsm hper hderiv
  have hδπ : δ ≤ Real.pi := by linarith [Real.pi_gt_three]
  obtain ⟨η₀, hη₀, hsep⟩ := separation_away_family γ hsm.continuous hper hinj hδ hδπ
  have hη₀π : 0 < η₀ / Real.pi := div_pos hη₀ Real.pi_pos
  have hcpos : 0 < min (ε₁ / 2) (η₀ / Real.pi) := lt_min (by linarith) hη₀π
  -- the constant of `embedded_close_of_bounds`, independent of `τ`
  refine ⟨min (ε₁ / 2) (η₀ / Real.pi) / 2, div_pos hcpos (by norm_num), ?_⟩
  intro τ hτ η hηper hηC1 hηsup hηder
  have hC1τ : ContDiff ℝ 1 (fun t : ℝ => γ τ t) := by
    simpa only [Function.comp_def, id_eq] using hsm.comp (contDiff_const.prodMk contDiff_id)
  exact embedded_close_of_bounds (fun t => γ τ t) hC1τ (hper τ) hε₁ hδ hη₀
    (hmin τ hτ) (huc τ hτ) (hsep τ hτ) η hηper hηC1 hηsup hηder

end Work.RPB.B5
