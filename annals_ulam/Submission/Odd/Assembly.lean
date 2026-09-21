import Mathlib
import Submission.Odd.Statement
import Submission.Work.OddCaps.odd_cap_volume_half
import Submission.Work.OddCaps.odd_cap_centroid_span
import Submission.Work.Odd.not_centrally_symmetric_of_h_ne_zero
import Submission.Work.Odd.sub_singleton_eq_neg_iff

/-!
# Assembly of the odd case

Taking the two moment equations

* `(A)`: `∫_{-x s}^{y s} (f² - (s t + h s)²)^n √(f² - (s t + h s)²) = C / √(1+s²)`
* `(B)`: `∫_{-x s}^{y s} (f² - (s t + h s)²)^{n-1} √(f² - (s t + h s)²) (t + h' s) = 0`

for all `s > 0`, together with the geometric data (`f` strictly concave with support `[-1,1]`,
`h` smooth with `h 0 = 0` and non-zero, `±x, y` the two roots of `f² = L²`, inside `(-1,1)`),
the two family conditions (volume half and centroid in span) and non-central-symmetry, this file
produces `Submission.Odd.odd_floating_family_data`.

The two family conditions are supplied here as hypotheses; they are the conclusions of the
"cap" lemmas (commons `odd_profile_cap_volume_half` / `odd_profile_cap_centroid_span`, or their
smooth-regularity versions in `Submission/Work/OddCaps/`), and non-central-symmetry comes from
`Submission/Work/Odd/not_centrally_symmetric_of_h_ne_zero`.
-/

namespace Submission.Odd

open MeasureTheory
open Commons.Geometry.Ulam
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Moment equations plus geometric data plus the two family conditions give the family data. -/
theorem family_data_of_moment_equations (hd : 3 ≤ d) [NeZero d] (hdodd : Odd d) (n : ℕ)
    (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {C : ℝ} {f h x y : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_strict : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_contIcc : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiff ℝ ∞ h) (h0 : h 0 = 0) (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)))
    (hx_pos : ∀ s : ℝ, 0 < s → 0 < x s) (hy_pos : ∀ s : ℝ, 0 < s → 0 < y s)
    (hinside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1)
    (hroot_l : ∀ s : ℝ, 0 < s → f (-x s) = -(s * (-x s) + h s))
    (hroot_r : ∀ s : ℝ, 0 < s → f (y s) = s * y s + h s)
    (hA : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0)
    :
    OddFamilyData d := by
  letI : NeZero d := ⟨by omega⟩
  have hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧ (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2 := by
    intro s hs
    exact ⟨hx_pos s hs, hy_pos s hs,
      congrArg (fun z : ℝ => z ^ 2) (hroot_r s hs),
      (by rw [hroot_l s hs]; ring)⟩
  have hvol_l : ∀ s : ℝ, 0 < s →
      let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      volume.real (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}) = volume.real K / 2 := by
    intro s hs
    exact Work.OddCaps.odd_cap_volume_half (d := d) (n := n) hdn hn hf_support hf_cont
      hf_strict.concaveOn hf_left hf_right hf_pos hh_cont.contDiffOn h0 hxy hinside hB s hs
  have hcent_l : ∀ s : ℝ, 0 < s →
      let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) +
          (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
    intro s hs
    exact Work.OddCaps.odd_cap_centroid_span (d := d) (n := n) hdn hn hf_support hf_cont
      hf_strict.concaveOn hf_left hf_right hf_pos hh_cont.contDiffOn h0 hxy hinside hA hB hvol_l s hs
  have hvol' : ∀ s : ℝ, 0 < s →
      let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      volume.real (K ∩ {x | x
        ⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}) =
          volume.real K / 2 := by
    intro s hs
    simpa [lastFin] using hvol_l s hs
  have hlast_eq : (⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ : Fin d)
      = lastFin d := by
    apply Fin.ext
    simp [lastFin]
  have hcent' : ∀ s : ℝ, 0 < s →
      let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x
        ⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ (EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single
            (⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ : Fin d) 1) := by
    intro s hs
    have h := hcent_l s hs
    have hsingle : EuclideanSpace.single (0 : Fin d) (-s)
        = (-s) • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) := by
      ext i
      by_cases hi : i = 0 <;> simp [hi]
    have htarget : EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single
            (⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ : Fin d) 1
        = ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) +
            (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
      rw [hsingle, hlast_eq]
    rw [htarget]
    exact h
  have hK_meas : MeasurableSet {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∑ i > 0, (x i)^2 ≤ f (x 0)^2} :=
    body_of_revolution_measurable (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_support hf_cont hf_left hf_right
  have hK_conv : Convex ℝ {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∑ i > 0, (x i)^2 ≤ f (x 0)^2} :=
    body_of_revolution_convex (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_strict.concaveOn hf_left hf_right
  have hK_bdd : Bornology.IsBounded {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∑ i > 0, (x i)^2 ≤ f (x 0)^2} :=
    body_of_revolution_bounded (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_strict.concaveOn hf_left hf_right
  have hK_fin : volume {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∑ i > 0, (x i)^2 ≤ f (x 0)^2} < ⊤ := hK_bdd.measure_lt_top
  have hK_int : (interior {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∑ i > 0, (x i)^2 ≤ f (x 0)^2}).Nonempty :=
    interior_nonempty_body_of_revolution (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      (by norm_num) hf_cont.continuousOn hf_pos
  have hrefl : ¬ ∃ p : ℝᵈ, ∀ x : ℝᵈ,
      (x ∈ {y : ℝᵈ | y 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (y i)^2 ≤ f (y 0)^2} ↔
        (2 : ℝ) • p - x ∈ {y : ℝᵈ | y 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
          ∑ i > 0, (y i)^2 ≤ f (y 0)^2}) :=
    Work.Odd.not_centrally_symmetric_of_h_ne_zero (K := {y : ℝᵈ |
      y 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (y i)^2 ≤ f (y 0)^2}) (h := h)
      hK_meas hK_conv hK_int hK_fin hvol_l hh_supp hhne
  have hnonc' : ¬ ∃ p : ℝᵈ,
      ({x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2} : Set ℝᵈ) -
        ({p} : Set ℝᵈ)
      = -(({x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2} : Set ℝᵈ) -
        ({p} : Set ℝᵈ)) := by
    rintro ⟨p, hp⟩
    have hconv : ∀ s : Set ℝᵈ, -s = (fun x : ℝᵈ => -x) '' s := by
      intro s
      ext a
      rw [Set.mem_neg, Set.mem_image]
      constructor
      · intro h
        exact ⟨-a, h, by simp⟩
      · rintro ⟨x, hx, hxa⟩
        have : -a = x := by rw [← hxa]; simp
        rwa [this]
    have hkey : Set.image2 (fun a b : ℝᵈ => a - b) {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
          ∑ i > 0, (x i)^2 ≤ f (x 0)^2} ({p} : Set ℝᵈ)
        = (fun x : ℝᵈ => -x) '' Set.image2 (fun a b : ℝᵈ => a - b)
            {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2} ({p} : Set ℝᵈ) := by
      calc Set.image2 (fun a b : ℝᵈ => a - b)
            {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2} ({p} : Set ℝᵈ)
          = (({x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
              ∑ i > 0, (x i)^2 ≤ f (x 0)^2} : Set ℝᵈ) - {p}) := rfl
        _ = -(({x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
              ∑ i > 0, (x i)^2 ≤ f (x 0)^2} : Set ℝᵈ) - {p}) := hp
        _ = (fun x : ℝᵈ => -x) '' (({x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧
              ∑ i > 0, (x i)^2 ≤ f (x 0)^2} : Set ℝᵈ) - {p}) := hconv _
        _ = (fun x : ℝᵈ => -x) '' Set.image2 (fun a b : ℝᵈ => a - b)
              {x : ℝᵈ | x 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
              ({p} : Set ℝᵈ) := rfl
    exact hrefl ⟨p, (Work.Odd.sub_singleton_eq_neg_iff (K := {y : ℝᵈ |
      y 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∑ i > 0, (y i)^2 ≤ f (y 0)^2}) (p := p)).mp hkey⟩
  exact ⟨1, 1, f, h, by norm_num, hf_support, hf_cont, hf_strict, hf_contIcc, hf_left,
    hf_right, hf_pos, hh_cont, h0, hhne, hvol', hcent', hnonc'⟩

end Submission.Odd
