import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs

/-!
# Smoothness of the reconstructed radial function `rhoNew R r`

`Work.OddCurve.LowSlope.rhoNew R r` is the radial function of the body reconstructed from the
solution `(R, r)` of the two-power system:

`rhoNew R r u = R (arccos u)` for `u ≥ 0`,  `rhoNew R r u = r (arccos (-u))` for `u < 0`.

If `R` and `r` are smooth on `[0, π/2]` and `rhoNew R r ≡ 1` near `0` (equivalently: the two
half-profiles match to all orders at the junction `u = 0`), then `rhoNew R r` is smooth on the
open interval `(-1, 1)`. This is what the hypotheses of the target say, so we prove it directly.
-/

namespace Work.OddVolterra.Free

open Set

theorem contDiffOn_rhoNew {R r : ℝ → ℝ}
    (hR : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hconst : ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, |u| < δ → Work.OddCurve.LowSlope.rhoNew R r u = 1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      (Set.Ioo (-1 : ℝ) 1) := by
  obtain ⟨δ, hδpos, hδ⟩ := hconst
  -- `arccos` is smooth on `(-1, 1)`, hence on `(0, 1)` and on `(-1, 0)`.
  have harc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.arccos (Set.Ioo (-1 : ℝ) 1) :=
    Real.contDiffOn_arccos.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ne_of_gt hx.1, ne_of_lt hx.2⟩)
  have harc0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.arccos (Set.Ioo (0 : ℝ) 1) :=
    harc.mono (Set.Ioo_subset_Ioo_left (by norm_num))
  -- right half `(0, 1)`: `rhoNew R r = R ∘ arccos`
  have hRight : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      (Set.Ioo (0 : ℝ) 1) := by
    have hmap : Set.MapsTo Real.arccos (Set.Ioo (0 : ℝ) 1) (Set.Icc 0 (Real.pi / 2)) := by
      intro u hu
      exact ⟨Real.arccos_nonneg u, Real.arccos_le_pi_div_two.mpr (le_of_lt hu.1)⟩
    refine (hR.comp harc0 hmap).congr ?_
    intro u hu
    exact Work.OddCurve.LowSlope.rhoNew_of_nonneg (le_of_lt hu.1)
  -- left half `(-1, 0)`: `rhoNew R r = r ∘ (arccos ∘ neg)`
  have hLeft : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      (Set.Ioo (-1 : ℝ) 0) := by
    have hneg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => -u)
        (Set.Ioo (-1 : ℝ) 0) := contDiff_neg.contDiffOn
    have hmapneg : Set.MapsTo (fun u : ℝ => -u) (Set.Ioo (-1 : ℝ) 0) ({-1, 1}ᶜ : Set ℝ) := by
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by intro h; linarith [hu.1, hu.2, h], by intro h; linarith [hu.1, hu.2, h]⟩
    have hphi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => Real.arccos (-u))
        (Set.Ioo (-1 : ℝ) 0) := Real.contDiffOn_arccos.comp hneg hmapneg
    have hmap : Set.MapsTo (fun u : ℝ => Real.arccos (-u)) (Set.Ioo (-1 : ℝ) 0)
        (Set.Icc 0 (Real.pi / 2)) := by
      intro u hu
      exact ⟨Real.arccos_nonneg (-u), Real.arccos_le_pi_div_two.mpr (by linarith [hu.2])⟩
    refine (hr.comp hphi hmap).congr ?_
    intro u hu
    exact Work.OddCurve.LowSlope.rhoNew_of_neg hu.2
  -- the constant patch around `0`
  have hZero : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      (Set.Ioo (-δ) δ) := by
    refine (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioo (-δ) δ)).congr ?_
    intro u hu
    exact hδ u (abs_lt.mpr hu)
  -- glue the three open pieces
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.rhoNew R r)
      ((Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1) ∪ Set.Ioo (-δ) δ) :=
    (hLeft.union_of_isOpen hRight isOpen_Ioo isOpen_Ioo).union_of_isOpen hZero
      (isOpen_Ioo.union isOpen_Ioo) isOpen_Ioo
  refine hU.mono ?_
  intro u hu
  rcases lt_trichotomy u 0 with h | h | h
  · exact Or.inl (Or.inl ⟨hu.1, h⟩)
  · subst h
    exact Or.inr ⟨by linarith, hδpos⟩
  · exact Or.inl (Or.inr ⟨h, hu.2⟩)

end Work.OddVolterra.Free
