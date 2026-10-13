import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_up_loc_deriv
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_up_loc_c
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_up_tail

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

/-! The three integrability inputs for the integration by parts at the upper end are proved
separately (and in a general form, for arbitrary real exponents) in the sibling modules
`radGreen_up_loc_deriv`, `radGreen_up_loc_c` and `radGreen_up_tail`. -/

/-- Gluing: integrability on `(z,1)` and on `(1,∞)` gives integrability on `(z,∞)` when `z < 1`.
(The two pieces overlap at `t = 1`, and `(z,1) ∪ [1,∞) = (z,∞)` exactly when `z < 1`; the
singleton `{1}` is added by hand because `[1,∞) = (1,∞) ∪ {1}` whereas `hdinf` gives `(1,∞)`.) -/
private lemma upAux_union {f : ℝ → ℝ} {z : ℝ} (hz1 : z < 1)
    (h1 : IntegrableOn f (Set.Ioo z 1)) (h2 : IntegrableOn f (Set.Ioi 1)) :
    IntegrableOn f (Set.Ioi z) := by
  have hsing : IntegrableOn f ({1} : Set ℝ) :=
    integrableOn_singleton (f := f) (x := 1) (by finiteness) (by simp)
  have hIci : IntegrableOn f (Set.Ici (1 : ℝ)) := by
    have h4 : IntegrableOn f (Set.Ioi (1 : ℝ) ∪ {1}) := h2.union hsing
    rwa [show (Set.Ioi (1 : ℝ) ∪ {1} : Set ℝ) = Set.Ici 1 from by
      ext t
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff, Set.mem_Ici]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'.symm] at h4
  have h5 : IntegrableOn f (Set.Ioo z 1 ∪ Set.Ici (1 : ℝ)) := h1.union hIci
  rwa [show (Set.Ioo z 1 ∪ Set.Ici (1 : ℝ) : Set ℝ) = Set.Ioi z from by
    ext t
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      rcases lt_or_ge t 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'] at h5

/-- **Integration by parts at the upper end, in `rgB`-form** (intended namespace
`Work.FTS.ClassCHon.Zpz`, module `Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_upper`).

With `p = rgP α m = 2*m/α ≥ 0`, `rgB α m c z = ∫ t in Set.Ioi z, c t * t ^ (-p - 1)`, and `hlim`
the (requested separately) statement that `t ↦ c t * t ^ (-p) → 0` at `∞`: the `t`-weighted source
`t ↦ t * deriv c t` satisfies
`rgB α m (fun t => t * deriv c t) z = p * rgB α m c z - c z * z ^ (-p)` for every `z > 0`.

This is the integration by parts
`∫ x in Set.Ioi z, deriv c x * x ^ (-p) = - c z * z ^ (-p) + p * ∫ x in Set.Ioi z, c x * x ^ (-p-1)`
(whose boundary term at `∞` vanishes by `hlim`), transported to `rgB` through the a.e. identity
`(t * deriv c t) * t ^ (-p - 1) = deriv c t * t ^ (-p)` on `t > 0`, via
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'` applied to `F t = c t * t ^ (-p)` with
`a = z`, `m = 0` (so the integral of `F'` over `Ioi z` is `-F z`).
The hypotheses `hinf`/`hdinf` give integrability on `(1,∞)`; `hd0` gives local integrability of
`deriv c` on `(z,1)` when `z < 1` (`|deriv c t| ≤ z ^ (-q) * |t * deriv c t * t ^ (q - 1)|` for
`t ≥ z`, `q = rgQ α m`), so that the integral of `F'` over `Ioi z` is finite (that is,
`MeasureTheory.IntegrableOn F' (Set.Ioi z)`). -/
theorem radGreen_ibp_upper {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (hlim : Filter.Tendsto (fun t => c t * t ^ (-(Work.FTS.EllExist.rgP α m)))
      Filter.atTop (nhds 0))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) (Set.Ioi 1))
    (hd0 : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.rgB α m (fun t => t * deriv c t) z
        = Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgB α m c z
          - c z * z ^ (-(Work.FTS.EllExist.rgP α m)) := by
  intro z hz
  dsimp only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
  set p : ℝ := Work.FTS.EllExist.rgP α m with hp
  set q : ℝ := Work.FTS.EllExist.rgQ α m with hq
  have hp0 : 0 ≤ p := by rw [hp]; exact Work.FTS.EllExist.rgP_nonneg hα m
  have hq0 : 0 < q := by rw [hq]; exact Work.FTS.EllExist.rgQ_pos hα m
  -- the pointwise derivative of `F t = c t * t ^ (-p)`
  have hderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => c s * s ^ (-p))
        (deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s ^ (-p)) ((-p) * t ^ (-p - 1)) t :=
      Real.hasDerivAt_rpow_const (x := t) (p := -p) (Or.inl (ne_of_gt ht))
    refine ((hcd t ht).mul h1).congr_deriv ?_
    ring
  -- integrability inputs: local (`(z,1)`) and tail (`(1,∞)`)
  have hF1_loc : IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioo z 1) :=
    radGreen_up_loc_deriv hp0 hq0 hz hd0
  have hF2_loc : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioo z 1) :=
    radGreen_up_loc_c hz hcd
  have hF1_tail : IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioi 1) :=
    radGreen_up_tail hdinf
  have hF2_tail : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi 1) := hinf
  have hF1 : IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioi z) := by
    by_cases hz1 : z < 1
    · exact upAux_union hz1 hF1_loc hF1_tail
    · exact hF1_tail.mono_set (Set.Ioi_subset_Ioi (not_lt.mp hz1))
  have hF2 : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi z) := by
    by_cases hz1 : z < 1
    · exact upAux_union hz1 hF2_loc hF2_tail
    · exact hF2_tail.mono_set (Set.Ioi_subset_Ioi (not_lt.mp hz1))
  have hpF2 : IntegrableOn (fun t => p * (c t * t ^ (-p - 1))) (Set.Ioi z) := by
    rw [MeasureTheory.IntegrableOn] at hF2 ⊢
    exact hF2.const_mul p
  let F : ℝ → ℝ := fun t => c t * t ^ (-p)
  let F' : ℝ → ℝ := fun t => deriv c t * t ^ (-p) - p * (c t * t ^ (-p - 1))
  have hF'deriv : ∀ t : ℝ, 0 < t → HasDerivAt F (F' t) t := hderiv
  have hF'int : IntegrableOn F' (Set.Ioi z) := hF1.sub hpF2
  have hlimF : Tendsto F Filter.atTop (nhds 0) := hlim
  -- the fundamental theorem of calculus on `(z, ∞)`
  have hftc : ∫ t in Set.Ioi z, F' t = 0 - F z :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := z) (f := F) (f' := F')
      (m := 0) (fun x hx => hF'deriv x (lt_of_lt_of_le hz hx)) hF'int hlimF
  -- splitting the integral
  have hsplit : (∫ t in Set.Ioi z, F' t)
      = (∫ t in Set.Ioi z, deriv c t * t ^ (-p))
        - p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) := by
    rw [MeasureTheory.integral_sub hF1 hpF2,
      MeasureTheory.integral_const_mul p (fun t : ℝ => c t * t ^ (-p - 1))]
  -- the a.e. identity `(t * deriv c t) * t ^ (-p - 1) = deriv c t * t ^ (-p)` on `(z, ∞)`
  have hcongr : (∫ t in Set.Ioi z, deriv c t * t ^ (-p))
      = ∫ t in Set.Ioi z, (t * deriv c t) * t ^ (-p - 1) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    have h1 : t ^ (-p) = t ^ (1 + (-p - 1)) :=
      congrArg (fun r : ℝ => t ^ r) (by ring)
    have h2 : t ^ (-p) = t * t ^ (-p - 1) := by
      rw [h1, Real.rpow_add ht0 1 (-p - 1), Real.rpow_one]
    rw [h2]
    ring
  have hmain : (∫ t in Set.Ioi z, (t * deriv c t) * t ^ (-p - 1))
      = p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) - c z * z ^ (-p) := by
    have h := hftc
    rw [hsplit, hcongr] at h
    have hFz : F z = c z * z ^ (-p) := rfl
    rw [hFz] at h
    linarith
  exact hmain

end Work.FTS.ClassCHon.Zpz
