import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
## The convergence of the primitive forces the total integral to vanish

If a function `u` satisfies the finite-increment relation
`u b - u a = ∫_a^b ψ + ∫_a^b gE` for all `0 < a < b`, and both limits of `u`
(at `0⁺` and at `+∞`) are forced to be `0` (the hypotheses `hL0`, `hLinf`),
then the total integral of `ψ + gE` over `[0,∞)` vanishes.

The proof identifies `u` as a primitive of `f = ψ + gE`.  For `0 < a < b` the
splitting `Ioi a = Ioc a b ∪ Ioi b` gives
`u b = (u a + ∫_{Ioi a} f) - ∫_{Ioi b} f`; since the tail integral tends to `0`
along `atTop`, `u` has the limit `u a + ∫_{Ioi a} f` at `+∞`, which is therefore
`0`.  Feeding `u = -∫_{Ioi ·} f` into the limit at `0⁺` (where `∫_{Ioi ε} f`
tends to `∫_{Ioi 0} f`, by the a.e.-cover machinery for `Ioi ε ↑ Ioi 0`)
gives `∫_{Ioi 0} f = 0`, and `{0}` is a null set.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

theorem ZibpUConcl {u ψ gE : ℝ → ℝ}
    (hψ : MeasureTheory.IntegrableOn ψ Work.Spaces.Iz)
    (hgE : MeasureTheory.IntegrableOn gE Work.Spaces.Iz)
    (hfe : ∀ a b : ℝ, 0 < a → a < b →
      u b - u a = (∫ z in a..b, ψ z) + ∫ z in a..b, gE z)
    (hLinf : ∀ L : ℝ, Filter.Tendsto u Filter.atTop (nhds L) → L = 0)
    (hL0 : ∀ L : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds L) → L = 0) :
    (∫ z in Work.Spaces.Iz, ψ z) = - ∫ z in Work.Spaces.Iz, gE z := by
  set f : ℝ → ℝ := fun z => ψ z + gE z with hfdef
  have hψ' : IntegrableOn ψ (Ici (0:ℝ)) := hψ
  have hgE' : IntegrableOn gE (Ici (0:ℝ)) := hgE
  have hf : IntegrableOn f (Ici (0:ℝ)) := by
    rw [hfdef]; exact hψ'.add hgE'
  have hfIoi : IntegrableOn f (Ioi (0:ℝ)) := hf.mono_set Ioi_subset_Ici_self
  have hψIoi : IntegrableOn ψ (Ioi (0:ℝ)) := hψ'.mono_set Ioi_subset_Ici_self
  have hgEIoi : IntegrableOn gE (Ioi (0:ℝ)) := hgE'.mono_set Ioi_subset_Ici_self
  -- The finite-increment relation in terms of the half-open interval `(a,b]`.
  have step1 : ∀ a b : ℝ, 0 < a → a < b → u b - u a = ∫ z in Ioc a b, f z := by
    intro a b ha hab
    have hab' : a ≤ b := le_of_lt hab
    have hψab : IntegrableOn ψ (Ioc a b) :=
      hψ'.mono_set (fun x hx => le_of_lt (lt_trans ha hx.1))
    have hgab : IntegrableOn gE (Ioc a b) :=
      hgE'.mono_set (fun x hx => le_of_lt (lt_trans ha hx.1))
    have hadd : (∫ z in Ioc a b, f z) = (∫ z in Ioc a b, ψ z) + ∫ z in Ioc a b, gE z := by
      rw [hfdef]
      exact integral_add hψab hgab
    have h1 := hfe a b ha hab
    rw [intervalIntegral.integral_of_le hab', intervalIntegral.integral_of_le hab'] at h1
    rw [hadd, h1]
  -- Splitting the tail integral at `b`.
  have step2 : ∀ a b : ℝ, 0 < a → a < b →
      (∫ z in Ioi a, f z) = (∫ z in Ioc a b, f z) + ∫ z in Ioi b, f z := by
    intro a b ha hab
    have hunion : Ioi a = Ioc a b ∪ Ioi b := by
      ext x; constructor
      · intro hx
        rcases le_or_gt x b with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨hx, -⟩ | hx)
        · exact hx
        · exact lt_trans hab hx
    rw [hunion]
    refine setIntegral_union ?_ measurableSet_Ioi ?_ ?_
    · rw [Set.disjoint_left]; intro x hx1 hx2; exact absurd hx1.2 (not_le.mpr hx2)
    · exact hfIoi.mono_set (fun x hx => lt_trans ha hx.1)
    · exact hfIoi.mono_set (fun x hx => lt_trans ha (lt_trans hab hx))
  have htail : Tendsto (fun b : ℝ => ∫ z in Ioi b, f z) atTop (nhds 0) :=
    tendsto_integral_Ioi_zero (f := f) tendsto_id
  -- The limit of `u` at `+∞` is `u a + ∫_{Ioi a} f`, hence `0`.
  have hinf : ∀ a : ℝ, 0 < a → u a + (∫ z in Ioi a, f z) = 0 := by
    intro a ha
    refine hLinf _ ?_
    have hcongr : u =ᶠ[atTop]
        (fun b : ℝ => (u a + ∫ z in Ioi a, f z) - ∫ z in Ioi b, f z) := by
      filter_upwards [eventually_gt_atTop a] with b hb
      have h1 := step1 a b ha hb
      have h2 := step2 a b ha hb
      linarith
    have hT : Tendsto (fun b : ℝ => (u a + ∫ z in Ioi a, f z) - ∫ z in Ioi b, f z) atTop
        (nhds ((u a + ∫ z in Ioi a, f z) - 0)) := tendsto_const_nhds.sub htail
    have h := hT.congr' hcongr.symm
    simpa using h
  -- The tail integral tends to `∫_{Ioi 0} f` at `0⁺` (the sets `Ioi ε` cover `Ioi 0`).
  have htail0 : Tendsto (fun ε : ℝ => ∫ z in Ioi ε, f z) (nhdsWithin (0:ℝ) (Ioi 0))
      (nhds (∫ z in Ioi (0:ℝ), f z)) := by
    have hφ : AECover (volume.restrict (Ioi (0:ℝ))) (nhdsWithin (0:ℝ) (Ioi (0:ℝ)))
        (fun ε : ℝ => Ioi ε) :=
      aecover_Ioi_of_Ioi (μ := volume) (A := (0:ℝ)) (a := fun ε : ℝ => ε)
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    have hmain := hφ.integral_tendsto_of_countably_generated (f := f) hfIoi
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Ioi_subset_Ioi hε.le)]
  have hzero : ∫ z in Ioi (0:ℝ), f z = 0 := by
    have hcongr : u =ᶠ[nhdsWithin (0:ℝ) (Ioi 0)] (fun ε : ℝ => - ∫ z in Ioi ε, f z) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have h := hinf ε hε
      linarith
    have hT : Tendsto (fun ε : ℝ => - ∫ z in Ioi ε, f z) (nhdsWithin (0:ℝ) (Ioi 0))
        (nhds (- ∫ z in Ioi (0:ℝ), f z)) := htail0.neg
    have h := hT.congr' hcongr.symm
    exact neg_eq_zero.mp (hL0 (- ∫ z in Ioi (0:ℝ), f z) h)
  have hsum : (∫ z in Ioi (0:ℝ), f z)
      = (∫ z in Ioi (0:ℝ), ψ z) + ∫ z in Ioi (0:ℝ), gE z := by
    rw [hfdef]
    exact integral_add hψIoi hgEIoi
  have hψeq : (∫ z in Ioi (0:ℝ), ψ z) = ∫ z in Ici (0:ℝ), ψ z :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (μ := volume) (a := (0:ℝ)) (by simp))
  have hgEeq : (∫ z in Ioi (0:ℝ), gE z) = ∫ z in Ici (0:ℝ), gE z :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (μ := volume) (a := (0:ℝ)) (by simp))
  have hfin : (∫ z in Ici (0:ℝ), ψ z) + ∫ z in Ici (0:ℝ), gE z = 0 := by
    rw [← hψeq, ← hgEeq, ← hsum, hzero]
  show (∫ z in Ici (0:ℝ), ψ z) = - ∫ z in Ici (0:ℝ), gE z
  linarith

end Work.FTS.H2
