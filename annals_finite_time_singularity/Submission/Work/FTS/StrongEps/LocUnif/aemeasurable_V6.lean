/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e.-measurability of the level-6 measurable majorants `V6z`, `V6t`

`V6z α f` (resp. `V6t α f`) is the `liminf`, as `j → ∞`, of the squared backward difference
quotients of the level-5 slots `mixed (5-i) i f` (resp. of `mixed 0 5 f`), evaluated at the
shifted point `(z - 1/(j+1), θ)` (resp. `(z, θ - 1/(j+1))`) and weighted by `z · rho6 α i`.

The hypothesis gives a.e.-measurability of the level-5 slots on the **open** quadrant
`Q0 = (0,∞) × (0,π/2)`.  The backward shift can push a point of the box `[a,b] × [c,d]`
outside `Q0`, namely when `1/(j+1) ≥ a` (resp. `≥ c`), but that happens for only *finitely
many* indices `j`: a `liminf` over `Filter.atTop` is unchanged when finitely many initial
terms of the sequence are dropped.  Concretely, for `n₀` so large that
`1/((j+n₀)+1) < min a c` for every `j`, the shifted point stays in `Q0`, so each term of the
reindexed sequence is a.e.-measurable (translation invariance of Lebesgue measure) and
`AEMeasurable.liminf` applies.

The hypotheses `0 < a`, `0 < c`, `d < π/2` are exactly what makes the box lie in the open
quadrant, so that the shifts never leave it once they are small enough.
-/
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.V6Defs
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_comp_sub_of_aemeasurable
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub_snd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## Auxiliary lemmas -/

/-- **A.e.-measurability transfers under a *vertical* translation.**  The second-coordinate
analogue of `aemeasurable_comp_sub_of_aemeasurable`: if `F` is a.e.-measurable on `A` and the
shift `q ↦ (q.1, q.2 - h)` maps `B` into `A`, then the composite is a.e.-measurable on `B`.

Proof: `AEMeasurable F (volume.restrict A)` unfolds to a *measurable* `g` with
`F =ᵐ[volume.restrict A] g`; the a.e.-equality is transported across the shift by
`ae_shift_preimage_sub_snd`, and `g ∘ shift` is measurable. -/
private theorem aemeasurable_comp_sub_snd_of_aemeasurable {A B : Set (ℝ × ℝ)} {h : ℝ}
    {β : Type*} [MeasurableSpace β] {F : ℝ × ℝ → β}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hmap : ∀ q ∈ B, (q.1, q.2 - h) ∈ A)
    (hf : AEMeasurable F (MeasureTheory.volume.restrict A)) :
    AEMeasurable (fun q : ℝ × ℝ => F (q.1, q.2 - h)) (MeasureTheory.volume.restrict B) := by
  obtain ⟨g, hgm, hfg⟩ := hf
  refine ⟨fun q : ℝ × ℝ => g (q.1, q.2 - h), hgm.comp ?_, ?_⟩
  · exact measurable_fst.prodMk (measurable_snd.sub measurable_const)
  · filter_upwards [ae_shift_preimage_sub_snd (Q := fun q => F q = g q) hAm hBm hfg hmap]
      with q hq
    exact hq

/-- **Dropping finitely many initial terms does not change a `liminf` over `atTop`.** -/
private theorem liminf_add_atTop_eq {u : ℕ → ℝ≥0∞} (n : ℕ) :
    Filter.liminf (fun j : ℕ => u (j + n)) Filter.atTop = Filter.liminf u Filter.atTop := by
  have h := Filter.liminf_comp u (fun j : ℕ => j + n) Filter.atTop
  rw [Filter.map_add_atTop_eq_nat n] at h
  exact h

/-- The level-6 weight function `rho6`, as a function of the point `(z,θ)`, is measurable. -/
private theorem measurable_rho6 (α : ℝ) (i : ℕ) :
    Measurable (fun p : ℝ × ℝ => rho6 α i p.1 p.2) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hw : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)
  by_cases hi : i = 0
  · have hρ : (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      funext p
      simp only [rho6, hi, ite_true]
    rw [hρ]
    exact (hw.comp measurable_fst).div ((hsin.comp measurable_snd).pow_const _)
  · have hρ : (fun p : ℝ × ℝ => rho6 α i p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p
      simp only [rho6, hi, ite_false, Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [hρ]
    exact (hw.comp measurable_fst).mul ((hsin.comp measurable_snd).pow_const _)

theorem aemeasurable_V6 {α : ℝ} {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : d < π / 2)
    (hW : ∀ (j i : ℕ), j + i = 5 →
      AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))) :
    AEMeasurable (Work.FTS.StrongEps.LocUnif.V6z α f)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) ∧
      AEMeasurable (Work.FTS.StrongEps.LocUnif.V6t α f)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have hQmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hBmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hBQ : (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ))
      ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    rintro ⟨z, θ⟩ hx
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hx
    obtain ⟨haz, hzb⟩ := Set.mem_Icc.mp hz
    obtain ⟨hcθ, hθd⟩ := Set.mem_Icc.mp hθ
    exact Set.mem_prod.mpr
      ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
  -- Number of initial shifts that have to be discarded.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / min a c)
  have hmpos : 0 < min a c := lt_min ha hc
  have hNmul : 1 < (N : ℝ) * min a c := by
    have h := (div_lt_iff₀ hmpos).mp hN
    linarith
  have hnN : 1 / ((N : ℝ) + 1) < min a c := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hsh : ∀ j : ℕ, 1 / (((j + N : ℕ) : ℝ) + 1) < min a c := by
    intro j
    have hle : ((N : ℝ) + 1) ≤ (((j + N : ℕ) : ℝ) + 1) := by
      have h1 : (N : ℕ) ≤ j + N := Nat.le_add_left N j
      have h2 : (N : ℝ) ≤ ((j + N : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hmono := one_div_le_one_div_of_le hpos hle
    linarith
  -- The shifts stay inside the open quadrant.
  have hmapz : ∀ j : ℕ, ∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
      (q.1 - 1 / (((j + N : ℕ) : ℝ) + 1), q.2)
        ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro j q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    obtain ⟨haz, hzb⟩ := Set.mem_Icc.mp hq1
    obtain ⟨hcθ, hθd⟩ := Set.mem_Icc.mp hq2
    have h1 : 1 / (((j + N : ℕ) : ℝ) + 1) < a :=
      lt_of_lt_of_le (hsh j) (min_le_left _ _)
    have hp : 0 < q.1 - 1 / (((j + N : ℕ) : ℝ) + 1) := by linarith
    have hp2 : 0 < q.2 := by linarith
    have hq2' : q.2 < π / 2 := by linarith
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hp, Set.mem_Ioo.mpr ⟨hp2, hq2'⟩⟩
  have hmapθ : ∀ j : ℕ, ∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
      (q.1, q.2 - 1 / (((j + N : ℕ) : ℝ) + 1))
        ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro j q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    obtain ⟨haz, hzb⟩ := Set.mem_Icc.mp hq1
    obtain ⟨hcθ, hθd⟩ := Set.mem_Icc.mp hq2
    have h1 : 1 / (((j + N : ℕ) : ℝ) + 1) < c :=
      lt_of_lt_of_le (hsh j) (min_le_right _ _)
    have hpos : (0 : ℝ) < 1 / (((j + N : ℕ) : ℝ) + 1) := by positivity
    have hp : 0 < q.1 := by linarith
    have hp2 : 0 < q.2 - 1 / (((j + N : ℕ) : ℝ) + 1) := by linarith
    have hq2' : q.2 - 1 / (((j + N : ℕ) : ℝ) + 1) < π / 2 := by linarith
    exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr hp, Set.mem_Ioo.mpr ⟨hp2, hq2'⟩⟩
  -- A.e.-measurability of a single `z`-difference quotient term (generic shift and constant).
  have key : ∀ (h cst : ℝ), (∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
        (q.1 - h, q.2) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) →
      AEMeasurable (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - h) p.2) * cst
          * (p.1 * rho6 α i p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    intro h cst hmap
    have hterm : ∀ i ∈ Finset.range 6, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - h) p.2) * cst
          * (p.1 * rho6 α i p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hbase : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed (5 - i) i f p.1 p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        AEMeasurable.mono_set hBQ (hW (5 - i) i (by omega))
      have hshift : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed (5 - i) i f (p.1 - h) p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        aemeasurable_comp_sub_of_aemeasurable
          (f := fun p : ℝ × ℝ => Work.Spaces.mixed (5 - i) i f p.1 p.2)
          hQmeas hBmeas hmap (hW (5 - i) i (by omega))
      have hw : AEMeasurable (fun p : ℝ × ℝ => p.1 * rho6 α i p.1 p.2)
          (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
        (measurable_fst.mul (measurable_rho6 α i)).aemeasurable
      exact ((((hbase.sub hshift).mul_const cst).mul hw).pow_const 2).ennreal_ofReal
    exact Finset.aemeasurable_sum (Finset.range 6) hterm
  -- A.e.-measurability of the `θ`-difference quotient term.
  have keyT : ∀ (h cst : ℝ), (∀ q ∈ (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)),
        (q.1, q.2 - h) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) →
      AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - h)) * cst
          * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    intro h cst hmap
    have hbase : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed 0 5 f p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      AEMeasurable.mono_set hBQ (hW 0 5 (by norm_num))
    have hshift : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed 0 5 f p.1 (p.2 - h))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      aemeasurable_comp_sub_snd_of_aemeasurable
        (F := fun p : ℝ × ℝ => Work.Spaces.mixed 0 5 f p.1 p.2)
        hQmeas hBmeas hmap (hW 0 5 (by norm_num))
    have hw : AEMeasurable (fun p : ℝ × ℝ => Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).mul
        (measurable_rho6 α 6)).aemeasurable
    exact ((((hbase.sub hshift).mul_const cst).mul hw).pow_const 2).ennreal_ofReal
  constructor
  · have hseq : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / (((j + N : ℕ) : ℝ) + 1)) p.2)
          * (((j + N : ℕ) : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      fun j => key (1 / (((j + N : ℕ) : ℝ) + 1)) (((j + N : ℕ) : ℝ) + 1) (hmapz j)
    have hlim := AEMeasurable.liminf hseq
    have heq : V6z α f = fun p : ℝ × ℝ => Filter.liminf (fun j : ℕ =>
        ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / (((j + N : ℕ) : ℝ) + 1)) p.2)
          * (((j + N : ℕ) : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2)) Filter.atTop := by
      funext p
      show Filter.liminf (fun j : ℕ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / ((j : ℝ) + 1)) p.2)
          * ((j : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2)) Filter.atTop = _
      exact (liminf_add_atTop_eq N (u := fun j : ℕ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
        (((Work.Spaces.mixed (5 - i) i f p.1 p.2
            - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / ((j : ℝ) + 1)) p.2)
          * ((j : ℝ) + 1) * (p.1 * rho6 α i p.1 p.2)) ^ 2))).symm
    rw [heq]
    exact hlim
  · have hseq : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / (((j + N : ℕ) : ℝ) + 1)))
          * (((j + N : ℕ) : ℝ) + 1)
          * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2))
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
      fun j => keyT (1 / (((j + N : ℕ) : ℝ) + 1)) (((j + N : ℕ) : ℝ) + 1) (hmapθ j)
    have hlim := AEMeasurable.liminf hseq
    have heq : V6t α f = fun p : ℝ × ℝ => Filter.liminf (fun j : ℕ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / (((j + N : ℕ) : ℝ) + 1)))
          * (((j + N : ℕ) : ℝ) + 1)
          * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop := by
      funext p
      show Filter.liminf (fun j : ℕ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1)))
          * ((j : ℝ) + 1) * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop = _
      exact (liminf_add_atTop_eq N (u := fun j : ℕ => ENNReal.ofReal
        (((Work.Spaces.mixed 0 5 f p.1 p.2
            - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1)))
          * ((j : ℝ) + 1) * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2))).symm
    rw [heq]
    exact hlim

end Work.FTS.StrongEps.LocUnif
