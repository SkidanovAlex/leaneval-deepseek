import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.pevalF_split
import Submission.Work.Holonomy3.exp_trig_null
import Submission.Work.Holonomy3.sliceF_ne_zero
import Submission.Work.Holonomy3.prod_measure_zero_of_fibers

/-!
# `mv_lex_null_zero`

The zero set of a nonzero finite character sum on the torus
`{s : Fin d → ℝ | pevalF c (tor s) = 0}` is null for the normalised torus measure
`torMeasure d`.

The proof is the classical induction on the number of variables: slicing along the first
coordinate turns the character sum into a one-variable exponential polynomial whose zero set
is finite (hence null) unless all the slices vanish; the set of parameter values for which
*all* slices vanish is null by the induction hypothesis.
-/

namespace Work.Holonomy3

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- `s ↦ pevalF c (tor s)` is continuous on the parameter cube. -/
theorem continuous_pevalF_tor_mv_lex_null_zero {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) :
    Continuous fun s : Fin d → ℝ => pevalF c (tor s) := by
  unfold pevalF tor
  fun_prop

/-- The zero set of `pevalF c (tor ·)` is measurable (indeed closed). -/
theorem measurableSet_pevalF_eq_zero {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) :
    MeasurableSet {s : Fin d → ℝ | pevalF c (tor s) = 0} :=
  (isClosed_eq (continuous_pevalF_tor_mv_lex_null_zero c) continuous_const).measurableSet

/-- In dimension zero the evaluation is the constant coefficient. -/
theorem pevalF_fin_zero (c : (Fin 0 →₀ ℕ) →₀ ℂ) (z : Fin 0 → ℂ) : pevalF c z = c 0 := by
  unfold pevalF
  refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro m _ hm0
    exact absurd (Subsingleton.elim m 0) hm0
  · intro h
    rw [show c 0 = 0 by simpa [Finsupp.mem_support_iff] using h, zero_mul]
  · rw [Finset.prod_eq_one (fun j _ => by rw [Finsupp.zero_apply]; exact pow_zero _), mul_one]

/-! ### The induction -/

/-- `mv_lex_null_zero`, in the form suited to induction on `d`. -/
theorem mv_lex_null_zero_aux : ∀ d : ℕ, ∀ c : (Fin d →₀ ℕ) →₀ ℂ, c ≠ 0 →
    torMeasure d {s : Fin d → ℝ | pevalF c (tor s) = 0} = 0 := by
  intro d
  induction d with
  | zero =>
    intro c hc
    have hc0 : c 0 ≠ 0 := by
      intro h0
      refine hc (Finsupp.ext (fun m => ?_))
      have hm : m = 0 := Subsingleton.elim m 0
      rw [hm, h0]
      rfl
    have hempty : {s : Fin 0 → ℝ | pevalF c (tor s) = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro s hs
      exact hc0 (by rw [← pevalF_fin_zero c (tor s)]; exact hs)
    rw [hempty, MeasureTheory.measure_empty]
  | succ d ih =>
    intro c hc
    obtain ⟨t₀, ht₀mem, ht₀ne⟩ := sliceF_ne_zero c hc
    set N : Set (Fin d → ℝ) := {s | pevalF (sliceF c t₀) (tor s) = 0} with hNdef
    have hNmeas : MeasurableSet N := by
      rw [hNdef]; exact measurableSet_pevalF_eq_zero _
    have hN0 : torMeasure d N = 0 := by
      rw [hNdef]; exact ih (sliceF c t₀) ht₀ne
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (0 : Fin (d + 1))
      with he
    have he_symm : ∀ p : ℝ × (Fin d → ℝ), e.symm p = Fin.insertNth (0 : Fin (d + 1)) p.1 p.2 := by
      intro p
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    have he_mp : MeasurePreserving e (torMeasure (d + 1))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (torMeasure d)) := by
      rw [he]
      exact measurePreserving_piFinSuccAbove
        (fun _ : Fin (d + 1) => volume.restrict (Set.Icc (0 : ℝ) 1)) 0
    set W : Set (ℝ × (Fin d → ℝ)) :=
      e.symm ⁻¹' {s : Fin (d + 1) → ℝ | pevalF c (tor s) = 0} with hWdef
    have hWmeas : MeasurableSet W := by
      rw [hWdef]
      exact (measurableSet_pevalF_eq_zero c).preimage e.symm.measurable
    have hpre : e ⁻¹' W = {s : Fin (d + 1) → ℝ | pevalF c (tor s) = 0} := by
      ext x
      simp only [Set.mem_preimage, hWdef, Set.mem_ofPred_eq, MeasurableEquiv.symm_apply_apply]
    have htransport : torMeasure (d + 1) {s : Fin (d + 1) → ℝ | pevalF c (tor s) = 0}
        = ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (torMeasure d)) W := by
      rw [← he_mp.map_eq, Measure.map_apply e.measurable hWmeas, hpre]
    have hfiber : ∀ s : Fin d → ℝ, s ∉ N →
        (volume.restrict (Set.Icc (0 : ℝ) 1)) {u : ℝ | (u, s) ∈ W} = 0 := by
      intro s hs
      have hs_ne : pevalF (sliceF c t₀) (tor s) ≠ 0 := by simpa [hNdef] using hs
      have hmem : ∀ u : ℝ, ((u, s) ∈ W ↔
          pevalF c (tor (Fin.insertNth (0 : Fin (d + 1)) u s)) = 0) := by
        intro u
        rw [hWdef, Set.mem_preimage, he_symm (u, s)]
        rfl
      have hnull : (volume.restrict (Set.Icc (0 : ℝ) 1)) {u : ℝ | ∑ t ∈ suppFst c,
            pevalF (sliceF c t) (tor s)
              * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) ^ t = 0} = 0 :=
        exp_trig_null ⟨t₀, ht₀mem, hs_ne⟩
      refine measure_mono_null (fun u hu => ?_) hnull
      rw [Set.mem_ofPred_eq] at hu
      have h1 : pevalF c (tor (Fin.insertNth (0 : Fin (d + 1)) u s)) = 0 := (hmem u).mp hu
      rw [pevalF_split c u s] at h1
      rw [Set.mem_ofPred_eq]
      have hcomm : (∑ t ∈ suppFst c, pevalF (sliceF c t) (tor s)
            * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) ^ t)
          = ∑ t ∈ suppFst c, (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) ^ t
            * pevalF (sliceF c t) (tor s) :=
        Finset.sum_congr rfl (fun t _ => mul_comm _ _)
      rw [hcomm]
      exact h1
    have hfin : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (torMeasure d)) W = 0 :=
      prod_measure_zero_of_fibers N hNmeas hN0 W hWmeas hfiber
    rw [htransport, hfin]

theorem mv_lex_null_zero {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (hc : c ≠ 0) :
    torMeasure d {s : Fin d → ℝ | pevalF c (tor s) = 0} = 0 :=
  mv_lex_null_zero_aux d c hc

end

end Work.Holonomy3
