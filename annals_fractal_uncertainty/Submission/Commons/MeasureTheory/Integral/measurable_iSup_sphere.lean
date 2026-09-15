import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option linter.style.haveILetI false

open Set MeasureTheory TopologicalSpace Filter

namespace Commons.MeasureTheory.Integral

/-- The supremum of a continuous real-valued function over a set `K` equals its supremum over a
subset `t` that is dense in `K` (i.e. `K ⊆ closure t`), provided `K` is nonempty and the image of
`K` is bounded above. -/
lemma csSup_image_eq_of_subset_closure {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {f : X → ℝ} (hf : Continuous f) {K t : Set X}
    (hKne : K.Nonempty) (hKbdd : BddAbove (f '' K))
    (htK : t ⊆ K) (hKt : K ⊆ closure t) :
    sSup (f '' K) = sSup (f '' t) := by
  have htne : t.Nonempty := closure_nonempty_iff.mp (hKne.mono hKt)
  have htbdd : BddAbove (f '' t) := hKbdd.mono (image_mono htK)
  apply le_antisymm
  · refine csSup_le (hKne.image f) (fun b hb => ?_)
    rcases hb with ⟨u, huK, rfl⟩
    have hu : u ∈ closure t := hKt huK
    rw [mem_closure_iff_seq_limit] at hu
    obtain ⟨x, hxmem, hxtend⟩ := hu
    have hle : ∀ n, f (x n) ≤ sSup (f '' t) :=
      fun n => le_csSup htbdd (mem_image_of_mem f (hxmem n))
    exact le_of_tendsto ((hf.tendsto u).comp hxtend) (Eventually.of_forall hle)
  · exact csSup_le (htne.image f) (fun b hb => le_csSup hKbdd (image_mono htK hb))

theorem measurable_iSup_sphere {d : ℕ} (hd : 1 ≤ d)
    {g : _root_.EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => sSup (g '' {x : _root_.EuclideanSpace ℝ (Fin d) | ‖x‖ = r}))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  classical
  let E := _root_.EuclideanSpace ℝ (Fin d)
  let S : Set E := {u | ‖u‖ = 1}
  have hSne : S.Nonempty := by
    refine ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), ?_⟩
    simp only [S, mem_ofPred_eq]
    rw [PiLp.norm_single, norm_one]
  have hSc : IsCompact S := by
    have hsphere : S = Metric.sphere (0 : E) 1 := by
      ext x
      simp only [S, Metric.mem_sphere]
      rw [dist_zero_right]
      simp
    rw [hsphere]
    exact isCompact_sphere 0 1
  have hsep : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.of_separableSpace S
  obtain ⟨t, htS, htc, hSt⟩ := hsep.exists_countable_dense_subset
  haveI : Countable t := htc
  have hmeasF : Measurable (fun r : ℝ => ⨆ (u : t), g (r • (u : E))) := by
    apply Measurable.iSup
    intro u
    exact (hg.comp (continuous_id.smul continuous_const)).measurable
  have hF : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ⨆ (u : t), g (r • (u : E)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hmeasF.aestronglyMeasurable
  refine hF.congr ?_
  have hpoint : ∀ r : ℝ, 0 < r →
      (⨆ (u : t), g (r • (u : E))) = sSup (g '' {x : E | ‖x‖ = r}) := by
    intro r hr
    let f0 : E → ℝ := fun u => g (r • u)
    have hcont : Continuous f0 := hg.comp (continuous_id.const_smul r)
    have hSph : {x : E | ‖x‖ = r} = (fun u : E => r • u) '' S := by
      ext x
      constructor
      · intro hx
        rw [mem_ofPred_eq] at hx
        refine ⟨r⁻¹ • x, ?_, ?_⟩
        · simp only [S, mem_ofPred_eq]
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hr)), hx,
            inv_mul_cancel₀ (ne_of_gt hr)]
        · show r • (r⁻¹ • x) = x
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
      · intro hx
        rw [mem_image] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        rw [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg (le_of_lt hr), hu, mul_one]
    have himg : g '' {x : E | ‖x‖ = r} = f0 '' S := by
      rw [hSph, image_image]
    have hub : BddAbove (f0 '' S) := (hSc.image hcont).bddAbove
    have hsSup_eq : sSup (f0 '' S) = sSup (f0 '' t) :=
      csSup_image_eq_of_subset_closure hcont hSne hub htS hSt
    have hrange : range (fun u : t => f0 u) = f0 '' t := by
      rw [show (fun u : t => f0 u) = f0 ∘ Subtype.val from rfl, Set.range_comp,
        Subtype.range_coe]
    calc (⨆ (u : t), g (r • (u : E)))
        = sSup (range (fun u : t => f0 u)) := rfl
      _ = sSup (f0 '' t) := by rw [hrange]
      _ = sSup (f0 '' S) := hsSup_eq.symm
      _ = sSup (g '' {x : E | ‖x‖ = r}) := by rw [himg]
  refine (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume)
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).mpr ?_
  exact Filter.Eventually.of_forall (fun r hr => hpoint r hr)

end Commons.MeasureTheory.Integral