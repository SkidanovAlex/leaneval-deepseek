import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.sectorCountBoxAux
import Submission.Work.Measure.ae_measure_section_right_null
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.fibreWord_ae_eq_zero` — the sliding word vanishes on a.e.-zero box states

`Work.SlotWord.fibreWord h M k L d ε c μ u Ψ` is the sliding (fibre) word of the a-priori chapter,
`tBwordBInd k L d ε c u Ψ + qLHSwordB h M k L d μ u Ψ`.  The kinetic half is a sum over slots `i`
of `(2π)⁻³∫_p F‖p‖(L³)⁻¹∫_{abox k L}‖tBamp χ_B p (Q_{B,i}Ψ) i x‖²`, the potential half an integral
over `abox k L` of `(Ψ x)²` against a fixed kernel.  **Every one of those integrals only ever
evaluates `Ψ` at configurations inside the big box** — the FS projection `Q_{B,i}` uses the box
indicator `1_B(x_i)` and the slot mean `∫_{z∈B}Ψ(x_{i←z})`, the window `χ_B` is supported in
`acube L` — so if `Ψ` vanishes a.e. on `abox k L` the whole word vanishes.

## The single analytic input

`sliceAe_eq_zero`: *if `Ψ =ᵐ 0` on `abox N L` then for a.e. `x` the slot-`i` slice
`z ↦ Ψ (x_{i←z})` is `=ᵐ 0` on `acube L`.*  (`Ψ` is **not** assumed measurable: the a.e.-null set
`{Ψ ≠ 0}` is replaced by a *measurable* null superset, on which the product-measure peel
`Submission.BoseGases.abox_peel_mp` + Fubini (`Work.Measure.ae_measure_section_right_null`) gives
a.e.-null sections.)  Everything else is bookkeeping: the a.e. vanishing of `boxQInd`, of `tBamp`,
of `cnPlusBoxInd`, of `tBdiagFormInd`, and the elementary `qLHSwordB` integral.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The peel identification `x_{i←z} = kcInsN i (z, x ∘ succAbove)` -/

private lemma update_eq_kcInsN (n : ℕ) (i : Fin (n + 1))
    (x : Submission.BoseGases.X (n + 1)) (z : EuclideanSpace ℝ (Fin 3)) :
    Function.update x i z = Submission.BoseGases.kcInsN n i
      (z, (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i x).2) := by
  have h : (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i x).2
      = fun j => x (i.succAbove j) := rfl
  rw [h]
  ext k
  by_cases hk : k = i
  · subst hk
    simp [Submission.BoseGases.kc_insN_apply_same]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [Submission.BoseGases.kc_insN_apply_succ, Fin.succAbove_ne]

/-! ## 2. The analytic input: slices of an a.e.-zero box state are a.e. zero -/

/-- **Slices of an a.e.-zero state are a.e. zero.**  For `Ψ =ᵐ 0` on `abox N L`, for a.e. `x` the
slot-`i` slice `z ↦ Ψ (x_{i←z})` vanishes a.e. on `acube L`.  No measurability of `Ψ` is needed:
the (possibly non-measurable) null set `{Ψ ≠ 0}` is enlarged to a measurable null set `S'`, on
which the peel/Fubini argument applies. -/
theorem sliceAe_eq_zero {N : ℕ} {L : ℝ} {i : Fin N}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)),
      (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0 := by
  rcases N with _ | n
  · exact i.elim0
  classical
  have hmp := Submission.BoseGases.abox_peel_mp (n := n) L i
  have hmp' : MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i))
      ((MeasureTheory.volume.restrict (Submission.BoseGases.acube L)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n L)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)) := by
    have h2 := MeasurePreserving.symm
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i) hmp
    simpa [Submission.BoseGases.kcInsN] using h2
  -- a measurable null superset of `{Ψ ≠ 0}`
  have hS0 : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))
      {x | Ψ x ≠ 0} = 0 := MeasureTheory.ae_iff.mp hΨ
  obtain ⟨S', hSS', hS'm, hS'0⟩ := MeasureTheory.exists_measurable_superset_of_null hS0
  have hZ'm : MeasurableSet ((⇑(Submission.BoseGases.kcInsN n i)) ⁻¹' S') :=
    hS'm.preimage (MeasurableEquiv.measurable (Submission.BoseGases.kcInsN n i))
  have hZ'0 : ((MeasureTheory.volume.restrict (Submission.BoseGases.acube L)).prod
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n L)))
      ((⇑(Submission.BoseGases.kcInsN n i)) ⁻¹' S') = 0 :=
    (hmp'.measure_preimage hS'm.nullMeasurableSet).trans hS'0
  -- Fubini on the product space
  have hsec := Work.Measure.ae_measure_section_right_null
    (MeasureTheory.volume.restrict (Submission.BoseGases.acube L))
    (MeasureTheory.volume.restrict (Submission.BoseGases.abox n L)) hZ'm hZ'0
  have hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n L)),
      (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, r)))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0 := by
    filter_upwards [hsec] with r hr
    refine MeasureTheory.ae_iff.mpr (MeasureTheory.measure_mono_null (fun t ht => ?_) hr)
    exact hSS' ht
  -- transport to `q = (z, r)`
  have hQ : ((MeasureTheory.volume.restrict (Submission.BoseGases.acube L)).prod
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n L)))
      {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n |
        ¬ ((fun z : EuclideanSpace ℝ (Fin 3) =>
              Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0)} = 0 := by
    have hset : {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n |
        ¬ ((fun z : EuclideanSpace ℝ (Fin 3) =>
              Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0)}
        = Set.univ ×ˢ {r : Submission.BoseGases.X n |
        ¬ ((fun z : EuclideanSpace ℝ (Fin 3) =>
              Ψ (Submission.BoseGases.kcInsN n i (z, r)))
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0)} := by
      ext q; simp
    rw [hset, MeasureTheory.Measure.prod_prod, MeasureTheory.ae_iff.mp hslice, mul_zero]
  -- pull back along the peel equivalence
  have hfinal : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))
      {x | ¬ ((fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z))
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0)} = 0 := by
    have hset : {x : Submission.BoseGases.X (n + 1) |
          ¬ ((fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z))
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0)}
        = (⇑(MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i)) ⁻¹'
          {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n |
            ¬ ((fun z : EuclideanSpace ℝ (Fin 3) =>
                  Ψ (Submission.BoseGases.kcInsN n i (z, q.2)))
              =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      have hupd : (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z))
          = fun z => Ψ (Submission.BoseGases.kcInsN n i
              (z, (MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i x).2)) := by
        funext z; rw [update_eq_kcInsN]
      rw [hupd]
    rw [hset, hmp.measure_preimage (MeasureTheory.NullMeasurableSet.of_null hQ)]
    exact hQ
  exact MeasureTheory.ae_iff.mpr hfinal

/-! ## 3. The FS box projection `Q_{B,i}` is a.e. zero -/

/-- The slot-mean half `boxPInd` is a.e. zero, from the slice form. -/
theorem boxPInd_ae_eq_zero_of_slice {N : ℕ} {L volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {i : Fin N} {Ψ : Submission.BoseGases.X N → ℝ}
    (hsl : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)),
      (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0) :
    Work.UBBInputs8.boxPInd volA A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0 := by
  filter_upwards [hsl] with x hx
  simp only [Pi.zero_apply]
  unfold Work.UBBInputs8.boxPInd
  have h2 : (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x i z))
      =ᵐ[MeasureTheory.volume.restrict A] 0 := by
    have h := hx.filter_mono
      (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self (s := A)))
    rwa [MeasureTheory.Measure.restrict_restrict_of_subset hAc] at h
  have hint : (∫ z in A, Ψ (Function.update x i z)) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
      ((MeasureTheory.ae_restrict_iff' hA).mp h2)
  rw [hint]; ring

/-- **The FS box projection `Q_{B,i}Ψ` vanishes a.e.** on the big box for a state vanishing a.e.
there: the box-indicator term carries the factor `Ψ x`, the slot-mean term is handled by
`boxPInd_ae_eq_zero_of_slice`. -/
theorem boxQInd_ae_eq_zero_of_ae_eq_zero {N : ℕ} {L volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {i : Fin N} {Ψ : Submission.BoseGases.X N → ℝ}
    (h0 : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0) :
    Work.UBBInputs8.boxQInd volA A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0 := by
  have hsl := sliceAe_eq_zero (L := L) (i := i) h0
  have hP := boxPInd_ae_eq_zero_of_slice (volA := volA) hA hAc hsl
  filter_upwards [h0, hP] with x h0x hPx
  simp only [Pi.zero_apply] at h0x hPx ⊢
  unfold Work.UBBInputs8.boxQInd
  rw [h0x, hPx]; ring

/-- **The excited count vanishes**: `cnPlusBoxInd` is a sum of integrals of the squares of the a.e.
zero `boxQInd`. -/
theorem cnPlusBoxInd_eq_zero_of_ae_eq_zero {N : ℕ} {L volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) {Ψ : Submission.BoseGases.X N → ℝ}
    (h0 : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0) :
    Work.UBBInputs8.cnPlusBoxInd L A volA Ψ = 0 := by
  unfold Work.UBBInputs8.cnPlusBoxInd
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hQ := boxQInd_ae_eq_zero_of_ae_eq_zero (volA := volA) (A := A) hA hAc (i := i) h0
  refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [(MeasureTheory.ae_restrict_iff'
    (Submission.BoseGases.abox_measurable N L)).mp hQ] with x hx
  simp only [Pi.zero_apply] at hx
  intro hxmem
  rw [hx hxmem]; ring

/-! ## 4. The windowed amplitude `tBamp` is a.e. zero -/

/-- **`tBamp` vanishes a.e.** when the slice is a.e. zero and the window `χ` is supported in
`acube L`: its integrand `z ↦ χ z·e^{-i⟨p,z⟩}·Φ(x_{i←z})` vanishes off `acube L` (by `hχ`) and
a.e. on it (by the slice hypothesis). -/
theorem tBamp_ae_eq_zero_of_slice {N : ℕ} {L : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube L → χ z = 0)
    {Φ : Submission.BoseGases.X N → ℝ} {i : Fin N} (p : EuclideanSpace ℝ (Fin 3))
    (hsl : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)),
      (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Function.update x i z))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0) :
    (fun x : Submission.BoseGases.X N => Work.SmallBoxTBWord.tBamp χ p Φ i x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0 := by
  filter_upwards [hsl] with x hx
  have hmem := (MeasureTheory.ae_restrict_iff'
    (Submission.BoseGases.acube_measurable L)).mp hx
  rw [Work.SmallBoxTBWord.tBamp]
  have hzero : (fun z : EuclideanSpace ℝ (Fin 3) =>
      (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ)) =ᵐ[(MeasureTheory.volume : Measure ℝ³)] 0 := by
    filter_upwards [hmem] with z hz
    simp only [Pi.zero_apply] at hz
    by_cases h : z ∈ Submission.BoseGases.acube L
    · rw [hz h]; simp
    · rw [hχ z h]; simp
  rw [MeasureTheory.integral_congr_ae hzero]
  simp

/-! ## 5. The spectral half of `𝒯_B` vanishes -/

/-- **The `p`-diagonal kinetic form vanishes** when every slot slice of `Q_{B,i}Ψ` is a.e. zero
and `χ` is supported in `acube L`.  For each `p` the inner `x`-integral of `‖tBamp‖²` vanishes
(`tBamp_ae_eq_zero_of_slice`), so the `p`-integrand is identically `0`. -/
theorem tBdiagFormInd_eq_zero_of_slice {N : ℕ} {L : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (F : ℝ → ℝ) {Ψ : Submission.BoseGases.X N → ℝ}
    (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube L → χ z = 0)
    (hsl : ∀ i : Fin N,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)),
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.boxQInd volA A i Ψ (Function.update x i z))
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0) :
    Work.UBBInputs8.tBdiagFormInd L A volA χ F Ψ = 0 := by
  unfold Work.UBBInputs8.tBdiagFormInd
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hInt : ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫ x in Submission.BoseGases.abox N L,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) = 0 := by
    intro p
    have hb := tBamp_ae_eq_zero_of_slice (N := N) (L := L) hχ (i := i) p (hsl i)
    refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [(MeasureTheory.ae_restrict_iff'
      (Submission.BoseGases.abox_measurable N L)).mp hb] with x hx
    simp only [Pi.zero_apply] at hx
    intro hxmem
    rw [hx hxmem]; simp
  have hpzero : (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ * ((L ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox N L,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)) = 0 := by
    have hz : (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ * ((L ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox N L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2))
        = fun _ => 0 := by
      funext p; rw [hInt p]; ring
    rw [hz]; simp
  rw [hpzero]; ring

/-! ## 6. The potential word -/

/-- **The localised potential word vanishes** on a state vanishing a.e. on the big box: it is an
integral over `abox N L` of `(Ψ x)²` against a state-independent kernel. -/
theorem qLHSwordB_eq_zero_of_ae_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} {L d μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {N : ℕ}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (h0 : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0) :
    Work.SmallBoxSliding.qLHSwordB (v := v) h M L d μ u Ψ = 0 := by
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
  refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [(MeasureTheory.ae_restrict_iff'
    (Submission.BoseGases.abox_measurable N L)).mp h0] with x hx
  simp only [Pi.zero_apply] at hx
  intro hxmem
  rw [hx hxmem]; ring

/-! ## 7. The support of the window `χ_{B(u)}` -/

/-- The window `chiB L d u` vanishes off `acube L` (its first factor is
`chiScale L`, supported in `acube L`). -/
theorem chiB_vanishes_off_acube {L d : ℝ} (hL : 0 < L) (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube L →
      Submission.BoseGases.chiB L d u z = 0 := by
  intro z hz
  rw [Submission.BoseGases.chiB]
  have h0 : Submission.BoseGases.chiScale L z = 0 := by
    by_contra hne
    exact hz (Submission.BoseGases.chiScale_mem_acube hL hne)
  rw [h0, zero_mul]

/-! ## 8. The sliding kinetic word vanishes -/

/-- **`tBwordBInd` vanishes** on a state vanishing a.e. on the big box: combine the excited count
and the spectral form. -/
theorem tBwordBInd_eq_zero_of_ae_eq_zero {N : ℕ} {L d ε c : ℝ} (hL : 0 < L)
    (u : EuclideanSpace ℝ (Fin 3)) {Ψ : Submission.BoseGases.X N → ℝ}
    (h0 : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0) :
    Work.UBBInputs8.tBwordBInd N L d ε c u Ψ = 0 := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox L d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox L d u
  have hAc : Submission.BoseGases.dlBox L d u ⊆ Submission.BoseGases.acube L :=
    Work.SmallBoxSliding.dlBox_subset_acube L d u
  have hcn := cnPlusBoxInd_eq_zero_of_ae_eq_zero
    (volA := Work.SmallBoxSliding.boxMass L d u) hA hAc h0
  have hQ : ∀ i : Fin N,
      Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i Ψ
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)] 0 := fun i =>
    boxQInd_ae_eq_zero_of_ae_eq_zero (volA := Work.SmallBoxSliding.boxMass L d u) hA hAc h0
  have hslQ : ∀ i : Fin N,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N L)),
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i Ψ (Function.update x i z))
          =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.acube L)] 0 := fun i =>
    sliceAe_eq_zero (hQ i)
  have htbd := tBdiagFormInd_eq_zero_of_slice (A := Submission.BoseGases.dlBox L d u)
    (volA := Work.SmallBoxSliding.boxMass L d u) (χ := Submission.BoseGases.chiB L d u)
    (Submission.BoseGases.fsKinCoeff c) (chiB_vanishes_off_acube hL u) hslQ
  rw [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
    hcn, htbd]
  ring

/-! ## 9. The target -/

theorem fibreWord_ae_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (M k : ℕ) (L d ε c μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {Ψ : Submission.BoseGases.X k → ℝ}
    (hL : 0 < L)
    (h0 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox k L)), Ψ x = 0) :
    Work.SlotWord.fibreWord h M k L d ε c μ u Ψ = 0 := by
  have hkin := tBwordBInd_eq_zero_of_ae_eq_zero (N := k) (L := L) (d := d) (ε := ε) (c := c) hL u h0
  have hpot := qLHSwordB_eq_zero_of_ae_eq_zero (h := h) (M := M) (L := L) (d := d) (μ := μ)
    (u := u) h0
  rw [Work.SlotWord.fibreWord, hkin, hpot]
  ring

end Work.BoseFixB1B
