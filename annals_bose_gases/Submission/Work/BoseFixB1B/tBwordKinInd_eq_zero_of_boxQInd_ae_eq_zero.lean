import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FibreWord.SliceAE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.tBwordKinInd_eq_zero_of_boxQInd_ae_eq_zero`

**If the FS-faithful box mean-free projection vanishes a.e. on the particle box, the windowed
kinetic word vanishes.**

`Work.UBBInputs8.tBwordKinInd a A volA χ c Ψ = tBdiagFormInd a A volA χ (fsKinCoeff c) Ψ` is the
sum over the slots `i` of the `p`-integral of

  `fsKinCoeff c ‖p‖ · (a³)⁻¹ · ∫_{x ∈ abox N a} ‖tBamp χ p (boxQInd volA A i Ψ) i x‖²`,

and the main theorem shows that it is `0` as soon as every `boxQInd volA A i Ψ` is `0` a.e. on the
particle box `abox N a`.

## Why the *box-restricted* hypothesis suffices

The state `F := boxQInd volA A i Ψ` enters each summand only through the windowed amplitude

  `tBamp χ p F i x = ∫_z χ z · e^{−i⟪p,z⟫} · F(x ←ᵢ z) dz`,

an integral over the slice variable `z`.  The window `χ` is supported in `A ⊆ acube a`, and the two
features of the centred box `abox N a = (acube a)ᴺ` that make this work are

* the slice map `Tᵢ` is *internal* on the box: for `x ∈ abox N a` and `z ∈ acube a` one has
  `Function.update x i z ∈ abox N a`; and
* the slice map is quasi-measure-preserving, so the *box-restricted* null set
  `{F ≠ 0} ∩ abox N a` propagates to a.e. `x`-slice — this is
  `Work.FibreWord.quasiMeasurePreserving_update` (the slice-a.e. foundation of `Work.FibreWord`).

Both steps are assembled in the auxiliary lemma
`tBamp_integral_sq_eq_zero_of_ae_eq_zero`: first `F` is replaced by its box-restricted indicator
`Q = 1_{abox N a}·F`, which is a.e. zero on the *whole* space (so the global a.e.-slice machinery
applies), and then the pointwise identity `Q (x ←ᵢ z) = F (x ←ᵢ z)` for `x ∈ abox`, `z ∈ A` closes
the amplitude.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
-- the fixed statement of the target carries hypotheses (`ha`, `hA`, `hχm`, `hΨm`) which the
-- proof does not need; they are part of the interface and must not be removed.
set_option linter.unusedVariables false

/-- **The windowed amplitude of a state which vanishes a.e. on the particle box.**  If
`F =ᵐ[volume.restrict (abox N a)] 0` and the window `χ` is supported in `A ⊆ acube a`, then the
`p`-amplitude `tBamp χ p F i ·` has vanishing `L²`-norm on the box.

The proof replaces `F` by the box-restricted indicator `Q = 1_{abox N a}·F` (a.e. zero on the whole
space, hence a.e. zero along every `i`-slice, by quasi-measure-preservation of the slice map
`Function.update`), and then uses that a slice `x ←ᵢ z` of a box point `x` at `z ∈ A ⊆ acube a` is
again a box point. -/
theorem tBamp_integral_sq_eq_zero_of_ae_eq_zero {N : ℕ} {a : ℝ} {A : Set ℝ³} {χ : ℝ³ → ℝ}
    {F : Submission.BoseGases.X N → ℝ} (i : Fin N) (p : ℝ³)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    (hF : F =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)] 0) :
    ∫ x in Submission.BoseGases.abox N a, ‖Work.SmallBoxTBWord.tBamp χ p F i x‖ ^ 2 = 0 := by
  -- the box-restricted null set where `F` fails to vanish
  have hFnull : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))
      ({x | F x ≠ 0} ∩ Submission.BoseGases.abox N a) = 0 := by
    have h : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)), F x = 0 := hF
    rw [MeasureTheory.ae_iff] at h
    rw [Measure.restrict_apply' (Submission.BoseGases.abox_measurable N a)] at h
    simpa using h
  -- the box-restricted indicator of `F` is a.e. zero on the whole space
  set Q : Submission.BoseGases.X N → ℝ :=
    (Submission.BoseGases.abox N a).indicator F with hQdef
  have hQae : Q =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))]
      (0 : Submission.BoseGases.X N → ℝ) := by
    change ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)),
      Q x = 0
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun x hx => ?_) hFnull
    have hxmem : x ∈ Submission.BoseGases.abox N a := by
      by_contra h
      refine hx ?_
      rw [hQdef]
      exact Set.indicator_of_notMem h F
    refine ⟨?_, hxmem⟩
    intro hFx
    refine hx ?_
    rw [hQdef]
    exact Set.indicator_of_mem hxmem F ▸ hFx
  -- quasi-measure-preservation of the slice map turns that into an a.e. statement on slices
  have hslice : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)),
      (fun z : ℝ³ => Q (Function.update x i z))
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ³)] (0 : ℝ³ → ℝ) := by
    have hcomp : Function.uncurry (fun (x : Submission.BoseGases.X N) (z : ℝ³) =>
          Q (Function.update x i z))
        =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ³))]
        Function.uncurry (fun (x : Submission.BoseGases.X N) (z : ℝ³) => (0 : ℝ)) :=
      (Work.FibreWord.quasiMeasurePreserving_update i).ae_eq hQae
    exact Measure.ae_ae_eq_of_ae_eq_uncurry hcomp
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  have hself : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)),
      x ∈ Submission.BoseGases.abox N a :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable N a)
  filter_upwards [hslice.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self), hself]
    with x hx hxab
  -- the amplitude vanishes: the window is supported in `A`, and on `A` the slice lies in the box
  have ht : Work.SmallBoxTBWord.tBamp χ p F i x = 0 := by
    rw [Work.SmallBoxTBWord.tBamp]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [hx] with z hz
    by_cases hzA : z ∈ A
    · have hupd : Function.update x i z ∈ Submission.BoseGases.abox N a := by
        rw [Submission.BoseGases.mem_abox_iff]
        intro j
        rw [Submission.BoseGases.mem_abox_iff] at hxab
        rcases eq_or_ne j i with rfl | hj
        · rw [Function.update_self]; exact hAc hzA
        · rw [Function.update_of_ne hj]; exact hxab j
      have hQval : Q (Function.update x i z) = F (Function.update x i z) := by
        rw [hQdef]; exact Set.indicator_of_mem hupd F
      rw [← hQval, hz]; simp
    · rw [hχsupp z hzA]; simp
  rw [ht]; simp

/-- **The target.**  If every FS box mean-free projection of `Ψ` vanishes a.e. on the particle box
`abox N a`, then the windowed kinetic word of `Ψ` vanishes.  The window `χ` must be supported in
`A ⊆ acube a` — this is what keeps the windowed amplitude's slice integral inside the box. -/
theorem tBwordKinInd_eq_zero_of_boxQInd_ae_eq_zero {N : ℕ} {a volA c : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Ψ : Submission.BoseGases.X N → ℝ}
    (ha : 0 < a) (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube a)
    (hχm : Measurable χ) (hχsupp : ∀ z, z ∉ A → χ z = 0) (hΨm : Measurable Ψ)
    (hbox : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)] 0) :
    Work.UBBInputs8.tBwordKinInd a A volA χ c Ψ = 0 := by
  unfold Work.UBBInputs8.tBwordKinInd Work.UBBInputs8.tBdiagFormInd
  refine Finset.sum_eq_zero fun i _ => ?_
  have hinner : ∀ p : ℝ³,
      (∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) = 0 :=
    fun p => tBamp_integral_sq_eq_zero_of_ae_eq_zero i p hAc hχsupp (hbox i)
  have h0 : (∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)) = 0 := by
    simp only [hinner]
    simp
  rw [h0, mul_zero]

end Work.BoseFixB1B
