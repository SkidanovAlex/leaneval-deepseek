import Mathlib.CategoryTheory.Countable
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FibreWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FibreWord

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission.BoseGases Work.PerSector Work.UBB Work.SmallBoxSliding Work.UBBInputs8 Work.BlockBound4 Work.KinPSuperadd Work.SlotWord Work.SmallBoxTBWord Work.FibreWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The vanishing of a fibre mass forces the fibre to vanish a.e.

`fibMass L d u S Φ y` is (the real part of) the box `L²`-mass of the fibre of the slot piece
`1_{slotSet (dlBox L d u) S}·Φ`.  The content of this file is the elementary "if an `L²`-mass is
zero, the function is zero a.e." statement for this mass, together with the *finiteness* of that
mass which is needed to pass from the `ENNReal`-valued `lintegral` to its real part.

The finiteness is where the continuity hypothesis `Continuous Φ` is used: on the box `B^{S}` the
fibre `z ↦ Φ (slotComb S z y)` is the composition of the continuous `Φ` with the continuous
reassembly map, and `B ⊆ acube L` is bounded (indeed the box `B^{S}` sits inside the compact
`acube L^{S}`), so the integrand is bounded and the mass is finite. -/

/-- **Continuity of the reassembly map in its in-box variable**: for fixed outside configuration
`y`, the map `z ↦ slotComb S z y` is continuous (it replaces the slots of `S` by the coordinates of
`z` and leaves the others at `y`). -/
lemma continuous_slotComb_snd {N : ℕ} (S : Finset (Fin N)) (y : SlotOut N S → ℝ³) :
    Continuous (fun z : SlotIn N S → ℝ³ => slotComb S z y) := by
  rw [continuous_pi_iff]
  intro i
  rw [show (fun z : SlotIn N S → ℝ³ => slotComb S z y i)
      = (fun z => if h : i ∈ S then z ⟨i, h⟩ else y ⟨i, h⟩) from by
        funext z; rw [slotComb_apply]]
  by_cases h : i ∈ S
  · simp only [dif_pos h]
    exact (continuous_apply (A := fun _ : SlotIn N S => ℝ³) ⟨i, h⟩)
  · simp only [dif_neg h]; exact continuous_const

/-- **The fibre mass of a slot piece is finite.**  For `0 < L` and continuous `Φ`, the `ENNReal`
box mass of the fibre of the slot piece `slotPiece (dlBox L d u) S Φ` is `≠ ⊤`.

The proof bounds the integrand by a constant: `slotBox (acube L) ⊇ slotBox (dlBox L d u)` is
compact, the function `z ↦ Φ (slotComb S z y)` is continuous on it, and the slot piece is
pointwise dominated by `Φ` in absolute value, so the integral is at most
`ofReal C² · volume (slotBox (acube L))`, which is finite. -/
lemma lintegral_slotPiece_ne_top {N : ℕ} {L d : ℝ} (hL : 0 < L)
    (u : ℝ³) (S : Finset (Fin N)) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (y : SlotOut N S → ℝ³) :
    (∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u),
        ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2)) ≠ ⊤ := by
  have hGcont : Continuous (fun z : SlotIn N S → ℝ³ => Φ (slotComb S z y)) :=
    hΦc.comp (continuous_slotComb_snd S y)
  have hcomp : IsCompact (slotBox (ι := SlotIn N S) (acube L)) := by
    rw [show slotBox (ι := SlotIn N S) (acube L)
        = Set.univ.pi (fun _ : SlotIn N S => acube L) from by
          ext z; simp [slotBox]]
    exact isCompact_univ_pi (fun _ => acube_compact hL)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hGcont.continuousOn
  have hCbound : ∀ z ∈ slotBox (ι := SlotIn N S) (acube L), ‖Φ (slotComb S z y)‖ ≤ |C| :=
    fun z hz => le_trans (hC z hz) (le_abs_self C)
  have hbdd : ∀ z ∈ slotBox (ι := SlotIn N S) (dlBox L d u),
      ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2)
        ≤ ENNReal.ofReal ((|C|)^2) := by
    intro z hz
    have hz' : z ∈ slotBox (ι := SlotIn N S) (acube L) :=
      Work.PerSector.slotBox_mono (dlBox_subset_acube L d u) hz
    have hCz : ‖Φ (slotComb S z y)‖ ≤ |C| := hCbound z hz'
    have habs : |slotPiece (dlBox L d u) S Φ (slotComb S z y)| ≤ |Φ (slotComb S z y)| := by
      rw [slotPiece]
      by_cases hmem : slotComb S z y ∈ slotSet (dlBox L d u) S
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]; simp
    refine ENNReal.ofReal_le_ofReal ?_
    calc (slotPiece (dlBox L d u) S Φ (slotComb S z y))^2
        ≤ (Φ (slotComb S z y))^2 := (sq_le_sq).mpr habs
      _ ≤ (|C|)^2 := by
          refine (sq_le_sq).mpr ?_
          rw [abs_of_nonneg (abs_nonneg C)]
          simpa [Real.norm_eq_abs] using hCz
  have hsmeas : MeasurableSet (slotBox (ι := SlotIn N S) (dlBox L d u)) :=
    Work.PerSector.slotBox_measurable (measurableSet_dlBox L d u)
  have hvol : (volume : Measure (SlotIn N S → ℝ³))
      (slotBox (ι := SlotIn N S) (acube L)) ≠ ⊤ := by
    rw [show slotBox (ι := SlotIn N S) (acube L)
        = Set.univ.pi (fun _ : SlotIn N S => acube L) from by
          ext z; simp [slotBox]]
    rw [volume_pi_pi]
    refine ne_of_lt (ENNReal.prod_lt_top (fun i _ => ?_))
    rw [acube_volume L hL.le]
    exact ENNReal.ofReal_lt_top
  have hbound : (∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u),
        ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2))
      ≤ ENNReal.ofReal ((|C|)^2) * (volume : Measure (SlotIn N S → ℝ³))
          (slotBox (ι := SlotIn N S) (acube L)) := by
    calc (∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u),
          ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2))
        ≤ ∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u), ENNReal.ofReal ((|C|)^2) := by
          apply lintegral_mono_ae
          filter_upwards [self_mem_ae_restrict hsmeas] with z hz
          exact hbdd z hz
      _ ≤ ∫⁻ z in slotBox (ι := SlotIn N S) (acube L), ENNReal.ofReal ((|C|)^2) :=
          lintegral_mono_set (Work.PerSector.slotBox_mono (dlBox_subset_acube L d u))
      _ = ENNReal.ofReal ((|C|)^2) * (volume : Measure (SlotIn N S → ℝ³))
            (slotBox (ι := SlotIn N S) (acube L)) := setLIntegral_const _ _
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (|C|)^2)) hvol) hbound

/-- **A vanishing fibre mass forces the fibre to vanish a.e.**  If the `ENNReal` box mass of the
fibre of the slot piece `slotPiece B S Φ` over `slotBox B` is zero, then the fibre transported to
`X S.card` along `e` vanishes almost everywhere.

The proof does not use anything analytic: `∫⁻ z in slotBox B, ofReal (g z ^ 2) = 0` gives
`g =ᵐ 0` by `lintegral_eq_zero_iff`, the support of `g` is contained in `slotBox B` (a nonzero
value of the slot piece forces its argument into the slot set, hence the in-box coordinates into
`B`), so the restriction to `slotBox B` may be dropped, and finally the reindexing
`x ↦ fun i => x (e i)` is measure-preserving, so it preserves the almost-everywhere statement. -/
lemma pieceFibre_ae_eq_zero_of_lintegral_eq_zero {N : ℕ} (S : Finset (Fin N))
    (e : SlotIn N S ≃ Fin S.card) {B : Set ℝ³} (hB : MeasurableSet B) {Φ : X N → ℝ}
    (hΦm : Measurable Φ) (y : SlotOut N S → ℝ³)
    (hint : (∫⁻ z in slotBox (ι := SlotIn N S) B,
        ENNReal.ofReal ((slotPiece B S Φ (slotComb S z y))^2)) = 0) :
    pieceFibre B S e Φ y =ᵐ[volume] (fun _ : X S.card => 0) := by
  set s : Set (SlotIn N S → ℝ³) := slotBox (ι := SlotIn N S) B with hs
  have hsmeas : MeasurableSet s := by rw [hs]; exact Work.PerSector.slotBox_measurable hB
  have hg_meas : Measurable (fun z : SlotIn N S → ℝ³ =>
      ENNReal.ofReal ((slotPiece B S Φ (slotComb S z y))^2)) :=
    Measurable.ennreal_ofReal
      (((slotPiece_measurable B hB S hΦm).comp (continuous_slotComb_snd S y).measurable).pow_const 2)
  have hae_s : (fun z : SlotIn N S → ℝ³ =>
      slotPiece B S Φ (slotComb S z y)) =ᵐ[volume.restrict s] (fun _ => 0) := by
    have h1 : (fun z : SlotIn N S → ℝ³ =>
        ENNReal.ofReal ((slotPiece B S Φ (slotComb S z y))^2)) =ᵐ[volume.restrict s]
        (fun _ => 0) := by
      refine (lintegral_eq_zero_iff hg_meas).mp ?_
      simpa [hs] using hint
    exact h1.mono (fun z hz => by
      have hle : (slotPiece B S Φ (slotComb S z y))^2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hz
      exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))
  have hsub : ∀ z : SlotIn N S → ℝ³,
      slotPiece B S Φ (slotComb S z y) ≠ 0 → z ∈ s := by
    intro z hz
    rw [hs]
    by_contra hznot
    exact hz (by
      rw [slotPiece]
      exact Set.indicator_of_notMem
        (fun hmem => hznot ((slotComb_mem_slotSet_iff B S z y).mp hmem).1) Φ)
  have hae_g : (fun z : SlotIn N S → ℝ³ =>
      slotPiece B S Φ (slotComb S z y)) =ᵐ[volume] (fun _ => 0) := by
    have h1 : ∀ᵐ z ∂(volume : Measure (SlotIn N S → ℝ³)),
        z ∈ s → slotPiece B S Φ (slotComb S z y) = 0 :=
      (ae_restrict_iff' hsmeas).mp hae_s
    have h2 : ∀ᵐ z ∂(volume : Measure (SlotIn N S → ℝ³)),
        z ∉ s → slotPiece B S Φ (slotComb S z y) = 0 :=
      ae_of_all _ (fun z hz => by by_contra hne; exact hz (hsub z hne))
    filter_upwards [h1, h2] with z hz1 hz2
    by_cases hz : z ∈ s
    · exact hz1 hz
    · exact hz2 hz
  let E : X S.card ≃ᵐ (SlotIn N S → ℝ³) :=
    MeasurableEquiv.piCongrLeft (fun _ : SlotIn N S => ℝ³) e.symm
  have hEm : MeasurePreserving (⇑E) volume volume :=
    measurePreserving_piCongrLeft (fun _ : SlotIn N S => (volume : Measure ℝ³)) e.symm
  have hEapp : ∀ x : X S.card, ⇑E x = fun i : SlotIn N S => x (e i) := by
    intro x
    funext i
    have hkey := MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm)
      (β := fun _ : SlotIn N S => ℝ³) (x := x) (i := e i)
    rw [Equiv.symm_apply_apply] at hkey
    exact hkey
  have hcomp : (fun x : X S.card => slotPiece B S Φ (slotComb S (fun i => x (e i)) y))
      =ᵐ[volume] (fun _ : X S.card => 0) := by
    simpa [Function.comp_def, hEapp] using hEm.quasiMeasurePreserving.ae_eq_comp hae_g
  exact hcomp

theorem fibPiece_ae_eq_zero_of_fibMass_eq_zero {N : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    (e : Work.PerSector.SlotIn N S ≃ Fin S.card) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))
    (hzero : fibMass L d u S Φ y = 0) :
    fibPiece L d u S e Φ y =ᵐ[volume] (fun _ : X S.card => 0) := by
  have hfin : (∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u),
      ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2)) ≠ ⊤ :=
    lintegral_slotPiece_ne_top hL u S hΦc y
  have hint : (∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u),
      ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2)) = 0 := by
    have hz : (∫⁻ z in slotBox (ι := SlotIn N S) (dlBox L d u),
        ENNReal.ofReal ((slotPiece (dlBox L d u) S Φ (slotComb S z y))^2)).toReal = 0 := hzero
    rcases (ENNReal.toReal_eq_zero_iff _).mp hz with h | h
    · exact h
    · exact absurd h hfin
  exact pieceFibre_ae_eq_zero_of_lintegral_eq_zero S e (measurableSet_dlBox L d u)
    hΦc.measurable y hint

end Work.FibreWord
