import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_slotExact_compl_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotExact_indicator_abox_ae` — the sector only sees the state inside the box

A state `Ψ` and its restriction `1_{Λ^N} Ψ` to the `N`-particle cube `abox n ℓ` have the *same*
`S`-sector, as functions of the configuration, at every configuration that lies in the box.
The reason is the mode support `supp (e l) ⊆ boxL ℓ = acube ℓ` (`boxL_eq_acube_of_pos`): in the
slot projection `slotProj e T Φ x` the slots in `T` are integrated against the kernel
`PV e (x i) (z i)`, which vanishes as soon as *either* argument leaves the box
(`PV_apply_eq_zero_of_notMem_boxL` for the first, `PV_eq_zero_of_notMem_boxL_right` below for the
second).  Hence at a box configuration `x` the integrand of `slotProj e T Ψ x` is supported on
those `z` for which the "modified configuration" `fun i => if i ∈ T then z i else x i` still lies
in the box; there the indicator `1_{Λ^N}` acts as the identity, and the two integrands are the
same function of `z`, so the integrals agree (integrability is irrelevant: the integrands are
pointwise equal).  Summing the inclusion–exclusion expansion over `T ⊇ S` gives the sector
equality, and since it holds at *every* point of the box, it holds a.e. for the restricted measure
`volume.restrict (abox n ℓ)`.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The projection kernel vanishes off the box in its second argument**: with the modes
supported in `boxL ℓ`, `PV e x y = 0` for *every* `x` as soon as `y ∉ boxL ℓ` (in the product
`e l x * conj (e l y)` the second factor vanishes). -/
lemma PV_eq_zero_of_notMem_boxL_right {ℓ : ℝ} {m : ℕ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {x y : E3} (hy : y ∉ Work.BoseK15.corpusBox.boxL ℓ) : PV e x y = 0 := by
  unfold PV
  refine Finset.sum_eq_zero fun l _ => ?_
  have he : e l y = 0 := Function.notMem_support.mp fun hmem => hy (hsupp l hmem)
  rw [he]
  simp

/-- **At a box configuration the slot projection of `Φ` and of `1_{Λ^N} Φ` coincide.**  For
`x ∈ abox n ℓ` and every `z`, the two integrands of `slotProj` agree: either the modified
configuration `fun i => if i ∈ T then z i else x i` is in the box (and the indicator acts as the
identity), or some slot of it leaves the box — and since the unmodified coordinates `x i` are all
in the box, that slot must be projected, so the corresponding `PV`-factor of the product kernel
vanishes (`PV_eq_zero_of_notMem_boxL_right`, via `boxL ℓ = acube ℓ`). -/
lemma slotProj_indicator_abox_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {n m : ℕ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {Φ : Submission.BoseGases.X n → ℂ} {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    slotProj e T Φ x = slotProj e T ((Submission.BoseGases.abox n ℓ).indicator Φ) x := by
  have hxmem : ∀ i : Fin n, x i ∈ Submission.BoseGases.acube ℓ := by
    simpa [Submission.BoseGases.abox] using hx
  unfold slotProj
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  let w : Submission.BoseGases.X n := fun i => if h : i ∈ T then z ⟨i, h⟩ else x i
  show (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) * Φ w
      = (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) *
        ((Submission.BoseGases.abox n ℓ).indicator Φ) w
  by_cases hw : w ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hw]
  · rw [Set.indicator_of_notMem hw]
    have hesc : ∃ j : Fin n, w j ∉ Submission.BoseGases.acube ℓ := by
      simpa [Submission.BoseGases.abox] using hw
    obtain ⟨j, hj⟩ := hesc
    have hjT : j ∈ T := by
      by_contra hjT
      have hwj' : w j = x j := dif_neg hjT
      rw [hwj'] at hj
      exact hj (hxmem j)
    have hwj : w j = z ⟨j, hjT⟩ := dif_pos hjT
    have hznot : z ⟨j, hjT⟩ ∉ Work.BoseK15.corpusBox.boxL ℓ := by
      rw [boxL_eq_acube_of_pos hℓ]
      exact fun h => hj (hwj ▸ h)
    have hPV : PV e (x j) (z ⟨j, hjT⟩) = 0 :=
      PV_eq_zero_of_notMem_boxL_right hsupp hznot
    have hprod : (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ⟨j, hjT⟩) hPV
    rw [hprod]
    simp

/-- **The sector equality at a box configuration**: summing `slotProj_indicator_abox_eq` over the
supersets `T ⊇ S` of the inclusion–exclusion expansion. -/
lemma slotExact_indicator_abox_eq_of_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {n m : ℕ}
    {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : Submission.BoseGases.X n → ℂ)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    slotExact e S Φ x = slotExact e S ((Submission.BoseGases.abox n ℓ).indicator Φ) x := by
  unfold slotExact
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Pi.smul_apply]
  rw [slotProj_indicator_abox_eq hℓ hsupp T hx]

theorem slotExact_indicator_abox_ae {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΨ : MeasureTheory.MemLp Ψ ⊤) :
    (fun x => Work.BoseBoxFock.slotExact e S Ψ x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
            (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => Work.BoseBoxFock.slotExact e S
        ((Submission.BoseGases.abox n ℓ).indicator Ψ) x) := by
  exact ae_restrict_of_forall_mem (Submission.BoseGases.abox_measurable n ℓ)
    fun x hx => slotExact_indicator_abox_eq_of_mem hℓ hsupp S Ψ hx

end Work.BoseBoxFock
