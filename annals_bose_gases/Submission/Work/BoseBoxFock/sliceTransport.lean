import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.exists_slice_le_window
import Submission.Work.BoseBoxFock.sliceModelWindow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceTransport` — the `↥S`/`Fin S.card` transport of the BF3c slice layer

The BF3c pipeline produces its state (`Work.BoseBoxFock.exists_slice_le_window`) in the
`↥S`-indexed description of the sector (`sectorSlice e S Φ y : ({i // i ∈ S} → Ω) → ℂ`, with the
slot sum `slotSumSub e T S`), while the model consumes the `Fin S.card`-indexed description
(`sliceF e S Φ y`, `Work.BoseDict.boxSlotSum e T`, `Work.BoseDict.boxRealise e (S.card)`).

This module carries the dictionary between the two:

* `sliceEquiv S : (Fin S.card → Ω) ≃ᵐ ({i // i ∈ S} → Ω)` — the reindexing along `S.equivFin`,
  with `sliceEquiv_apply` (`sliceEquiv S x i = x (S.equivFin i)`) and
  `measurePreserving_sliceEquiv`;
* `boxSlotOf_sliceEquiv` / `boxSlotSum_slice` — the *pointwise* identity: the box slot sum of the
  reindexed slice is the `↥S`-slot sum of the slice (`Work.BoseBoxFock.boxSlotOf_pairCoord`'s
  `Fin S.card` twin);
* `cIPn_sliceF_eq_sectorSlice` / `cIPn_sliceF_self_eq` — the *integral* form of the same identity,
  obtained from `MeasurePreserving.integral_comp'` (no integrability hypothesis: the change of
  variables along a measurable equivalence is an identity of Bochner integrals);
* `sliceModelWindow_deg` — the strengthened `Work.BoseBoxFock.sliceModelWindow`: the two real
  model vectors of the slice not only lie in `ExcWindow M n`, they are *homogeneous of degree*
  `S.card` (which is what the dictionary rows `bomb_dGamma_slot` / `boxRealise_cIPn_gen` need).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The reindexing of the `S`-slots by `Fin S.card` -/

/-- The measurable equivalence `(Fin S.card → Ω) ≃ᵐ ({i // i ∈ S} → Ω)` induced by
`S.equivFin`: `x ↦ (i ↦ x (S.equivFin i))`.  (The `KinLoc` counterpart for the order iso
`slotIso S` is `Work.BoseKinLoc.Sector.slotIsoME`.) -/
noncomputable def sliceEquiv {n : ℕ} (S : Finset (Fin n)) :
    (Fin S.card → Ω) ≃ᵐ ({i // i ∈ S} → Ω) :=
  MeasurableEquiv.piCongrLeft (fun _ : {i // i ∈ S} => Ω) S.equivFin.symm

/-- The value of `sliceEquiv S`. -/
lemma sliceEquiv_apply {n : ℕ} (S : Finset (Fin n)) (x : Fin S.card → Ω)
    (i : {i // i ∈ S}) : sliceEquiv S x i = x (S.equivFin i) := by
  have h1 := Equiv.piCongrLeft_apply_apply (P := fun _ : {i // i ∈ S} => Ω)
    (e := S.equivFin.symm) x (S.equivFin i)
  rwa [Equiv.symm_apply_apply] at h1

/-- The function form of `sliceEquiv_apply`. -/
lemma sliceEquiv_coe {n : ℕ} (S : Finset (Fin n)) :
    ⇑(sliceEquiv S) = fun x : Fin S.card → Ω => fun i : {i // i ∈ S} => x (S.equivFin i) :=
  funext fun x => funext fun i => sliceEquiv_apply S x i

/-- `sliceEquiv S` is measure preserving (both sides carry `volume`). -/
lemma measurePreserving_sliceEquiv {n : ℕ} (S : Finset (Fin n)) :
    MeasurePreserving (sliceEquiv S) volume volume :=
  volume_measurePreserving_piCongrLeft _ S.equivFin.symm

/-- `sliceF` is the composition of the `↥S`-indexed slice with `sliceEquiv`. -/
lemma sliceF_eq_comp {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) :
    sliceF e S Φ y = (sectorSlice e S Φ y) ∘ (sliceEquiv S) := by
  funext x
  rw [Function.comp_apply, sliceEquiv_coe]
  rfl

/-! ## 2. The pointwise identity of the slot sums -/

/-- **The `↥S`-slot operator of the reindexed slice.**  For a slot `j` of `S`, the box slot
`Work.BoseDict.boxSlotOf` at the slot `S.equivFin j` applied to the reindexed slice equals the
`↥S`-slot operator `slotOfSub` at `j` applied to the slice.  The two ingredients are
`sliceEquiv_apply` (the slot value) and the fact that `Function.update` commutes with
`sliceEquiv`. -/
lemma boxSlotOf_sliceEquiv {m n : ℕ} (e : Fin m → Ω → ℂ) (w v : Fin m → ℝ)
    (S : Finset (Fin n)) (Ψ : ({i // i ∈ S} → Ω) → ℂ)
    (j : {i // i ∈ S}) (u : Fin S.card → Ω) :
    Work.BoseDict.boxSlotOf e w v (S.equivFin j) (fun x => Ψ (sliceEquiv S x)) u
      = slotOfSub e w v j Ψ (sliceEquiv S u) := by
  have hslot : (sliceEquiv S u) j = u (S.equivFin j) := sliceEquiv_apply S u j
  rw [Work.BoseDict.boxSlotOf, slotOfSub, hslot]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  beta_reduce
  congr 1
  have h2 : ∀ i : {i // i ∈ S}, sliceEquiv S (Function.update u (S.equivFin j) z) i
      = Function.update (sliceEquiv S u) j z i := by
    intro i
    rw [sliceEquiv_apply, Function.update_apply, Function.update_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (fun h : S.equivFin i = S.equivFin j => hij (S.equivFin.injective h)),
        if_neg hij, sliceEquiv_apply]
  rw [congrArg Ψ (funext h2)]

/-- **The pointwise decoupling in the `Fin S.card` indexing.**  The box slot sum of the reindexed
slice, read at the configuration `u`, is the `↥S`-slot sum of the slice read at `sliceEquiv S u`.
This is `Work.BoseBoxFock.boxSlotSum_pairCoord` transported along `S.equivFin` (the reindexing is
`Equiv.sum_comp`, and the summand is `boxSlotOf_sliceEquiv`). -/
lemma boxSlotSum_slice {m n : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Ψ : ({i // i ∈ S} → Ω) → ℂ) (u : Fin S.card → Ω) :
    Work.BoseDict.boxSlotSum e T (fun x => Ψ (sliceEquiv S x)) u
      = slotSumSub e T S Ψ (sliceEquiv S u) := by
  rw [Work.BoseDict.boxSlotSum, slotSumSub]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [← Equiv.sum_comp S.equivFin (fun j : Fin S.card =>
      ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (fun x => Ψ (sliceEquiv S x)) u)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [boxSlotOf_sliceEquiv]

/-! ## 3. The integral form (the change of variables) -/

/-- **The form decoupling in the `Fin S.card` indexing.**  The complex pairing of the reindexed
slice with its box slot sum equals the `↥S`-indexed pairing of the slice with its slot sum.
`MeasurePreserving.integral_comp'` along `sliceEquiv S` (no integrability hypothesis), with the
pointwise identity `boxSlotSum_slice`. -/
lemma cIPn_sliceF_eq_sectorSlice {m n : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) :
    Work.BoseDict.cIPn S.card (sliceF e S Φ y)
        (Work.BoseDict.boxSlotSum e T (sliceF e S Φ y))
      = ∫ u : {i // i ∈ S} → Ω,
          (starRingEnd ℂ) (sectorSlice e S Φ y u)
            * slotSumSub e T S (sectorSlice e S Φ y) u := by
  have hfun : sliceF e S Φ y = fun v => sectorSlice e S Φ y (sliceEquiv S v) := by
    funext v
    rw [sliceEquiv_coe]
    rfl
  have hpt : ∀ x : Fin S.card → Ω,
      (starRingEnd ℂ) (sliceF e S Φ y x)
          * Work.BoseDict.boxSlotSum e T (sliceF e S Φ y) x
        = (starRingEnd ℂ) (sectorSlice e S Φ y (sliceEquiv S x))
          * slotSumSub e T S (sectorSlice e S Φ y) (sliceEquiv S x) := by
    intro x
    rw [hfun, boxSlotSum_slice]
  rw [Work.BoseDict.cIPn]
  rw [show (∫ x : Fin S.card → Ω,
        (starRingEnd ℂ) (sliceF e S Φ y x)
          * Work.BoseDict.boxSlotSum e T (sliceF e S Φ y) x)
      = ∫ x : Fin S.card → Ω,
        (starRingEnd ℂ) (sectorSlice e S Φ y (sliceEquiv S x))
          * slotSumSub e T S (sectorSlice e S Φ y) (sliceEquiv S x) from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact MeasurePreserving.integral_comp' (f := sliceEquiv S) (measurePreserving_sliceEquiv S)
    (fun u : {i // i ∈ S} → Ω =>
      (starRingEnd ℂ) (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u)

/-- **The norm decoupling in the `Fin S.card` indexing.**  The real mass of the reindexed slice is
the `↥S`-indexed integral of the squared norm of the slice. -/
lemma cIPn_sliceF_self_eq {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) :
    (Work.BoseDict.cIPn S.card (sliceF e S Φ y) (sliceF e S Φ y)).re
      = ∫ u : {i // i ∈ S} → Ω, ‖sectorSlice e S Φ y u‖ ^ 2 := by
  have h1 : (Work.BoseDict.cIPn S.card (sliceF e S Φ y) (sliceF e S Φ y)).re
      = massR (sliceF e S Φ y) := by
    simp only [Work.BoseDict.cIPn, massR, starRingEnd_apply]
  have hpt : ∀ x : Fin S.card → Ω,
      ‖sliceF e S Φ y x‖ ^ 2 = ‖sectorSlice e S Φ y (sliceEquiv S x)‖ ^ 2 := by
    intro x
    rw [sliceEquiv_coe]
    rfl
  rw [h1, massR_eq_integral_normSq]
  rw [show (∫ x : Fin S.card → Ω, ‖sliceF e S Φ y x‖ ^ 2)
      = ∫ x : Fin S.card → Ω, ‖sectorSlice e S Φ y (sliceEquiv S x)‖ ^ 2 from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact MeasurePreserving.integral_comp' (f := sliceEquiv S) (measurePreserving_sliceEquiv S)
    (fun u : {i // i ∈ S} → Ω => ‖sectorSlice e S Φ y u‖ ^ 2)

/-! ## 4. The strengthened window lemma -/

/-- **The two real model vectors of the selected slice, with the excited window and their degree.**
The strengthened form of `Work.BoseBoxFock.sliceModelWindow`: the two vectors it produces are
`realPart`/`imagPart` of the degree-`S.card` part of the `CFock` vector realising the slice, hence
*homogeneous of degree* `S.card` — which is exactly the hypothesis under which the dictionary rows
(`Work.BoseDict.bomb_dGamma_slot`, `Work.BoseDict.boxRealise_cIPn_gen`) apply. -/
theorem sliceModelWindow_deg {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (e : Fin m → Ω → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n), (fun x : Fin n → Ω => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → Ω)
    (hG : ∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
      ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α) (sliceF e S Φ y) = 0) :
    ∃ Ψ₁ Ψ₂ : Work.BoseB4.RealFock m,
      Work.BoseDict.boxRealise e S.card Ψ₁ + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂
        = sliceF e S Φ y ∧
      ExcWindow M n Ψ₁ ∧ ExcWindow M n Ψ₂ ∧
      (∀ α ∈ Ψ₁.support, α.sum (fun _ k => k) = S.card) ∧
      (∀ α ∈ Ψ₂.support, α.sum (fun _ k => k) = S.card) := by
  classical
  obtain ⟨Ψc, hΨc⟩ := exists_boxRealiseC_eq_sliceF e hcont hcomp S Φ hΦ hΦc hΦsym y
  set Ψc' : CFock m := Ψc.filter (fun α : Fin m →₀ ℕ => α.sum (fun _ k => k) = S.card)
    with hΨc'def
  have hdeg : ∀ α ∈ Ψc'.support, α.sum (fun _ k => k) = S.card := by
    intro α hα
    rw [hΨc'def, Finsupp.support_filter] at hα
    exact (Finset.mem_filter.mp hα).2
  have hreal : boxRealiseC e S.card Ψc' = sliceF e S Φ y := by
    rw [hΨc'def]
    exact (boxRealiseC_filter e Ψc).trans hΨc
  have hwin : ∀ α ∈ Ψc'.support, ((S.card - α 0 : ℕ) : ℝ) ≤ (⌊M⌋₊ : ℝ) :=
    sliceWindow_of_coeff_zero (ℓ := ℓ) (M := M) e horth hbdd hsupp Ψc' (sliceF e S Φ y)
      hreal hdeg hG
  have hsub : ∀ Ψ : Work.BoseB4.RealFock m, Ψ = realPart Ψc' ∨ Ψ = imagPart Ψc' →
      Ψ.support ⊆ Ψc'.support := by
    intro Ψ hΨ
    rcases hΨ with h | h
    · rw [h]; exact Finsupp.support_mapRange
    · rw [h]; exact Finsupp.support_mapRange
  have hbranch : ∀ Ψ : Work.BoseB4.RealFock m, Ψ = realPart Ψc' ∨ Ψ = imagPart Ψc' →
      ExcWindow M n Ψ := by
    intro Ψ hΨ
    rw [excwindow_iff]
    refine ⟨fun α hα => ?_, fun α hα => ?_⟩
    · have hd := hdeg α (hsub Ψ hΨ hα)
      calc deg α = α.sum (fun _ k => k) := rfl
        _ = S.card := hd
        _ ≤ n := by simpa using Finset.card_le_univ S
    · have hd := hdeg α (hsub Ψ hΨ hα)
      have h1 := hwin α (hsub Ψ hΨ hα)
      have h2 : S.card - α 0 ≤ ⌊M⌋₊ := Nat.cast_le.mp h1
      have h3 : S.card ≤ ⌊M⌋₊ + α 0 := Nat.sub_le_iff_le_add.mp h2
      calc deg α = α.sum (fun _ k => k) := rfl
        _ = S.card := hd
        _ ≤ ⌊M⌋₊ + α 0 := h3
  refine ⟨realPart Ψc', imagPart Ψc', ?_, hbranch _ (Or.inl rfl), hbranch _ (Or.inr rfl),
    fun α hα => hdeg α (hsub _ (Or.inl rfl) hα), fun α hα => hdeg α (hsub _ (Or.inr rfl) hα)⟩
  rw [← boxRealiseC_eq_re_add_im e Ψc']
  exact hreal

end Work.BoseBoxFock
