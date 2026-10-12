import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.ae_ae_slice_regular
import Submission.Work.BoseBoxFock.modeProd_support_subset_abox
import Submission.Work.BoseBoxFock.slice_coeff_pointwise_bound
import Submission.Work.BoseBoxFock.slotExact_ae_bounded_of_bounded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ae_sliceCoeff_le`

The a.e.-in-`y` form of the slice coefficient bound: for almost every complement configuration
`y`, the monomial coefficient `c_α(y) = ∫_u conj(M_α u)·slice_y(u)` of the slice of a box state
satisfies the `L²` Cauchy–Schwarz bound

    |c_α(y)|² ≤ ‖M_α‖²_{L²(abox)} · ∫_{abox} ‖slice_y‖² .

The ingredients are all in the neighbouring modules:

* `slice_coeff_pointwise_bound` — the *restricted* (`∫_{abox}`) version of the bound, obtained
  from the pairing identity `XSpow_modeProd_pairing` and the `L²` Cauchy–Schwarz
  `norm_integral_mul_sq_le`; here it is used at `j = 0`, where `XSpow ℓ univ 0 = id`;
* `slotExact_ae_bounded_of_bounded` — the sector `Θ = slotExact e S Φ` of an `L^∞` state is
  a.e. strongly measurable and a.e. bounded;
* `ae_ae_slice_regular` — a.e. sections of an a.e. strongly measurable, a.e. bounded function
  are a.e. strongly measurable and a.e. bounded, which turns the previous point into the two
  hypotheses of the pointwise bound for the slice `sliceF e S Φ y`.

The one structural point not supplied by the existing modules is that the slice **vanishes
outside the box**: if some slot `i ∈ S` of the configuration `x` lies outside `boxL ℓ`, then
every mode `e l` vanishes there, so every kernel factor `PV e (x i) (z i)` of every
`slotProj e T Φ x` (`T ⊇ S`) vanishes and hence `slotExact e S Φ x = 0`.  This upgrades the
*restricted* integral of `slice_coeff_pointwise_bound` to the *unrestricted* integral appearing
in the statement.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 1. The slice vanishes outside the box -/

/-- A kernel factor vanishes when its *first* argument kills all the modes. -/
lemma aeSliceCoeff_PV_eq_zero_of_left_factors {m : ℕ} {e : Fin m → Ω → ℂ} {a z : Ω}
    (h : ∀ l, e l a = 0) : PV e a z = 0 := by
  rw [PV]
  exact Finset.sum_eq_zero (fun l _ => by rw [h l, zero_mul])

/-- **The slot projection vanishes at a configuration with a slot outside the box.**
If `i ∈ T` and `x i` lies outside `boxL ℓ`, then every mode vanishes at `x i`, so the kernel
factor `PV e (x i) (z i)` is identically zero in `z` and the whole integrand of `slotProj` is
zero. -/
lemma aeSliceCoeff_slotProj_eq_zero_of_slot_notMem {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) (Ψ : (Fin n → Ω) → ℂ) {x : Fin n → Ω} {i : Fin n}
    (hi : i ∈ T) (hx : x i ∉ Work.BoseK15.corpusBox.boxL ℓ) : slotProj e T Ψ x = 0 := by
  have he0 : ∀ l, e l (x i) = 0 := by
    intro l
    by_contra hne
    exact hx (hsupp l (Function.mem_support.mpr hne))
  rw [slotProj]
  have hzero : (fun z : ↥T → Ω => (∏ j : ↥T, PV e (x j.1) (z j)) *
      Ψ (fun j => if h : j ∈ T then z ⟨j, h⟩ else x j)) = fun _ => (0 : ℂ) := by
    funext z
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : ↥T))
      (aeSliceCoeff_PV_eq_zero_of_left_factors (e := e) (a := x i) (z := z ⟨i, hi⟩) he0),
      zero_mul]
  rw [hzero]
  simp

/-- **The sector projection vanishes at a configuration with an `S`-slot outside the box.**
`slotExact e S Ψ` is the alternating sum of the `slotProj e T Ψ` over `T ⊇ S`, and each of them
vanishes by `aeSliceCoeff_slotProj_eq_zero_of_slot_notMem`. -/
lemma aeSliceCoeff_slotExact_eq_zero_of_slot_notMem {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Ψ : (Fin n → Ω) → ℂ) {x : Fin n → Ω} {i : Fin n}
    (hi : i ∈ S) (hx : x i ∉ Work.BoseK15.corpusBox.boxL ℓ) : slotExact e S Ψ x = 0 := by
  simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_zero fun T hT => ?_
  have hST : S ⊆ T := (Finset.mem_filter.mp hT).2
  rw [aeSliceCoeff_slotProj_eq_zero_of_slot_notMem hsupp T Ψ (hST hi) hx, smul_zero]

/-- **The slice is supported in the box.**  `sliceF e S Ψ y u` is the sector projection of `Ψ`
at the configuration obtained by placing the `S`-slots of a configuration at `u` (re-indexed by
`S.equivFin`) and the rest at `y`; as soon as some coordinate of `u` lies outside `boxL ℓ`, the
corresponding `S`-slot of that configuration does too, so the sector projection vanishes. -/
lemma aeSliceCoeff_sliceF_eq_zero_of_notMem_abox {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Ψ : (Fin n → Ω) → ℂ)
    {y : {i // i ∉ S} → Ω} {u : Fin S.card → Ω}
    (hu : u ∉ Submission.BoseGases.abox S.card ℓ) : sliceF e S Ψ y u = 0 := by
  rw [Submission.BoseGases.mem_abox_iff] at hu
  push Not at hu
  obtain ⟨j, hj⟩ := hu
  have hj' : u j ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    rw [corpusBox_boxL_eq_acube hℓ]; exact hj
  set i₀ : Fin n := (S.equivFin.symm j : Fin n) with hi₀
  have hS : i₀ ∈ S := (S.equivFin.symm j).2
  have hx : (pairCoord S (fun i => u (S.equivFin i)) y) i₀
      ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    rw [pairCoord_mem S _ y i₀ hS]
    rw [show S.equivFin ⟨i₀, hS⟩ = j from S.equivFin.apply_symm_apply j]
    exact hj'
  exact aeSliceCoeff_slotExact_eq_zero_of_slot_notMem hsupp S Ψ hS hx

/-! ## 2. The a.e. coefficient bound for an `L^∞` state -/

/-- **The slice coefficient bound, for an `L^∞` state.**  The pointwise bound
`slice_coeff_pointwise_bound` at `j = 0` gives the inequality with both integrals restricted to
`abox`, and `aeSliceCoeff_sliceF_eq_zero_of_notMem_abox` upgrades the left-hand integral to the
unrestricted one (the integrand `conj M_α · slice_y` vanishes off the box). -/
lemma ae_sliceCoeff_le_of_memLp {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : Measure Ω), e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) {Ψ : (Fin n → Ω) → ℂ} (hΨ : MemLp Ψ ⊤)
    (α : Fin m →₀ ℕ) (hk : 0 < S.card - α 0) :
    ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)),
      ‖∫ u : Fin S.card → Ω, (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * sliceF e S Ψ y u‖ ^ 2
        ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
          * (∫ u in Submission.BoseGases.abox S.card ℓ, ‖sliceF e S Ψ y u‖ ^ 2) := by
  classical
  -- a.e. strong measurability and a.e. boundedness of the sector, and hence of its slices
  obtain ⟨hΘaesm, C, hΘbdd⟩ := slotExact_ae_bounded_of_bounded hbdd hsupp S hΨ
  have hslice := ae_ae_slice_regular (S := S) hΘaesm hΘbdd
  filter_upwards [hslice] with y hy
  obtain ⟨hyA, hyB⟩ := hy
  have hgA : AEStronglyMeasurable (sliceF e S Ψ y) (volume : Measure (Fin S.card → Ω)) := hyA
  have hgB : ∀ᵐ u ∂(volume : Measure (Fin S.card → Ω)), ‖sliceF e S Ψ y u‖ ≤ C := hyB
  -- the pointwise bound at `j = 0`
  have hpt := slice_coeff_pointwise_bound hℓ he hbdd hsupp hc α 0 hgA hgB hk
  rw [show XSpow ℓ (Finset.univ : Finset (Fin S.card)) 0 (sliceF e S Ψ y) = sliceF e S Ψ y
      from rfl] at hpt
  simp only [Nat.mul_zero, pow_zero, div_one] at hpt
  -- upgrade the left-hand restricted integral to the unrestricted one
  have hsuppF : ∀ u : Fin S.card → Ω, u ∉ Submission.BoseGases.abox S.card ℓ →
      (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u) * sliceF e S Ψ y u = 0 := by
    intro u hu
    rw [aeSliceCoeff_sliceF_eq_zero_of_notMem_abox hℓ hsupp S Ψ hu, mul_zero]
  rw [(MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox S.card ℓ)
      (f := fun u : Fin S.card → Ω =>
        (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u) * sliceF e S Ψ y u) hsuppF).symm]
  exact hpt

/-! ## 3. The requested statement -/

theorem ae_sliceCoeff_le {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (α : Fin m →₀ ℕ) (hk : 0 < S.card - α 0) :
    ∀ᵐ y ∂(MeasureTheory.volume :
        MeasureTheory.Measure ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3))),
      ‖∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * Work.BoseBoxFock.sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2
        ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
          * (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseBoxFock.sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2) := by
  -- the complexified state is continuous with compact support, hence `L^∞`
  have hΦc' : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact n hℓ)
      (isClosed_tsupport Φ) hΦc
  have hΦ'c : HasCompactSupport (fun x : Fin n → Ω => ((Φ x : ℝ) : ℂ)) :=
    HasCompactSupport.comp_left hΦc' Complex.ofReal_zero
  have hmem : MemLp (fun x : Fin n → Ω => ((Φ x : ℝ) : ℂ)) ⊤ :=
    (Complex.continuous_ofReal.comp hΦ).memLp_of_hasCompactSupport hΦ'c
  exact ae_sliceCoeff_le_of_memLp hℓ he hbdd hsupp hc S hmem α hk

end Work.BoseBoxFock
