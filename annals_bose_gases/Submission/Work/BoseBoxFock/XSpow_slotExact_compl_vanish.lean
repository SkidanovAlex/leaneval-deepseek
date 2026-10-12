import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxOrthDefs
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.sliceFCRealise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.XSpow_slotExact_compl_vanish` — the complement support of a sector

The `S`-**sector** of a box state, `slotExact e S Φ`, is the component of `Φ` whose slots in `S`
are projected onto `V = span{e l}` and whose slots *outside* `S` are projected onto `Vᗮ` (written
by inclusion–exclusion over the supersets of `S`, `FibreProjDefs.slotExact`).

The mathematical content of this file is the elementary but essential *support* statement: the
complement slots of the sector are pinned to the box.  Precisely, if a coordinate `k ∉ S` of the
configuration `x` lies outside the cube `acube ℓ` — the cube supporting the modes (`hsupp`) and
the state (`hΦc`) — then the whole sector vanishes at `x`, and so does every iterate
`XSpow ℓ S j` of the excited-count operator `XS ℓ S = Σ_{i ∈ S} (1 − aPC_i)` on it.

The reason is that at such a configuration *every* term of the two expansions is killed:

* in `slotProj e T Φ x`, the slot `k` is either *projected*, in which case the factor
  `PV e (x k) ·` of the product kernel vanishes because the modes vanish off `boxL ℓ`
  (`PV_apply_eq_zero_of_notMem_boxL`, using `boxL ℓ = acube ℓ` for `ℓ > 0`), or *kept*, in which
  case the argument of `Φ` has `k`-th coordinate `x k` and `Φ` vanishes off `abox n ℓ`
  (`eq_zero_of_notMem_abox`);
* applying `XS ℓ S` keeps this property: the term `Ψ x` vanishes directly, and the slot mean
  `aPC ℓ i Ψ x` — an integral over `y ∈ acube ℓ` of `Ψ (x[i ↦ y])` with `i ∈ S` — integrates a
  function that is *identically* zero, because updating the slot `i ∈ S` does not move the
  `k ∉ S`-th coordinate.

No integrability, regularity or integrability hypothesis is needed beyond the two support
conditions; in particular `aPC` is applied only to functions vanishing identically.

This is the support half of the sector bookkeeping of the BF3c selection
(`FINDING_BF3c_selection_s8.md`); it lets the sector's square integral be taken over the box
`abox n ℓ` alone.
-/

noncomputable section

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The box is the cube** (for `ℓ > 0`): `boxL ℓ = ℓ • unitCell = {x | ∀ i, |x i| ≤ ℓ/2}`
agrees with the centred cube `acube ℓ`. -/
lemma boxL_eq_acube_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ := by
  ext x
  rw [Work.BoseBoxFock.mem_corpusBox_boxL hℓ, Submission.BoseGases.mem_acube_iff]
  constructor
  · intro h i
    have hi : |x i| ≤ ℓ / 2 := h i
    rw [Set.mem_Icc]
    exact ⟨by linarith [(abs_le.mp hi).1], (abs_le.mp hi).2⟩
  · intro h i
    have hi := h i
    rw [Set.mem_Icc] at hi
    rw [abs_le]
    exact ⟨by linarith [hi.1], hi.2⟩

/-- **The projection kernel vanishes off the box**: if the modes are supported in `boxL ℓ` then
`PV e x y = 0` for `x ∉ boxL ℓ`, for *every* `y` (the `x`-slot is the projected one). -/
lemma PV_apply_eq_zero_of_notMem_boxL {ℓ : ℝ} {m : ℕ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {x y : E3} (hx : x ∉ Work.BoseK15.corpusBox.boxL ℓ) : PV e x y = 0 := by
  unfold PV
  refine Finset.sum_eq_zero fun l _ => ?_
  have he : e l x = 0 := Function.notMem_support.mp (fun hmem => hx (hsupp l hmem))
  rw [he, zero_mul]

/-- **A state supported in the box vanishes off it**: `Φ z = 0` as soon as `z ∉ abox n ℓ`, the
hypothesis being `tsupport Φ ⊆ abox n ℓ`. -/
lemma eq_zero_of_notMem_abox {ℓ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℂ}
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) {z : Submission.BoseGases.X n}
    (hz : z ∉ Submission.BoseGases.abox n ℓ) : Φ z = 0 :=
  Function.notMem_support.mp fun hmem => hz (hΦc (subset_closure hmem))

/-- **The sector vanishes at every configuration with a complement slot outside the cube.**
This is the inclusion–exclusion sum over `T ⊇ S`, each of whose terms is zero: the slot `k ∉ S`
is either projected (kernel factor zero, `PV_apply_eq_zero_of_notMem_boxL`) or kept (state
argument off the box, `eq_zero_of_notMem_abox`). -/
lemma slotExact_apply_eq_zero_of_compl {ℓ : ℝ} (hℓ : 0 < ℓ) {n m : ℕ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Φ : Submission.BoseGases.X n → ℂ}
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (S : Finset (Fin n)) {x : Submission.BoseGases.X n}
    (hx : ∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) :
    slotExact e S Φ x = 0 := by
  obtain ⟨k, hkS, hkx⟩ := hx
  have hkx' : x k ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    rw [boxL_eq_acube_of_pos hℓ]; exact hkx
  unfold slotExact
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun T _ => ?_
  have hzero : slotProj e T Φ x = 0 := by
    unfold slotProj
    rw [show (fun z : {i : Fin n // i ∈ T} → E3 =>
        (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) *
          Φ (fun i => if h : i ∈ T then z ⟨i, h⟩ else x i)) = fun _ => (0 : ℂ) from
      funext fun z => ?_, MeasureTheory.integral_zero]
    by_cases hkT : k ∈ T
    · -- the slot `k` is projected: the kernel factor vanishes
      have hfac : PV e (x k) (z ⟨k, hkT⟩) = 0 := PV_apply_eq_zero_of_notMem_boxL hsupp hkx'
      have hprod : (∏ i : {i : Fin n // i ∈ T}, PV e (x i.1) (z i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ ⟨k, hkT⟩) hfac
      rw [hprod, zero_mul]
    · -- the slot `k` is kept: the state argument is off the box
      have harg : (fun i : Fin n => if h : i ∈ T then z ⟨i, h⟩ else x i) k = x k := by
        simp [hkT]
      have hΦz : Φ (fun i : Fin n => if h : i ∈ T then z ⟨i, h⟩ else x i) = 0 :=
        eq_zero_of_notMem_abox
          (z := fun i : Fin n => if h : i ∈ T then z ⟨i, h⟩ else x i) hΦc
          (fun hmem => hkx (harg ▸ hmem k))
      rw [hΦz, mul_zero]
  simp only [Pi.smul_apply, hzero, smul_zero]

/-- **`XS` preserves the complement-vanishing property**: for `x` with `k ∉ S`, `x k ∉ acube ℓ`,
both terms of every summand vanish — `Ψ x` by hypothesis, and the slot mean `aPC ℓ i Ψ x`
(`i ∈ S`) because the integrated function `y ↦ Ψ (x[i ↦ y])` is *identically* zero (updating the
slot `i ∈ S` does not move the `k ∉ S`-th coordinate). -/
lemma XS_apply_eq_zero_of_vanish {ℓ : ℝ} {n : ℕ} (S : Finset (Fin n))
    {Ψ : Submission.BoseGases.X n → ℂ}
    (hΨ : ∀ x : Submission.BoseGases.X n,
      (∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) → Ψ x = 0)
    {x : Submission.BoseGases.X n}
    (hx : ∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) :
    XS ℓ S Ψ x = 0 := by
  obtain ⟨k, hkS, hkx⟩ := hx
  have hx0 : Ψ x = 0 := hΨ x ⟨k, hkS, hkx⟩
  unfold XS
  refine Finset.sum_eq_zero fun i hi => ?_
  have hki : k ≠ i := fun h => hkS (h ▸ hi)
  have haPC : aPC ℓ i Ψ x = 0 := by
    unfold aPC
    rw [show (fun y : E3 => Ψ (Function.update x i y)) = fun _ => (0 : ℂ) from
      funext fun y => hΨ _ ⟨k, hkS, by rw [Function.update_of_ne hki]; exact hkx⟩,
      MeasureTheory.integral_zero, mul_zero]
  rw [hx0, haPC, sub_zero]

/-- **Every iterate `XSpow ℓ S j` preserves the complement-vanishing property** (induction on `j`,
the step being `XS_apply_eq_zero_of_vanish`). -/
lemma XSpow_apply_eq_zero_of_vanish {ℓ : ℝ} {n : ℕ} (S : Finset (Fin n))
    {Ψ : Submission.BoseGases.X n → ℂ}
    (hΨ : ∀ x : Submission.BoseGases.X n,
      (∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) → Ψ x = 0) :
    ∀ (j : ℕ) (x : Submission.BoseGases.X n),
      (∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) → XSpow ℓ S j Ψ x = 0
  | 0, x, hx => hΨ x hx
  | j + 1, x, hx => by
      show XS ℓ S (XSpow ℓ S j Ψ) x = 0
      exact XS_apply_eq_zero_of_vanish S (XSpow_apply_eq_zero_of_vanish S hΨ j) hx

/-- **The sector `slotExact e S Φ` of a box state, and all its `XSpow`-iterates, vanish at every
configuration with a slot `k ∉ S` outside the cube `acube ℓ`.** -/
theorem XSpow_slotExact_compl_vanish {n m : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (S : Finset (Fin n)) (j : ℕ) :
    ∀ x : Fin n → EuclideanSpace ℝ (Fin 3),
      (∃ k : Fin n, k ∉ S ∧ x k ∉ Submission.BoseGases.acube ℓ) →
      Work.BoseBoxFock.XSpow ℓ S j
        (Work.BoseBoxFock.slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x = 0 := by
  have hcast : Function.support (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ))
      = Function.support Φ := by
    ext x
    simp [Function.mem_support]
  have hΦc' : tsupport (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ))
      ⊆ Submission.BoseGases.abox n ℓ := by
    intro z hz
    exact hΦc (by simpa only [tsupport, hcast] using hz)
  intro x hx
  refine XSpow_apply_eq_zero_of_vanish S ?_ j x hx
  intro z hz
  exact slotExact_apply_eq_zero_of_compl hℓ hsupp hΦc' S hz

end Work.BoseBoxFock
