import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.sliceFCRealise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.XSpow_sliceF_pointwise` — the sector operator commutes with slicing

The sector excited-count operator `XS ℓ S = ∑_{i ∈ S} (1 − aPC ℓ i)` acts **slotwise** on the
slots in `S`, and the slot mean `aPC ℓ i` of slot `i` involves only the *other* slots of the
configuration (`aPC ℓ i Ψ x = ℓ⁻³ ∫_{acube ℓ} Ψ (x[i ↦ z]) dz` is unchanged when `x i` is
changed).  Consequently the operator commutes with the operation "freeze the complementary
slots at `y`", i.e. with

`sliceF e S F y u = slotExact e S F (pairCoord S (fun i => u (S.equivFin i)) y)`,

and so does every iterate `XSpow`: this is the pointwise identity

`XSpow ℓ univ j (sliceF e S F y) u = XSpow ℓ S j (slotExact e S F) (pairCoord S u y)`.

This is the *pointwise* companion of the (false as stated, see
`FINDING_slice_Xpow_fubini.md`) Fubini identity `slice_Xpow_fubini`.  Nothing analytic is needed
here: both sides are `j`-fold compositions of the same slotwise operator, so the identity is a
purely combinatorial statement about `pairCoord`/`Function.update`.  In particular no
integrability of the modes `e` and no regularity of `F` is required (the two Bochner integrals
appearing inside `aPC` have *identical* integrands, so `integral_undef` cannot separate them).
-/

noncomputable section

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Two elementary lemmas about `pairCoord` and `Function.update` -/

/-- **Updating a relation coordinate of a pair configuration.**  For `j : ↥S` (a slot of `S`)
the configuration `pairCoord S u y` with its `j`-th coordinate overwritten by `z` is again a pair
configuration, with the `S`-part of `u` updated at `j`.  (The complementary coordinates are
untouched because `j ∈ S`.) -/
lemma update_pairCoord {n : ℕ} (S : Finset (Fin n)) (u : ↥S → Ω) (y : {i // i ∉ S} → Ω)
    (j : ↥S) (z : Ω) :
    Function.update (pairCoord S u y) (j : Fin n) z = pairCoord S (Function.update u j z) y := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i ∈ S
  · rw [pairCoord_mem S u y i hi, pairCoord_mem S (Function.update u j z) y i hi,
      Function.update_apply]
    by_cases h : (⟨i, hi⟩ : ↥S) = j
    · subst h; simp
    · have h' : ¬ (i = (j : Fin n)) := fun hh => h (Subtype.ext hh)
      simp [h, h']
  · rw [pairCoord_notMem S u y i hi, pairCoord_notMem S (Function.update u j z) y i hi]
    rw [if_neg]
    intro h'
    exact hi (by rw [h']; exact j.2)

/-- **Updating a coordinate through `S.equivFin`.**  The function `i ↦ u (S.equivFin i)` on `↥S`,
with its `j`-th entry overwritten by `z`, is the reindexing of `Function.update u (S.equivFin j) z`
along the bijection `S.equivFin`. -/
lemma update_comp_equivFin {n : ℕ} (S : Finset (Fin n)) (u : Fin S.card → Ω) (j : ↥S)
    (z : Ω) :
    Function.update (fun i => u (S.equivFin i)) j z
      = fun i => Function.update u (S.equivFin j) z (S.equivFin i) := by
  funext i
  rw [Function.update_apply, Function.update_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : S.equivFin i ≠ S.equivFin j := fun hh => h (S.equivFin.injective hh)
    simp [h, h']

/-! ## 2. The slice of an arbitrary state, indexed by `Fin S.card` -/

/-- The slice of an arbitrary box state `Ψ` at the complement configuration `y`, transported to
the standard index type `Fin S.card` along `S.equivFin`.  For `Ψ = slotExact e S F` this is
`sliceF e S F y`. -/
def sectorSliceF {n : ℕ} (S : Finset (Fin n)) (Ψ : (Fin n → Ω) → ℂ)
    (y : {i // i ∉ S} → Ω) : (Fin S.card → Ω) → ℂ :=
  fun u => Ψ (pairCoord S (fun i => u (S.equivFin i)) y)

/-! ## 3. The slot mean is oblivious to the sliced coordinates -/

/-- **Fibre independence of the slot mean.**  At the pair configuration `pairCoord S u y`, the slot
mean of the slot `j ∈ S` depends only on the coordinates of the *other* `S`-slots and on `y`;
it is therefore the slot mean of slot `S.equivFin j` of the slice `sectorSliceF S Ψ y`, evaluated
at `u`. -/
lemma aPC_pairCoord {n : ℕ} (S : Finset (Fin n)) (ℓ : ℝ) (Ψ : (Fin n → Ω) → ℂ)
    (y : {i // i ∉ S} → Ω) (u : Fin S.card → Ω) (j : ↥S) :
    aPC ℓ (j : Fin n) Ψ (pairCoord S (fun i => u (S.equivFin i)) y)
      = aPC ℓ (S.equivFin j) (sectorSliceF S Ψ y) u := by
  unfold aPC sectorSliceF
  congr 1
  congr 1
  funext z
  rw [update_pairCoord S (fun i => u (S.equivFin i)) y j z, update_comp_equivFin S u j z]

/-! ## 4. The operator `XS` and its iterates commute with slicing -/

/-- **`XS` commutes with slicing.**  Slicing the sector excited count of `Ψ` at `y` is the sector
excited count (on the whole slot set `univ`) of the slice. -/
lemma XS_sectorSliceF {n : ℕ} (S : Finset (Fin n)) (ℓ : ℝ) (Ψ : (Fin n → Ω) → ℂ)
    (y : {i // i ∉ S} → Ω) (u : Fin S.card → Ω) :
    XS ℓ S Ψ (pairCoord S (fun i => u (S.equivFin i)) y)
      = XS ℓ (Finset.univ : Finset (Fin S.card)) (sectorSliceF S Ψ y) u := by
  unfold XS
  have hcoe : (∑ i ∈ S, (Ψ (pairCoord S (fun i => u (S.equivFin i)) y)
        - aPC ℓ i Ψ (pairCoord S (fun i => u (S.equivFin i)) y)))
      = ∑ i : ↥S, (sectorSliceF S Ψ y u
        - aPC ℓ (S.equivFin i) (sectorSliceF S Ψ y) u) := by
    rw [← Finset.sum_coe_sort S (f := fun i => (Ψ (pairCoord S (fun i => u (S.equivFin i)) y)
        - aPC ℓ i Ψ (pairCoord S (fun i => u (S.equivFin i)) y)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [sectorSliceF]
    rw [aPC_pairCoord]
  rw [hcoe]
  exact Equiv.sum_comp S.equivFin (fun k : Fin S.card => sectorSliceF S Ψ y u
    - aPC ℓ k (sectorSliceF S Ψ y) u)

/-- **Every iterate of `XS` commutes with slicing** (the pointwise form used by the target): the
`j`-th iterate of the sector count on the full space, applied to the slice of `Ψ`, is the slice of
the `j`-th iterate of the sector count on the sector slots. -/
lemma XSpow_sectorSliceF {n : ℕ} (S : Finset (Fin n)) (ℓ : ℝ) (j : ℕ) (Ψ : (Fin n → Ω) → ℂ)
    (y : {i // i ∉ S} → Ω) (u : Fin S.card → Ω) :
    XSpow ℓ (Finset.univ : Finset (Fin S.card)) j (sectorSliceF S Ψ y) u
      = (XSpow ℓ S j Ψ) (pairCoord S (fun i => u (S.equivFin i)) y) := by
  induction j generalizing u with
  | zero => rfl
  | succ k ih =>
    show XS ℓ (Finset.univ : Finset (Fin S.card))
          (XSpow ℓ (Finset.univ : Finset (Fin S.card)) k (sectorSliceF S Ψ y)) u
        = XS ℓ S (XSpow ℓ S k Ψ) (pairCoord S (fun i => u (S.equivFin i)) y)
    rw [XS_sectorSliceF S ℓ (XSpow ℓ S k Ψ) y u]
    have hfun : (XSpow ℓ (Finset.univ : Finset (Fin S.card)) k (sectorSliceF S Ψ y)
          : (Fin S.card → Ω) → ℂ) = sectorSliceF S (XSpow ℓ S k Ψ) y := by
      funext v
      rw [ih v]
      rfl
    rw [hfun]

/-! ## 5. The target -/

theorem XSpow_sliceF_pointwise {n m : ℕ} (ℓ : ℝ) {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (S : Finset (Fin n)) (F : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (j : ℕ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) (u : Fin S.card → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
        (Work.BoseBoxFock.sliceF e S F y) u
      = Work.BoseBoxFock.XSpow ℓ S j (Work.BoseBoxFock.slotExact e S F)
          (Work.BoseBoxFock.pairCoord S (fun i => u (S.equivFin i)) y) := by
  have h1 : (Work.BoseBoxFock.sliceF e S F y : (Fin S.card → EuclideanSpace ℝ (Fin 3)) → ℂ)
      = sectorSliceF S (slotExact e S F) y := rfl
  rw [h1]
  exact XSpow_sectorSliceF S ℓ j (slotExact e S F) y u

end Work.BoseBoxFock
