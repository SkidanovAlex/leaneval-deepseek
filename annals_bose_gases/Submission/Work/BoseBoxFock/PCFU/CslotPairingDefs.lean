import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PCFU.chCslot_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.CslotPairingDefs`

The one structural definition that the `(C)`-slot reduction needs: the configuration
`chCcfg i j w w' x'` obtained from a configuration `x'` of the *remaining* coordinates by
writing `w` into the slot `i` and `w'` into the slot `j`.

For `i ≠ j` the map
`(w, w', x') ↦ chCcfg i j w w' x'`
is a measurable bijection between `E3 × E3 × ({k // k ≠ i ∧ k ≠ j} → E3)` and `X n`, and it
preserves Lebesgue measure; the two peel identities `integral_chCcfg`/`lintegral_chCcfg` record
the resulting integration formulas in the *iterated* form in which the `(C)`-slot estimate
consumes them:

    ∫_x F x = ∫_{x'} ∫_w ∫_{w'} F (chCcfg i j w w' x')

This is the order that makes the `w'`-slot (the one that only occurs in the state `Θ`) innermost,
so that its integral collapses against the state, while the two slots `w, w'` remain available
for the alias-kernel pairing bound `PCFU.ChKerPair`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The `(i,j)`-slot configuration.**  `chCcfg i j w w' x'` writes `w` into slot `i`, `w'` into
slot `j`, and takes the remaining slots from `x'`. -/
def chCcfg {n : ℕ} (i j : Fin n) (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) : Submission.BoseGases.X n :=
  fun k => if h : k = i then w else if h' : k = j then w' else x' ⟨k, h, h'⟩

@[simp] lemma chCcfg_i {n : ℕ} (i j : Fin n) (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) : chCcfg i j w w' x' i = w := by
  simp [chCcfg]

@[simp] lemma chCcfg_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) : chCcfg i j w w' x' j = w' := by
  simp only [chCcfg]
  rw [dif_neg (Ne.symm hij), dif_pos trivial]

lemma chCcfg_other {n : ℕ} {i j : Fin n} (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    chCcfg i j w w' x' k = x' ⟨k, hki, hkj⟩ := by
  simp only [chCcfg]
  rw [dif_neg hki, dif_neg hkj]

@[simp] lemma chCcfg_mem_abox_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w w' : E3) (ℓ : ℝ)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    chCcfg i j w w' x' ∈ Submission.BoseGases.abox n ℓ ↔
      w ∈ Submission.BoseGases.acube ℓ ∧ w' ∈ Submission.BoseGases.acube ℓ ∧
        (∀ k, x' k ∈ Submission.BoseGases.acube ℓ) := by
  constructor
  · intro h
    refine ⟨by simpa using h i, ?_, fun k => ?_⟩
    · simpa [chCcfg_j hij] using h j
    · simpa [chCcfg, k.2.1, k.2.2] using h k.1
  · rintro ⟨hw, hw', hx'⟩ k
    simp only [chCcfg]
    split_ifs with h1 h2
    · exact hw
    · exact hw'
    · exact hx' ⟨k, h1, h2⟩

end Work.BoseBoxFock.PCFU
