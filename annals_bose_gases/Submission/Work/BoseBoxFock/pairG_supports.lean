import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG_supports` — the box support of the pair-row fibres

The five triple integrals of `potPairRows_kernelExpanded` are rewritten (step (S2), see
`FINDING_PotPairRows_exists.md`) as `∫_w ∫_y K w y · 𝒢 w y` with `𝒢` one of the *fibre* functions
`pairG13`, `pairG23`, `pairG21` of `pairRowGDefs`.  The `(S2)` substitutions `pairRowS2`'s block
lemmas (`block13_Ksub`, `blockTwo3_Ksub`, `blockII1_Ksub`) consume the fibre `L²` bounds over the
box squared `boxL ℓ × boxL ℓ` — i.e. they need

    support (uncurry 𝒢) ⊆ boxL ℓ ×ˢ boxL ℓ ,

which is exactly the hypothesis `hCsupp` of `pairG13_L2` / `pairG23_L2` / `pairG21_L2` in
`Submission/Work/BoseBoxFock/pairRowS2Inst.lean`.

The present file supplies that hypothesis from the *state* hypothesis
`support Θ ⊆ Work.MB.boxPow n ℓ`: each of the three fibres evaluates `Θ` at a configuration in
which one of the two kernel variables is frozen into a definite slot (`insertCoord` /
`insertCoord2` / `Function.update`), so that variable must lie in the one-particle box; outside it
the corresponding factor vanishes and the whole integral with it.

This is a purely pointwise (measure-free) argument: every fibre is an integral whose integrand
vanishes identically, so the integral is `0` and the point is not in the support.  No integrability,
measurability or finiteness of measure is used — only that `0` is absorbent.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The basic facts about the frozen slots -/

/-- A state supported in the `n`-particle box `boxPow n ℓ = (boxL ℓ)^n` vanishes at every
configuration having a coordinate outside the one-particle box. -/
theorem theta_eq_zero_of_coord_notMem {n : ℕ} {ℓ : ℝ} {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {z : Work.BoseDict.Xn n} {j : Fin n}
    (h : z j ∉ Work.BoseK15.corpusBox.boxL ℓ) : Θ z = 0 := by
  by_contra hz
  exact h ((Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr hz))) j)

/-- `insertCoord` really inserts at the named coordinate. -/
private lemma insertCoord_apply_index {n : ℕ} (j : Fin n) (w : E3)
    (x' : {k : Fin n // k ≠ j} → E3) : insertCoord j w x' j = w := by
  rw [insertCoord_eq]; simp

/-- `insertCoord2` inserts `w₀` at the first coordinate. -/
private lemma insertCoord2_apply_fst {n : ℕ} (p : Fin n × Fin n) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) : insertCoord2 p w₀ w₁ x' p.1 = w₀ := by
  rw [insertCoord2_eq]; simp

/-- `insertCoord2` inserts `w₁` at the second coordinate (here `p.1 ≠ p.2` is used). -/
private lemma insertCoord2_apply_snd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) : insertCoord2 p w₀ w₁ x' p.2 = w₁ := by
  rw [insertCoord2_eq]; simp [Ne.symm hp]

/-- The two-fold update keeps the value inserted first (here `p.1 ≠ p.2` is used). -/
private lemma update_update_apply_fst {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {z : Fin n → E3} {y u : E3} : Function.update (Function.update z p.1 y) p.2 u p.1 = y := by
  rw [Function.update_apply, if_neg hp, Function.update_self]

/-- The two-fold update keeps the value inserted second. -/
private lemma update_update_apply_snd {n : ℕ} {p : Fin n × Fin n} {z : Fin n → E3} {y u : E3} :
    Function.update (Function.update z p.1 y) p.2 u p.2 = u := by
  rw [Function.update_apply, if_pos rfl]

/-! ## 2. The fibres vanish when a kernel variable leaves the box -/

/-- `pairG13` vanishes outside the box in its **first** kernel variable: the frozen configuration
`insertCoord p.2 w x'` has the coordinate `p.2` equal to `w`, so `Θ` vanishes on it whenever
`w ∉ boxL ℓ`, and hence so does the whole `u`-integral for every fibre `x'`. -/
theorem pairG13_eq_zero_of_fst_notMem {n : ℕ} (p : Fin n × Fin n) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {w y : E3}
    (hw : w ∉ Work.BoseK15.corpusBox.boxL ℓ) : pairG13 p Θ A B w y = 0 := by
  rw [pairG13]
  have h1 : ∀ x' : {k : Fin n // k ≠ p.2} → E3,
      (∫ u : E3, star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1)
        * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)) = 0 := by
    intro x'
    have hz : Θ (insertCoord p.2 w x') = 0 :=
      theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by rw [insertCoord_apply_index]; exact hw)
    simp only [hz, star_zero, zero_mul, integral_zero]
  simp only [h1, integral_zero]

/-- `pairG13` vanishes outside the box in its **second** kernel variable: the updated
configuration `update (update (insertCoord p.2 w x') p.1 y) p.2 u` has the coordinate `p.1` equal
to `y`, so `Θ` vanishes on it whenever `y ∉ boxL ℓ`. -/
theorem pairG13_eq_zero_of_snd_notMem {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {w y : E3}
    (hy : y ∉ Work.BoseK15.corpusBox.boxL ℓ) : pairG13 p Θ A B w y = 0 := by
  rw [pairG13]
  have h1 : ∀ x' : {k : Fin n // k ≠ p.2} → E3,
      (∫ u : E3, star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1)
        * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)) = 0 := by
    intro x'
    have hfun : (fun u : E3 => star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1)
        * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u))
        = fun _ : E3 => (0 : ℂ) := by
      funext u
      have hz : Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.1)
          (by rw [update_update_apply_fst hp]; exact hy)
      simp only [hz, mul_zero]
    rw [hfun, integral_zero]
  simp only [h1, integral_zero]

/-- `pairG23` vanishes outside the box in its **first** kernel variable (`insertCoord2` freezes it
into the slot `p.1`). -/
theorem pairG23_eq_zero_of_fst_notMem {n : ℕ} (p : Fin n × Fin n) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {w₀ w₁ : E3}
    (hw : w₀ ∉ Work.BoseK15.corpusBox.boxL ℓ) : pairG23 p Θ A B w₀ w₁ = 0 := by
  rw [pairG23]
  have h2 : ∀ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3,
      (∫ y : E3, ∫ u : E3, star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
        * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u)) = 0 := by
    intro x'
    have hz : Θ (insertCoord2 p w₀ w₁ x') = 0 :=
      theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by rw [insertCoord2_apply_fst]; exact hw)
    simp only [hz, star_zero, zero_mul, integral_zero]
  simp only [h2, integral_zero]

/-- `pairG23` vanishes outside the box in its **second** kernel variable (`insertCoord2` freezes it
into the slot `p.2`). -/
theorem pairG23_eq_zero_of_snd_notMem {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {w₀ w₁ : E3}
    (hw : w₁ ∉ Work.BoseK15.corpusBox.boxL ℓ) : pairG23 p Θ A B w₀ w₁ = 0 := by
  rw [pairG23]
  have h2 : ∀ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3,
      (∫ y : E3, ∫ u : E3, star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
        * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u)) = 0 := by
    intro x'
    have hz : Θ (insertCoord2 p w₀ w₁ x') = 0 :=
      theta_eq_zero_of_coord_notMem hΘs (j := p.2)
        (by rw [insertCoord2_apply_snd p hp]; exact hw)
    simp only [hz, star_zero, zero_mul, integral_zero]
  simp only [h2, integral_zero]

/-- `pairG21` vanishes outside the box in its **first** kernel variable (which `pairG21` inserts at
the slot `p.2`). -/
theorem pairG21_eq_zero_of_fst_notMem {n : ℕ} (p : Fin n × Fin n) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {u y : E3}
    (hu : u ∉ Work.BoseK15.corpusBox.boxL ℓ) : pairG21 p Θ A u y = 0 := by
  rw [pairG21]
  have hfun : (fun x : Work.BoseDict.Xn n => star (Θ x) * A (x p.1) * A (x p.2)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)) = fun _ => (0 : ℂ) := by
    funext x
    have hz : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 :=
      theta_eq_zero_of_coord_notMem hΘs (j := p.2)
        (by rw [update_update_apply_snd]; exact hu)
    simp only [hz, mul_zero]
  rw [hfun, integral_zero]

/-- `pairG21` vanishes outside the box in its **second** kernel variable (which `pairG21` inserts at
the slot `p.1`). -/
theorem pairG21_eq_zero_of_snd_notMem {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {u y : E3}
    (hy : y ∉ Work.BoseK15.corpusBox.boxL ℓ) : pairG21 p Θ A u y = 0 := by
  rw [pairG21]
  have hfun : (fun x : Work.BoseDict.Xn n => star (Θ x) * A (x p.1) * A (x p.2)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)) = fun _ => (0 : ℂ) := by
    funext x
    have hz : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 :=
      theta_eq_zero_of_coord_notMem hΘs (j := p.1)
        (by rw [update_update_apply_fst hp]; exact hy)
    simp only [hz, mul_zero]
  rw [hfun, integral_zero]

/-! ## 3. The support statement -/

/-- **The fibre functions of the `Q₂` pair row are supported in the box squared.**  If the state
`Θ` vanishes outside the `n`-particle box `boxPow n ℓ = (boxL ℓ)^n`, then each of the three fibre
functions `pairG13`, `pairG23`, `pairG21` — as a function of its two kernel variables — vanishes as
soon as one of those two variables lies outside the one-particle box `boxL ℓ`.

This is the hypothesis `hCsupp` of `pairG13_L2` / `pairG23_L2` / `pairG21_L2`
(`Submission/Work/BoseBoxFock/pairRowS2Inst.lean`), which discharges the `hGle` hypothesis of the
block lemmas `block13_Ksub` / `blockTwo3_Ksub` / `blockII1_Ksub` of `pairRowS2`. -/
theorem pairG_supports {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)
      ∧ Function.support (Function.uncurry (pairG23 p Θ A B)) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)
      ∧ Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
        Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨w, y⟩ hz
    simp only [Function.mem_support, Function.uncurry_apply_pair] at hz
    refine ⟨?_, ?_⟩
    · by_contra hw
      exact hz (pairG13_eq_zero_of_fst_notMem p hΘs hw)
    · by_contra hy
      exact hz (pairG13_eq_zero_of_snd_notMem p hp hΘs hy)
  · rintro ⟨w, y⟩ hz
    simp only [Function.mem_support, Function.uncurry_apply_pair] at hz
    refine ⟨?_, ?_⟩
    · by_contra hw
      exact hz (pairG23_eq_zero_of_fst_notMem p hΘs hw)
    · by_contra hy
      exact hz (pairG23_eq_zero_of_snd_notMem p hp hΘs hy)
  · rintro ⟨u, y⟩ hz
    simp only [Function.mem_support, Function.uncurry_apply_pair] at hz
    refine ⟨?_, ?_⟩
    · by_contra hu
      exact hz (pairG21_eq_zero_of_fst_notMem p hΘs hu)
    · by_contra hy
      exact hz (pairG21_eq_zero_of_snd_notMem p hp hΘs hy)

end Work.BoseBoxFock
