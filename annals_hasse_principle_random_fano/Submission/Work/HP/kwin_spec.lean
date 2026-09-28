import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.sum_le_ceil_logb_of_prod

/-!
# Dyadic window exponents of the successive minima (`Work.HP.kwin_spec`)

`kwin r L j = ⌈log₂ λ_{j+1}(L)⌉` is the dyadic window exponent attached to the `(j+1)`-st
successive minimum of the integral lattice `L ⊆ ℤ^ι`.  This file records the four
properties of `kwin` used when lattices are grouped into dyadic windows:

* `λ_{j+1} ≤ 2^{kwin j}` and `2^{kwin j} ≤ 2 λ_{j+1}` (the window is *tight*);
* `kwin` is monotone in `j` (successive minima are monotone);
* the exponents of a *monotone* family with `∏ 2^{kwin j} ≤ M` are bounded by
  `⌈log₂ M⌉`, i.e. the dyadic window search costs at most a factor `M`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

/-- For `1 ≤ i ≤ rk L` the `i`-th successive minimum of an integral lattice is at least `1`:
all vectors of `lamSet L i` are nonzero lattice vectors, hence of Euclidean norm `≥ 1`.
This strengthens `lam_pos` (`0 < lam L i`) to `1 ≤ lam L i`, which is what the dyadic
window bounds need. -/
lemma one_le_lam {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) {i : ℕ}
    (hi1 : 1 ≤ i) (hi : i ≤ rk L) : 1 ≤ lam L i := by
  rw [lam_eq_sInf]
  refine le_csInf (lamSet_nonempty L hi) ?_
  rintro r ⟨_, f, _, hfLI, hfr⟩
  have h0 : f ⟨0, hi1⟩ ≠ 0 := hfLI.ne_zero ⟨0, hi1⟩
  exact (one_le_eNorm h0).trans (hfr ⟨0, hi1⟩)

theorem kwin_spec (ι : Type) [Fintype ι] (r : ℕ) (L : Submodule ℤ (ι → ℤ)) (hr2 : 2 ≤ r)
    (hr : rk L = r) :
    (∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j)) ∧
    (∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1)) ∧
    Monotone (kwin r L) ∧
    (∀ M : ℝ, 1 ≤ M → (∏ j : Fin r, (2 : ℝ) ^ (kwin r L j)) ≤ M →
      (∑ j : Fin r, kwin r L j) ≤ ⌈Real.logb 2 M⌉₊) := by
  -- the index `j.1 + 1` never exceeds the rank
  have hrk : ∀ j : Fin r, j.1 + 1 ≤ rk L := by
    intro j
    rw [hr]
    exact j.2
  have hpos : ∀ j : Fin r, 1 ≤ lam L (j.1 + 1) := fun j =>
    one_le_lam L (by omega) (hrk j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa [kwin] using (ceil_logb_bounds (hpos j)).1
  · intro j
    simpa [kwin] using (ceil_logb_bounds (hpos j)).2
  · rintro j j' hjj
    have hjj' : j.1 + 1 ≤ j'.1 + 1 := by
      have h := Fin.le_def.mp hjj
      omega
    have hle : lam L (j.1 + 1) ≤ lam L (j'.1 + 1) := lam_mono L hjj' (hrk j')
    have h1 : 0 < lam L (j.1 + 1) := lam_pos L (by omega) (hrk j)
    have h2 : 0 < lam L (j'.1 + 1) := lam_pos L (by omega) (hrk j')
    have hlog := (Real.logb_le_logb (b := 2) (by norm_num) h1 h2).mpr hle
    simpa [kwin] using Nat.ceil_mono hlog
  · intro M hM h
    exact sum_le_ceil_logb_of_prod hM h

end Work.HP
