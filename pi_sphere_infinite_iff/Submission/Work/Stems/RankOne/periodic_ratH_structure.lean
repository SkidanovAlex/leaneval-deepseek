import Mathlib
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Serre.EulerFibreRoot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rational homology of a space with periodic rational cohomology

If `X` has vanishing rational homology in positive degrees below `d`, rational cohomology
periodic with period `d` up to `T` (`H^m ≅ H^{m+d}` for `m + d ≤ T`) and `H^0(X;ℚ) ≅ ℚ`, then

* `H_{d·k}(X;ℚ) ≅ ℚ` for every `k` with `d·k ≤ T`, and
* `H_e(X;ℚ) = 0` for every `e ≤ T` that is not a multiple of `d`.

Both statements follow from the field universal coefficient theorem `H^n ≅ (H_n)^*`
(`Work.StemsB.ratDualUCT`, packaged as `Work.Serre.ratCoh_ratH_iso_rat` for the one-dimensional
case and `Work.Stems.isZero_ratH_of_isZero_ratCoh` /
`Work.Serre.isZero_ratCoh_of_isZero_ratH_dup` for vanishing): periodicity identifies `H^e` with
`H^{e mod d}`, and `H_{e mod d} = 0` for `0 < e mod d < d`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Stems.RankOne

theorem periodic_ratH_structure {X : Type} [TopologicalSpace X] {d T : ℕ} (hd : 1 ≤ d)
    (hLow : ∀ e : ℕ, 0 < e → e < d → CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) e))
    (hper : ∀ m : ℕ, m + d ≤ T →
      Nonempty (Work.Serre.ratCoh (TopCat.of X) m ≅ Work.Serre.ratCoh (TopCat.of X) (m + d)))
    (h0 : Nonempty (Work.Serre.ratCoh (TopCat.of X) 0 ≅ ModuleCat.of ℚ ℚ)) :
    (∀ k : ℕ, d * k ≤ T → Nonempty (Work.Serre.ratH (TopCat.of X) (d * k) ≅ ModuleCat.of ℚ ℚ)) ∧
      (∀ e : ℕ, e ≤ T → (∀ k : ℕ, e ≠ d * k) →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) e)) := by
  classical
  -- The periodicity iterated downwards: `H^{m + d·j} ≅ H^m` as long as `m + d·j ≤ T`.
  have shift : ∀ (m j : ℕ), m + d * j ≤ T →
      Nonempty (Work.Serre.ratCoh (TopCat.of X) (m + d * j) ≅
        Work.Serre.ratCoh (TopCat.of X) m) := by
    intro m j
    induction j with
    | zero => exact fun _ => ⟨Iso.refl _⟩
    | succ j ih =>
      intro h
      have hmul : m + d * (j + 1) = (m + d * j) + d := by
        rw [Nat.mul_succ, Nat.add_assoc]
      have hdT : (m + d * j) + d ≤ T := by rw [← hmul]; exact h
      have hmT : m + d * j ≤ T := by omega
      obtain ⟨e₁⟩ := hper (m + d * j) hdT
      obtain ⟨e₂⟩ := ih hmT
      exact ⟨(eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of X)) hmul)).trans
        (e₁.symm.trans e₂)⟩
  constructor
  · -- `H^{d·k} ≅ H^0 ≅ ℚ`, hence `H_{d·k} ≅ ℚ` by the universal coefficient theorem.
    intro k hk
    obtain ⟨e⟩ := shift 0 k (by simpa using hk)
    have heq0 : 0 + d * k = d * k := Nat.zero_add (d * k)
    have hCoh : Nonempty (Work.Serre.ratCoh (TopCat.of X) (d * k) ≅ ModuleCat.of ℚ ℚ) :=
      ⟨(eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of X)) heq0)).symm.trans
        (e.trans h0.some)⟩
    exact (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of X) (d * k)).mp hCoh
  · -- `H_e ≅ H^{e mod d} = 0` for `e` not a multiple of `d`.
    intro e he hne
    have hmod : e % d ≠ 0 := by
      intro h0r
      have h1 : d * (e / d) + e % d = e := Nat.div_add_mod e d
      rw [h0r, Nat.add_zero] at h1
      exact hne (e / d) h1.symm
    have hrpos : 0 < e % d := Nat.pos_of_ne_zero hmod
    have hrd : e % d < d := Nat.mod_lt e (by omega)
    have hHr : IsZero (Work.Serre.ratH (TopCat.of X) (e % d)) := hLow (e % d) hrpos hrd
    have hCr : IsZero (Work.Serre.ratCoh (TopCat.of X) (e % d)) :=
      Work.Serre.isZero_ratCoh_of_isZero_ratH_dup hHr
    have heq : e % d + d * (e / d) = e := by rw [Nat.add_comm, Nat.div_add_mod]
    have hbound : e % d + d * (e / d) ≤ T := by rw [heq]; exact he
    obtain ⟨eiso⟩ := shift (e % d) (e / d) hbound
    have hCe : IsZero (Work.Serre.ratCoh (TopCat.of X) e) :=
      IsZero.of_iso hCr
        ((eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of X)) heq.symm)).trans eiso)
    exact Work.Stems.isZero_ratH_of_isZero_ratCoh hCe

end Work.Stems.RankOne
