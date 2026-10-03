import Mathlib
import Submission.Work.Peluse.UControl.levDInvStep

/-!
# The datum and the window tower of the level chain

This file fixes the last two objects the assembly of `PetLevelChain` needs: the nested PET datum
`D` attached to a `LevDInv`-state at level `d - 1`, and the map from the window tower
(`Fin (2H+1) × WinTower H L`) to the datum's parameter box `D.parBox d H`.

* `D.S j = Fin (N j)`: level `0` is the dummy singleton (`N 0 = 1`, hence `Fin (N 0) ≃ PUnit`);
* `D.par j k = the raw index set P j k, read through the inclusion `range (N j) → Fin (N j)`;
* `levTowerIdx h H p : (j : Fin d) → Fin (N j.1) → ℤ` is `boxVal H p.1` at level `0` and
  `WinTower.param H L p.2 (the coordinate c j s)` at the levels `≥ 1`.

The properties the terminal comparison (`levelCompareGen`) needs are `htower0` (definitional),
`htower_indep` (the level-`0` value does not influence the higher levels), `htower_mem`,
`htower_surj` (which needs the *inverse* coordinate map, built from `LevDInv.ccover` and
`LevDInv.cinj`) and `htower_inj`, together with the cardinality bound
`(D.parBox d H).card ≤ (2 * H + 1) ^ (L + 1)`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

/-- The inclusion of a raw attachment into `Fin (N j)`. -/
def levEmb {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i)) (j : ℕ)
    (k : Fin (N (j + 1))) : {s // s ∈ P j k.1} ↪ Fin (N j) :=
  ⟨fun s => ⟨s.1, Finset.mem_range.mp ((hsub j k.1 k.2) s.2)⟩,
    fun a b hab => by simpa using hab⟩

/-- **The nested PET datum of a `LevDInv`-state.**

Marked `@[reducible]` so that `(levDatumOf ...).S j` reduces to `Fin (N j)` at *reducible*
transparency: the terminal comparison (`levelCompareGen`) and the slot bijection work with `Finset`s
of `D.S (dd-1)`, and the elaborator must see that this is `Finset (Fin (N (dd-1)))`. -/
@[reducible] def levDatumOf (N : ℕ → ℕ) (P : ℕ → ℕ → Finset ℕ)
    (hsub : ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i))
    (hne : ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty) : IdxDatum where
  S := fun j => Fin (N j)
  finS := fun _ => inferInstance
  decS := fun _ => inferInstance
  par := fun j k => ⟨(P j k.1).attach.map (levEmb hsub j k), by
    obtain ⟨s, hs⟩ := hne j k.1 k.2
    exact ⟨(levEmb hsub j k) ⟨s, hs⟩,
      Finset.mem_map.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩⟩⟩

/-- The window tower of a `LevDInv`-state, mapped to the datum's parameter box. -/
def levTowerIdx {d : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ} {c : ℕ → ℕ → ℕ}
    {L' : ℕ} {hL' : 1 ≤ L'} {X : HistData d L'} {f₀ : Fin L' → Bool}
    (h : LevDInv d lc (d - 1) L' hL' N P c X f₀) (H : ℕ)
    (p : Fin (2 * H + 1) × WinTower H L') : (j : Fin d) → Fin (N j.1) → ℤ :=
  fun j s => if h0 : (j : ℕ) = 0 then IdxDatum.boxVal H p.1
    else WinTower.param H L' p.2
      ⟨c j.1 s.1, h.cbound j.1 (by omega) (by have := j.2; omega) s.1 s.2⟩

@[simp] lemma levTowerIdx_zero {d : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {L' : ℕ} {hL' : 1 ≤ L'} {X : HistData d L'} {f₀ : Fin L' → Bool}
    (h : LevDInv d lc (d - 1) L' hL' N P c X f₀) (H : ℕ)
    (p : Fin (2 * H + 1) × WinTower H L') (hd : 0 < d) :
    levTowerIdx h H p ⟨0, hd⟩ = fun _ => IdxDatum.boxVal H p.1 := by
  funext s
  simp [levTowerIdx]

lemma levTowerIdx_indep {d : ℕ} {lc : ℤ} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {L' : ℕ} {hL' : 1 ≤ L'} {X : HistData d L'} {f₀ : Fin L' → Bool}
    (h : LevDInv d lc (d - 1) L' hL' N P c X f₀) (H : ℕ)
    (k k' : Fin (2 * H + 1)) (t : WinTower H L') {j : Fin d} (hj : (j : ℕ) ≠ 0) :
    levTowerIdx h H (k, t) j = levTowerIdx h H (k', t) j := by
  funext s
  simp [levTowerIdx, hj]

end

end Work.Peluse.UControl
