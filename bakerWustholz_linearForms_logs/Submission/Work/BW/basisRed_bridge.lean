import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.basisRed_dim_transport
import Submission.Work.BW.basisRed_sInf_posPart
import Submission.Work.BW.basisRed_succMinL_set_univ_or_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bridge between `succMinL (wNorm A c)` and `succMin (latOf A) (wl1 c)`

Two formalisations of the successive minima of the lattice `A ℤⁿ` with respect to the weighted
`ℓ¹` body are in circulation in this development:

* `Work.BW.succMinL F j` (file `basisRed_defs`) — successive minimum of `ℤⁿ` with respect to the
  unit ball of `F`, i.e. of the *preimage* lattice;
* `Work.BW.succMin L F j` (file `minkowski_defs`) — successive minimum of a lattice `L` with
  respect to the body `{F ≤ 1}`.

For `F = Work.BW.wNorm A c` (the weighted `ℓ¹`-norm of the image under `A`) and
`L = Work.BW.latOf A = A ℤⁿ` with `F = Work.BW.wl1 c` these two invariants coincide:
`wNorm A c` on `ℤⁿ` is `wl1 c ∘ A`, and `A` maps `ℤⁿ` isomorphically (as a real vector space,
`A.det ≠ 0`) onto `A ℤⁿ`.  This file proves the identity.

The three ingredients are delegated and proved in sibling files:

* `Work.BW.basisRed_dim_transport` — the level sets of the two norms correspond under `A`, so
  their real spans have the same dimension;
* `Work.BW.basisRed_succMinL_set_univ_or_nonneg` — the level set `{t | j ≤ dim span …}` of
  `succMinL` is either all of `ℝ` (a negative level is then attained, and absolute homogeneity of
  `wNorm` forces arbitrary negative levels) or contained in `[0,∞)`;
* `Work.BW.basisRed_sInf_posPart` — for an upward closed set with that property the infimum does
  not change on intersecting with the *positive* levels `(0,∞)`, which is precisely the
  difference between the two conventions (`succMinL` allows all real levels, `succMin` requires
  `0 < lam`).
-/

namespace Work.BW

open scoped Classical

theorem basisRed_bridge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (j : ℕ) :
    Work.BW.succMinL (Work.BW.wNorm A c) j
      = Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) j := by
  -- The level set of `succMinL` and its counterpart for `succMin` (without the positivity
  -- condition on the level).
  set S : Set ℝ := {t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
      (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t})} with hSdef
  set S' : Set ℝ := {t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ
      ({x : Fin n → ℝ | Work.BW.wl1 c x ≤ t} ∩ (Work.BW.latOf A : Set (Fin n → ℝ))))} with hS'def
  have h1 : Work.BW.succMinL (Work.BW.wNorm A c) j = sInf S := rfl
  -- The two level conditions agree, level by level.
  have hlev : ∀ t : ℝ,
      j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t})
      ↔ j ≤ Module.finrank ℝ (Submodule.span ℝ
          ({x : Fin n → ℝ | Work.BW.wl1 c x ≤ t} ∩ (Work.BW.latOf A : Set (Fin n → ℝ)))) :=
    fun t => by rw [basisRed_dim_transport A hA c t]
  have hconv : ∀ t : ℝ, (t ∈ S ↔ t ∈ S') := by
    intro t
    rw [hSdef, hS'def]
    exact hlev t
  have hSS' : S = S' := Set.ext hconv
  -- The set of levels on the `succMin` side is the intersection of `S'` with the positive levels.
  have hT : {lam : ℝ | 0 < lam ∧ j ≤ Module.finrank ℝ (Submodule.span ℝ
          ({x : Fin n → ℝ | Work.BW.wl1 c x ≤ lam} ∩ (Work.BW.latOf A : Set (Fin n → ℝ))))}
        = S' ∩ Set.Ioi 0 := by
    rw [hS'def]
    ext lam
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioi]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have h2 : Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) j = sInf (S' ∩ Set.Ioi 0) := by
    rw [Work.BW.succMin, hT]
  -- `S'` is upward closed …
  have hup : ∀ ⦃s t : ℝ⦄, s ∈ S' → s ≤ t → t ∈ S' := by
    intro s t hs hst
    rw [hS'def] at hs ⊢
    refine le_trans hs (Submodule.finrank_mono (Submodule.span_mono ?_))
    intro x hx
    exact ⟨le_trans hx.1 hst, hx.2⟩
  -- … and it is either everything or contained in `[0,∞)`.
  have hpos : S' = Set.univ ∨ S' ⊆ Set.Ici 0 := by
    rcases basisRed_succMinL_set_univ_or_nonneg A c j with h | h
    · left
      ext t
      rw [← hconv t, hSdef, h]
    · right
      intro t ht
      exact h ((hconv t).mpr ht)
  -- Hence the positivity condition on the level does not change the infimum.
  have hkey := basisRed_sInf_posPart hup hpos
  rw [h1, h2, hSS']
  exact hkey

end Work.BW
