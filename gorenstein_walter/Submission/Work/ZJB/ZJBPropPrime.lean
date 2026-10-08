import Submission.Work.ZJB.DefsPaper

/-!
# ZJB — the restated contract `ZJBProp'` (product order `N_G(Z(J(P)))·C_G(W)`)

LEAD RULING (design pass 11, `NOTES_LEAD_gw_design11.md` §3.1).  Glauberman 1968 writes
`x^g = g⁻¹xg`, so his `(C_p)` (p. 1116) reads, in Mathlib's vocabulary,
`conj g W ⊆ P ⟹ g ∈ N_G(K)·C_G(W)`, i.e. `g = n * c` with `n ∈ N_G(Z(J(P)))` and
`c ∈ C_G(W)`.  The printed product order cannot be reversed without extra input
(`ProductsCommute`, not in the source), so the contract is *restated* in the order the source
proves:

* `ZJBProp'` — the restated contract;
* `zjbProp'_of_satisfiesCpPaper` — the paper-form Theorem B plus `PStableProp` give it, with no
  product-commutation hypothesis;
* `mem_of_zjbProp'` — the shape the unique consumer (`CORE2A/lemma24.lean`) uses: `g` lies in
  every subgroup containing `C_G(W)` and `N_G(Z(J(P)))`.

The old contract-order files (`PaperBridge.lean`, the `ProductsCommute` route, `TheoremBStable`)
are kept as records but are off the path.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

/-- **`ZJBProp` restated** (product order `N_G(Z(J(P)))·C_G(W)`).  Identical to the contract
except for the conclusion `∃ n c, n ∈ N(Z(J(P))) ∧ c ∈ C(W) ∧ g = n * c`. -/
def ZJBProp' : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → DihOrCycSylow X →
    ∀ (P : Sylow p X) (W : Set X) (g : X), W.Nonempty → W ⊆ (P : Subgroup X) →
      (∀ w ∈ W, g * w * g⁻¹ ∈ (P : Subgroup X)) →
      ∃ n c : X, n ∈ normalizer (ZJ (P : Subgroup X) : Set X) ∧ c ∈ centralizer W ∧ g = n * c

/-- The paper-form Theorem B gives `ZJBProp'` directly (no product-commutation input). -/
theorem zjbProp'_of_satisfiesCpPaper
    (h : ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → DihOrCycSylow X →
      SatisfiesCpPaper p X) : ZJBProp' := by
  intro X _ _ p _ hp hD P W g hW hWP hg
  exact (controlsStrongFusionPaper_iff_rev _ _).1 (h X p hp hD P) W hW hWP g hg

/-- What `lemma24` actually consumes, derived from `ZJBProp'`: `g` lies in every subgroup that
contains both `C_G(W)` and `N_G(Z(J(P)))`. -/
theorem mem_of_zjbProp' (h : ZJBProp') {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hD : DihOrCycSylow X) (P : Sylow p X) (W : Set X) (g : X) (hW : W.Nonempty)
    (hWP : W ⊆ (P : Subgroup X)) (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ (P : Subgroup X))
    (H : Subgroup X) (hC : centralizer W ≤ H)
    (hN : normalizer (ZJ (P : Subgroup X) : Set X) ≤ H) : g ∈ H := by
  obtain ⟨n, c, hn, hc, rfl⟩ := h X p hp hD P W g hW hWP hg
  exact H.mul_mem (hN hn) (hC hc)

end Work.ZJB
