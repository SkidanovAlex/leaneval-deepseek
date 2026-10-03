/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (equivariant form of node P7 of the Følner/Lück argument for JZLA20)

# The two-term operator `S + C·λ(t)` is injective (equivariant hypotheses)

This is the equivariant variant of `Work.ORP311.twoTerm_injective`.  Let `t ∈ G` normalise `N`
and have infinite order modulo `N` (`Work.ORP311.P311.TwistData N t`), and let
`S C : HSum n →L[ℂ] HSum n` be **equivariant** for the right regular representation
(`Work.ORVonNeumann.Rep.Equivariant`, i.e. lie in the group von Neumann algebra), **block
diagonal** over the `N`-cosets `N t^j` together with their adjoints (`Work.ORP311.IsBlockDiag`),
with `S` injective.  Then

  `S + C · λ(t)`

is injective.

The proof is the Følner/Lück window argument, identical to `Work.ORP311.twoTerm_injective`: the
kernel `K` of the two-term operator is invariant under the whole right regular action of `G`, so
its projection is equivariant and `hdim K = tDim (sWin t p) K / (2p+1)`; bounding
`tDim (sWin t p) K ≤ tDim (sWin t p) Ewin ≤ n` gives `(2p+1)·hdim K ≤ n` for every `p`, so
`hdim K = 0` and `K = ⊥`.

Compared with `twoTerm_injective`, the hypotheses here are exactly the ones available in the
call site: equivariance in place of commutation with `ρ(N)` and `ρ(t)` (over the extension
`G = N ⋊ ⟨t⟩`), and block diagonality of the adjoints in place of the extension hypothesis,
which was only used there to *derive* those two facts.  The whole remaining argument depends on
`TwistData` alone.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.twoTerm_injective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

theorem twoTerm_injective_equivariant {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n : ℕ) (S C : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) (hSe : Work.ORVonNeumann.Rep.Equivariant (G := G) S) (hCe : Work.ORVonNeumann.Rep.Equivariant (G := G) C) (hSb : Work.ORP311.IsBlockDiag N t n S) (hSb' : Work.ORP311.IsBlockDiag N t n (ContinuousLinearMap.adjoint S)) (hCb : Work.ORP311.IsBlockDiag N t n C) (hCb' : Work.ORP311.IsBlockDiag N t n (ContinuousLinearMap.adjoint C)) (hS : Function.Injective S) : Function.Injective (Work.ORP311.twoTerm (G := G) n t S C) := by
  classical
  -- The two-term operator is equivariant.
  have hZe : Rep.Equivariant (G := G) (twoTerm (G := G) n t S C) :=
    equivariant_twoTerm hSe hCe
  -- Block diagonality of the operators, and of their adjoints, gives commutation with `blk`.
  have hSb2 : ∀ j : ℤ, P311.blk n N t j ∘L S = S ∘L P311.blk n N t j :=
    fun j => blk_comp_of_isBlockDiag n j S hSb hSb'
  have hCb2 : ∀ j : ℤ, P311.blk n N t j ∘L C = C ∘L P311.blk n N t j :=
    fun j => blk_comp_of_isBlockDiag n j C hCb hCb'
  -- The kernel is invariant under the right regular action of `G`.
  have hKinv : ∀ g : G, ∀ x ∈ (twoTerm (G := G) n t S C).ker,
      Rep.diagOp (G := G) n g x ∈ (twoTerm (G := G) n t S C).ker := by
    intro g x hx
    have h1 : (twoTerm (G := G) n t S C) (Rep.diagOp (G := G) n g x)
        = Rep.diagOp (G := G) n g ((twoTerm (G := G) n t S C) x) := by
      have h2 := congrArg (fun f : Rep.HSum (G := G) n →L[ℂ] Rep.HSum (G := G) n => f x)
        (hZe g)
      simpa [ContinuousLinearMap.comp_apply] using h2
    have hx0 : (twoTerm (G := G) n t S C) x = 0 := hx
    have h2 : (twoTerm (G := G) n t S C) (Rep.diagOp (G := G) n g x) = 0 := by
      rw [h1, hx0, map_zero]
    simpa using h2
  -- Hence the projection onto the kernel is equivariant.
  have hPK : Rep.Equivariant (G := G) (twoTerm (G := G) n t S C).ker.starProjection :=
    Rep.equivariant_starProjection hKinv
  -- The Følner window bound `(2p+1)·hdim K ≤ n`.
  have hbound : ∀ p : ℕ,
      ((2 * p + 1 : ℕ) : ℝ) * Rep.hdim (G := G) (twoTerm (G := G) n t S C).ker ≤ (n : ℝ) := by
    intro p
    have h1 : tDim (G := G) n (P311.sWin t p) (twoTerm (G := G) n t S C).ker
        = ((P311.sWin t p).card : ℝ) * Rep.hdim (G := G) (twoTerm (G := G) n t S C).ker :=
      tDim_eq_card_mul_hdim _ hPK _
    have h2 : (P311.sWin t p).card = 2 * p + 1 := card_sWin h p
    have h3 := tDim_ker_le_tDim_Ewin (h := h) (p := p) hSb2 hCb2
    have h4 := tDim_Ewin_le (h := h) (p := p) hSb2 hCb2 hZe hS
    rw [h1, h2] at h3
    nlinarith [h3, h4]
  have hd0 : Rep.hdim (G := G) (twoTerm (G := G) n t S C).ker = 0 := by
    have hnn : 0 ≤ Rep.hdim (G := G) (twoTerm (G := G) n t S C).ker := by
      rw [Rep.hdim]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases eq_or_lt_of_le hnn with hh | hh
    · exact hh.symm
    · exfalso
      set d := Rep.hdim (G := G) (twoTerm (G := G) n t S C).ker with hd
      obtain ⟨p, hp⟩ := exists_nat_gt ((n : ℝ) / d)
      have h1 := hbound p
      have h2 : ((2 * p + 1 : ℕ) : ℝ) > (n : ℝ) / d := by
        have h3 : (p : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) := by push_cast; nlinarith
        linarith
      have h4 : ((2 * p + 1 : ℕ) : ℝ) * d > (n : ℝ) := by
        have h5 : (n : ℝ) / d < ((2 * p + 1 : ℕ) : ℝ) := h2
        have h6 := (div_lt_iff₀ hh).mp h5
        linarith
      linarith [h1, h4]
  have hKbot : (twoTerm (G := G) n t S C).ker = ⊥ :=
    eq_bot_of_hdim_eq_zero _ hKinv hd0
  intro x y hxy
  have hsub : x - y ∈ (twoTerm (G := G) n t S C).ker := by
    have h2 : (twoTerm (G := G) n t S C) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    simpa using h2
  rw [hKbot] at hsub
  have h0 : x - y = 0 := by simpa using hsub
  exact sub_eq_zero.mp h0

end Work.ORP311
