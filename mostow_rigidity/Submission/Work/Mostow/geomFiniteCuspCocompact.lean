import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspHoroballsPairwise
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Work.Mostow.cuspCocompactAllLevels

/-!
# Area C1/G7 — cusp stabilisers are cocompact on horospheres

For a lattice `Γ` (discrete, finite covolume) and a parabolic fixed point `ξ`, the stabiliser
`Γ_ξ` acts cocompactly on every horosphere at `ξ`.

The proof has three chapters, each proved in its own file:

* `cuspHoroballsPairwise` : a `Γ`-equivariant height `ht` on `parFixed Γ` whose horoballs
  `horoball ξ (ht ξ)` are pairwise disjoint (Margulis).
* `cuspCocompactAtLevel` : that embedding at level `ht ξ` forces the quotient of the horosphere
  at `ξ` by `Γ_ξ` to have finite flat volume, whence (Bieberbach) a compact fundamental set.
* `cuspCocompactAllLevels` : horocyclic-flow equivariance transports one level to all levels.

The hypothesis `hvan` says every element of `Γ` fixing a parabolic fixed point preserves the
horospheres there; read at `ξ ∈ parFixed Γ` it is exactly the level preservation of `Γ_ξ`.

The embedding step is derived here: for `γ ∈ Γ` with `bd γ ξ ≠ ξ` the translate of the
`ht ξ`-horoball is `horoball (bd γ ξ) (ht ξ + bCocy γ ξ) = horoball (bd γ ξ) (ht (bd γ ξ))`
by equivariance of `ht`, and the cusp point `bd γ ξ` is again in `parFixed Γ`, so the pairwise
disjointness of the Margulis horoballs applies verbatim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- An element of `Γ` fixing `ξ ∈ parFixed Γ` preserves every horosphere at `ξ`. -/
lemma bCocy_eq_zero_of_mem_parFixed (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0) :
    ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
  fun γ hγ => hvan γ ξ hξ hγ

/-- `Γ_ξ` preserves every horosphere at `ξ`. -/
lemma busemann_smul_of_bd_eq (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} {ξ : E n} (hξ : ξ ∈ Sph n)
    (hstab : ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) (u : E n) :
    busemann ξ ((γ : PO n 1) • u) = busemann ξ u := by
  have hbus : busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • u)
      = busemann ξ u + busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) :=
    hI.2.2.2.2.2.2.2.2.2.2.2.2 (γ : PO n 1) ξ u hξ
  have h0 : busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) = 0 := by
    simpa only [bCocy] using hstab γ hγ
  rw [hγ] at hbus h0
  rw [h0] at hbus
  simpa using hbus

/-- The `ht ξ`-horoball at `ξ` embeds modulo `Γ`: its translates by elements of `Γ` not fixing
`ξ` are disjoint from it. -/
lemma cuspHoroballEmbedded (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0) :
    ∃ τ : ℝ, ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ)
        (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)) := by
  obtain ⟨ht, heq, hdisj⟩ := cuspHoroballsPairwise n hn hA hI hBb Γ hΓ hvan
  refine ⟨ht ξ, ?_⟩
  intro γ hγ
  have hmem : bd (γ : PO n 1) ξ ∈ parFixed Γ := parFixed_invariant hA hI Γ γ hξ
  have heqγ : ht (bd (γ : PO n 1) ξ) = ht ξ + bCocy (γ : PO n 1) ξ := heq γ ξ hξ
  have hne : ξ ≠ bd (γ : PO n 1) ξ := fun h => hγ h.symm
  have hpair := hdisj hξ hmem hne
  simp only at hpair
  rwa [heqγ] at hpair

theorem geomFiniteCuspCocompact (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0) :
    CuspCocompact Γ ξ := by
  -- Chapter 1: the τ-horoball at ξ embeds modulo Γ.
  obtain ⟨τ, hemb⟩ := cuspHoroballEmbedded n hn hA hI hBb Γ hΓ ξ hξ hvan
  -- The stabiliser Γ_ξ preserves the horospheres (hvan, read at ξ).
  have hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    bCocy_eq_zero_of_mem_parFixed Γ ξ hξ hvan
  -- Chapter 2: the horosphere at level τ is Γ_ξ-cocompact.
  obtain ⟨K, hKc, hK⟩ := cuspCocompactAtLevel n hn hA hI hBb Γ hΓ ξ hξ hstab τ hemb
  -- Chapter 3: horocyclic flow equivariance upgrades one level to all levels.
  exact cuspCocompactAllLevels n hA hI Γ ξ hξ.1 hstab τ ⟨K, hKc, hK⟩

end

end Work.Mostow
