import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.PL.Generic.Basic
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.hndOfFzvHull
import Submission.Work.Engulf.E4Aux.ordGeom

/-!
# `E4b`, the `X`-case: the `X`-points of a shelled simplex are `(q-2)`-dominated

This is the `X`-half of the bad-set lemma `E4b` of the shelling loop of Newman's Lemma 7 Case 1
(`Submission/Work/Engulf/E4Aux/NOTES_loop.md` §7.4, `Submission/Work/Engulf/E4alt/NOTES_step_interface.md`).
The other half — the *collision* case `g₁ x = g₁ y` with `y ∈ K ∪ Q^i` — is
`Work.Engulf.E4alt.collisionOfPair`.

Setting: the `E4a` normalisation `ND` (`Work.Engulf.Alt.NormData`), an `L7Hyp` instance, the `i`-th
simplex `σ = ND.ord[i]` of the shelling order (a core face, so `ND.wit` gives its affine witness
`A`, with `ND.g₁ = ψ ∘ A` on `simp σ`), and the affine series of the perturbed chart map.

Conclusion: there is `J ⊆ E n` with `PL.DomDim J (q - 2)` such that **every** point `x ∈ simp σ`
whose chart image `ψ (A x)` lies in `X` has `A x ∈ J`.  Consequently the `X`-points of the prism of
`σ` lie over `J`, which is what `E4Aux.prism_push_step`'s `hAs` needs (`J` is then transported by
the projection of the prism, `Work.Engulf.E4Aux.DomDim.affine_image'`).

**Interface point.**  The proof needs the cardinality bound `S.card ≤ p + 1` on the members of the
`Fixed` family `ND.Xcov`, so that `ND.fixed` yields `DomDim ((.(q+2) + T.card - 2 - n)) ≤ q - 2`
(`Work.Engulf.E4Aux.gdbound`).  `Work.Engulf.Alt.NormData` does not record such a bound, so it is
taken here as an explicit hypothesis `hXcov_card`; the intended value of `ND.Xcov` is the `DomIn`
cover of `ψ⁻¹ X ∩ closedCube 1` supplied by `SmoothChart` (whose members have `card ≤ p + 1`), not
a triangulation of the unit cube.
-/

open Set Metric PL

namespace Work.Engulf.E4Aux

universe u

theorem xCaseOfXcov {n p q N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁) (hp : p + 3 ≤ n)
    (hXcov_card : ∀ S ∈ ND.Xcov, S.card ≤ p + 1)
    {i : ℕ} (hi : i < ND.ord.length)
    (hcore : f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    {A : PL.E N →ᵃ[ℝ] PL.E n}
    (hAeq : ∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A x))
    (hAopen : ∀ x ∈ PL.simp (ND.ord[i]), A x ∈ PL.openCube (1 : ℝ))
    (hAvv : ∀ v ∈ ND.ord[i], A v = ND.vv v) :
    ∃ J : Set (PL.E n), PL.DomDim J ((q : ℤ) - 2) ∧
      ∀ x ∈ PL.simp (ND.ord[i]), ψ.toFun (A x) ∈ X → A x ∈ J := by
  classical
  have hq : q ≤ p := H7.hq
  have hmem : ND.ord[i] ∈ ND.ord := List.getElem_mem hi
  have hσ : ND.ord[i] ∈ ND.Γ₁.faces := ND.ord_mem _ hmem
  have hcard : (ND.ord[i]).card = q + 2 := by
    rw [ND.ord_card _ hmem, H7.card]
  have hsubΔ : PL.simp (ND.ord[i]) ⊆ PL.simp (τ₀ ∪ τ₁) := ND.ord_sub _ hmem
  -- the vertex set and the frozen independence needed by `ND.fixed`
  have hVt : ∀ v ∈ ND.ord[i], v ∈ ND.Vt := fun v hv => (ND.Vt_mem v).mpr ⟨_, hσ, hv⟩
  have hcardN : (ND.ord[i]).card ≤ n + 1 := by omega
  have hG : AffineIndependent ℝ (fun v : ↥(ND.ord[i] ∩ ND.Fzv) => ND.vv v) :=
    Work.Engulf.E4alt.hndOfFzvHull ND H7 ND.Fzv_hull hσ hsubΔ hcore
  -- the general-position bound, chosen once for each member of `ND.Xcov`
  have hex : ∀ T : Finset (E n), T ∈ ND.Xcov → ∃ J : Set (PL.E n),
      PL.DomDim J ((q : ℤ) - 2) ∧
      A '' PL.simp (ND.ord[i]) ∩ PL.simp T ⊆ A '' PL.simp (ND.ord[i] ∩ ND.Fzv) ∪ J := by
    intro T hT
    obtain ⟨D, hDdim, hDsub⟩ :=
      ND.fixed (ND.ord[i]) (ND.ord[i]) A T hcardN hVt hAvv hG hT
    refine ⟨D, PL.DomDim.mono_dim ?_ hDdim, hDsub⟩
    rw [hcard]
    have := hXcov_card T hT
    have hb := gdbound (q := q) hp
    push_cast at hb ⊢
    omega
  -- the family of exceptional sets, chosen so that it does not depend on the membership proof
  let J : Finset (E n) → Set (PL.E n) :=
    fun T => if hT : T ∈ ND.Xcov then Classical.choose (hex T hT) else ∅
  have hJ : ∀ T (hT : T ∈ ND.Xcov), PL.DomDim (J T) ((q : ℤ) - 2) ∧
      A '' PL.simp (ND.ord[i]) ∩ PL.simp T ⊆ A '' PL.simp (ND.ord[i] ∩ ND.Fzv) ∪ J T := by
    intro T hT
    have : J T = Classical.choose (hex T hT) := dif_pos hT
    rw [this]
    exact Classical.choose_spec (hex T hT)
  refine ⟨⋃ T ∈ ND.Xcov, J T, ?_, ?_⟩
  · refine PL.DomDim.biUnion fun T hT => (hJ T hT).1
  · intro x hx hX
    have hxσ : x ∈ PL.simp (ND.ord[i]) := hx
    have hycube : A x ∈ PL.closedCube (1 : ℝ) :=
      openCube_subset_closedCube (N := n) (1 : ℝ) (hAopen x hxσ)
    obtain ⟨T, hT, hyT⟩ := Set.mem_iUnion₂.mp (ND.Xcov_cov (A x) hycube hX)
    rcases (hJ T hT).2 ⟨⟨x, hxσ, rfl⟩, hyT⟩ with ⟨x', hx', hxx'⟩ | hyJ
    · -- the frozen alternative is impossible: it contradicts `L7Hyp.offX`
      exfalso
      have hx'σ : x' ∈ PL.simp (ND.ord[i]) := simp_mono Finset.inter_subset_left hx'
      have hx'L : x' ∈ L := ND.Fzv_hull _ hσ hcore hx'
      have heq : A x = A x' := hxx'.symm
      have hxx : x = x' :=
        (ND.indep (ND.ord[i]) A hcardN hVt hAvv hG) hxσ hx'σ heq
      have hxfz : x ∈ PL.simp (ND.ord[i] ∩ ND.Fzv) := hxx ▸ hx'
      have hxL : x ∈ L := ND.Fzv_hull _ hσ hcore hxfz
      have hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁) := hsubΔ hxσ
      have hfx : f x = ψ.toFun (A x) := by rw [← ND.g₁frz hxL, hAeq x hxσ]
      exact Set.disjoint_left.mp H7.offX ⟨x, ⟨hxL, hxΔ⟩, hfx⟩ hX
    · exact Set.mem_iUnion₂.mpr ⟨T, hT, hyJ⟩

end Work.Engulf.E4Aux
