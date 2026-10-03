import Mathlib
import Submission.Work.OROneRel.winSplitNoPin
import Submission.Work.OROneRel.conjugateHnnSubgroups_zInvariant

/-!
# The residual of the window route, in **pin-free** form

`Submission/Work/OROneRel/winSplitNoPin.lean` proves that the two-maps assembly of the `Z`-domain
splitting of `G = ⟨α | u ^ l⟩` over the window vertex needs only

* an associated subgroup `A ≤ Hd = ⟨winBeta | winRoot ^ l⟩`, an isomorphism `ψ : A ≃* A` with the
  conjugation relation `hψ` (both are *free*: `Work.OROneRel.conjugateHnnSubgroups_zInvariant`
  produces them from the injectivity of the class map),
* a family `Q` with `Q 0 = 1`, `Q 1 = 1` and the **consistency** `hcons` of the coedge labels,
* the **generation** plank `hgen : θ.range ⊔ zpowers (mk τ) = ⊤`,
* the Freiheitssatz plank `hA` and the injectivity `hθ` of the class map `θ = winTheta`.

The **pin** `∀ j, θ (Q j) = mk (Wt j * τ ^ (-j))` is *not* used: it was needed in
`Submission/Work/OROneRel/winPinResidual.lean` only to produce `Q 0 = 1`, `Q 1 = 1` and `hgen`, and
`hgen` is much weaker than the pin -- it follows from the *level-factor memberships at the levels of
the generators* (`Work.OROneRel.winVertex_generation_of_levelFactors`), which in turn follow from the
*containment of the walks of `τ ^ i` in the window* (`Work.OROneRel.winVertex_generation_of_htr`,
using the proved `Work.OROneRel.winVertex_levelFactor_mem`).

The first section below shows that `A` and `ψ` (and the relation `hψ`) are likewise *free*: they are
the `ℤ`-invariant part of the vertex together with its conjugation by `mk (Wt 1)`.  Hence the
residual is exactly `Work.OROneRel.winConsistencyResidual` below -- a family `Q` with `Q 0 = 1`,
`Q 1 = 1`, the consistency of the coedge labels and the generation plank -- and its single `sorry`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Levels of a window walk -/

/-- **A traversal of a walk whose edge lies in the window has both its levels in the window.** -/
theorem coverSrc_mem_of_coverEdge_mem {c : α → ℤ} {lo hi : ℤ} {p : (α × ℤ) × Bool}
    (h : coverEdge p ∈ winE c lo hi) : lo ≤ coverSrc c p ∧ coverSrc c p ≤ hi := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp h
  rcases p with ⟨e, b⟩
  cases b
  · -- negative traversal: the source is `e.2 + c e.1`
    simp only [coverEdge, coverSrc, Bool.false_eq_true, if_false]
    exact ⟨h3, h4⟩
  · -- positive traversal: the source is `e.2`
    simp only [coverEdge, coverSrc, if_true]
    exact ⟨h1, h2⟩

/-- **A traversal of a walk whose edge lies in the window has both its levels in the window**
(target form). -/
theorem coverTgt_mem_of_coverEdge_mem {c : α → ℤ} {lo hi : ℤ} {p : (α × ℤ) × Bool}
    (h : coverEdge p ∈ winE c lo hi) : lo ≤ coverTgt c p ∧ coverTgt c p ≤ hi := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_winE.mp h
  rcases p with ⟨e, b⟩
  cases b
  · simp only [coverEdge, coverTgt, Bool.false_eq_true, if_false]
    exact ⟨h1, h2⟩
  · simp only [coverEdge, coverTgt, if_true]
    exact ⟨h3, h4⟩

/-! ## The associated subgroup `A` and its conjugation `ψ` are *free*

The relation `hψ` of the residual -- `mk (Wt 1) * θ a = θ (ψ a) * mk (Wt 1)` -- is not an extra
obligation: it holds for the *`ℤ`-invariant part* of the vertex with `ψ` the (inverse) conjugation
by `mk (Wt 1)`, which is exactly `Work.OROneRel.conjugateHnnSubgroups_zInvariant` applied to the
class map `θ = winTheta` (injective by the Freiheitssatz plank `hθ`).  Consequently the residual can
be restated with `A` and `ψ` *fixed* (the canonical choice below), and the only remaining content is
the family `Q` with its consistency and the generation plank. -/

/-- **The associated subgroup of the window and its conjugation automorphism.**  Given the
Freiheitssatz plank (through the injectivity of the class map `θ = winTheta`), the `ℤ`-invariant
part of the vertex comes with an automorphism `ψ` satisfying the HNN relation
`mk (Wt 1) * θ a = θ (ψ a) * mk (Wt 1)`; this is
`Work.OROneRel.conjugateHnnSubgroups_zInvariant` with the two directions of the conjugation
reversed. -/
theorem winSplitAux {α : Type u} (u : FreeGroup α) (l : ℕ) {c : α → ℤ} {Wt : ℤ → FreeGroup α}
    {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)) :
    ∃ (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A),
      ∀ a : A, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
          Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (a : winHd Wt c lo hi u l) =
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (ψ a : winHd Wt c lo hi u l) *
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) := by
  classical
  obtain ⟨A, φ, -, hφ⟩ :=
    Work.OROneRel.conjugateHnnSubgroups_zInvariant
      (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) hθ
  refine ⟨A, φ.symm, fun a => ?_⟩
  have h := hφ (φ.symm a)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-- The canonical associated subgroup of the residual. -/
noncomputable def winSplitA {α : Type u} (u : FreeGroup α) (l : ℕ) {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)) :
    Subgroup (winHd Wt c lo hi u l) :=
  (winSplitAux u l hW0 hcu hwin hθ).choose

/-- The canonical conjugation automorphism of the residual. -/
noncomputable def winSplitPsi {α : Type u} (u : FreeGroup α) (l : ℕ) {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)) :
    winSplitA u l hW0 hcu hwin hθ ≃* winSplitA u l hW0 hcu hwin hθ :=
  (winSplitAux u l hW0 hcu hwin hθ).choose_spec.choose

/-- The canonical pair satisfies the HNN relation. -/
theorem winSplitPsi_hψ {α : Type u} (u : FreeGroup α) (l : ℕ) {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)) :
    ∀ a : winSplitA u l hW0 hcu hwin hθ,
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
          Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin
            (a : winHd Wt c lo hi u l) =
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin
            (winSplitPsi u l hW0 hcu hwin hθ a : winHd Wt c lo hi u l) *
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) :=
  (winSplitAux u l hW0 hcu hwin hθ).choose_spec.choose_spec

/-! ## The residual -/

/-- **The residual of the window route, with the associated subgroup fixed.**  This is the exact
remaining content of `Work.OROneRel.magnusDomainDatum_of_consistencyData`: a family
`Q : ℤ → Hd` with `Q 0 = 1`, `Q 1 = 1`, the **consistency** of the coedge labels (an equation in the
HNN extension `HNN (Hd, A, A, ψ)` with the *canonical* `A = winSplitA`, `ψ = winSplitPsi`), and the
**generation** plank.

* The consistency is the *content* of the splitting: it is equivalent to the existence of the
  explicit inverse of the comparison map (the two-maps construction), i.e. to Linton's
  `π₁(X) ≅ HNN (π₁ D, π₁ (D ∩ t⁻¹D), π₁ (D ∩ tD))` (`One-relator hierarchies`, arXiv 2202.11324,
  Proposition 4.3).
* The generation plank is *provable* from the containment of the walks of `τ ^ i` in the window
  (`Work.OROneRel.winVertex_generation_of_htr`); it is kept here because that containment is a
  property of the specific gauge `treeGauge` of `Work.OROneRel.exists_winWindowData`. -/
theorem winConsistencyResidual (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
    (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hA : ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))))
    (hθ : Function.Injective (winTheta Wt c lo hi u l hW0 hcu hwin)) :
    ∃ Q : ℤ → winHd Wt c lo hi u l,
      Q 0 = 1 ∧ Q 1 = 1 ∧
      (∀ (x : α) (i j : ℤ), (x, i) ∈ winE c lo hi → (x, j) ∈ winE c lo hi →
        (levelEl (A := winSplitA u l hW0 hcu hwin hθ)
            (ψ := winSplitPsi u l hW0 hcu hwin hθ) Q i)⁻¹ *
          winGammaK Wt c lo hi u l (winSplitA u l hW0 hcu hwin hθ)
            (winSplitPsi u l hW0 hcu hwin hθ) (x, i) *
          levelEl (A := winSplitA u l hW0 hcu hwin hθ)
            (ψ := winSplitPsi u l hW0 hcu hwin hθ) Q (i + c x) =
        (levelEl (A := winSplitA u l hW0 hcu hwin hθ)
            (ψ := winSplitPsi u l hW0 hcu hwin hθ) Q j)⁻¹ *
          winGammaK Wt c lo hi u l (winSplitA u l hW0 hcu hwin hθ)
            (winSplitPsi u l hW0 hcu hwin hθ) (x, j) *
          levelEl (A := winSplitA u l hW0 hcu hwin hθ)
            (ψ := winSplitPsi u l hW0 hcu hwin hθ) Q (j + c x)) ∧
      (winTheta Wt c lo hi u l hW0 hcu hwin).range ⊔
        Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) = ⊤ := by
  sorry

/-- **The residual of the window route in pin-free form.**  Given the window data and the two
Freiheitssatz planks, there are an associated subgroup `A` of the vertex with its conjugation
automorphism `ψ`, a family `Q` with `Q 0 = 1`, `Q 1 = 1` and the consistency of the coedge labels,
and the generation plank holds.

This is now a *consequence* of `Work.OROneRel.winConsistencyResidual`: the pair `(A, ψ)` is the
canonical one (`Work.OROneRel.winSplitA`, `Work.OROneRel.winSplitPsi`, whose HNN relation is
`Work.OROneRel.winSplitPsi_hψ`), so the only remaining content is the family `Q`. -/
theorem winSplitResidual (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
    (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hA : ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))))
    (hθ : Function.Injective (winTheta Wt c lo hi u l hW0 hcu hwin)) :
    ∃ (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A) (Q : ℤ → winHd Wt c lo hi u l),
      (∀ a : A,
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
            winTheta Wt c lo hi u l hW0 hcu hwin (a : winHd Wt c lo hi u l) =
          winTheta Wt c lo hi u l hW0 hcu hwin (ψ a : winHd Wt c lo hi u l) *
            PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) ∧
      Q 0 = 1 ∧ Q 1 = 1 ∧
      (∀ (x : α) (i j : ℤ), (x, i) ∈ winE c lo hi → (x, j) ∈ winE c lo hi →
        (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
            levelEl (A := A) (ψ := ψ) Q (i + c x) =
          (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
            levelEl (A := A) (ψ := ψ) Q (j + c x)) ∧
      (winTheta Wt c lo hi u l hW0 hcu hwin).range ⊔
        Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) = ⊤ := by
  obtain ⟨Q, hQ0, hQ1, hcons, hgen⟩ :=
    winConsistencyResidual u l hl hW0 hcu hcoh hwin htree hcov hlo1 hhi1 hA hθ
  exact ⟨winSplitA u l hW0 hcu hwin hθ, winSplitPsi u l hW0 hcu hwin hθ, Q,
    winSplitPsi_hψ u l hW0 hcu hwin hθ, hQ0, hQ1, hcons, hgen⟩

/-! ## The Freiheitssatz plank -/

/-- **The Freiheitssatz plank of the window route.**  For the canonical window data of
`Work.OROneRel.exists_winWindowData` (together with the normalization `lo ≤ 1 ≤ hi` of
`Work.OROneRel.exists_winWindowData_containing_one`, which is available by reflecting the levels when
the walk has no positive level), the class map of the window basis satisfies the *Freiheitssatz of
the domain*:

  `winRho x ∈ ⟪u ^ l⟫  →  x ∈ ⟪winRoot ^ l⟫`.

This is Linton's `π₁`-injectivity of the gates `D ∩ t^{±1}D → D, t^±D` (`One-relator hierarchies`,
arXiv 2202.11324, Proposition 4.9 combined with the Freiheitssatz), i.e. the input of Proposition 4.3
(the splitting) and of Proposition 2.2.19 (`π₁(X) ≅ π₁(Z) ∗_ψ`).

**The statement is deliberately *not* universal in the window data**: it is false as a universal
statement even with all the band hypotheses and `hbad` -- see
`Submission/Work/OROneRel/wfbBandCounter.lean` and `NOTES_winFreiheitssatz_band_false.md`, where the
`β`-basis is not tied to the relator by anything except the traversals of the walk.  The canonical
window of `Work.OROneRel.exists_winWindowData` is a *minimal* `Z`-domain (its `hone` condition says
that no non-zero translate of the walk of `u` fits in it), and this is exactly the setting in which
Linton's minimality argument produces the Freiheitssatz; hence the data is existentially quantified
here. -/
theorem winFreiheitssatzResidual {α : Type u} [Fintype α] [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (hu : ¬ IsProperPower u) (hn : 2 ≤ relatorNorm u)
    (hbad : ∀ x : α, x ∈ relatorLetters u → eps x u ≠ 0) :
    ∃ (c : α → ℤ) (lo hi : ℤ) (Wt : ℤ → FreeGroup α),
      cohom c u = 1 ∧ Wt 0 = 1 ∧
      (∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      lo ≤ 1 ∧ 1 ≤ hi ∧
      (∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi) ∧
      (∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi) ∧
      (∃ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winTree Wt c lo hi) ∧
      (∀ x : FreeGroup (winBeta Wt c lo hi),
        winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
          x ∈ Subgroup.normalClosure
            ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi)))) := by
  sorry

/-- **The `Z`-domain datum from the residual.**  This is the assembly that turns the pin-free
residual into the datum of `Work.OROneRel.magnus_step_root_no_eps_zero`: the aperiodicity and the
norm bound of the window root are *proved* (`Work.OROneRel.not_isProperPower_winRoot`,
`Work.OROneRel.winRootNormLt`), and the splitting data of `winSplitResidual` feeds
`Work.OROneRel.magnusDomainDatum_of_consistencyData`. -/
theorem nonempty_magnusDomainDatum_of_residual (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
    (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ decor c 0 (wordOf (Wt i)), coverEdge q ∈ winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hppv : ¬ IsProperPower (winRoot Wt c lo hi u))
    (hnorm : relatorNorm (winRoot Wt c lo hi u) < relatorNorm u)
    (hA : ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))))
    (hθ : Function.Injective (winTheta Wt c lo hi u l hW0 hcu hwin)) :
    Nonempty (MagnusDomainDatum u l) := by
  obtain ⟨A, ψ, Q, hψ, hQ0, hQ1, hcons, hgen⟩ :=
    winSplitResidual u l hl hW0 hcu hcoh hwin htree hcov hlo1 hhi1 hA hθ
  exact ⟨magnusDomainDatum_of_consistencyData hW0 hcu hcoh hwin htree hcov hlo1 hhi1 hppv hnorm
    hA hθ A ψ hψ hgen Q hQ0 hQ1 hcons⟩

end Work.OROneRel
