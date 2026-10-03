import Mathlib
import Submission.Work.OROneRel.hnnSplitPinPow
import Submission.Work.OROneRel.generation_of_level_factors
import Submission.Work.OROneRel.winVertex_levelFactor_mem

/-!
# The window splitting **without the pin**

The residual of `Work.OROneRel.magnusStepCase2` is the `Z`-domain splitting of
`G = ⟨α | u ^ l⟩` over the window vertex `winVertex = ⟨winBeta | winRoot ^ l⟩`.  In
`Submission/Work/OROneRel/hnnSplitPinFinal.lean` that splitting is derived from the **pin**

  `hQ : ∀ j, θ (Q j) = mk (Wt j * (Wt 1) ^ (-j))`

together with the **consistency** `hcons` of the coedge labels.  A direct inspection of the proof
(and of `Work.OROneRel.magnusDomainDatum_of_pin`) shows that the pin is used there for *three*
things only:

* `Q 0 = 1` and `Q 1 = 1` (the values of `Q` at the levels `0`, `1`),
* the *generation* plank `θ.range ⊔ zpowers (mk (Wt 1)) = ⊤`, via
  `Work.OROneRel.winVertex_generation_of_pin`;

everything else (`lift_genX_pow`, `lift_genX_Wt_one`, `lift_genX_coverClassAt`) uses only `Q 0 = 1`,
`Q 1 = 1` and the consistency `hcons`.

**The point of this file**: the generation plank is *weaker* than the pin and is provable from
*level-factor memberships at finitely many levels* -- namely, for each generator `x`, at *one*
window level `i x` of `x` and at `i x + c x`.  Concretely, `Work.OROneRel.generation_of_level_factors`
gives the generation from

  `mk (Wt i) * (mk τ) ^ (-i) ∈ winVertex`  and  `mk (Wt (i + c x)) * (mk τ) ^ (-(i + c x)) ∈ winVertex`

at the *chosen* levels, and the loop class of a window edge lies in `winVertex` by definition.

So the splitting of the window can be assembled from

* the **consistency** `hcons` for an *arbitrary* family `Q` with `Q 0 = Q 1 = 1`
  (the pin is **not** needed),
* the **generation** plank (provable from the level-factor memberships, see
  `Work.OROneRel.winVertex_generation_of_levelFactors`, or available directly from
  `Work.OROneRel.winVertex_levelFactor_mem` when the walks of `τ ^ i` stay inside the window),
* the Freiheitssatz plank `hA`/`hθ`.

The main output is `Work.OROneRel.magnusDomainDatum_of_consistencyData`: the `Z`-domain datum from
the window data, the Freiheitssatz, the generation plank, an associated subgroup `A ≤ Hd` with
`ψ : A ≃* A` and `hψ`, and a family `Q` with `Q 0 = 1`, `Q 1 = 1` and `hcons`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The loop class of a window edge lies in the vertex.**  (`winVertex` is the image of the loop
class map `winRho` under `PresentedGroup.mk`, so this is immediate, but it is used constantly.) -/
theorem winVertex_coverClassAt_mem (u : FreeGroup α) (l : ℕ) (c : α → ℤ)
    (Wt : ℤ → FreeGroup α) (lo hi : ℤ) {e : α × ℤ} (he : e ∈ winE c lo hi) :
    PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (coverClassAt Wt c e) ∈
      winVertex Wt c lo hi u l := by
  rw [winVertex]
  by_cases hcl : coverClassAt Wt c e = 1
  · rw [hcl, map_one]
    exact Subgroup.one_mem _
  · let e' : winBeta Wt c lo hi := ⟨e, he, hcl⟩
    refine ⟨winRho Wt c lo hi (FreeGroup.of e'), ⟨_, rfl⟩, ?_⟩
    show PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
        (winRho Wt c lo hi (FreeGroup.of e')) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (coverClassAt Wt c e)
    rw [winRho_of]

/-- **The generation plank from the level factors at the levels of the generators.**  If for every
generator `x` there is a window level `i` of `x` such that the level factors at `i` and at `i + c x`
lie in the vertex, then the vertex together with the class of the deck element `τ` generates
`⟨α | u ^ l⟩`.  This is exactly the hypothesis used by the two-maps construction, in its weakest
form: no *family* `Q` is needed, only these finitely many memberships. -/
theorem winVertex_generation_of_levelFactors {u : FreeGroup α} {l : ℕ} {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) (τ : FreeGroup α)
    (hfac : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi ∧
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈
        winVertex Wt c lo hi u l ∧
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt (i + c x)) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x)) ∈
        winVertex Wt c lo hi u l) :
    winVertex Wt c lo hi u l ⊔
      Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} = ⊤ := by
  have hfac' : ∀ x : α, ∃ i : ℤ,
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈
        (winTheta Wt c lo hi u l hW0 hcu hwin).range ∧
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt (i + c x)) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x)) ∈
        (winTheta Wt c lo hi u l hW0 hcu hwin).range ∧
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
          (Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹) ∈
        (winTheta Wt c lo hi u l hW0 hcu hwin).range := by
    intro x
    obtain ⟨i, hi1, hi2, hi3⟩ := hfac x
    refine ⟨i, ?_, ?_, ?_⟩
    · rw [winTheta_range]; exact hi2
    · rw [winTheta_range]; exact hi3
    · rw [winTheta_range, ← gaugeMap_of Wt c (x, i)]
      exact winVertex_coverClassAt_mem u l c Wt lo hi hi1
  have hrange : winVertex Wt c lo hi u l =
      (winTheta Wt c lo hi u l hW0 hcu hwin).range :=
    (winTheta_range Wt c lo hi u l hW0 hcu hwin).symm
  rw [hrange]
  exact generation_of_level_factors u l (winRoot Wt c lo hi u) _ c Wt τ hfac'

/-- **The generation plank from the walk containment on the window.**  This is the practical form of
`Work.OROneRel.winVertex_generation_of_levelFactors`: the level-factor memberships are supplied by
`Work.OROneRel.winVertex_levelFactor_mem`, whose hypothesis `htr` is *containment of the walk of
`τ ^ i` in the window* for the levels `i` of the window -- a purely combinatorial condition on the
window and the gauge.

So the generation half of the residual is **not** the pin: it follows from the containment of the
walks of `τ ^ i` in the window, since then every level factor at a level of the window lies in the
vertex, and the levels used by the two-maps construction are the window levels of the generators
(`hcov`). -/
theorem winVertex_generation_of_htr {u : FreeGroup α} {l : ℕ} (hl : 1 ≤ l)
    {c : α → ℤ} {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) (τ : FreeGroup α)
    (hτ : cohom c τ = Multiplicative.ofAdd 1)
    (htr : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ e ∈ decor c 0 (wordOf (τ ^ i)), coverEdge e ∈ winE c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ winE c lo hi) :
    winVertex Wt c lo hi u l ⊔
      Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} = ⊤ := by
  refine winVertex_generation_of_levelFactors hW0 hcu hwin τ ?_
  intro x
  obtain ⟨i, hmem⟩ := hcov x
  obtain ⟨hlo, hhi, hlo', hhi'⟩ := mem_winE.mp hmem
  exact ⟨i, hmem, winVertex_levelFactor_mem u l hl c τ Wt lo hi hW0 hcoh hcu hτ htr i hlo hhi,
    winVertex_levelFactor_mem u l hl c τ Wt lo hi hW0 hcoh hcu hτ htr (i + c x) hlo' hhi'⟩

/-- **The level-factor membership form of the pin.**  If the level factors
`mk (Wt j) * (mk τ) ^ (-j)` lie in the vertex for every level `j`, then there is a family
`Q : ℤ → Hd` with `θ (Q j) = mk (Wt j) * (mk τ) ^ (-j)` (the pin of
`Submission/Work/OROneRel/hnnSplitPinFinal.lean`).  Conversely (not needed here) the pin gives the
memberships.  So the *only* content of the pin is that these memberships hold. -/
theorem exists_pin_of_levelFactor_mem {u : FreeGroup α} {l : ℕ} {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1) (hcu : cohom c u = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) (τ : FreeGroup α)
    (hmem : ∀ j : ℤ, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt j) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-j) ∈
      winVertex Wt c lo hi u l) :
    ∃ Q : ℤ → winHd Wt c lo hi u l,
      ∀ j : ℤ, winTheta Wt c lo hi u l hW0 hcu hwin (Q j) =
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt j) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-j) := by
  have hmem' : ∀ j : ℤ, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt j) *
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-j) ∈
      (winTheta Wt c lo hi u l hW0 hcu hwin).range := by
    intro j
    rw [winTheta_range]
    exact hmem j
  choose Q hQ using fun j => hmem' j
  exact ⟨Q, hQ⟩

/-- **The `Z`-domain datum from the consistency alone** (no pin).  The comparison map
`Ψ : HNNExtension Hd A A ψ →* ⟨α | u ^ l⟩` is built from the class map `θ = winTheta` and the **stable
letter** `τ := Wt 1`; the explicit inverse is produced by the generator map `genX hcov Q`, whose three
defining conditions hold as soon as `Q 0 = 1`, `Q 1 = 1` and the coedge labels are consistent
(`hcons`); the generation plank `hgen` and the Freiheitssatz (`hA`, `hθ`) are the remaining inputs.

This is the *sharpened* form of `Work.OROneRel.magnusDomainDatum_of_pin`: the pin
`∀ j, θ (Q j) = mk (Wt j * τ ^ (-j))` is **not** used, so `Q` is an arbitrary family (subject only to
`Q 0 = 1`, `Q 1 = 1` and `hcons`). -/
noncomputable def magnusDomainDatum_of_consistencyData {u : FreeGroup α} {l : ℕ} {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ}
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
    (hθ : Function.Injective (winTheta Wt c lo hi u l hW0 hcu hwin))
    (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A)
    (hψ : ∀ a : A,
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
          winTheta Wt c lo hi u l hW0 hcu hwin (a : winHd Wt c lo hi u l) =
        winTheta Wt c lo hi u l hW0 hcu hwin (ψ a : winHd Wt c lo hi u l) *
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1))
    (hgen : (winTheta Wt c lo hi u l hW0 hcu hwin).range ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) = ⊤)
    (Q : ℤ → winHd Wt c lo hi u l) (hQ0 : Q 0 = 1) (hQ1 : Q 1 = 1)
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ winE c lo hi → (x, j) ∈ winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x)) :
    MagnusDomainDatum u l :=
  magnusDomainDatum_of_windowInverse u l Wt lo hi (Wt 1) hW0 hcu (hcoh 1) hwin hppv hnorm hA hθ
    A ψ hψ hgen (genX (A := A) (ψ := ψ) hcov Q)
    (lift_genX_pow (A := A) (ψ := ψ) hcu hwin hcov Q hQ0 hcons)
    (lift_genX_Wt_one (A := A) (ψ := ψ) hcov Q hQ0 hQ1 hcons hcoh htree hlo1 hhi1)
    (fun e => lift_genX_coverClassAt (A := A) (ψ := ψ) hcov Q hQ0 hcons hcoh htree e)

end Work.OROneRel
