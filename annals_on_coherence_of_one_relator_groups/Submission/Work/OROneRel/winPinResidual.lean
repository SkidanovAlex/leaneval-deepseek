import Mathlib
import Submission.Work.OROneRel.hnnSplitPinFinal

/-!
# The residual of `magnusStepCase2`: the pin and its consistency

After the two-maps assembly (`Submission/Work/OROneRel/hnnSplitAssembly.lean`,
`hnnSplitPin.lean`, `hnnSplitPinPow.lean`, `hnnSplitPinFinal.lean`) everything needed to build the
`Z`-domain datum of the residual case of `Work.OROneRel.magnusStepCase2` is proved, and the datum
follows from exactly two statements about the window of `Work.OROneRel.exists_winWindowData`:

* the **pin** `hQ : ∀ j, θ (Q j) = mk (Wt j * (Wt 1) ^ (-j))` — the level factors
  `mk (Wt j) * (mk (Wt 1)) ^ (-j)` lie in the image of the vertex
  `⟨winBeta | winRoot ^ l⟩ ≤ ⟨α | u ^ l⟩` — for a family `Q : ℤ → ⟨winBeta | winRoot ^ l⟩`;
* the **consistency** `hcons` of the coedge labels along the levels:
  `(V i)⁻¹ * Γ (x,i) * V (i + c x) = (V j)⁻¹ * Γ (x,j) * V (j + c x)` for all window edges `(x,i)`,
  `(x,j)`, where `V j := of (Q j) * t ^ j` and `Γ (x,i)` is the coedge generator attached to `(x,i)`
  (`1` for a tree edge);

together with the *Freiheitssatz* plank `hA` (`winRho x ∈ ⟪u ^ l⟫ → x ∈ ⟪winRoot ^ l⟫`) and the
injectivity of `winTheta` (the same plank), the aperiodicity and norm bounds of `winRoot` (both
**provable**: `not_isProperPower_winRoot`, `winRootNormLt`), and the window data itself
(`Work.OROneRel.exists_winWindowData`).

This file states that package as `Work.OROneRel.winPinAndConsistency` (the single `sorry`) and proves
that it implies the `Z`-domain datum through the (sorry-free)
`Work.OROneRel.magnusDomainDatum_of_pin`.  **The statement of `winPinAndConsistency` is the exact
remaining gap of `Work.OROneRel.magnusStepCase2`**; see the seventeenth-session notes in the header of
`Submission/Work/OROneRel/magnusStepCase2.lean` for the warnings (the consistency is not a
consequence of the HNN relations — it is the splitting itself, in the form given by the two-maps
construction).

## Why the consistency is needed

`hcons` is exactly what makes the generator image

  `X x := (V (i0 x))⁻¹ * Γ (x, i0 x) * V (i0 x + c x)`

*independent of the chosen window level* `i0 x` of `x`, and it is equivalent (given the pin) to the
existence of the explicit inverse of the comparison map
`HNNExtension (⟨winBeta | winRoot ^ l⟩) A A ψ →* ⟨α | u ^ l⟩`, which is how the splitting was
reduced to algebra.  It is *not* a consequence of the pin: `Ψ` maps both sides of the defining
equation to `mk x`, so the equation says that the difference lies in the kernel of the comparison map.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The pin and its consistency: the exact residual of `Work.OROneRel.magnusStepCase2`.** -/
theorem winPinAndConsistency (u : FreeGroup α) (l : ℕ) {c : α → ℤ} (Wt : ℤ → FreeGroup α)
    (lo hi : ℤ) (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))))
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)) :
    ∃ (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A) (Q : ℤ → winHd Wt c lo hi u l),
      (∀ a : A, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
          Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (a : winHd Wt c lo hi u l) =
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (ψ a : winHd Wt c lo hi u l) *
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) ∧
      (∀ j : ℤ, Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (Q j) =
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt j * (Wt 1) ^ (-j))) ∧
      (∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
        (x, j) ∈ Work.OROneRel.winE c lo hi →
        (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
            levelEl (A := A) (ψ := ψ) Q (i + c x) =
          (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
            levelEl (A := A) (ψ := ψ) Q (j + c x)) := by
  sorry

/-- **The `Z`-domain datum of the residual from the pin and its consistency** (the sharpened form of
`Work.OROneRel.magnusDomainDatum_of_pin` with the existential package as a single hypothesis). -/
noncomputable def magnusDomainDatum_of_winPin (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    {c : α → ℤ} (Wt : ℤ → FreeGroup α) (lo hi : ℤ) (hW0 : Wt 0 = 1)
    (hcu : Work.OROneRel.cohom c u = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hppv : ¬ Work.OROneRel.IsProperPower (Work.OROneRel.winRoot Wt c lo hi u))
    (hnorm : Work.OROneRel.relatorNorm (Work.OROneRel.winRoot Wt c lo hi u) <
      Work.OROneRel.relatorNorm u)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))))
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)) :
    MagnusDomainDatum u l := by
  classical
  have h : Nonempty (MagnusDomainDatum u l) := by
    obtain ⟨A, ψ, Q, hψ, hQ, hcons⟩ :=
      winPinAndConsistency u l Wt lo hi hW0 hcu hcoh hwin htree hcov hlo1 hhi1 hA hθ
    exact ⟨magnusDomainDatum_of_pin u l hl Wt lo hi hW0 hcu hcoh hwin htree hcov hlo1 hhi1
      hppv hnorm hA hθ A ψ hψ Q hQ hcons⟩
  exact Classical.choice h

end Work.OROneRel
