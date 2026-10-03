import Mathlib
import Submission.Work.OROneRel.hnnSplitPinPow
import Submission.Work.OROneRel.winVertex_generation_of_pin

/-!
# The `Z`-domain datum of the residual case from the *pin*

This file assembles the reduction of the residual case of `Work.OROneRel.magnusStepCase2` to its
geometric input, the **pin**: a family `Q : ℤ → ⟨winBeta | winRoot ^ l⟩` with

  `θ (Q j) = mk (Wt j * (Wt 1) ^ (-j))`

(the *level factors* `mk (Wt j) * (mk (Wt 1)) ^ (-j)` lie in the image of the vertex), together with
the **consistency** of the coedge labels along the levels (`hcons`).

From the pin one gets

* `Q 0 = 1` and `Q 1 = 1` (the pin at the levels `0` and `1` is trivial),
* the *generation* plank `θ.range ⊔ zpowers (mk (Wt 1)) = ⊤`
  (`winVertex_generation_of_pin` with the level factors from the pin),
* the generator image `X = genX` of the two-maps construction and its three conditions
  (`lift_genX_pow`, `lift_genX_Wt_one`, `lift_genX_coverClassAt`, all from the telescoping along the
  walks of `u` and of `Wt 1`);

`Work.OROneRel.magnusDomainDatum_of_windowInverse` then produces the `Z`-domain datum, and the
proved `Work.OROneRel.magnus_step_root_no_eps_zero_of_domainDatum` produces the target.

So the residual of `Work.OROneRel.magnusStepCase2` is exactly: **the pin and its consistency** for
the window of `Work.OROneRel.exists_winWindowData` (plus the Freiheitssatz plank `hA` and the
aperiodicity/norm bounds, which are proved elsewhere).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The `Z`-domain datum of the residual case from the pin.** -/
noncomputable def magnusDomainDatum_of_pin (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) {c : α → ℤ}
    (Wt : ℤ → FreeGroup α) (lo hi : ℤ)
    (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
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
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin))
    (A : Subgroup (winHd Wt c lo hi u l)) (ψ : A ≃* A)
    (hψ : ∀ a : A, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1) *
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (a : winHd Wt c lo hi u l) =
      Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (ψ a : winHd Wt c lo hi u l) *
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1))
    (Q : ℤ → winHd Wt c lo hi u l)
    (hQ : ∀ j : ℤ, Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin (Q j) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt j * (Wt 1) ^ (-j)))
    (hcons : ∀ (x : α) (i j : ℤ), (x, i) ∈ Work.OROneRel.winE c lo hi →
      (x, j) ∈ Work.OROneRel.winE c lo hi →
      (levelEl (A := A) (ψ := ψ) Q i)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, i) *
          levelEl (A := A) (ψ := ψ) Q (i + c x) =
        (levelEl (A := A) (ψ := ψ) Q j)⁻¹ * winGammaK Wt c lo hi u l A ψ (x, j) *
          levelEl (A := A) (ψ := ψ) Q (j + c x)) :
    MagnusDomainDatum u l := by
  classical
  -- the pin at the levels `0` and `1`
  have hQ0 : Q 0 = 1 := by
    apply hθ
    have h1 : Wt 0 * (Wt 1) ^ (-(0 : ℤ)) = 1 := by
      rw [hW0, one_mul]
      exact zpow_zero (Wt 1)
    rw [hQ 0, map_one, h1, map_one]
  have hQ1 : Q 1 = 1 := by
    apply hθ
    have h1 : Wt 1 * (Wt 1) ^ (-(1 : ℤ)) = 1 := by
      rw [zpow_neg_one, mul_inv_cancel]
    rw [hQ 1, map_one, h1, map_one]
  -- the level factors are in the vertex
  have hpin : ∀ i : ℤ, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt i) *
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) ^ (-i) ∈
      Work.OROneRel.winVertex Wt c lo hi u l := by
    intro i
    have h := hQ i
    rw [map_mul, map_zpow] at h
    rw [← h,
      show Work.OROneRel.winVertex Wt c lo hi u l =
          (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range from
        (Work.OROneRel.winTheta_range Wt c lo hi u l hW0 hcu hwin).symm]
    exact ⟨Q i, rfl⟩
  -- generation
  have hgen : (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Wt 1)) = ⊤ := by
    rw [Work.OROneRel.winTheta_range Wt c lo hi u l hW0 hcu hwin, Subgroup.zpowers_eq_closure]
    exact Work.OROneRel.winVertex_generation_of_pin u l hl c (Wt 1) Wt lo hi hcu hcov hpin
  exact magnusDomainDatum_of_windowInverse u l Wt lo hi (Wt 1) hW0 hcu (hcoh 1) hwin hppv hnorm
    hA hθ A ψ hψ hgen (genX (A := A) (ψ := ψ) hcov Q)
    (lift_genX_pow (A := A) (ψ := ψ) hcu hwin hcov Q hQ0 hcons)
    (lift_genX_Wt_one (A := A) (ψ := ψ) hcov Q hQ0 hQ1 hcons hcoh htree hlo1 hhi1)
    (fun e => lift_genX_coverClassAt (A := A) (ψ := ψ) hcov Q hQ0 hcons hcoh htree e)

end Work.OROneRel
