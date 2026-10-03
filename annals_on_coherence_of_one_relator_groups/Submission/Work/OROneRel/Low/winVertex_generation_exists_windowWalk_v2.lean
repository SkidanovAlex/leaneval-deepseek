import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.magnusCaseDefs

namespace Work.OROneRel

namespace Low

universe u

set_option maxHeartbeats 1000000

/-- **The generation in `G = ⟨α | u ^ l⟩` from the generation in the free group.**  If the window
vertex of the free group, `(winRho Wt c lo hi).range`, together with the class of a deck element `τ`
generates `F α`, then the image vertex `winVertex Wt c lo hi u l = (winRho).range.map mk` together
with the class of `τ` in `G = ⟨α | u ^ l⟩` generates `G`.  This is the transport of a free-group
generation statement to the one-relator group, along the surjection
`PresentedGroup.mk {u ^ l} : F α →* G`. -/
theorem sup_zpowers_of_freeGeneration_local {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (τ : FreeGroup α)
    (h : (Work.OROneRel.winRho Wt c lo hi).range ⊔ Subgroup.zpowers τ = ⊤) :
    winVertex Wt c lo hi u l ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = ⊤ := by
  have hmap : Subgroup.map (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
      ((Work.OROneRel.winRho Wt c lo hi).range ⊔ Subgroup.zpowers τ) = ⊤ := by
    rw [h, Subgroup.map_top_of_surjective _ (PresentedGroup.mk_surjective _)]
  have hsplit : Subgroup.map (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
      ((Work.OROneRel.winRho Wt c lo hi).range ⊔ Subgroup.zpowers τ)
      = winVertex Wt c lo hi u l ⊔
        Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) := by
    rw [Subgroup.map_sup, winVertex]
    congr 1
    exact MonoidHom.map_zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) τ
  rw [← hsplit, hmap]

theorem winVertex_generation_exists_windowWalk_v2 {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    (hnd : ∀ (t : α) (c : α → ℤ), t ∈ Work.OROneRel.relatorLetters u → c t = 1 →
      Work.OROneRel.cohom c u ≠ 1)
    (hnlo : ∀ (x : α) (b : Bool), (FreeGroup.toWord u).count (x, b) = 1 →
      (FreeGroup.toWord u).count (x, Bool.not b) ≠ 0)
    (hocc : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u)
    (hnfk : ¬ Work.OROneRel.FreeKernelCase u l)
    (hnc : ¬ Work.OROneRel.NielsenCountCase u)
    {c : α → ℤ} (hcu : Work.OROneRel.cohom c u = 1)
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlast : ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) :
    ∃ τ : FreeGroup α, Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1 ∧
      (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf τ),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) ∧
      winVertex Wt c lo hi u l ⊔
        Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = ⊤ := by
  sorry

end Low

end Work.OROneRel
