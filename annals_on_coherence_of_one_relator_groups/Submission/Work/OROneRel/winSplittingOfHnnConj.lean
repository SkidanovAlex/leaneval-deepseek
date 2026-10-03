/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The `Z`-domain splitting of `⟨α | u ^ l⟩`, in the pair form `(H, τ)`, from the gate injections

This file restates the *splitting* plank (`Work.OROneRel.winVertexSplits`, the (B) plank of
`Submission/Work/OROneRel/winAssembly.lean`) in the sharp form isolated by
`Submission/Work/OROneRel/hnnConjSplit.lean`, namely as the **injectivity of the canonical comparison
map**

  `hnnConjMap (winVertex Wt c lo hi u l) (PresentedGroup.mk ({u ^ l}) τ) : HNN(↥H, A, B, φ) →* G`,

where `H = winVertex …` is the image of the vertex in `G = ⟨α | u ^ l⟩` and the associated subgroups
are the *maximal* ones `A = H ⊓ τ⁻¹Hτ`, `B = τ A τ⁻¹` with `φ = conj_τ`.  All the HNN bookkeeping is
then already proved in `hnnConjSplit.lean` (`hnnConjMap_bijective`), so this is the *only* remaining
content of (B) — the Britton/normal-form input, which Linton's Proposition 2.2.19
(*One-relator hierarchies*, arXiv 2202.11324) supplies from the **π₁-injectivity of the gates**
`D ∩ t^{±1}D → D`.

Two consequences of the restatement are proved here (they are pure bookkeeping, and they are what
makes the sharp form *usable*):

* `winVertexSplitting_of_hnnConjMap` -- the injectivity plus the *generation*
  `winVertex ⊔ ⟨mk τ⟩ = ⊤` gives **the splitting as data**, in exactly the shape consumed by
  `Work.OROneRel.magnusDomainDatum_of_winData` (`e : HNN(↥H, A, B, φ) ≃* G` with `of ↦ of` and
  `t ↦ mk τ`);
* `magnusDomainDatum_of_hnnConjMap` -- hence the whole `Z`-domain datum follows from
  **(A)** (the Freiheitssatz of the window, used only for the *vertex identification*
  `⟨β | v ^ l⟩ ≃* ↥H`), **(B)** in the pair form, the generation plank, and the root data.

The point of the restatement is that **(B) no longer mentions the window Freiheitssatz**: its
geometric hypothesis is the gate injection, which is a strictly weaker input (it is *implied* by (A)
together with the proved `Work.OROneRel.winGateFreiheitssatz` and the non-degeneracy witness
`Work.OROneRel.winRoot_letter_notMem_gate`), and it is independent of (A) as a statement, so it can
be attacked on its own -- which is what this file sets up.

The remaining piece — the injectivity itself, from the gate injections — is the target
`Work.OROneRel.winHnnConjMap_injective_of_gateInjective`, stated in its own module (so that its prover
does not have to import this file):
`WinGateInjective Wt c lo hi u l (winGateBelow c lo hi) … → WinGateInjective … (winGateAbove c lo hi) …
→ Function.Injective (hnnConjMap (winVertex Wt c lo hi u l) (PresentedGroup.mk ({u ^ l}) τ))`.
-/
import Mathlib
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.winGateDefs
import Submission.Work.OROneRel.winGateClassDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The splitting as data, from the pair form

`hnnConjSplit.lean` proves that the canonical comparison map `hnnConjMap H τ` is an isomorphism as
soon as it is injective and `H` together with `τ` generates.  Here that is packaged in exactly the
shape consumed by `magnusDomainDatum_of_winData`. -/

/-- **The window splitting in the `(H, τ)` pair form.**  If the canonical comparison map
`HNN(↥H, H ⊓ τ⁻¹Hτ, τ(H ⊓ τ⁻¹Hτ)τ⁻¹, conj_τ) →* G` is injective and `H` together with `τ` generates
`G`, then the splitting data over `H = winVertex` is available: an isomorphism which is the identity
on `↥H` and sends the stable letter to `mk τ`.

This is the exact shape of the `(B)` input of `Work.OROneRel.magnusDomainDatum_of_winData`. -/
theorem winVertexSplitting_of_hnnConjMap {u : FreeGroup α} {l : ℕ} {c : α → ℤ}
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} {τ : FreeGroup α}
    (hinj : Function.Injective (hnnConjMap (winVertex Wt c lo hi u l)
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ)))
    (hgen : winVertex Wt c lo hi u l ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = ⊤) :
    ∃ (A B : Subgroup ↥(winVertex Wt c lo hi u l)) (φ : A ≃* B)
      (e : HNNExtension ↥(winVertex Wt c lo hi u l) A B φ ≃*
        PresentedGroup ({u ^ l} : Set (FreeGroup α))),
      (∀ h : ↥(winVertex Wt c lo hi u l),
        e (HNNExtension.of h) = ((h : ↥(winVertex Wt c lo hi u l)) :
          PresentedGroup ({u ^ l} : Set (FreeGroup α)))) ∧
      e HNNExtension.t = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ := by
  classical
  set H := winVertex Wt c lo hi u l with hH
  set τG := PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ with hτG
  have hgen' : H ⊔ Subgroup.closure ({τG} : Set (PresentedGroup ({u ^ l} : Set (FreeGroup α)))) = ⊤ := by
    rw [Subgroup.zpowers_eq_closure] at hgen
    exact hgen
  have hbij := hnnConjMap_bijective H τG hinj hgen'
  refine ⟨_, _, _, MulEquiv.ofBijective (hnnConjMap H τG) hbij, ?_, ?_⟩
  · intro h
    rw [MulEquiv.ofBijective_apply]
    exact hnnConjMap_of H τG h
  · rw [MulEquiv.ofBijective_apply]
    exact hnnConjMap_t H τG

/-- **The `Z`-domain datum from the pair-form splitting.**  Given the window data, the root data
(`winRoot` aperiodic of smaller norm), **the Freiheitssatz (A)** — used only to identify the vertex
with the one-relator presentation `⟨β | winRoot ^ l⟩` — the *generation* plank, and **(B) in the pair
form** (the injectivity of the canonical comparison map), the datum of the residual holds.

Compared with `Work.OROneRel.magnusDomainDatum_of_winData` (whose `(B)` input `e` is taken as an
arbitrary HNN isomorphism) and with `Work.OROneRel.magnusDomainDatum_of_consistencyData` (whose `(B)`
input is the consistency of the coedge labels, *derived from* (A)), this version takes **(B) as the
single injectivity statement about the pair `(H, mk τ)`**, which does not mention (A). -/
noncomputable def magnusDomainDatum_of_hnnConjMap {u : FreeGroup α} {l : ℕ} {c : α → ℤ}
    (hcu : cohom c u = 1) {Wt : ℤ → FreeGroup α} {lo hi : ℤ} {τ : FreeGroup α}
    (hW0 : Wt 0 = 1)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi)
    (hτ : cohom c τ = Multiplicative.ofAdd 1)
    (hppv : ¬ IsProperPower (winRoot Wt c lo hi u))
    (hnorm : relatorNorm (winRoot Wt c lo hi u) < relatorNorm u)
    (hA : ∀ x : FreeGroup (winBeta Wt c lo hi),
      winRho Wt c lo hi x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt c lo hi u ^ l} : Set (FreeGroup (winBeta Wt c lo hi))))
    (hinj : Function.Injective (hnnConjMap (winVertex Wt c lo hi u l)
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ)))
    (hgen : winVertex Wt c lo hi u l ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = ⊤) :
    MagnusDomainDatum u l :=
  Classical.choice (by
    obtain ⟨A, B, φ, e, he_of, he_t⟩ := winVertexSplitting_of_hnnConjMap hinj hgen
    exact ⟨magnusDomainDatum_of_winData u l hcu Wt lo hi τ hW0 hwin hτ hppv hnorm hA A B φ e
      he_of he_t⟩)

end Work.OROneRel
