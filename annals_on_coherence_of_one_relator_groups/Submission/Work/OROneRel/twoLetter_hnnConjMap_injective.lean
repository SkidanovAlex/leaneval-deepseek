import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.hnnConjMap_deckChange
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.tlWin_pq_eq_tlH
import Submission.Work.OROneRel.tlWin_deckClimb
import Submission.Work.OROneRel.exists_short_deck_with_deck_mem
import Submission.Work.OROneRel.tlWin_succ_of_walk_le
import Submission.Work.OROneRel.hnnConjMap_injective_tlWin_bottom
import Submission.Work.OROneRel.twoLetter_target_of_F2crux

/-!
# Injectivity of the comparison map of the two-letter band window

The target `Work.OROneRel.twoLetter_hnnConjMap_injective` states that, for the two-letter relator
`u = tlU p q = a ^ p * b ^ q` (coprime exponents), the band window `[0, pq]` of the weight
`tlW p q` (`a ↦ q`, `b ↦ -p`), and the low deck element `τ = tlLowTau p q`, the canonical comparison
map

  `hnnConjMap H τG : HNN(↥H, H ⊓ τG⁻¹HτG, τG (H ⊓ τG⁻¹HτG) τG⁻¹, conj_{τG}) →* G`

of the pair `(H, τG)` -- where `H = winVertex Wt c 0 (pq) u l` is the vertex and `τG = mk τ` -- is
injective, as soon as the vertex Freiheitssatz `hA` (the identification of `↥H` with the one-relator
group `⟨winBeta | winRoot ^ l⟩`) and the generation plank `hgen` (`H ⊔ ⟪τG⟫ = ⊤`) hold.

## The proof, and the three inputs it rests on

The whole content is the `F₂`-level crux `Work.OROneRel.band_hnnConjMap_injective`: injectivity of
`hnnConjMap (tlH p q Wt) (tlLowTau p q)` inside the free group `F₂ = ⟨a,b⟩`, where
`tlH p q Wt = (winRho Wt (tlW p q) 0 (p*q)).range = π₁` of the band graph of the `ℤ`-cover.  It is
reached here through the following steps, all of them proved in this workspace.

* **The deck change** (`hnnConjMap_deckChange`, and `band_hnnConjMap_injective_congr_of_mul_mem`
  below).  For any group `G`, subgroup `H ≤ G` and `τ = γ * σ` with `γ ∈ H`, the canonical
  comparison maps of the pairs `(H, τ)` and `(H, σ)` are *simultaneously injective*.  For the band
  this removes the obstruction recorded in
  `Submission/Work/OROneRel/NOTES_twoLetter_hnnConjMap_freeRank2.md` §9: the opaque low deck element
  `tlLowTau p q = (twoLetterLowTauBound …).choose` may be replaced by *any* `σ` with
  `tlLowTau * σ⁻¹ ∈ tlH`, in particular by one whose walk is confined to the short window
  `[0,p+q-1]`.

* **The window climb** (`tlWin_succ_of_walk_le`, delegated and proved).  For every element `σ` of
  weight one whose walk lies in the window `[0,m]`, `m ≥ p+q-1`, the window groups satisfy
  `tlWin p q (m+1) = tlWin p q m ⊔ σ · tlWin p q m · σ⁻¹`.  (The "≤" half is van Kampen for the
  union `Y[0,m+1] = Y[0,m] ∪ Y[1,m+1]` with the basepoint at level `1`; the "≥" half is the walk
  computation.)  The walk hypothesis is *necessary*: for the opaque `tlLowTau` at `(3,4)`, `m = 8`
  it fails.

* **The bottom case** (`hnnConjMap_injective_tlWin_bottom`, delegated and proved): the window
  `[0,p+q-1]` is a cycle, so the bottom vertex is cyclic, and the HNN extension of a cyclic group
  is two-generated, which gives the injectivity at the bottom by
  `Work.OROneRel.hnnConjMap_injective_of_two_generated`.

* **The short deck element** (`exists_short_deck_with_deck_mem`, delegated and proved): `σ` of weight
  one with walk in `[0,p+q-1]` and `tlLowTau * σ⁻¹ ∈ tlWin p q (p*q)` exists.  Both halves are
  *walk* statements, so nothing here inspects the value of the `Classical.choose`.

* **The passage to the target** (`twoLetter_target_of_F2crux`, delegated and proved): the `F₂`-level
  crux plus the (proved) generation plank `tlH ⊔ ⟪tlLowTau⟫ = ⊤` of
  `Work.OROneRel.twoLetter_F2_generation` make the Bass--Serre coset graph
  `GradedHNN.Coset (tlH p q Wt) (tlLowTau p q)` a tree
  (`Work.OROneRel.isTree_coset_of_hnnConjMap_injective`); the quotient of that tree by
  `N = ⟪⟪u^l⟫⟫` is a `G`-tree with vertex stabiliser `winVertex = tlH · N/N`
  (`Work.OROneRel.twoLetter_treeData_of_F2treeData`), and
  `Work.OROneRel.hnnConjMap_injective_of_treeData` gives the injectivity.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

/-! ## §1 The deck change at the level of the band vertex -/

/-- **The deck change for the band vertex.**  If `σ` is another element of `F₂` with
`tlLowTau p q * σ⁻¹ ∈ tlH p q Wt`, then the `F₂`-level crux for `σ` is equivalent to the one for
the low deck element. -/
theorem band_hnnConjMap_injective_congr_of_mul_mem (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) {Wt : ℤ → FreeGroup (Fin 2)} {σ : FreeGroup (Fin 2)}
    (h : tlLowTau p q hp hq hcop * σ⁻¹ ∈ tlH p q Wt) :
    Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop)) ↔
      Function.Injective (hnnConjMap (tlH p q Wt) σ) :=
  hnnConjMap_injective_iff_mul_left (H := tlH p q Wt)
    (τ := tlLowTau p q hp hq hcop) (σ := σ) (γ := tlLowTau p q hp hq hcop * σ⁻¹) h
    (by rw [mul_assoc, inv_mul_cancel, mul_one])

/-! ## §2 The assembly of the target -/

/-- `winE` is monotone in the upper bound. -/
theorem winE_mono_hi {α : Type*} {c : α → ℤ} {lo hi hi' : ℤ} (h : hi ≤ hi') :
    winE c lo hi ⊆ winE c lo hi' := by
  intro e he
  rw [mem_winE] at he ⊢
  exact ⟨he.1, le_trans he.2.1 h, he.2.2.1, le_trans he.2.2.2 h⟩

/-- **The two-letter target.**  Assembled from the deck change, the window climb with the explicit
short deck element, the cyclic bottom case and the coset-tree descent. -/
theorem twoLetter_hnnConjMap_injective (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))),
      Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)) x ∈
          Subgroup.normalClosure ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
              (Work.OROneRel.tlU p q) ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt (Work.OROneRel.tlW p q) 0
              ((p : ℤ) * (q : ℤ))))))
    (hgen : Work.OROneRel.winVertex Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
        (Work.OROneRel.tlU p q) l ⊔
      Subgroup.closure (singleton (PresentedGroup.mk ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (Work.OROneRel.tlLowTau p q hp hq hcop))) = ⊤) :
    Function.Injective (Work.OROneRel.hnnConjMap
      (Work.OROneRel.winVertex Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))
        (Work.OROneRel.tlU p q) l)
      (PresentedGroup.mk ({Work.OROneRel.tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (Work.OROneRel.tlLowTau p q hp hq hcop))) := by
  classical
  obtain ⟨σ, hσcoh, hσwalk, hdeck⟩ := exists_short_deck_with_deck_mem p q hp hq hcop
  -- the climb, with the walk hypothesis at every window from `p+q-1` up to `p*q`
  have hrec : ∀ m : ℤ, ((p : ℤ) + (q : ℤ) - 1) ≤ m → m + 1 ≤ (p : ℤ) * (q : ℤ) →
      tlWin p q (m + 1) = tlWin p q m ⊔ (tlWin p q m).map (MulAut.conj σ) := by
    intro m hm1 hm2
    refine tlWin_succ_of_walk_le p q hp hq hcop hm1 hm2 hσcoh ?_
    intro e he
    exact winE_mono_hi (by linarith : ((p : ℤ) + (q : ℤ) - 1) ≤ m) (hσwalk e he)
  have hbot : Function.Injective (hnnConjMap (tlWin p q ((p : ℤ) + (q : ℤ) - 1)) σ) :=
    hnnConjMap_injective_tlWin_bottom p q hp hq hcop hσcoh
  have htop : tlWin p q ((p : ℤ) * (q : ℤ)) = tlH p q Wt :=
    tlWin_pq_eq_tlH p q hp hq hcop Wt hW0 hcoh hwin htree
  have hcrux : Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q hp hq hcop)) :=
    band_hnnConjMap_injective_of_shortDeck p q hp hq (Wt := Wt) (σ := σ) hrec hbot hdeck htop
  exact twoLetter_target_of_F2crux p q l hp hq hl hcop Wt hW0 hcoh hwin htree hA hgen hcrux

end Work.OROneRel
