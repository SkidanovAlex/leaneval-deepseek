/-
# The Karrass--Solitar descent along the amalgam `K ∗_{⟨z ^ p⟩} ⟨z⟩`

Let `P = F(RootIdx α t)` be the free group obtained from `F(α)` by adjoining the letter
`z = rootLetter t`, let `K = (rootHom t p).range = ⟨z ^ p, a (a ≠ t)⟩`, `⟨z⟩ = Subgroup.zpowers z`
and `C = ⟨z ^ p⟩`.  Then `C ≤ K`, `C ≤ ⟨z⟩` and `P` is the amalgam `K ∗_C ⟨z⟩`
(`Submission.Work.ORLocInd.CohenLyndon.rootAmaSetup` presents it as the pushout `Ama t p`, and
`rootAmaEquiv` identifies `P` with it).

The theorem `rootHom_descent` proved here is the descent step of the Karrass--Solitar argument:
if `M ∈ K` is conjugated into `K` by an element `g ∉ K`, then `M` is conjugate *within* `K` into
the edge subgroup `C`.

The proof is the standard fixed point argument on the Bass--Serre tree of the amalgam: `M` fixes
the `K`-leaf of the star tree, `g M g⁻¹ ∈ K` makes it fix a second leaf, and an element of a group
acting on a tree which fixes two distinct vertices fixes an edge, whence it lies in a conjugate of
the edge group; since the first edge at the `K`-leaf is labelled by an element of the `K`-vertex,
the conjugate is by an element of `K`.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.rootHomConjCriterion
import Submission.Work.ORLocInd.CohenLyndon.rootAmaSetup
import Submission.Work.ORLocInd.CohenLyndon.rootAmaEquiv
import Submission.Work.ORLocInd.CohenLyndon.pushoutStarTreeDescent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

universe u

namespace Work.ORLocInd.CohenLyndon

/-- **The Karrass--Solitar descent along the amalgam `K ∗_{⟨z ^ p⟩} ⟨z⟩`.**  An element `M` of
`K = (rootHom t p).range` which is conjugated into `K` by an element `g ∉ K` is conjugate *within*
`K` into the edge subgroup `⟨z ^ p⟩`. -/
theorem rootHom_descent {α : Type u} [DecidableEq α] {t : α} {p : ℤ} (hp : p ≠ 0)
    {g M : FreeGroup (Work.ORLocInd.CohenLyndon.RootIdx α t)}
    (hM : M ∈ (Work.ORLocInd.CohenLyndon.rootHom t p).range)
    (hg : g ∉ (Work.ORLocInd.CohenLyndon.rootHom t p).range)
    (h : g * M * g⁻¹ ∈ (Work.ORLocInd.CohenLyndon.rootHom t p).range) :
    ∃ Q ∈ (Work.ORLocInd.CohenLyndon.rootHom t p).range,
      Q * M * Q⁻¹ ∈ Subgroup.zpowers (Work.ORLocInd.CohenLyndon.rootLetter t ^ p) := by
  classical
  -- the isomorphism `P ≃* K ∗_{⟨z ^ p⟩} ⟨z⟩` and its behaviour on `K` and on `⟨z ^ p⟩`
  obtain ⟨Φ, hΦK, hΦC⟩ := rootAmaEquiv t p
  -- the hypotheses, transported to the amalgam
  have hMK : Φ M ∈ Ama.subK t p := by
    rw [hΦK M hM]
    exact ⟨⟨M, hM⟩, rfl⟩
  have hconj : Φ g * Φ M * (Φ g)⁻¹ ∈ Ama.subK t p := by
    have heq : Φ (g * M * g⁻¹) = Φ g * Φ M * (Φ g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← heq, hΦK (g * M * g⁻¹) h]
    exact ⟨⟨g * M * g⁻¹, h⟩, rfl⟩
  have hgK : Φ g ∉ Ama.subK t p := by
    rintro ⟨y, hy⟩
    refine hg ?_
    have h1 : Φ (y : FreeGroup (RootIdx α t)) = Φ g := by
      rw [hΦK (y : FreeGroup (RootIdx α t)) y.2, hy]
    have h2 : (y : FreeGroup (RootIdx α t)) = g := Φ.injective h1
    rw [← h2]
    exact y.2
  -- the Bass--Serre descent on the star tree of the pushout
  obtain ⟨k, hk⟩ := @pushoutStarTreeDescent RootAmaIdx _ ↥(rootC t p) (RootAmaG t p) _ _
    (amaPhi t p) RootAmaIdx.vK (Φ M) (Φ g) hMK hconj hgK
  -- translate the conclusion back along `Φ`
  obtain ⟨c, hc⟩ := hk
  refine ⟨(k : FreeGroup (RootIdx α t)), k.2, ?_⟩
  have hkey : Φ ((k : FreeGroup (RootIdx α t)) * M * (k : FreeGroup (RootIdx α t))⁻¹) =
      Ama.base t p c := by
    rw [map_mul, map_mul, map_inv, hΦK (k : FreeGroup (RootIdx α t)) k.2]
    exact hc.symm
  have hkey' : Φ ((k : FreeGroup (RootIdx α t)) * M * (k : FreeGroup (RootIdx α t))⁻¹) =
      Φ (c : FreeGroup (RootIdx α t)) := by
    rw [hkey, hΦC (c : FreeGroup (RootIdx α t)) c.2]
  have hfin : (k : FreeGroup (RootIdx α t)) * M * (k : FreeGroup (RootIdx α t))⁻¹ =
      (c : FreeGroup (RootIdx α t)) := Φ.injective hkey'
  rw [hfin]
  exact c.2

end Work.ORLocInd.CohenLyndon
