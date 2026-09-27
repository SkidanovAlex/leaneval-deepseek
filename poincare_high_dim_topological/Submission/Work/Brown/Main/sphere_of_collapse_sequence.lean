import Mathlib
import Submission.Work.Brown.Basic
import Submission.Work.Brown.Cell.isOpenCell_compl_point_sphere
import Submission.Work.Brown.Main.nonempty_homeomorph_compl_image
import Submission.Work.Brown.Main.nearHomeo_of_collapse
import Submission.Work.Brown.Main.nonempty_homeomorph_of_collapse_sequence

/-!
# The sphere from a collapse sequence

If a compact Hausdorff space `Z` is collapsed onto `𝕊ⁿ` by a sequence of maps `q k` whose unique
non-trivial fibre is a decreasing sequence `F k` of closed sets with `⋂ k, F k = {z₀}`, then
`Z ≃ₜ 𝕊ⁿ`.

This is the engine of Uspenskij's proof of Brown's monotone union theorem
(`Work.Brown.Engine.sphere_of_collapse_sequence`), assembled here from the two pieces of the
`Main` area that are free of invariance-of-domain input:

* `Work.Brown.Main.nonempty_homeomorph_of_collapse_sequence`: `Z` is the inverse limit of the
  induced bonding maps `g k : 𝕊ⁿ → 𝕊ⁿ` (`g k ∘ q (k+1) = q k`), and the inverse limit of a
  sequence of near homeomorphisms of `𝕊ⁿ` is `𝕊ⁿ` (Morton Brown);
* `Work.Brown.Main.nearHomeo_of_collapse_compl_openCell`: each `g k` is a near homeomorphism,
  because its unique non-trivial fibre is `q (k+1) '' F k`, a closed set whose complement is an
  open `n`-cell (`Work.Brown.Main.nonempty_homeomorph_compl_image` plus the fact that `𝕊ⁿ` minus
  a point is an open cell, `Work.Brown.Cell.isOpenCell_compl_point_sphere`).

Compared with the `Engine` version, no cellularity (`IsCellular`) and hence no topological
invariance of domain is used: the shrinking input is
`Work.Brown.Main.exists_homeomorph_shrink_compl_openCell`.
-/

namespace Work.Brown.Main

open Set Metric Function

theorem sphere_of_collapse_sequence {n : ℕ} {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [T2Space Z] {F : ℕ → Set Z} (hcl : ∀ k, IsClosed (F k)) (hanti : Antitone F) {z₀ : Z}
    (hint : (⋂ k, F k) = {z₀})
    (hq : ∀ k, ∃ q : Z → ↥(Metric.sphere (0 : PL.E (n + 1)) 1), Continuous q ∧
      Function.Surjective q ∧ ∀ x y, q x = q y ↔ x = y ∨ (x ∈ F k ∧ y ∈ F k)) :
    Nonempty (Z ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) := by
  classical
  choose q hqc hqs hqf using hq
  have hzF : ∀ k, z₀ ∈ F k := fun k =>
    Set.mem_iInter.mp (by rw [hint]; exact Set.mem_singleton z₀) k
  -- the bonding maps of the collapse sequence
  let g : ℕ → ↥(Metric.sphere (0 : PL.E (n + 1)) 1) → ↥(Metric.sphere (0 : PL.E (n + 1)) 1) :=
    fun k y => q k (Classical.choose (hqs (k + 1) y))
  have hg_comp : ∀ k z, g k (q (k + 1) z) = q k z := by
    intro k z
    show q k (Classical.choose (hqs (k + 1) (q (k + 1) z))) = q k z
    have hspec : q (k + 1) (Classical.choose (hqs (k + 1) (q (k + 1) z))) = q (k + 1) z :=
      Classical.choose_spec (hqs (k + 1) (q (k + 1) z))
    rcases (hqf (k + 1) _ _).mp hspec with h | ⟨h1, h2⟩
    · rw [h]
    · exact (hqf k _ _).mpr (Or.inr ⟨hanti (Nat.le_succ k) h1, hanti (Nat.le_succ k) h2⟩)
  have hgc : ∀ k, Continuous (g k) := by
    intro k
    have hquot : Topology.IsQuotientMap (q (k + 1)) :=
      (hqc (k + 1)).isClosedMap.isQuotientMap (hqc (k + 1)) (hqs (k + 1))
    rw [hquot.continuous_iff]
    have hcomp : g k ∘ q (k + 1) = q k := funext fun z => hg_comp k z
    rw [hcomp]; exact hqc k
  have hgs : ∀ k, Function.Surjective (g k) := by
    intro k
    have hcomp : g k ∘ q (k + 1) = q k := funext fun z => hg_comp k z
    have h : Function.Surjective (g k ∘ q (k + 1)) := by rw [hcomp]; exact hqs k
    exact h.of_comp
  have hg_fiber : ∀ k (y y' : ↥(Metric.sphere (0 : PL.E (n + 1)) 1)),
      g k y = g k y' ↔ y = y' ∨
        (y ∈ q (k + 1) '' F k ∧ y' ∈ q (k + 1) '' F k) := by
    intro k y y'
    constructor
    · intro h
      obtain ⟨x, hx⟩ := hqs (k + 1) y
      obtain ⟨x', hx'⟩ := hqs (k + 1) y'
      have hy : g k y = q k x := hx ▸ hg_comp k x
      have hy' : g k y' = q k x' := hx' ▸ hg_comp k x'
      rw [hy, hy'] at h
      rcases (hqf k x x').mp h with h' | ⟨h1, h2⟩
      · left; rw [← hx, ← hx', h']
      · exact Or.inr ⟨⟨x, h1, hx⟩, ⟨x', h2, hx'⟩⟩
    · rintro (rfl | ⟨⟨x, hx, hxq⟩, ⟨x', hx', hx'q⟩⟩)
      · rfl
      · have hy : g k y = q k x := hxq ▸ hg_comp k x
        have hy' : g k y' = q k x' := hx'q ▸ hg_comp k x'
        rw [hy, hy']
        exact (hqf k x x').mpr (Or.inr ⟨hx, hx'⟩)
  have hK_closed : ∀ k, IsClosed (q (k + 1) '' F k) := fun k =>
    ((hcl k).isCompact.image (hqc (k + 1))).isClosed
  have hKne : ∀ k, (q (k + 1) '' F k).Nonempty := fun k => ⟨q (k + 1) z₀, z₀, hzF k, rfl⟩
  have hKcell : ∀ k, PL.IsOpenCell n ((q (k + 1) '' F k)ᶜ :
      Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) := by
    intro k
    refine ⟨(hK_closed k).isOpen_compl, ?_⟩
    -- the complement of the fibre is the complement of the image of `F k` under the collapse
    obtain ⟨h1⟩ := nonempty_homeomorph_compl_image (q (k + 1)) (hqc (k + 1)) (hqs (k + 1))
      (F k) (hcl k)
      (fun x hx y hy hxy => by
        rcases (hqf (k + 1) x y).mp hxy with h | ⟨hx', _⟩
        · exact h
        · exact absurd (hanti (Nat.le_succ k) hx') hx)
      (fun x hx a ha h => by
        rcases (hqf (k + 1) x a).mp h with h' | ⟨h', _⟩
        · exact hx (h' ▸ ha)
        · exact absurd (hanti (Nat.le_succ k) h') hx)
    obtain ⟨h2⟩ := nonempty_homeomorph_compl_image (q k) (hqc k) (hqs k) (F k) (hcl k)
      (fun x hx y hy hxy => by
        rcases (hqf k x y).mp hxy with h | ⟨hx', _⟩
        · exact h
        · exact absurd hx' hx)
      (fun x hx a ha h => by
        rcases (hqf k x a).mp h with h' | ⟨h', _⟩
        · exact hx (h' ▸ ha)
        · exact absurd h' hx)
    have hset : q k '' F k = {q k z₀} := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hqf k x z₀).mpr (Or.inr ⟨hx, hzF k⟩)
      · rintro rfl
        exact ⟨z₀, hzF k, rfl⟩
    have h3 : ↥((q k '' F k)ᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) ≃ₜ PL.E n :=
      (Homeomorph.setCongr (show (q k '' F k)ᶜ = ({q k z₀}ᶜ :
          Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) by rw [hset])).trans
        (Work.Brown.Cell.isOpenCell_compl_point_sphere (q k z₀)).2.some
    exact ⟨h1.symm.trans (h2.trans h3)⟩
  have hgnear : ∀ k, Work.Brown.IsNearHomeo (g k) := fun k =>
    nearHomeo_of_collapse_compl_openCell (g k) (hgc k) (hgs k) (hK_closed k) (hKne k)
      (hKcell k) (hg_fiber k)
  exact nonempty_homeomorph_of_collapse_sequence hint hqc hqs hqf hgc hg_comp hgnear

end Work.Brown.Main
