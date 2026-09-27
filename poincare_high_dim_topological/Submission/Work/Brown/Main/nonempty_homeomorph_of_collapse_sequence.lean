import Mathlib
import Submission.Work.Brown.Basic
import Submission.Work.Brown.Engine.brown_inverseLimit

namespace Work.Brown.Main

open Set Function Metric
open scoped Topology

/-- Auxiliary: the sphere `𝕊ⁿ` is nonempty. -/
theorem sphere_nonempty_aux (n : ℕ) :
    (Metric.sphere (0 : PL.E (n + 1)) 1).Nonempty :=
  ⟨EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), by simp⟩

/-- **Collapse sequences give a homeomorphism with the sphere.**

Let `Z` be a compact Hausdorff space and `F k` a sequence of subsets with
`⋂ k, F k = {z₀}`.  Suppose `q k : Z → 𝕊ⁿ` are continuous surjections whose only non-trivial
fibre is `F k` (i.e. `q k x = q k y ↔ x = y ∨ (x, y ∈ F k)`), and let `g k : 𝕊ⁿ → 𝕊ⁿ` be
continuous near homeomorphisms with `g k ∘ q (k+1) = q k`.  Then `Z ≃ₜ 𝕊ⁿ`.

Indeed `z ↦ (q k z)_k` is a homeomorphism of `Z` onto the inverse limit of the tower
`𝕊ⁿ ←g 0– 𝕊ⁿ ←g 1– ⋯` (injectivity is the shrinking of the fibres to `{z₀}`, surjectivity is
the finite intersection property for the nested closed sets `q k ⁻¹' {x k}`), and the inverse
limit of a sequence of near homeomorphisms of a compact metric space is the space itself
(Morton Brown, `Work.Brown.Engine.brown_inverseLimit`). -/
theorem nonempty_homeomorph_of_collapse_sequence {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] [T2Space Z] {F : ℕ → Set Z} {z₀ : Z} (hint : (⋂ k, F k) = {z₀})
    {q : ℕ → Z → ↥(Metric.sphere (0 : PL.E (n + 1)) 1)} (hqc : ∀ k, Continuous (q k))
    (hqs : ∀ k, Function.Surjective (q k))
    (hqf : ∀ k, ∀ x y, q k x = q k y ↔ x = y ∨ (x ∈ F k ∧ y ∈ F k))
    {g : ℕ → (↥(Metric.sphere (0 : PL.E (n + 1)) 1) → ↥(Metric.sphere (0 : PL.E (n + 1)) 1))}
    (hgc : ∀ k, Continuous (g k)) (hg : ∀ k z, g k (q (k + 1) z) = q k z)
    (hgn : ∀ k, Work.Brown.IsNearHomeo (g k)) :
    Nonempty (Z ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) := by
  classical
  -- the bonding maps `g k` are surjective
  have hgsurj : ∀ k, Function.Surjective (g k) := by
    intro k
    have hcomp : g k ∘ q (k + 1) = q k := funext fun z => hg k z
    have : Function.Surjective (g k ∘ q (k + 1)) := by rw [hcomp]; exact hqs k
    exact this.of_comp
  -- `Z` is nonempty (it surjects onto the nonempty sphere)
  have hneZ : Nonempty Z := by
    obtain ⟨y, hy⟩ := sphere_nonempty_aux n
    obtain ⟨z, -⟩ := hqs 0 ⟨y, hy⟩
    exact ⟨z⟩
  -- the canonical map from `Z` to the inverse limit of the `g`-system
  let φ : Z → {x : ℕ → ↥(Metric.sphere (0 : PL.E (n + 1)) 1) //
      ∀ k, g k (x (k + 1)) = x k} :=
    fun z => ⟨fun k => q k z, fun k => hg k z⟩
  have hφcont : Continuous φ :=
    Continuous.subtype_mk (continuous_pi fun k => hqc k) (fun z => fun k => hg k z)
  have hφinj : Function.Injective φ := by
    intro z z' h
    have hk : ∀ k, q k z = q k z' := fun k => congrFun (congrArg Subtype.val h) k
    by_contra hne
    have hF : ∀ k, z ∈ F k ∧ z' ∈ F k := fun k => by
      rcases (hqf k z z').mp (hk k) with h' | h'
      · exact absurd h' hne
      · exact h'
    have hz : z = z₀ := by
      have hmem : z ∈ ⋂ k, F k := Set.mem_iInter.mpr fun k => (hF k).1
      rw [hint] at hmem; exact hmem
    have hz' : z' = z₀ := by
      have hmem : z' ∈ ⋂ k, F k := Set.mem_iInter.mpr fun k => (hF k).2
      rw [hint] at hmem; exact hmem
    exact hne (hz.trans hz'.symm)
  have hφsurj : Function.Surjective φ := by
    intro x
    -- the closed sets `q k ⁻¹' {x k}` are nested
    have hstep : ∀ j, {z : Z | q (j + 1) z = x.1 (j + 1)} ⊆ {z : Z | q j z = x.1 j} := by
      intro j z hz
      change q (j + 1) z = x.1 (j + 1) at hz
      change q j z = x.1 j
      rw [← hg j z, hz, x.2 j]
    have hnest : ∀ ⦃i j : ℕ⦄, i ≤ j →
        {z : Z | q j z = x.1 j} ⊆ {z : Z | q i z = x.1 i} := by
      intro i j hij
      exact Nat.le_induction
        (P := fun m _ => {z : Z | q m z = x.1 m} ⊆ {z : Z | q i z = x.1 i})
        subset_rfl (fun k _ ih => (hstep k).trans ih) j hij
    have hne : ∀ u : Finset ℕ, (⋂ i ∈ u, {z : Z | q i z = x.1 i}).Nonempty := by
      intro u
      rcases u.eq_empty_or_nonempty with rfl | hu
      · exact ⟨Classical.choice hneZ, by simp⟩
      · obtain ⟨z, hz⟩ := hqs (u.sup id) (x.1 (u.sup id))
        exact ⟨z, Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi =>
          hnest (Finset.le_sup (f := id) hi) hz⟩
    have hclosed : ∀ i : ℕ, IsClosed {z : Z | q i z = x.1 i} :=
      fun i => isClosed_eq (hqc i) continuous_const
    obtain ⟨z, hz⟩ := IsCompact.inter_iInter_nonempty isCompact_univ
      (fun i => {z : Z | q i z = x.1 i}) hclosed (fun u => by simpa using hne u)
    refine ⟨z, Subtype.ext ?_⟩
    funext k
    exact Set.mem_iInter.mp (Set.mem_of_mem_inter_right hz) k
  -- the inverse limit of the `g`-system is the sphere
  have hlim : Nonempty ({x : ℕ → ↥(Metric.sphere (0 : PL.E (n + 1)) 1) //
      ∀ k, g k (x (k + 1)) = x k} ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) :=
    Work.Brown.Engine.brown_inverseLimit g hgc hgn
  -- assemble: `Z ≃ₜ` inverse limit `≃ₜ 𝕊ⁿ`
  let e : Z ≃ {x : ℕ → ↥(Metric.sphere (0 : PL.E (n + 1)) 1) //
      ∀ k, g k (x (k + 1)) = x k} := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have he : Continuous (e : Z → _) := by
    rw [show (e : Z → _) = φ from funext fun z => Equiv.ofBijective_apply _ _ z]
    exact hφcont
  let H1 : Z ≃ₜ {x : ℕ → ↥(Metric.sphere (0 : PL.E (n + 1)) 1) //
      ∀ k, g k (x (k + 1)) = x k} := Continuous.homeoOfEquivCompactToT2 he
  exact ⟨H1.trans hlim.some⟩

end Work.Brown.Main
