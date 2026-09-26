import Mathlib
import Submission.Work.Smooth.JordanSeparation.square_lemma_aux
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.OnePointLocallyConnected
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected
import Submission.Work.Smooth.SphereJordan.janiszewskiChain.IsPreconnectedComplComponentInSphere
/-! # Copy of `Submission/Work/Smooth/JordanSeparation/sphereJaniszewski_of_simplyConnected.lean` under the namespace `Work.Smooth.SphereJordan.Chain`

Duplicate of the team module `Submission/Work/Smooth/JordanSeparation/sphereJaniszewski_of_simplyConnected.lean`, with the import of
`Submission.Work.Smooth.SphereJordan.janiszewskiConnectedInter` replaced by the
namespace-local `...janiszewskiChain.DisjointPlane`, so that the chain can be imported
by `janiszewskiConnectedInter.lean` itself without an import cycle. -/


/-!
# Janiszewski's theorem on the sphere, from "complementary domains of continua are simply
connected"

This file proves the **Janiszewski crux** on the Riemann sphere `OnePoint ℂ`:

* `Work.Smooth.SphereJordan.Chain.janiszewski_of_simplyConnected`: if `K₁, K₂ ⊆ OnePoint ℂ` are
  closed, `K₁ ∩ K₂` is non-empty and preconnected, `x y ∉ K₁ ∪ K₂` lie in the same component both
  of `K₁ᶜ` and of `K₂ᶜ`, then they lie in the same component of `(K₁ ∪ K₂)ᶜ`.

The three mathematical inputs are taken as explicit hypotheses, so that this file is a pure
reduction:

* `hsc` — **every non-empty open preconnected subset of the sphere with preconnected complement is
  simply connected** (the classical theorem on complementary domains of continua; it fails on `ℂ`
  for *unbounded* domains, which is why the sphere formulation is the correct one);
* `hcomp` — **the complement of a complementary domain of a continuum is preconnected**;
* `hLP` — `LocallyPathConnectedSpace (OnePoint ℂ)`, so that components of open sets are path
  connected.

## Proof

Let `K = K₁ ∩ K₂` (compact, non-empty, preconnected) and `D` be the component of `x` in `Kᶜ`.
Since `D` is an open preconnected subset of the sphere with preconnected complement (`hcomp`), it is
simply connected (`hsc`).  The components `P = connectedComponentIn K₁ᶜ x`, `Q =
connectedComponentIn K₂ᶜ x` lie in `D` (they are preconnected, contain `x`, and avoid `K`), so we
may choose paths `α ⊆ P`, `β ⊆ Q` from `x` to `y`; both are paths in `D`, hence homotopic in `D` by
simple connectedness, giving a continuous `H : ℝ × ℝ → D ⊆ Kᶜ` with `H (0, ·) = α`, `H (1, ·) = β`,
`H (·, 0) = x`, `H (·, 1) = y`.  The square lemma applied to `S₁ = H⁻¹ K₁`, `S₂ = H⁻¹ K₂` (closed,
disjoint, with the four edge conditions) produces a preconnected `J` from `(0,0)` to `(0,1)` avoiding
`S₁ ∪ S₂`, and `H '' J ⊆ (K₁ ∪ K₂)ᶜ` is preconnected and contains `x` and `y`.
-/

namespace Work.Smooth.SphereJordan.Chain

open Set
open scoped OnePoint

noncomputable section

/-- **Janiszewski's theorem on the sphere, from simple connectedness of complementary domains.**

`hsc`, `hcomp` and `hLP` are the three classical inputs (see the module docstring); the conclusion
is Janiszewski's theorem for two closed subsets of `OnePoint ℂ` with preconnected intersection. -/
theorem janiszewski_of_simplyConnected
    (hsc : ∀ D : Set (OnePoint ℂ), IsOpen D → D.Nonempty → IsPreconnected D →
      IsPreconnected Dᶜ → IsSimplyConnected D)
    (hcomp : ∀ {K : Set (OnePoint ℂ)}, IsClosed K → K.Nonempty → IsPreconnected K →
      ∀ {x : OnePoint ℂ}, x ∉ K → IsPreconnected ((connectedComponentIn Kᶜ x)ᶜ))
    (hLP : LocallyPathConnectedSpace (OnePoint ℂ))
    {K₁ K₂ : Set (OnePoint ℂ)} (h₁ : IsClosed K₁) (h₂ : IsClosed K₂)
    (hne : (K₁ ∩ K₂).Nonempty) (hcon : IsPreconnected (K₁ ∩ K₂))
    {x y : OnePoint ℂ} (hx : x ∉ K₁ ∪ K₂) (hy : y ∉ K₁ ∪ K₂)
    (hc₁ : y ∈ connectedComponentIn K₁ᶜ x) (hc₂ : y ∈ connectedComponentIn K₂ᶜ x) :
    y ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ x := by
  classical
  haveI := hLP
  set K : Set (OnePoint ℂ) := K₁ ∩ K₂ with hKdef
  have hKcl : IsClosed K := h₁.inter h₂
  have hxK : x ∉ K := fun h => hx (Or.inl h.1)
  have hxKc : x ∈ Kᶜ := hxK
  -- the global component
  set D : Set (OnePoint ℂ) := connectedComponentIn Kᶜ x with hDdef
  have hDo : IsOpen D := by
    rw [hDdef]
    exact hKcl.isOpen_compl.connectedComponentIn
  have hxD : x ∈ D := by
    rw [hDdef]; exact mem_connectedComponentIn hxKc
  have hDne : D.Nonempty := ⟨x, hxD⟩
  have hDp : IsPreconnected D := by rw [hDdef]; exact isPreconnected_connectedComponentIn
  have hDc' : IsPreconnected Dᶜ := by
    rw [hDdef]
    exact hcomp hKcl hne hcon hxK
  have hDsub : D ⊆ Kᶜ := by rw [hDdef]; exact connectedComponentIn_subset _ _
  haveI : SimplyConnectedSpace D := hsc D hDo hDne hDp hDc'
  -- the two components
  have hxK₁ : x ∈ K₁ᶜ := fun h => hx (Or.inl h)
  have hxK₂ : x ∈ K₂ᶜ := fun h => hx (Or.inr h)
  have hPo : IsOpen (K₁ᶜ : Set (OnePoint ℂ)) := h₁.isOpen_compl
  have hQo : IsOpen (K₂ᶜ : Set (OnePoint ℂ)) := h₂.isOpen_compl
  -- `P ⊆ D` and `Q ⊆ D`
  have hPD : connectedComponentIn K₁ᶜ x ⊆ D := by
    rw [hDdef]
    exact (isPreconnected_connectedComponentIn (F := K₁ᶜ) (x := x)).subset_connectedComponentIn
      (mem_connectedComponentIn hxK₁)
      (fun z hz hzK => connectedComponentIn_subset K₁ᶜ x hz hzK.1)
  have hQD : connectedComponentIn K₂ᶜ x ⊆ D := by
    rw [hDdef]
    exact (isPreconnected_connectedComponentIn (F := K₂ᶜ) (x := x)).subset_connectedComponentIn
      (mem_connectedComponentIn hxK₂)
      (fun z hz hzK => connectedComponentIn_subset K₂ᶜ x hz hzK.2)
  -- paths inside `P` and `Q`
  obtain ⟨α, hα⟩ : JoinedIn (K₁ᶜ : Set (OnePoint ℂ)) x y :=
    Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn hPo hxK₁ hc₁
  obtain ⟨β, hβ⟩ : JoinedIn (K₂ᶜ : Set (OnePoint ℂ)) x y :=
    Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn hQo hxK₂ hc₂
  have hαrange : range α ⊆ (K₁ᶜ : Set (OnePoint ℂ)) := fun z hz => by
    obtain ⟨t, rfl⟩ := hz
    exact hα t
  have hβrange : range β ⊆ (K₂ᶜ : Set (OnePoint ℂ)) := fun z hz => by
    obtain ⟨t, rfl⟩ := hz
    exact hβ t
  have hαP : ∀ t, α t ∈ connectedComponentIn K₁ᶜ x := fun t =>
    (isPreconnected_range α.continuous).subset_connectedComponentIn
      ⟨0, α.source⟩ hαrange ⟨t, rfl⟩
  have hβP : ∀ t, β t ∈ connectedComponentIn K₂ᶜ x := fun t =>
    (isPreconnected_range β.continuous).subset_connectedComponentIn
      ⟨0, β.source⟩ hβrange ⟨t, rfl⟩
  have hαD : ∀ t, α t ∈ D := fun t => hPD (hαP t)
  have hβD : ∀ t, β t ∈ D := fun t => hQD (hβP t)
  have hyD : y ∈ D := α.target ▸ hαD 1
  -- lift to paths in the subtype `D`
  set αD : Path ⟨x, hxD⟩ ⟨y, hyD⟩ :=
    { toFun := fun t => ⟨α t, hαD t⟩
      continuous_toFun := Continuous.subtype_mk α.continuous hαD
      source' := Subtype.ext α.source
      target' := Subtype.ext α.target } with hαDdef
  set βD : Path ⟨x, hxD⟩ ⟨y, hyD⟩ :=
    { toFun := fun t => ⟨β t, hβD t⟩
      continuous_toFun := Continuous.subtype_mk β.continuous hβD
      source' := Subtype.ext β.source
      target' := Subtype.ext β.target } with hβDdef
  -- homotopy between them, from simple connectedness
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic αD βD
  -- the continuous map `H : ℝ × ℝ → OnePoint ℂ`
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set Hf : ℝ × ℝ → D := fun p =>
    F (Set.projIcc 0 1 h01 p.1, Set.projIcc 0 1 h01 p.2) with hHfdef
  have hHfc : Continuous Hf := by
    rw [hHfdef]
    fun_prop
  set H : ℝ × ℝ → OnePoint ℂ := fun p => (Hf p : OnePoint ℂ) with hHdef
  have hHc : Continuous H := by
    rw [hHdef]
    fun_prop
  -- the edge values of `H`
  have hproj0 : Set.projIcc 0 1 h01 (0 : ℝ) = (0 : unitInterval) := by
    apply Subtype.ext
    rw [Set.projIcc_of_mem h01 ⟨le_rfl, zero_le_one⟩]; rfl
  have hproj1 : Set.projIcc 0 1 h01 (1 : ℝ) = (1 : unitInterval) := by
    apply Subtype.ext
    rw [Set.projIcc_of_mem h01 ⟨zero_le_one, le_rfl⟩]; rfl
  have hHleft : ∀ v : ℝ, H (0, v) = α (Set.projIcc 0 1 h01 v) := by
    intro v
    have hval : Hf (0, v) = αD (Set.projIcc 0 1 h01 v) := by
      rw [hHfdef]
      show F (Set.projIcc 0 1 h01 (0:ℝ), Set.projIcc 0 1 h01 v) = αD (Set.projIcc 0 1 h01 v)
      rw [hproj0]
      exact F.map_zero_left _
    rw [hHdef]
    exact congrArg Subtype.val hval
  have hHright : ∀ v : ℝ, H (1, v) = β (Set.projIcc 0 1 h01 v) := by
    intro v
    have hval : Hf (1, v) = βD (Set.projIcc 0 1 h01 v) := by
      rw [hHfdef]
      show F (Set.projIcc 0 1 h01 (1:ℝ), Set.projIcc 0 1 h01 v) = βD (Set.projIcc 0 1 h01 v)
      rw [hproj1]
      exact F.map_one_left _
    rw [hHdef]
    exact congrArg Subtype.val hval
  have hHbot : ∀ u : ℝ, H (u, 0) = x := by
    intro u
    have hval : Hf (u, 0) = ⟨x, hxD⟩ := by
      rw [hHfdef]
      show F (Set.projIcc 0 1 h01 u, Set.projIcc 0 1 h01 (0:ℝ)) = ⟨x, hxD⟩
      rw [hproj0]
      exact F.source _
    rw [hHdef]
    exact congrArg Subtype.val hval
  have hHtop : ∀ u : ℝ, H (u, 1) = y := by
    intro u
    have hval : Hf (u, 1) = ⟨y, hyD⟩ := by
      rw [hHfdef]
      show F (Set.projIcc 0 1 h01 u, Set.projIcc 0 1 h01 (1:ℝ)) = ⟨y, hyD⟩
      rw [hproj1]
      exact F.target _
    rw [hHdef]
    exact congrArg Subtype.val hval
  -- the sets `S₁ = H ⁻¹' K₁`, `S₂ = H ⁻¹' K₂`
  set S₁ : Set (ℝ × ℝ) := H ⁻¹' K₁ with hS₁def
  set S₂ : Set (ℝ × ℝ) := H ⁻¹' K₂ with hS₂def
  have hmS₁ : ∀ z : ℝ × ℝ, z ∈ S₁ ↔ H z ∈ K₁ := fun z => by rw [hS₁def]; rfl
  have hmS₂ : ∀ z : ℝ × ℝ, z ∈ S₂ ↔ H z ∈ K₂ := fun z => by rw [hS₂def]; rfl
  have hS₁c : IsClosed S₁ := by rw [hS₁def]; exact h₁.preimage hHc
  have hS₂c : IsClosed S₂ := by rw [hS₂def]; exact h₂.preimage hHc
  have hSdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have h1 : H z ∈ K₁ := (hmS₁ z).mp hz₁
    have h2 : H z ∈ K₂ := (hmS₂ z).mp hz₂
    have hzK : H z ∈ K := ⟨h1, h2⟩
    exact hDsub (Hf z).2 hzK
  -- edge conditions
  have hL : S₁ ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨u, v⟩ ⟨h1, h2⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
    obtain ⟨hu, hv⟩ := h2
    have hval : H (u, v) = α (Set.projIcc 0 1 h01 v) := by rw [hu]; exact hHleft v
    exact hα (Set.projIcc 0 1 h01 v) (hval ▸ (hmS₁ _).mp h1)
  have hR : S₂ ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨u, v⟩ ⟨h1, h2⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
    obtain ⟨hu, hv⟩ := h2
    have hval : H (u, v) = β (Set.projIcc 0 1 h01 v) := by rw [hu]; exact hHright v
    exact hβ (Set.projIcc 0 1 h01 v) (hval ▸ (hmS₂ _).mp h1)
  have hBtm : (S₁ ∪ S₂) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨u, v⟩ ⟨h1, h2⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
    obtain ⟨hu, hv⟩ := h2
    have hval : H (u, v) = x := by rw [hv]; exact hHbot u
    rcases h1 with h | h
    · exact hx (Or.inl (hval ▸ (hmS₁ _).mp h))
    · exact hx (Or.inr (hval ▸ (hmS₂ _).mp h))
  have hTop : (S₁ ∪ S₂) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨u, v⟩ ⟨h1, h2⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff] at h2
    obtain ⟨hu, hv⟩ := h2
    have hval : H (u, v) = y := by rw [hv]; exact hHtop u
    rcases h1 with h | h
    · exact hy (Or.inl (hval ▸ (hmS₁ _).mp h))
    · exact hy (Or.inr (hval ▸ (hmS₂ _).mp h))
  -- the square lemma
  have hkey := Work.Smooth.JordanSeparation.square_lemma_aux hS₁c hS₂c hSdisj hL hR hBtm hTop
  set J : Set (ℝ × ℝ) := connectedComponentIn (S₁ ∪ S₂)ᶜ ((0,0) : ℝ × ℝ) with hJdef
  have hJpre : IsPreconnected J := by
    rw [hJdef]; exact isPreconnected_connectedComponentIn
  have hJsub : J ⊆ (S₁ ∪ S₂)ᶜ := by rw [hJdef]; exact connectedComponentIn_subset _ _
  have h00J : ((0:ℝ), (0:ℝ)) ∈ J := by
    rw [hJdef]
    refine mem_connectedComponentIn ?_
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨fun h => hx (Or.inl (hHbot 0 ▸ (hmS₁ _).mp h)),
           fun h => hx (Or.inr (hHbot 0 ▸ (hmS₂ _).mp h))⟩
  have h01J : ((0:ℝ), (1:ℝ)) ∈ J := by rw [hJdef]; exact hkey
  -- push forward
  have hImpre : IsPreconnected (H '' J) := hJpre.image H hHc.continuousOn
  have hImsub : H '' J ⊆ (K₁ ∪ K₂)ᶜ := by
    rintro z ⟨p, hp, rfl⟩
    have hp' := hJsub hp
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hp' ⊢
    exact ⟨fun h => hp'.1 ((hmS₁ p).mpr h), fun h => hp'.2 ((hmS₂ p).mpr h)⟩
  have hxIm : x ∈ H '' J := ⟨(0,0), h00J, hHbot 0⟩
  have hyIm : y ∈ H '' J := ⟨(0,1), h01J, hHtop 0⟩
  exact hImpre.subset_connectedComponentIn hxIm hImsub hyIm

/-- **Janiszewski's theorem on the sphere, from simple connectedness of complementary domains.**

This is `janiszewski_of_simplyConnected` with the two auxiliary classical inputs `hcomp` and
`hLP` supplied by the workspace lemmas
`Work.Smooth.SphereJordan.Chain.isPreconnected_compl_componentIn_sphere` and
`Work.Smooth.JordanSeparation.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected`.  The only remaining hypothesis is the
simple connectivity of `D` (`IsSimplyConnected D`) for an open preconnected `D` with preconnected
complement. -/
theorem sphereJaniszewski_of_simplyConnected
    (hsc : ∀ D : Set (OnePoint ℂ), IsOpen D → D.Nonempty → IsPreconnected D →
      IsPreconnected Dᶜ → IsSimplyConnected D)
    {K₁ K₂ : Set (OnePoint ℂ)} (h₁ : IsClosed K₁) (h₂ : IsClosed K₂)
    (hne : (K₁ ∩ K₂).Nonempty) (hcon : IsPreconnected (K₁ ∩ K₂))
    {x y : OnePoint ℂ} (hx : x ∉ K₁ ∪ K₂) (hy : y ∉ K₁ ∪ K₂)
    (hc₁ : y ∈ connectedComponentIn K₁ᶜ x) (hc₂ : y ∈ connectedComponentIn K₂ᶜ x) :
    y ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ x := by
  have hcomp' : ∀ {K : Set (OnePoint ℂ)}, IsClosed K → K.Nonempty → IsPreconnected K →
      ∀ {x : OnePoint ℂ}, x ∉ K → IsPreconnected ((connectedComponentIn Kᶜ x)ᶜ) := by
    intro K hK hKne hKp x hx'
    exact isPreconnected_compl_componentIn_sphere hK hKne hKp hx'
  exact janiszewski_of_simplyConnected hsc hcomp' Work.Smooth.JordanSeparation.onePoint_locallyPathConnected
    h₁ h₂ hne hcon hx hy hc₁ hc₂

end

end Work.Smooth.SphereJordan.Chain
