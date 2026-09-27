import Mathlib
import Submission.Work.Whitney.PushDefs

/-!
# The frontier bookkeeping of a cut ("collar") push

This module contains the parts of `Work.Whitney.HasAmbientPushData` that follow from its *clauses
alone*, with no geometry: the structure of `W₀` relative to the fixed set of `ψ`.

They are the lemmas any construction of the push has to respect, and they are the reason the
"cut" form of the push has to be stated carefully:

* `closure_inter_preimage_subset`: if `ψ` is the identity outside an open set `S` and the image of
  `frontier W₀` is disjoint from `S`, then `W₀ ∩ f ⁻¹' S` is **clopen in** `f ⁻¹' S`; consequently
  (`preconnected_subset_or_disjoint`) any connected subset of `f ⁻¹' S` lies either in `W₀` or in
  its complement.  This is exactly the analysis used to locate the support of a cut push.
* `pushData_notMem_closure`: from the clauses of the push data, `p₁ ∉ closure W₀` (and likewise
  `q₁`): the partner of the moved point cannot be in the closure of the pushed region.
* `pushData_notMem_O`: the moved value `f p₂` cannot be in the region on which `ψ` is the identity.
* `cutForm_of_placement`: the placement clause of `HasAmbientPushData` is equivalent, for the
  sources in `W₀`, to the "cut" conclusion `z ∈ W₀ ∨ z = p₁ ∨ z = q₁`; this is the form in which a
  *local* geometric construction has to produce the clause.

Nothing here uses the hypothesis `hsign : OppositeType ...`: the sign enters only in the geometric
construction of `ψ` (see `Submission/Work/Whitney/CutPush/README.md`).
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The clopen structure of `W₀ ∩ f ⁻¹' S` -/

/-- If the image of the frontier of `W₀` avoids `S`, then `closure (W₀ ∩ f ⁻¹' S) ∩ f ⁻¹' S ⊆ W₀`:
every limit point (inside `f ⁻¹' S`) of the part of `W₀` mapping into `S` is itself in `W₀`.

This is the elementary "clopen" fact behind every cut push: the pushed region is a union of
components of the preimage of the support of `ψ`. -/
theorem closure_inter_preimage_subset {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (W₀ : Set M) (S : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (hfr : f '' frontier W₀ ∩ S = ∅) :
    closure (W₀ ∩ f ⁻¹' S) ∩ f ⁻¹' S ⊆ W₀ := by
  intro x hx
  by_contra hxW
  have hxcl : x ∈ closure W₀ := (closure_mono Set.inter_subset_left) hx.1
  have hxfr : x ∈ frontier W₀ := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨hxcl, subset_closure hxW⟩
  have hmem : f x ∈ f '' frontier W₀ ∩ S := ⟨⟨x, hxfr, rfl⟩, hx.2⟩
  rw [hfr] at hmem
  exact hmem

/-- **The pushed region is a union of components of the preimage of the support.**  If `ψ` is the
identity off an open `S` (so that `f ⁻¹' S ⊆ Fix ψ` on the relevant part) and the image of
`frontier W₀` avoids `S`, then every preconnected `C ⊆ f ⁻¹' S` either lies in `W₀` or misses it.
In particular the source of the moved part of `f '' W₀` is a union of components of the (open) set
`f ⁻¹' S`. -/
theorem preconnected_subset_or_disjoint {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (W₀ : Set M) (hW₀ : IsOpen W₀) (S : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (hfr : f '' frontier W₀ ∩ S = ∅) {C : Set M} (hC : IsPreconnected C)
    (hCS : C ⊆ f ⁻¹' S) : C ⊆ W₀ ∨ Disjoint C W₀ := by
  -- the two halves of the clopen statement
  have hA : ∀ x ∈ C, x ∉ W₀ → x ∉ closure W₀ := by
    intro x hxC hxW hxcl
    have hxS : x ∈ f ⁻¹' S := hCS hxC
    have hxfr : x ∈ frontier W₀ := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hxcl, subset_closure hxW⟩
    have hmem : f x ∈ f '' frontier W₀ ∩ S := ⟨⟨x, hxfr, rfl⟩, hxS⟩
    rw [hfr] at hmem
    exact hmem
  by_cases hne : (C ∩ W₀).Nonempty
  · left
    have hdisj : Disjoint W₀ ((closure W₀)ᶜ) :=
      Set.disjoint_left.mpr fun x hxW hxc => hxc (subset_closure hxW)
    refine IsPreconnected.subset_left_of_subset_union hW₀ (isClosed_closure.isOpen_compl)
      hdisj ?_ ?_ hC
    · intro x hx
      by_cases hxW : x ∈ W₀
      · exact Or.inl hxW
      · exact Or.inr (hA x hx hxW)
    · exact hne
  · right
    rw [Set.disjoint_left]
    exact fun x hxC hxW => hne ⟨x, hxC, hxW⟩

/-- **The landing obstruction.**  Suppose `S` is a set containing everything `ψ` moves and the
image of `frontier W₀` avoids `S`.  If two points `z` and `p₁` are both in `f ⁻¹' S` and are joined
by a *preconnected* subset of `f ⁻¹' S`, and `p₁ ∉ W₀`, then `z ∉ W₀`.

Equivalently: the preimage of a point moved by `ψ` which is joined to `p₁` through the support can
never lie in the pushed region `W₀`.  This is the structural fact behind the obstruction to the
*local* cut push (see `Submission/Work/Whitney/CutPush/README.md`): the pushed sheet has to meet the
other sheet again, at a point whose preimage is joined to `p₁` through the support, so that the cut
clause `z ∈ W₀` fails for a single local push.  It is the reason the two local pushes have to be
constructed jointly (the "gluing" step, where the framing hypothesis `OppositeType` enters). -/
theorem notMem_of_preconnected_subset_preimage {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {W₀ : Set M} (hW₀ : IsOpen W₀) {S : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    (hfr : f '' frontier W₀ ∩ S = ∅) {C : Set M} (hC : IsPreconnected C) (hCS : C ⊆ f ⁻¹' S)
    {z p₁ : M} (hz : z ∈ C) (hp₁C : p₁ ∈ C) (hp₁ : p₁ ∉ W₀) : z ∉ W₀ := by
  intro hzW₀
  rcases preconnected_subset_or_disjoint W₀ hW₀ S hfr hC hCS with hsub | hdisj
  · exact hp₁ (hsub hp₁C)
  · exact (Set.disjoint_left.mp hdisj hz hzW₀).elim

/-- **The cut form implies the placement clause.**  Conversely to `cutForm_of_placement`: if every
coincidence `ψ (f x) = f z` with `x ∈ W₀` has `z ∈ W₀` or `z` one of the two partners `p₁`, `q₁`
(whose values are attained on `W₀` because `p₂, q₂ ∈ W₀`), then `ψ` maps `f '' W₀` into
`f '' W₀ ∪ (f '' univ)ᶜ`. -/
theorem placement_of_cutForm {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W₀ : Set M}
    {p₁ p₂ q₁ q₂ : M} (hp₂ : p₂ ∈ W₀) (hq₂ : q₂ ∈ W₀) (hfp : f p₁ = f p₂)
    (hfq : f q₁ = f q₂)
    {ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))}
    (hcut : ∀ x : M, x ∈ W₀ → ∀ z : M, ψ (f x) = f z → z ∈ W₀ ∨ z = p₁ ∨ z = q₁) :
    ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ := by
  rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
  by_cases hmem : ψ (f x) ∈ f '' (Set.univ : Set M)
  · left
    obtain ⟨z, -, hz⟩ := hmem
    rcases hcut x hx z hz.symm with h3 | h3 | h3
    · exact ⟨z, h3, hz⟩
    · exact ⟨p₂, hp₂, by rw [← hz, h3, hfp]⟩
    · exact ⟨q₂, hq₂, by rw [← hz, h3, hfq]⟩
  · right; exact hmem

/-! ## Necessary conditions on `W₀` and `O` -/

/-- **The partner of the moved point is not in the closure of the pushed region.**
If `ψ` is the identity on an open `O` containing the image of `frontier W₀`, `p₂` is in `W₀` while
`p₁` is not, `f p₁ = f p₂`, and the value `f p₂` is not attained by `ψ` on `f '' W₀`, then
`p₁ ∉ closure W₀`.

(Indeed `p₁ ∈ frontier W₀` would put `f p₁ ∈ O`, hence `ψ (f p₁) = f p₁ = f p₂`, and `f p₂` *is*
attained by `ψ` on `f '' W₀` --- at `p₂`.) -/
theorem pushData_notMem_closure {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W₀ : Set M}
    (hW₀open : IsOpen W₀) {O : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    (hfront : f '' frontier W₀ ⊆ O) {ψ : EuclideanSpace ℝ (Fin (2 * n)) →
      EuclideanSpace ℝ (Fin (2 * n))} (hψid : ∀ y ∈ O, ψ y = y)
    {p₁ p₂ : M} (hp₁ : p₁ ∉ W₀) (hp₂ : p₂ ∈ W₀) (hfp : f p₁ = f p₂)
    (hnot : f p₂ ∉ ψ '' (f '' W₀)) : p₁ ∉ closure W₀ := by
  intro hcl
  have hfr : p₁ ∈ frontier W₀ := by
    rw [hW₀open.frontier_eq]
    exact ⟨hcl, hp₁⟩
  have hp₁O : f p₁ ∈ O := hfront ⟨p₁, hfr, rfl⟩
  refine hnot ⟨f p₁, ⟨p₂, hp₂, hfp.symm⟩, (hψid (f p₁) hp₁O).trans hfp⟩

/-- **The moved value is not in the fixed region.**  If `ψ` is the identity on `O`, `p₂ ∈ W₀` and
`f p₂ ∉ ψ '' (f '' W₀)`, then `f p₂ ∉ O`. -/
theorem pushData_notMem_O {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W₀ : Set M}
    {O : Set (EuclideanSpace ℝ (Fin (2 * n)))} {ψ : EuclideanSpace ℝ (Fin (2 * n)) →
      EuclideanSpace ℝ (Fin (2 * n))} (hψid : ∀ y ∈ O, ψ y = y)
    {p₂ : M} (hp₂ : p₂ ∈ W₀) (hnot : f p₂ ∉ ψ '' (f '' W₀)) : f p₂ ∉ O := by
  intro hO
  refine hnot ⟨f p₂, ⟨p₂, hp₂, rfl⟩, hψid (f p₂) hO⟩

/-! ## The cut form of the placement clause -/

/-- **The placement clause in "cut" form.**  For a point `x` of the pushed region whose image is
again in `f '' M`, the *preimage* driving the coincidence must be in `W₀` --- unless it is one of
the partners `p₁`, `q₁` (which are not in `W₀`, and whose values `f p₁ = f p₂`, `f q₁ = f q₂` *are*
attained on `W₀`).

This is the form in which the geometric construction has to deliver the placement clause. -/
theorem cutForm_of_placement {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W W₀ : Set M}
    {p₁ p₂ q₁ q₂ : M} (hW₀sub : W₀ ⊆ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁ : p₁ ∉ W₀) (hq₁ : q₁ ∉ W₀)
    {ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))}
    (hplace : ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ)
    {x z : M} (hx : x ∈ W₀) (hxz : ψ (f x) = f z) :
    z ∈ W₀ ∨ z = p₁ ∨ z = q₁ := by
  have hmem : ψ (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ :=
    hplace ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  rcases hmem with ⟨y, hy, hyx⟩ | hnotmem
  · have hyz : f y = f z := hyx.trans hxz
    by_cases hzW : z ∈ W
    · rcases hclean y z (hW₀sub hy) hzW hyz with h | h | h | h | h
      · exact Or.inl (h ▸ hy)
      · exact absurd (h.1 ▸ hy) hp₁
      · exact Or.inr (Or.inl h.2)
      · exact absurd (h.1 ▸ hy) hq₁
      · exact Or.inr (Or.inr h.2)
    · exact (hsep y z (hW₀sub hy) hzW hyz).elim
  · exact absurd (hnotmem ⟨z, Set.mem_univ z, hxz.symm⟩) (by simp)

end Work.Whitney.CutPush
