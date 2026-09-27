import Mathlib
import Submission.Work.Whitney.PushSigned
import Submission.Work.Whitney.CutPush.Frontier

/-!
# Localisation of the cut-push obligations

This module contains the purely topological reductions that *localise* the two obligations of a cut
push (`Work.Whitney.CutPush.HasCutPushData`) to the neighbourhoods of the two double points.  They
are the lemmas any construction of the push has to satisfy, and they are what makes the geometric
input a *local* statement at `p₂` and `q₂`.

* `frontier_sdiff_subset` — `frontier (W \ K) ⊆ frontier W ∪ K` for closed `K`: the frontier of a
  cut region consists of the frontier of `W` and the bits of the cuts themselves.
* `frontier_avoid_of_cuts` — the frontier clause of the interface follows from the three checks
  `f '' frontier W`, `f '' K_P`, `f '' K_Q` avoiding the closure of the support.
* `placement_of_moved` — **the placement clause localises to the moved sources**: it is enough to
  check the points `x ∈ W₀` whose value `f x` lies in the support of `ψ` (where `ψ` may move it);
  all other sources are sent to their own value, which lies in `f '' W₀`.
* `cutClause_of_moved` — the "cut form" of the placement clause, obtained by combining the
  localisation with `cutForm_of_placement`.
* `image_subset_of_support` — the placement clause from the local form on the support's preimage.

The lemmas are stated for an arbitrary ambient self-map `ψ` of `ℝ^{2n}`; the geometry of the finger
enters only through the local clause `hmoved`.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The frontier of a cut region -/

/-- **The frontier of a cut region.**  For closed `K`, the frontier of `W \ K` is contained in the
union of the frontier of `W` and `K` itself. -/
theorem frontier_sdiff_subset {W K : Set M} (hK : IsClosed K) :
    frontier (W \ K) ⊆ frontier W ∪ K := by
  intro x hx
  rw [frontier_eq_closure_inter_closure] at hx
  have hxW : x ∈ closure W := (closure_mono Set.sdiff_subset) hx.1
  have hxcompl : x ∈ closure ((W \ K)ᶜ) := hx.2
  have hsub : (W \ K)ᶜ = Wᶜ ∪ K := by
    ext y
    by_cases hy : y ∈ W <;> simp [Set.mem_sdiff, hy]
  rw [hsub, closure_union, hK.closure_eq] at hxcompl
  rcases hxcompl with h | h
  · exact Or.inl (by rw [frontier_eq_closure_inter_closure]; exact ⟨hxW, h⟩)
  · exact Or.inr h

/-- **The frontier clause localises to the cuts.**  If the images of `frontier W`, of the two cuts
`K_P`, `K_Q`, all avoid the closure of the support `S`, then so does the image of the frontier of
`W \ (K_P ∪ K_Q)`. -/
theorem frontier_avoid_of_cuts {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {W K_P K_Q : Set M} {S : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    (hK_P : IsClosed K_P) (hK_Q : IsClosed K_Q)
    (hW : f '' frontier W ∩ closure S = ∅)
    (hP : f '' K_P ∩ closure S = ∅) (hQ : f '' K_Q ∩ closure S = ∅) :
    f '' frontier (W \ (K_P ∪ K_Q)) ∩ closure S = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨⟨x, hx, hxy⟩, hy⟩
  have hy' : f x ∈ closure S := hxy ▸ hy
  have hx' : x ∈ frontier W ∪ (K_P ∪ K_Q) :=
    frontier_sdiff_subset (hK_P.union hK_Q) hx
  rcases hx' with hx' | hx'
  · exact Set.eq_empty_iff_forall_notMem.mp hW (f x) ⟨⟨x, hx', rfl⟩, hy'⟩
  · rcases hx' with hx' | hx'
    · exact Set.eq_empty_iff_forall_notMem.mp hP (f x) ⟨⟨x, hx', rfl⟩, hy'⟩
    · exact Set.eq_empty_iff_forall_notMem.mp hQ (f x) ⟨⟨x, hx', rfl⟩, hy'⟩

/-! ## The placement clause localises to the moved sources -/

/-- **The placement clause localises to the moved sources.**  If `ψ` is the identity off `S` and the
local clause "moved values land in `f '' W₀ ∪ (f '' M)ᶜ`" holds for the sources `x ∈ W₀` with
`f x ∈ S`, then the global placement clause holds. -/
theorem placement_of_moved {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W₀ : Set M}
    {S : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    {ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))}
    (hid : ∀ y, y ∉ S → ψ y = y)
    (hmoved : ∀ x ∈ W₀, f x ∈ S → ψ (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ) :
    ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ := by
  rintro y ⟨z, ⟨x, hx, rfl⟩, hzy⟩
  subst hzy
  by_cases h : f x ∈ S
  · exact hmoved x hx h
  · left
    rw [hid (f x) h]
    exact ⟨x, hx, rfl⟩

/-- **The cut form of the placement clause, localised to the moved sources.**  With the same
hypotheses as `placement_of_moved`, together with the cleanness/separatedness of `f` on `W`, the
conclusion `ψ (f x) = f z → z ∈ W₀ ∨ z = p₁ ∨ z = q₁` holds for every `x ∈ W₀`. -/
theorem cutClause_of_moved {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W W₀ : Set M}
    {S : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    {ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))}
    {p₁ p₂ q₁ q₂ : M}
    (hW₀sub : W₀ ⊆ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁ : p₁ ∉ W₀) (hq₁ : q₁ ∉ W₀)
    (hid : ∀ y, y ∉ S → ψ y = y)
    (hmoved : ∀ x ∈ W₀, f x ∈ S → ψ (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ) :
    ∀ x : M, x ∈ W₀ → ∀ z : M, ψ (f x) = f z → z ∈ W₀ ∨ z = p₁ ∨ z = q₁ := by
  have hplace := placement_of_moved (f := f) hid hmoved
  intro x hx z hz
  exact cutForm_of_placement hW₀sub hclean hsep hp₁ hq₁ hplace hx hz

/-- **Placement from the local form on the support's preimage.**  Packaging of `placement_of_moved`:
the placement clause of the interface is implied by the local statement that the values of the
sources of `W₀` which lie in the support are sent into `f '' W₀ ∪ (f '' M)ᶜ`. -/
theorem image_subset_of_support {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W₀ : Set M}
    {S : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    {ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))}
    (hid : ∀ y, y ∉ S → ψ y = y)
    (hlocal : ψ '' (f '' (W₀ ∩ f ⁻¹' S)) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ) :
    ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ :=
  placement_of_moved hid fun x hx hxS =>
    hlocal ⟨f x, ⟨x, ⟨hx, hxS⟩, rfl⟩, rfl⟩

/-- **The residual local obligation.**  Combining `placement_of_moved` with the cut form: the whole
placement obligation of the interface reduces to the two local clauses (i) "the support's preimage
inside `W₀` is contained in the region where the push is to be geometrically controlled" and (ii)
"the pushed values of the sources in the support lie in `f '' W₀ ∪ (f '' M)ᶜ`".  This is the form in
which the Whitney finger has to deliver the placement clause. -/
theorem placement_of_localSupport {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W W₀ : Set M}
    {S S' : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    {ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))}
    (hid : ∀ y, y ∉ S → ψ y = y) (hSS : S ⊆ S')
    (hlocal : ∀ x ∈ W₀, f x ∈ S' → ψ (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ) :
    ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ :=
  placement_of_moved hid fun x hx hxS => hlocal x hx (hSS hxS)


/-! ## Localisation to the two double points -/

open scoped Classical in
/-- **Containment of a small clean ball (self-contained).**  If the value `q` of a continuous map
`f` on a compact Hausdorff space has at most the two preimages `p₁`, `p₂`, then for every pair of
open neighbourhoods `U₁ ∋ p₁`, `U₂ ∋ p₂` there is a radius `ε > 0` such that the preimage of
`ball (q, ε)` is contained in `U₁ ∪ U₂`.  (This is the point-set input that localises every
obligation of the push to the two sheets at one double point.) -/
theorem exists_radius_containment {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (q : EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ : M)
    (hpre : ∀ y : M, f y = q → y = p₁ ∨ y = p₂)
    (U₁ U₂ : Set M) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' (Metric.ball q ε) ⊆ U₁ ∪ U₂ := by
  by_cases hne : (((U₁ ∪ U₂)ᶜ : Set M)).Nonempty
  · have hK : IsCompact (((U₁ ∪ U₂)ᶜ : Set M)) := (hU₁.union hU₂).isClosed_compl.isCompact
    have hne' : ∀ y ∈ ((U₁ ∪ U₂)ᶜ : Set M), f y ≠ q := by
      intro y hy h
      rcases hpre y h with rfl | rfl
      · exact hy (Or.inl hp₁)
      · exact hy (Or.inr hp₂)
    have hcont : Continuous fun y : M => dist (f y) q := by fun_prop
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    refine ⟨dist (f y₀) q, dist_pos.mpr (hne' y₀ hy₀), fun y hy => ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball] at hy
    by_contra hnot
    have hle : dist (f y₀) q ≤ dist (f y) q := hmin hnot
    linarith
  · exact ⟨1, one_pos, fun y hy => by
      by_contra h
      exact hne ⟨y, h⟩⟩

/-- **Localisation to the two double points.**  Near the two values `f p₂ ≠ f q₂`, every point of
`M` whose value is close to one of them lies in prescribed neighbourhoods of the four preimages.
This is the point-set statement that reduces every clause of a cut push to the four parameter
neighbourhoods of `p₁, p₂, q₁, q₂`. -/
theorem exists_localisation_near_double_points {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (p₁ p₂ q₁ q₂ : M) (huv : f p₂ ≠ f q₂)
    (hpreP : ∀ y : M, f y = f p₂ → y = p₁ ∨ y = p₂)
    (hpreQ : ∀ y : M, f y = f q₂ → y = q₁ ∨ y = q₂)
    (U₁ U₂ U₃ U₄ : Set M) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU₃ : IsOpen U₃)
    (hU₄ : IsOpen U₄) (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) (hq₁ : q₁ ∈ U₃) (hq₂ : q₂ ∈ U₄) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M,
      f x ∈ Metric.ball (f p₂) ε ∪ Metric.ball (f q₂) ε → x ∈ U₁ ∪ U₂ ∪ U₃ ∪ U₄ := by
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_radius_containment f hf (f p₂) p₁ p₂ hpreP U₁ U₂ hU₁ hU₂ hp₁ hp₂
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_radius_containment f hf (f q₂) q₁ q₂ hpreQ U₃ U₄ hU₃ hU₄ hq₁ hq₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx => ?_⟩
  rcases hx with hx | hx
  · have hx' : x ∈ f ⁻¹' Metric.ball (f p₂) ε₁ := by
      rw [Set.mem_preimage]
      exact Metric.ball_subset_ball (min_le_left ε₁ ε₂) hx
    rcases h₁ hx' with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
  · have hx' : x ∈ f ⁻¹' Metric.ball (f q₂) ε₂ := by
      rw [Set.mem_preimage]
      exact Metric.ball_subset_ball (min_le_right ε₁ ε₂) hx
    rcases h₂ hx' with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-! ## The automatic part of the cut clause -/

/-- **The only bad coincidences are at the two double points.**  For `W₀ ⊆ W` with `p₁, q₁ ∉ W₀`, a
coincidence `f y = f z` with `y ∈ W₀` and `z ∉ W₀` can only be the pair `(p₂, p₁)` or `(q₂, q₁)`.
Hence the placement clause of the push only needs to be verified for the *moved* sources. -/
theorem coincidence_of_mem_notMem {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W W₀ : Set M}
    {p₁ p₂ q₁ q₂ : M}
    (hW₀W : W₀ ⊆ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁ : p₁ ∉ W₀) (hq₁ : q₁ ∉ W₀)
    {y z : M} (hy : y ∈ W₀) (hz : z ∉ W₀) (h : f y = f z) :
    (y = p₂ ∧ z = p₁) ∨ (y = q₂ ∧ z = q₁) := by
  by_cases hzW : z ∈ W
  · rcases hclean y z (hW₀W hy) hzW h with h1 | h1 | h1 | h1 | h1
    · exact absurd (h1 ▸ hy : z ∈ W₀) hz
    · exact absurd (h1.1 ▸ hy : p₁ ∈ W₀) hp₁
    · exact Or.inl h1
    · exact absurd (h1.1 ▸ hy : q₁ ∈ W₀) hq₁
    · exact Or.inr h1
  · exact absurd h (hsep y z (hW₀W hy) hzW)

end Work.Whitney.CutPush
