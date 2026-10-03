import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.spread_chain_nesting
import Submission.Work.Topology.Covering.restrict_base_homeomorph
import Submission.Work.Topology.Covering.isEvenlyCovered_subtype_of_sheets

set_option linter.style.haveILetI false

namespace Work.Horn

open Set Metric Filter

/-- **First rung of the chain's degree structure** (Shishikura, Lemma 5.4; `NOTES_GERM_F0.md`
§§41–43, item 2).

`G` is holomorphic on the open `D`, is a covering map on `D` over `ℂ ∖ {0, v}`, and every critical
point of `G` in `D` has value `v`.  `W : ℕ → Fin q → Set ℂ` is an *increasing* chain of open
subsets of `D` with `G '' W (n+1) i ⊆ W n i ∪ {0}` which is **component-saturated**:

`hWsat : ∀ C, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (W n i) → (C ∩ W (n+1) i).Nonempty →
  C ⊆ W (n+1) i`

(the two reviewers' fix: one-sided maximality "`C` meets `W n i` ⟹ `C ⊆ W (n+1) i`" allows
*truncated* branches of `D ∩ G ⁻¹' (W n i)` inside `W (n+1) i`, which destroys even covering —
counterexamples `G = exp` on a small ball and `G = z²` on `ℂ∖{0}` were supplied.  Saturation is
what the construction "`W (n+1) i` = the union of the components of `D ∩ G ⁻¹' (W n i)` meeting
`W n i`" of `Work.Horn.spread_chain_nesting` actually gives.)

Then each chain map is a covering of the previous level away from the critical value:
`fun z : ↥(W (n+1) i) => G z` is a covering map over `W n i \ {0, v}`.

*Proof sketch.*  For `y ∈ W n i \ {0, v}`: `hcov` gives local sections of `G` near `y`; if
`σ : U → ℂ` is a section through `z ∈ W (n+1) i` with `U ∋ y` connected, then `σ '' U` is
preconnected, lies in `D`, satisfies `G (σ u) = u ∈ W n i` so `σ '' U ⊆ G ⁻¹' (W n i)` and meets
`W (n+1) i` at `z`; saturation puts `σ '' U ⊆ W (n+1) i`, so the section is a section of the
subtype map, giving even covering.  No properness and no degree is claimed here. -/
theorem spread_chain_covering_off_critval {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {v : ℂ}
    {W : ℕ → Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hcov : IsCoveringMapOn (fun z : ↥D => G z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hcritval : ∀ z ∈ D, deriv G z = 0 → G z = v)
    (hWopen : ∀ n i, IsOpen (W n i)) (hWsub : ∀ n i, W n i ⊆ D)
    (hWmono : ∀ n i, W n i ⊆ W (n + 1) i)
    (hWmap : ∀ n i, Set.MapsTo G (W (n + 1) i) (W n i ∪ {0}))
    (hWsat : ∀ n i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (W n i) →
      (C ∩ W (n + 1) i).Nonempty → C ⊆ W (n + 1) i) :
    ∀ n i, IsCoveringMapOn (fun z : ↥(W (n + 1) i) => G z) (W n i \ {0, v}) := by
  intro n i
  -- the ambient covering `f = G↾D` and its data at a point `y` of the smaller base
  intro y hy
  rw [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
  obtain ⟨hyW, hy0, hyv⟩ := hy
  have hyS : y ∈ {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} := ⟨hy0, hyv⟩
  obtain ⟨hIdisc, U, hyU, hUopen, hfUopen, H, hH⟩ := hcov y hyS
  -- shrink the evenly covered neighbourhood of `y` to a ball inside `W n i ∩ U`
  have hmem : W n i ∩ U ∈ nhds y :=
    inter_mem ((hWopen n i).mem_nhds hyW) (hUopen.mem_nhds hyU)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hyr : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hballW : Metric.ball y r ⊆ W n i := fun z hz => (hrsub hz).1
  have hballU : Metric.ball y r ⊆ U := fun z hz => (hrsub hz).2
  -- restrict the trivialization to that ball
  obtain ⟨hfU'open, H', hH'⟩ :=
    Work.Topology.Covering.restrict_base_homeomorph (f := fun z : ↥D => G z)
      hballU Metric.isOpen_ball hfUopen H hH
  -- the saturated set: the next level of the chain, viewed inside `↥D`
  let X₀ : Set ↥D := {z | (z : ℂ) ∈ W (n + 1) i}
  have hsat : ∀ C : Set ↥D, IsPreconnected C → C ⊆ (fun z : ↥D => G z) ⁻¹' Metric.ball y r →
      (C ∩ X₀).Nonempty → C ⊆ X₀ := by
    intro C hCpre hCU hCmeet
    have hpre : IsPreconnected (Subtype.val '' C) :=
      hCpre.image Subtype.val continuous_subtype_val.continuousOn
    have hsubD : Subtype.val '' C ⊆ D := by rintro _ ⟨z, _, rfl⟩; exact z.2
    have hsubG : Subtype.val '' C ⊆ G ⁻¹' (W n i) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hballW (hCU hz)
    have hmeet : (Subtype.val '' C ∩ W (n + 1) i).Nonempty := by
      obtain ⟨z, hzC, hzX⟩ := hCmeet
      exact ⟨z, ⟨z, hzC, rfl⟩, hzX⟩
    have hsub := hWsat n i (Subtype.val '' C) hpre hsubD hsubG hmeet
    intro z hz
    exact hsub ⟨z, hz, rfl⟩
  -- even coveredness of `G↾↥D` restricted to `X₀`
  haveI := hIdisc
  have hres := Work.Topology.Covering.isEvenlyCovered_subtype_of_sheets
    (X := ↥D) (Y := ℂ) (f := fun z : ↥D => G z) (y := y)
    (I := ↥((fun z : ↥D => G z) ⁻¹' {y})) (X₀ := X₀) (U' := Metric.ball y r)
    hyr Metric.isOpen_ball Metric.isPreconnected_ball hfU'open H' hH' hsat
  -- transport along the canonical homeomorphism `↥(W (n+1) i) ≃ₜ ↥X₀`
  let e : ↥(W (n + 1) i) ≃ₜ ↥X₀ :=
    { toFun := fun z => ⟨⟨z.1, hWsub (n + 1) i z.2⟩, z.2⟩
      invFun := fun w => ⟨w.1.1, w.2⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl
      continuous_toFun := by
        refine Continuous.subtype_mk (f := fun z : ↥(W (n + 1) i) =>
          (⟨(z : ℂ), hWsub (n + 1) i z.2⟩ : ↥D)) ?_ (fun z => z.2)
        exact Continuous.subtype_mk continuous_subtype_val (fun z => hWsub (n + 1) i z.2)
      continuous_invFun := by
        refine Continuous.subtype_mk (f := fun w : ↥X₀ => (((w : ↥D) : ℂ))) ?_
          (fun w => w.2)
        exact continuous_subtype_val.comp continuous_subtype_val }
  exact (hres.comp_homeomorph e).to_isEvenlyCovered_preimage

end Work.Horn
