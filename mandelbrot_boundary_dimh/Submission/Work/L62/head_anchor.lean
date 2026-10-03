import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.l62c_mid
import Submission.Work.L62.openMapOn_Bu
import Submission.Work.L62.uniform_preimage_bound

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-! ## Auxiliary facts

This file supplies `Work.L62.head_anchor`, the `β`-uniform bound on a preimage of a prescribed
value needed by the head of Lemma 6.2.  It uses one fact of its own,

* `isCompact_betaBox`: the box `{0 ≤ Re ≤ 1, |Im| ≤ b}` of admissible `β` is compact,

and two facts from the shared library,

* `Work.L62.openMapOn_Bu`: the lifted horn map `d.E` is *open* on the upper horn `hd.Bu` (the open
  mapping theorem for holomorphic functions, with `hd.Bu_conn` and `hd.surj_u` ruling out the
  constant case);
* `Work.L62.uniform_preimage_bound`: the abstract compactness argument — a map which is open on an
  open set `X` and surjective onto a compact `K` has *chosen* preimages of the points of `K` lying
  in a single ball.  (This is the only place where the compactness of the value set is used; note
  that it bounds a *chosen* preimage, not every preimage -- the latter is false in general, e.g.
  for `exp` on `ℂ`.)

The assembly is `head_anchor` itself: for each of the two centres `c ∈ {ζa, ζb}`, apply
`uniform_preimage_bound` to `X := hd.Bu`, `f := d.E` and the compact value set `K := c + box`, and
take the maximum of the two bounds.  The separation hypothesis `c + β ∉ hd.v + ℤ` is used only to
upgrade `hd.crit` to non-criticality of the point produced. -/

/-- The `β`-box `{0 ≤ Re β ≤ 1, |Im β| ≤ b}` of Lemma 6.2 is compact: it is the image of the
rectangle `[0,1] × [-b,b]` under `(x,y) ↦ x + iy`. -/
theorem isCompact_betaBox (b : ℝ) :
    IsCompact {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
  have himg : ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-b) b))
      = {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
    ext β
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      refine ⟨by simpa using hp1.1, by simpa using hp1.2, ?_⟩
      have h2 : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
      rw [h2]
      exact abs_le.mpr ⟨hp2.1, hp2.2⟩
    · intro hβ
      refine ⟨(β.re, β.im), ⟨⟨hβ.1, hβ.2.1⟩, ?_⟩, ?_⟩
      · exact abs_le.mp hβ.2.2
      · simp
  rw [← himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- **A bounded preimage of a prescribed value, uniform in `β` and in the choice of centre.**

`d.E : Bu → ℂ` (`Bu = hd.Bu`) is surjective (`hd.surj_u`) and a covering map over
`ℂ \ (hd.v + ℤ)` (`hd.cov_u`); `Bu` is open, connected, `T`-invariant and contains `{hd.η < Im ·}`.

There is a *fixed* bound `M` such that for every `β` in the box `{0 ≤ Re β ≤ 1, |Im β| ≤ b}`, every
prescribed centre `c ∈ {ζa, ζb}` for which `c + β` is not a critical value of `d.E - β`
(i.e. `c + β ∉ hd.v + ℤ`), there is a point `u ∈ Bu` with `d.E u = c + β`, `‖u‖ ≤ M`, which is not a
critical point of `d.E`.  (If `c + β ∉ hd.v + ℤ` then *every* `Bu`-preimage is non-critical, by
`hd.crit`; so the whole content is the *β-uniform bound* `‖u‖ ≤ M`, the choice of `u` being free.)

This is the missing input of the head of Lemma 6.2 (see `NOTES_L62_head_up.md`, `NOTES_L62f.md` §6,
and the *refuted* shortcut `preimage_box.lean`): the head discs must all lie in ONE fixed compact
`K ⊆ d.DE`, because `L62Statement` hands `DR ⊇ K ∪ {|Im| ≥ y₁}` to the chain and requires
`W (j+1) ⊆ DR`.  Taking `W₁` to be the component of `(d.E - β)⁻¹ (ball c ρ) ∩ Bu` through such a
`u` gives `W₁` close to `u`, hence inside a fixed compact for small `ρ`.

Proof: for each of the two centres `c`, apply `uniform_preimage_bound` to
`X := hd.Bu`, `f := d.E` (`d.E` is open on `Bu` by `isOpen_image_subset_Bu`, and surjective) and
`K := c + box` (compact by `isCompact_betaBox`).  This gives one bound `M_c` for all admissible `β`
simultaneously; the separation hypothesis `c + β ∉ hd.v + ℤ` is used only to upgrade
`hd.crit` to non-criticality of the point produced. -/
theorem head_anchor {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} (hb : 0 < b) {ζa ζb : ℂ}
    (hζa : ζa ∉ d.DE) (hζb : ζb ∉ d.DE) (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
      ∀ c : ℂ, (c = ζa ∨ c = ζb) → (∀ k : ℤ, c + β ≠ hd.v + (k : ℂ)) →
      ∃ u : ℂ, u ∈ hd.Bu ∧ d.E u = c + β ∧ ‖u‖ ≤ M ∧ deriv d.E u ≠ 0 := by
  -- the uniform bound for one fixed centre: valid for *every* value in the compact `c + box`
  have key : ∀ c : ℂ, ∃ M : ℝ, 0 < M ∧ ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
      ∃ u : ℂ, u ∈ hd.Bu ∧ d.E u = c + β ∧ ‖u‖ ≤ M := by
    intro c
    have hK : IsCompact ((fun β : ℂ => c + β) ''
        {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b}) :=
      (isCompact_betaBox b).image (by continuity)
    obtain ⟨M, hM, hMy⟩ := uniform_preimage_bound (X := hd.Bu) (f := d.E)
      hd.Bu_open (fun s hs hso => openMapOn_Bu d hd hs hso) hK (fun y hy => by
        obtain ⟨β, hβ, rfl⟩ := hy
        obtain ⟨u, hu, huE⟩ := hd.surj_u (c + β)
        exact ⟨u, hu, huE⟩)
    refine ⟨M, hM, ?_⟩
    intro β h0 h1 him
    obtain ⟨u, hu, huE, hnorm⟩ := hMy (c + β) ⟨β, ⟨h0, h1, him⟩, rfl⟩
    exact ⟨u, hu, huE, hnorm⟩
  obtain ⟨Ma, hMa, hka⟩ := key ζa
  obtain ⟨Mb, hMb, hkb⟩ := key ζb
  refine ⟨max Ma Mb + 1, by positivity, ?_⟩
  intro β h0 h1 him c hc hsep'
  -- non-criticality of any preimage of `c + β`, since `c + β` is not a critical value
  have hnc : ∀ u : ℂ, u ∈ hd.Bu → d.E u = c + β → deriv d.E u ≠ 0 := by
    intro u hu huE hd0
    obtain ⟨k, hk⟩ := hd.crit u (Or.inl hu) hd0
    exact hsep' k (huE.symm.trans hk)
  rcases hc with rfl | rfl
  · obtain ⟨u, hu, huE, hnorm⟩ := hka β h0 h1 him
    exact ⟨u, hu, huE, by linarith [le_max_left Ma Mb, hnorm, le_refl (1 : ℝ)], hnc u hu huE⟩
  · obtain ⟨u, hu, huE, hnorm⟩ := hkb β h0 h1 him
    exact ⟨u, hu, huE, by linarith [le_max_right Ma Mb, hnorm, le_refl (1 : ℝ)], hnc u hu huE⟩

end

end Work.L62
