import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.affFactsDefs
import Submission.Work.SG.conjAct_action
import Submission.Work.SG.affinelyEquivalent_conjAct

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# affEquiv_facts — equivalence relations + orientation preserved (easy–medium, ~150–350 lines)

**Claims.** (i) `AffinelyEquivalent` and (ii) `AffOPEquivalent` are equivalence relations on
`CrystallographicGroup d`; (iii) if `AffinelyEquivalent G H` and all elements of `G` have
`0 < det(linear part)`, so do all elements of `H`.

**Sketch.** Refl: `φ = 1`. Symm: `φ⁻¹` (conjugate both sides of the set equality; for OP,
`det(φ⁻¹.linear) = (det φ.linear)⁻¹ > 0`). Trans: `φ₂ * φ₁`, the sets compose
(`{φ₂ h φ₂⁻¹ | h ∈ φ₁ S φ₁⁻¹}`), and `det` is multiplicative
(`AffineEquiv.linear` of a product is the composite: `AffineEquiv.linearHom` is a monoid hom;
`LinearEquiv.det` is a hom `(M ≃ₗ M) →* Rˣ`). (iii): `g' ∈ H` ⇒ `g'.toAffineEquiv = φ g φ⁻¹`,
so `g'.linear = φ.linear ∘ g.linear ∘ φ.linear⁻¹`, same det.

**Pitfalls.** The sets live in `AffineGroup d = E d ≃ᵃ[ℝ] E d` whose multiplication is
`trans` in the reverse order; use `AffineEquiv.linearHom` / `map_mul` rather than unfolding.
Note `(u : ℝ)` for `u : ℝˣ` is the coercion of `LinearEquiv.det`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

namespace AffFacts

/-! ### The determinant of the linear part

`AffineEquiv.linearHom : (P ≃ᵃ[k] P) →* (V ≃ₗ[k] V)` and `LinearEquiv.det` (a monoid hom)
make all of this formal: `det` is multiplicative and inverts, hence is conjugation invariant. -/

theorem lin_mul {d : ℕ} (φ ψ : AffineGroup d) :
    (φ * ψ).linear = φ.linear * ψ.linear := by
  show AffineEquiv.linearHom (φ * ψ) = AffineEquiv.linearHom φ * AffineEquiv.linearHom ψ
  rw [map_mul]

theorem lin_inv {d : ℕ} (φ : AffineGroup d) : (φ⁻¹).linear = φ.linear⁻¹ := by
  show AffineEquiv.linearHom φ⁻¹ = (AffineEquiv.linearHom φ)⁻¹
  rw [map_inv]

theorem det_mul {d : ℕ} (φ ψ : AffineGroup d) :
    ((φ * ψ).linear.det : ℝ) = (φ.linear.det : ℝ) * (ψ.linear.det : ℝ) := by
  rw [lin_mul, map_mul, Units.val_mul]

theorem det_inv {d : ℕ} (φ : AffineGroup d) :
    ((φ⁻¹).linear.det : ℝ) = ((φ.linear.det : ℝ))⁻¹ := by
  rw [lin_inv, map_inv, Units.val_inv_eq_inv_val]

theorem det_conj {d : ℕ} (φ g : AffineGroup d) :
    ((φ * g * φ⁻¹).linear.det : ℝ) = (g.linear.det : ℝ) := by
  have h : ((φ * g * φ⁻¹).linear.det : ℝˣ) =
      φ.linear.det * g.linear.det * (φ.linear.det)⁻¹ := by
    rw [lin_mul, lin_mul, lin_inv, map_mul, map_mul, map_inv]
  rw [h, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [mul_comm (φ.linear.det : ℝ) (g.linear.det : ℝ), mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero (φ.linear.det)), mul_one]

theorem det_one (d : ℕ) : (0 : ℝ) < ((1 : AffineGroup d).linear.det : ℝ) := by
  have h : (1 : AffineGroup d).linear = 1 := by
    rw [← AffineEquiv.linearHom_apply, map_one]
  rw [h, map_one, Units.val_one]
  norm_num

end AffFacts

/-- Both equivalences are equivalence relations on crystallographic groups, and affine
equivalence preserves "all elements orientation preserving". -/
theorem affEquiv_facts (d : ℕ) :
    Equivalence (fun G H : CrystallographicGroup d => AffinelyEquivalent G.1 H.1) ∧
    Equivalence (fun G H : CrystallographicGroup d => AffOPEquivalent G.1 H.1) ∧
    ∀ G H : Subgroup (EuclideanIsom d), AffinelyEquivalent G H →
      (∀ g ∈ G, IsOrientationPreservingIsom g) → ∀ g ∈ H, IsOrientationPreservingIsom g := by
  obtain ⟨hc1, hc2⟩ := conjAct_action d
  obtain ⟨_, hiffAE, hiffOP⟩ := affinelyEquivalent_conjAct d
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro G
      rw [hiffAE]
      exact ⟨1, hc1 _⟩
    · intro G H hGH
      rw [hiffAE] at hGH ⊢
      obtain ⟨φ, hφ⟩ := hGH
      exact ⟨φ⁻¹, by rw [← hφ, ← hc2, inv_mul_cancel, hc1]⟩
    · intro G H K hGH hHK
      rw [hiffAE] at hGH hHK ⊢
      obtain ⟨φ, hφ⟩ := hGH
      obtain ⟨ψ, hψ⟩ := hHK
      exact ⟨ψ * φ, by rw [hc2, hφ, hψ]⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro G
      rw [hiffOP]
      exact ⟨1, AffFacts.det_one d, hc1 _⟩
    · intro G H hGH
      rw [hiffOP] at hGH ⊢
      obtain ⟨φ, hpos, hφ⟩ := hGH
      exact ⟨φ⁻¹, by rw [AffFacts.det_inv]; exact inv_pos.mpr hpos,
        by rw [← hφ, ← hc2, inv_mul_cancel, hc1]⟩
    · intro G H K hGH hHK
      rw [hiffOP] at hGH hHK ⊢
      obtain ⟨φ, hposφ, hφ⟩ := hGH
      obtain ⟨ψ, hposψ, hψ⟩ := hHK
      exact ⟨ψ * φ, by rw [AffFacts.det_mul]; exact mul_pos hposψ hposφ,
        by rw [hc2, hφ, hψ]⟩
  · intro G H hGH hG g hg
    rw [hiffAE] at hGH
    obtain ⟨φ, hφ⟩ := hGH
    have hmem : g.toAffineEquiv ∈ AffFacts.affImage H := ⟨g, hg, rfl⟩
    rw [← hφ] at hmem
    obtain ⟨x, hx, hxeq⟩ := hmem
    obtain ⟨g', hg', rfl⟩ := hx
    show 0 < ((g.toAffineEquiv).linear.det : ℝ)
    rw [hxeq, AffFacts.det_conj]
    exact hG g' hg'

end Work.SG
