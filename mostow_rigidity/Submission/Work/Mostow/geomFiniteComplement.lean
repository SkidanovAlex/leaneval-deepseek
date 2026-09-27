import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.thinTubeDefs
import Submission.Work.Mostow.exists_closest_orbit

/-! # Area C1 (geomFinite) — complement cocompactness (L17)

For a lattice `Γ` and a `Γ`-equivariant cusp height `ht` on `parFixed Γ`, the complement of the
horoballs `{horoball ξ (ht ξ)}` is `Γ`-cocompact.

The reduction to the Dirichlet set is carried out here: an orbit point closest to `0`
(`Work.Mostow.exists_closest_orbit`) lies in `Dirichlet Γ`, and because the horoball family is
`Γ`-invariant (`heq`), it is still outside every horoball.  The remaining geometric content —
that a **Dirichlet** point outside every horoball is bounded — is the input `hdir`
(the escape analysis: `Work.Mostow.L14/L15` + HL + the chimney `L16`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Every `Γ`-orbit meets the Dirichlet set: the orbit point closest to `0` is Dirichlet. -/
theorem dirichlet_nonempty (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdis : IsDiscrete (SetLike.coe Γ)) (u : E n) :
    ∃ γ : Γ, (γ : PO n 1) • u ∈ Dirichlet Γ := by
  obtain ⟨γ, hγ⟩ := exists_closest_orbit n hA hI hdis u 0
  refine ⟨γ, ?_⟩
  intro δ
  have h := hγ (δ * γ)
  change hdist (0 : E n) ((γ : PO n 1) • u) ≤
    hdist (0 : E n) ((δ : PO n 1) • ((γ : PO n 1) • u))
  have hmul : ((δ * γ : Γ) : PO n 1) • u = (δ : PO n 1) • ((γ : PO n 1) • u) := by
    simpa using hA.2.2.2.2.1 (δ : PO n 1) (γ : PO n 1) u
  rw [hmul] at h
  exact h

/-- Complement cocompactness for a `Γ`-equivariant height, reduced to the Dirichlet set. -/
theorem complement_cocompact (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdis : IsDiscrete (SetLike.coe Γ))
    (ht : E n → ℝ) (heq : IsEquivHeight Γ (parFixed Γ) ht)
    (hdir : ∃ R : ℝ, ∀ z : E n, z ∈ Dirichlet Γ →
        (∀ ξ ∈ parFixed Γ, z ∉ horoball ξ (ht ξ)) → hdist (0 : E n) z ≤ R) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
      (∀ ξ ∈ parFixed Γ, u ∉ horoball ξ (ht ξ)) → ∃ γ : Γ, (γ : PO n 1) • u ∈ K := by
  have hA' := hA
  obtain ⟨hcen, hact, hbdO, hone, hsmul, hfaith, hcontAct, hbdSph, hbdone, hbdmul, hcontBd,
    hmeas⟩ := hA'
  have hcomp : ∀ u : E n, ∀ r : ℝ, IsCompact {v : E n | hdist u v ≤ r} := hI.2.2.2.2.2.1
  obtain ⟨R, hR⟩ := hdir
  refine ⟨{z : E n | hdist (0 : E n) z ≤ R}, hcomp 0 R, ?_⟩
  intro u hu
  obtain ⟨γ, hγ⟩ := dirichlet_nonempty hA hI Γ hdis u
  refine ⟨γ, ?_⟩
  have hout : ∀ η ∈ parFixed Γ, ((γ : PO n 1) • u) ∉ horoball η (ht η) := by
    intro η hη
    have hηS : η ∈ Sph n := hη.1
    set ξ : E n := bd (((γ⁻¹ : Γ) : PO n 1)) η with hξdef
    have hξP : ξ ∈ parFixed Γ := by
      rw [hξdef]; exact parFixed_invariant hA hI Γ (γ⁻¹) hη
    have hbd : bd (γ : PO n 1) ξ = η := by
      rw [hξdef, ← hbdmul (γ : PO n 1) (((γ⁻¹ : Γ) : PO n 1)) η hηS]
      have h1 : (γ : PO n 1) * (((γ⁻¹ : Γ) : PO n 1)) = 1 := by
        rw [show (((γ⁻¹ : Γ) : PO n 1)) = (γ : PO n 1)⁻¹ from rfl, mul_inv_cancel]
      rw [h1, hbdone η hηS]
    have heqv := horoball_equiv_of_height hA hI Γ (parFixed Γ) ht (fun ξ hξ => hξ.1) heq
      γ ξ hξP u
    rw [hbd] at heqv
    intro hcon
    exact hu ξ hξP (heqv.mp hcon)
  exact hR ((γ : PO n 1) • u) hγ hout

/-- `HasCuspHoroballs Γ` assembled from a `Γ`-equivariant, pairwise-disjoint cusp height and the
Dirichlet boundedness of its complement. -/
theorem hasCuspHoroballs_of (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdis : IsDiscrete (SetLike.coe Γ)) (ht : E n → ℝ)
    (heq : IsEquivHeight Γ (parFixed Γ) ht)
    (hdisj : (parFixed Γ).Pairwise
      (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η))))
    (hdir : ∃ R : ℝ, ∀ z : E n, z ∈ Dirichlet Γ →
        (∀ ξ ∈ parFixed Γ, z ∉ horoball ξ (ht ξ)) → hdist (0 : E n) z ≤ R) :
    HasCuspHoroballs Γ :=
  ⟨ht, heq, hdisj, complement_cocompact hA hI Γ hdis ht heq hdir⟩

end

end Work.Mostow
