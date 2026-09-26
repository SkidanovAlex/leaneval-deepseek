import Mathlib
import Submission.Work.Drive.Mono.JunctionGenB

/-!
# The repair of clause (c) of the junction bundle: `JunctionGenC`

`Work.Drive.Mono.JunctionGenB` (`Mono/JunctionGenB.lean`) restricts clause (c) of
`Work.Drive.Mono.JunctionGen` to the box sphere.  That is still too strong, and the data producer
`Work.Drive.Mono.exists_junctionGood_tiltData` was **refuted** for exactly this reason
(`Mono/NOTES_junctionGood_REFUTED.md`): `BoxGen ψ c σ s` does not exclude the surface from
*containing an arc of a box edge* at the level `s` — `CornerGen` is vacuous there — and along such
an arc clause (c) would force a *finite* `exc` to contain the `ℓ`-image of a segment, hence
`ℓ (edge direction) = 0`; three arcs in the three coordinate directions force `ℓ = 0`, contradicting
`ℓ ≠ 0` of `Work.Drive.Mono.TiltData`.

`Work.Drive.Mono.JunctionGenC` below is the repair prescribed by the design
(`Submission/Work/Drive/Final/NOTES_LEAD_grazes_L.md`, and `NOTES_junctionGood_REFUTED.md` §6):
clause (c) is restricted to the **closed slab**, where it is exactly what the trace analysis needs
(the only consumer applies it at a point of the trace strictly inside the slab) and where it is
vacuous as soon as the data has `EdgeFree` (the closed slab misses the surface's part on the box
edges).  It is implied by `JunctionGenB` (`junctionGenC_of_junctionGenB`), and it is monotone in the
exceptional set, so the disjoint-sphere bookkeeping can still enlarge `exc`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The repaired stratified genericity of the trace at the junctions.**

Clauses (a), (b), (d) of `Work.Drive.Mono.JunctionGenB` verbatim; clause (c) — the levels of the
carrier points of the box sphere with two extremal coordinates lie in `exc` — restricted to the
points of the **closed slab**. -/
def JunctionGenC (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h → ℓ z < lam →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      ℓ z ∈ (exc : Set ℝ)) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ℓ z ∈ (exc : Set ℝ))

/-- The canonical inclusion `exc ⊆ exc ∪ B` of `Finset`s, as sets. -/
theorem coe_subset_union (exc B : Finset ℝ) : (exc : Set ℝ) ⊆ ((exc ∪ B : Finset ℝ) : Set ℝ) := by
  intro x hx
  rw [Finset.mem_coe] at hx ⊢
  exact Finset.mem_union_left B hx

/-- **The repaired bundle is implied by the previous one** (the restriction of clause (c) to the
closed slab is a weakening). -/
theorem junctionGenC_of_junctionGenB {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hJ : JunctionGenB ψ s c σ u v h ℓ exc lam0 lam1) :
    JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1 :=
  ⟨hJ.1, hJ.2.1, fun z hz hzs hslab hext => hJ.2.2.1 z hz hzs hext, hJ.2.2.2⟩

/-- **`EdgeFree`**: the closed slab misses the surface's part on the box edges — the design's
condition (`NOTES_LEAD_grazes_L.md`) under which clause (c) of `JunctionGenC` is vacuous.  A point of
the box sphere (`boxNorm = s`) with two extremal box coordinates lies on a box edge; `EdgeFree` puts
every such point strictly outside the closed slab.

The `boxNorm c σ z = s` antecedent is **not** cosmetic: on the *extended* edge lines (the two
extremal coordinates alone, the third free) there are carrier points arbitrarily far from `c` on
which the slab functional is small, so the unconditional form is not producible from a margin
(`Mono/g3EdgeFreeNegative.lean`, lead's 20:5x ruling).  Every consumer of `EdgeFree` evaluates it only
at box-sphere points (`boxNorm = s ∩ closure PBox`), so this is the honest hypothesis. -/
def EdgeFree (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) : Prop :=
  ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
    Submission.boxNorm c σ z = s →
    (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
    h < |inner ℝ v z - (inner ℝ v c + u)|

/-- **Under `EdgeFree`, clause (c) of `JunctionGenC` is automatic** (its hypothesis is empty: a
point of the closed slab with two extremal coordinates would contradict `EdgeFree`).  This is the
sense in which the design's `EdgeFree` *repairs* the bundle: the surplus that refuted
`Work.Drive.Mono.exists_junctionGood_tiltData` is not merely weakened but annihilated by the geometry
of the datum. -/
theorem junctionGenC_clauseC_of_edgeFree {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    (hEF : EdgeFree ψ s c σ u v h) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      ℓ z ∈ (exc : Set ℝ) :=
  fun z hz hbox hslab hext => absurd (hEF z hz hbox hext) (not_lt.mpr hslab)

/-- **`JunctionGenC` is monotone in `exc`.** -/
theorem junctionGenC_mono_exc {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc B : Finset ℝ}
    {lam0 lam1 : ℝ} (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1) :
    JunctionGenC ψ s c σ u v h ℓ (exc ∪ B) lam0 lam1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam hlam hne
    exact h1 lam hlam (fun hmem => hne (coe_subset_union exc B hmem))
  · intro lam hlam hne
    exact h2 lam hlam (fun hmem => hne (coe_subset_union exc B hmem))
  · intro z hz hzs hslab hext
    exact Finset.mem_union_left B (h3 z hz hzs hslab hext)
  · intro z hz hzs hface
    exact Finset.mem_union_left B (h4 z hz hzs hface)

end

end Work.Drive.Mono
