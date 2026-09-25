import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep
import Submission.Work.BourgainPlan.IonescuWainger.sigmaSubA_add
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset

namespace Work.BourgainPlan.Maximal

open Finset
open Work.BourgainPlan.IonescuWainger (sigmaSubAFinset sigmaLeFinset QA arcPt zsmul_arcPt_eq_zero
  exists_arcPt_of_zsmul_eq_zero arcPt_emod_toNat)

/-- **The torsion arcs `Σ_{⊆ A} = 𝕋[Q_A]` are the `Q_A`-torsion subgroup of the circle**, for the
`Finset` version `sigmaSubAFinset`, under the single hypothesis `Q_A ≠ 0`.

The landed `mem_sigmaSubAFinset_iff_zsmul_eq_zero` states the same with the hypothesis
`∀ q ∈ A, 2 ≤ q`, which is used only to obtain `Q_A ≠ 0`; for an arbitrary subset `A` of
`taoSetS ρ N` that hypothesis is not available, so we restate it. -/
lemma mem_sigmaSubAFinset_iff_zsmul_eq_zero' {A : Finset ℕ} (hQ : QA A ≠ 0)
    (β : Work.BourgainPlan.IonescuWainger.Circle) :
    β ∈ sigmaSubAFinset A ↔ (QA A : ℤ) • β = 0 := by
  constructor
  · intro h
    simp only [sigmaSubAFinset, Finset.mem_image] at h
    obtain ⟨a, -, rfl⟩ := h
    exact zsmul_arcPt_eq_zero hQ dvd_rfl
  · intro h
    obtain ⟨n, hn⟩ := exists_arcPt_of_zsmul_eq_zero hQ h
    have hQpos : (0 : ℤ) < (QA A : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hQ
    have hnonneg : 0 ≤ n % (QA A : ℤ) := Int.emod_nonneg n (ne_of_gt hQpos)
    have hlt : n % (QA A : ℤ) < (QA A : ℤ) := Int.emod_lt_of_pos n hQpos
    simp only [sigmaSubAFinset, Finset.mem_image]
    exact ⟨(n % (QA A : ℤ)).toNat,
      Finset.mem_range.mpr ((Int.toNat_lt hnonneg).mpr hlt),
      by rw [arcPt_emod_toNat hQ n]; exact hn.symm⟩

/-- **Negation preserves each torsion arc `Σ_{⊆ A}`**: `-β ∈ Σ_{⊆ A} ↔ β ∈ Σ_{⊆ A}`.  (For
`Q_A = 0` the arc is empty — `range 0 = ∅` — so both sides are false.) -/
lemma neg_mem_sigmaSubAFinset (A : Finset ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle) :
    -β ∈ sigmaSubAFinset A ↔ β ∈ sigmaSubAFinset A := by
  rcases eq_or_ne (QA A) 0 with h0 | h0
  · simp [sigmaSubAFinset, h0]
  · rw [mem_sigmaSubAFinset_iff_zsmul_eq_zero' h0 (-β),
      mem_sigmaSubAFinset_iff_zsmul_eq_zero' h0 β, smul_neg, neg_eq_zero]

/-- The MST level arc set `mstU l n = iwSigma (mstRho l) (n^l)` (Tao's Ionescu–Wainger superset
`Σ_{n^l}`, a union of torsion subgroups `𝕋[Q_A]`) is invariant under negation of the circle:
`-β ∈ mstU l n ↔ β ∈ mstU l n`, i.e. the reflection `β ↦ -β` is a bijection of the level set. -/
theorem neg_mstU (l n : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle) :
    -β ∈ Work.BourgainPlan.Maximal.mstU l n ↔ β ∈ Work.BourgainPlan.Maximal.mstU l n := by
  rw [mstU_apply, iwSigma, sigmaLeFinset]
  simp only [Finset.mem_biUnion]
  exact exists_congr fun A => and_congr_right fun _ => neg_mem_sigmaSubAFinset A β

end Work.BourgainPlan.Maximal
