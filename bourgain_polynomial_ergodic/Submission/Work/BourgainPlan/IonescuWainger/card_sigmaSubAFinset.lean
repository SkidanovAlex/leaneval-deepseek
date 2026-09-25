import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs

namespace Work.BourgainPlan.IonescuWainger

/-- The map `a ↦ a/Q` is injective on the numerators `{0, …, Q-1}`: two such points of the circle
`𝕋 = ℝ/ℤ` coincide only if their numerators are congruent modulo `Q` (`arcPt_eq_arcPt_iff_dvd`),
and two distinct numerators in `[0, Q)` differ by a nonzero integer of absolute value `< Q`. -/
private lemma arcPt_injOn_range {Q : ℕ} (hQ : Q ≠ 0) :
    Set.InjOn (fun a : ℕ => arcPt Q (a : ℤ)) ↑(Finset.range Q) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  have hdvd : (Q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := (arcPt_eq_arcPt_iff_dvd hQ a b).mp hab
  have hlt : |((a : ℤ) - (b : ℤ))| < (Q : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have h0 : (a : ℤ) - (b : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  have hab' : (a : ℤ) = (b : ℤ) := by omega
  omega

/-- **The cardinality of `Σ_{⊆A} = 𝕋[Q_A]`**: the `Q_A` points `a/Q_A` (`a < Q_A`) of the circle are
pairwise distinct, so the `Finset` `sigmaSubAFinset A` has exactly `Q_A` elements.  This is the
elementary counting input of Tao's "arithmetic limit" estimates for the major arcs
(`ortho-apply`(i), the `2^k` counting bound). -/
theorem card_sigmaSubAFinset (A : Finset ℕ) : (sigmaSubAFinset A).card = QA A := by
  rcases eq_or_ne (QA A) 0 with hQ | hQ
  · simp [sigmaSubAFinset, hQ]
  · refine (Finset.card_image_of_injOn (arcPt_injOn_range hQ)).trans (Finset.card_range _)

end Work.BourgainPlan.IonescuWainger
