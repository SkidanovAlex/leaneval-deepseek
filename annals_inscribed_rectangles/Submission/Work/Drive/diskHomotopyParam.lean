import Mathlib
import Submission.Work.Drive.diskLiftHomotopy

/-!
# A *parameter-rich* perturbation of the disk homotopy lift

The (B) half of the ends clause builds its homotopy from a lift of the form
`diskHomotopyLift V W χ p` (`diskLiftHomotopy.lean`), whose only free parameter is the single vector
`p : Eucl 3`.  The **admissibility** half (the `Meet3Hyp` clauses of `HasClassLinearization`) needs a
*family* of homotopies with a parameter space rich enough for a Sard argument: by
`Work.Drive.exists_meet3Hyp_of_good_family` it suffices to have a smooth family
`G : ℝ^N → Fin 3 → ℝ³ → M` of triples of `3`-chains with a parameter-derivative that is onto at every
zero of the charted difference map (`hsurj`), and `hsurj` needs the perturbation to move **all three**
blocks (see `ENCODED_ADMISSIBILITY_STATUS.md` §2bis).

This file only *defines* the family's lift: the extra terms

> `∑ i, (smoothPhi q.1 * t i * X i (sqDisk (foldBox q.2))) • E i`

are supported in the interior of the time interval (`smoothPhi` vanishes for `q.1 < 1/4` and
`q.1 > 3/4`), so the two endpoints of the homotopy are untouched, and they are **anti-equivariant on the
seam** whenever the weights `X i` are odd on the unit circle — which is what keeps the class map of the
perturbed homotopy seam-invariant.  Both facts are the subject of the lemmas below (delegated).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section


/-- **The parameter-rich perturbation of the disk homotopy lift.**  `t` is the extra parameter, `X i`
the (odd, on the circle) weights and `E i` the perturbation directions.  At `t = 0` the perturbation
vanishes, so the endpoints and the base homotopy are those of `diskHomotopyLift`. -/
def diskHomotopyLiftParam {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (t : Fin N → ℝ)
    (q : ℝ × EuclideanSpace ℝ (Fin 2)) : Eucl 3 :=
  diskHomotopyLift V W χ p q
    + ∑ i : Fin N, (smoothPhi q.1 * t i * X i (sqDisk (foldBox q.2))) • E i

/-- At `t = 0` the perturbation vanishes. -/
lemma diskHomotopyLiftParam_zero {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (q : ℝ × EuclideanSpace ℝ (Fin 2)) :
    diskHomotopyLiftParam V W χ p X E (0 : Fin N → ℝ) q = diskHomotopyLift V W χ p q := by
  simp [diskHomotopyLiftParam]

/-- **The endpoints of the parameter-rich homotopy are those of `diskHomotopyLift`**, for *every*
parameter: the extra terms carry the factor `smoothPhi`, which vanishes at `q.1 = 0` and `q.1 = 1`. -/
lemma diskHomotopyLiftParam_endpoints {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (t : Fin N → ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    diskHomotopyLiftParam V W χ p X E t (0, y) = V (sqDisk (foldBox y)) ∧
    diskHomotopyLiftParam V W χ p X E t (1, y) = W (sqDisk (foldBox y)) := by
  constructor
  · simp [diskHomotopyLiftParam, diskHomotopyLift, smoothSigma_zero, smoothPhi_zero]
  · simp [diskHomotopyLiftParam, diskHomotopyLift, smoothSigma_one, smoothPhi_one]

/-- **The parameter-rich lift is anti-equivariant on the seam**, for every parameter: the base lift
flips (all three of `V`, `W`, `χ` are odd on the circle) and so does the perturbation (the weights
`X i` are odd there, and `sqDisk` flips the sign on the seam).  This is what keeps the class map of
the perturbed homotopy seam-invariant, i.e. the `hseam` hypothesis of
`Work.Drive.exists_meet3Hyp_of_good_family`. -/
lemma diskHomotopyLiftParam_seam {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3)
    (hVodd : ∀ z : ℂ, ‖z‖ = 1 → V (-z) = - V z)
    (hWodd : ∀ z : ℂ, ‖z‖ = 1 → W (-z) = - W z)
    (hχodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = - χ z)
    (hXodd : ∀ (i : Fin N) (z : ℂ), ‖z‖ = 1 → X i (-z) = - X i z)
    (t : Fin N → ℝ) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (hy : onSeam2 y) :
    diskHomotopyLiftParam V W χ p X E t (s, seamInv2 y)
      = - diskHomotopyLiftParam V W χ p X E t (s, y) := by
  have hbox : foldBox y ∈ Submission.Drive.unitBox 1 := foldBox_mem_unitBox y
  have hnorm : ‖sqDisk (foldBox y)‖ = 1 :=
    (norm_sqDisk_eq_one_iff _ hbox).mpr (onSeam2_foldBox hy)
  have hθ : sqDisk (foldBox (seamInv2 y)) = - sqDisk (foldBox y) := by
    rw [foldBox_seamInv2, sqDisk_seamInv]
  have hbase : diskHomotopyLift V W χ p (s, seamInv2 y) = - diskHomotopyLift V W χ p (s, y) := by
    simp only [diskHomotopyLift, hθ, hVodd _ hnorm, hWodd _ hnorm, hχodd _ hnorm]
    module
  have hsum : (∑ i : Fin N, (smoothPhi s * t i * X i (sqDisk (foldBox (seamInv2 y)))) • E i)
      = - ∑ i : Fin N, (smoothPhi s * t i * X i (sqDisk (foldBox y))) • E i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hθ, hXodd i _ hnorm]
    have hcoef : smoothPhi s * t i * -X i (sqDisk (foldBox y))
        = -(smoothPhi s * t i * X i (sqDisk (foldBox y))) := by ring
    rw [hcoef, neg_smul]
  rw [diskHomotopyLiftParam, diskHomotopyLiftParam, hbase, hsum, neg_add]

/-- **Joint smoothness of the parameter-rich lift** in the parameter `t` and the point `q`. -/
lemma contDiff_diskHomotopyLiftParam {N : ℕ} (V W : ℂ → Eucl 3) (χ : ℂ → ℝ)
    (X : Fin N → ℂ → ℝ) (E : Fin N → Eucl 3) (p : Eucl 3)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hX : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Fin N → ℝ) × (ℝ × EuclideanSpace ℝ (Fin 2)) =>
        diskHomotopyLiftParam V W χ p X E z.1 z.2) := by
  have hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Fin N → ℝ) × (ℝ × EuclideanSpace ℝ (Fin 2)) =>
        sqDisk (foldBox z.2.2)) :=
    sqDisk_contDiff.comp (((contMDiff_iff_contDiff.mp foldBox_contMDiff).comp
      (contDiff_snd.snd)))
  have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Fin N → ℝ) × (ℝ × EuclideanSpace ℝ (Fin 2)) =>
        diskHomotopyLift V W χ p z.2) :=
    (contDiff_diskHomotopyLift V W χ p hV hW hχ).comp contDiff_snd
  have hterm : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Fin N → ℝ) × (ℝ × EuclideanSpace ℝ (Fin 2)) =>
        (smoothPhi z.2.1 * z.1 i * X i (sqDisk (foldBox z.2.2))) • E i) := by
    intro i
    exact (((contDiff_smoothPhi.comp contDiff_snd.fst).mul
      ((contDiff_apply ℝ ℝ i).comp contDiff_fst)).mul ((hX i).comp hθ)).smul contDiff_const
  unfold diskHomotopyLiftParam
  exact hbase.add (ContDiff.sum (fun i _ => hterm i))

end

end Work.Drive
