import Mathlib
import Submission.Work.Drive.diskHomotopyParam
import Submission.Work.Drive.exists_small_diskHomotopyLiftParam_ne_zero
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.contMDiffAt_cappingVecPoint_general
import Submission.Work.Drive.diskHomotopyChain

/-!
# The parameter-rich class homotopy (part (ii) of the admissibility half of the ends clause)

`Work.Drive.diskHomotopyLiftParam` (`diskHomotopyParam.lean`) perturbs the disk-homotopy lift
`diskHomotopyLift` by terms `∑ i, (smoothPhi q.1 * t i * X i (sqDisk (foldBox q.2))) • E i` supported
in the interior of the time interval.  Its nonvanishing holds only for parameters `t` of norm below a
threshold `δ > 0` (`Work.Drive.exists_small_diskHomotopyLiftParam_ne_zero`), while the parametric-Sard
engine `Work.Drive.exists_meet3Hyp_of_good_family` asks for a family defined and jointly `C^∞` on *all*
of `ℝ^N × ℝ³`.

This file closes that gap:

* `Work.Drive.paramClamp` — the smooth clamp `t ↦ (δ/2 * (1 + ∑ i, t i ^ 2)⁻¹) • t`, a map
  `EuclideanSpace ℝ (Fin N) → (Fin N → ℝ)` whose values all have norm `< δ` (it is the standard smooth
  radial clamp; the ℓ²-norm squared of the source is a polynomial, so no non-smooth norm appears);
* **`Work.Drive.exists_diskClassHomotopyParam`** — the resulting *parameter-rich* class homotopy
  `H : ℝ^N → ℝ × ℝ² → ℝP³`, with the two endpoints of the base homotopy (for **every** parameter), the
  seam invariance, continuity in the point, joint `C^∞`-smoothness of the chain
  `(t, x) ↦ H t (x 2, mk2 (x 0) (x 1))`, and the pointwise smoothness of each slice's chain.

**Status of the family (read `ENDS_A_OBSTRUCTION.md` first).**  This module was written for the
parametrised-Sard route to the transversality half (`Meet3Hyp` of the *encoded* chains,
`ENCODED_ADMISSIBILITY_STATUS.md` §3bis); that route is **refuted**: the machine's hypothesis `hsurj` is
unsatisfiable for every family of encoded triples (the level coordinates of blocks `1`, `2` are box
coordinates, immovable by any parameter, and block `0` moves its level only through the single number
`c t`) — see `Submission/Work/Drive/ENDS_A_OBSTRUCTION.md` and the machine-checked
`Work.Drive.not_surjective_hsurj_encodedChains_family`
(`Submission/Work/Drive/encodedHsurjObstruction.lean`).  What survives, and what this module is
therefore *for*:

* the **clamp** `paramClamp` and the **joint smoothness** of a family of class homotopies (the analytic
  input of any genericity argument that varies the homotopy), for the *corrected* route of
  `ENDS_A_OBSTRUCTION.md` §3, whose condition (1) — the homotopy chain must be a **submersion** at the
  triple points — is a statement about the *spatial* derivative, where the level direction is reachable;
* the non-vanishing half (`exists_small_diskHomotopyLiftParam_ne_zero`) and the seam/endpoint lemmas,
  which are independent of the refuted route.

The four `contMDiff_chain_param_*` lemmas below are correct and axiom-clean but are on that refuted path
for the *encoded* family; they remain the right shape for a family of homotopies.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- The product smooth structure on `ℝP³ × ℝ` (model `ℝ³ × ℝ`), the one from which
`Work.Drive.projTimesLineCharted` is obtained by the linear model change `Work.Drive.psiLin`. -/
local instance instProdChartedPlaneLevelH4 :
    ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  exact prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-! ## 1. The smooth radial clamp -/

/-- **The smooth radial clamp.**  `paramClamp δ t` has all values of norm `< δ` (see
`norm_paramClamp_lt`), is smooth in `t`, and equals `t` for `t` near `0` up to the factor `δ / 2`
— precisely, `paramClamp δ t = (δ / 2 * (1 + ∑ i, t i ^ 2)⁻¹) • t`, so it is *not* required to be a
retraction, only to land in the ball. -/
def paramClamp {N : ℕ} (δ : ℝ) (t : EuclideanSpace ℝ (Fin N)) : Fin N → ℝ :=
  fun i => (δ / 2 * (1 + ∑ j, (t j) ^ 2)⁻¹) * t i

/-- **Smoothness of the clamp.** -/
lemma contDiff_paramClamp {N : ℕ} (δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (paramClamp (N := N) δ) := by
  rw [contDiff_pi]
  intro i
  have hproj : ∀ j : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : EuclideanSpace ℝ (Fin N) => t j) :=
    fun j => (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  have hsq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : EuclideanSpace ℝ (Fin N) => ∑ j, (t j) ^ 2) := by
    refine ContDiff.sum (fun j _ => ?_)
    exact (hproj j).pow 2
  have hne : ∀ t : EuclideanSpace ℝ (Fin N), (1 + ∑ j, (t j) ^ 2) ≠ 0 := by
    intro t
    have h0 : 0 ≤ ∑ j, (t j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    positivity
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : EuclideanSpace ℝ (Fin N) => (1 + ∑ j, (t j) ^ 2)⁻¹) :=
    (contDiff_const.add hsq).inv hne
  exact ((contDiff_const.mul hinv).mul (hproj i))

/-- The coordinate bound `‖t i‖ ≤ ‖t‖` for the Euclidean norm (the ℓ²-norm of `PiLp`). -/
lemma norm_proj_le {N : ℕ} (t : EuclideanSpace ℝ (Fin N)) (i : Fin N) : ‖t i‖ ≤ ‖t‖ := by
  have h1 : ‖t.ofLp i‖ ^ 2 ≤ ∑ j, ‖t.ofLp j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖t.ofLp j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (t i))]
  exact Real.sqrt_le_sqrt h1

/-- **The clamp lands in the half-ball.** -/
lemma norm_paramClamp_le {N : ℕ} (δ : ℝ) (hδ : 0 ≤ δ) (t : EuclideanSpace ℝ (Fin N)) :
    ‖paramClamp (N := N) δ t‖ ≤ δ / 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : paramClamp (N := 0) δ t = 0 := by
      funext i; exact Fin.elim0 i
    rw [h0, norm_zero]
    linarith
  · haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    set S : ℝ := ∑ j, (t j) ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hden : 0 < 1 + S := by linarith
    have hc : 0 ≤ δ / 2 * (1 + S)⁻¹ := by positivity
    have hsum : (∑ j, ‖t.ofLp j‖ ^ 2) = S := by
      rw [hS]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Real.norm_eq_abs, sq_abs]
    have hti : ‖t i‖ ≤ Real.sqrt S := by
      have h := norm_proj_le t i
      rw [EuclideanSpace.norm_eq, hsum] at h
      exact h
    have hs : Real.sqrt S ≤ 1 + S := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hfi : ‖paramClamp (N := N) δ t i‖ = (δ / 2 * (1 + S)⁻¹) * ‖t i‖ := by
      simp only [paramClamp, ← hS]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, Real.norm_eq_abs]
    rw [hfi]
    have h1 : (δ / 2 * (1 + S)⁻¹) * ‖t i‖ ≤ (δ / 2 * (1 + S)⁻¹) * Real.sqrt S :=
      mul_le_mul_of_nonneg_left hti hc
    have h2 : (δ / 2 * (1 + S)⁻¹) * Real.sqrt S ≤ (δ / 2 * (1 + S)⁻¹) * (1 + S) :=
      mul_le_mul_of_nonneg_left hs hc
    have h3 : (δ / 2 * (1 + S)⁻¹) * (1 + S) = δ / 2 := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hden), mul_one]
    linarith [h1, h2, h3.le, h3.ge]

/-- **The clamp is strictly inside the ball.** -/
lemma norm_paramClamp_lt {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (t : EuclideanSpace ℝ (Fin N)) :
    ‖paramClamp (N := N) δ t‖ < δ :=
  lt_of_le_of_lt (norm_paramClamp_le δ hδ.le t) (by linarith)

/-! ## 2. The parameter-rich class homotopy -/

/-- **The parameter-rich class homotopy.**  The parameter-rich perturbation of the disk-homotopy lift
(`diskHomotopyParam.lean`), with the parameter smoothly clamped into the ball of radius `δ` on which the
perturbed lift is nonvanishing (`exists_small_diskHomotopyLiftParam_ne_zero`), defines a *total* family
of class homotopies of `ℝ^N`:

* both endpoints of the disk homotopy `diskHomotopyLift` are attained for **every** parameter `t` (the
  perturbation is supported in the interior of the time interval);
* the family is invariant under the antipodal involution of the square on the whole seam (all the weights
  are odd on the boundary circle), which is the `hseam` input of the Sard engine;
* each slice's chain `x ↦ H t (x 2, mk2 (x 0) (x 1))` is `C^∞` into `ℝP³`, and the *joint* chain
  `(t, x) ↦ H t (x 2, mk2 (x 0) (x 1))` is `C^∞` on `ℝ^N × ℝ³` — this is the joint smoothness `hG`
  of `Work.Drive.exists_meet3Hyp_of_good_family`. -/
theorem exists_diskClassHomotopyParam {N : ℕ}
    (D E : ℂ → CappingSpace) (V W : ℂ → Eucl 3) (χ : ℂ → ℝ) (p : Eucl 3)
    (X : Fin N → ℂ → ℝ) (E' : Fin N → Eucl 3)
    (hVsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hXsm : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X i))
    (hVne : ∀ z : ℂ, V z ≠ 0) (hWne : ∀ z : ℂ, W z ≠ 0)
    (hVcls : IsClassLift D V hVne) (hWcls : IsClassLift E W hWne)
    (hVodd : ∀ z : ℂ, ‖z‖ = 1 → V (-z) = - V z)
    (hWodd : ∀ z : ℂ, ‖z‖ = 1 → W (-z) = - W z)
    (hχodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = - χ z)
    (hXodd : ∀ (i : Fin N) (z : ℂ), ‖z‖ = 1 → X i (-z) = - X i z)
    (hnz : DiskGood V W χ p) :
    ∃ H : EuclideanSpace ℝ (Fin N) → ℝ × EuclideanSpace ℝ (Fin 2) →
        Projectivization ℝ (Eucl 3),
      (∀ (t : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin 2)),
        H t (0, y) = planeClassMap (diskPlane D) y) ∧
      (∀ (t : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin 2)),
        H t (1, y) = planeClassMap (diskPlane E) y) ∧
      (∀ (t : EuclideanSpace ℝ (Fin N)) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        onSeam2 y → H t (s, seamInv2 y) = H t (s, y)) ∧
      (∀ t : EuclideanSpace ℝ (Fin N),
        ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin 3) => H t (x 2, mk2 (x 0) (x 1)))) ∧
      (ContMDiff (modelWithCornersSelf ℝ
          (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
        (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)))) ∧
      (∀ t : EuclideanSpace ℝ (Fin N), Continuous (H t)) := by
  obtain ⟨δ, hδpos, hne⟩ :=
    exists_small_diskHomotopyLiftParam_ne_zero V W χ p X E' hVsm hWsm hχsm hXsm hVne hWne hnz
  refine ⟨fun t q => Projectivization.mk ℝ
    (diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) q)
    (hne (paramClamp δ t) (norm_paramClamp_lt δ hδpos t) q), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t y
    rw [planeClassMap_diskPlane_of_lift hVcls y, Projectivization.mk_eq_mk_iff]
    exact ⟨1, by
      rw [(diskHomotopyLiftParam_endpoints V W χ p X E' (paramClamp δ t) y).1]
      simp⟩
  · intro t y
    rw [planeClassMap_diskPlane_of_lift hWcls y, Projectivization.mk_eq_mk_iff]
    exact ⟨1, by
      rw [(diskHomotopyLiftParam_endpoints V W χ p X E' (paramClamp δ t) y).2]
      simp⟩
  · intro t s y hy
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨(-1 : ℝˣ), by
      rw [diskHomotopyLiftParam_seam V W χ p X E' hVodd hWodd hχodd hXodd (paramClamp δ t) s y hy]
      simp⟩
  · intro t x
    have hne_t : ∀ q : ℝ × EuclideanSpace ℝ (Fin 2),
        diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) q ≠ 0 :=
      fun q => hne (paramClamp δ t) (norm_paramClamp_lt δ hδpos t) q
    have hθ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => sqDisk (foldBox (mk2 (x 0) (x 1)))) :=
      contDiff_comp_mk2 (sqDisk_contDiff.comp (contMDiff_iff_contDiff.mp foldBox_contMDiff))
    have hσ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => smoothSigma (x 2)) :=
      contDiff_smoothSigma.comp coordCLM2.contDiff
    have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => smoothPhi (x 2)) :=
      contDiff_smoothPhi.comp coordCLM2.contDiff
    have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          diskHomotopyLift V W χ p (x 2, mk2 (x 0) (x 1))) := by
      have heq : (fun x : EuclideanSpace ℝ (Fin 3) =>
            diskHomotopyLift V W χ p (x 2, mk2 (x 0) (x 1)))
          = fun x => (1 - smoothSigma (x 2)) • V (sqDisk (foldBox (mk2 (x 0) (x 1))))
              + smoothSigma (x 2) • W (sqDisk (foldBox (mk2 (x 0) (x 1))))
              + (smoothPhi (x 2) * χ (sqDisk (foldBox (mk2 (x 0) (x 1))))) • p := rfl
      rw [heq]
      exact (((contDiff_const.sub hσ').smul (hVsm.comp hθ')).add
        (hσ'.smul (hWsm.comp hθ'))).add
        ((hφ'.mul (hχsm.comp hθ')).smul contDiff_const)
    have hterm : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          (smoothPhi (x 2) * (paramClamp δ t) i * X i (sqDisk (foldBox (mk2 (x 0) (x 1))))) •
            E' i) :=
      fun i => ((hφ'.mul contDiff_const).mul ((hXsm i).comp hθ')).smul contDiff_const
    have hlift : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) (x 2, mk2 (x 0) (x 1))) x := by
      have heq : (fun x : EuclideanSpace ℝ (Fin 3) =>
            diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) (x 2, mk2 (x 0) (x 1)))
          = fun x => diskHomotopyLift V W χ p (x 2, mk2 (x 0) (x 1))
              + ∑ i, (smoothPhi (x 2) * (paramClamp δ t) i *
                  X i (sqDisk (foldBox (mk2 (x 0) (x 1))))) • E' i := rfl
      rw [heq]
      exact (hbase.add (ContDiff.sum (fun i _ => hterm i))).contDiffAt
    refine contMDiffAt_projMk_general (𝓡 3)
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) (x 2, mk2 (x 0) (x 1)))
      (fun x => hne_t _) x ?_
    rw [contMDiffAt_iff_contDiffAt]
    exact hlift
  · intro z
    have hcl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) => paramClamp δ z.1) :=
      (contDiff_paramClamp (N := N) δ).comp contDiff_fst
    have hcli : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          (paramClamp δ z.1) i) :=
      fun i => (contDiff_pi.mp hcl) i
    have hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          sqDisk (foldBox (mk2 (z.2 0) (z.2 1)))) :=
      (contDiff_comp_mk2
        (sqDisk_contDiff.comp (contMDiff_iff_contDiff.mp foldBox_contMDiff))).comp contDiff_snd
    have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) => smoothSigma (z.2 2)) :=
      contDiff_smoothSigma.comp (coordCLM2.contDiff.comp contDiff_snd)
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) => smoothPhi (z.2 2)) :=
      contDiff_smoothPhi.comp (coordCLM2.contDiff.comp contDiff_snd)
    have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          diskHomotopyLift V W χ p (z.2 2, mk2 (z.2 0) (z.2 1))) := by
      have heq : (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
            diskHomotopyLift V W χ p (z.2 2, mk2 (z.2 0) (z.2 1)))
          = fun z => (1 - smoothSigma (z.2 2)) • V (sqDisk (foldBox (mk2 (z.2 0) (z.2 1))))
              + smoothSigma (z.2 2) • W (sqDisk (foldBox (mk2 (z.2 0) (z.2 1))))
              + (smoothPhi (z.2 2) * χ (sqDisk (foldBox (mk2 (z.2 0) (z.2 1))))) • p := rfl
      rw [heq]
      exact (((contDiff_const.sub hσ).smul (hVsm.comp hθ)).add
        (hσ.smul (hWsm.comp hθ))).add
        ((hφ.mul (hχsm.comp hθ)).smul contDiff_const)
    have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          ∑ i, (smoothPhi (z.2 2) * (paramClamp δ z.1) i *
            X i (sqDisk (foldBox (mk2 (z.2 0) (z.2 1))))) • E' i) := by
      refine ContDiff.sum (fun i _ => ?_)
      exact ((hφ.mul (hcli i)).mul ((hXsm i).comp hθ)).smul contDiff_const
    have hliftsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          diskHomotopyLiftParam V W χ p X E' (paramClamp δ z.1) (z.2 2, mk2 (z.2 0) (z.2 1))) := by
      have heq : (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
            diskHomotopyLiftParam V W χ p X E' (paramClamp δ z.1) (z.2 2, mk2 (z.2 0) (z.2 1)))
          = fun z => diskHomotopyLift V W χ p (z.2 2, mk2 (z.2 0) (z.2 1))
              + ∑ i, (smoothPhi (z.2 2) * (paramClamp δ z.1) i *
                  X i (sqDisk (foldBox (mk2 (z.2 0) (z.2 1))))) • E' i := rfl
      rw [heq]
      exact hbase.add hsum
    have hne_z : ∀ z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3),
        diskHomotopyLiftParam V W χ p X E' (paramClamp δ z.1) (z.2 2, mk2 (z.2 0) (z.2 1)) ≠ 0 :=
      fun z => hne (paramClamp δ z.1) (norm_paramClamp_lt δ hδpos z.1) _
    refine contMDiffAt_projMk_general
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        diskHomotopyLiftParam V W χ p X E' (paramClamp δ z.1) (z.2 2, mk2 (z.2 0) (z.2 1)))
      hne_z z ?_
    rw [contMDiffAt_iff_contDiffAt]
    exact hliftsm.contDiffAt
  · intro t
    have hne_t : ∀ q : ℝ × EuclideanSpace ℝ (Fin 2),
        diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) q ≠ 0 :=
      fun q => hne (paramClamp δ t) (norm_paramClamp_lt δ hδpos t) q
    change Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => Projectivization.mk ℝ
      (diskHomotopyLiftParam V W χ p X E' (paramClamp δ t) q) (hne_t q))
    exact (continuous_projectivizationMk ℝ (Eucl 3)).comp
      (Continuous.subtype_mk
        ((contDiff_diskHomotopyLiftParam V W χ X E' p hVsm hWsm hχsm hXsm).comp
          (contDiff_const.prodMk contDiff_id)).continuous hne_t)

/-! ## 3. What is *not* here: the parameter-rich **chain** lemmas, and the model trap

The parametric-Sard engine `Work.Drive.exists_meet3Hyp_of_good_family` consumes, for each block
`k : Fin 3`, a family of chains `G t k : ℝ³ → M` with `M = ℝP³ × ℝ` carrying the *transported*
structure `Work.Drive.projTimesLineCharted` (model `ℝ⁴`), and asks for the joint `C^∞`-smoothness
`hG : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
(modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ (fun q => G q.1 k q.2)`.

The *natural* route to `hG` is the parameter-rich form of
`Work.Drive.contMDiff_chain_projTimesLine` / `..._plane` (`diskHomotopyChain.lean`):
the chain `(t, x) ↦ (H t (x 2, mk2 (x 0) (x 1)), c₀)` is smooth into the *product* structure on
`ℝP³ × ℝ` (from the joint smoothness delivered by `exists_diskClassHomotopyParam`, which is the
hypothesis `ContMDiff (self (ℝ^N × ℝ³)) (𝓡 3)` of the class-homotopy chain), and then the product
structure is converted to the transported one by `contMDiffWithinAt_chartedSpaceChangeModel'`.

**The formalisation trap (recorded so that the next attempt does not repeat it).**  The codomain of
`hG` with the *transported* model `𝓡 4` is fine (that is exactly the form
`diskHomotopyChain.lean` proves for a *single* homotopy, since its domain model is `𝓡 3`, not a
product).  The problem is the *intermediate* product step: `ContMDiff.prodMk` produces the model
`(𝓡 3).prod (modelWithCornersSelf ℝ ℝ)`, which is **not** syntactically
`modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)` (`ModelWithCorners.prod`'s model space is
`ModelProd (EuclideanSpace ℝ (Fin 3)) ℝ`, and the two `ChartedSpace` instances differ), so the goal
must be rewritten by `modelWithCornersSelf_prod`.  As soon as the *domain* model is itself a product
self-model — which it is here, `self (ℝ^N × ℝ³)` — that rewrite also fires on the domain and the
rewriting of a `ContMDiff` *hypothesis* then re-synthesizes the `ChartedSpace` instance (which fails),
while the `rw`-on-the-goal-only pattern changes the manifold type `M` of the domain
(`EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)` versus `ModelProd …`), so `exact` no longer
matches.  Two workable resolutions, neither attempted here:

* state the chain lemmas with the *product* domain model `(𝓡 N).prod (𝓡 3)` (no rewriting is then
  needed at all: `hH.prodMk contMDiff_const` closes the product form, and the transported form is
  reached through `contMDiffWithinAt_chartedSpaceChangeModel'` with `I := (𝓡 N).prod (𝓡 3)`), and
  convert the domain model **once**, at the consumer's `G`-family, where the family itself can be
  *defined* with the product domain model and the engine's `hG` hypothesis instantiated through the
  model equality;
* or prove `hG` pointwise from the charts, avoiding `ContMDiff.prodMk` altogether.

The mathematical content of §1–§2 below is independent of this bookkeeping: `exists_diskClassHomotopyParam`
already delivers the joint smoothness of the class homotopy on *all* of `ℝ^N × ℝ³`, which is the only
non-obvious input of either route. -/


/-! ## 3. The chain of the parameter-rich homotopy, into `ℝP³ × ℝ`

The parametric-Sard engine `Work.Drive.exists_meet3Hyp_of_good_family` consumes the family as chains
`G t k : ℝ³ → M` with `M = ℝP³ × ℝ` carrying the *transported* structure
`Work.Drive.projTimesLineCharted` (model `ℝ⁴`) and asks for the joint `C^∞`-smoothness
`hG : ContMDiff (modelWithCornersSelf ℝ (ℝ^N × ℝ³)) (modelWithCornersSelf ℝ (ℝ⁴)) ⊤ (fun q => G q.1 k q.2)`
of each block.  The four lemmas below are the parameter-rich forms of
`Work.Drive.contMDiff_chain_projTimesLine` / `..._plane` (`diskHomotopyChain.lean`) for the block `0`
(the homotopy chain, with parameter-dependent homotopy `H`) and for blocks `1`, `2` (a
parameter-dependent family of class maps `A`), in the product *and* the transported structure.

**Model convention (the one trap of this construction).**  Two model conventions occur, and both are
provided below: the *product* model `(𝓡 N).prod (𝓡 3)` on the domain (the `..._prodDomain` forms, whose
proofs need only `ContMDiff.prodMk` and `contMDiff_fst`/`contMDiff_snd`) and the *self* model
`modelWithCornersSelf ℝ (ℝ^N × ℝ³)` (the plain-named forms, which are the ones the Sard engine's `hG`
asks for).  The self-model forms are proved from the components given by
`ContinuousLinearMap.contMDiff` (stated for the self models) by converting the *codomain* model to the
product model with a **targeted** rewrite

```
conv in (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =>
  rw [modelWithCornersSelf_prod]
```

Rewriting the whole goal instead is what one must not do: `modelWithCornersSelf_prod` also matches the
*domain* model, and after rewriting it the inferred manifold type of the domain changes from
`ℝ^N × ℝ³` to `ModelProd …`, so the hypothesis no longer applies; and rewriting a `ContMDiff`
*hypothesis* re-synthesizes its `ChartedSpace` instance and fails. -/

section ProjTimesLineParam

attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-- **The chain of the parameter-rich homotopy, with the product structure on `ℝP³ × ℝ`.** -/
theorem contMDiff_chain_param_prodCharted_prodDomain {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff ((𝓡 N).prod (𝓡 3))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)))) :
    ContMDiff ((𝓡 N).prod (𝓡 3))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)), c₀)) := by
  rw [modelWithCornersSelf_prod]
  exact hH.prodMk contMDiff_const

/-- **The chain of the parameter-rich homotopy, jointly `C^∞` into the transported structure.** -/
theorem contMDiff_chain_param_projTimesLine_prodDomain {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff ((𝓡 N).prod (𝓡 3))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)))) :
    ContMDiff ((𝓡 N).prod (𝓡 3)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)), c₀)) := by
  unfold Work.Drive.projTimesLineCharted
  exact fun z => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
    (I := (𝓡 N).prod (𝓡 3))
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
      (H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)), c₀)) Set.univ z).mpr
      (contMDiff_chain_param_prodCharted_prodDomain H c₀ hH z)

/-- **The chain of a parameterised family of plane presentations**, with the product structure on
`ℝP³ × ℝ`: blocks `1`/`2` of the encoded chains, with a *parameter-dependent* class map `A`. -/
theorem contMDiff_chain_param_prodCharted_plane_prodDomain {N : ℕ}
    (A : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3))
    (hA : ContMDiff ((𝓡 N).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A)) :
    ContMDiff ((𝓡 N).prod (𝓡 3))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (A z.1 (mk2 (z.2 0) (z.2 1)), z.2 2)) := by
  have hcls : ContMDiff ((𝓡 N).prod (𝓡 3)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        A z.1 (mk2 (z.2 0) (z.2 1))) := by
    have hg : ContMDiff ((𝓡 N).prod (𝓡 3)) ((𝓡 N).prod (𝓡 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          (z.1, mk2 (z.2 0) (z.2 1))) :=
      (contMDiff_fst (I := 𝓡 N) (J := 𝓡 3)).prodMk
        ((mk2CLM.contDiff.contMDiff).comp (contMDiff_snd (I := 𝓡 N) (J := 𝓡 3)))
    simpa only [Function.comp_def, Function.uncurry] using hA.comp hg
  have hτ : ContMDiff ((𝓡 N).prod (𝓡 3)) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) => z.2 2) :=
    (coordCLM2.contDiff.contMDiff).comp (contMDiff_snd (I := 𝓡 N) (J := 𝓡 3))
  rw [modelWithCornersSelf_prod]
  exact hcls.prodMk hτ

/-- **The chain of a parameterised family of plane presentations, into the transported structure.** -/
theorem contMDiff_chain_param_projTimesLine_plane_prodDomain {N : ℕ}
    (A : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3))
    (hA : ContMDiff ((𝓡 N).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A)) :
    ContMDiff ((𝓡 N).prod (𝓡 3)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (A z.1 (mk2 (z.2 0) (z.2 1)), z.2 2)) := by
  unfold Work.Drive.projTimesLineCharted
  exact fun z => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
    (I := (𝓡 N).prod (𝓡 3))
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
      (A z.1 (mk2 (z.2 0) (z.2 1)), z.2 2)) Set.univ z).mpr
      (contMDiff_chain_param_prodCharted_plane_prodDomain A hA z)
end ProjTimesLineParam

attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-! ### 3bis. The engine-facing forms (self model on the domain)

`Work.Drive.exists_meet3Hyp_of_good_family` asks for the joint smoothness with the *self* model
`modelWithCornersSelf ℝ (ℝ^N × ℝ³)` on the domain.  The four lemmas below are the §3 lemmas in
exactly that form.  The codomain model is converted to the product model by a *targeted*
`conv in (modelWithCornersSelf ℝ (ℝ³ × ℝ)) => rw [modelWithCornersSelf_prod]` (rewriting the whole
goal would also rewrite the domain model and change the inferred manifold type `ℝ^N × ℝ³` into
`ModelProd …`), and the components are the continuous-linear-map smoothness lemmas
`ContinuousLinearMap.contMDiff` (which is stated for the self models, hence applicable here). -/

/-- **The chain of the parameter-rich homotopy** (self-model form, product structure on `ℝP³ × ℝ`). -/
theorem contMDiff_chain_param_prodCharted {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)))) :
    ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)), c₀)) := by
  conv in (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =>
    rw [modelWithCornersSelf_prod]
  exact hH.prodMk contMDiff_const

/-- **The chain of the parameter-rich homotopy into the transported structure** (self-model form) —
this is the `hG` of block `0` of the encoded chains. -/
theorem contMDiff_chain_param_projTimesLine {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) → ℝ × EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)))) :
    ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)), c₀)) := by
  unfold Work.Drive.projTimesLineCharted
  exact fun z => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
    (I := modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
      (H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)), c₀)) Set.univ z).mpr
      (contMDiff_chain_param_prodCharted H c₀ hH z)

/-- **The chain of a parameterised family of plane presentations** (self-model form, product structure
on `ℝP³ × ℝ`) — blocks `1`, `2` of the encoded chains, with a parameter-dependent class map `A`. -/
theorem contMDiff_chain_param_prodCharted_plane {N : ℕ}
    (A : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A)) :
    ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (A z.1 (mk2 (z.2 0) (z.2 1)), z.2 2)) := by
  have hcls : ContMDiff (modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        A z.1 (mk2 (z.2 0) (z.2 1))) := by
    have hg : ContMDiff (modelWithCornersSelf ℝ
          (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ
          (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 2)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          (z.1, mk2 (z.2 0) (z.2 1))) :=
      (((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N))
          (EuclideanSpace ℝ (Fin 3))).prod
        (mk2CLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N))
          (EuclideanSpace ℝ (Fin 3))))).contMDiff)
    simpa only [Function.comp_def, Function.uncurry] using hA.comp hg
  have hτ : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) => z.2 2) :=
    ((coordCLM2.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin N))
      (EuclideanSpace ℝ (Fin 3)))).contMDiff)
  conv in (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)) =>
    rw [modelWithCornersSelf_prod]
  exact hcls.prodMk hτ

/-- **The chain of a parameterised family of plane presentations into the transported structure**
(self-model form) — blocks `1`, `2` of the encoded chains. -/
theorem contMDiff_chain_param_projTimesLine_plane {N : ℕ}
    (A : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 2) →
      Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A)) :
    ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
        (A z.1 (mk2 (z.2 0) (z.2 1)), z.2 2)) := by
  unfold Work.Drive.projTimesLineCharted
  exact fun z => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ)
    (I := modelWithCornersSelf ℝ
      (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
      (A z.1 (mk2 (z.2 0) (z.2 1)), z.2 2)) Set.univ z).mpr
      (contMDiff_chain_param_prodCharted_plane A hA z)

/-! ## 4. The design's two ends in parameter-rich form

The analogue of `Work.Drive.exists_diskClassHomotopy_linear` (`diskLiftHomotopy.lean`) for the
parameter-rich family: the first end is a disk chart `D` with a smooth nonvanishing lift `V` odd on the
boundary circle plus a smooth odd weight `χ` and the non-collision condition `hgood`; the second end is
the *linear* plane chart `linPlaneChart φ c hc` with the proved lift `φ ∘ linVecC` (odd on the circle by
`Work.Drive.linVecC_neg`).  This is the family from which the Sard route's `G` is built for block `0` of
the ends clause. -/
theorem exists_diskClassHomotopyParam_linear {N : ℕ} (D : ℂ → CappingSpace) (V : ℂ → Eucl 3)
    (χ : ℂ → ℝ) (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (X : Fin N → ℂ → ℝ) (E' : Fin N → Eucl 3)
    (hVne : ∀ z : ℂ, V z ≠ 0)
    (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hXsm : ∀ i : Fin N, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X i))
    (hVcls : IsClassLift D V hVne)
    (hVodd : ∀ z : ℂ, ‖z‖ = 1 → V (-z) = - V z)
    (hχodd : ∀ z : ℂ, ‖z‖ = 1 → χ (-z) = - χ z)
    (hXodd : ∀ (i : Fin N) (z : ℂ), ‖z‖ = 1 → X i (-z) = - X i z)
    (hgood : ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 0 →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (1 - s) • V z + s • (φ (linVecC z)) ≠ 0) :
    ∃ (p : Eucl 3) (H : EuclideanSpace ℝ (Fin N) → ℝ × EuclideanSpace ℝ (Fin 2) →
        Projectivization ℝ (Eucl 3)),
      (∀ (t : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin 2)),
        H t (0, y) = planeClassMap (diskPlane D) y) ∧
      (∀ (t : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin 2)),
        H t (1, y) = planeClassMap (diskPlane (linPlaneChart φ c hc)) y) ∧
      (∀ (t : EuclideanSpace ℝ (Fin N)) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        onSeam2 y → H t (s, seamInv2 y) = H t (s, y)) ∧
      (ContMDiff (modelWithCornersSelf ℝ
          (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3)))
        (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) =>
          H z.1 (z.2 2, mk2 (z.2 0) (z.2 1)))) ∧
      (∀ t : EuclideanSpace ℝ (Fin N), Continuous (H t)) := by
  have hWsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => φ (linVecC z)) :=
    ((φ : Eucl 3 →L[ℝ] Eucl 3)).contDiff.comp linVecC_contDiff
  have hWne : ∀ z : ℂ, (fun z : ℂ => φ (linVecC z)) z ≠ 0 := fun z => phi_linVecC_ne_zero φ z
  have hWodd : ∀ z : ℂ, ‖z‖ = 1 → (fun z : ℂ => φ (linVecC z)) (-z)
      = - (fun z : ℂ => φ (linVecC z)) z := by
    intro z hz
    simp only
    rw [linVecC_neg hz, map_neg]
  obtain ⟨p, hp⟩ := exists_perturbation_disk V (fun z : ℂ => φ (linVecC z)) χ hVsmooth hWsmooth
    hχsmooth hVne hWne hgood
  obtain ⟨H, h0, h1, hseam, hsm, hjoint, hcont⟩ :=
    exists_diskClassHomotopyParam D (linPlaneChart φ c hc) V (fun z : ℂ => φ (linVecC z)) χ p
      X E' hVsmooth hWsmooth hχsmooth hXsm hVne hWne hVcls (isClassLift_linPlaneChart φ c hc)
      hVodd hWodd hχodd hXodd hp
  exact ⟨p, H, h0, h1, hseam, hjoint, hcont⟩

/-! ## 5. Recorded next step (NOT in this file): the `p`-parametrised joint smoothness

The *corrected* route for (A) (`ENDS_A_OBSTRUCTION.md` §3) must produce, for a suitable homotopy of the
design, the first condition of `Work.Drive.tripleTransverseE_encoded`: the homotopy chain is a
**submersion** at the triple points of the (fixed) pair of planes.  Its free parameters are the
perturbation vector `p : Eucl 3` of `Work.Drive.diskHomotopyLift` (whose good set `DiskGood` is *open
dense*: `Work.Drive.isOpen_dense_diskGood`) and the linear chart; the first half of a genericity
argument in `p` consumes the **joint** smoothness in `(p, x)` of the chain.  The two ingredients are:

* `ContDiff ℝ ⊤ (fun z : Eucl 3 × (ℝ × ℝ²) => diskHomotopyLift V W χ z.1 z.2)` — an immediate
  consequence of the explicit formula (the `p`-dependence is linear), in the style of
  `contDiff_diskHomotopyLift`;
* the chain form, obtained from it by `contMDiffAt_projMk_general` (the technique of §2) — with one
  bookkeeping point: the class map is only defined where the lift does not vanish, so the *total*
  function must be defined with a junk value on the vanishing locus
  (`if h : lift z = 0 then junk else Projectivization.mk ℝ (lift z) h`) and its smoothness at a good
  `(p, x)` proved by `ContMDiffAt.congr_of_eventuallyEq` from `Work.Drive.isOpen_diskGood` +
  `diskHomotopyLift_ne_zero`.  That is the exact form to write next; it is deliberately not attempted
  here (the §1–§4 declarations above are the ones this session verified).

-/