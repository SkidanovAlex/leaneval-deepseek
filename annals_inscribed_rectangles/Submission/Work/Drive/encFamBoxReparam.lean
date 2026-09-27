import Mathlib
import Submission.Work.Drive.encFamQ0
import Submission.Work.Drive.boxReparamLift
import Submission.Work.Drive.meet3Hyp_encodedChains
import Submission.Work.Drive.contMDiffAt_classMap_prod

/-!
# The `hodd` family is the encoded chains of `H'`, composed with the box reparametrisation

`Work.Drive.encFamQ0` (`Submission/Work/Drive/encFamQ0.lean`, §2.2 of `NOTES_LEAD_hodd_blockT6.md`)
parametrises the sheared ends-clause family: block `0` is the class-perturbed homotopy `H` evaluated at
the *sheared* plane coordinates, and blocks `1`, `2` are the two class maps, sheared and level-twisted.

`Work.Drive.boxReparam` (`Submission/Work/Drive/boxReparamLift.lean`) is the lift of the clamped
cross-shear and of the level twist to `𝔼³`; `Work.Drive.meet3Hyp_of_boxReparam_family` transfers the
triple-intersection hypothesis along it.

This module supplies the missing *identification*: the family `encFamQ0 H A B c₀ t` **is** the encoded
chains of the perturbed homotopy

> `encFamH' H p (s, y) := clsSh (chartPert (betaG s • p) (capOf (H (s, y))))`

composed with `boxReparam`.  Consequently (with the smoothness and seam data of the encoded chains,
which are the §2.1 prover's obligations)

* `Work.Drive.encFamH'_zero`, `encFamH'_one` — `H'` agrees with `H` at the two ends (so the ends of the
  homotopy are not moved by the perturbation);
* `Work.Drive.encFamQ0_apply_eq` — the identification, pointwise;
* **`Work.Drive.meet3Hyp_encFamQ0`** — `Meet3Hyp` of the sheared family gives `Meet3Hyp` of
  `encodedChains (fun x => encFamH' H p (x 2) (pt2 (x 0) (x 1))) A B c₀`, i.e. exactly the conclusion
  of §2.1's `exists_homotopy_meet3Hyp_encoded` (with `H'` written out).

With this, the *transfer* half of the last research hole of the wall is done: what remains for §2.1 is
the parametrised-Sard generation of the `Meet3Hyp` hypothesis for `encFamQ0` (the pointwise
surjectivity `surjective_paramDeriv_encFamQ0_caseI`/`caseII` fed to
`Work.Drive.localSard_family_in_open`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- **The perturbed homotopy** of the design: the class perturbation `chartPert (β s • p)` of the
homotopy `H`, read in the class.  It agrees with `H` at the two ends (`β 0 = β 1 = 0`). -/
def encFamH' (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4)) (sy : ℝ × EuclideanSpace ℝ (Fin 2)) :
    Projectivization ℝ (Eucl 3) :=
  clsSh (chartPert (betaG sy.1 • p) (capOf (H sy)))

@[simp] lemma encFamH'_zero (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    encFamH' H p (0, y) = H (0, y) := by
  simp [encFamH']

@[simp] lemma encFamH'_one (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    encFamH' H p (1, y) = H (1, y) := by
  simp [encFamH']

/-- **`encFamH'` is the class perturbation `classMap`**: the chart perturbation of the capped point
acts on the class by `classMap (β s • p)`. -/
lemma encFamH'_eq_classMap (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4)) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    encFamH' H p (s, y) = classMap (betaG s • p) (H (s, y)) := by
  simp [encFamH', clsSh_chartPert, clsSh_capOf]

/-- `encFamH'` is seam-invariant as soon as the homotopy is (the class perturbation and the clamped
parameter do not involve the plane coordinates). -/
theorem encFamH'_seam (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4))
    (hH : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (t, seamInv2 y) = H (t, y)) :
    ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      encFamH' H p (t, seamInv2 y) = encFamH' H p (t, y) := by
  intro t y hy
  rw [encFamH'_eq_classMap, encFamH'_eq_classMap, hH t y hy]

/-- The witness chain of the sheared family, as a function of the parameter point. -/
def encFamWitness (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4)) (x : EuclideanSpace ℝ (Fin 3)) :
    Projectivization ℝ (Eucl 3) :=
  encFamH' H p (x 2, pt2 (x 0) (x 1))

/-- `encFamWitness` as an anonymous function (the form in which the encoded chains consume it). -/
lemma encFamWitness_eq (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4)) :
    encFamWitness H p
      = fun y : EuclideanSpace ℝ (Fin 3) => encFamH' H p (y 2, pt2 (y 0) (y 1)) := rfl

/-- The shear parameters of the three blocks of the design's family. -/
def encFamQ (t : EncParQ0) : Fin 3 → EuclideanSpace ℝ (Fin 4) :=
  ![q0Q0 t, q0Q1 t, q0Q2 t]

/-- The level-twist parameters: block `0` has constant level, so its twist parameter is `0`
(`thetaS 0 = id`). -/
def encFamR (t : EncParQ0) : Fin 3 → ℝ := ![0, q0R1 t, q0R2 t]

/-- `pt2` of the two coordinates of a point of `𝔼²` is the point. -/
private lemma pt2_eta (y : EuclideanSpace ℝ (Fin 2)) : pt2 (y 0) (y 1) = y := by
  ext i
  fin_cases i <;> simp


/-- **The identification**: the design's sheared family at the parameter `t` is the encoded chains of
the perturbed homotopy `encFamH'`, composed with the box reparametrisation. -/
theorem encFamQ0_apply_eq (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (t : EncParQ0)
    (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    encFamQ0 H A B c₀ t k x
      = encodedChains (encFamWitness H (q0P t)) A B c₀ k
          (boxReparam (encFamQ t k) (encFamR t k) x) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [encFamQ0, encFamQ0₀, Fin.isValue, Fin.zero_eta, if_true, encFamQ, encFamR,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, encodedChains_zero, encFamWitness, encFamH', boxReparam_apply_zero,
      boxReparam_apply_one, boxReparam_apply_two, thetaS_zero, mk2CLM_apply, pt2_eq_mk2,
      pt2_eta, mk2_eta]
  · by_cases hk1 : k = 1
    · subst hk1
      simp only [encFamQ0, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        if_neg (show ¬ ((1 : Fin 3) = 0) by decide),
        if_pos (show ((1 : Fin 3) = 1) by decide), if_true, mk2_eta, encFamQ,
        encFamR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, encodedChains_zero, encodedChains_one, encFamWitness, encFamH',
        boxReparam_apply_zero, boxReparam_apply_one, boxReparam_apply_two, mk2CLM_apply,
        pt2_eq_mk2, pt2_eta]
    · have hk2 : k = 2 := by
        have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
        rcases hk with h | h | h
        · exact absurd h hk0
        · exact absurd h hk1
        · exact h
      subst hk2
      simp only [encFamQ0, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        if_neg (show ¬ ((2 : Fin 3) = 0) by decide),
        if_neg (show ¬ ((2 : Fin 3) = 1) by decide), mk2_eta, encFamQ,
        encFamR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, encodedChains_zero, encodedChains_one, encodedChains_two, encFamWitness,
        encFamH', boxReparam_apply_zero, boxReparam_apply_one, boxReparam_apply_two, mk2CLM_apply,
        pt2_eq_mk2, pt2_eta]

/-- The time bump of the family is `C^∞`. -/
lemma contDiff_betaG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) betaG := by
  have h : betaG = fun s : ℝ => expNegInvGlue s * expNegInvGlue (1 - s) := rfl
  rw [h]
  exact expNegInvGlue.contDiff.mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

/-- The class-perturbation parameter `x ↦ β (x 2) • p` is `C^∞` (as a map into the model space of
the first factor of `ℝ⁴ × ℝP³`). -/
lemma contMDiff_betaG_smul (p : EuclideanSpace ℝ (Fin 4)) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => betaG (x 2) • p) := by
  rw [contMDiff_iff_contDiff]
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => betaG (coordCLM2 x) • p) :=
    (contDiff_betaG.comp coordCLM2.contDiff).smul contDiff_const
  simpa [coordCLM2_apply] using hcd

/-- **The perturbed homotopy chain is `C^∞`** (the `Meet3Hyp.smooth` input of the encoded chains built
from `encFamH'`). -/
theorem contMDiff_encFamWitness
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (p : EuclideanSpace ℝ (Fin 4))
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => encFamH' H p (x 2, mk2 (x 0) (x 1))) := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin 3) => encFamH' H p (x 2, mk2 (x 0) (x 1)))
      = fun x : EuclideanSpace ℝ (Fin 3) =>
          classMap (betaG (x 2) • p) (H (x 2, mk2 (x 0) (x 1))) := by
    funext x
    simp only [encFamH'_eq_classMap]
  rw [hfun]
  intro x
  have hpair : ContMDiffAt (𝓡 3) ((𝓡 4).prod (𝓡 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (betaG (x 2) • p, H (x 2, mk2 (x 0) (x 1)))) x :=
    (contMDiff_betaG_smul p).contMDiffAt.prodMk hH.contMDiffAt
  have hcomp := (contMDiffAt_classMap_prod (betaG (x 2) • p) (H (x 2, mk2 (x 0) (x 1)))).comp
    x hpair
  simpa only [Function.comp_def] using hcomp

/-- **The transfer, in the exact shape of §2.1's conclusion.**  If the sheared family
`encFamQ0 H A B c₀ t` satisfies the triple-intersection hypothesis, then so do the encoded chains of
the perturbed homotopy `encFamH' H (q0P t)`.  All the smoothness and seam data of those chains are
*derived* here from the corresponding data of `H`, `A`, `B`, so the caller only has to supply the
`Meet3Hyp` of the sheared family (produced by the parametrised Sard) and the design's data. -/
theorem meet3Hyp_encFamQ0
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ) (t : EncParQ0)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hHseam : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H (s, seamInv2 y) = H (s, y))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hBseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    (h : Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encFamQ0 H A B c₀ t)) :
    Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (encFamWitness H (q0P t)) A B c₀) := by
  have hfun : encFamQ0 H A B c₀ t
      = fun k x => encodedChains (encFamWitness H (q0P t)) A B c₀ k
          (boxReparam (encFamQ t k) (encFamR t k) x) := by
    funext k x
    exact encFamQ0_apply_eq H A B c₀ t k x
  rw [hfun] at h
  refine meet3Hyp_of_boxReparam_family (encodedChains (encFamWitness H (q0P t)) A B c₀)
    (fun k => by
      have hw := contMDiff_encodedChains (encFamH' H (q0P t)) A B c₀ k
        (contMDiff_encFamWitness H (q0P t) hH) hA hB
      simpa [encFamWitness_eq] using hw)
    (fun k x hx => by
      have hw := seam_encodedChains (encFamH' H (q0P t)) A B c₀ k
        (encFamH'_seam H (q0P t) hHseam) hAseam hBseam x hx
      simpa [encFamWitness_eq] using hw)
    (encFamQ t) (encFamR t) h

/-- **The last line of §2.1's conclusion.**  From a `Meet3Hyp` of the design's sheared family and the
design's data, the existential conclusion of `exists_homotopy_meet3Hyp_encoded` holds, with
`H' = encFamH' H (q0P t)`.  What the §2.1 prover still owes is exactly the hypothesis
`Meet3Hyp (ℝP³ × ℝ) (encFamQ0 H A B c₀ t)` (the parametrised Sard). -/
theorem exists_meet3Hyp_encFamQ0
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) {c₀ : ℝ} (t : EncParQ0)
    (hH : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))))
    (hHseam : ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H (s, seamInv2 y) = H (s, y))
    (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hAseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → A (seamInv2 y) = A y)
    (hB : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hBseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → B (seamInv2 y) = B y)
    (hmeet : Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encFamQ0 H A B c₀ t)) :
    ∃ H' : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
      (∀ y, H' (0, y) = H (0, y)) ∧ (∀ y, H' (1, y) = H (1, y)) ∧
      Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
        (encodedChains (fun x : EuclideanSpace ℝ (Fin 3) => H' (x 2, pt2 (x 0) (x 1))) A B c₀) :=
  ⟨encFamH' H (q0P t), encFamH'_zero H (q0P t), encFamH'_one H (q0P t),
   by simpa only [encFamWitness_eq] using
     meet3Hyp_encFamQ0 H A B c₀ t hH hHseam hA hAseam hB hBseam hmeet⟩

end

end Work.Drive
