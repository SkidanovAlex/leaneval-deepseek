import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB2.DvApriori.BandDefs
import Submission.Work.BoseFixB2.Homog.neuFrac_defect
import Submission.Work.BoseFixB2.Polar.neuFrac_continuous_smul
import Submission.Work.BoseFixB2.Polar.polB_symm
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_lipschitz_of_aemeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.neuFrac_bilinear` — the polar form of the box Neumann fraction

`Work.BoseKinLoc.neuFrac ℓ a² u` is FS `eq:DefT`'s first term, the box Neumann-resolvent
fraction `A(A+a²)⁻¹` (`A` the Neumann Laplacian on `lamBox ℓ u`), defined variationally as
the `sInf` of the Dirichlet-principle trial functional.  Its polar form

`neuBil ℓ a² u f g = (Q(f+g) − Q(f−g)) / 4`

is the central object of the FS §6 off-diagonal (`band`) analysis: the off-diagonal matrix
element of the slot-`j` kinetic operator between two different joint sectors is `4·neuBil`
of the two slot-`j` fibres.

## Contents

* `additive_continuous_eq_mul` — an additive continuous `ℝ → ℝ` is `ℝ`-linear;
* `neuFrac_diff_smul` — homogeneity `Q(t·f+g) − Q(t·f−g) = t(Q(f+g) − Q(f−g))`, from the
  additivity of the defect `Homog.neuFrac_defect_add` and line-continuity;
* `exists_cutoff_lamBox` — a smooth compactly supported cutoff equal to `1` on `lamBox ℓ u`;
* `neuFrac_lipschitz_box` — the *box-restricted* Lipschitz bound
  `|Q ψ − Q ψ'| ≤ 6R√(∫_Λ(ψ−ψ')²)` for continuous states (`Kinetic.neuFrac_lipschitz_of_aemeasurable`
  only assumes *global* integrability, which continuous states need not have; the cutoff
  localises the states to compact support, where `neuFrac_eq_of_lamBox_eq` shows the value of
  `neuFrac` is unchanged);
* `neuBil` and its symmetry, additivity, homogeneity and zero laws;
* `neuBil_lipschitz_left`/`_right` — the `L²(Λ)`-Lipschitz bound for `neuBil` in each slot.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB2.DvApriori

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-! ## 1. Homogeneity of the polar form in the scalar -/

/-- **An additive continuous function `ℝ → ℝ` is `ℝ`-linear.**  Such an `F` is a `ℚ`-linear
additive map (by `map_rat_smul`), hence agrees with `t ↦ t * F 1` on the rationals, which are
dense in `ℝ`; both sides being continuous, the equality holds everywhere. -/
lemma additive_continuous_eq_mul (F : ℝ → ℝ) (hadd : ∀ s t : ℝ, F (s + t) = F s + F t)
    (hcont : Continuous F) (t : ℝ) : F t = t * F 1 := by
  have hF0 : F 0 = 0 := by
    have h := hadd 0 0
    rw [zero_add] at h
    linarith
  let f : ℝ →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  have hfcont : Continuous f := hcont
  have hkey : (f : ℝ → ℝ) = fun t => t * F 1 := by
    refine (Rat.denseRange_cast).equalizer hfcont ?_ ?_
    · fun_prop
    · funext q
      have h := map_rat_smul f q (1 : ℝ)
      rw [Rat.smul_one_eq_cast, Rat.smul_def] at h
      simpa [f] using h
  exact congr_fun hkey t

/-- **Homogeneity of the `neuFrac` polar form in the scalar**: for smooth `f, g`,
`Q(t·f+g) − Q(t·f−g) = t·(Q(f+g) − Q(f−g))`.

The defect `D(t) = Q(t·f+g) − Q(t·f−g)` (`Homog.neuFracDefect`) is additive in `t`
(`Homog.neuFrac_defect_add`, a rearrangement of the parallelogram law) and continuous in `t`
(`Polar.neuFrac_continuous_smul`); an additive continuous function `ℝ → ℝ` is linear. -/
lemma neuFrac_diff_smul {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (u : EuclideanSpace ℝ (Fin 3))
    (t : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z)
      - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z - g z)
    = t * (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + g z)
      - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z - g z)) := by
  have hadd : ∀ s t' : ℝ, Work.BoseFixB2.Homog.neuFracDefect ℓ a2 u f g (s + t')
      = Work.BoseFixB2.Homog.neuFracDefect ℓ a2 u f g s
        + Work.BoseFixB2.Homog.neuFracDefect ℓ a2 u f g t' :=
    fun s t' => Work.BoseFixB2.Homog.neuFrac_defect_add hℓ ha2 u hf hg s t'
  have hcont : Continuous (fun s : ℝ => Work.BoseFixB2.Homog.neuFracDefect ℓ a2 u f g s) := by
    have h1 : Continuous fun s : ℝ =>
        Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => s * f z + g z) :=
      Work.BoseFixB2.Polar.neuFrac_continuous_smul hℓ ha2 u hf hg
    have h2 : Continuous fun s : ℝ =>
        Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => s * f z - g z) := by
      have h := (Work.BoseFixB2.Polar.neuFrac_continuous_smul (ℓ := ℓ) (a2 := a2) hℓ ha2 u
        hf hg).comp continuous_neg
      refine h.congr (fun s => ?_)
      show Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => (-s) * f z + g z)
        = Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => s * f z - g z)
      rw [show (fun z : EuclideanSpace ℝ (Fin 3) => s * f z - g z)
            = (fun z => -((-s) * f z + g z)) from by funext z; ring,
        Work.BoseFixB2.Polar.PolB.neuFrac_neg]
    have hsub : Continuous fun s : ℝ =>
        Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => s * f z + g z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => s * f z - g z) := h1.sub h2
    simpa only [Work.BoseFixB2.Homog.neuFracDefect] using hsub
  have hlin := additive_continuous_eq_mul
    (fun s : ℝ => Work.BoseFixB2.Homog.neuFracDefect ℓ a2 u f g s) hadd hcont t
  simpa only [Work.BoseFixB2.Homog.neuFracDefect, one_mul] using hlin

/-! ## 2. A cutoff on the box, and the box-restricted Lipschitz bound -/

/-- **A smooth compactly supported cutoff equal to `1` on the moving box `lamBox ℓ u`**
(which is contained in the ball of radius `√3·ℓ/2` around `ℓ·u`). -/
lemma exists_cutoff_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ θ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Work.BoseKinLoc.lamBox ℓ u → θ x = 1) := by
  obtain ⟨θ, hθc, hθs, -, -, -, hθ1, -⟩ :=
    Submission.BoseGases.exists_smooth_radial_cutoff
      (R := Real.sqrt 3 * (ℓ / 2)) (M := Real.sqrt 3 * (ℓ / 2) + 1)
      (by positivity) (by linarith)
  have htr : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin 3) => x + -(ℓ • u)) :=
    contDiff_id.add contDiff_const
  have hcs : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) => θ (x + -(ℓ • u))) :=
    hθs.comp_homeomorph (Homeomorph.addRight (-(ℓ • u)))
  refine ⟨fun x => θ (x + -(ℓ • u)), hθc.comp htr, hcs, ?_⟩
  intro x hx
  show θ (x + -(ℓ • u)) = 1
  rw [← sub_eq_add_neg]
  apply hθ1
  have hmem : x - ℓ • u ∈ Submission.BoseGases.acube ℓ := hx
  have hcoord : ∀ m : Fin 3, |((x - ℓ • u) m)| ≤ ℓ / 2 := by
    intro m
    have hm := (Submission.BoseGases.mem_acube_iff ℓ (x - ℓ • u)).mp hmem m
    exact abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
  exact Submission.BoseGases.eucl_norm_le_of_abs_coord_le (by positivity) hcoord

/-- **The box-restricted Lipschitz bound for `neuFrac`.**  For *continuous* states `ψ, ψ'`
with `∫_Λψ², ∫_Λψ'² ≤ R²` (`Λ = lamBox ℓ u`),

`|Q ψ − Q ψ'| ≤ 6R·√(∫_Λ (ψ−ψ')²)`.

`Kinetic.neuFrac_lipschitz_of_aemeasurable` assumes *global* `L²`-integrability, which
continuous states need not have; multiplying by a cutoff equal to `1` on `Λ`
(`exists_cutoff_lamBox`) produces compactly supported (hence globally integrable) states with
the same value of `neuFrac` (`NeuFrac.neuFrac_eq_of_lamBox_eq`), and the box integrals are
unchanged. -/
lemma neuFrac_lipschitz_box {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ ψ' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2) :
    |Work.BoseKinLoc.neuFrac ℓ a2 u ψ - Work.BoseKinLoc.neuFrac ℓ a2 u ψ'|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  obtain ⟨θ, hθc, hθs, hθ1⟩ := exists_cutoff_lamBox hℓ u
  set Ψ : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => θ z * ψ z with hΨ
  set Ψ' : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => θ z * ψ' z with hΨ'
  have hΨc : Continuous Ψ := hθc.continuous.mul hψ
  have hΨ'c : Continuous Ψ' := hθc.continuous.mul hψ'
  have hΨs : HasCompactSupport Ψ := hθs.mul_right
  have hΨ's : HasCompactSupport Ψ' := hθs.mul_right
  -- values of `neuFrac` are unchanged
  have hval : Work.BoseKinLoc.neuFrac ℓ a2 u Ψ = Work.BoseKinLoc.neuFrac ℓ a2 u ψ :=
    Work.BoseKinLoc.Sector.neuFrac_eq_of_lamBox_eq u
      (fun z hz => by simp only [hΨ, hθ1 z hz, one_mul])
  have hval' : Work.BoseKinLoc.neuFrac ℓ a2 u Ψ' = Work.BoseKinLoc.neuFrac ℓ a2 u ψ' :=
    Work.BoseKinLoc.Sector.neuFrac_eq_of_lamBox_eq u
      (fun z hz => by simp only [hΨ', hθ1 z hz, one_mul])
  -- the box integrals agree
  have hI : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Ψ z) ^ 2
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 :=
    setIntegral_congr_fun (Work.BoseKinLoc.Word.measurableSet_lamBox ℓ u)
      (fun z hz => by simp only [hΨ, hθ1 z hz, one_mul])
  have hI' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Ψ' z) ^ 2
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 :=
    setIntegral_congr_fun (Work.BoseKinLoc.Word.measurableSet_lamBox ℓ u)
      (fun z hz => by simp only [hΨ', hθ1 z hz, one_mul])
  have hId : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Ψ z - Ψ' z) ^ 2
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2 :=
    setIntegral_congr_fun (Work.BoseKinLoc.Word.measurableSet_lamBox ℓ u)
      (fun z hz => by simp only [hΨ, hΨ', hθ1 z hz, one_mul])
  have hcs2 : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (Ψ z) ^ 2) :=
    hΨs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hcs2' : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (Ψ' z) ^ 2) :=
    hΨ's.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hcs2d : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (Ψ z - Ψ' z) ^ 2) :=
    (hΨs.sub hΨ's).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have h := Work.BoseKinLoc.Kinetic.neuFrac_lipschitz_of_aemeasurable (ℓ := ℓ) (a2 := a2)
    (R := R) hℓ ha2 hR u hΨc.aestronglyMeasurable hΨ'c.aestronglyMeasurable
    ((hΨc.pow 2).integrable_of_hasCompactSupport hcs2)
    ((hΨ'c.pow 2).integrable_of_hasCompactSupport hcs2')
    (((hΨc.sub hΨ'c).pow 2).integrable_of_hasCompactSupport hcs2d)
    (by rw [hI]; exact hRψ) (by rw [hI']; exact hRψ')
  rw [hval, hval', hId] at h
  exact h

/-! ## 3. The polar form `neuBil` and its elementary properties -/

/-- **The polar form of the box Neumann-resolvent fraction** `neuFrac ℓ a² u`:
`neuBil ℓ a² u f g = (Q(f+g) − Q(f−g))/4`.  For a quadratic form `Q` this is the
associated symmetric bilinear form. -/
noncomputable def neuBil (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (f g : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + g z)
    - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z - g z)) / 4

/-- `neuBil` is symmetric: it is the polar form of a quadratic form. -/
lemma neuBil_symm (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (f g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    neuBil ℓ a2 u f g = neuBil ℓ a2 u g f := by
  unfold neuBil
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) => f z + g z) = (fun z => g z + f z)
        from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => f z - g z) = (fun z => -(g z - f z))
        from by funext z; ring,
    Work.BoseFixB2.Polar.PolB.neuFrac_neg]

/-- `neuBil` vanishes when the second argument vanishes. -/
@[simp] lemma neuBil_zero_right (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) : neuBil ℓ a2 u f 0 = 0 := by
  unfold neuBil
  simp

/-- `neuBil` vanishes when the first argument vanishes (by symmetry). -/
@[simp] lemma neuBil_zero_left (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) : neuBil ℓ a2 u 0 g = 0 := by
  rw [neuBil_symm]
  simp

/-- **Additivity of the polar form in its second slot**, from the additivity in the first
slot (`Homog.neuFrac_polar_add3`) and symmetry. -/
lemma neuBil_add_right {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) {c f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    neuBil ℓ a2 u c (fun z => f z + g z) = neuBil ℓ a2 u c f + neuBil ℓ a2 u c g := by
  have h3 := Work.BoseFixB2.Homog.neuFrac_polar_add3 (ℓ := ℓ) (a2 := a2) hℓ ha2 u hf hg hc
  have h3' : Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + g z + c z)
        - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + g z - c z)
      = (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + c z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z - c z))
        + (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => g z + c z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => g z - c z)) := h3
  unfold neuBil
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) => c z + (f z + g z))
        = (fun z => f z + g z + c z) from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z - (f z + g z))
        = (fun z => -(f z + g z - c z)) from by funext z; ring,
    Work.BoseFixB2.Polar.PolB.neuFrac_neg,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z + f z) = (fun z => f z + c z)
        from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z - f z) = (fun z => -(f z - c z))
        from by funext z; ring,
    Work.BoseFixB2.Polar.PolB.neuFrac_neg,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z + g z) = (fun z => g z + c z)
        from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z - g z) = (fun z => -(g z - c z))
        from by funext z; ring,
    Work.BoseFixB2.Polar.PolB.neuFrac_neg]
  linarith [h3']

/-- **Additivity of the polar form in its first slot** (from the additivity in the second
slot and symmetry). -/
lemma neuBil_add_left {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) {f g c : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    neuBil ℓ a2 u (fun z => f z + g z) c = neuBil ℓ a2 u f c + neuBil ℓ a2 u g c := by
  rw [neuBil_symm, neuBil_add_right hℓ ha2 u (f := f) (g := g) hc hf hg, neuBil_symm,
    neuBil_symm (ℓ := ℓ) (a2 := a2) u g c]

/-- **`ℝ`-homogeneity of the polar form in its second slot**. -/
lemma neuBil_smul_right {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) {c f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    neuBil ℓ a2 u c (fun z => t * f z) = t * neuBil ℓ a2 u c f := by
  have h := neuFrac_diff_smul (ℓ := ℓ) (a2 := a2) hℓ ha2 u t hf hc
  unfold neuBil
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) => c z + t * f z) = (fun z => t * f z + c z)
        from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z - t * f z) = (fun z => -(t * f z - c z))
        from by funext z; ring,
    Work.BoseFixB2.Polar.PolB.neuFrac_neg,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z + f z) = (fun z => f z + c z)
        from by funext z; ring,
    show (fun z : EuclideanSpace ℝ (Fin 3) => c z - f z) = (fun z => -(f z - c z))
        from by funext z; ring,
    Work.BoseFixB2.Polar.PolB.neuFrac_neg]
  linarith [h]

/-- **`ℝ`-homogeneity of the polar form in its first slot** (from the homogeneity in the
second slot and symmetry). -/
lemma neuBil_smul_left {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) {f c : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    neuBil ℓ a2 u (fun z => t * f z) c = t * neuBil ℓ a2 u f c := by
  rw [neuBil_symm, neuBil_smul_right hℓ ha2 u t (f := f) hc hf, neuBil_symm]

/-! ## 4. The `L²(Λ)`-Lipschitz bound for `neuBil` -/

/-- The `L²(Λ)`-Lipschitz bound for the polar form in its second slot. -/
lemma neuBil_lipschitz_right {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {c f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : Continuous c) (hf : Continuous f) (hg : Continuous g)
    (hRcf : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z + f z) ^ 2 ≤ R ^ 2)
    (hRcg : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z + g z) ^ 2 ≤ R ^ 2)
    (hRdf : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z - f z) ^ 2 ≤ R ^ 2)
    (hRdg : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z - g z) ^ 2 ≤ R ^ 2) :
    |neuBil ℓ a2 u c f - neuBil ℓ a2 u c g|
      ≤ 3 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (f z - g z) ^ 2) := by
  have h1 : |Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
      - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (f z - g z) ^ 2) := by
    have h := neuFrac_lipschitz_box hℓ ha2 hR u (hc.add hf) (hc.add hg) hRcf hRcg
    have hI : ∫ z in Work.BoseKinLoc.lamBox ℓ u, ((c + f) z - (c + g) z) ^ 2
        = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (f z - g z) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Pi.add_apply]; ring))
    rw [hI] at h
    rwa [show (fun z : EuclideanSpace ℝ (Fin 3) => c z + f z) = c + f from rfl,
      show (fun z : EuclideanSpace ℝ (Fin 3) => c z + g z) = c + g from rfl]
  have h2 : |Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z)
      - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z)|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (f z - g z) ^ 2) := by
    have h := neuFrac_lipschitz_box hℓ ha2 hR u (hc.sub hf) (hc.sub hg) hRdf hRdg
    have hI : ∫ z in Work.BoseKinLoc.lamBox ℓ u, ((c - f) z - (c - g) z) ^ 2
        = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (f z - g z) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Pi.sub_apply]; ring))
    rw [hI] at h
    rwa [show (fun z : EuclideanSpace ℝ (Fin 3) => c z - f z) = c - f from rfl,
      show (fun z : EuclideanSpace ℝ (Fin 3) => c z - g z) = c - g from rfl]
  have htri : |(Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
        - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z))
      - (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)
        - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z))|
      ≤ |Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
            - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)|
        + |Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z)
            - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z)| := by
    have he : Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z)
          - (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)
            - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z))
        = (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
            - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z))
          - (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z)
            - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z)) := by ring
    rw [he]
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
      (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
        - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)) 0
      (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z)
        - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z))
  unfold neuBil
  rw [show (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z)) / 4
        - (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z)) / 4
      = ((Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + f z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - f z))
        - (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z + g z)
          - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => c z - g z))) / 4 from by ring]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
  linarith [htri, h1, h2]

/-- The `L²(Λ)`-Lipschitz bound for the polar form in its first slot (from the bound in the
second slot and symmetry). -/
lemma neuBil_lipschitz_left {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {c f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : Continuous c) (hf : Continuous f) (hg : Continuous g)
    (hRcf : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z + f z) ^ 2 ≤ R ^ 2)
    (hRcg : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z + g z) ^ 2 ≤ R ^ 2)
    (hRdf : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z - f z) ^ 2 ≤ R ^ 2)
    (hRdg : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (c z - g z) ^ 2 ≤ R ^ 2) :
    |neuBil ℓ a2 u f c - neuBil ℓ a2 u g c|
      ≤ 3 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (f z - g z) ^ 2) := by
  rw [neuBil_symm (ℓ := ℓ) (a2 := a2) u f c, neuBil_symm (ℓ := ℓ) (a2 := a2) u g c]
  exact neuBil_lipschitz_right hℓ ha2 hR u hc hf hg hRcf hRcg hRdf hRdg

end Work.BoseFixB2.DvApriori
