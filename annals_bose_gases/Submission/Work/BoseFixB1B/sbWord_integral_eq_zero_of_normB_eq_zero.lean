import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.AprioriPieces
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.sbWord_integral_eq_zero_of_normB_eq_zero`

**The degenerate-state clause of the sliding (FS `eq:BSsliding2`) inequality.**

The chapter `Work.BoseFixB1` states its per-state inequalities only for states
with `0 < normB`, and the degenerate case `normB = 0` has to be discharged
separately (`normB` is the *boxed* `L²`-norm square `∫_{abox n ℓ} Φ²`; the class
`Work.BoseKinLoc.BoxState` carries no support condition, so a state may vanish on
the box while being non-zero outside it — exactly the phenomenon that makes the
per-state windows fail without the `0 < normB` hypothesis).

The statement proved here is the corresponding clause for the **sliding word**
`Work.BoseFixB1.sbWord h μ u Φ = sbKin h μ u Φ + sbPot h μ u Φ`: if the boxed
norm vanishes then the `u`-integral of the sliding word vanishes.

## Route

`normB v μ n Φ = sqNormB n ℓ Φ = 0` with `ℓ = sideAt μ (a v) > 0` and `Φ` smooth
forces `Φ x = 0` *pointwise* on the box (`Sector.eq_zero_on_abox_of_sqNormB_eq_zero`).
Both halves of the sliding word then vanish **for every `u`**, and hence so does
the `u`-integral:

* `sbPot h μ u Φ = qLHSword ℓ μ w w₁ Φ` is an integral over `abox n ℓ` of
  `(Φ x)²` times a kernel weight, so it vanishes pointwise;
* `sbKin ≅ tBwordInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) (chiB ℓ d u) …` is built from
  the FS-faithful projections `Q_{B(u),i} = 1_{B(u)}Φ − P_{B(u),i}Φ`, whose box
  indicator `1_{B(u)}(x_i)` and whose slot-mean over `B(u) ⊆ acube ℓ`
  (`SmallBoxSliding.dlBox_subset_acube`) only ever evaluate `Φ` *inside* the box,
  and from the windowed amplitudes `tBamp` with window `chiB ℓ d u`, whose support
  lies in `acube ℓ` (`chiScale_mem_acube`).  All of these vanish on the box.

The general vanishing statements are proved first for the pieces
(`boxQInd`, `tBamp`, `tBdiagFormInd`, `cnPlusBoxInd`, `tBwordInd`,
`tBwordBInd`) and then assembled.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary geometry -/

/-- A slot update of a box configuration stays in the box when the new
coordinate does. -/
private lemma update_mem_abox {N : ℕ} {a : ℝ} {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N a) (i : Fin N) {z : ℝ³}
    (hz : z ∈ Submission.BoseGases.acube a) :
    Function.update x i z ∈ Submission.BoseGases.abox N a := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  rw [Function.update_apply]
  by_cases hj : j = i
  · rw [if_pos hj]; exact hz
  · rw [if_neg hj]; exact hx j

/-! ## 2. The FS box projection `Q_{B,i}` vanishes on the box -/

/-- **`Q_{B,i}Φ` vanishes on the big box** for a state `Φ` vanishing pointwise on
the big box, whenever the small box `A` sits inside the big cube `acube a`:
both the box indicator `1_A(x_i)` and the slot mean
`|A|⁻¹∫_{z∈A}Φ(x_{i←z})` only see `Φ` at points of the big box. -/
lemma boxQInd_eq_zero_of_eq_zero_on_abox {a volA : ℝ} {A : Set ℝ³}
    (hA : A ⊆ Submission.BoseGases.acube a) {N : ℕ} (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N a, Ψ x = 0) :
    ∀ x ∈ Submission.BoseGases.abox N a, Work.UBBInputs8.boxQInd volA A i Ψ x = 0 := by
  intro x hx
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ A
  · rw [Set.indicator_of_mem hxi (fun _ => (1 : ℝ))]
    have hint : (∫ z in A, Ψ (Function.update x i z)) = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
        (fun z hz => hΨ _ (update_mem_abox hx i (hA hz)))
    rw [hΨ x hx, hint]
    ring
  · rw [Set.indicator_of_notMem hxi (fun _ => (1 : ℝ))]
    ring

/-! ## 3. The windowed amplitude `tBamp` vanishes on the box -/

/-- **`tBamp` vanishes on the big box.**  Its integrand over `z` carries the
window `χ`, which is supported in `acube a` by hypothesis, and the projected
state `Q_{B,i}Ψ` vanishes at the updated configuration `x_{i←z}` whenever
`z ∈ acube a` (by `boxQInd_eq_zero_of_eq_zero_on_abox`). -/
lemma tBamp_eq_zero_of_eq_zero_on_abox {a volA : ℝ} {A : Set ℝ³}
    (hA : A ⊆ Submission.BoseGases.acube a) {N : ℕ} (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N a, Ψ x = 0)
    {χ : ℝ³ → ℝ} (hχ : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube a → χ z = 0)
    (p : ℝ³) :
    ∀ x ∈ Submission.BoseGases.abox N a,
      Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x = 0 := by
  intro x hx
  rw [Work.SmallBoxTBWord.tBamp]
  rw [show (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
      ((Work.UBBInputs8.boxQInd volA A i Ψ (Function.update x i z) : ℝ) : ℂ)) = fun _ => 0
      from ?_]
  · simp
  · funext z
    by_cases hz : z ∈ Submission.BoseGases.acube a
    · rw [boxQInd_eq_zero_of_eq_zero_on_abox hA i hΨ (Function.update x i z)
        (update_mem_abox hx i hz)]
      simp
    · rw [hχ z hz]
      simp

/-! ## 4. The pieces of `tBwordInd` -/

/-- **The `p`-diagonal kinetic form vanishes**: every inner box integral of
`‖tBamp‖²` vanishes by `tBamp_eq_zero_of_eq_zero_on_abox`. -/
lemma tBdiagFormInd_eq_zero_of_eq_zero_on_abox {a volA : ℝ} {A : Set ℝ³}
    (hA : A ⊆ Submission.BoseGases.acube a) {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N a, Ψ x = 0)
    {χ : ℝ³ → ℝ} (hχ : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube a → χ z = 0)
    (F : ℝ → ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ = 0 := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hzero : (fun p : ℝ³ => F ‖p‖ * ((a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2))
      = fun _ : ℝ³ => 0 := by
    funext p
    have hI : (∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
        (fun x hx => by
          rw [tBamp_eq_zero_of_eq_zero_on_abox hA i hΨ hχ p x hx]; simp)
    rw [hI]
    ring
  rw [hzero]
  simp

/-- **The FS-faithful excited count vanishes**: its integrand is
`(Q_{B,i}Ψ)²`, which is zero on the box. -/
lemma cnPlusBoxInd_eq_zero_of_eq_zero_on_abox {a volA : ℝ} {A : Set ℝ³}
    (hA : A ⊆ Submission.BoseGases.acube a) {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N a, Ψ x = 0) :
    Work.UBBInputs8.cnPlusBoxInd a A volA Ψ = 0 := by
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
  rw [boxQInd_eq_zero_of_eq_zero_on_abox hA i hΨ x hx]
  ring

/-! ## 5. The box words vanish -/

/-- **`tBwordInd` vanishes** on a state vanishing on the box. -/
lemma tBwordInd_eq_zero_of_eq_zero_on_abox {a volA : ℝ} {A : Set ℝ³}
    (hA : A ⊆ Submission.BoseGases.acube a) {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N a, Ψ x = 0)
    {χ : ℝ³ → ℝ} (hχ : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube a → χ z = 0)
    (s ε c : ℝ) :
    Work.UBBInputs8.tBwordInd a A volA χ s ε c Ψ = 0 := by
  rw [Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
    cnPlusBoxInd_eq_zero_of_eq_zero_on_abox hA hΨ,
    tBdiagFormInd_eq_zero_of_eq_zero_on_abox hA hΨ hχ]
  ring

/-- The window `chiB ℓ d u` vanishes off the big cube `acube ℓ` (its first
factor is `chiScale ℓ = χ(·/ℓ)`, supported in `acube ℓ`). -/
lemma chiB_eq_zero_of_notMem_acube {ℓ d : ℝ} (hℓ : 0 < ℓ) (u z : ℝ³)
    (hz : z ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiB ℓ d u z = 0 := by
  rw [Submission.BoseGases.chiB]
  have h0 : Submission.BoseGases.chiScale ℓ z = 0 := by
    by_contra hne
    exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hne)
  rw [h0, zero_mul]

/-- **The sliding box word `tBwordBInd` vanishes** on a state vanishing on the
big box: the box `B(u) = dlBox ℓ d u` lies in `acube ℓ`
(`SmallBoxSliding.dlBox_subset_acube`) and the window `chiB ℓ d u` is supported
in `acube ℓ`. -/
lemma tBwordBInd_eq_zero_of_eq_zero_on_abox {N : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ³) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N ℓ, Ψ x = 0) :
    Work.UBBInputs8.tBwordBInd N ℓ d ε c u Ψ = 0 := by
  rw [Work.UBBInputs8.tBwordBInd]
  exact tBwordInd_eq_zero_of_eq_zero_on_abox
    (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hΨ
    (fun z hz => chiB_eq_zero_of_notMem_acube hℓ u z hz) (ℓ * d) ε c

/-- **The sliding potential word vanishes** on a state vanishing on the big box:
it is an integral over `abox N ℓ` of `(Φ x)²` times a kernel weight. -/
lemma qLHSwordB_eq_zero_of_eq_zero_on_abox {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d μ : ℝ} {u : ℝ³} {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N ℓ, Ψ x = 0) :
    Work.SmallBoxSliding.qLHSwordB (v := v) h M ℓ d μ u Ψ = 0 := by
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
  exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    (fun x hx => by rw [hΨ x hx]; ring)

/-! ## 6. The target -/

theorem sbWord_integral_eq_zero_of_normB_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hnorm : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) = 0 := by
  -- the box side is positive
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    have hKl : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl := by
      show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2))
      exact Work.BoseBox.fsXp_pos ht
    exact Work.BoseBox.boxSide_pos hμ hav hKl
  -- the boxed norm vanishes, so the state vanishes pointwise on the box
  have hsq : Work.BoseKinLoc.sqNormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) = 0 := hnorm
  have hΦ0 : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ : Submission.BoseGases.X n → ℝ) x = 0 :=
    Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hℓ Φ.contDiff.continuous hsq
  -- hence the sliding word vanishes for every `u`
  have hpoint : ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
    intro u
    have hkin : Work.BoseFixB1.sbKin (v := v) μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
        (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
      rw [Work.BoseFixB1.sbKin]
      exact tBwordBInd_eq_zero_of_eq_zero_on_abox hℓ u hΦ0
    have hpot : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
      rw [Work.BoseFixB1.sbPot]
      exact qLHSwordB_eq_zero_of_eq_zero_on_abox hΦ0
    rw [Work.BoseFixB1.sbWord, hkin, hpot]
    ring
  rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) = fun _ => 0
      from funext hpoint]
  simp

end Work.BoseFixB1B
