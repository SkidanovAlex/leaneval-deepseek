import Mathlib
import Submission.Work.Drive.sideGermSepDefs

/-!
# The concrete family of `Work.Drive.sep_fam_regular`

`Work.Drive.sep_fam_regular` is the *Sard regularity* obligation of the germ/parity route: for the
straight path from the configuration `A` to the configuration `B`, with the loop side shifted by `τ₁`
and the chain side by `τ₂`, there are arbitrarily small shifts at which the five-box family of
`Work.Drive.famLoop` versus `Work.Drive.famChain` is regular (`FamBox.Lf` onto at every meet, and the
face data at the boundary meets).

This file fixes the *notation*: the two families of the statement, as `2`-chains and `4`-chains in the
sense of `Work.Drive.famLoop` / `Work.Drive.famChain`, together with the two descriptions of the
statement's own maps (`chartLoopFam (sepQfam …)` / `sweepFam c (1 - ·) (sepPfam …)`).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {m : ℕ}

/-- **The loop family of `sep_fam_regular`** at the shift `τ₁`: the core loop of the `τ₁`-shift of
the straight-path family of charts.  As a `2`-chain, so that its `famLoop` is the loop side of the
five-box family. -/
def sepLoopFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  chartLoopFam (sepQfam Ξ Q A B τ₁)

/-- **The chain family of `sep_fam_regular`** at the shift `τ₂`: the clamped sweep of the `τ₂`-shift
of the straight-path family of plane presentations, as a `4`-chain. -/
def sepChainFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin 4) → CappingSpace :=
  sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)

@[simp] lemma sepLoopFam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin 2)) :
    sepLoopFam Ξ Q A B τ₁ p = coreLoop (sepQfam Ξ Q A B τ₁ (p 0)) (p 1) := rfl

@[simp] lemma sepChainFam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) (q : EuclideanSpace ℝ (Fin 4)) :
    sepChainFam Ξ Q c tR t'R A B τ₂ q
      = clampedSweep c (fun u => 1 - u)
          (sepPfam Ξ Q tR t'R A B τ₂ (q 0)) (famT3 (q 1) (q 2) (q 3)) := rfl

@[simp] lemma sep_famT3_apply_zero (a b c : ℝ) : famT3 a b c 0 = a := by
  rw [famT3, WithLp.ofLp_toLp]; rfl

@[simp] lemma sep_famT3_apply_one (a b c : ℝ) : famT3 a b c 1 = b := by
  rw [famT3, WithLp.ofLp_toLp]; rfl

@[simp] lemma sep_famT3_apply_two (a b c : ℝ) : famT3 a b c 2 = c := by
  rw [famT3, WithLp.ofLp_toLp]; rfl

/-- The loop side of the five-box family, in coordinates. -/
lemma sep_famLoop_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin 5)) :
    famLoop (sepLoopFam Ξ Q A B τ₁) p
      = coreLoop (sepQfam Ξ Q A B τ₁ (p 0)) (p 1) := by
  rw [famLoop, sepLoopFam, chartLoopFam, mk2_apply_zero, mk2_apply_one]

/-- The chain side of the five-box family, in coordinates. -/
lemma sep_famChain_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin 5)) :
    famChain (sepChainFam Ξ Q c tR t'R A B τ₂) p
      = clampedSweep c (fun u => 1 - u)
          (sepPfam Ξ Q tR t'R A B τ₂ (p 0)) (famT3 (p 2) (p 3) (p 4)) := by
  rw [famChain, sepChainFam, sweepFam]
  simp only [famPt_apply_zero, sep_famPt_apply_one, sep_famPt_apply_two, sep_famPt_apply_three]
  congr 2

/-- The loop side of `Work.Drive.SepRegular` is the `famLoop` of `sepLoopFam`. -/
lemma sep_chartLoopFam_eq_famLoop (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    chartLoopFam (sepQfam Ξ Q A B τ₁) = sepLoopFam Ξ Q A B τ₁ := rfl

/-- The chain side of `Work.Drive.SepRegular` is the `famChain` of `sepChainFam`. -/
lemma sep_sweepFam_eq_famChain (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) :
    sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B τ₂)
      = sepChainFam Ξ Q c tR t'R A B τ₂ := rfl

/-! ## The smoothness packages of the two families

These are stated as `def`s of `Prop` (and not directly as `ContMDiff` statements) so that mentioning
them *elsewhere* does not require the local charted-space instances of `CappingSpace` to be in scope:
the instances are resolved here, once, at the transparent structure `Work.Drive.cappingCharted`.
-/

/-- The loop family is `C^∞` in the loop parameter. -/
def SepLoopSmooth {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) : Prop :=
  ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (sepLoopFam Ξ Q A B τ₁)

/-- The chain family at a fixed shift is `C^∞` in the chain parameter. -/
def SepChainSmooth {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₂ : EuclideanSpace ℝ (Fin m)) : Prop :=
  ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (sepChainFam Ξ Q c tR t'R A B τ₂)

/-- The chain family is *jointly* `C^∞` in the shift and the chain parameter. -/
def SepChainSmoothJoint {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (tR t'R : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) : Prop :=
  ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) =>
      sepChainFam Ξ Q c tR t'R A B q.1 q.2)

/-! ## The packaged interface of the regularity argument

The notions below mention the (local, transparent) charted-space structure of `CappingSpace`
(`Work.Drive.chr`, `ContMDiff`, `fderiv`), so they are *defined here*, where the instances are in
scope; statements elsewhere can then refer to them without carrying those instances.
-/

/-- **The chart-region condition** of the bumped charted difference system for the chart `p`, on the
rectangle `U ×ˢ V`: there both values of the family lie in the source of the chart at `p`. -/
def SepChartReg {m : ℕ} (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace)
    (p : CappingSpace) (U : Set (EuclideanSpace ℝ (Fin m))) (V : Set (Amb 4)) : Prop :=
  U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
    famLoop (Lf q.1) q.2 ∈ (chr p).source ∧ famChain (N q.1) q.2 ∈ (chr p).source}

/-- **The bumped charted difference system is `C^∞`** (the cut-off version, with the parameter
reparametrisation `sq`). -/
def SepCutoffSystemSmooth {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace)
    (p : CappingSpace) (γ : EuclideanSpace ℝ (Fin m) → ℝ) (β : Amb 4 → ℝ)
    (sq : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      (γ (sq q.1) * β q.2) •
        FamBox.chartDif p (famLoop (Lf (sq q.1))) (famChain (N (sq q.1))) q.2)

/-- **Joint smoothness of the two families** in the parameter and the chain parameter. -/
def SepFamSmooth {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace) : Prop :=
  ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2) ∧
  ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2)

/-- **The bumped charted difference system is `C^∞`** (without the parameter reparametrisation). -/
def SepBumpedSmooth {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace)
    (p : CappingSpace) (γ : EuclideanSpace ℝ (Fin m) → ℝ) (β : Amb 4 → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      (γ q.1 * β q.2) •
        FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2)

/-- **The parameter-derivative of the charted difference is onto** at `(τ, y)`.  This is the `hsurj`
hypothesis of the parametric-Sard bricks. -/
def SepChartDifSurj {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace)
    (p : CappingSpace) (τ : EuclideanSpace ℝ (Fin m)) (y : Amb 4) : Prop :=
  Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) =>
    FamBox.chartDif p (famLoop (Lf τ')) (famChain (N τ')) y) τ)

/-- **The family itself is continuous**, in the parameter and the box variable (both sides). -/
def SepFamContinuous {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace) : Prop :=
  Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2) ∧
  Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2)

/-- **A finite family of chart pieces covering the meet set of the family at the shift `0`**, with
the containment of both values of the family (for all shifts of norm `< ε₀`) in the source of the
corresponding chart, on the open sets `V i ⊇ K i`. -/
structure SepFamilyCover {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace) where
  /-- The number of chart pieces. -/
  r : ℕ
  /-- The chart centres. -/
  p : Fin r → CappingSpace
  /-- The compact pieces containing the meets. -/
  K : Fin r → Set (Amb 4)
  /-- The open sets on which the chart containment holds. -/
  V : Fin r → Set (Amb 4)
  /-- The radius of the parameter ball. -/
  ε₀ : ℝ
  hε₀ : 0 < ε₀
  hK : ∀ i, IsCompact (K i)
  hV : ∀ i, IsOpen (V i)
  hKV : ∀ i, K i ⊆ V i
  /-- The chart containment on `V i`, uniformly over the parameter ball. -/
  hchart : ∀ (i : Fin r) (τ : EuclideanSpace ℝ (Fin m)) (y : Amb 4), ‖τ‖ < ε₀ → y ∈ V i →
    famLoop (Lf τ) y ∈ (chr (p i)).source ∧ famChain (N τ) y ∈ (chr (p i)).source
  /-- Every meet at the shift `0` lies in the interior of a piece. -/
  hbase : ∀ y : Amb 4, y ∈ Submission.Drive.unitBox 4 →
    famLoop (Lf 0) y = famChain (N 0) y → y ∈ ⋃ i, interior (K i)

/-- The chart containment of a cover, in the packaged form `SepChartReg`. -/
lemma SepFamilyCover.chartReg {m : ℕ} {Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) →
      CappingSpace} {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace}
    (cov : SepFamilyCover Lf N) (i : Fin cov.r) :
    SepChartReg Lf N (cov.p i) (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (cov.ε₀))
      (cov.V i) := by
  rintro ⟨τ', y⟩ ⟨hτ', hy⟩
  exact cov.hchart i τ' y (by rwa [Metric.mem_ball, dist_zero_right] at hτ') hy

/-- **The loop family is jointly `C^∞`** in the shift and the loop parameter. -/
def SepLoopSmoothJoint {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) : Prop :=
  ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
      sepLoopFam Ξ Q A B q.1 q.2)

/-- `q` lies in the source of the chart at `p`. -/
def SepInChart (q p : CappingSpace) : Prop := q ∈ (chr p).source

/-- **The loop family at a fixed box point is `C^∞`** in the shift. -/
def SepLoopSmoothIn {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (y : Amb 4) : Prop :=
  ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun τ' : EuclideanSpace ℝ (Fin m) => famLoop (sepLoopFam Ξ Q A B τ') y)

/-- **The manifold-level parameter-derivative of the loop family is onto** at `(τ, y)`. -/
def SepLoopMfderivSurj {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) (y : Amb 4) : Prop :=
  Function.Surjective (mfderiv (𝓡 m) (𝓡 4)
    (fun τ' : EuclideanSpace ℝ (Fin m) => famLoop (sepLoopFam Ξ Q A B τ') y) τ)

/-- **The parameter-derivative of the charted loop value is onto** at `(τ, y)`. -/
def SepLoopChartSurj {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (p : CappingSpace) (τ : EuclideanSpace ℝ (Fin m)) (y : Amb 4) : Prop :=
  Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) =>
    chr p (famLoop (sepLoopFam Ξ Q A B τ') y)) τ)

/-- The `SepLoopChartSurj` conclusion implies the charted-difference form `SepChartDifSurj` when the
chain side does not depend on the parameter. -/
lemma SepChartDifSurj.of_loop_of_const {m : ℕ}
    {Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace}
    {p : CappingSpace} {τ : EuclideanSpace ℝ (Fin m)} {y : Amb 4}
    (hN : ∀ τ' : EuclideanSpace ℝ (Fin m), N τ' = N τ)
    (hS : Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) =>
      chr p (famLoop (Lf τ') y)) τ)) :
    SepChartDifSurj Lf N p τ y := by
  have hfun : (fun τ' : EuclideanSpace ℝ (Fin m) =>
      FamBox.chartDif p (famLoop (Lf τ')) (famChain (N τ')) y)
      = fun τ' : EuclideanSpace ℝ (Fin m) =>
          chr p (famLoop (Lf τ') y) + (-(chr p (famChain (N τ) y))) := by
    funext τ'
    rw [hN τ', FamBox.chartDif, sub_eq_add_neg]
  rw [SepChartDifSurj, hfun, fderiv_add_const]
  exact hS

/-! ## A bounded reparametrisation with everywhere-surjective derivative -/


/-- **A smooth bounded map whose derivative is surjective everywhere.** -/
theorem sep_squeeze_map (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      (∀ s, ‖σ s‖ ≤ δ) ∧
      (∀ s, Function.Surjective (fderiv ℝ σ s)) := by
  set c : ℝ := δ / (Real.pi * ((m : ℝ) + 1)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i)), ?_, ?_, ?_⟩
  · rw [contDiff_piLp]
    intro i
    exact (contDiff_const.mul
      (Real.contDiff_arctan.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).contDiff))
  · intro s
    have hb : ∀ i : Fin m,
        ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          ≤ (c * (Real.pi / 2)) ^ 2 := by
      intro i
      have h1 : |Real.arctan (s i)| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
          le_of_lt (Real.arctan_lt_pi_div_two _)⟩
      have h2 : |c * Real.arctan (s i)| ≤ c * (Real.pi / 2) := by
        rw [abs_mul, abs_of_nonneg hcpos.le]
        exact mul_le_mul_of_nonneg_left h1 hcpos.le
      have h3 : ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          = (c * Real.arctan (s i)) ^ 2 := by
        simp only [Real.norm_eq_abs]
        rw [sq_abs]
      rw [h3]
      calc (c * Real.arctan (s i)) ^ 2 = |c * Real.arctan (s i)| ^ 2 := by rw [sq_abs]
        _ ≤ (c * (Real.pi / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hsq : ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s‖ ^ 2 ≤ δ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (ι := Fin m) (β := fun _ : Fin m => ℝ)]
      calc ∑ i : Fin m, ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          ≤ ∑ _i : Fin m, (c * (Real.pi / 2)) ^ 2 := Finset.sum_le_sum (fun i _ => hb i)
        _ = (m : ℝ) * (c * (Real.pi / 2)) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ δ ^ 2 := by
              rw [hc]
              have h2 : (0 : ℝ) < Real.pi * ((m : ℝ) + 1) := by positivity
              field_simp
              nlinarith [sq_nonneg ((m : ℝ) + 1), hδ]
    nlinarith [norm_nonneg ((fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s),
      hδ, hsq]
  · intro s
    have hτ : HasFDerivAt
        (fun s' : EuclideanSpace ℝ (Fin m) => fun i : Fin m => c * Real.arctan (s' i))
        (ContinuousLinearMap.pi (fun i : Fin m =>
          (c * (1 + (s i) ^ 2)⁻¹) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) s := by
      rw [hasFDerivAt_pi]
      intro i
      have h := (Real.hasDerivAt_arctan (s i)).comp_hasFDerivAt s
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt
      have h2 : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin m) => c * Real.arctan (s' i))
          (c • ((1 / (1 + (s i) ^ 2)) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) s :=
        (h.const_smul c).congr_of_eventuallyEq (by
          filter_upwards with x
          rfl)
      rw [smul_smul, one_div] at h2
      exact h2
    have hσ : HasFDerivAt (fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i)))
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm :
          (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
          (ContinuousLinearMap.pi fun i : Fin m =>
            (c * (1 + (s i) ^ 2)⁻¹) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i)) s :=
      (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (fun i : Fin m => c * Real.arctan (s i))).comp s hτ
    rw [hσ.fderiv]
    have hdτsurj : Function.Surjective (ContinuousLinearMap.pi (fun i : Fin m =>
        (c * (1 + (s i) ^ 2)⁻¹) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) := by
      intro w
      refine ⟨WithLp.toLp 2 (fun i => w i / (c * (1 + (s i) ^ 2)⁻¹)), ?_⟩
      funext i
      simp only [ContinuousLinearMap.pi_apply, smul_apply, PiLp.proj_apply]
      have hne : c * (1 + (s i) ^ 2)⁻¹ ≠ 0 := by
        have h2 : 0 < 1 + (s i) ^ 2 := by positivity
        positivity
      rw [smul_eq_mul]
      field_simp
    intro w
    obtain ⟨u, hu⟩ := hdτsurj w.ofLp
    refine ⟨u, ?_⟩
    rw [ContinuousLinearMap.comp_apply, hu]
    exact WithLp.toLp_ofLp 2 w

end

end Work.Drive
