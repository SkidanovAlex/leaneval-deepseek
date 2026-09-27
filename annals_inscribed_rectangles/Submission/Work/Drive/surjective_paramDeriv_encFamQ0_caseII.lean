import Mathlib
import Submission.Work.Drive.encFamQ0
import Submission.Work.Drive.hrichCore
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.range_fderiv_chart_block0_frozen
import Submission.Work.Drive.range_fderiv_chart_planeBlock
import Submission.Work.Drive.deriv_thetaS_ne_zero_of_eq
import Submission.Work.Drive.blockZeroCoset
import Submission.Work.Drive.sup_inf_eq_top_of_triple_bot

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Case II of the richness `hrich` for the ends-clause family `encFamQ0`

At a zero `y` of the charted triple-difference map `TParity.chartDiff3 p (encFamQ0 H A B c₀ t)` at
which the time bump of block `0` vanishes (`betaG ((bPartC 0 y) 2) = 0`), the parameter derivative of
the charted triple-difference map is surjective onto `ℝ⁸`.

**Why.**  `betaG s = 0` for `s ∉ (0,1)`, and the homotopy is constant on the two ends, so block `0`
reduces to `F (Sh_{q₀} v)` with `F = H (0,·)` or `H (1,·)`.  Its parameter derivative has the
`2`-dimensional class reach `W₀ = range (dF)` (the shear contributes the plane directions, the level
is frozen at `c₀`), while the two plane blocks have the reaches `liftAll A'`, `liftAll B'` with
`A' = range dA`, `B' = range dB` (here the twist supplies a free level direction).  `PairReg` gives
`A' ⊔ B' = ⊤` and `EndTripleReg` gives `W₀ ⊓ A' ⊓ B' = ⊥`, hence `W₀ ⊔ (A' ⊓ B') = ⊤`, and the
coset lemma `Work.Drive.exists_coset_mem_lift` + the closer
`Work.Drive.surjective_pair_sub_of_coset` (both in `hrichCore.lean`) produce the surjectivity.

The file first builds the elementary vocabulary (the six block projections of the parameter
`EncParQ0` as continuous linear maps, the vanishing locus of `betaG`, the splitting of the source of
the transported chart `chr`, the differentiability of the charted block maps) and then the
assembly.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option backward.isDefEq.respectTransparency false

section Helpers

attribute [local instance] Work.Drive.projCharted Work.Drive.isManifold_projCharted
  Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-- The product charted structure on `ℝP³ × ℝ`, made a local instance so that instance search finds
it (it cannot see through the `def` `ModelProd`). -/
local instance q0ProdCharted : ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ)
    (Projectivization ℝ (Eucl 3) × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-! ## 1. The source of the transported chart -/

/-- **The chart of `ℝP³ × ℝ` is `psiLin ∘ (projective chart × identity)`.  Local copy of
`Work.Drive.chr_projTimesLine_apply` (whose instance arguments are local to its file). -/
theorem q0_chr_apply (p z : Projectivization ℝ (Eucl 3) × ℝ) :
    chr p z = psiLin (chartAt (EuclideanSpace ℝ (Fin 3)) p.1 z.1, z.2) := by
  rw [show (chr p : Projectivization ℝ (Eucl 3) × ℝ → EuclideanSpace ℝ (Fin 4))
      = fun z => psiLin (chartAt (EuclideanSpace ℝ (Fin 3) × ℝ) p z) from
    chartAt_chartedSpaceChangeModel_apply (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin p]
  rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
  simp

/-- **The source of the transported chart is a product of sources.** -/
theorem q0_chr_source (p : Projectivization ℝ (Eucl 3) × ℝ) :
    (chr p).source
      = (chartAt (EuclideanSpace ℝ (Fin 3)) p.1).source ×ˢ (chartAt ℝ p.2).source := by
  show (chartAt (EuclideanSpace ℝ (Fin 4)) p : OpenPartialHomeomorph _ _).source = _
  rw [show (chartAt (EuclideanSpace ℝ (Fin 4)) p : OpenPartialHomeomorph _ _)
      = (chartAt (EuclideanSpace ℝ (Fin 3) × ℝ) p).trans
          psiLin.toHomeomorph.toOpenPartialHomeomorph from rfl]
  rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ, prodChartedSpace_chartAt,
    OpenPartialHomeomorph.prod_source]

/-- The class component of a point of the source of `chr p` lies in the source of the projective
chart at `p.1`. -/
theorem q0_fst_mem_source {p z : Projectivization ℝ (Eucl 3) × ℝ} (hz : z ∈ (chr p).source) :
    z.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p.1).source := by
  have h := hz
  rw [q0_chr_source] at h
  exact h.1

/-! ## 2. The vanishing locus of the time bump -/

/-- **`betaG s = 0` exactly outside the open unit interval.** -/
theorem betaG_eq_zero_iff (s : ℝ) : betaG s = 0 ↔ s ≤ 0 ∨ 1 ≤ s := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd h (ne_of_gt (betaG_pos hcon.1 hcon.2))
  · rintro (h | h)
    · exact betaG_nonneg_of_le h
    · exact betaG_nonneg_of_one_le h


/-! ## 3. The block projections of the parameter `EncParQ0` -/

private abbrev Q0E4 := EuclideanSpace ℝ (Fin 4)
private abbrev Q0T1 := Q0E4 × (Q0E4 × (Q0E4 × (ℝ × ℝ)))
private abbrev Q0T2 := Q0E4 × (Q0E4 × (ℝ × ℝ))
private abbrev Q0T3 := Q0E4 × (ℝ × ℝ)

private def q0t1 : EncParQ0 →L[ℝ] Q0T1 := ContinuousLinearMap.snd ℝ Q0E4 Q0T1
private def q0t2 : Q0T1 →L[ℝ] Q0T2 := ContinuousLinearMap.snd ℝ Q0E4 Q0T2
private def q0t3 : Q0T2 →L[ℝ] Q0T3 := ContinuousLinearMap.snd ℝ Q0E4 Q0T3
private def q0t4 : Q0T3 →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.snd ℝ Q0E4 (ℝ × ℝ)

/-- The class-perturbation parameter as a continuous linear map. -/
def q0PCLM : EncParQ0 →L[ℝ] Q0E4 := ContinuousLinearMap.fst ℝ Q0E4 Q0T1
/-- The shear parameter of block `0` as a continuous linear map. -/
def q0Q0CLM : EncParQ0 →L[ℝ] Q0E4 := (ContinuousLinearMap.fst ℝ Q0E4 Q0T2).comp q0t1
/-- The shear parameter of block `1` as a continuous linear map. -/
def q0Q1CLM : EncParQ0 →L[ℝ] Q0E4 := (ContinuousLinearMap.fst ℝ Q0E4 Q0T3).comp (q0t2.comp q0t1)
/-- The shear parameter of block `2` as a continuous linear map. -/
def q0Q2CLM : EncParQ0 →L[ℝ] Q0E4 :=
  (ContinuousLinearMap.fst ℝ Q0E4 (ℝ × ℝ)).comp (q0t3.comp (q0t2.comp q0t1))
/-- The level twist of block `1` as a continuous linear map. -/
def q0R1CLM : EncParQ0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (q0t4.comp (q0t3.comp (q0t2.comp q0t1)))
/-- The level twist of block `2` as a continuous linear map. -/
def q0R2CLM : EncParQ0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (q0t4.comp (q0t3.comp (q0t2.comp q0t1)))

@[simp] lemma q0PCLM_apply (t : EncParQ0) : q0PCLM t = q0P t := rfl
@[simp] lemma q0Q0CLM_apply (t : EncParQ0) : q0Q0CLM t = q0Q0 t := rfl
@[simp] lemma q0Q1CLM_apply (t : EncParQ0) : q0Q1CLM t = q0Q1 t := rfl
@[simp] lemma q0Q2CLM_apply (t : EncParQ0) : q0Q2CLM t = q0Q2 t := rfl
@[simp] lemma q0R1CLM_apply (t : EncParQ0) : q0R1CLM t = q0R1 t := rfl
@[simp] lemma q0R2CLM_apply (t : EncParQ0) : q0R2CLM t = q0R2 t := rfl

/-- The shear map of the block `0`-projection is onto `𝔼⁴`. -/
lemma surjective_q0Q0CLM : Function.Surjective q0Q0CLM :=
  fun v => ⟨⟨0, v, 0, 0, 0, 0⟩, rfl⟩

/-- The `(shear, twist)` map of block `1` is onto `𝔼⁴ × ℝ`. -/
lemma surjective_q0Q1R1 : Function.Surjective (fun t : EncParQ0 => (q0Q1CLM t, q0R1CLM t)) :=
  fun p => ⟨⟨0, 0, p.1, 0, p.2, 0⟩, rfl⟩

/-- The `(shear, twist)` map of block `2` is onto `𝔼⁴ × ℝ`. -/
lemma surjective_q0Q2R2 : Function.Surjective (fun t : EncParQ0 => (q0Q2CLM t, q0R2CLM t)) :=
  fun p => ⟨⟨0, 0, 0, p.1, 0, p.2⟩, rfl⟩

/-- **The mixed parameter**: block `0` read from `u₀`, blocks `1`, `2` from `u₁`, `u₂`. -/
def q0Mix (tp u₀ u₁ u₂ : EncParQ0) : EncParQ0 :=
  ⟨q0PCLM tp, q0Q0CLM u₀, q0Q1CLM u₁, q0Q2CLM u₂, q0R1CLM u₁, q0R2CLM u₂⟩

@[simp] lemma q0PCLM_q0Mix (tp u₀ u₁ u₂ : EncParQ0) :
    q0PCLM (q0Mix tp u₀ u₁ u₂) = q0PCLM tp := rfl
@[simp] lemma q0Q0CLM_q0Mix (tp u₀ u₁ u₂ : EncParQ0) :
    q0Q0CLM (q0Mix tp u₀ u₁ u₂) = q0Q0CLM u₀ := rfl
@[simp] lemma q0Q1CLM_q0Mix (tp u₀ u₁ u₂ : EncParQ0) :
    q0Q1CLM (q0Mix tp u₀ u₁ u₂) = q0Q1CLM u₁ := rfl
@[simp] lemma q0Q2CLM_q0Mix (tp u₀ u₁ u₂ : EncParQ0) :
    q0Q2CLM (q0Mix tp u₀ u₁ u₂) = q0Q2CLM u₂ := rfl
@[simp] lemma q0R1CLM_q0Mix (tp u₀ u₁ u₂ : EncParQ0) :
    q0R1CLM (q0Mix tp u₀ u₁ u₂) = q0R1CLM u₁ := rfl
@[simp] lemma q0R2CLM_q0Mix (tp u₀ u₁ u₂ : EncParQ0) :
    q0R2CLM (q0Mix tp u₀ u₁ u₂) = q0R2CLM u₂ := rfl

/-! ## 4. Differentiability of the charted block maps -/

private abbrev QB2 := EuclideanSpace ℝ (Fin 2)
private abbrev QB3 := EuclideanSpace ℝ (Fin 3)
private abbrev QB4 := EuclideanSpace ℝ (Fin 4)
private abbrev QP3 := Projectivization ℝ (Eucl 3)

/-- The parameter map `q' ↦ shear q' u` is differentiable (local copy of the first step of
`Work.Drive.range_fderiv_chart_planeBlock`). -/
theorem differentiableAt_shear_param (u : QB2) (q : QB4) :
    DifferentiableAt ℝ (fun q' : QB4 => shear q' u) q := by
  have hfun : (fun q' : QB4 => shear q' u) = fun q' => spdPhiT u (ballClamp q') := by
    funext q'
    exact (spdPhiT_ballClamp q' u).symm
  rw [hfun]
  exact (spdDifferentiableAt_PhiT u (ballClamp q)).comp q
    (spdHasFDerivAt_ballClamp q).differentiableAt

/-- **Block `0`**: the charted frozen map `z ↦ chr p (E (shear z u), c₀)` is differentiable. -/
theorem differentiableAt_chr_block0Frozen
    (E : QB2 → QP3) (hE : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (u : QB2) (q : QB4) (c₀ : ℝ) (p : QP3 × ℝ)
    (hsrc : E (shear q u) ∈ (chartAt (QB3) p.1).source) :
    DifferentiableAt ℝ (fun z : QB4 => chr p (E (shear z u), c₀)) q := by
  have hsm : MDifferentiableAt (𝓡 2) (𝓡 3) E (shear q u) := hE.mdifferentiableAt (by simp)
  have hL' : MDifferentiableAt (𝓡 4) (𝓡 2) (fun q' : QB4 => shear q' u) q :=
    (differentiableAt_shear_param u q).mdifferentiableAt
  have hC : MDifferentiableAt (𝓡 4) (𝓡 3) (fun q' : QB4 => E (shear q' u)) q := hsm.comp q hL'
  have hF₁ : HasFDerivAt (fun q' : QB4 => chartAt (QB3) p.1 (E (shear q' u)))
      ((tangentCoordChange (𝓡 3) (E (shear q u)) p.1 (E (shear q u))).comp
        (mfderiv (𝓡 4) (𝓡 3) (fun q' : QB4 => E (shear q' u)) q)) q :=
    hasFDerivAt_chartAt_comp (fun q' : QB4 => E (shear q' u)) p.1 hC hsrc
  have hf : DifferentiableAt ℝ (fun q' : QB4 => chartAt (QB3) p.1 (E (shear q' u))) q :=
    hF₁.differentiableAt
  have hfun : (fun z : QB4 => chr p (E (shear z u), c₀))
      = fun z => psiLin ((fun q' : QB4 => chartAt (QB3) p.1 (E (shear q' u))) z, c₀) := by
    funext z
    rw [q0_chr_apply]
  rw [hfun]
  have hpairdiff : DifferentiableAt ℝ
      (fun z : QB4 => ((fun q' : QB4 => chartAt (QB3) p.1 (E (shear q' u))) z, c₀)) q :=
    hf.prodMk (differentiableAt_const c₀)
  exact psiLin.differentiableAt.comp q hpairdiff

/-- **A plane block**: the charted map `z ↦ chr p (A (shear z.1 u), thetaS z.2 v)` is
differentiable. -/
theorem differentiableAt_chr_planeBlock
    (A : QB2 → QP3) (hA : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (u : QB2) (q : QB4) (r v : ℝ) (p : QP3 × ℝ)
    (hsrc : A (shear q u) ∈ (chartAt (QB3) p.1).source) :
    DifferentiableAt ℝ (fun z : QB4 × ℝ => chr p (A (shear z.1 u), thetaS z.2 v)) (q, r) := by
  have hsm : MDifferentiableAt (𝓡 2) (𝓡 3) A (shear q u) := hA.mdifferentiableAt (by simp)
  have hL' : MDifferentiableAt (𝓡 4) (𝓡 2) (fun q' : QB4 => shear q' u) q :=
    (differentiableAt_shear_param u q).mdifferentiableAt
  have hC : MDifferentiableAt (𝓡 4) (𝓡 3) (fun q' : QB4 => A (shear q' u)) q := hsm.comp q hL'
  have hF₁ : HasFDerivAt (fun q' : QB4 => chartAt (QB3) p.1 (A (shear q' u)))
      ((tangentCoordChange (𝓡 3) (A (shear q u)) p.1 (A (shear q u))).comp
        (mfderiv (𝓡 4) (𝓡 3) (fun q' : QB4 => A (shear q' u)) q)) q :=
    hasFDerivAt_chartAt_comp (fun q' : QB4 => A (shear q' u)) p.1 hC hsrc
  have hf : DifferentiableAt ℝ (fun q' : QB4 => chartAt (QB3) p.1 (A (shear q' u))) q :=
    hF₁.differentiableAt
  have hgCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r' : ℝ => thetaS r' v) :=
    contDiff_shear_thetaS.2.comp (contDiff_id.prodMk contDiff_const)
  have hg : DifferentiableAt ℝ (fun r' : ℝ => thetaS r' v) r :=
    hgCD.contDiffAt.differentiableAt (by simp)
  have hfun : (fun z : QB4 × ℝ => chr p (A (shear z.1 u), thetaS z.2 v))
      = fun z => psiLin ((fun q' : QB4 => chartAt (QB3) p.1 (A (shear q' u))) z.1,
          (fun r' : ℝ => thetaS r' v) z.2) := by
    funext z
    rw [q0_chr_apply]
  rw [hfun]
  have h1c : DifferentiableAt ℝ
      ((fun q' : QB4 => chartAt (QB3) p.1 (A (shear q' u))) ∘ Prod.fst) (q, r) :=
    hf.comp (q, r) differentiableAt_fst
  have h2c : DifferentiableAt ℝ ((fun r' : ℝ => thetaS r' v) ∘ Prod.snd) (q, r) :=
    hg.comp (q, r) differentiableAt_snd
  have hpairdiff : DifferentiableAt ℝ
      (fun z : QB4 × ℝ => ((fun q' : QB4 => chartAt (QB3) p.1 (A (shear q' u))) z.1,
        (fun r' : ℝ => thetaS r' v) z.2)) (q, r) :=
    h1c.prodMk h2c
  exact psiLin.differentiableAt.comp (q, r) hpairdiff

/-- The end map of the homotopy, read on the first two coordinates of `𝔼³`, is smooth. -/
theorem contMDiff_endMk2 (E : QB2 → QP3) (hE : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) E) :
    ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : QB3 => E (mk2 (x 0) (x 1))) :=
  hE.comp mk2CLM.contMDiff

/-! ## 5. The Case-II assembly -/

/-- **The Case-II assembly.**  Everything is expressed in terms of the end map `E` (`= H (0,·)` or
`H (1,·)`, equal to the block-`0` slice `H (s,·)` of the homotopy at the meet). -/
private theorem caseII_body
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (hAsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hBsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hfoldA : FoldFlat A) (hfoldB : FoldFlat B)
    (hpair : PairReg A B)
    (s : ℝ) (E : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hEeq : ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = E y)
    (hEsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hEfold : FoldFlat E) (hEreg : EndTripleReg E A B)
    (p : Projectivization ℝ (Eucl 3) × ℝ) (t : EncParQ0) (y : EuclideanSpace ℝ (Fin 9))
    (u₀ u₁ u₂ : EuclideanSpace ℝ (Fin 2)) (v₁ v₂ : ℝ)
    (hu₀ : pt2 ((TParity.bPartC 0 y) 0) ((TParity.bPartC 0 y) 1) = u₀)
    (hu₁ : pt2 ((TParity.bPartC 1 y) 0) ((TParity.bPartC 1 y) 1) = u₁)
    (hu₂ : pt2 ((TParity.bPartC 2 y) 0) ((TParity.bPartC 2 y) 1) = u₂)
    (hv₁ : (TParity.bPartC 1 y) 2 = v₁) (hv₂ : (TParity.bPartC 2 y) 2 = v₂)
    (hsrc : ∀ k : Fin 3, encFamQ0 H A B c₀ t k (TParity.bPartC k y) ∈ (chr p).source)
    (hzero : TParity.chartDiff3 p (encFamQ0 H A B c₀ t) y = 0)
    (hbeta : betaG s = 0) (hs : (TParity.bPartC 0 y) 2 = s) :
    Function.Surjective
      (fderiv ℝ (fun t' => TParity.chartDiff3 p (encFamQ0 H A B c₀ t') y) t) := by
  -- (0) the meet
  have hmeet : TParity.meet3 (encFamQ0 H A B c₀ t) y :=
    (TParity.chartDiff3_eq_zero_iff (p := p) (D := encFamQ0 H A B c₀ t) (x := y) hsrc).mp hzero
  -- (1) the value-level identifications of the three blocks
  have hval0 : ∀ t' : EncParQ0, encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)
      = (E (shear (q0Q0 t') u₀), c₀) := by
    intro t'
    simp only [encFamQ0_apply_zero, encFamQ0₀]
    rw [hs, hbeta, zero_smul, chartPert_zero, clsSh_capOf, hu₀, hEeq]
  have hval1 : ∀ t' : EncParQ0, encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y)
      = (A (shear (q0Q1 t') u₁), thetaS (q0R1 t') v₁) := by
    intro t'
    simp only [encFamQ0_apply_one, hu₁, hv₁]
  have hval2 : ∀ t' : EncParQ0, encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y)
      = (B (shear (q0Q2 t') u₂), thetaS (q0R2 t') v₂) := by
    intro t'
    simp only [encFamQ0_apply_two, hu₂, hv₂]
  -- (2) the class and level equalities at the meet
  have hclass1 : A (shear (q0Q1 t) u₁) = E (shear (q0Q0 t) u₀) := by
    have h := congrArg Prod.fst hmeet.1
    simp only [encFamQ0_apply_zero, encFamQ0_apply_one, encFamQ0₀] at h
    rw [hs, hbeta, zero_smul, chartPert_zero, clsSh_capOf, hu₀, hu₁] at h
    exact h.symm.trans (hEeq _)
  have hclass2 : B (shear (q0Q2 t) u₂) = E (shear (q0Q0 t) u₀) := by
    have h := congrArg Prod.fst hmeet.2
    simp only [encFamQ0_apply_zero, encFamQ0_apply_two, encFamQ0₀] at h
    rw [hs, hbeta, zero_smul, chartPert_zero, clsSh_capOf, hu₀, hu₂] at h
    exact h.symm.trans (hEeq _)
  have hlevel1 : thetaS (q0R1 t) v₁ = c₀ := by
    have h := congrArg Prod.snd hmeet.1
    simp only [encFamQ0_apply_zero, encFamQ0_apply_one, encFamQ0₀] at h
    rw [hv₁] at h
    exact h.symm
  have hlevel2 : thetaS (q0R2 t) v₂ = c₀ := by
    have h := congrArg Prod.snd hmeet.2
    simp only [encFamQ0_apply_zero, encFamQ0_apply_two, encFamQ0₀] at h
    rw [hv₂] at h
    exact h.symm
  -- (3) the sources of the projective chart
  have hsrcC0 : E (shear (q0Q0 t) u₀) ∈ (chartAt (QB3) p.1).source := by
    have h := hsrc 0
    rw [hval0 t] at h
    exact q0_fst_mem_source h
  have hsrcC1 : A (shear (q0Q1 t) u₁) ∈ (chartAt (QB3) p.1).source := by
    have h := hsrc 1
    rw [hval1 t] at h
    exact q0_fst_mem_source h
  have hsrcC2 : B (shear (q0Q2 t) u₂) ∈ (chartAt (QB3) p.1).source := by
    have h := hsrc 2
    rw [hval2 t] at h
    exact q0_fst_mem_source h
  -- (4) the block maps on the parameter space
  have hblock0fun : (fun t' : EncParQ0 => chr p (E (shear (q0Q0 t') u₀), c₀))
      = (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y))) := by
    funext t'
    simp only [hval0 t']
  have hblock1fun : (fun t' : EncParQ0 => chr p (A (shear (q0Q1CLM t') u₁), thetaS (q0R1CLM t') v₁))
      = (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y))) := by
    funext t'
    simp only [hval1 t', q0Q1CLM_apply, q0R1CLM_apply]
  have hblock2fun : (fun t' : EncParQ0 => chr p (B (shear (q0Q2CLM t') u₂), thetaS (q0R2CLM t') v₂))
      = (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y))) := by
    funext t'
    simp only [hval2 t', q0Q2CLM_apply, q0R2CLM_apply]
  -- (5) the parameter derivatives of the three blocks
  set E₀ : QB4 →L[ℝ] Tgt 4 :=
    fderiv ℝ (fun z : QB4 => chr p (E (shear z u₀), c₀)) (q0Q0 t) with hE₀def
  set E₁ : (QB4 × ℝ) →L[ℝ] Tgt 4 :=
    fderiv ℝ (fun z : QB4 × ℝ => chr p (A (shear z.1 u₁), thetaS z.2 v₁)) (q0Q1 t, q0R1 t)
    with hE₁def
  set E₂ : (QB4 × ℝ) →L[ℝ] Tgt 4 :=
    fderiv ℝ (fun z : QB4 × ℝ => chr p (B (shear z.1 u₂), thetaS z.2 v₂)) (q0Q2 t, q0R2 t)
    with hE₂def
  set D0 : EncParQ0 →L[ℝ] Tgt 4 := E₀.comp q0Q0CLM with hD0def
  set D1 : EncParQ0 →L[ℝ] Tgt 4 := E₁.comp (q0Q1CLM.prod q0R1CLM) with hD1def
  set D2 : EncParQ0 →L[ℝ] Tgt 4 := E₂.comp (q0Q2CLM.prod q0R2CLM) with hD2def
  have hD0 : HasFDerivAt
      (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y))) D0 t := by
    have h0 := (differentiableAt_chr_block0Frozen E hEsm u₀ (q0Q0 t) c₀ p hsrcC0).hasFDerivAt.comp
      t q0Q0CLM.hasFDerivAt
    simp only [Function.comp_def] at h0
    rw [hblock0fun] at h0
    exact h0
  have hD1 : HasFDerivAt
      (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y))) D1 t := by
    have h1 := (differentiableAt_chr_planeBlock A hAsm u₁ (q0Q1 t) (q0R1 t) v₁ p hsrcC1).hasFDerivAt.comp
      t (q0Q1CLM.prod q0R1CLM).hasFDerivAt
    simp only [Function.comp_def, ContinuousLinearMap.prod_apply] at h1
    rw [hblock1fun] at h1
    exact h1
  have hD2 : HasFDerivAt
      (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y))) D2 t := by
    have h2 := (differentiableAt_chr_planeBlock B hBsm u₂ (q0Q2 t) (q0R2 t) v₂ p hsrcC2).hasFDerivAt.comp
      t (q0Q2CLM.prod q0R2CLM).hasFDerivAt
    simp only [Function.comp_def, ContinuousLinearMap.prod_apply] at h2
    rw [hblock2fun] at h2
    exact h2
  -- (6) the change of coordinates and the three reaches
  set cstar : Projectivization ℝ (Eucl 3) := E (shear (q0Q0 t) u₀) with hcstardef
  set tcc : QB3 →L[ℝ] QB3 := tangentCoordChange (𝓡 3) cstar p.1 cstar with htccdef
  set tcc' : QB3 →L[ℝ] QB3 := tangentCoordChange (𝓡 3) p.1 cstar cstar with htcc'def
  set rW : Submodule ℝ QB3 := (mfderiv (𝓡 2) (𝓡 3) E (shear (q0Q0 t) u₀)).range with hrWdef
  set rA : Submodule ℝ QB3 := (mfderiv (𝓡 2) (𝓡 3) A (shear (q0Q1 t) u₁)).range with hrAdef
  set rB : Submodule ℝ QB3 := (mfderiv (𝓡 2) (𝓡 3) B (shear (q0Q2 t) u₂)).range with hrBdef
  set W₀ : Submodule ℝ QB3 := Submodule.map tcc.toLinearMap rW with hW₀def
  set A' : Submodule ℝ QB3 := Submodule.map tcc.toLinearMap rA with hA'def
  set B' : Submodule ℝ QB3 := Submodule.map tcc.toLinearMap rB with hB'def
  have hcstar_src : cstar ∈ (extChartAt (𝓡 3) p.1).source := by
    rw [extChartAt_source]
    exact hsrcC0
  have htcc'_tcc : ∀ v : QB3, tcc' (tcc v) = v := by
    intro v
    have h : cstar ∈ (extChartAt (𝓡 3) cstar).source ∩ (extChartAt (𝓡 3) p.1).source ∩
        (extChartAt (𝓡 3) cstar).source :=
      ⟨⟨mem_extChartAt_source cstar, hcstar_src⟩, mem_extChartAt_source cstar⟩
    have h2 := tangentCoordChange_comp (I := 𝓡 3) (w := cstar) (x := p.1) (y := cstar) (z := cstar)
      (v := v) h
    rw [tangentCoordChange_self (I := 𝓡 3) (x := cstar) (z := cstar)
      (mem_extChartAt_source cstar)] at h2
    simpa only [htccdef, htcc'def] using h2
  have htcc_tcc' : ∀ v : QB3, tcc (tcc' v) = v := by
    intro v
    have h : cstar ∈ (extChartAt (𝓡 3) p.1).source ∩ (extChartAt (𝓡 3) cstar).source ∩
        (extChartAt (𝓡 3) p.1).source :=
      ⟨⟨hcstar_src, mem_extChartAt_source cstar⟩, hcstar_src⟩
    have h2 := tangentCoordChange_comp (I := 𝓡 3) (w := p.1) (x := cstar) (y := p.1) (z := cstar)
      (v := v) h
    rw [tangentCoordChange_self (I := 𝓡 3) (x := p.1) (z := cstar) hcstar_src] at h2
    simpa only [htccdef, htcc'def] using h2
  let e : QB3 ≃ₗ[ℝ] QB3 := LinearEquiv.ofLinearMap tcc.toLinearMap tcc'.toLinearMap
    (LinearMap.ext (fun v => htcc_tcc' v)) (LinearMap.ext (fun v => htcc'_tcc v))
  have htcc_surj : Function.Surjective tcc := fun v => ⟨tcc' v, htcc_tcc' v⟩
  obtain ⟨hfA0, hfA1⟩ := (foldFlat_iff A).mp hfoldA
  obtain ⟨hfB0, hfB1⟩ := (foldFlat_iff B).mp hfoldB
  have hderiv1 : deriv (fun r' : ℝ => thetaS r' v₁) (q0R1 t) ≠ 0 :=
    deriv_thetaS_ne_zero_of_eq v₁ (q0R1 t) c₀ hc₀0 hc₀1 hlevel1
  have hderiv2 : deriv (fun r' : ℝ => thetaS r' v₂) (q0R2 t) ≠ 0 :=
    deriv_thetaS_ne_zero_of_eq v₂ (q0R2 t) c₀ hc₀0 hc₀1 hlevel2
  have hE₀range : E₀.range = lift0 W₀ := by
    have h := range_fderiv_chart_block0_frozen (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => E q.2)
      u₀ (q0Q0 t) s c₀ p (contMDiff_endMk2 E hEsm) hEfold hsrcC0
    rw [hE₀def]
    simpa only [hW₀def, htccdef, hrWdef, hcstardef] using h
  have hE₁range : E₁.range = liftAll A' := by
    have h := range_fderiv_chart_planeBlock A u₁ (q0Q1 t) (q0R1 t) v₁ p hAsm hfA0 hfA1 hderiv1 hsrcC1
    rw [hE₁def]
    rw [hclass1] at h
    simpa only [hA'def, htccdef, hrAdef, hcstardef] using h
  have hE₂range : E₂.range = liftAll B' := by
    have h := range_fderiv_chart_planeBlock B u₂ (q0Q2 t) (q0R2 t) v₂ p hBsm hfB0 hfB1 hderiv2 hsrcC2
    rw [hE₂def]
    rw [hclass2] at h
    simpa only [hB'def, htccdef, hrBdef, hcstardef] using h
  have hD0range : D0.range = lift0 W₀ := by
    have hle1 : (E₀.comp q0Q0CLM).range ≤ E₀.range := by
      rintro y ⟨u, rfl⟩
      exact ⟨q0Q0CLM u, rfl⟩
    have hle2 : E₀.range ≤ (E₀.comp q0Q0CLM).range := by
      rintro y ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_q0Q0CLM w
      exact ⟨u, rfl⟩
    rw [hD0def]
    exact (le_antisymm hle1 hle2).trans hE₀range
  have hD1range : D1.range = liftAll A' := by
    have hle1 : (E₁.comp (q0Q1CLM.prod q0R1CLM)).range ≤ E₁.range := by
      rintro y ⟨u, rfl⟩
      exact ⟨(q0Q1CLM.prod q0R1CLM) u, rfl⟩
    have hle2 : E₁.range ≤ (E₁.comp (q0Q1CLM.prod q0R1CLM)).range := by
      rintro y ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_q0Q1R1 w
      exact ⟨u, rfl⟩
    rw [hD1def]
    exact (le_antisymm hle1 hle2).trans hE₁range
  have hD2range : D2.range = liftAll B' := by
    have hle1 : (E₂.comp (q0Q2CLM.prod q0R2CLM)).range ≤ E₂.range := by
      rintro y ⟨u, rfl⟩
      exact ⟨(q0Q2CLM.prod q0R2CLM) u, rfl⟩
    have hle2 : E₂.range ≤ (E₂.comp (q0Q2CLM.prod q0R2CLM)).range := by
      rintro y ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_q0Q2R2 w
      exact ⟨u, rfl⟩
    rw [hD2def]
    exact (le_antisymm hle1 hle2).trans hE₂range
  -- (7) the linear algebra of the reaches
  have hreg := hEreg (shear (q0Q0 t) u₀) (shear (q0Q1 t) u₁) (shear (q0Q2 t) u₂)
    hclass1.symm hclass2.symm
  have hfinW : Module.finrank ℝ (mfderiv (𝓡 2) (𝓡 3) E (shear (q0Q0 t) u₀)).range = 2 := by
    rw [LinearMap.finrank_range_of_inj hreg.1]
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp [finrank_euclideanSpace]
  have hfinA : Module.finrank ℝ (mfderiv (𝓡 2) (𝓡 3) A (shear (q0Q1 t) u₁)).range = 2 := by
    rw [LinearMap.finrank_range_of_inj hreg.2.1]
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp [finrank_euclideanSpace]
  have hfinB : Module.finrank ℝ (mfderiv (𝓡 2) (𝓡 3) B (shear (q0Q2 t) u₂)).range = 2 := by
    rw [LinearMap.finrank_range_of_inj hreg.2.2.1]
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp [finrank_euclideanSpace]
  have hdimW : Module.finrank ℝ W₀ = 2 := by
    have h1 : Module.finrank ℝ (Submodule.map (e : QB3 →ₗ[ℝ] QB3) rW) = 2 := by
      rw [LinearEquiv.finrank_map_eq, hrWdef]
      exact hfinW
    rw [hW₀def]
    exact h1
  have hdimA : Module.finrank ℝ A' = 2 := by
    have h1 : Module.finrank ℝ (Submodule.map (e : QB3 →ₗ[ℝ] QB3) rA) = 2 := by
      rw [LinearEquiv.finrank_map_eq, hrAdef]
      exact hfinA
    rw [hA'def]
    exact h1
  have hdimB : Module.finrank ℝ B' = 2 := by
    have h1 : Module.finrank ℝ (Submodule.map (e : QB3 →ₗ[ℝ] QB3) rB) = 2 := by
      rw [LinearEquiv.finrank_map_eq, hrBdef]
      exact hfinB
    rw [hB'def]
    exact h1
  have hAB : A' ⊔ B' = ⊤ := by
    have hp : rA ⊔ rB = ⊤ := hpair (shear (q0Q1 t) u₁) (shear (q0Q2 t) u₂)
      (hclass1.trans hclass2.symm)
    rw [hA'def, hB'def, ← Submodule.map_sup, hp, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr htcc_surj
  have htri : W₀ ⊓ A' ⊓ B' = ⊥ := by
    have htri' : Submodule.map (e : QB3 →ₗ[ℝ] QB3) rW ⊓ Submodule.map (e : QB3 →ₗ[ℝ] QB3) rA ⊓
        Submodule.map (e : QB3 →ₗ[ℝ] QB3) rB = ⊥ := by
      rw [← Submodule.map_inf (e : QB3 →ₗ[ℝ] QB3) e.injective,
        ← Submodule.map_inf (e : QB3 →ₗ[ℝ] QB3) e.injective,
        hreg.2.2.2, Submodule.map_bot]
    rw [hW₀def, hA'def, hB'def]
    exact htri'
  have hWsup : W₀ ⊔ (A' ⊓ B') = ⊤ :=
    sup_inf_eq_top_of_triple_bot W₀ A' B' hAB htri hdimW hdimA hdimB
  -- (8) the coset condition, realisability and the closer
  have hcoset : ∀ w₁ w₂ : Tgt 4,
      ∃ a ∈ lift0 W₀, a - w₁ ∈ liftAll A' ∧ a - w₂ ∈ liftAll B' :=
    fun w₁ w₂ => exists_coset_mem_lift W₀ A' B' hAB hWsup w₁ w₂
  have hreal : ∀ a ∈ lift0 W₀, ∀ b ∈ liftAll A', ∀ c ∈ liftAll B',
      ∃ u : EncParQ0, D0 u = a ∧ D1 u = b ∧ D2 u = c := by
    intro a ha b hb c hc
    have h0 : a ∈ D0.range := by rw [hD0range]; exact ha
    have h1 : b ∈ D1.range := by rw [hD1range]; exact hb
    have h2 : c ∈ D2.range := by rw [hD2range]; exact hc
    obtain ⟨u₀', hu₀'⟩ := LinearMap.mem_range.mp h0
    obtain ⟨u₁', hu₁'⟩ := LinearMap.mem_range.mp h1
    obtain ⟨u₂', hu₂'⟩ := LinearMap.mem_range.mp h2
    refine ⟨q0Mix t u₀' u₁' u₂', ?_, ?_, ?_⟩
    · have hmix : D0 (q0Mix t u₀' u₁' u₂') = D0 u₀' := by
        rw [hD0def]
        show E₀ (q0Q0CLM (q0Mix t u₀' u₁' u₂')) = E₀ (q0Q0CLM u₀')
        rw [q0Q0CLM_q0Mix]
      exact hmix.trans hu₀'
    · have hmix : D1 (q0Mix t u₀' u₁' u₂') = D1 u₁' := by
        rw [hD1def]
        show E₁ ((q0Q1CLM.prod q0R1CLM) (q0Mix t u₀' u₁' u₂')) =
          E₁ ((q0Q1CLM.prod q0R1CLM) u₁')
        rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply,
          q0Q1CLM_q0Mix, q0R1CLM_q0Mix]
      exact hmix.trans hu₁'
    · have hmix : D2 (q0Mix t u₀' u₁' u₂') = D2 u₂' := by
        rw [hD2def]
        show E₂ ((q0Q2CLM.prod q0R2CLM) (q0Mix t u₀' u₁' u₂')) =
          E₂ ((q0Q2CLM.prod q0R2CLM) u₂')
        rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply,
          q0Q2CLM_q0Mix, q0R2CLM_q0Mix]
      exact hmix.trans hu₂'
  have hsurj : Function.Surjective (fun u : EncParQ0 => (D0 u - D1 u, D0 u - D2 u)) :=
    surjective_pair_sub_of_coset D0 D1 D2 (lift0 W₀) (liftAll A') (liftAll B')
      (le_of_eq hD0range) (le_of_eq hD1range) (le_of_eq hD2range) hreal hcoset
  -- (9) the derivative of the charted triple-difference map
  have hpUp_surj : Function.Surjective TParity.pUpCLM := fun w =>
    ⟨(TParity.fst8 w, TParity.snd8 w), by
      rw [TParity.pUpCLM_apply, TParity.pUp_fst8_snd8]⟩
  have hpairHD : HasFDerivAt (fun t' : EncParQ0 =>
      (((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y))),
        ((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y)))))
      ((D0 - D1).prod (D0 - D2)) t :=
    (hD0.sub hD1).prodMk (hD0.sub hD2)
  have hcompHD : HasFDerivAt (fun t' : EncParQ0 =>
      TParity.pUp
        ((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y)))
        ((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y))))
      (TParity.pUpCLM.comp ((D0 - D1).prod (D0 - D2))) t := by
    have h1 := TParity.pUpCLM.hasFDerivAt.comp t hpairHD
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => ?_))
    exact (TParity.pUpCLM_apply _ _).symm
  have hfinal : HasFDerivAt (fun t' => TParity.chartDiff3 p (encFamQ0 H A B c₀ t') y)
      (TParity.pUpCLM.comp ((D0 - D1).prod (D0 - D2))) t :=
    hcompHD.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => rfl))
  rw [hfinal.fderiv]
  exact hpUp_surj.comp hsurj

end Helpers

end

theorem surjective_paramDeriv_encFamQ0_caseII
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.projTimesLineCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.isManifold_projTimesLineCharted
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) →
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) A →
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) B →
    Work.Drive.FoldFlat A → Work.Drive.FoldFlat B →
    Work.Drive.FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y)) →
    Work.Drive.FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y)) →
    (∀ (s : ℝ), s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (0, y)) →
    (∀ (s : ℝ), 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (1, y)) →
    Work.Drive.PairReg A B →
    Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y)) A B →
    Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y)) A B →
    (p : Projectivization ℝ (Eucl 3) × ℝ) → (t : Work.Drive.EncParQ0) →
    (y : EuclideanSpace ℝ (Fin 9)) →
    (∀ k : Fin 3, Work.Drive.encFamQ0 H A B c₀ t k (Work.Drive.TParity.bPartC k y)
      ∈ (Work.Drive.chr p).source) →
    Work.Drive.TParity.chartDiff3 p (Work.Drive.encFamQ0 H A B c₀ t) y = 0 →
    Work.Drive.betaG ((Work.Drive.TParity.bPartC 0 y) 2) = 0 →
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p
        (Work.Drive.encFamQ0 H A B c₀ t') y) t) := by
  intro hHsm hAsm hBsm hfoldA hfoldB hfold0 hfold1 hH0 hH1 hpair hend0 hend1
  intro p t y9 hsrc hzero hbeta
  rcases (betaG_eq_zero_iff ((TParity.bPartC 0 y9) 2)).mp hbeta with hs | hs
  · exact caseII_body H A B c₀ hc₀0 hc₀1 hAsm hBsm hfoldA hfoldB hpair
      ((TParity.bPartC 0 y9) 2) (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y))
      (fun y => hH0 ((TParity.bPartC 0 y9) 2) hs y) (contMDiff_slice H 0 hHsm) hfold0 hend0
      p t y9 (pt2 ((TParity.bPartC 0 y9) 0) ((TParity.bPartC 0 y9) 1))
      (pt2 ((TParity.bPartC 1 y9) 0) ((TParity.bPartC 1 y9) 1))
      (pt2 ((TParity.bPartC 2 y9) 0) ((TParity.bPartC 2 y9) 1))
      ((TParity.bPartC 1 y9) 2) ((TParity.bPartC 2 y9) 2)
      rfl rfl rfl rfl rfl hsrc hzero hbeta rfl
  · exact caseII_body H A B c₀ hc₀0 hc₀1 hAsm hBsm hfoldA hfoldB hpair
      ((TParity.bPartC 0 y9) 2) (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y))
      (fun y => hH1 ((TParity.bPartC 0 y9) 2) hs y) (contMDiff_slice H 1 hHsm) hfold1 hend1
      p t y9 (pt2 ((TParity.bPartC 0 y9) 0) ((TParity.bPartC 0 y9) 1))
      (pt2 ((TParity.bPartC 1 y9) 0) ((TParity.bPartC 1 y9) 1))
      (pt2 ((TParity.bPartC 2 y9) 0) ((TParity.bPartC 2 y9) 1))
      ((TParity.bPartC 1 y9) 2) ((TParity.bPartC 2 y9) 2)
      rfl rfl rfl rfl rfl hsrc hzero hbeta rfl

end Work.Drive
