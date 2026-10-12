import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The localised windowed mode coefficient `∫_A χ(z)e^{−i⟪p,z⟫}dz`
(mirror of `SmallBoxPairMode.modeChat`). -/
noncomputable def modeChatLoc (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∫ z in A, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))

/-- The localised `Q_A`-projected windowed momentum mode
`1_A(y)·χ(y)e^{−i⟪p,y⟫} − (volA)⁻¹·(∫_A χ e^{−i⟪p,·⟫})·1_A(y)`
(mirror of `SmallBoxPairMode.qMode`, with the box indicator carried explicitly). -/
noncomputable def qModeLoc (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p y : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  A.indicator (fun z => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) y
    - ((volA)⁻¹ : ℂ) * modeChatLoc A χ p * (A.indicator (fun _ => (1 : ℝ)) y : ℂ)

/-- The localised creation-like mode operator (mirror of `SmallBoxPairIdent.bDag`):
`(volA)⁻¹ Σ_i g(x i) ∫_{z∈A} Ψ(x_{i←z})dz`.  The `(volA)⁻¹` is `volA^{−1/2}·volA^{−1/2}`, i.e.
FS's `b†_p = |B|^{−1/2}a†(Q_Bχ_Be^{−ipx})a_0` up to the `a_0` (which is supplied by the
`P`-projections inside `boxA2`). -/
noncomputable def bDagLoc (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ) {N : ℕ}
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : Submission.BoseGases.X N → ℂ) :
    Submission.BoseGases.X N → ℂ :=
  fun x => (volA)⁻¹ * ∑ i : Fin N, g (x i) * ∫ z in A, Ψ (Function.update x i z)

/-- The localised two-body kernel `χ(x)·𝒲(x−y)·χ(y)` (mirror of `KernelIds.wPair`). -/
noncomputable def wPairLoc (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ) (x y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  χ x * 𝒲 (x - y) * χ y

/-- The inner factor `𝒲` of the corpus's localised kernel `DLSmallKernels.wSmallPair`, i.e.
`wSmallPair M ℓ d u h x y = chiSmallB M ℓ d u x · wSmallInner M ℓ d h (x − y) · chiSmallB M ℓ d u y`. -/
noncomputable def wSmallInner (M : ℕ) (ℓ d : ℝ)
    (h : EuclideanSpace ℝ (Fin 3) → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => Submission.BoseGases.wSmallScaled M (ℓ * d) h z / Submission.BoseGases.convScale ℓ z

/-- The localised **p-space pairing form**: the right-hand side of FS's second quantization of
`A₂` at the sliding box, i.e. the mirror of the analysis-box integrand of
`SmallBoxPairAPairing.q4PairWord_eq_pPairing`.  With `b†_g = bDagLoc A volA g` and
`χ = chiSmallB M ℓ d u`, `𝒲 = wSmallInner M ℓ d (g0 v h)`:

    pairFormLoc ℓ A volA χ 𝒲 Φ = (2π)⁻³ ∫ 𝓕𝒲((2π)⁻¹•q) · ⟨Φ, b†_{−q} b†_{q} Φ⟩ dq .

The identity `boxA2 ℓ volA A (wSmall1Pair h M ℓ d u) Φ = pairFormLoc ℓ A volA χ 𝒲 Φ` is the
localised pairing identity (item 2 of `FINDING_localisedAppBogVolNeg_session1.md` §4). -/
noncomputable def pairFormLoc (ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (χ 𝒲 : EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) : ℂ :=
  (((2 * Real.pi) ^ 3)⁻¹ : ℂ) *
    ∫ q : EuclideanSpace ℝ (Fin 3), FourierTransform.fourier (fun x => (𝒲 x : ℂ))
        (((2 * Real.pi)⁻¹) • q) *
      (∫ x in Submission.BoseGases.abox N ℓ, (Φ x : ℂ) *
        bDagLoc A volA (qModeLoc A volA χ (-q))
          (bDagLoc A volA (qModeLoc A volA χ q) (fun y => (Φ y : ℂ))) x)

/-- The localised **annihilation-type mode operator**, i.e. the honest `L²(abox N ℓ)`-adjoint of
`tauDagLoc`: `(√volA)⁻¹ Σ_i 1_A(x i)·∫_{z∈A} g(z)Ψ(x_{i←z})dz`.

The box indicator `1_A(x i)` is **essential**: at the sliding box `A = dlBox ℓ d u ⊊ acube ℓ`,
the operator without it is *not* the adjoint of `tauDagLoc`, and the resulting "commutator"
inequality `∫(τ†)² − ∫τ² ≤ (∫_A g²)·(flat count)` is FALSE for `N ≥ 5` — see
`Submission/Work/BoseFixB1/FINDING_boxTau_commutator_le_sharp_FALSE.md` and
`_num/boxTau_commutator_counterexample.py` (the defect is the missing `1_A(x i)`).  With the
indicator the analysis-box statement (`SharpCommutator.tau_commutator_le_sharp`, PROVED, where
`A = acube s` makes the indicator invisible) mirrors correctly. -/
noncomputable def tauAnnLoc (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.X N → ℝ :=
  fun x => (Real.sqrt volA)⁻¹ * ∑ i : Fin N,
    (A.indicator (fun _ => (1 : ℝ)) (x i)) * ∫ z in A, g z * Ψ (Function.update x i z)

/-- The localised **creation-type mode operator** (mirror of `SmallBoxTauModes.tauDag`):
`(√volA)⁻¹ Σ_i g(x i) ∫_{z∈A} Ψ(x_{i←z})dz`. -/
noncomputable def tauDagLoc (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.X N → ℝ :=
  fun x => (Real.sqrt volA)⁻¹ * ∑ i : Fin N, g (x i) * ∫ z in A, Ψ (Function.update x i z)

/-! ## 2. §9.1 of the assembly plan: wiring `bDagLoc` to the `τ`-language

`localisedPairIdentity` (item 2) expresses `boxA2` through `bDagLoc`, while
`localisedTwoModeBogoliubov` (item 3b) consumes the `τ`-operators `tauAnnLoc`/`tauDagLoc`.  The
bridge is the *definitional* identity

    bDagLoc A volA (↑g) (↑Ψ) = (√volA)⁻¹ • (tauDagLoc A volA g Ψ)          (real data)

(the `(volA)⁻¹` of `bDagLoc` splits as `(√volA)⁻¹·(√volA)⁻¹`, `tauDagLoc` carrying one `(√volA)⁻¹`),
together with `ℂ`-linearity of `bDagLoc` in the mode and the `Re`/`Im` splitting which turns a
complex mode (`qModeLoc A volA χ q`, as in item 2) into the two *real* modes that 3b accepts. -/

/-- `bDagLoc` is additive in the mode. -/
lemma bDagLoc_add (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ) {N : ℕ}
    (g g' : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : Submission.BoseGases.X N → ℂ) :
    bDagLoc A volA (fun z => g z + g' z) Ψ = bDagLoc A volA g Ψ + bDagLoc A volA g' Ψ := by
  funext x
  simp only [bDagLoc, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

/-- `bDagLoc` is `ℂ`-homogeneous in the mode. -/
lemma bDagLoc_smul (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ) {N : ℕ} (c : ℂ)
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : Submission.BoseGases.X N → ℂ) :
    bDagLoc A volA (fun z => c * g z) Ψ = c • bDagLoc A volA g Ψ := by
  funext x
  simp only [bDagLoc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The `Re`/`Im` splitting of a complex mode** for `bDagLoc`. -/
lemma bDagLoc_re_add_im (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ) {N : ℕ}
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (Ψ : Submission.BoseGases.X N → ℂ) :
    bDagLoc A volA g Ψ
      = bDagLoc A volA (fun z => ((g z).re : ℂ)) Ψ
        + Complex.I • bDagLoc A volA (fun z => ((g z).im : ℂ)) Ψ := by
  have hmode : g = fun z => ((g z).re : ℂ) + Complex.I * ((g z).im : ℂ) := by
    funext z
    apply Complex.ext <;> simp
  conv_lhs => rw [hmode]
  rw [bDagLoc_add, bDagLoc_smul]

/-- **§9.1: `bDagLoc` on real data is `(√volA)⁻¹` times `tauDagLoc`.**  For a real mode `g` and a
real state `Ψ` (both viewed in `ℂ`),

    bDagLoc A volA (↑g) (↑Ψ) = (√volA)⁻¹ • (tauDagLoc A volA g Ψ) .

This is the bridge that carries item 2's integrand (`bDagLoc`-form) into the `τ`-language of item 3b.
The hypothesis is the `IntegrableOn` of the slot fibres, needed to commute `ℂ`-inclusion with the
Bochner integral (in the application it comes from continuity of `Ψ` and the compactness of `A`). -/
lemma bDagLoc_ofReal {volA : ℝ} (hvolA : 0 ≤ volA) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {N : ℕ} (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : Submission.BoseGases.X N → ℝ)
    (hint : ∀ (x : Submission.BoseGases.X N) (i : Fin N),
      IntegrableOn (fun z => Ψ (Function.update x i z)) A) :
    bDagLoc A volA (fun z => (g z : ℂ)) (fun x => (Ψ x : ℂ))
      = fun x => ((Real.sqrt volA)⁻¹ : ℂ) * ((tauDagLoc A volA g Ψ x : ℝ) : ℂ) := by
  have hterm : ∀ (x : Submission.BoseGases.X N) (i : Fin N),
      (g (x i) : ℂ) * ∫ z in A, ((Ψ (Function.update x i z) : ℝ) : ℂ)
        = ((g (x i) * ∫ z in A, Ψ (Function.update x i z) : ℝ) : ℂ) := by
    intro x i
    rw [Complex.ofReal_mul]
    congr 1
    exact ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM (hint x i)
  have hsq : ((Real.sqrt volA : ℂ))⁻¹ * ((Real.sqrt volA : ℂ))⁻¹ = ((volA : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hvolA]
  funext x
  have hsum : (∑ i : Fin N, (g (x i) : ℂ) * ∫ z in A, ((Ψ (Function.update x i z) : ℝ) : ℂ))
      = ((∑ i : Fin N, g (x i) * ∫ z in A, Ψ (Function.update x i z) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => hterm x i
  simp only [bDagLoc, tauDagLoc, hsum, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [← mul_assoc, hsq]

end Work.BoseFixB1B
