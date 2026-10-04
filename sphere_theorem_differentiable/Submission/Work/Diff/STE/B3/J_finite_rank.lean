import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.JPrelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the Friedrichs mollifier `J ρ ε` has finite rank

`Work.Diff.STE.B3Data.J ρ ε` is the Friedrichs mollifier

  `J ρ ε h = Σ_i R_i*(S_ε (R_i h))`,   where `S_ε = STruncR ρ ε`

has Fourier coefficients `ρ (ε • m) · ĉ(m)`.  If `ρ` vanishes outside the ball
`{y | 2 < Σ_i (y i)^2}` in frequency space (the hypothesis `hρ0` of the target theorem), then `S_ε`
keeps only the *finitely many* frequencies `m` with `Σ_i (ε m_i)^2 ≤ 2` — the box `truncBox ε` of
`JPrelim.lean`.  Consequently the image of `J ρ ε` lies in the span of the fixed finite family

  `jVec D ε i a b q (p) =
      (ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹ · modeFun q (coord i p)) • Φ i a b (p)`

indexed by a chart `i`, the two frame indices `a b`, and the mode `q` (an integer frequency in the
box together with the choice of real or imaginary part of the character `e^{2πi m·z}`); here
`Φ i a b = e_i^a ♭ ⊗ e_i^b ♭` is the elementary form of the `g₀`-orthonormal frame `e i` of chart
`i`.

Main results of this file:

* `smulRight_finset_sum`, `mul_sum_smul_eq` — the two elementary linear-algebra lemmas;
* `STruncR_eq_fintype_sum` — `STruncR ρ ε f` is the finite sum `Σ_q scoeff ρ ε f q · modeFun q`;
* `Rstar_expand` — `Rstar i u = Σ_{ab} (wgt i · (u a b) ∘ coord i) • Φ i a b`;
* `jVec` — the spanning vectors of the finite family;
* `J_eq_sum`, `J_eq_sum_index` — the expansion of `J ρ ε h` in the fixed family;
* `J_finite_rank` — the finite-rank statement.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

/-! ## 1. Two elementary linear-algebra lemmas -/

/-- `ContinuousLinearMap.smulRight` distributes over a finite sum in its vector argument. -/
lemma smulRight_finset_sum {ι : Type*} {M₁ M₂ : Type*} [NormedAddCommGroup M₁]
    [NormedSpace ℝ M₁] [NormedAddCommGroup M₂] [NormedSpace ℝ M₂]
    (c : M₁ →L[ℝ] ℝ) (f : ι → M₂) (a : ι → ℝ) (s : Finset ι) :
    c.smulRight (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • c.smulRight (f i) := by
  ext x
  simp only [ContinuousLinearMap.smulRight_apply, sum_apply, smul_apply]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (c x) (a i) (f i)

/-- Pulling a finite linear combination out of the scalar factor of a `smul`. -/
lemma mul_sum_smul_eq {ι V : Type*} [AddCommMonoid V] [Module ℝ V]
    (K : ℝ) (s : Finset ι) (C m : ι → ℝ) (Φ : V) :
    (K * ∑ q ∈ s, C q * m q) • Φ = ∑ q ∈ s, C q • ((K * m q) • Φ) := by
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [smul_smul]
  congr 1
  ring

/-! ## 2. The finite mode index and the mode functions -/

/-- The finite index set of Fourier modes that survive the truncation `trunc ρ ε`: the integer
frequencies in the box `truncBox ε`, each together with the choice of the real (`false`) or the
imaginary (`true`) part of the character. -/
abbrev QIdx (n : ℕ) (ε : ℝ) : Type :=
  {m : Fin n → ℤ // m ∈ truncBox (n := n) ε} × Bool

/-- The real Fourier mode selected by `q = (m, σ)`: `σ = true` is the imaginary part of the
character `e^{2πi m·z}`, `σ = false` its real part. -/
def modeFun (n : ℕ) {ε : ℝ} (q : QIdx n ε) (z : Fin n → ℝ) : ℝ :=
  cond q.2 (fourierExp q.1.1 z).im (fourierExp q.1.1 z).re

/-- The Fourier coefficients of the periodisation `Σ_k f (· + k)` of `f`; for `n = finrank ℝ E`
this is `Work.Diff.STE.B3.perCoeff`. -/
def perCoeffN (n : ℕ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℤ) → ℂ :=
  Work.Diff.STE.fourierCoeff fun y =>
    ∑' k : Fin n → ℤ, ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)

/-- The coefficient of the mode `q` in the truncation of `f`: the real (resp. the negative of the
imaginary) part of `trunc ρ ε (perCoeffN n f) m` for `σ = false` (resp. `σ = true`). -/
def scoeff (n : ℕ) (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ)
    (q : QIdx n ε) : ℝ :=
  cond q.2 (-(Work.Diff.STE.trunc ρ ε (perCoeffN n f) q.1.1).im)
    (Work.Diff.STE.trunc ρ ε (perCoeffN n f) q.1.1).re

/-- **`STruncR` as a finite sum over the mode index `QIdx ε`.**  This is the finite-support form of
the truncation: the hypothesis `hρ0` on `ρ` cuts the Fourier series down to the box
`truncBox ε`. -/
theorem STruncR_eq_fintype_sum
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.STE.B3Data.STruncR ρ ε f z
      = ∑ q : QIdx (Module.finrank ℝ E) ε,
          scoeff (Module.finrank ℝ E) ρ ε f q * modeFun (Module.finrank ℝ E) q z := by
  rw [STruncR_eq_sum ρ ε hε hρ0 f z]
  rw [Finset.sum_subtype (s := truncBox (n := Module.finrank ℝ E) ε)
    (p := fun m => m ∈ truncBox (n := Module.finrank ℝ E) ε) (fun _ => Iff.rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Fintype.sum_bool, Complex.mul_re]
  simp only [scoeff, modeFun, perCoeffN, perCoeff, Bool.cond_true, Bool.cond_false]
  ring

/-! ## 3. The elementary forms of the frame and the expansion of `Rstar` -/

/-- The scalar factor of the reconstruction `Rstar i`,
`ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹`. -/
def jWgt (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (p : M) : ℝ :=
  D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
    * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹

/-- The elementary bilinear form `e_i^a ♭ ⊗ e_i^b ♭` of the `g₀`-orthonormal frame of chart `i`. -/
def jForm (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) : Bil (I := I) (M := M) :=
  fun p => (g₀.inner p (D.e i a p)).smulRight (g₀.inner p (D.e i b p))

/-- **The expansion of `Rstar`.**  The reconstruction is a sum of the elementary forms weighted by
the scalar function `jWgt i · (u a b) ∘ coord i`; in particular it is linear in the component
function `u`, which is what the finite-rank argument uses. -/
lemma Rstar_expand (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    D.Rstar i u = ∑ a, ∑ b, (fun p =>
      (jWgt D i p * u a b (coord (I := I) (D.x₀ i) p)) • (jForm D i a b p)) := by
  funext p
  simp only [B3Data.Rstar, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ext x
  simp only [ContinuousLinearMap.smulRight_apply, sum_apply, smul_apply, jForm, jWgt]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [smul_comm]

/-- **The spanning vectors of the finite family.**  The chart-`i` component of the mode `q` of the
section, carried back to a section by the elementary form `e_i^a ♭ ⊗ e_i^b ♭`. -/
def jVec (D : B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (q : QIdx (Module.finrank ℝ E) ε) :
    Bil (I := I) (M := M) :=
  fun p => (jWgt D i p * modeFun (Module.finrank ℝ E) q (coord (I := I) (D.x₀ i) p))
    • (jForm D i a b p)

/-- **The product index of the spanning family.** -/
abbrev JIdx (ι₀ : Type*) [Fintype ι₀] (n : ℕ) (ε : ℝ) :=
  ι₀ × (Fin n × (Fin n × QIdx n ε))

/-- **The spanning family of `J ρ ε`**, indexed by the product of the chart index, the two frame
indices and the mode index. -/
def jFamily (D : B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) :
    JIdx ι₀ (Module.finrank ℝ E) ε → Bil (I := I) (M := M) :=
  fun z => jVec D ε z.1 z.2.1 z.2.2.1 z.2.2.2

/-- The coefficients of the expansion of `J ρ ε h` in the family `jFamily D ε`. -/
def jFamilyCoeff (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (h : Bil (I := I) (M := M)) : JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => scoeff (Module.finrank ℝ E) ρ ε (D.R z.1 h z.2.1 z.2.2.1) z.2.2.2

/-! ## 4. The expansion of `J ρ ε h` -/

/-- **The expansion of the mollifier.**  For every section `h`, `J ρ ε h` is a finite real linear
combination of the *fixed* family `jVec D ε i a b q`, the coefficients being the (finitely many)
Fourier coefficients of the chart components of `h`. -/
lemma J_eq_sum (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Bil (I := I) (M := M)) :
    D.J ρ ε h = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E), ∑ q : QIdx (Module.finrank ℝ E) ε,
        scoeff (Module.finrank ℝ E) ρ ε (D.R i h a b) q • jVec D ε i a b q := by
  have h1 : D.J ρ ε h
      = ∑ i : ι₀, D.Rstar i (fun a b z => B3Data.STruncR ρ ε (D.R i h a b) z) := rfl
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Rstar_expand D i (fun a b z => B3Data.STruncR ρ ε (D.R i h a b) z)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  funext p
  rw [STruncR_eq_fintype_sum ρ ε hε hρ0 (D.R i h a b) (coord (I := I) (D.x₀ i) p)]
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact mul_sum_smul_eq (jWgt D i p) Finset.univ
    (scoeff (Module.finrank ℝ E) ρ ε (D.R i h a b))
    (fun q => modeFun (Module.finrank ℝ E) q (coord (I := I) (D.x₀ i) p))
    (jForm D i a b p)

/-- **The expansion of `J ρ ε h` in the product-indexed family.** -/
lemma J_eq_sum_index (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Bil (I := I) (M := M)) :
    D.J ρ ε h
      = ∑ z : JIdx ι₀ (Module.finrank ℝ E) ε, jFamilyCoeff D ρ ε h z • jFamily D ε z := by
  rw [J_eq_sum D ρ ε hε hρ0 h]
  simp only [Fintype.sum_prod_type, jFamily, jFamilyCoeff]

end

theorem J_finite_rank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → Work.Diff.STE.Bil (I := I) (M := M)),
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        ∃ c : Fin N → ℝ, D.J ρ ε h = ∑ i, c i • v i := by
  classical
  refine ⟨Fintype.card (JIdx ι₀ (Module.finrank ℝ E) ε),
    fun k => jFamily D ε ((Fintype.equivFin (JIdx ι₀ (Module.finrank ℝ E) ε)).symm k),
    fun h => ⟨fun k => jFamilyCoeff D ρ ε h
      ((Fintype.equivFin (JIdx ι₀ (Module.finrank ℝ E) ε)).symm k), ?_⟩⟩
  rw [J_eq_sum_index D ρ ε hε hρ0 h]
  exact (Equiv.sum_comp (Fintype.equivFin (JIdx ι₀ (Module.finrank ℝ E) ε)).symm
    (fun z : JIdx ι₀ (Module.finrank ℝ E) ε =>
      jFamilyCoeff D ρ ε h z • jFamily D ε z)).symm

end Work.Diff.STE.B3
