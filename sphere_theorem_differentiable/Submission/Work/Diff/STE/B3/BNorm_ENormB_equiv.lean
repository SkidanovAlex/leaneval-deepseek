/-
# Layer D2: the equivalence of the composite norm `BNorm` with the physical `Hᵏ` energy

The energy estimate of Layer D is run on the **integral side**

  `ENormB k h := Σ_{i a b} ENormSq k (D.Rper i h a b)`

(because `Work.Diff.STE.garding_vec_uniform` is stated with `ENormSq`/`L2re`), while the pointwise
control `Work.Diff.STE.B3Data.pointwise_bound`, the mollifier bounds (`BNorm_J_le`,
`BNorm_J_sub_le`) and the compactness/limit step are stated with the **Fourier side**
`D.BNorm k`.  This file records the two-sided equivalence (constants depending only on `D`, `k`):

* `BNorm_le_ENormB`: `D.BNorm k h ≤ C (ENormB k h + ENormB 0 h)`, from the proved
  `Work.Diff.STE.CSq_le_ENormSq` (per component) — note the extra `ENormB 0`.
* `ENormB_le_BNorm`: `ENormB k h ≤ C * D.BNorm k h`, from
  `Work.Diff.STE.B3Data.ENormSq_le_CSq` (the Parseval direction, filed and proved this session).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3Data

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The physical (integral-side) energy of a section**: the sum of the `Hᵏ` norms `ENormSq k` of
the periodised components.  This is the norm on which `garding_vec_uniform` acts. -/
def ENormB (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) : ℝ :=
  ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    Work.Diff.STE.ENormSq k (D.Rper i h a b)

/-- **The physical energy pairing**: the companion bilinear form of `ENormB` (the real `Hᵏ`
inner product of the periodised components).  `ENormB_pair k h h = ENormB k h`. -/
def ENormB_pair (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h h' : Bil (I := I) (M := M)) : ℝ :=
  ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ∑ l : Fin k → Fin (Module.finrank ℝ E),
      Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (D.Rper i h a b))
        (Work.Diff.STE.pdVec k l (D.Rper i h' a b))

/-- The physical energy is nonnegative. -/
lemma ENormB_nonneg (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M))
    (hint : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      0 ≤ Work.Diff.STE.ENormSq k (D.Rper i h a b)) :
    0 ≤ D.ENormB k h :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hint i a b

/-- **The Fourier-side norm is controlled by the physical energy** (with an extra `ENormSq 0`
term, which is harmless: it is the `L²` norm of the section itself). -/
theorem BNorm_le_ENormB (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ k (D.Rper i h a b))
    (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i h a b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      D.BNorm k h ≤ C * (D.ENormB k h + D.ENormB 0 h) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, ?_⟩
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
        ≤ C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
    intro i a b
    exact hCb (D.Rper i h a b) (hsm i a b) (hper i a b)
  have hsum : D.BNorm k h ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm i a b
  have hsplit : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)))
      = C * (D.ENormB k h + D.ENormB 0 h) := by
    simp only [ENormB, Finset.sum_add_distrib, ← Finset.mul_sum]
  rwa [hsplit] at hsum

/-- **The physical energy is controlled by the Fourier-side norm.** -/
theorem ENormB_le_BNorm (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M))
    (hsmooth : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ D.ENormB k h ≤ C * D.BNorm k h := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.ENormSq_le_CSq (I := I) (M := M) D k h hsmooth
  refine ⟨C, hC, ?_⟩
  have hsum : D.ENormB k h ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum fun b _ => hCb i a b
  have hsplit : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)))
      = C * D.BNorm k h := by
    simp only [BNorm, ← Finset.mul_sum]
  rwa [hsplit] at hsum

end

end Work.Diff.STE.B3Data
