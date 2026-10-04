import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.GExpSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Real-analysis core of `cap_avoid`.**  Let `F : ℝ → ℝ` be continuous, `0 < c`, `0 ≤ ε`,
`ε·π < c`, `0 ≤ s ≤ π`.  Assume

* `F 0 ≥ -1 + 3c`;
* `g ≥ -1 + 3c` on `[0,s]`;
* on every prefix `[0,t]` (`t ∈ [0,s]`) on which `F > -1 + c`, we have `g t - ε·t ≤ F t`.

Then `F > -1 + 2c` on `[0,s]`.

The proof is the "first bad point" argument: the bad set `Z = {t ∈ [0,s] : F t ≤ -1+2c}` is closed
and does not contain `0`; if non-empty, let `t₀ = sInf Z`.  Points below `t₀` are not bad, so
`F > -1+2c` there and, by continuity, `F t₀ ≥ -1+2c`, whence `F > -1+c` on all of `[0,t₀]` and the
comparison hypothesis applies at `t₀`, giving `F t₀ ≥ -1+3c - ε t₀ > -1+2c` — contradiction. -/
lemma cap_avoid_aux {F g : ℝ → ℝ} (hFcont : Continuous F)
    {c ε s : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (hεπ : ε * Real.pi < c)
    (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi)
    (hF0 : -1 + 3 * c ≤ F 0)
    (htrig : ∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ g σ)
    (hcmp : ∀ t ∈ Set.Icc (0 : ℝ) s,
      (∀ σ ∈ Set.Icc (0 : ℝ) t, -1 + c < F σ) → g t - ε * t ≤ F t) :
    ∀ t ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c < F t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨tbad, htbad⟩ := hcon
  set Z : Set ℝ := Set.Icc (0 : ℝ) s ∩ {t : ℝ | F t ≤ -1 + 2 * c} with hZ
  have hZmem : ∀ t : ℝ, t ∈ Z ↔ t ∈ Set.Icc (0 : ℝ) s ∧ F t ≤ -1 + 2 * c := by
    intro t
    rw [hZ]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hZne : Z.Nonempty := ⟨tbad, (hZmem tbad).mpr htbad⟩
  have hZcl : IsClosed Z := by
    rw [hZ]
    exact isClosed_Icc.inter (isClosed_le hFcont continuous_const)
  have hZbdd : BddBelow Z := ⟨0, fun t ht => ((hZmem t).mp ht).1.1⟩
  have ht₀Z : sInf Z ∈ Z := hZcl.csInf_mem hZne hZbdd
  have ht₀Icc : sInf Z ∈ Set.Icc (0 : ℝ) s := ((hZmem _).mp ht₀Z).1
  have ht₀le : F (sInf Z) ≤ -1 + 2 * c := ((hZmem _).mp ht₀Z).2
  have ht₀pos : 0 < sInf Z := by
    rcases lt_or_eq_of_le ht₀Icc.1 with h | h
    · exact h
    · exfalso
      have h0 : F 0 ≤ -1 + 2 * c := by rw [h]; exact ht₀le
      linarith
  -- every point of `[0, sInf Z)` is good
  have hsub : Set.Ico (0 : ℝ) (sInf Z) ⊆ {σ : ℝ | -1 + 2 * c < F σ} := by
    intro σ hσ
    obtain ⟨hσ0, hσlt⟩ := Set.mem_Ico.mp hσ
    have hσIcc : σ ∈ Set.Icc (0 : ℝ) s := ⟨hσ0, hσlt.le.trans ht₀Icc.2⟩
    by_contra hle
    have hmem : σ ∈ Z := (hZmem σ).mpr ⟨hσIcc, not_lt.mp hle⟩
    exact absurd hσlt (not_lt.mpr (csInf_le hZbdd hmem))
  -- hence `F (sInf Z) ≥ -1 + 2c` by continuity
  have ht₀ge : -1 + 2 * c ≤ F (sInf Z) := by
    have ht₀cl : sInf Z ∈ closure (Set.Ico (0 : ℝ) (sInf Z)) := by
      rw [closure_Ico (ne_of_lt ht₀pos)]
      exact ⟨le_of_lt ht₀pos, le_refl _⟩
    exact closure_minimal (fun x hx => le_of_lt hx) (isClosed_le continuous_const hFcont)
      (closure_mono hsub ht₀cl)
  have hreg : ∀ σ ∈ Set.Icc (0 : ℝ) (sInf Z), -1 + c < F σ := by
    intro σ hσ
    rcases lt_or_eq_of_le hσ.2 with hlt | heq
    · have h2 : -1 + 2 * c < F σ := hsub (Set.mem_Ico.mpr ⟨hσ.1, hlt⟩)
      linarith
    · rw [heq]; linarith
  have hcmp₀ := hcmp (sInf Z) ht₀Icc hreg
  have htrig₀ := htrig (sInf Z) ht₀Icc
  have heps : ε * sInf Z ≤ ε * Real.pi :=
    mul_le_mul_of_nonneg_left (ht₀Icc.2.trans hsπ) hε
  linarith

theorem cap_avoid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {q : M} {f : M → ℝ} {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (hεπ : ε * Real.pi < c)
    (hcont : Continuous f)
    {u : TangentSpace I q} {s : ℝ} (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi)
    (htrig : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + 3 * c ≤ f q * Real.cos σ + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin σ)
    (hcmp : ∀ t ∈ Set.Icc (0 : ℝ) s,
      (∀ σ ∈ Set.Icc (0 : ℝ) t, -1 + c < f (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u))) →
      f q * Real.cos t + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin t - ε * t
        ≤ f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) :
    ∀ t ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c < f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) := by
  -- the exponential ray is continuous in the parameter
  have hGcont : Continuous (fun w : TangentSpace I q =>
      Submission.GlobalExp.GExp (cov := cov) hmet q w) :=
    continuous_iff_continuousAt.mpr (fun v =>
      (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet q v).continuousAt)
  have hray : Continuous (fun t : ℝ =>
      Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) :=
    hGcont.comp (continuous_id.smul continuous_const)
  have hFcont : Continuous (fun t : ℝ =>
      f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))) := hcont.comp hray
  -- `F 0 = f q ≥ -1 + 3c` from the trigonometric hypothesis at `σ = 0`
  have hF0 : -1 + 3 * c ≤ f (Submission.GlobalExp.GExp (cov := cov) hmet q ((0 : ℝ) • u)) := by
    have h := htrig 0 ⟨le_refl 0, hs0⟩
    simpa using h
  exact cap_avoid_aux hFcont hc hε hεπ hs0 hsπ hF0 htrig hcmp

end Work.Diff.C
