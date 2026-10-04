import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

/-! ## A tool: pointwise convergence of linear functionals on a finite-dimensional space

Every linear functional on a finite-dimensional normed space over `ℝ` is continuous, and a family
of linear functionals converging pointwise to zero converges uniformly on bounded sets.  This is the
form in which the "moving slot" of the product rule below is handled: the family of functionals is
the difference `rmP4B (G s) x (update p j ·) - rmP4B (G t) x (update p j ·)`, which converges to
zero pointwise, and it is evaluated on the slope `(s - t)⁻¹ • (w s - w t)`, which is bounded. -/
theorem tendsto_apply_zero_of_tendsto_pointwise_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter ℝ} {ψ : ℝ → V →ₗ[ℝ] ℝ}
    (hψ : ∀ u : V, Filter.Tendsto (fun s => ψ s u) l (nhds 0))
    {v : ℝ → V} (hv : ∃ B : ℝ, ∀ᶠ s in l, ‖v s‖ ≤ B) :
    Filter.Tendsto (fun s => ψ s (v s)) l (nhds 0) := by
  classical
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℝ V) :=
    ⟨_, ⟨Module.finBasis ℝ V⟩⟩
  obtain ⟨B, hB⟩ := hv
  -- the coordinate functionals of the basis, as continuous linear maps
  let c : Fin n → (V →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hc : ∀ (i : Fin n) (u : V), c i u = b.repr u i := by
    intro i u
    simp [c]
  have hcoord : ∀ (i : Fin n) (u : V), |b.repr u i| ≤ ‖c i‖ * ‖u‖ := by
    intro i u
    rw [← hc i u]
    simpa [Real.norm_eq_abs] using (c i).le_opNorm u
  -- the "operator norm" of `ψ s` on the unit ball, as a function of `s`, tends to `0`
  have hM : Filter.Tendsto (fun s => ∑ i : Fin n, ‖c i‖ * |ψ s (b i)|) l (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ i : Fin n, ‖c i‖ * |(0 : ℝ)| := by simp
    rw [h0]
    refine tendsto_finset_sum _ (fun i _ => ?_)
    simpa using ((hψ (b i)).abs).const_mul (‖c i‖)
  have hkey : ∀ᶠ s in l, ‖ψ s (v s)‖ ≤ B * (∑ i : Fin n, ‖c i‖ * |ψ s (b i)|) := by
    filter_upwards [hB] with s hs
    have hexp : ψ s (v s) = ∑ i : Fin n, b.repr (v s) i * ψ s (b i) := by
      conv_lhs => rw [← b.sum_repr (v s)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [hexp, Real.norm_eq_abs]
    calc |∑ i : Fin n, b.repr (v s) i * ψ s (b i)|
        ≤ ∑ i : Fin n, |b.repr (v s) i * ψ s (b i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |b.repr (v s) i| * |ψ s (b i)| := by
            exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i : Fin n, (‖c i‖ * ‖v s‖) * |ψ s (b i)| :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcoord i (v s)) (abs_nonneg _)
      _ = ‖v s‖ * (∑ i : Fin n, ‖c i‖ * |ψ s (b i)|) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ B * (∑ i : Fin n, ‖c i‖ * |ψ s (b i)|) :=
            mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg fun i _ => by positivity)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) hkey
      (by simpa using hM.const_mul B))

/-! ## Additivity and homogeneity of `rmP4B` in one slot -/

/-- `rmP4B` is additive in the slot `j` (the other slots being frozen at `p`). -/
theorem rmP4B_update_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (p : Fin 4 → TangentSpace I x) (j : Fin 4) (u v : TangentSpace I x) :
    rmP4B g x (Function.update p j (u + v))
      = rmP4B g x (Function.update p j u) + rmP4B g x (Function.update p j v) := by
  fin_cases j <;>
    simp only [rmP4B, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      Fin.mk_one, Fin.reduceFinMk, rmP_add_fst g hLC, rmP_add_snd g hLC, rmP_add_thd g hLC,
      rmP_add_fth g hLC]

/-- `rmP4B` is homogeneous in the slot `j` (the other slots being frozen at `p`). -/
theorem rmP4B_update_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (p : Fin 4 → TangentSpace I x) (j : Fin 4) (c : ℝ) (u : TangentSpace I x) :
    rmP4B g x (Function.update p j (c • u)) = c * rmP4B g x (Function.update p j u) := by
  fin_cases j <;>
    simp only [rmP4B, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      Fin.mk_one, Fin.reduceFinMk, rmP_smul_fst g hLC, rmP_smul_snd g hLC, rmP_smul_thd g hLC,
      rmP_smul_fth g hLC]

/-- **The moving-slot product rule for the curvature.**  If `s ↦ w s` is a curve in `TₓM` with
`HasDerivAt w w' t` and `t` is an interior time of a Ricci flow `G` on `[0,T)`, then the
`s`-derivative of the component `s ↦ rmP (G s) x (… w s …)` of the curvature — with `w s` inserted
in the slot `j` of the tuple `p : Fin 4 → TₓM` — is the value of Hamilton's evolution equation
`∂ₜRm = ΔRm + reactionMap(Rm)` on the *frozen* tuple, plus the "frozen slot" term coming from the
derivative `w'`.

`Work.Diff.GE.EvolB.rmP4B`, `lapRm4`, `react4` are the `4`-tuple versions of `rmP`, `lapRmAt` and
`reactionFormAt` (defined in `Submission/Work/Diff/GE/EvolB/Defs.lean`).

Route.  Subtract and add the frozen value:
`rmP4B (G s) x (update p j (w s)) - rmP4B (G t) x (update p j (w s)) + rmP4B (G t) x (update p j (w s))`.

* The second term is linear in `w s` (linearity of `rmP` in each slot:
  `Work.Diff.GE.rmP_add_fst` and its three siblings in `Submission/Work/Diff/GE/NablaRm.lean`, or
  `Work.Diff.GE.rmP4_update_add` / `rmP4_update_smul` in
  `Submission/Work/Diff/GE/covRmFixedEvolDefs.lean`), so its derivative is
  `rmP4B (G t) x (update p j w')` (a linear functional composed with `w`).
* For the first term, one uses the same device as in
  `Submission/Work/Diff/GE/MovingFrame/FrameRule.lean` (`frame_of_fixed`, steps 3–6): for fixed `u`
  the slope `(s-t)⁻¹ * (rmP4B (G s) x (update p j u) - rmP4B (G t) x (update p j u))` converges, as
  `s → t`, to `lapRm4 (G t) x (update p j u) + react4 reactionMap (G t) x (update p j u)` — that is
  `Work.Diff.GE.EvolA.rmP_evol_fixed` (PROVED) at the fixed tuple `update p j u` rewritten with
  `hasDerivAt_iff_tendsto_slope` — and it is *linear* in `u` for every `s`, so with
  `w s → w t` (`hw.continuousAt`) the multilinear-apply limit
  `Work.Diff.GE.MovingFrame.tendsto_multilinear_apply` (PROVED) gives convergence at `u = w s`.
  Adding the two derivatives gives the claim. -/
theorem rmP4_update_hasDerivAt_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : M)
    (p : Fin 4 → TangentSpace I x) (j : Fin 4)
    (w : ℝ → TangentSpace I x) (w' : TangentSpace I x)
    (hw : HasDerivAt w w' t) :
    HasDerivAt
      (fun s ↦ Work.Diff.GE.EvolB.rmP4B (G s) x (Function.update p j (w s)))
      (Work.Diff.GE.EvolB.lapRm4 (G t) x (Function.update p j (w t))
        + Work.Diff.GE.EvolB.react4 Work.Diff.GE.reactionMap (G t) x (Function.update p j (w t))
        + Work.Diff.GE.EvolB.rmP4B (G t) x (Function.update p j w')) t := by
  -- the model-space structure on the tangent space (`TangentSpace I x` is a type synonym for `E`,
  -- which type class inference does not unfold).  The `AddTorsor` instance is pinned first: once the
  -- normed-group structure is available, type class inference would find the `NormedAddTorsor`
  -- instance for `TangentSpace I x` over itself, which is *not* definitionally the canonical
  -- `AddGroup`-torsor and would break the rewriting of `slope`.
  letI hAT : AddTorsor (TangentSpace I x) (TangentSpace I x) := inferInstance
  letI hNAG : NormedAddCommGroup (TangentSpace I x) :=
    (inferInstanceAs (NormedAddCommGroup E) : NormedAddCommGroup E)
  letI hNS : NormedSpace ℝ (TangentSpace I x) :=
    (inferInstanceAs (NormedSpace ℝ E) : NormedSpace ℝ E)
  letI hFD : FiniteDimensional ℝ (TangentSpace I x) :=
    (inferInstanceAs (FiniteDimensional ℝ E) : FiniteDimensional ℝ E)
  have hadd : ∀ (g : SMet I M) (u v : TangentSpace I x),
      rmP4B g x (Function.update p j (u + v))
        = rmP4B g x (Function.update p j u) + rmP4B g x (Function.update p j v) :=
    fun g u v => rmP4B_update_add hLC g x p j u v
  have hsmul : ∀ (g : SMet I M) (c : ℝ) (u : TangentSpace I x),
      rmP4B g x (Function.update p j (c • u)) = c * rmP4B g x (Function.update p j u) :=
    fun g c u => rmP4B_update_smul hLC g x p j c u
  -- the linear functional `u ↦ rmP4B g x (update p j u)`
  let Φ : SMet I M → (TangentSpace I x) →ₗ[ℝ] ℝ := fun g =>
    { toFun := fun u => rmP4B g x (Function.update p j u)
      map_add' := fun u v => hadd g u v
      map_smul' := fun c u => by rw [hsmul g c u, smul_eq_mul, RingHom.id_apply] }
  have hΦ : ∀ (g : SMet I M) (u : TangentSpace I x),
      Φ g u = rmP4B g x (Function.update p j u) := fun g u => rfl
  -- the fixed-tuple evolution identity
  have hderiv : ∀ u : TangentSpace I x,
      HasDerivAt (fun s => Φ (G s) u)
        (lapRm4 (G t) x (Function.update p j u)
          + react4 Work.Diff.GE.reactionMap (G t) x (Function.update p j u)) t := by
    intro u
    have h := Work.Diff.GE.EvolA.rmP_evol_fixed hLC hLV G T hflow t ht x
      ((Function.update p j u) 0) ((Function.update p j u) 1) ((Function.update p j u) 2)
      ((Function.update p j u) 3)
    simpa only [hΦ, rmP4B, lapRm4, react4] using h
  -- the pointwise convergence of the difference of the two functionals
  have hψ : ∀ u : TangentSpace I x,
      Tendsto (fun s => (Φ (G s) - Φ (G t)) u) (𝓝[≠] t) (𝓝 0) := by
    intro u
    have hc : Tendsto (fun s => Φ (G s) u) (𝓝 t) (𝓝 (Φ (G t) u)) := (hderiv u).continuousAt
    have hc' : Tendsto (fun s => Φ (G s) u) (𝓝[≠] t) (𝓝 (Φ (G t) u)) :=
      hc.mono_left nhdsWithin_le_nhds
    have hsub : Tendsto (fun s => Φ (G s) u - Φ (G t) u) (𝓝[≠] t)
        (𝓝 (Φ (G t) u - Φ (G t) u)) := hc'.sub tendsto_const_nhds
    simpa only [LinearMap.sub_apply, sub_self] using hsub
  -- the slope of `w` at `t` is bounded near `t` (it converges to `w'`)
  have hvT : Tendsto (slope w t) (𝓝[≠] t) (𝓝 w') := (hasDerivAt_iff_tendsto_slope).mp hw
  have hbdd : ∃ B : ℝ, ∀ᶠ s in 𝓝[≠] t, ‖slope w t s‖ ≤ B := by
    refine ⟨‖w'‖ + 1, ?_⟩
    filter_upwards [Metric.tendsto_nhds.1 hvT.norm 1 one_pos] with s hs
    have hs' : |‖slope w t s‖ - ‖w'‖| < 1 := by simpa [Real.dist_eq] using hs
    linarith [(abs_lt.1 hs').2]
  -- the three limits
  have h1 : Tendsto (slope (fun σ => Φ (G σ) (w t)) t) (𝓝[≠] t)
      (𝓝 (lapRm4 (G t) x (Function.update p j (w t))
        + react4 Work.Diff.GE.reactionMap (G t) x (Function.update p j (w t)))) :=
    (hasDerivAt_iff_tendsto_slope).mp (hderiv (w t))
  have h2 : Tendsto (fun s => (Φ (G s) - Φ (G t)) (slope w t s)) (𝓝[≠] t) (𝓝 0) :=
    @tendsto_apply_zero_of_tendsto_pointwise_zero (TangentSpace I x) hNAG hNS hFD (𝓝[≠] t)
      (fun s => Φ (G s) - Φ (G t)) hψ (fun s => slope w t s) hbdd
  have h3 : Tendsto (fun s => Φ (G t) (slope w t s)) (𝓝[≠] t) (𝓝 (Φ (G t) w')) :=
    ((LinearMap.continuous_of_finiteDimensional (Φ (G t))).tendsto w').comp hvT
  -- the algebraic decomposition of the slope
  have hdecomp : ∀ s : ℝ,
      (slope (fun σ => Φ (G σ) (w t)) t s + (Φ (G s) - Φ (G t)) (slope w t s))
          + Φ (G t) (slope w t s)
        = (s - t)⁻¹ * (Φ (G s) (w s) - Φ (G t) (w t)) := by
    intro s
    simp only [slope, vsub_eq_sub, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.map_sub,
      smul_eq_mul]
    ring
  have hF : (fun s : ℝ => (slope (fun σ => Φ (G σ) (w t)) t s
        + (Φ (G s) - Φ (G t)) (slope w t s)) + Φ (G t) (slope w t s))
      = slope (fun s => Φ (G s) (w s)) t := by
    funext s
    rw [hdecomp s, slope, vsub_eq_sub, smul_eq_mul]
  -- change to the `Φ`-form
  change HasDerivAt (fun s => Φ (G s) (w s))
    (lapRm4 (G t) x (Function.update p j (w t))
      + react4 Work.Diff.GE.reactionMap (G t) x (Function.update p j (w t)) + Φ (G t) w') t
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum : Tendsto (fun s : ℝ => (slope (fun σ => Φ (G σ) (w t)) t s
        + (Φ (G s) - Φ (G t)) (slope w t s)) + Φ (G t) (slope w t s)) (𝓝[≠] t)
      (𝓝 (lapRm4 (G t) x (Function.update p j (w t))
        + react4 Work.Diff.GE.reactionMap (G t) x (Function.update p j (w t)) + Φ (G t) w')) := by
    simpa using (h1.add h2).add h3
  rw [← hF]
  exact hsum

end Work.Diff.GE.EvolB
