import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- The Euclidean norm of a coordinate cross product is at most the product of the norms:
`crossProduct` (`⨯₃`) is Mathlib's bilinear form on `Fin 3 → ℝ`, and
`InnerProductGeometry.norm_ofLp_crossProduct` computes `‖a × b‖ = ‖a‖ ‖b‖ sin ∠(a,b)`. -/
private lemma norm_toLp_cross_le (a b : R3) :
    ‖WithLp.toLp 2 (crossProduct a b)‖ ≤ ‖a‖ * ‖b‖ := by
  rw [InnerProductGeometry.norm_ofLp_crossProduct a b]
  calc ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b)
      ≤ ‖a‖ * ‖b‖ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
    _ = ‖a‖ * ‖b‖ := by ring

/-- **The curl is bounded by three times the derivative**:
`‖vorticity u x‖ ≤ 3 * ‖fderiv ℝ u x‖`.  This holds with no hypothesis on `u`, since Lean's
`fderiv` is the junk value `0` where `u` is not differentiable (and then so is the curl). -/
theorem norm_vorticity_le_three (u : R3 → R3) (x : R3) :
    ‖FiniteTimeSingularity.vorticity u x‖ ≤ 3 * ‖fderiv ℝ u x‖ := by
  have hsplit : FiniteTimeSingularity.vorticity u x
      = ∑ i : Fin 3,
          WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
            (fderiv ℝ u x (FiniteTimeSingularity.e i))) := by
    rw [show FiniteTimeSingularity.vorticity u x
        = WithLp.toLp 2 (∑ i : Fin 3,
            crossProduct (FiniteTimeSingularity.e i)
              (fderiv ℝ u x (FiniteTimeSingularity.e i))) from rfl]
    exact WithLp.toLp_sum 2 (Fin 3 → ℝ) Finset.univ _
  have he (i : Fin 3) : ‖FiniteTimeSingularity.e i‖ = (1 : ℝ) := by
    simp [FiniteTimeSingularity.e]
  rw [hsplit]
  calc ‖∑ i : Fin 3, WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖
      ≤ ∑ i : Fin 3, ‖WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3,
          ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖ :=
        Finset.sum_le_sum (fun i _ => norm_toLp_cross_le _ _)
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ u x‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u x) (FiniteTimeSingularity.e i)
        rw [he i, mul_one] at h
        calc ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖
            ≤ 1 * (‖fderiv ℝ u x‖ * 1) :=
              mul_le_mul (le_of_eq (he i)) (by simpa using h) (norm_nonneg _) (by norm_num)
          _ = ‖fderiv ℝ u x‖ := by ring
    _ = 3 * ‖fderiv ℝ u x‖ := by simp

/-- **Positive-time regularity of the vorticity slices** (piece of `tendsto_timeDeriv_physVel`).

If the Biot–Savart velocity `u = physVel ω` is jointly `C^{1,α}` on every strip `ℝ³ × [0,S']`
with `S' < T`, and ω is the pointwise curl of `u` at every time `s ∈ [0,T)`, then on the
half-open interval `(0,S]` (with `S ∈ (0,T)`) the vorticity slices `ω · s` are uniformly bounded
and almost everywhere strongly measurable.

Recipe: take `S' ∈ Ioo 0 T` with `S < S'` (e.g. `(S+T)/2`) and `hcd := ContDiffOn ℝ 1
(uncurry (physVel ω)) (univ ×ˢ Icc 0 S')` from `hstrips`.  The second component of
`IsContDiffHolderOn` bounds `fderivWithin ℝ (uncurry (physVel ω)) (univ ×ˢ Icc 0 S')` on that
strip by some `C ≥ 0` (`Bornology.IsBounded.exists_pos_norm_le`).  For `s ∈ Ioc 0 S` and any `z`
the point `(z,s)` is an *interior* point of the strip, so `ContDiffOn.contDiffAt` +
`fderivWithin_of_mem_nhds` give the honest derivative `fderiv ℝ (uncurry (physVel ω)) (z,s)` with
the same bound, and (`fderiv_comp` + `hasFDerivAt_prodMk_left`) the derivative of the slice
`fun y => physVel ω y s` is `(fderiv ℝ (uncurry (physVel ω)) (z,s)) ∘L ContinuousLinearMap.inl`.
Hence the vorticity (a finite sum of three cross products `e i ⨯₃ (Du (e i))`) is bounded by a
multiple of `C`, and (by continuity, since `fderiv ℝ (uncurry …) (·, s)` is continuous as a
composition of a continuous map on the open strip with `z ↦ (z,s)`) each slice is continuous,
hence a.e. strongly measurable.

Possible useful templates inside the workspace: `Submission/Work/SolutionDelivery/Measurable/
continuousOn_vorticity_of_contDiffOn.lean` (`fderiv_slice_eq`, `curlOf`, `continuous_curlOf` —
but note that file assumes a two-sided *open* window `extWindow T`, whereas here the strip is
`univ ×ˢ Icc 0 S'`, so only the *interior* points `s ∈ Ioo 0 S'` are covered) and
`Submission/Work/FTS/BSIdent/Liouville/continuous_vorticity_of_contDiff.lean`
(`fun_prop` handles the continuity of `vorticity`). Do not import the `SolutionDelivery` modules
(their import closure contains `sorry`s); copy the few lines you need. -/

/-
**Remark on the route.**  The strip used below is `univ ×ˢ Icc 0 S` *itself* (the hypothesis
`hstrips` applies at `S' = S` since `S ∈ Ioo 0 T`): the target half-open interval `(0,S]` lies in
the closed strip, and the only defect of the boundary line `s = S` is that the joint derivative is
available only *within* the strip — which is precisely what `IsContDiffHolderOn` bounds and what
`fderiv_slice_eq_fderivWithin_prod` (from
`Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips`) converts into the honest
spatial derivative of the slice.  So no auxiliary `S' > S` and no interiority argument is needed. -/
theorem omegaSliceRegularPos {α : NNReal} {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    (∃ M, 0 ≤ M ∧ ∀ s ∈ Set.Ioc 0 S, ∀ x, ‖ω x s‖ ≤ M) ∧
      ∀ s ∈ Set.Ioc 0 S,
        MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume := by
  obtain ⟨hcd, hbdd, -⟩ := hstrips S hS
  -- A uniform bound `B` on the joint derivative, within the closed strip `ℝ³ × [0,S]`.
  obtain ⟨B, hBpos, hB⟩ := hbdd.exists_pos_norm_le
  have hBdd : ∀ p ∈ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)),
      ‖fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p‖ ≤ B :=
    fun p hp => hB _ ⟨p, hp, rfl⟩
  -- The honest spatial derivative of a slice is the spatial block of the within-derivative.
  have hslice_eq : ∀ s ∈ Set.Ioc 0 S, ∀ x : R3,
      fderiv ℝ (fun y => Work.FTS.Physical.physVel ω y s) x
        = fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
            (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s)
          ∘SL ContinuousLinearMap.inl ℝ R3 ℝ := by
    intro s hs x
    have hsIcc : s ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hs.1, hs.2⟩
    exact fderiv_slice_eq_fderivWithin_prod (u := Work.FTS.Physical.physVel ω)
      (I := Set.Icc (0 : ℝ) S) hsIcc (hcd.contDiffWithinAt ⟨trivial, hsIcc⟩)
  constructor
  · -- Uniform bound on `(0,S]`.
    refine ⟨3 * B, by positivity, fun s hs x => ?_⟩
    have hsIcc : s ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hs.1, hs.2⟩
    have hsT : s ∈ Set.Ico 0 T := ⟨le_of_lt hs.1, lt_of_le_of_lt hs.2 hS.2⟩
    set L : (R3 × ℝ) →L[ℝ] R3 :=
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) with hL
    have hLb : ‖L‖ ≤ B := hBdd (x, s) ⟨trivial, hsIcc⟩
    -- composing with `inl` does not increase the operator norm
    have hcomp : ‖L ∘SL ContinuousLinearMap.inl ℝ R3 ℝ‖ ≤ ‖L‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
      calc ‖(L ∘SL ContinuousLinearMap.inl ℝ R3 ℝ) v‖ = ‖L (v, (0 : ℝ))‖ := rfl
        _ ≤ ‖L‖ * ‖(v, (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm L (v, (0 : ℝ))
        _ = ‖L‖ * ‖v‖ := by simp
    have h3 : ‖fderiv ℝ (fun y => Work.FTS.Physical.physVel ω y s) x‖ ≤ B := by
      rw [hslice_eq s hs x]
      exact le_trans hcomp hLb
    calc ‖ω x s‖
        = ‖FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x‖ := by
          rw [hcurl s hsT x]
      _ ≤ 3 * ‖fderiv ℝ (fun y => Work.FTS.Physical.physVel ω y s) x‖ :=
          norm_vorticity_le_three _ _
      _ ≤ 3 * B := by linarith
  · -- Almost-everywhere strong measurability: each slice is continuous.
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hs.1, hs.2⟩
    have hsT : s ∈ Set.Ico 0 T := ⟨le_of_lt hs.1, lt_of_le_of_lt hs.2 hS.2⟩
    have hUd : UniqueDiffOn ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
      UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS.1)
    have hcont : ContinuousOn (fun p : R3 × ℝ =>
        fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p) (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
      hcd.continuousOn_fderivWithin hUd le_rfl
    have h1 : Continuous (fun z : R3 =>
        fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s)) :=
      hcont.comp_continuous (by fun_prop) (fun _ => ⟨trivial, hsIcc⟩)
    have h2 : Continuous (fun z : R3 =>
        fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ) :=
      h1.clm_comp continuous_const
    have h3 : Continuous (fun z : R3 => curlOf
        (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)) :=
      continuous_curlOf.comp h2
    have heq : (fun z : R3 => ω z s) = fun z : R3 => curlOf
        (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ) := by
      funext z
      rw [← hcurl s hsT z, vorticity_eq_curlOf, hslice_eq s hs z]
    rw [heq]
    exact h3.aestronglyMeasurable

end Work.FTS.PressureOn
