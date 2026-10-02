import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Differentiability of `z ↦ readFrame (A z) (V z)` when `V a = 0`

`Work.ThomBordism.readFrame f : ℝ^N →L[ℝ] ℝ^k` is the coordinate reading `x ↦ (⟨f j, x⟩)_j` of an
ambient vector in a frame `f`.  In the last mile of the Thom isomorphism argument the frame `A` is
merely *continuous* at the base point while the vector `V` is differentiable and **vanishes at the
point**.  This file records the resulting differentiability statement, whose derivative is
`readFrame (A a) ∘ L`: the dependence of the reading on the (only continuous) frame contributes
nothing to first order precisely because `V a = 0`, so the frame may be frozen at `A a`.

The two ingredients are

* `readFrame_sub_frame` — `readFrame` is additive in its frame argument;
* `norm_readFrame_le` — the reading is bounded by `‖funToEuc k‖ * ‖f‖ * ‖x‖`, so a frame tending to
  `0` produces a quantity that is `o(‖z - a‖)` once the vector is `O(‖z - a‖)`.
-/

open scoped Topology

namespace Work.ThomBordism.KeyLocal

/-- `readFrame` is additive in its frame argument. -/
theorem readFrame_sub_frame {N k : ℕ} (f g : Fin k → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    Work.ThomBordism.readFrame (fun j => f j - g j) x
      = Work.ThomBordism.readFrame f x - Work.ThomBordism.readFrame g x := by
  simp only [Work.ThomBordism.readFrame_apply]
  rw [show (fun j => inner ℝ (f j - g j) x)
      = (fun j => inner ℝ (f j) x) - (fun j => inner ℝ (g j) x) from by
        funext j; exact inner_sub_left _ _ _]
  rw [map_sub]

/-- The reading map is bounded: `‖readFrame f x‖ ≤ ‖funToEuc k‖ * ‖f‖ * ‖x‖`. -/
theorem norm_readFrame_le {N k : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖Work.ThomBordism.readFrame f x‖
      ≤ ‖(Work.Tubular.funToEuc k : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖
        * (‖f‖ * ‖x‖) := by
  rw [Work.ThomBordism.readFrame_apply]
  refine (ContinuousLinearMap.le_opNorm
    ((Work.Tubular.funToEuc k : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k)))
    (fun j => inner ℝ (f j) x)).trans ?_
  gcongr
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  intro j
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_le_pi_norm f j) (norm_nonneg x))

/-- **The reading of a differentiable vanishing vector in a merely continuous frame.**  If `A` is
continuous at `a`, `V` is differentiable at `a` with derivative `L`, and `V a = 0`, then
`z ↦ readFrame (A z) (V z)` is differentiable at `a` with derivative `readFrame (A a) ∘ L`. -/
theorem hasFDerivAt_readFrame_of_continuousAt {N n k : ℕ} {a : EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) → Fin k → EuclideanSpace ℝ (Fin N)}
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)}
    {L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N)}
    (hAc : ContinuousAt A a) (hV : HasFDerivAt V L a) (hVa : V a = 0) :
    HasFDerivAt (fun z => Work.ThomBordism.readFrame (A z) (V z))
      ((Work.ThomBordism.readFrame (A a)).comp L) a := by
  -- the difference of the frames, a continuous function vanishing at `a`
  set B : EuclideanSpace ℝ (Fin n) → Fin k → EuclideanSpace ℝ (Fin N) :=
    fun z j => A z j - A a j with hB
  have hBa : B a = 0 := by ext j; simp [hB]
  have hBcont : ContinuousAt B a := by
    rw [hB]
    exact hAc.sub continuousAt_const
  -- the frame difference tends to `0`
  have hBnorm_tendsto : Filter.Tendsto (fun z => ‖B z‖) (𝓝 a) (𝓝 0) := by
    have h := hBcont.norm.tendsto
    rwa [hBa, norm_zero] at h
  have hBnorm : (fun z => ‖B z‖) =o[𝓝 a] (fun _ => (1:ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hBnorm_tendsto
  -- the vanishing vector is differentiable, hence `O(‖z - a‖)`
  have hVlitt : (fun z => V z - L (z - a)) =o[𝓝 a] (fun z => z - a) := by
    simpa [hVa] using hV.isLittleO
  have hVbig : (fun z => V z) =O[𝓝 a] (fun z => z - a) := by
    have h1 : (fun z => V z - L (z - a)) =O[𝓝 a] (fun z => z - a) := hVlitt.isBigO
    have h2 : (fun z => L (z - a)) =O[𝓝 a] (fun z => z - a) :=
      ContinuousLinearMap.isBigO_comp L (fun z => z - a) (𝓝 a)
    simpa only [sub_add_cancel] using h1.add h2
  have hVnormR : (fun z => ‖V z‖) =O[𝓝 a] (fun z => ‖z - a‖) :=
    (Asymptotics.isBigO_norm_right).mpr hVbig.norm_left
  -- the product `‖B z‖ * ‖V z‖` is little-o of `‖z - a‖`
  have hmul : (fun z => ‖B z‖ * ‖V z‖) =o[𝓝 a] (fun z => ‖z - a‖) := by
    have h := hBnorm.mul_isBigO hVnormR
    simpa using h
  have hO : (fun z => Work.ThomBordism.readFrame (B z) (V z)) =O[𝓝 a]
      (fun z => ‖B z‖ * ‖V z‖) := by
    refine Asymptotics.IsBigO.of_bound
      ‖(Work.Tubular.funToEuc k : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact norm_readFrame_le (B z) (V z)
  have hH : (fun z => Work.ThomBordism.readFrame (B z) (V z)) =o[𝓝 a] (fun z => z - a) :=
    (Asymptotics.isLittleO_norm_norm).mp ((hO.trans_isLittleO hmul).norm_left)
  -- the frozen-frame part is differentiable by the chain rule with a continuous linear map
  have h2 : HasFDerivAt (fun z => Work.ThomBordism.readFrame (A a) (V z))
      ((Work.ThomBordism.readFrame (A a)).comp L) a :=
    (ContinuousLinearMap.hasFDerivAt (Work.ThomBordism.readFrame (A a))).comp a hV
  have hFa : Work.ThomBordism.readFrame (A a) (V a) = 0 := by rw [hVa, map_zero]
  -- split the difference of the two readings according to the frame difference
  have hsplit : (fun z => Work.ThomBordism.readFrame (A z) (V z)
        - Work.ThomBordism.readFrame (A a) (V a)
        - ((Work.ThomBordism.readFrame (A a)).comp L) (z - a))
      = fun z => Work.ThomBordism.readFrame (B z) (V z)
        + (Work.ThomBordism.readFrame (A a) (V z)
            - (Work.ThomBordism.readFrame (A a)) (L (z - a))) := by
    funext z
    rw [hFa, ContinuousLinearMap.comp_apply, hB, readFrame_sub_frame (A z) (A a) (V z)]
    abel
  rw [hasFDerivAt_iff_isLittleO]
  show (fun z => Work.ThomBordism.readFrame (A z) (V z)
        - Work.ThomBordism.readFrame (A a) (V a)
        - ((Work.ThomBordism.readFrame (A a)).comp L) (z - a)) =o[𝓝 a] (fun z => z - a)
  rw [hsplit]
  refine Asymptotics.IsLittleO.add hH ?_
  simpa [hFa, ContinuousLinearMap.comp_apply] using h2.isLittleO

end Work.ThomBordism.KeyLocal
