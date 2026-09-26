import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Main
import Submission.Work.InnermostDisk.not_isEssential_of_const
import Submission.Work.InnermostDisk.isEssential_iff_hasWinding
import Submission.Work.InnermostDisk.homotopic_iff_homotopicClosed
import Submission.Work.InnermostDisk.not_isEssential_of_section

/-!
# A curve bounding a disc in the surface is inessential

If `α` is a closed curve of the surface `F = P.carrier` of a parametrised torus and `α` bounds
a (continuous, possibly non-injective) disc *in the surface* — `BoundsDiscInSurface P α` — then
`α` is null-homotopic in `F`, hence not essential: its winding vector vanishes.

The proof proceeds as follows.

* The disc `e` gives an explicit contraction of `α` to the point `e 0`: the homotopy
  `H (s, t) = e (clamp s • circlePoint t)` (where `clamp s ∈ [0,1]`) runs from the constant
  curve at `e 0` to `α`, through closed curves of `F`.  This is
  `homotopicClosed_of_fillsDisc`.
* The winding vector is a homotopy invariant of closed curves on the torus
  (`homotopicClosed_winding_eq_param`, the version of
  `Work.TorusCover.hasWinding_eq_of_homotopicClosed` for a `ParamTorus`, which does not carry
  the immersion hypothesis (iii) of `TorusParam`).
* The constant curve has vanishing winding vector (`Work.TorusCover.hasWinding_zero_of_const`),
  so `α` does too, and `Work.TorusCover.IsEssential` is "nonzero winding vector".

Everything is phrased in the `Work.TorusCover` vocabulary; the bridge to
`Work.CoreTopology.IsEssential` is `Work.InnermostDisk.isEssential_iff_hasWinding`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-! ## The circle point is periodic -/

/-- `circlePoint` is `2π`-periodic: the point `e^{iθ}` of the unit circle only depends on `θ`
modulo `2π`. -/
theorem circlePoint_add_two_pi (θ : ℝ) :
    circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  rw [circlePoint_coe, circlePoint_coe,
    show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I from by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `circlePoint` is continuous. -/
theorem continuous_circlePoint :
    Continuous (circlePoint : ℝ → Metric.closedBall (0 : ℂ) 1) := by
  refine Continuous.subtype_mk ?_ (fun θ => (circlePoint θ).2)
  show Continuous fun θ : ℝ => Complex.exp (θ * Complex.I)
  fun_prop

/-! ## A clamp `ℝ → [0,1]` -/

/-- The continuous map `ℝ → [0,1]` which is `s` for `0 ≤ s ≤ 1` and is clamped outside. -/
def clamp (s : ℝ) : ℝ := max 0 (min s 1)

theorem continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp_mem_Icc (s : ℝ) : clamp s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem clamp_abs_le_one (s : ℝ) : |clamp s| ≤ 1 := by
  have h := clamp_mem_Icc s
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2⟩

@[simp] theorem clamp_zero : clamp 0 = 0 := by
  simp [clamp]

@[simp] theorem clamp_one : clamp 1 = 1 := by
  simp [clamp]

/-- Scaling the point `e^{iθ}` of the unit circle by `clamp s` stays inside the unit disc. -/
theorem clamp_smul_circlePoint_mem (s t : ℝ) :
    clamp s • (circlePoint t : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
  have h1 : |clamp s| ≤ 1 := clamp_abs_le_one s
  have h2 : ‖(circlePoint t : ℂ)‖ ≤ 1 := by
    have := (circlePoint t).2
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  calc |clamp s| * ‖(circlePoint t : ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-! ## The explicit contraction of a filling disc -/

/-- The point `clamp s • e^{it}` of the disc, as a continuous function of `(s,t)`. -/
theorem continuous_clamp_smul_circlePoint :
    Continuous (fun st : ℝ × ℝ =>
      (⟨clamp st.1 • (circlePoint st.2 : ℂ), clamp_smul_circlePoint_mem st.1 st.2⟩ :
        Metric.closedBall (0 : ℂ) 1)) := by
  refine Continuous.subtype_mk ?_ (fun st : ℝ × ℝ => clamp_smul_circlePoint_mem st.1 st.2)
  exact (continuous_clamp.comp continuous_fst).smul
    (continuous_subtype_val.comp (continuous_circlePoint.comp continuous_snd))

/-- **A disc filling `α` contracts `α` to a point.**

If `e : 𝔻 → F` is a continuous map into the surface of a parametrised torus whose boundary
circle maps to the closed curve `α`, then `α` is homotopic through closed curves of `F` to the
constant curve at `e 0`.  The homotopy is `(s,t) ↦ e (clamp s • e^{it})`. -/
theorem homotopicClosed_of_fillsDisc (P : Work.CoreTopology.ParamTorus)
    {α : Work.CoreTopology.ClosedCurve P} (e : C(Disc, P.carrier))
    (he : ∀ θ : ℝ, (e (circlePoint θ) : R3) = α.γ θ) :
    Work.TorusCover.HomotopicClosed P.psi (fun _ => (e 0 : R3)) α.γ := by
  let Φ : ℝ × ℝ → Disc := fun st =>
    ⟨clamp st.1 • (circlePoint st.2 : ℂ), clamp_smul_circlePoint_mem st.1 st.2⟩
  have hΦ_cont : Continuous Φ := continuous_clamp_smul_circlePoint
  have hΦ0 : ∀ t : ℝ, Φ (0, t) = (0 : Disc) := by
    intro t
    apply Subtype.ext
    simp [Φ, clamp]
  have hΦ1 : ∀ t : ℝ, Φ (1, t) = circlePoint t := by
    intro t
    apply Subtype.ext
    simp [Φ, clamp]
  have hΦper : ∀ s t : ℝ, Φ (s, t + 2 * Real.pi) = Φ (s, t) := by
    intro s t
    apply Subtype.ext
    simp [Φ, circlePoint_add_two_pi]
  refine ⟨fun st : ℝ × ℝ => (e (Φ st) : R3), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (e.continuous.comp hΦ_cont)
  · intro t
    rw [show (fun st : ℝ × ℝ => (e (Φ st) : R3)) (0, t) = (e (Φ (0, t)) : R3) from rfl,
      hΦ0 t]
  · intro t
    rw [show (fun st : ℝ × ℝ => (e (Φ st) : R3)) (1, t) = (e (Φ (1, t)) : R3) from rfl,
      hΦ1 t]
    exact he t
  · intro s t
    show (e (Φ (s, t + 2 * Real.pi)) : R3) = (e (Φ (s, t)) : R3)
    rw [hΦper s t]
  · intro s t
    exact (e (Φ (s, t))).2

/-! ## Homotopy invariance of the winding vector for a `ParamTorus` -/

/-- **The winding vector is unique**, for a `ParamTorus`.

Two `2π`-periodic lifts of the same closed curve differ by a continuous function with values in
the (discrete) period lattice, hence by a constant; consequently they have the same period
shift, i.e. the same winding vector.  This is
`Work.TorusCover.hasWinding_unique` with the immersion hypothesis (iii) of `TorusParam`
removed. -/
theorem hasWinding_unique_param (P : Work.CoreTopology.ParamTorus)
    {γ : ℝ → R3} {v w : ℤ × ℤ}
    (hv : Work.TorusCover.HasWinding P.psi γ v) (hw : Work.TorusCover.HasWinding P.psi γ w) :
    v = w := by
  obtain ⟨Λ, hΛ⟩ := hv
  obtain ⟨Λ', hΛ'⟩ := hw
  have hmem : ∀ t, (Λ t - Λ' t) ∈ Work.TorusCover.lattice := fun t =>
    (Work.TorusCover.psiMap_eq_iff_param P).mp (by
      rw [Work.TorusCover.psiMap_apply, Work.TorusCover.psiMap_apply,
        hΛ.map_eq t, hΛ'.map_eq t])
  have hcont : Continuous (fun t : ℝ => Λ t - Λ' t) := hΛ.continuous.sub hΛ'.continuous
  have hconst := isPreconnected_univ.constant_of_mapsTo Work.TorusCover.isDiscrete_lattice
    hcont.continuousOn (fun t _ => hmem t) (mem_univ (0 : ℝ)) (mem_univ (2 * Real.pi))
  change Λ 0 - Λ' 0 = Λ (2 * Real.pi) - Λ' (2 * Real.pi) at hconst
  rw [hΛ.displacement, hΛ'.displacement] at hconst
  have hdis : Work.TorusCover.periodShift v - Work.TorusCover.periodShift w = 0 := by
    have hab : (Λ 0 + Work.TorusCover.periodShift v) - (Λ' 0 + Work.TorusCover.periodShift w)
        = (Λ 0 - Λ' 0) + (Work.TorusCover.periodShift v - Work.TorusCover.periodShift w) := by
      abel
    rw [hab] at hconst
    have h2 : (Λ 0 - Λ' 0) + (Work.TorusCover.periodShift v - Work.TorusCover.periodShift w)
        = (Λ 0 - Λ' 0) + 0 := by rw [add_zero]; exact hconst.symm
    exact add_left_cancel h2
  exact Work.TorusCover.periodShift_injective (sub_eq_zero.mp hdis)

open unitInterval in
/-- **Homotopic closed curves have the same winding vector**, for a `ParamTorus`.

This is `Work.TorusCover.hasWinding_eq_of_homotopicClosed` with the immersion hypothesis (iii)
of `TorusParam` removed: the proof only uses that `psiMapToRange P.psi` is a covering map
(`Work.TorusCover.isCoveringMap_psiMapToRange_param`), injectivity modulo `2π`, and the
discreteness of the period lattice.  The winding vector of the two curves is read off from the
period displacement of a lifted homotopy, which is constant in the homotopy parameter because
the period lattice is discrete. -/
theorem homotopicClosed_winding_eq_param (P : Work.CoreTopology.ParamTorus)
    {γ₀ γ₁ : ℝ → R3} {v w : ℤ × ℤ}
    (h : Work.TorusCover.HomotopicClosed P.psi γ₀ γ₁)
    (hv : Work.TorusCover.HasWinding P.psi γ₀ v)
    (hw : Work.TorusCover.HasWinding P.psi γ₁ w) : v = w := by
  have hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi) :=
    Work.TorusCover.isCoveringMap_psiMapToRange_param P
  obtain ⟨H, hHcont, hH0, hH1, hHper, hHrange⟩ := h
  obtain ⟨Λ₀, hΛ₀⟩ := hv
  -- the homotopy, viewed as a map into the range of `psiMap P.psi`
  let Hbar : C(ℝ × ℝ, Set.range (Work.TorusCover.psiMap P.psi)) :=
    ⟨fun st => ⟨H st, hHrange st.1 st.2⟩,
      hHcont.subtype_mk (fun st => hHrange st.1 st.2)⟩
  have hHbar_coe : ∀ st : ℝ × ℝ,
      ((Hbar st : Set.range (Work.TorusCover.psiMap P.psi)) : R3) = H st := fun st => rfl
  -- the homotopy restricted to `[0,1] × ℝ`
  let G : C(unitInterval × ℝ, Set.range (Work.TorusCover.psiMap P.psi)) :=
    Hbar.comp (ContinuousMap.prodMap ⟨Subtype.val, continuous_subtype_val⟩ (ContinuousMap.id ℝ))
  have hG_coe : ∀ (s : unitInterval) (t : ℝ),
      ((G (s, t) : Set.range (Work.TorusCover.psiMap P.psi)) : R3) = H ((s : ℝ), t) := by
    intro s t
    rw [show (G (s, t) : Set.range (Work.TorusCover.psiMap P.psi)) = Hbar ((s : ℝ), t)
        from rfl]
    exact hHbar_coe ((s : ℝ), t)
  -- the given periodic lift `Λ₀`, as a continuous map
  let Λ₀c : C(ℝ, ℝ × ℝ) := ⟨Λ₀, hΛ₀.continuous⟩
  -- the prescribed lift of the initial curve `{0} × ℝ`
  have h0 : ∀ t : ℝ, G (0, t) = Work.TorusCover.psiMapToRange P.psi (Λ₀c t) := by
    intro t
    have hL : ((G (0, t) : Set.range (Work.TorusCover.psiMap P.psi)) : R3) = γ₀ t := by
      rw [hG_coe]
      simpa using hH0 t
    have hR : ((Work.TorusCover.psiMapToRange P.psi (Λ₀c t) :
        Set.range (Work.TorusCover.psiMap P.psi)) : R3) = γ₀ t := by
      rw [Work.TorusCover.psiMapToRange_coe]
      exact hΛ₀.map_eq t
    exact Subtype.ext (hL.trans hR.symm)
  -- the lift of the whole homotopy
  let F : C(unitInterval × ℝ, ℝ × ℝ) := hcov.liftHomotopy G Λ₀c h0
  have hF_lifts : ∀ (s : unitInterval) (t : ℝ),
      Work.TorusCover.psiMapToRange P.psi (F (s, t)) = G (s, t) :=
    fun s t => congr_fun (hcov.liftHomotopy_lifts G Λ₀c h0) (s, t)
  have hF_zero : ∀ t : ℝ, F (0, t) = Λ₀ t := fun t => hcov.liftHomotopy_zero G Λ₀c h0 t
  -- `F` lies over `H`
  have hF_psi : ∀ (s : unitInterval) (t : ℝ),
      Work.TorusCover.psiMap P.psi (F (s, t)) = H ((s : ℝ), t) := by
    intro s t
    have h1 := congrArg (fun x : Set.range (Work.TorusCover.psiMap P.psi) => (x : R3))
      (hF_lifts s t)
    rw [hG_coe s t] at h1
    simpa [Work.TorusCover.psiMapToRange_coe] using h1
  -- the displacement of `F` over one period lies in the period lattice
  have hd_mem : ∀ s : unitInterval,
      (F (s, 2 * Real.pi) - F (s, 0)) ∈ Work.TorusCover.lattice := by
    intro s
    rw [← (Work.TorusCover.psiMap_eq_iff_param P), hF_psi s (2 * Real.pi), hF_psi s 0]
    simpa using hHper (s : ℝ) 0
  have hd_cont : Continuous fun s : unitInterval => F (s, 2 * Real.pi) - F (s, 0) :=
    (F.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (F.continuous.comp (continuous_id.prodMk continuous_const))
  -- ... hence is constant in `s`, since the lattice is discrete and `[0,1]` is connected
  have hd_const : ∀ s : unitInterval,
      F (s, 2 * Real.pi) - F (s, 0) = F (0, 2 * Real.pi) - F (0, 0) := by
    intro s
    exact (isPreconnected_univ.constant_of_mapsTo Work.TorusCover.isDiscrete_lattice
      hd_cont.continuousOn (fun s _ => hd_mem s) (mem_univ (0 : unitInterval))
      (mem_univ s)).symm
  have hd_one : F (1, 2 * Real.pi) - F (1, 0) = Work.TorusCover.periodShift v := by
    rw [hd_const 1, hF_zero, hF_zero, hΛ₀.displacement, add_sub_cancel_left]
  -- the lift of `γ₁` obtained from `F`, together with its period displacement
  let Λ₁ : ℝ → ℝ × ℝ := fun t => F (1, t)
  have hΛ₁cont : Continuous Λ₁ :=
    F.continuous.comp (continuous_const.prodMk continuous_id)
  have hΛ₁psi : ∀ t, P.psi (Λ₁ t).1 (Λ₁ t).2 = γ₁ t := by
    intro t
    have h1 := hF_psi 1 t
    have h2 : Work.TorusCover.psiMap P.psi (Λ₁ t) = γ₁ t := by
      rw [show Λ₁ t = F (1, t) from rfl, h1]
      simpa using hH1 t
    simpa [Work.TorusCover.psiMap_apply] using h2
  have hℓ_mem : ∀ t : ℝ, (F (1, t + 2 * Real.pi) - F (1, t)) ∈ Work.TorusCover.lattice := by
    intro t
    rw [← (Work.TorusCover.psiMap_eq_iff_param P), hF_psi 1 (t + 2 * Real.pi), hF_psi 1 t]
    simpa using hHper 1 t
  have hℓ_cont : Continuous fun t : ℝ => F (1, t + 2 * Real.pi) - F (1, t) :=
    (F.continuous.comp (continuous_const.prodMk (continuous_id.add continuous_const))).sub
      (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hℓ_const : ∀ t : ℝ,
      F (1, t + 2 * Real.pi) - F (1, t) = Work.TorusCover.periodShift v := by
    intro t
    have hc : F (1, t + 2 * Real.pi) - F (1, t) = F (1, 0 + 2 * Real.pi) - F (1, 0) :=
      isPreconnected_univ.constant_of_mapsTo Work.TorusCover.isDiscrete_lattice
        hℓ_cont.continuousOn (fun t _ => hℓ_mem t) (mem_univ (0 : ℝ)) (mem_univ t)
    rw [hc, zero_add]
    exact hd_one
  refine hasWinding_unique_param P ?_ hw
  refine ⟨Λ₁, ⟨⟨hΛ₁cont, hΛ₁psi⟩, fun t => ?_⟩⟩
  exact eq_add_of_sub_eq' (hℓ_const t)

/-! ## The main theorem -/

theorem not_isEssential_of_boundsDiscInSurface (P : Work.CoreTopology.ParamTorus)
    {α : Work.CoreTopology.ClosedCurve P} (h : Work.InnermostDisk.BoundsDiscInSurface P α) :
    ¬ Work.CoreTopology.IsEssential P α := by
  rintro hEss
  obtain ⟨e, he⟩ := h
  have hTC : Work.TorusCover.IsEssential P.psi α.γ :=
    (Work.InnermostDisk.isEssential_iff_hasWinding P α).mp hEss
  obtain ⟨v, hv, hwv⟩ := hTC
  have hHom : Work.TorusCover.HomotopicClosed P.psi (fun _ => (e 0 : R3)) α.γ :=
    homotopicClosed_of_fillsDisc P e he
  have hx : (e 0 : R3) ∈ Set.range (Work.TorusCover.psiMap P.psi) := (e 0).2
  have hw0 : Work.TorusCover.HasWinding P.psi (fun _ => (e 0 : R3)) 0 :=
    Work.TorusCover.hasWinding_zero_of_const (psi := P.psi) hx
  have h0 : (0 : ℤ × ℤ) = v := homotopicClosed_winding_eq_param P hHom hw0 hwv
  exact hv h0.symm

end

end Work.InnermostDisk
