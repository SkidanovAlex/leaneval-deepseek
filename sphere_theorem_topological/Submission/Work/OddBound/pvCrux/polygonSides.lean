import Mathlib
import Submission.Work.OddBound.polygonValue.Basic
import Submission.Work.OddBound.pvCrux.continuousMinimisingInterp
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.design.PolygonValueBoundFamily

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.OddBound.pvCrux

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

noncomputable section

/-! ## Two geodesic-theory helpers -/

/-- **The `GExp`-ray of a geodesic from an arbitrary base time.**  If `γ` is a geodesic at every
time, smooth with nowhere vanishing velocity, then for every base time `t₀` and `T ≥ 0` the curve
`s ↦ γ (t₀ + s)` is the `GExp`-ray of its initial velocity on `[0,T]`.  This is
`Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt` applied to the time-shifted geodesic
`γ (· + t₀)`, whose velocity at `0` is `γ̇ t₀`
(`Submission.SecondVarGlobal.curveVelocity_comp_add_right`) and which is again a geodesic
(`Submission.HopfRinow.isGeodesicAt_comp_affine`). -/
private lemma geodesic_GExp_ray_at_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (t₀ T : ℝ) (hT : 0 ≤ T) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      γ (t₀ + s) = Submission.GlobalExp.GExp (cov := cov) hmet (γ t₀)
        (s • Submission.Geodesic.curveVelocity (I := I) γ t₀) := by
  intro s hs
  have hmd : ∀ u : ℝ, MDiffAt γ u := fun u =>
    hγsm.contMDiffAt.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hsm1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => s + t₀) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  have hsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => γ (s + t₀)) (Set.Ioo (-1 : ℝ) (T+1)) :=
    (hγsm.comp hsm1).contMDiffOn
  have hvel : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => γ (s + t₀)) 0
      = Submission.Geodesic.curveVelocity (I := I) γ t₀ := by
    have h := Submission.SecondVarGlobal.curveVelocity_comp_add_right (I := I) γ t₀ 0
      (by simpa using hmd t₀)
    have h' : (0 : ℝ) + t₀ = t₀ := zero_add t₀
    rw [h'] at h
    exact h
  have hne' : ∀ t ∈ Set.Ioo (-1 : ℝ) (T+1),
      Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => γ (s + t₀)) t ≠ 0 := by
    intro t ht
    have h := Submission.SecondVarGlobal.curveVelocity_comp_add_right (I := I) γ t₀ t (hmd (t + t₀))
    rw [h]
    exact hne _
  have hgeo' : ∀ t ∈ Set.Ioo (-1 : ℝ) (T+1),
      Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ (s + t₀)) t := by
    intro t ht
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := 1) (b := t₀)
      (c := t + t₀ - 1) (d := t + t₀ + 1) one_ne_zero hγsm.contMDiffOn (fun y _ => hgeo y)
      (r := t) (by constructor <;> linarith)
    simpa [one_mul] using h
  have h0 : (fun s : ℝ => γ (s + t₀)) 0 = γ t₀ := by simp
  have hmain := Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet (p := γ t₀)
    (V := Submission.Geodesic.curveVelocity (I := I) γ t₀) (hne t₀) (a := -1) (b := T+1) (T := T)
    (by norm_num) hT (by linarith) hsm hgeo' hne' h0 hvel
  have h := hmain s hs
  rwa [add_comm] at h

/-- **A point at distance `s` from `x` and `r - s` from `y`, with `d x y = r`, lies on the ray of
the minimising vector from `x` to `y`.**  Here `r < ρ` is below the injectivity radius at `x`, and
`y` is known to be on the ray of the unit vector `v`.  This is the "no corner" principle: the broken
path `x → m → y` is minimising, so `m` is the point of the ray at arclength `s`. -/
private lemma eq_GExp_smul_of_broken_dist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y m : M} {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r < ρ) (hs0 : 0 < s) (hsr : s < r)
    (hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x ρ)
    {v : TangentSpace I x} (hv : ‖v‖ = 1)
    (hy : y = Submission.GlobalExp.GExp (cov := cov) hmet x (r • v))
    (hm1 : Manifold.riemannianEDist I x m = ENNReal.ofReal s)
    (hm2 : Manifold.riemannianEDist I m y = ENNReal.ofReal (r - s)) :
    m = Submission.GlobalExp.GExp (cov := cov) hmet x (s • v) := by
  have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have hrnorm : ‖r • v‖ = r := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hr.le]
  have hxy : Manifold.riemannianEDist I x y = ENNReal.ofReal r := by
    rw [hy]
    have h := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (u := r • v) hmet htor hinj
      (by rw [hrnorm]; exact hrρ) (smul_ne_zero (ne_of_gt hr) hv0)
    rw [h, hrnorm]
  have hmρ : Manifold.riemannianEDist I x m < ENNReal.ofReal ρ := by
    rw [hm1]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mpr (lt_trans hsr hrρ)
  obtain ⟨u, ⟨hu1, hu2⟩, -⟩ :=
    Submission.InjRadius.exists_unique_GExp_of_injAtLeast hmet htor hinj hmρ
  have hus : ‖u‖ = s := by
    have h : ENNReal.ofReal ‖u‖ = ENNReal.ofReal s := by rw [← hu2, hm1]
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg u) hs0.le).mp h
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hus; linarith
  set w : TangentSpace I x := s⁻¹ • u with hw
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ s⁻¹), hus,
      inv_mul_cancel₀ (ne_of_gt hs0)]
  have hsu : s • w = u := by rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hs0), one_smul]
  have hxw : Submission.GlobalExp.GExp (cov := cov) hmet x (s • w) = m := by
    rw [hsu]; exact hu1
  have hbroken : y = Submission.GlobalExp.GExp (cov := cov) hmet x (r • w) :=
    Submission.GSField.eq_GExp_of_minimising_broken (cov := cov) hmet htor hwnorm hr.le hs0 hsr
      (by rw [hxw]; exact hm1) (by rw [hxw]; exact hm2) hxy
  have hwn : ‖r • w‖ = r := by rw [norm_smul, hwnorm, mul_one, Real.norm_of_nonneg hr.le]
  have hrw : r • w = r • v := by
    obtain ⟨z, ⟨hz1, hz2⟩, hzuniq⟩ :=
      Submission.InjRadius.exists_unique_GExp_of_injAtLeast hmet htor hinj
        (by rw [hxy]; exact (ENNReal.ofReal_lt_ofReal_iff hρ).mpr hrρ)
    have e1 : r • w = z := hzuniq (r • w) ⟨hbroken.symm, by rw [hwn, hxy]⟩
    have e2 : r • v = z := hzuniq (r • v) ⟨hy.symm, by rw [hrnorm, hxy]⟩
    rw [e1, e2]
  have hwv : w = v := by
    have h := congrArg (fun z : TangentSpace I x => r⁻¹ • z) hrw
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hr)] using h
  rw [← hxw, hwv]

end

/-- **The side-curve family of `Work.OddBound.polygonValue.brokenGeodesicFamily`, and the fact that
at `τ = 0` every side has length `L/N`.**

Under the hypothesis that every slice of `w` has energy `< 2π²/K`, every side is
shorter than `ρ` (`Work.OddBound.gonSideLen_lt_of_energy_lt`), so between consecutive vertices there
is a unique minimising geodesic; the family `S i r τ` records the point at fraction `r` of arclength
along it.  Joint continuity (in `(r,τ)`) is the content of
`Work.OddBound.polygonValue.continuousMinimisingInterp`, applied to the vertex families
`τ ↦ gonVert p (w τ) i` and `τ ↦ gonVert p (w τ) (i+1)`.

The identifications at the two ends of the family use the unit-speed geodesic structure of `γ`: at
`τ = 0` the side `i` is the arc of `γ` between `γ (L i / N)` and `γ (L (i+1) / N)` (`hS0slice`), and
at `τ = 1` all vertices are `p`, so every side curve is constant (`hS1slice`).  These are the
hypotheses of `Work.OddBound.polygonValue.balancedBrokenLoop`, which concatenates and balances the
family; together with the equal side lengths at `τ = 0` (from `hunit` and the minimality of the
sub-arcs, `L/N < ρ` by `Work.OddBound.div_lt_of_lt_two_pi_div_sqrt`) they are exactly what
`Work.OddBound.polygonValue.brokenGeodesicFamily` needs.

For the `τ = 0` clause: the point `S i r 0` is at distance `r · L/N` from `x = γ (L i / N)` and
`(1 - r) · L/N` from `y = γ (L (i+1) / N)`, with `d(x,y) = L/N`, so the broken path `x → S i r 0 → y`
is minimising; writing it as a ray and applying the no-corner result
(`Submission.GSField.eq_GExp_of_minimising_broken`) identifies it with the ray of the minimising
vector `v` from `x` to `y`, and `γ (L (i + r) / N) = GExp x (r • v)` is the same ray by
`Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt` (`hunit` says `‖γ'‖ = 1` on `[0,L]`). -/
theorem polygonSides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {L : ℝ} (hL : 0 < L) (hLlt : L < 2 * Real.pi / Real.sqrt K) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hper : ∀ t : ℝ, γ (t + L) = γ t) (hγ0 : γ 0 = p)
    {ρ : ℝ} (hρ : 0 < ρ) (hρlt : ρ < Real.pi / Real.sqrt K)
    (hρinj : ∀ x : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet x ρ)
    {N : ℕ} (hN : 3 ≤ N) (hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ))
    {w : ℝ → Fin (N - 1) → M} (hwcont : Continuous w)
    (hw0 : w 0 = fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N))
    (hw1 : ∀ i : Fin (N - 1), w 1 i = p)
    (hE : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Work.OddBound.gonEnergy (I := I) p (w τ) < 2 * Real.pi ^ 2 / K) :
    (∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p (w 0) (i : ℕ) = L / N) ∧
      ∃ S : Fin N → ℝ → ℝ → M,
        (∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) ∧
        (∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
          ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1)) ∧
        (∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
          S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ)) ∧
        (∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
          S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1)) ∧
        (∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
          0 ≤ a → a ≤ b → b ≤ 1 →
          Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
            = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ)) ∧
        (∀ (i : Fin N) (r : ℝ), r ∈ Set.Icc (0 : ℝ) 1 →
          S i r 0 = γ (L * ((i : ℕ) + r) / N)) ∧
        (∀ (i : Fin N) (r : ℝ), r ∈ Set.Icc (0 : ℝ) 1 → S i r 1 = p) := by
  classical
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hLNlt : L / N < ρ :=
    Work.OddBound.div_lt_of_lt_two_pi_div_sqrt (K := K) (ρ := ρ) (L := L) hK hρ hN hbig hLlt
  have hLNpos : 0 < L / N := div_pos hL (by positivity)
  -- the vertices of the `τ = 0` slice
  have hvert0 : ∀ j : ℕ, j ≤ N → Work.OddBound.gonVert p (w 0) j = γ (L * (j : ℝ) / N) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hjpos
    · subst h0
      simp [Work.OddBound.gonVert_zero, hγ0]
    · rcases lt_or_eq_of_le hj with hlt | heq
      · have hmem : j - 1 < N - 1 := by omega
        have hsucc := Work.OddBound.gonVert_succ p (w 0) hmem
        rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hsucc
        rw [hsucc, hw0]
        have hsub : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
        beta_reduce
        rw [hsub]
        ring_nf
      · rw [heq, Work.OddBound.gonVert_of_le p (w 0) le_rfl]
        have hLN' : L * (N : ℝ) / N = L := by rw [mul_div_assoc, div_self hNne, mul_one]
        rw [hLN', ← hγ0]
        simpa using (hper 0).symm
  -- unit speed of the sub-arcs
  have hξnorm : ∀ i : Fin N,
      ‖Submission.Geodesic.curveVelocity (I := I) γ (L * ((i : ℕ) : ℝ) / N)‖ = 1 := by
    intro i
    have hmem : L * ((i : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) L := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ))]
      have hi : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_of_lt i.isLt
      nlinarith [hL, hi]
    have h := hunit _ hmem
    rw [Submission.Length.curveSpeed, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)] at h
    exact h
  -- the arc of `γ` is the `GExp`-ray of the base point
  have hray : ∀ i : Fin N, ∀ s ∈ Set.Icc (0 : ℝ) (L / N),
      γ (L * ((i : ℕ) : ℝ) / N + s)
        = Submission.GlobalExp.GExp (cov := cov) hmet (γ (L * ((i : ℕ) : ℝ) / N))
            (s • Submission.Geodesic.curveVelocity (I := I) γ (L * ((i : ℕ) : ℝ) / N)) :=
    fun i => geodesic_GExp_ray_at_base (I := I) (cov := cov) hmet hγsm hgeo hne _ _
      (le_of_lt hLNpos)
  -- the extended distance between consecutive vertices of the `τ = 0` slice
  have hed0 : ∀ i : Fin N,
      Manifold.riemannianEDist I (γ (L * ((i : ℕ) : ℝ) / N))
          (γ (L * (((i : ℕ) + 1 : ℕ) : ℝ) / N)) = ENNReal.ofReal (L / N) := by
    intro i
    have hstep : L * (((i : ℕ) + 1 : ℕ) : ℝ) / N = L * ((i : ℕ) : ℝ) / N + L / N := by
      push_cast; ring
    rw [hstep, hray i (L / N) ⟨le_of_lt hLNpos, le_rfl⟩]
    have hnorm : ‖(L / N) • Submission.Geodesic.curveVelocity (I := I) γ (L * ((i : ℕ) : ℝ) / N)‖
        = L / N := by
      rw [norm_smul, hξnorm i, mul_one, Real.norm_of_nonneg (le_of_lt hLNpos)]
    have hlt : ‖(L / N) • Submission.Geodesic.curveVelocity (I := I) γ (L * ((i : ℕ) : ℝ) / N)‖
        < ρ := by rw [hnorm]; exact hLNlt
    have hne' : (L / N) • Submission.Geodesic.curveVelocity (I := I) γ (L * ((i : ℕ) : ℝ) / N)
        ≠ 0 := smul_ne_zero (ne_of_gt hLNpos) (hne _)
    have hspec := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (I := I) (cov := cov)
      (u := (L / N) • Submission.Geodesic.curveVelocity (I := I) γ (L * ((i : ℕ) : ℝ) / N))
      hmet htor (hρinj _) hlt hne'
    rwa [hnorm] at hspec
  -- the side lengths of the `τ = 0` slice
  have hside : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p (w 0) (i : ℕ) = L / N := by
    intro i
    unfold Work.OddBound.gonSideLen
    rw [hvert0 _ (by omega), hvert0 _ (by omega), Work.OddBound.polygon.riemannianDist_eq_toReal,
      hed0 i, ENNReal.toReal_ofReal (le_of_lt hLNpos)]
  constructor
  · exact hside
  · haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      Submission.EDist.isContinuousRiemannianBundle_of_contMDiffRiemannianBundle (I := I) (n := ∞)
    -- continuity of the vertex families
    have hcontVert : ∀ j : ℕ, Continuous (fun τ : ℝ => Work.OddBound.gonVert p (w τ) j) := by
      intro j
      rcases Nat.eq_zero_or_pos j with h0 | hjpos
      · subst h0
        simpa using (continuous_const : Continuous (fun _ : ℝ => (p : M)))
      · rcases lt_or_ge j N with hjN | hNj
        · have hmem : j - 1 < N - 1 := by omega
          have hfun : (fun τ : ℝ => Work.OddBound.gonVert p (w τ) j)
              = fun τ => w τ ⟨j - 1, hmem⟩ := by
            funext τ
            have hsucc := Work.OddBound.gonVert_succ p (w τ) hmem
            rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hsucc
            exact hsucc
          rw [hfun]
          exact (continuous_apply ⟨j - 1, hmem⟩).comp hwcont
        · have hconst : (fun τ : ℝ => Work.OddBound.gonVert p (w τ) j) = fun _ : ℝ => p := by
            funext τ; exact Work.OddBound.gonVert_of_le p (w τ) hNj
          rw [hconst]; exact continuous_const
    -- the interpolation family of each side
    have key : ∀ i : Fin N, ∃ S : ℝ → ℝ → M,
        ContinuousOn (fun u : ℝ × ℝ => S u.1 u.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, S 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, S 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S r τ) (Set.Icc (0 : ℝ) 1)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
          Submission.Length.curveLength (I := I) (fun r : ℝ => S r τ) a b
            = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
          Manifold.riemannianEDist I (Work.OddBound.gonVert p (w τ) (i : ℕ)) (S r τ)
            = ENNReal.ofReal (r * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
          Manifold.riemannianEDist I (S r τ) (Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
            = ENNReal.ofReal ((1 - r) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))) := by
      intro i
      exact continuousMinimisingInterp (I := I) (cov := cov) hmet htor (hcontVert (i : ℕ))
        (hcontVert ((i : ℕ) + 1)) hρ hρinj (fun τ hτ => by
          show Submission.Distance.riemannianDist (I := I) (Work.OddBound.gonVert p (w τ) (i : ℕ))
            (Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1)) < ρ
          exact Work.OddBound.gonSideLen_lt_of_energy_lt (I := I) hN hbig hK hρ (w τ) (hE τ hτ) i)
    choose S hScont hS0 hS1 hSsm hSlen hSd1 hSd2 using key
    refine ⟨S, hScont, ?_, hS0, hS1, ?_, ?_, ?_⟩
    · exact hSsm
    · exact hSlen
    · -- `τ = 0`: the side is the arc of `γ`
      intro i r hr
      have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      have hx0 : Work.OddBound.gonVert p (w 0) (i : ℕ) = γ (L * ((i : ℕ) : ℝ) / N) :=
        hvert0 _ (by omega)
      have hy0 : Work.OddBound.gonVert p (w 0) ((i : ℕ) + 1)
          = γ (L * (((i : ℕ) + 1 : ℕ) : ℝ) / N) := hvert0 _ (by omega)
      have hd0 : Work.OddBound.gonSideLen (I := I) p (w 0) (i : ℕ) = L / N := hside i
      rcases eq_or_lt_of_le hr.1 with hr0 | hrpos
      · rw [← hr0, hS0 i 0 h0mem, hx0]
        congr 1
        push_cast
        ring
      · rcases eq_or_lt_of_le hr.2 with hr1 | hrlt
        · rw [hr1, hS1 i 0 h0mem, hy0]
          congr 1
          push_cast
          ring
        · have harg : L * (((i : ℕ) + 1 : ℕ) : ℝ) / N
              = L * ((i : ℕ) : ℝ) / N + L / N := by push_cast; ring
          have hrayi := hray i (L / N) ⟨le_of_lt hLNpos, le_rfl⟩
          have hy : Work.OddBound.gonVert p (w 0) ((i : ℕ) + 1)
              = Submission.GlobalExp.GExp (cov := cov) hmet (γ (L * ((i : ℕ) : ℝ) / N))
                  ((L / N) • Submission.Geodesic.curveVelocity (I := I) γ
                    (L * ((i : ℕ) : ℝ) / N)) := by
            rw [hy0, harg, hrayi]
          have e1 : Manifold.riemannianEDist I (γ (L * ((i : ℕ) : ℝ) / N)) (S i r 0)
              = ENNReal.ofReal (r * (L / N)) := by
            have h := hSd1 i 0 h0mem r hr
            beta_reduce at h
            rw [hx0, hd0] at h
            exact h
          have e2 : Manifold.riemannianEDist I (S i r 0)
              (Work.OddBound.gonVert p (w 0) ((i : ℕ) + 1))
              = ENNReal.ofReal (L / N - r * (L / N)) := by
            have h := hSd2 i 0 h0mem r hr
            beta_reduce at h
            rw [hd0] at h
            rw [h]
            congr 1
            ring
          have hslt : r * (L / N) < 1 * (L / N) := mul_lt_mul_of_pos_right hrlt hLNpos
          have hslt' : r * (L / N) < L / N := by simpa using hslt
          have hsmem : r * (L / N) ∈ Set.Icc (0 : ℝ) (L / N) :=
            ⟨le_of_lt (mul_pos hrpos hLNpos), le_of_lt hslt'⟩
          have hmain := eq_GExp_smul_of_broken_dist (I := I) (cov := cov) hmet htor hρ hLNpos
            hLNlt (mul_pos hrpos hLNpos) hslt' (hρinj _) (hξnorm i) hy e1 e2
          rw [hmain, ← hray i (r * (L / N)) hsmem]
          congr 1
          ring
    · -- `τ = 1`: all vertices are `p`, so every side curve is constant
      intro i r hr
      have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      have hx1 : Work.OddBound.gonVert p (w 1) (i : ℕ) = p := by
        rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
        · rw [h0]; exact Work.OddBound.gonVert_zero p (w 1)
        · rcases lt_or_ge ((i : ℕ)) N with hiN | hiN
          · have hmem : (i : ℕ) - 1 < N - 1 := by omega
            have hsucc := Work.OddBound.gonVert_succ p (w 1) hmem
            rw [Nat.sub_add_cancel (by omega : 1 ≤ (i : ℕ))] at hsucc
            rw [hsucc, hw1]
          · exact Work.OddBound.gonVert_of_le p (w 1) hiN
      have hy1 : Work.OddBound.gonVert p (w 1) ((i : ℕ) + 1) = p := by
        rcases lt_or_ge ((i : ℕ) + 1) N with hiN | hiN
        · have hmem : (i : ℕ) < N - 1 := by omega
          rw [Work.OddBound.gonVert_succ p (w 1) hmem, hw1]
        · exact Work.OddBound.gonVert_of_le p (w 1) hiN
      have hd1 : Work.OddBound.gonSideLen (I := I) p (w 1) (i : ℕ) = 0 := by
        unfold Work.OddBound.gonSideLen
        rw [hx1, hy1, Submission.Distance.riemannianDist_self]
      have he := hSd1 i 1 h1mem r hr
      beta_reduce at he
      rw [hd1, mul_zero, ENNReal.ofReal_zero] at he
      have heq := (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp he
      rw [hx1] at heq
      exact heq.symm

end Work.OddBound.pvCrux
