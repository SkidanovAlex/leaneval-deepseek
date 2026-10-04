import Mathlib
import Submission.Work.Final.DimOne.Defs
import Submission.ClosedGeodesic
import Submission.LensLoop
import Submission.RayChart
import Submission.BrokenLength
import Submission.GeodesicExtend
import Submission.Length
import Submission.HopfRinow2
import Submission.GeodesicSpeed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp
open Submission.Geodesic
open Set

set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- **One-dimensional linear algebra.**  In a one-dimensional real vector space every vector is a
real multiple of any given nonzero vector. -/
lemma exists_smul_eq_of_finrank_eq_one_ray {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (h : Module.finrank ℝ V = 1) {x : V} (hx : x ≠ 0) (y : V) :
    ∃ c : ℝ, y = c • x := by
  have hspan : Submodule.span ℝ ({x} : Set V) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_singleton hx, h]
  have hy : y ∈ Submodule.span ℝ ({x} : Set V) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
  exact ⟨c, hc.symm⟩

section Transport

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Transporting a tangent vector along an equality of base points does not change its norm. -/
lemma norm_transport {x y : M} (h : x = y) (v : TangentSpace I x) :
    ‖(h ▸ v : TangentSpace I y)‖ = ‖v‖ := by
  cases h
  rfl

/-- Transporting a tangent vector along an equality of base points leaves it unchanged (the two
representatives of the same vector in the two fibres agree). -/
lemma transport_self {x y : M} (h : x = y) (v : TangentSpace I x) :
    (h ▸ v : TangentSpace I y) = v := by
  cases h
  rfl

end Transport

/-- **The periodic `GExp`-ray in dimension one, for `a < b`.**  If the ray `s ↦ GExp p (s • u)`
returns to itself at two parameters `a < b` (with `u ≠ 0`, in dimension one), then it is periodic
with some positive period `Q ≤ b - a`.

Let `γ s = GExp p (s • u)` and `q = γ a = γ b`.  Both `γ'(a)` and `γ'(b)` are non-zero vectors of
the one-dimensional space `T_qM` and have the same norm (the speed of a geodesic ray is constant),
so `γ'(b) = c • γ'(a)` with `c = ±1`.

* If `c = 1` the curves `s ↦ γ (s + a)` and `s ↦ γ (s + b)` are geodesics with the same value and
  the same non-zero velocity at `0`, so they agree everywhere: `Q = b - a` is a period.
* If `c = -1` then the curves `s ↦ γ (a + s)` and `s ↦ γ (b - s)` are geodesics with the same
  value and velocity at `0`, hence are equal.  Comparing their velocities at the midpoint
  `s = (b - a)/2` gives `γ'((a+b)/2) = -γ'((a+b)/2)`, i.e. `γ'((a+b)/2) = 0`, contradicting the
  non-vanishing of the velocity of a ray.  So this case cannot occur. -/
private theorem period_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (hdim : Module.finrank ℝ E = 1)
    (p : M) (u : TangentSpace I p) (hu : u ≠ 0) {a b : ℝ} (hab : a < b)
    (heq : GExp (cov := cov) hmet p (a • u) = GExp (cov := cov) hmet p (b • u)) :
    ∃ Q : ℝ, 0 < Q ∧ Q ≤ |b - a| ∧ ∀ s : ℝ,
      GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u) := by
  classical
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • u) with hγdef
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ Set.univ := by
    rw [hγdef]
    exact Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hu
  have hγgeo : ∀ t : ℝ, IsGeodesicAt cov γ t := by
    intro t
    rw [hγdef]
    exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hu t
  have hγne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0 := by
    intro t
    rw [hγdef]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hu t
  have hγspeed : ∀ t : ℝ, ‖curveVelocity (I := I) γ t‖ = ‖u‖ := by
    intro t
    rw [hγdef]
    have h := Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hu t
    rwa [Submission.GeodesicSpeed.curveSpeed_eq_norm] at h
  have hγmd : ∀ t : ℝ, MDifferentiableAt 𝓘(ℝ) I γ t := fun t =>
    (hγsm.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
  have hpt : γ a = γ b := by
    rw [hγdef]
    exact heq
  -- ## affine reparametrisations of `γ`
  have reparam_sm : ∀ (c d R : ℝ), 0 < R →
      ContMDiffOn 𝓘(ℝ) I ∞ (fun x : ℝ => γ (c * x + d)) (Ioo (-R) R) := by
    intro c d R hR
    have hf : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => c * x + d) (Ioo (-R) R) :=
      (((contMDiff_const (I := 𝓘(ℝ, ℝ)) (c := c)).mul contMDiff_id).add
        (contMDiff_const (I := 𝓘(ℝ, ℝ)) (c := d))).contMDiffOn
    exact hγsm.comp hf (fun x _ => Set.mem_univ _)
  have reparam_geo : ∀ (c d : ℝ), c ≠ 0 → ∀ (R : ℝ), 0 < R →
      ∀ x ∈ Ioo (-R) R, IsGeodesicAt cov (fun y : ℝ => γ (c * y + d)) x := by
    intro c d hc R hR x hx
    have hxabs : |x| < R := abs_lt.mpr hx
    have hcnn : 0 < |c| := abs_pos.mpr hc
    refine Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := c) (b := d)
      (c := -(R * |c| + |d| + 1)) (d := R * |c| + |d| + 1) hc
      (hγsm.mono (fun _ _ => Set.mem_univ _)) (fun y _ => hγgeo y) (r := x) ?_
    have h1 : |c * x + d| < R * |c| + |d| + 1 := by
      calc |c * x + d| ≤ |c * x| + |d| := abs_add_le _ _
        _ = |c| * |x| + |d| := by rw [abs_mul]
        _ < |c| * R + |d| := by
            have := mul_lt_mul_of_pos_left hxabs hcnn
            linarith
        _ = R * |c| + |d| := by rw [mul_comm]
        _ < R * |c| + |d| + 1 := by linarith
    exact Set.mem_Ioo.mpr (abs_lt.mp h1)
  have reparam_ne : ∀ (c d : ℝ), c ≠ 0 → ∀ t : ℝ,
      curveVelocity (I := I) (fun y : ℝ => γ (c * y + d)) t ≠ 0 := by
    intro c d hc t hzero
    have hv : c • curveVelocity (I := I) γ (c * t + d) = 0 := by
      rw [← Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := c) (d := d)
        (t := t) (hγmd (c * t + d))]
      exact hzero
    have hv' : curveVelocity (I := I) γ (c * t + d) = 0 := by
      have h1 : c⁻¹ • (c • curveVelocity (I := I) γ (c * t + d))
          = curveVelocity (I := I) γ (c * t + d) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [← h1, hv, smul_zero]
    exact hγne (c * t + d) hv'
  -- ## the sign analysis, in the fibre of `γ b`
  haveI : FiniteDimensional ℝ (TangentSpace I (γ b)) := inferInstanceAs (FiniteDimensional ℝ E)
  have hfr : Module.finrank ℝ (TangentSpace I (γ b)) = 1 := by
    rw [show Module.finrank ℝ (TangentSpace I (γ b)) = Module.finrank ℝ E from rfl]
    exact hdim
  -- the direction at `a`, transported into the fibre at `γ b`
  set Va : TangentSpace I (γ b) := (hpt ▸ curveVelocity (I := I) γ a : TangentSpace I (γ b))
    with hVadef
  have hVanorm : ‖Va‖ = ‖u‖ := by
    rw [hVadef]
    exact (norm_transport (h := hpt) (v := curveVelocity (I := I) γ a)).trans (hγspeed a)
  have hVane : Va ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hVanorm
    exact (norm_ne_zero_iff.mpr hu) hVanorm.symm
  obtain ⟨c, hc⟩ : ∃ c : ℝ, curveVelocity (I := I) γ b = c • Va :=
    exists_smul_eq_of_finrank_eq_one_ray hfr hVane _
  have hcnorm : |c| = 1 := by
    have h1 : |c| * ‖u‖ = ‖u‖ := by
      calc |c| * ‖u‖ = |c| * ‖Va‖ := by rw [hVanorm]
        _ = ‖c • Va‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = ‖curveVelocity (I := I) γ b‖ := by rw [← hc]
        _ = ‖u‖ := hγspeed b
    have h1' : |c| * ‖u‖ = 1 * ‖u‖ := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hu) h1'
  have hcases : c = 1 ∨ c = -1 := by
    have h2 : c ^ 2 = 1 := by
      rw [← sq_abs, hcnorm]
      norm_num
    exact sq_eq_one_iff.mp h2
  rcases hcases with hc1 | hcm1
  · -- ## case `γ'(b) = γ'(a)`: `b - a` is a period
    have hvel_eq : curveVelocity (I := I) γ b = curveVelocity (I := I) γ a := by
      have h1 : curveVelocity (I := I) γ b = Va := by simpa [hc1] using hc
      rw [h1, hVadef]
      exact transport_self hpt (curveVelocity (I := I) γ a)
    have hper : ∀ s : ℝ, γ (s + (b - a)) = γ s := by
      intro s
      set R : ℝ := |s - a| + (b - a) + 1 with hRdef
      have hRpos : 0 < R := by
        rw [hRdef]
        have := abs_nonneg (s - a)
        linarith
      have hEqOn : EqOn (fun x : ℝ => γ (1 * x + b)) (fun x : ℝ => γ (1 * x + a))
          (Ioo (-R) R) := by
        refine eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := -R) (b := R)
          (reparam_sm 1 b R hRpos) (reparam_sm 1 a R hRpos)
          (reparam_geo 1 b one_ne_zero R hRpos) (reparam_geo 1 a one_ne_zero R hRpos)
          (fun x _ => reparam_ne 1 b one_ne_zero x) (fun x _ => reparam_ne 1 a one_ne_zero x)
          (t₀ := 0) ⟨by linarith, hRpos⟩ ?_ ?_
        · show γ (1 * 0 + b) = γ (1 * 0 + a)
          rw [show (1 : ℝ) * 0 + b = b by ring, show (1 : ℝ) * 0 + a = a by ring]
          exact hpt.symm
        · show curveVelocity (I := I) (fun x : ℝ => γ (1 * x + b)) 0
              = curveVelocity (I := I) (fun x : ℝ => γ (1 * x + a)) 0
          rw [Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := b)
                (t := 0) (hγmd (1 * 0 + b)),
              Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := a)
                (t := 0) (hγmd (1 * 0 + a))]
          rw [show (1 : ℝ) * 0 + b = b by ring, show (1 : ℝ) * 0 + a = a by ring]
          rw [one_smul, one_smul]
          exact hvel_eq
      have hmem : s - a ∈ Ioo (-R) R := by
        refine ⟨?_, ?_⟩
        · rw [hRdef]
          have := neg_le_abs (s - a)
          linarith
        · rw [hRdef]
          have := le_abs_self (s - a)
          linarith
      have hres : γ (1 * (s - a) + b) = γ (1 * (s - a) + a) := hEqOn hmem
      rw [show (1 : ℝ) * (s - a) + b = s + (b - a) by ring,
        show (1 : ℝ) * (s - a) + a = s by ring] at hres
      exact hres
    refine ⟨b - a, by linarith, ?_, fun s => ?_⟩
    · rw [abs_of_pos (by linarith : (0 : ℝ) < b - a)]
    · simpa [hγdef] using hper s
  · -- ## case `γ'(b) = -γ'(a)`: impossible
    exfalso
    have hvel_neg : curveVelocity (I := I) γ b = -curveVelocity (I := I) γ a := by
      have h1 : curveVelocity (I := I) γ b = -Va := by simpa [hcm1] using hc
      rw [h1, hVadef]
      exact congrArg Neg.neg (transport_self hpt (curveVelocity (I := I) γ a))
    set R : ℝ := (b - a) + 1 with hRdef
    have hRpos : 0 < R := by rw [hRdef]; linarith
    have hEqOn : EqOn (fun x : ℝ => γ ((-1) * x + b)) (fun x : ℝ => γ (1 * x + a))
        (Ioo (-R) R) := by
      refine eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := -R) (b := R)
        (reparam_sm (-1) b R hRpos) (reparam_sm 1 a R hRpos)
        (reparam_geo (-1) b (by norm_num) R hRpos) (reparam_geo 1 a one_ne_zero R hRpos)
        (fun x _ => reparam_ne (-1) b (by norm_num) x) (fun x _ => reparam_ne 1 a one_ne_zero x)
        (t₀ := 0) ⟨by linarith, hRpos⟩ ?_ ?_
      · show γ ((-1) * 0 + b) = γ (1 * 0 + a)
        rw [show (-1 : ℝ) * 0 + b = b by ring, show (1 : ℝ) * 0 + a = a by ring]
        exact hpt.symm
      · show curveVelocity (I := I) (fun x : ℝ => γ ((-1) * x + b)) 0
            = curveVelocity (I := I) (fun x : ℝ => γ (1 * x + a)) 0
        rw [Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -1) (d := b)
              (t := 0) (hγmd ((-1) * 0 + b)),
            Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := a)
              (t := 0) (hγmd (1 * 0 + a))]
        rw [show (-1 : ℝ) * 0 + b = b by ring, show (1 : ℝ) * 0 + a = a by ring]
        rw [neg_one_smul, one_smul]
        exact (congrArg Neg.neg hvel_neg).trans (neg_neg _)
    set t₀ : ℝ := (b - a) / 2 with ht₀def
    have ht₀mem : t₀ ∈ Ioo (-R) R := by
      refine ⟨?_, ?_⟩
      · rw [ht₀def, hRdef]
        have := le_abs_self (b - a)
        linarith
      · rw [ht₀def, hRdef]
        have := le_abs_self (b - a)
        linarith
    have hev : (fun x : ℝ => γ ((-1) * x + b)) =ᶠ[𝓝 t₀]
        (fun x : ℝ => γ (1 * x + a)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht₀mem) (fun x hx => hEqOn hx)
    have hv : curveVelocity (I := I) (fun x : ℝ => γ ((-1) * x + b)) t₀
        = curveVelocity (I := I) (fun x : ℝ => γ (1 * x + a)) t₀ :=
      Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev
    rw [Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -1) (d := b)
          (t := t₀) (hγmd ((-1) * t₀ + b)),
        Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := a)
          (t := t₀) (hγmd (1 * t₀ + a))] at hv
    rw [show (1 : ℝ) * t₀ + a = (-1) * t₀ + b by rw [ht₀def]; ring] at hv
    rw [neg_one_smul, one_smul] at hv
    refine hγne ((-1) * t₀ + b) ?_
    have hv' : curveVelocity (I := I) γ ((-1) * t₀ + b)
        = -curveVelocity (I := I) γ ((-1) * t₀ + b) := hv.symm
    have h3 : (2 : ℝ) • curveVelocity (I := I) γ ((-1) * t₀ + b) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hv'
    have h4 : (2 : ℝ)⁻¹ • ((2 : ℝ) • curveVelocity (I := I) γ ((-1) * t₀ + b)) = 0 :=
      (congrArg (fun w => (2 : ℝ)⁻¹ • w) h3).trans (smul_zero _)
    have hsm : (2 : ℝ)⁻¹ • ((2 : ℝ) • curveVelocity (I := I) γ ((-1) * t₀ + b))
        = ((2 : ℝ)⁻¹ * 2) • curveVelocity (I := I) γ ((-1) * t₀ + b) :=
      smul_smul (2 : ℝ)⁻¹ (2 : ℝ) _
    have hone : ((2 : ℝ)⁻¹ * 2) • curveVelocity (I := I) γ ((-1) * t₀ + b)
        = curveVelocity (I := I) γ ((-1) * t₀ + b) := by
      rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
    calc curveVelocity (I := I) γ ((-1) * t₀ + b)
        = ((2 : ℝ)⁻¹ * 2) • curveVelocity (I := I) γ ((-1) * t₀ + b) := hone.symm
      _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • curveVelocity (I := I) γ ((-1) * t₀ + b)) := hsm.symm
      _ = 0 := h4

theorem period_of_GExp_ray_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (hdim : Module.finrank ℝ E = 1)
    (p : M) (u : TangentSpace I p) (hu : u ≠ 0) {a b : ℝ} (hab : a ≠ b)
    (heq : GExp (cov := cov) hmet p (a • u) = GExp (cov := cov) hmet p (b • u)) :
    ∃ Q : ℝ, 0 < Q ∧ Q ≤ |b - a| ∧ ∀ s : ℝ,
      GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact period_lt (cov := cov) hmet hdim p u hu hlt heq
  · obtain ⟨Q, hQpos, hQle, hQper⟩ :=
      period_lt (cov := cov) hmet hdim p u hu (a := b) (b := a) hgt heq.symm
    exact ⟨Q, hQpos, by rwa [abs_sub_comm] at hQle, hQper⟩

end Work.Final.DimOne
