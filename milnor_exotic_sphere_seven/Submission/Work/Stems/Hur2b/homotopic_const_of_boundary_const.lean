import Mathlib
import Submission.Work.Stems.exists_collapsingMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Boundary-slice-constant homotopy with constant end slice implies based null-homotopy

If a generalized loop `p : Ω^(Fin n) X x₀` (a continuous map `Iⁿ → X` sending `∂Iⁿ` to `x₀`) admits
a homotopy `H : Iⁿ × I → X` from `p` to the constant map `x₀` which is *constant on the boundary
slice* `∂Iⁿ × {t}` for every `t`, then `p` is homotopic to `GenLoop.const` *relative to* `∂Iⁿ`.

In other words: a *free* null-homotopy of the underlying sphere map `Iⁿ/∂Iⁿ → X` (with the base
point track being a loop, which is automatic here) forces `p` to be null-homotopic as a based map.
This is Lemma 2.2(a) of Hutchings' cubical proof of the Hurewicz theorem.

## Proof

The boundary condition `hb` and the collapse `φ : Iⁿ → Iⁿ/∂Iⁿ ≅ Sⁿ`
(`Work.Stems.exists_collapsingMap`) say that `H` is constant on the fibres of the "cone map"
`c : Iⁿ × I → D^{n+1}`, `c(y,t) = (1-t) • φ y`, onto the closed unit ball `D^{n+1}` of
`EuclideanSpace ℝ (Fin (n+1))`; since `Iⁿ × I` is compact and the ball is Hausdorff, `c` is a
quotient map and `H` descends to a continuous `G : D^{n+1} → X`.

Then the straight-line homotopy `(y,s) ↦ (1-s) • φ y + s • φ 0` in the (convex) ball, pushed
forward by `G`, is the desired based homotopy: at `s = 0` it is `p`, at `s = 1` it is `G(φ 0) = x₀`,
and for `y ∈ ∂Iⁿ` we have `φ y = φ 0`, so the whole segment is the constant `φ 0`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

theorem homotopic_const_of_boundary_const {X : Type} [TopologicalSpace X] (n : ℕ) [NeZero n]
    {x₀ : X} (p : GenLoop (Fin n) X x₀) (z : X)
    (H : ContinuousMap ((Fin n → unitInterval) × unitInterval) X)
    (h0 : ∀ y, H (y, 0) = p.1 y) (h1 : ∀ y, H (y, 1) = z)
    (hb : ∀ (y y' : Fin n → unitInterval) (t : unitInterval), y ∈ Cube.boundary (Fin n) →
      y' ∈ Cube.boundary (Fin n) → H (y, t) = H (y', t)) :
    GenLoop.Homotopic p GenLoop.const := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  obtain ⟨φ, hφq, hφbd, hφinj⟩ := Work.Stems.exists_collapsingMap n hn
  have hφnorm : ∀ y : Fin n → unitInterval, ‖(φ y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    intro y
    have h := Metric.mem_sphere.mp (φ y).2
    rw [dist_eq_norm, sub_zero] at h
    exact h
  have h0mem : (0 : Fin n → unitInterval) ∈ Cube.boundary (Fin n) :=
    Work.Stems.zero_mem_cubeBoundary n hn
  have hφ0 : ∀ y ∈ Cube.boundary (Fin n),
      (φ y : EuclideanSpace ℝ (Fin (n+1))) = (φ 0 : EuclideanSpace ℝ (Fin (n+1))) :=
    fun y hy => congrArg Subtype.val (hφbd y hy)
  -- The pole of the cone map, and its norm bound
  have hcnorm : ∀ z : (Fin n → unitInterval) × unitInterval,
      ‖(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    intro z
    have h1' : ‖((1 - (z.2:ℝ)) : ℝ)‖ = 1 - (z.2:ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [z.2.2.1, z.2.2.2])]
    rw [norm_smul, h1', hφnorm z.1, mul_one]
    linarith [z.2.2.1, z.2.2.2]
  -- The cone map `c : Iⁿ × I → D^{n+1}`, `(y,t) ↦ (1-t) • φ y`
  let c : C((Fin n → unitInterval) × unitInterval,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨fun z => ⟨(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1))),
        Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hcnorm z)⟩, by fun_prop⟩
  have hc_val : ∀ z, ((c z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :
      EuclideanSpace ℝ (Fin (n+1))) = (1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n+1))) :=
    fun z => rfl
  -- `H` is constant on the fibres of `c`
  have hfac : Function.FactorsThrough H c := by
    intro a b hab
    have hval : (1 - (a.2 : ℝ)) • (φ a.1 : EuclideanSpace ℝ (Fin (n+1)))
        = (1 - (b.2 : ℝ)) • (φ b.1 : EuclideanSpace ℝ (Fin (n+1))) := by
      have h := congrArg (fun q : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (q : EuclideanSpace ℝ (Fin (n+1)))) hab
      rw [hc_val a, hc_val b] at h
      exact h
    -- the radial parameter is determined by the image
    have hnorm_eq : (1 - (a.2 : ℝ)) = (1 - (b.2 : ℝ)) := by
      have h := congrArg norm hval
      rw [norm_smul, norm_smul, hφnorm a.1, hφnorm b.1, mul_one, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [a.2.2.1, a.2.2.2]),
        abs_of_nonneg (by linarith [b.2.2.1, b.2.2.2])] at h
      exact h
    have ht_eq : a.2 = b.2 := Subtype.ext (by linarith [hnorm_eq])
    by_cases ha1 : a.2 = 1
    · -- on the top slice `H` is the constant `x₀`
      have hb1 : b.2 = 1 := by rw [← ht_eq]; exact ha1
      have ha' : H a = z := by
        change H (a.1, a.2) = z
        rw [ha1]; exact h1 a.1
      have hb' : H b = z := by
        change H (b.1, b.2) = z
        rw [hb1]; exact h1 b.1
      rw [ha', hb']
    · -- off the top slice, the sphere coordinate is determined
      have htne : (a.2 : ℝ) ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hne : (1:ℝ) - (a.2:ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm htne)
      have hφeq : φ a.1 = φ b.1 := by
        apply Subtype.ext
        have h := hval
        rw [← hnorm_eq] at h
        have h2 := congrArg (fun w => ((1 - (a.2:ℝ))⁻¹) • w) h
        simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using h2
      rcases hφinj a.1 b.1 hφeq with h1'' | ⟨ha1bd, hb1bd⟩
      · change H (a.1, a.2) = H (b.1, b.2)
        rw [h1'', ht_eq]
      · change H (a.1, a.2) = H (b.1, b.2)
        have hh := hb a.1 b.1 a.2 ha1bd hb1bd
        rw [hh, ht_eq]
  -- surjectivity of the cone map onto the ball
  have hcsurj : Function.Surjective c := by
    rintro ⟨u, hu⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
    by_cases hu0 : u = 0
    · refine ⟨((0 : Fin n → unitInterval), (1 : unitInterval)), ?_⟩
      apply Subtype.ext
      show (1 - ((1 : unitInterval) : ℝ)) • (φ (0 : Fin n → unitInterval) :
        EuclideanSpace ℝ (Fin (n+1))) = u
      rw [hu0]; norm_num
    · have hnormu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
      let ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := ⟨‖u‖⁻¹ • u, by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg u), inv_mul_cancel₀ hnormu]⟩
      obtain ⟨y, hy⟩ := hφq.surjective ω
      have htmem : (0:ℝ) ≤ 1 - ‖u‖ ∧ 1 - ‖u‖ ≤ 1 :=
        ⟨by linarith [norm_nonneg u, hu], by linarith [norm_nonneg u, hu]⟩
      let t : unitInterval := ⟨1 - ‖u‖, htmem⟩
      refine ⟨(y, t), ?_⟩
      apply Subtype.ext
      have ht : (t : ℝ) = 1 - ‖u‖ := rfl
      show (1 - (t : ℝ)) • (φ y : EuclideanSpace ℝ (Fin (n+1))) = u
      have hs : (1:ℝ) - (1 - ‖u‖) = ‖u‖ := by ring
      rw [ht, hs]
      have hφy : (φ y : EuclideanSpace ℝ (Fin (n+1))) = (ω : EuclideanSpace ℝ (Fin (n+1))) :=
        congrArg Subtype.val hy
      rw [hφy]
      show ‖u‖ • (‖u‖⁻¹ • u) = u
      rw [smul_inv_smul₀ hnormu u]
  have hcclosed : IsClosedMap c := fun s hs => (hs.isCompact.image c.continuous).isClosed
  have hcq : Topology.IsQuotientMap c := hcclosed.isQuotientMap c.continuous hcsurj
  -- the descent of `H` to the ball
  let F : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1, X) := hcq.lift H hfac
  have hF : ∀ z, F (c z) = H z := by
    intro z
    have h := Topology.IsQuotientMap.lift_comp hcq H hfac
    exact congrFun (congrArg (fun f : C((Fin n → unitInterval) × unitInterval, X) => ⇑f) h) z
  -- the straight-line homotopy towards the base point `φ 0` of the sphere
  have hSLnorm : ∀ z : (Fin n → unitInterval) × unitInterval,
      ‖(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1)))
        + (z.2 : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    intro z
    have h1' : ‖(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1)))‖
        = 1 - (z.2 : ℝ) := by
      rw [norm_smul, hφnorm z.1, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [z.2.2.1, z.2.2.2])]
    have h2' : ‖(z.2 : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n + 1)))‖ = (z.2 : ℝ) := by
      rw [norm_smul, hφnorm 0, mul_one, Real.norm_eq_abs, abs_of_nonneg z.2.2.1]
    calc ‖(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1)))
          + (z.2 : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n + 1)))‖
        ≤ ‖(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1)))‖
          + ‖(z.2 : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n + 1)))‖ := norm_add_le _ _
      _ = 1 := by rw [h1', h2']; ring
  let SL : C((Fin n → unitInterval) × unitInterval,
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨fun z => ⟨(1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n + 1)))
        + (z.2 : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n + 1))),
        Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hSLnorm z)⟩, by fun_prop⟩
  have hSL_val : ∀ z, ((SL z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :
      EuclideanSpace ℝ (Fin (n+1))) = (1 - (z.2 : ℝ)) • (φ z.1 : EuclideanSpace ℝ (Fin (n+1)))
        + (z.2 : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n+1))) := fun z => rfl
  let K : C((Fin n → unitInterval) × unitInterval, X) := F.comp SL
  have hK : ∀ z, K z = F (SL z) := fun z => rfl
  have hSL0 : ∀ y, SL (y, 0) = c (y, 0) := by
    intro y
    apply Subtype.ext
    rw [hSL_val, hc_val]
    simp
  have hSL1 : ∀ y, SL (y, 1) = c (0, 0) := by
    intro y
    apply Subtype.ext
    rw [hSL_val, hc_val]
    simp
  have hSLbd : ∀ (y : Fin n → unitInterval), y ∈ Cube.boundary (Fin n) → ∀ t : unitInterval,
      SL (y, t) = c (0, 0) := by
    intro y hy t
    apply Subtype.ext
    show (1 - (t : ℝ)) • (φ y : EuclideanSpace ℝ (Fin (n+1)))
      + (t : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n+1)))
      = (1 - (0 : unitInterval) : ℝ) • (φ 0 : EuclideanSpace ℝ (Fin (n+1)))
    rw [hφ0 y hy, ← add_smul]
    have hsum : ((1:ℝ) - (t:ℝ)) + (t:ℝ) = 1 := by ring
    rw [hsum]
    simp
  -- assemble the based homotopy
  refine ⟨⟨⟨fun z : unitInterval × (Fin n → unitInterval) => K (z.2, z.1), ?_⟩, ?_, ?_⟩, ?_⟩
  · fun_prop
  · intro y
    show K (y, 0) = p.1 y
    rw [hK, hSL0 y, hF (y, 0)]
    exact h0 y
  · intro y
    show K (y, 1) = x₀
    rw [hK, hSL1 y, hF (0, 0), h0 0]
    exact p.2 0 h0mem
  · intro t y hy
    change K (y, t) = p.1 y
    rw [hK, hSLbd y hy t, hF (0, 0), h0 0]
    exact (p.2 0 h0mem).trans (p.2 y hy).symm

end Work.Stems.Hur2b
