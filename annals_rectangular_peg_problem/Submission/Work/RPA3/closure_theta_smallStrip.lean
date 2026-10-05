import Mathlib
import Submission.Work.RPA3.TubularHDefs

/-!
# RPA3: the closure of the small tubular strip lies in the witness set

The tubular map `θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)` maps the strip of transverse radius
`ε/2` into the set of points with a witness of radius `ε` (`HasWitness`).  Here we show that the
*closure* of this image is still contained in the witness set:

`closure {θ(τ,x,t,ξ) | ‖ξ‖ < ε/2} ⊆ {y | HasWitness L T τ y}`.

Two mechanisms could a priori make the closure bigger: the transverse coordinate may reach the
value `ε/2` (harmless, since `ε/2 < ε`), and the `x`-coordinate may run off to infinity.  The
explicit choice of the radius `ε/2` (rather than `ε`) is what keeps the strip away from the
"boundary" `‖ξ‖ = ε` of the witness tube over the compact part of the family, and the far part is
handled by `theta_std`.

The proof decomposes the strip into two blocks.

* The **near** block `|x| ≤ X₀+1`.  There the configuration `(x, t mod 2π, ξ)` runs over a compact
  set, and the freedom in the angle is exactly the action of the integral shifts `Tk k` on the
  image (`theta_per_int`).  The projection `angleProj` of the phase space onto
  `(ℝ × ℝ/2πℤ) × ℝ²` collapses those shifts, so the image of the compact block under
  `angleProj ∘ θ` is compact, hence closed; its preimage is a closed set containing the near block,
  and every point of that preimage is a `Tk`-shift of a point of the block, hence has a witness
  (`HasWitness_Tk`).

* The **far** block `|x| > X₀+1`.  There `θ(τ,x,t,ξ) = ((x,t),(-ξ₁,-ξ₂))` (`theta_std`), so its
  closure lies in the closed set `{|q₁| ≥ X₀, ‖p‖ ≤ ε/2}`, and every point of that set has a
  witness (`HasWitness_std`).
-/

open scoped Topology
open Set

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-! ## The angle projection `PS → (ℝ × ℝ/2πℤ) × ℝ²` -/

/-- The projection of `PS` to "angle modulo `2π`": it remembers `q₁ = x` as a real number, the
angle `q₂` only as its class in `ℝ/2πℤ`, and the momenta `(p₁,p₂)`.  It is exactly the map that
identifies the points differing by an integral shift `Tk k` of the angle. -/
def angleProj (z : PS) : (ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ) :=
  ((z.1.1, (z.1.2 : AddCircle (2 * Real.pi))), z.2)

theorem continuous_angleProj : Continuous angleProj := by
  unfold angleProj
  fun_prop

/-- Shifting the angle by an integral multiple of `2π` does not change the class in `ℝ/2πℤ`. -/
theorem coe_add_two_pi_mul (t : ℝ) (k : ℤ) :
    ((t + 2 * Real.pi * (k : ℝ) : ℝ) : AddCircle (2 * Real.pi)) =
      (t : AddCircle (2 * Real.pi)) := by
  have harg : t + 2 * Real.pi * (k : ℝ) = t + k • (2 * Real.pi) := by
    rw [zsmul_eq_mul]; ring
  rw [harg, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]

/-- Two reals with the same class in `ℝ/2πℤ` differ by an integral multiple of `2π`. -/
theorem exists_int_of_angle_eq {a b : ℝ}
    (h : (a : AddCircle (2 * Real.pi)) = (b : AddCircle (2 * Real.pi))) :
    ∃ k : ℤ, a = b + 2 * Real.pi * (k : ℝ) := by
  rw [QuotientAddGroup.eq_iff_sub_mem] at h
  rw [AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [zsmul_eq_mul] at hk
  have h2 : 2 * Real.pi * (k : ℝ) = ↑k * (2 * Real.pi) := by ring
  rw [h2, hk]
  ring

/-- `angleProj` is invariant under the integral shifts of the angle. -/
theorem angleProj_Tk (k : ℤ) (z : PS) : angleProj (Tk k z) = angleProj z := by
  simp only [angleProj, Tk]
  rw [coe_add_two_pi_mul]

/-! ## The closure of the strip -/

set_option linter.unusedVariables false in
/-- **The closure of the small strip is contained in the set of points with a witness.**  Any
`z` in the closure of `{θ(τ,x,t,ξ) | ‖ξ‖ < ε/2}` is of the form `θ(τ,x,t,ξ)` with `‖ξ‖ < ε`.

The hypothesis `τ ∈ [-1,2]` is not needed: the argument uses only the periodicity of `θ` in the
angle (`theta_per_int`), the compactness of the block `|x| ≤ X₀+1`, `t ∈ [0,2π]`, `‖ξ‖ ≤ ε/2`, and
the explicit form of `θ` in the standard region (`theta_std`). -/
theorem closure_theta_smallStrip (L : Work.RPA3.LagFamilyAll) (T : Work.RPA3.TubularData L)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) :
    closure {z : Work.RPA3.PS | ∃ w : Work.RPA3.PS, ‖w.2‖ < T.ε / 2 ∧
        Work.RPA3.theta L τ w.1.1 w.1.2 w.2 = z}
      ⊆ {z : Work.RPA3.PS | Work.RPA3.HasWitness L T τ z} := by
  -- the strip, split according to whether `|x|` stays below `X₀ + 1`
  set S : Set PS :=
    {z : PS | ∃ w : PS, ‖w.2‖ < T.ε / 2 ∧ theta L τ w.1.1 w.1.2 w.2 = z} with hS
  set S₁ : Set PS :=
    {z : PS | ∃ w : PS, |w.1.1| ≤ L.X0 + 1 ∧ ‖w.2‖ < T.ε / 2 ∧
      theta L τ w.1.1 w.1.2 w.2 = z} with hS₁
  set S₂ : Set PS :=
    {z : PS | ∃ w : PS, L.X0 + 1 < |w.1.1| ∧ ‖w.2‖ < T.ε / 2 ∧
      theta L τ w.1.1 w.1.2 w.2 = z} with hS₂
  have hdecomp : S = S₁ ∪ S₂ := by
    rw [hS, hS₁, hS₂]
    ext z
    constructor
    · rintro ⟨w, hξ, hθ⟩
      by_cases h : |w.1.1| ≤ L.X0 + 1
      · exact Or.inl ⟨w, h, hξ, hθ⟩
      · exact Or.inr ⟨w, not_le.mp h, hξ, hθ⟩
    · rintro (⟨w, -, hξ, hθ⟩ | ⟨w, -, hξ, hθ⟩)
      · exact ⟨w, hξ, hθ⟩
      · exact ⟨w, hξ, hθ⟩
  rw [hdecomp, closure_union]
  refine union_subset ?_ ?_
  · -- ### The near block `|x| ≤ X₀ + 1`
    -- `θ` is continuous in the point variable at fixed `τ`
    have hθcont : Continuous (fun w : PS => theta L τ w.1.1 w.1.2 w.2) := by
      have h : Continuous (fun w : ℝ × PS => thetaZ L w.1 w.2) := continuous_thetaZ L
      have h2 : Continuous (fun z : PS => thetaZ L τ z) :=
        h.comp (continuous_const.prodMk continuous_id)
      simpa [thetaZ] using h2
    -- the compact block of configurations in the strip
    set C : Set PS := (Set.Icc (-(L.X0 + 1)) (L.X0 + 1) ×ˢ Set.Icc 0 (2 * Real.pi)) ×ˢ
      Metric.closedBall (0 : ℝ × ℝ) (T.ε / 2) with hC
    have hCcompact : IsCompact C := by
      rw [hC]
      exact (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
    -- its image in the angle-modulo-`2π` space
    set A : Set ((ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ)) :=
      angleProj '' ((fun w : PS => theta L τ w.1.1 w.1.2 w.2) '' C) with hA
    have hAclosed : IsClosed A := by
      rw [hA]
      exact ((hCcompact.image hθcont).image continuous_angleProj).isClosed
    have hcl : IsClosed (angleProj ⁻¹' A) := hAclosed.preimage continuous_angleProj
    -- every point of the near block lies in the preimage
    have hsub : S₁ ⊆ angleProj ⁻¹' A := by
      rintro z ⟨w, hx, hξ, hθ⟩
      obtain ⟨t', ht', k, htk⟩ := exists_shift_two_pi_Ico w.1.2
      have hmem : ((w.1.1, t'), w.2) ∈ C := by
        rw [hC]
        refine ⟨⟨?_, Set.Ico_subset_Icc_self ht'⟩, ?_⟩
        · rw [Set.mem_Icc]; exact abs_le.mp hx
        · rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hξ
      have hz : z = Tk k (theta L τ w.1.1 t' w.2) := by
        rw [← hθ, htk]
        exact theta_per_int L τ w.1.1 t' w.2 k
      rw [hz]
      change angleProj (Tk k (theta L τ w.1.1 t' w.2)) ∈ A
      rw [angleProj_Tk, hA]
      exact ⟨theta L τ w.1.1 t' w.2, ⟨((w.1.1, t'), w.2), hmem, rfl⟩, rfl⟩
    refine subset_trans (closure_mono hsub) ?_
    rw [hcl.closure_eq]
    -- every point of the preimage is a `Tk`-shift of a point of the block, hence has a witness
    intro y hy
    obtain ⟨p, hp, hpeq⟩ := hy
    obtain ⟨c, hc, hceq⟩ := hp
    rw [← hceq] at hpeq
    have hq1 : (theta L τ c.1.1 c.1.2 c.2).1.1 = y.1.1 := by
      simpa [angleProj] using congrArg (fun q => q.1.1) hpeq
    have hang : ((theta L τ c.1.1 c.1.2 c.2).1.2 : AddCircle (2 * Real.pi)) =
        (y.1.2 : AddCircle (2 * Real.pi)) := by
      simpa [angleProj] using congrArg (fun q => q.1.2) hpeq
    have hq2 : (theta L τ c.1.1 c.1.2 c.2).2 = y.2 := by
      simpa [angleProj] using congrArg (fun q => q.2) hpeq
    obtain ⟨k, hk⟩ := exists_int_of_angle_eq hang
    have hξε : ‖c.2‖ < T.ε := by
      have h1 : ‖c.2‖ ≤ T.ε / 2 := by
        rw [hC] at hc
        have h2 : dist c.2 0 ≤ T.ε / 2 := Metric.mem_closedBall.mp hc.2
        rwa [dist_zero_right] at h2
      linarith [T.εpos]
    have hTk : Tk k y = theta L τ c.1.1 c.1.2 c.2 := by
      have h4 : ((y.1.1, y.1.2 + 2 * Real.pi * (k : ℝ)), y.2)
          = theta L τ c.1.1 c.1.2 c.2 :=
        Prod.ext (Prod.ext hq1.symm hk.symm) hq2.symm
      simpa [Tk] using h4
    exact HasWitness_Tk L T τ k y ⟨c, hξε, hTk.symm⟩
  · -- ### The far block `|x| > X₀ + 1`
    -- there `θ` is the explicit map `((x,t),(-ξ₁,-ξ₂))`
    have hsub₂ : S₂ ⊆ {z : PS | L.X0 ≤ |z.1.1| ∧ ‖z.2‖ ≤ T.ε / 2} := by
      rintro z ⟨w, hx, hξ, hθ⟩
      have hxX0 : L.X0 ≤ |w.1.1| := by linarith
      have hz : z = ((w.1.1, w.1.2), (-w.2.1, -w.2.2)) := by
        rw [← hθ, theta_std L τ w.1.1 w.1.2 w.2 hxX0]
      constructor
      · rw [hz]; simpa using hxX0
      · rw [hz]
        have h2 : ‖(-w.2.1, -w.2.2)‖ = ‖w.2‖ := by
          rw [Prod.norm_def, Prod.norm_def, norm_neg, norm_neg]
        rw [h2]
        exact le_of_lt hξ
    have hclosed : IsClosed {z : PS | L.X0 ≤ |z.1.1| ∧ ‖z.2‖ ≤ T.ε / 2} := by
      have h1 : IsClosed {z : PS | L.X0 ≤ |z.1.1|} :=
        isClosed_le continuous_const (by fun_prop : Continuous (fun z : PS => |z.1.1|))
      have h2 : IsClosed {z : PS | ‖z.2‖ ≤ T.ε / 2} :=
        isClosed_le (by fun_prop : Continuous (fun z : PS => ‖z.2‖)) continuous_const
      rw [Set.ofPred_and]
      exact h1.inter h2
    refine subset_trans (closure_mono hsub₂) ?_
    rw [hclosed.closure_eq]
    rintro z ⟨hz1, hz2⟩
    have hξ : ‖(-z.2.1, -z.2.2)‖ < T.ε := by
      have h2 : ‖(-z.2.1, -z.2.2)‖ = ‖z.2‖ := by
        rw [Prod.norm_def, Prod.norm_def, norm_neg, norm_neg]
      rw [h2]
      linarith [T.εpos]
    have hwit := HasWitness_std L T τ z.1.1 z.1.2 (-z.2.1, -z.2.2) hz1 hξ
    simpa using hwit

end Work.RPA3
