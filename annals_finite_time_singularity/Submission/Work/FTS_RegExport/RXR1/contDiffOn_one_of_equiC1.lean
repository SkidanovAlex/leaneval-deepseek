import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

/-- Mean value bound for a difference quotient: if `φ` is `C¹` on `(0,∞)` and
`|deriv φ w - deriv φ u| ≤ ε` on the whole segment `[u, u+h]` (`h > 0`, `u > 0`), then the
difference quotient of `φ` at `u` with step `h` is within `ε` of `deriv φ u`. -/
theorem sub_deriv_slope_le {φ : ℝ → ℝ} {u h ε : ℝ} (hu : 0 < u) (hh : 0 < h)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi (0:ℝ)))
    (hbound : ∀ w ∈ Set.Icc u (u + h), |deriv φ w - deriv φ u| ≤ ε) :
    |h⁻¹ • (φ (u + h) - φ u) - deriv φ u| ≤ ε := by
  have hsub : (u + h : ℝ) - u = h := by ring
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope φ (show u < u + h by linarith)
    (hφ.continuousOn.mono (fun x hx => lt_of_lt_of_le hu (Set.mem_Icc.mp hx).1))
    ((hφ.differentiableOn_one).mono (fun x hx => lt_trans hu hx.1))
  have hξmem : ξ ∈ Set.Icc u (u + h) := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  rw [hsub] at hξeq
  have hkey : h⁻¹ • (φ (u + h) - φ u) - deriv φ u = deriv φ ξ - deriv φ u := by
    rw [hξeq, smul_eq_mul, div_eq_inv_mul, mul_comm]
  rw [hkey]
  exact hbound ξ hξmem

/-- The limit of the family `f τ` as `τ → 0⁺` is `C¹` on `(0,∞)` whenever the family is
uniformly `C¹` with an equicontinuous derivative (modulus `E`, vanishing on the diagonal) and
the pointwise limit `R` is differentiable. -/
theorem contDiffOn_one_of_equiC1 {f : ℝ → ℝ → ℝ} {R : ℝ → ℝ} {N : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hNcont : ContinuousOn N (Set.Ioi 0))
    (hC1 : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ContDiffOn ℝ 1 (fun z => f τ z) (Set.Ioi 0))
    (hN : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), |deriv (fun z' => f τ z') z| ≤ N z)
    (hEcont : ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)))
    (hEdiag : ∀ z ∈ Set.Ioi (0:ℝ), E z z = 0)
    (hE : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
      |deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z'| ≤ E z z')
    (htend : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun τ => f τ z) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (R z)))
    (hdiff : DifferentiableOn ℝ R (Set.Ioi (0:ℝ))) :
    ContDiffOn ℝ 1 R (Set.Ioi (0:ℝ)) := by
  -- Step 1: the derivative of `R` inherits the modulus of equicontinuity `E`.
  have hmod : ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ), |deriv R z - deriv R z'| ≤ E z z' := by
    intro z hz z' hz'
    have hz0 : (0:ℝ) < z := hz
    have hz'0 : (0:ℝ) < z' := hz'
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε2 : 0 < ε / 2 := by linarith
    -- continuity of the modulus at the diagonal points `(z,z)` and `(z',z')`
    have hcont_z := Metric.continuousWithinAt_iff.mp
      (hEcont.continuousWithinAt (show (z, z) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hz, hz⟩))
    have hcont_z' := Metric.continuousWithinAt_iff.mp
      (hEcont.continuousWithinAt (show (z', z') ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hz', hz'⟩))
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcont_z (ε / 2) hε2
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hcont_z' (ε / 2) hε2
    have hEz : ∀ w ∈ Set.Ioi (0:ℝ), |w - z| < δ₁ → E w z < ε / 2 := by
      intro w hw hwδ
      have hd : dist (w, z) (z, z) < δ₁ := by simpa [Prod.dist_eq, Real.dist_eq] using hwδ
      have h := hδ₁ (x := (w, z)) ⟨hw, hz⟩ hd
      rw [Real.dist_eq, hEdiag z hz, sub_zero] at h
      exact lt_of_le_of_lt (le_abs_self _) h
    have hEz' : ∀ w ∈ Set.Ioi (0:ℝ), |w - z'| < δ₂ → E w z' < ε / 2 := by
      intro w hw hwδ
      have hd : dist (w, z') (z', z') < δ₂ := by simpa [Prod.dist_eq, Real.dist_eq] using hwδ
      have h := hδ₂ (x := (w, z')) ⟨hw, hz'⟩ hd
      rw [Real.dist_eq, hEdiag z' hz', sub_zero] at h
      exact lt_of_le_of_lt (le_abs_self _) h
    have hδpos : 0 < min δ₁ δ₂ := lt_min hδ₁pos hδ₂pos
    have hIoc : Set.Ioc (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1:ℝ) 1, isOpen_Ioo, by norm_num, ?_⟩
      rintro x ⟨hx1, hx2⟩
      exact ⟨show (0:ℝ) < x from hx2, le_of_lt hx1.2⟩
    -- the bound for the difference quotients at a fixed step `h`
    have hkey : ∀ h : ℝ, 0 < h → h < min δ₁ δ₂ →
        |h⁻¹ • (R (z + h) - R z) - h⁻¹ • (R (z' + h) - R z')| ≤ E z z' + ε := by
      intro h hhpos hhδ
      have hzl : z + h ∈ Set.Ioi (0:ℝ) := by show (0:ℝ) < z + h; linarith
      have hz'l : z' + h ∈ Set.Ioi (0:ℝ) := by show (0:ℝ) < z' + h; linarith
      have hQb : ∀ τ ∈ Set.Ioc (0:ℝ) 1,
          |h⁻¹ • (f τ (z + h) - f τ z) - h⁻¹ • (f τ (z' + h) - f τ z')| ≤ E z z' + ε := by
        intro τ hτ
        have hpz : |h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z| ≤ ε / 2 := by
          refine sub_deriv_slope_le hz hhpos (hC1 τ hτ) ?_
          intro w hw
          have hw0 : w ∈ Set.Ioi (0:ℝ) := lt_of_lt_of_le hz (Set.mem_Icc.mp hw).1
          have hwδ : |w - z| < δ₁ := by
            have h1 : w - z ≤ h := by linarith [(Set.mem_Icc.mp hw).2]
            have h2 : 0 ≤ w - z := by linarith [(Set.mem_Icc.mp hw).1]
            rw [abs_of_nonneg h2]
            exact lt_of_le_of_lt h1 (lt_of_lt_of_le hhδ (min_le_left _ _))
          exact le_of_lt (lt_of_le_of_lt (hE τ hτ w hw0 z hz) (hEz w hw0 hwδ))
        have hpz' : |h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z'| ≤ ε / 2 := by
          refine sub_deriv_slope_le hz' hhpos (hC1 τ hτ) ?_
          intro w hw
          have hw0 : w ∈ Set.Ioi (0:ℝ) := lt_of_lt_of_le hz' (Set.mem_Icc.mp hw).1
          have hwδ : |w - z'| < δ₂ := by
            have h1 : w - z' ≤ h := by linarith [(Set.mem_Icc.mp hw).2]
            have h2 : 0 ≤ w - z' := by linarith [(Set.mem_Icc.mp hw).1]
            rw [abs_of_nonneg h2]
            exact lt_of_le_of_lt h1 (lt_of_lt_of_le hhδ (min_le_right _ _))
          exact le_of_lt (lt_of_le_of_lt (hE τ hτ w hw0 z' hz') (hEz' w hw0 hwδ))
        have hdiffτ : |deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z'| ≤ E z z' :=
          hE τ hτ z hz z' hz'
        have htri : |h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z
              + (deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z')
              - (h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z')|
            ≤ |h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z|
              + |deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z'|
              + |h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z'| := by
          have ht := abs_add_three
            (h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z)
            (deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z')
            (-(h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z'))
          rw [abs_neg] at ht
          exact ht
        have hsplit : h⁻¹ • (f τ (z + h) - f τ z) - h⁻¹ • (f τ (z' + h) - f τ z')
            = h⁻¹ • (f τ (z + h) - f τ z) - deriv (fun z'' => f τ z'') z
              + (deriv (fun z'' => f τ z'') z - deriv (fun z'' => f τ z'') z')
              - (h⁻¹ • (f τ (z' + h) - f τ z') - deriv (fun z'' => f τ z'') z') := by
          simp only [smul_eq_mul]; ring
        rw [hsplit]
        linarith [htri, hpz, hpz', hdiffτ]
      have htendQ : Filter.Tendsto
          (fun τ => h⁻¹ • (f τ (z + h) - f τ z) - h⁻¹ • (f τ (z' + h) - f τ z'))
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (h⁻¹ • (R (z + h) - R z) - h⁻¹ • (R (z' + h) - R z'))) := by
        have h1 : Filter.Tendsto (fun τ => h⁻¹ • (f τ (z + h) - f τ z))
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (h⁻¹ • (R (z + h) - R z))) :=
          ((htend (z + h) hzl).sub (htend z hz)).const_smul (h⁻¹)
        have h2 : Filter.Tendsto (fun τ => h⁻¹ • (f τ (z' + h) - f τ z'))
            (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (h⁻¹ • (R (z' + h) - R z'))) :=
          ((htend (z' + h) hz'l).sub (htend z' hz')).const_smul (h⁻¹)
        exact h1.sub h2
      exact le_of_tendsto htendQ.abs (Filter.eventually_of_mem hIoc (fun τ hτ => hQb τ hτ))
    -- pass to the limit `h → 0⁺`
    have hLtend : Filter.Tendsto
        (fun h => h⁻¹ • (R (z + h) - R z) - h⁻¹ • (R (z' + h) - R z'))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (deriv R z - deriv R z')) :=
      (((hdiff.differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt.tendsto_slope_zero_right).sub
       ((hdiff.differentiableAt (isOpen_Ioi.mem_nhds hz')).hasDerivAt.tendsto_slope_zero_right))
    have hIoo : Set.Ioo (0:ℝ) (min δ₁ δ₂) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂), isOpen_Ioo,
        ⟨by linarith, hδpos⟩, ?_⟩
      rintro x ⟨hx1, hx2⟩
      exact ⟨show (0:ℝ) < x from hx2, hx1.2⟩
    exact le_of_tendsto hLtend.abs (Filter.eventually_of_mem hIoo (fun h hh => hkey h hh.1 hh.2))
  -- Step 2: the modulus bound makes `deriv R` continuous on `(0,∞)`.
  have hcont : ContinuousOn (fun z => deriv R z) (Set.Ioi (0:ℝ)) := by
    intro z hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hcont_z := Metric.continuousWithinAt_iff.mp
      (hEcont.continuousWithinAt (show (z, z) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hz, hz⟩))
    obtain ⟨δ, hδpos, hδ⟩ := hcont_z ε hε
    refine ⟨δ, hδpos, ?_⟩
    intro z' hz' hz'δ
    have hd : dist (z', z) (z, z) < δ := by simpa [Prod.dist_eq, Real.dist_eq] using hz'δ
    have h := hδ (x := (z', z)) ⟨hz', hz⟩ hd
    rw [Real.dist_eq, hEdiag z hz, sub_zero] at h
    calc dist (deriv R z') (deriv R z)
        = |deriv R z' - deriv R z| := Real.dist_eq _ _
      _ ≤ E z' z := hmod z' hz' z hz
      _ ≤ |E z' z| := le_abs_self _
      _ < ε := h
  -- Step 3: `R` is differentiable with continuous derivative, i.e. `C¹`.
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  exact ⟨hdiff, hcont.congr fun x hx => derivWithin_of_isOpen isOpen_Ioi hx⟩

end Work.FTS_RegExport.RXR1
