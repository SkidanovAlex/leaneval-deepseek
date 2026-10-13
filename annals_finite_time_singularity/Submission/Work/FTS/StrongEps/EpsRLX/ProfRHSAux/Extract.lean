/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/Extract` — pointwise bounds from the honest norms

* extraction of pointwise `L^∞`-bounds from the honest `𝒲^{4,∞}`-norm (`WlInfMem`);
* the trace-free `ℋ⁴ → L^∞` trade-off (`SmoothOpen ∧ HkMem α 4` ⟹ bounded);
* the pointwise bounds on the star and elliptic parts of `ℛ(Φ̃)`, `U(Φ̃)/sin 2θ`, `V(Φ̃)`
  that follow from `StarPkgo2` and `EllPkgGo`;
* the filter bookkeeping used by the trace arguments.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Extraction of pointwise bounds from `WlInf` -/

/-- The `𝒲^{4,∞}`-norm is nonnegative on the honest class. -/
theorem wlInf_nonneg {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    0 ≤ Work.Spaces.WlInf α 4 f := by
  rw [Work.Spaces.WlInf]
  refine add_nonneg (Finset.sum_nonneg fun k hk => ?_)
    (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
  · exact Work.Spaces.supAbs_nonneg (hmem.1 k (by have := Finset.mem_range.mp hk; omega))
  · split_ifs with h
    · exact Work.Spaces.supAbs_nonneg
        (hmem.2 j (by have := Finset.mem_range.mp hj; omega) k
          (by have := Finset.mem_range.mp hk; omega) h.1 h.2)
    · exact le_refl 0

/-- The sup norm of the datum itself is bounded by `|f|_{𝒲^{4,∞}}` (the `k = 0` summand). -/
theorem supAbs_le_WlInf {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f) :
    Work.Spaces.supAbs f ≤ Work.Spaces.WlInf α 4 f := by
  have hfirst : Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0 * Work.Spaces.pzIter 0 f z θ)
      ≤ ∑ k ∈ Finset.range 5,
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ) :=
    Finset.single_le_sum
      (f := fun k => Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
      (fun k hk => Work.Spaces.supAbs_nonneg (hmem.1 k (by
        have := Finset.mem_range.mp hk; omega)))
      (by simp)
  have hsecond : (∑ k ∈ Finset.range 5,
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
      ≤ Work.Spaces.WlInf α 4 f := by
    rw [Work.Spaces.WlInf]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
    split_ifs with h
    · exact Work.Spaces.supAbs_nonneg (hmem.2 j (by have := Finset.mem_range.mp hj; omega) k
        (by have := Finset.mem_range.mp hk; omega) h.1 h.2)
    · exact le_refl 0
  calc Work.Spaces.supAbs f
      = Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0 * Work.Spaces.pzIter 0 f z θ) := by simp
    _ ≤ _ := hfirst
    _ ≤ Work.Spaces.WlInf α 4 f := hsecond

/-- **The pointwise bound from an honest `𝒲^{4,∞}`-norm.**  For a datum whose `𝒲^{4,∞}`-norm
is finite (`WlInfMem`), every value on the domain is bounded by that norm. -/
theorem abs_le_WlInf {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.WlInfMem α 4 f)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ| ≤ Work.Spaces.WlInf α 4 f ∧ 0 ≤ Work.Spaces.WlInf α 4 f := by
  have hfin : Work.Spaces.SupFinite f := by
    have h := hmem.1 0 (by norm_num)
    simpa using h
  exact ⟨le_trans (Work.Spaces.abs_le_supAbs hz hθ hfin) (supAbs_le_WlInf hmem),
    wlInf_nonneg hmem⟩

/-! ## The trace-free `ℋ⁴ → L^∞` trade-off -/

/-- **The pointwise bound from `SmoothOpen ∧ HkMem α 4`**: the trace-free `ℋ⁴ → L^∞`
trade-off `v2_hkMem_pointwise_min`, restricted to order `0` and with the `min z 1`-factor
dropped (`min z 1 ≤ 1`). -/
theorem exists_pointwise_bound_of_HQo {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ C := by
  obtain ⟨C, hC0, hbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  refine ⟨C * Work.Spaces.HkNorm α 4 f, mul_nonneg hC0 (Work.Spaces.HkNorm_nonneg α 4 f), ?_⟩
  intro z θ hz hθ0 hθ1
  have h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp h 4
  have hpt := hbd f h4 hm 0 0 (by norm_num) z θ hz hθ0 hθ1
  have hpt' : |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.pthIter_zero] using hpt
  calc |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := hpt'
    _ ≤ C * 1 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right z 1) hC0)
          (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = C * Work.Spaces.HkNorm α 4 f := by ring

/-! ## Pointwise bounds for the star and elliptic parts of `ℛ(Φ̃), U(Φ̃), V(Φ̃)` -/

/-- **The star bounds**: from `StarPkgo2` (whose `𝒲^{4,∞}`-fields bound
`((z+1)/z)ℛ(Φ̃_*)`, `V(Φ̃_*)` and `U(Φ̃_*)/sin 2θ` by `Cs·α`) one gets, at every interior
point, `|ℛ(Φ̃_*)| ≤ Cs·α`, `|V(Φ̃_*)| ≤ Cs·α` and `|U(Φ̃_*)| ≤ Cs·α·|sin 2θ|`. -/
theorem star_op_bounds {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ C ∧
       |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ C ∧
       |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          ≤ C * |Work.Construction.s2 θ|) := by
  obtain ⟨hRmem, hRb⟩ := hstar.RW
  obtain ⟨hVmem, hVb⟩ := hstar.VW
  obtain ⟨hUmem, hUb⟩ := hstar.UsW
  have hCnn : 0 ≤ Cs * α := le_trans (wlInf_nonneg hRmem) hRb
  refine ⟨Cs * α, hCnn, ?_⟩
  intro z θ hz hθ0 hθ1
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  obtain ⟨h1, -⟩ := abs_le_WlInf hRmem hzIz hθIθ
  have hR : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
    have h2 : |(z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ Cs * α := le_trans h1 hRb
    have hzpos : 0 < (z + 1) / z := by positivity
    have hfac : (z / (z + 1)) * ((z + 1) / z) = 1 := by field_simp
    have h3 : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| * ((z + 1) / z)
        ≤ Cs * α := by
      have h2' : (z + 1) / z
          * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
        rwa [abs_mul, abs_of_pos hzpos] at h2
      calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| * ((z + 1) / z)
          = (z + 1) / z * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
            ring
        _ ≤ Cs * α := h2'
    have hz1 : 0 < z + 1 := by linarith
    calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        = |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
            * ((z / (z + 1)) * ((z + 1) / z)) := by rw [hfac, mul_one]
      _ = (|Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| * ((z + 1) / z))
            * (z / (z + 1)) := by ring
      _ ≤ (Cs * α) * (z / (z + 1)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ (Cs * α) * 1 :=
          mul_le_mul_of_nonneg_left (by rw [div_le_one hz1]; linarith) hCnn
      _ = Cs * α := by ring
  have hV : |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
    obtain ⟨h1', -⟩ := abs_le_WlInf hVmem hzIz hθIθ
    exact le_trans h1' hVb
  have hU : |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ Cs * α * |Work.Construction.s2 θ| := by
    obtain ⟨h1', -⟩ := abs_le_WlInf hUmem hzIz hθIθ
    have h2 : |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ| ≤ Cs * α := le_trans h1' hUb
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      have h2θ : 0 < 2 * θ := by linarith
      have h2π : 2 * θ < Real.pi := by linarith [Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
    calc |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        = |(Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ) * Work.Construction.s2 θ| := by
          rw [div_mul_cancel₀ _ hs2]
      _ = |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := by rw [abs_mul]
      _ ≤ (Cs * α) * |Work.Construction.s2 θ| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  exact ⟨hR, hV, by simpa only [mul_assoc] using hU⟩

/-- **The elliptic bounds**: from `EllPkgGo` (whose fields are `SmoothOpen ∧ HkMem α 4`, hence
pointwise bounded by `exists_pointwise_bound_of_HQo`) one gets, at every interior point,
`|ℛ(Φ̃_ell)| ≤ C`, `|V(Φ̃_ell)| ≤ C` and `|U(Φ̃_ell)| ≤ C·|sin 2θ|`. -/
theorem ell_op_bounds {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W Φg : ℝ → ℝ → ℝ}
    (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Construction.Rop α (Work.Construction.PhiTil α W Φg) z θ| ≤ C ∧
       |Work.Construction.Vop (Work.Construction.PhiTil α W Φg) z θ| ≤ C ∧
       |Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ|
          ≤ C * |Work.Construction.s2 θ|) := by
  obtain ⟨CR, hCR0, hCR⟩ := exists_pointwise_bound_of_HQo hα hα1 hell.R.1.1 hell.R.1.2
  obtain ⟨CU, hCU0, hCU⟩ := exists_pointwise_bound_of_HQo hα hα1 hell.U.1.1 hell.U.1.2
  obtain ⟨CV, hCV0, hCV⟩ := exists_pointwise_bound_of_HQo hα hα1 hell.V.1.1 hell.V.1.2
  refine ⟨max CR (max CU CV), le_trans hCR0 (le_max_left _ _), ?_⟩
  intro z θ hz hθ0 hθ1
  have hCVmax : |Work.Construction.Vop (Work.Construction.PhiTil α W Φg) z θ|
      ≤ max CR (max CU CV) :=
    le_trans (hCV hz hθ0 hθ1)
      (le_trans (le_max_right CU CV) (le_max_right CR (max CU CV)))
  refine ⟨le_trans (hCR hz hθ0 hθ1) (le_max_left _ _), hCVmax, ?_⟩
  have hU := hCU hz hθ0 hθ1
  have hUC : Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ
      = (Work.Construction.Uop α (Work.Construction.PhiTil α W Φg) z θ
          / Work.Construction.s2 θ) * Work.Construction.s2 θ := by
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      have h2θ : 0 < 2 * θ := by linarith
      have h2π : 2 * θ < Real.pi := by linarith [Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
    rw [div_mul_cancel₀ _ hs2]
  rw [hUC, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact le_trans hU (le_trans (le_max_left CU CV) (le_max_right CR (max CU CV)))

/-! ## Filter bookkeeping -/

/-- `Ici 0` is a neighbourhood of every `z > 0`. -/
theorem Ici_mem_nhds_of_pos {z : ℝ} (hz : 0 < z) : Set.Ici (0 : ℝ) ∈ 𝓝 z :=
  Filter.mem_of_superset (isOpen_Ioi.mem_nhds hz) (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))

/-- Points of the filter `𝓝[>] 0` eventually lie in the open angular interval. -/
theorem eventually_mem_Ioo_left : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)] with θ h
  intro hθ
  exact ⟨hθ, h⟩

/-- Points of the filter `𝓝[<] (π/2)` eventually lie in the open angular interval. -/
theorem eventually_mem_Ioo_right :
    ∀ᶠ θ : ℝ in 𝓝[<] (Real.pi / 2), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)] with θ h
  intro hθ
  exact ⟨h, hθ⟩

/-- **A vanishing factor times an eventually bounded factor vanishes.** -/
theorem tendsto_mul_of_eventually_bounded {f g : ℝ → ℝ} {l : Filter ℝ} {C : ℝ}
    (hf : Filter.Tendsto f l (𝓝 0)) (hg : ∀ᶠ θ in l, |g θ| ≤ C) :
    Filter.Tendsto (fun θ => f θ * g θ) l (𝓝 0) := by
  have h1 : Filter.Tendsto (fun θ => |f θ| * C) l (𝓝 0) := by
    have h := hf.norm.mul_const C
    simpa only [Real.norm_eq_abs, norm_zero, zero_mul] using h
  have habs : Filter.Tendsto (fun θ => |f θ * g θ|) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
      (Eventually.of_forall fun θ => abs_nonneg _) ?_
    filter_upwards [hg] with θ hθ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- **The vanishing of a term bounded by a vanishing one.** -/
theorem tendsto_zero_of_eventually_abs_le {f v : ℝ → ℝ} {l : Filter ℝ}
    (hv : Filter.Tendsto v l (𝓝 0)) (h : ∀ᶠ θ in l, |f θ| ≤ |v θ|) :
    Filter.Tendsto f l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hv ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv
    (Eventually.of_forall fun θ => norm_nonneg _) ?_
  filter_upwards [h] with θ hθ
  simpa only [Real.norm_eq_abs] using hθ

/-- An eventually bounded factor times a vanishing one vanishes (commuted form). -/
theorem tendsto_mul_comm_of_eventually_bounded {f g : ℝ → ℝ} {l : Filter ℝ} {C : ℝ}
    (hf : Filter.Tendsto f l (𝓝 0)) (hg : ∀ᶠ θ in l, |g θ| ≤ C) :
    Filter.Tendsto (fun θ => g θ * f θ) l (𝓝 0) := by
  simpa only [mul_comm] using tendsto_mul_of_eventually_bounded hf hg

/-- `c2m θ = cos 2θ - sin²θ` is bounded by `2`. -/
theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  have ha : |Real.cos (2 * θ)| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hb : |Real.sin θ ^ 2| ≤ 1 := by
    have h : |Real.sin θ| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith [h, abs_nonneg (Real.sin θ)]
  calc |Work.Construction.c2m θ| = |Real.cos (2 * θ) - Real.sin θ ^ 2| := rfl
    _ ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by
        simpa only [abs_neg, sub_eq_add_neg] using abs_add_le (Real.cos (2 * θ)) (-(Real.sin θ ^ 2))
    _ ≤ 2 := by linarith


end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
