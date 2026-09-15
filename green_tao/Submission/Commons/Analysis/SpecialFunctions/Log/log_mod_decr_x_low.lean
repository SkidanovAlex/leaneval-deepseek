import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

open scoped Topology

namespace Commons.Analysis.SpecialFunctions.Log

noncomputable section

private def phi (a : ℝ) : ℝ := 2 * (a * Real.arctan a) - Real.log (1 + a ^ 2)

private lemma phi_hasDerivAt (a : ℝ) : HasDerivAt phi (2 * Real.arctan a) a := by
  have h1 : HasDerivAt (fun y : ℝ => y * Real.arctan y) (Real.arctan a + a / (1 + a ^ 2)) a := by
    change HasDerivAt (id * Real.arctan) (Real.arctan a + a / (1 + a ^ 2)) a
    simpa [div_eq_mul_inv] using (hasDerivAt_id a).mul (Real.hasDerivAt_arctan a)
  have hP : HasDerivAt (fun y : ℝ => 2 * (y * Real.arctan y))
      (2 * (Real.arctan a + a / (1 + a ^ 2))) a := by
    simpa using h1.const_mul 2
  have hi : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * a) a := by
    simpa using ((hasDerivAt_id a).pow 2).const_add (1 : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) ((2 * a) / (1 + a ^ 2)) a := by
    simpa [div_eq_mul_inv] using (hi.log (by positivity : 1 + a ^ 2 ≠ 0))
  unfold phi
  convert (hP.sub h2) using 1
  · rfl
  · rfl
  · funext a; rfl
  · ring

private lemma phi_nonneg (a : ℝ) (ha : 0 ≤ a) : 0 ≤ phi a := by
  have hcont : ContinuousOn phi (Set.Icc (0 : ℝ) a) := by
    intro y hy
    exact (phi_hasDerivAt y).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ phi (interior (Set.Icc (0 : ℝ) a)) := by
    intro y hy
    exact (phi_hasDerivAt y).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) a), 0 ≤ deriv phi y := by
    intro y hy
    rw [(phi_hasDerivAt y).deriv]
    have hy' : y ∈ Set.Ioo (0 : ℝ) a := by simpa [interior_Icc] using hy
    exact mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr (le_of_lt hy'.1))
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) a) hcont hdiff hnonneg
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 a := by exact ⟨le_rfl, ha⟩
  have hmemA : a ∈ Set.Icc 0 a := by exact ⟨ha, le_rfl⟩
  have hle := hmono hmem0 hmemA ha
  simpa [phi] using hle

private lemma log_two_arctan (a : ℝ) (ha : 0 ≤ a) :
    Real.log (1 + a ^ 2) ≤ 2 * a * Real.arctan a := by
  have h := phi_nonneg a ha
  rw [phi] at h
  linarith

private lemma log_y_mul_le_two_t_arctan (y t : ℝ) (hy0 : 0 < y) (hy1 : y ≤ 1) (ht : 0 ≤ t) :
    y * Real.log (y ^ 2 + t ^ 2) ≤ 2 * t * Real.arctan (t / y) := by
  by_cases ht0 : t = 0
  · subst t
    have hy2 : 0 < y ^ 2 := by positivity
    have hy2le : y ^ 2 ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hy1 (le_of_lt hy0)
      nlinarith
    have hlog2 : Real.log (y ^ 2) ≤ 0 := Real.log_nonpos (le_of_lt hy2) hy2le
    have hgoal : y * Real.log (y ^ 2) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hy0) hlog2
    simpa using hgoal
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let a : ℝ := t / y
    have hane : 0 ≤ a := div_nonneg ht (le_of_lt hy0)
    have hyne : y ≠ 0 := ne_of_gt hy0
    have hL : y * Real.log (y ^ 2 + t ^ 2) = 2 * y * Real.log y + y * Real.log (1 + a ^ 2) := by
      have harg : y ^ 2 + t ^ 2 = y ^ 2 * (1 + a ^ 2) := by
        subst a
        field_simp [hyne]
      calc
        y * Real.log (y ^ 2 + t ^ 2)
            = y * Real.log (y ^ 2 * (1 + a ^ 2)) := by rw [harg]
        _ = y * (Real.log (y ^ 2) + Real.log (1 + a ^ 2)) := by
            rw [Real.log_mul (by positivity : y ^ 2 ≠ 0) (by positivity : 1 + a ^ 2 ≠ 0)]
        _ = y * (2 * Real.log y + Real.log (1 + a ^ 2)) := by
            rw [Real.log_pow]
            norm_num
        _ = 2 * y * Real.log y + y * Real.log (1 + a ^ 2) := by ring
    have hloga : Real.log (1 + a ^ 2) ≤ 2 * a * Real.arctan a := by
      have hla := log_two_arctan a hane
      simpa [a] using hla
    have h1 : 2 * y * Real.log y ≤ 0 := by
      have hlogy : Real.log y ≤ 0 := Real.log_nonpos (le_of_lt hy0) hy1
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (le_of_lt hy0)) hlogy
    have h2 : y * Real.log (1 + a ^ 2) ≤ 2 * y * a * Real.arctan a := by
      calc
        y * Real.log (1 + a ^ 2) ≤ y * (2 * a * Real.arctan a) :=
          mul_le_mul_of_nonneg_left hloga (le_of_lt hy0)
        _ = 2 * y * a * Real.arctan a := by ring
    calc
      y * Real.log (y ^ 2 + t ^ 2)
          = 2 * y * Real.log y + y * Real.log (1 + a ^ 2) := hL
      _ ≤ 2 * y * a * Real.arctan a := by nlinarith
      _ = 2 * t * Real.arctan (t / y) := by
        subst a
        field_simp [hyne]

private def modSq (t : ℝ) (y : ℝ) : ℝ :=
  (((1 : ℝ) / 2) * Real.log (y ^ 2 + t ^ 2)) ^ 2 + (Real.arctan (t / y)) ^ 2

private lemma modSq_hasDerivAt (t : ℝ) (y : ℝ) (hy0 : 0 < y) :
    HasDerivAt (modSq t)
      ((y * Real.log (y ^ 2 + t ^ 2) - 2 * t * Real.arctan (t / y)) / (y ^ 2 + t ^ 2)) y := by
  have hy : y ≠ 0 := ne_of_gt hy0
  have hLpos : 0 < y ^ 2 + t ^ 2 := by positivity
  have hLne : y ^ 2 + t ^ 2 ≠ 0 := ne_of_gt hLpos
  have hu : HasDerivAt (fun u : ℝ => u ^ 2 + t ^ 2) (2 * y) y := by
    simpa using (((hasDerivAt_id y).pow 2).add_const (t ^ 2))
  have hlogu : HasDerivAt (fun u : ℝ => Real.log (u ^ 2 + t ^ 2)) ((2 * y) / (y ^ 2 + t ^ 2)) y := by
    simpa [div_eq_mul_inv] using hu.log hLne
  have hg1 : HasDerivAt (fun u : ℝ => ((1 : ℝ) / 2) * Real.log (u ^ 2 + t ^ 2))
      (((1 : ℝ) / 2) * ((2 * y) / (y ^ 2 + t ^ 2))) y := by
    simpa using hlogu.const_mul ((1 : ℝ) / 2)
  have hA : HasDerivAt (fun u : ℝ => (((1 : ℝ) / 2) * Real.log (u ^ 2 + t ^ 2)) ^ 2)
      ((y * Real.log (y ^ 2 + t ^ 2)) / (y ^ 2 + t ^ 2)) y := by
    have hp := hg1.pow 2
    convert hp using 1
    · rfl
    · rfl
    · funext u; rfl
    · field_simp [hLne]
      ring
  have hconst : HasDerivAt (fun u : ℝ => t) 0 y := hasDerivAt_const y t
  have hid : HasDerivAt (fun u : ℝ => u) 1 y := hasDerivAt_id y
  have hdiv : HasDerivAt (fun u : ℝ => t / u) (-t / y ^ 2) y := by
    have hd := hconst.div hid hy
    convert hd using 1
    · rfl
    · rfl
    · funext u; rfl
    · field_simp [hy]
      ring
  have harct : HasDerivAt (fun u : ℝ => Real.arctan (t / u))
      (1 / (1 + (t / y) ^ 2) * (-t / y ^ 2)) y := hdiv.arctan
  have hB : HasDerivAt (fun u : ℝ => (Real.arctan (t / u)) ^ 2)
      (-2 * t * Real.arctan (t / y) / (y ^ 2 + t ^ 2)) y := by
    have hp := harct.pow 2
    convert hp using 1
    · rfl
    · rfl
    · funext u; rfl
    · field_simp [hy]
      ring
  have hsum : HasDerivAt (fun u : ℝ => (((1 : ℝ) / 2) * Real.log (u ^ 2 + t ^ 2)) ^ 2 +
      (Real.arctan (t / u)) ^ 2)
      ((y * Real.log (y ^ 2 + t ^ 2)) / (y ^ 2 + t ^ 2) +
        (-2 * t * Real.arctan (t / y) / (y ^ 2 + t ^ 2))) y := by
    exact hA.add hB
  unfold modSq
  convert hsum using 1
  field_simp [hLne]
  ring

private lemma modSq_antitoneOn (t : ℝ) (ht : 0 ≤ t) :
    AntitoneOn (modSq t) (Set.Icc ((1 : ℝ) / 2) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc ((1 : ℝ) / 2) 1)
  · intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    exact (modSq_hasDerivAt t y hy0).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by simpa [interior_Icc] using hy
    have hy0 : 0 < y := by linarith [hy'.1]
    exact (modSq_hasDerivAt t y hy0).differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : y ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by simpa [interior_Icc] using hy
    have hy0 : 0 < y := by linarith [hy'.1]
    have hy1 : y ≤ 1 := le_of_lt hy'.2
    rw [(modSq_hasDerivAt t y hy0).deriv]
    rw [div_le_iff₀ (by positivity : 0 < y ^ 2 + t ^ 2)]
    have hnum : y * Real.log (y ^ 2 + t ^ 2) - 2 * t * Real.arctan (t / y) ≤ 0 := by
      exact sub_nonpos.mpr (log_y_mul_le_two_t_arctan y t hy0 hy1 ht)
    linarith

theorem log_mod_decr_x_low (x t : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 1) (ht : 0 ≤ t) :
    Real.sqrt ((((1 : ℝ) / 2) * Real.log (x ^ 2 + t ^ 2)) ^ 2 + (Real.arctan (t / x)) ^ 2) ≤
      Real.sqrt ((((1 : ℝ) / 2) * Real.log ((1 : ℝ) / 4 + t ^ 2)) ^ 2 + (Real.arctan (2 * t)) ^ 2) := by
  have hxmem : x ∈ Set.Icc ((1 : ℝ) / 2) 1 := ⟨hx1, hx2⟩
  have hx0mem : ((1 : ℝ) / 2) ∈ Set.Icc ((1 : ℝ) / 2) 1 := by
    exact ⟨le_rfl, by norm_num⟩
  have hanti := modSq_antitoneOn t ht
  have hmod : modSq t x ≤ modSq t ((1 : ℝ) / 2) := hanti hx0mem hxmem hx1
  have hhalf : modSq t ((1 : ℝ) / 2) =
      (((1 : ℝ) / 2) * Real.log ((1 : ℝ) / 4 + t ^ 2)) ^ 2 + (Real.arctan (2 * t)) ^ 2 := by
    unfold modSq
    congr 1
    · congr 1
      congr 1
      norm_num
    · congr 1
      field_simp
  have hmod' : modSq t x ≤
      (((1 : ℝ) / 2) * Real.log ((1 : ℝ) / 4 + t ^ 2)) ^ 2 + (Real.arctan (2 * t)) ^ 2 := by
    rw [hhalf] at hmod
    exact hmod
  have hle : (((1 : ℝ) / 2) * Real.log (x ^ 2 + t ^ 2)) ^ 2 + (Real.arctan (t / x)) ^ 2 ≤
      (((1 : ℝ) / 2) * Real.log ((1 : ℝ) / 4 + t ^ 2)) ^ 2 + (Real.arctan (2 * t)) ^ 2 := by
    simpa [modSq] using hmod'
  exact Real.sqrt_le_sqrt hle

end

end Commons.Analysis.SpecialFunctions.Log