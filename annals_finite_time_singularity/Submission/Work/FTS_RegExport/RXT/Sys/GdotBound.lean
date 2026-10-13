import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.GdotExp
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_Dz_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.GdotBound` -- the expansion of the transport operator (S5b, core)

`sys_bound`: the commutator bound for the transport operator at order `≤ 2`.  The difference
between `mixed j i (a·D_zX + d·D_θX + c·X)` and its principal part `a·mixed (j+1) i X +
d·mixed j (i+1) X` is a sum of order-`≤ 2` coefficient jets times order-`≤ 2` jets of `G`, where
`X = P + G`; it is bounded by `200·(|M|+1)` times the sum of the six order-`≤ 2` jets of `G`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7 ω phiTil)
open Work.FTS.RegExportIface.RXT (VR bR cR SigR μR GR ΦR idx)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## The abstract commutator bound -/

theorem sys_bound {a d c X P G : ℝ → ℝ → ℝ} {M : ℝ}
    (ha : ContDiffOn ℝ 2 (Function.uncurry a) Q0)
    (hd : ContDiffOn ℝ 2 (Function.uncurry d) Q0)
    (hc : ContDiffOn ℝ 2 (Function.uncurry c) Q0)
    (hP : ContDiffOn ℝ 3 (Function.uncurry P) Q0)
    (hG : ContDiffOn ℝ 3 (Function.uncurry G) Q0)
    (hXPG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → X z θ = P z θ + G z θ)
    (hM : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ p q : ℕ, p + q ≤ 2 →
      |Work.Spaces.mixed p q a z θ| ≤ M ∧ |Work.Spaces.mixed p q d z θ| ≤ M ∧
        |Work.Spaces.mixed p q c z θ| ≤ M)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.mixed j i (fun z θ => -(a z θ * Work.Spaces.Dz X z θ
          + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ)) z θ
        + (a z θ * Work.Spaces.mixed (j + 1) i G z θ
          + d z θ * Work.Spaces.mixed j (i + 1) G z θ)
        + Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz P z θ
          + d z θ * Work.Spaces.Dth P z θ + c z θ * P z θ) z θ|
      ≤ (200 * (|M| + 1)) * ∑ t : Fin 6, |Work.Spaces.mixed (idx t).1 (idx t).2 G z θ| := by
  have hzθ : (z, θ) ∈ Q0 := Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hi2 : i ≤ 2 := by omega
  have hj2 : j ≤ 2 := by omega
  have hX : ContDiffOn ℝ 3 (Function.uncurry X) Q0 :=
    (hP.add hG).congr (fun p hp => hXPG p.1 p.2 hp.1 hp.2.1 hp.2.2)
  have hXeq : EqOn (Function.uncurry X)
      (Function.uncurry (fun z θ => P z θ + G z θ)) Q0 :=
    fun p hp => hXPG p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hXsplit : ∀ p q : ℕ, p + q ≤ 3 →
      Work.Spaces.mixed p q X z θ = Work.Spaces.mixed p q P z θ + Work.Spaces.mixed p q G z θ := by
    intro p q hpq
    rw [mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hXeq p q z θ hzθ]
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
      Work.FTS.EllipticEst.isOpen_Q0 hP hG q p (Nat.add_comm p q ▸ hpq) (z, θ) hzθ
  set TA : (ℝ → ℝ → ℝ) → ℕ → ℕ → ℝ := fun Y u v =>
    ((i.choose u : ℝ) * (j.choose v : ℝ)) *
      (Work.Spaces.mixed v u a z θ * Work.Spaces.mixed (j - v + 1) (i - u) Y z θ) with hTA
  set TD : (ℝ → ℝ → ℝ) → ℕ → ℕ → ℝ := fun Y u v =>
    ((i.choose u : ℝ) * (j.choose v : ℝ)) *
      (Work.Spaces.mixed v u d z θ * Work.Spaces.mixed (j - v) (i - u + 1) Y z θ) with hTD
  set TC : (ℝ → ℝ → ℝ) → ℕ → ℕ → ℝ := fun Y u v =>
    ((i.choose u : ℝ) * (j.choose v : ℝ)) *
      (Work.Spaces.mixed v u c z θ * Work.Spaces.mixed (j - v) (i - u) Y z θ) with hTC
  set AX : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TA X u v with hAX
  set DX : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TD X u v with hDX
  set CX : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TC X u v with hCX
  set AP : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TA P u v with hAP
  set DP : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TD P u v with hDP
  set CP : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TC P u v with hCP
  set AG : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TA G u v with hAG
  set DG : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TD G u v with hDG
  set CG : ℝ := ∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TC G u v with hCG
  set R1 : ℝ := (∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TA G (u + 1) v)
    + (∑ v ∈ Finset.range j, TA G 0 (v + 1)) with hR1
  set R2 : ℝ := (∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TD G (u + 1) v)
    + (∑ v ∈ Finset.range j, TD G 0 (v + 1)) with hR2
  set Ssum : ℝ := ∑ t : Fin 6, |Work.Spaces.mixed (idx t).1 (idx t).2 G z θ| with hSsum
  have hSnn : 0 ≤ Ssum := by
    rw [hSsum]; exact Finset.sum_nonneg (fun t _ => abs_nonneg _)
  set K : ℝ := 4 * |M| * Ssum with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]; have := abs_nonneg M; nlinarith
  have hGle : ∀ p q : ℕ, p + q ≤ 2 →
      |Work.Spaces.mixed p q G z θ| ≤ Ssum := by
    intro p q hpq
    rw [hSsum]; exact mixed_le_sum_idx hpq
  have hA : Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ) z θ = AX + DX + CX := by
    rw [mixed_transport_expand ha hd hc hX hji hz hθ0 hθ1, hAX, hDX, hCX, hTA, hTD, hTC]
  have hB : Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz P z θ
        + d z θ * Work.Spaces.Dth P z θ + c z θ * P z θ) z θ = AP + DP + CP := by
    rw [mixed_transport_expand ha hd hc hP hji hz hθ0 hθ1, hAP, hDP, hCP, hTA, hTD, hTC]
  have hneg : Work.Spaces.mixed j i (fun z θ => -(a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ)) z θ = -(AX + DX + CX) := by
    rw [← hA]
    have h1 : (fun z θ : ℝ => -(a z θ * Work.Spaces.Dz X z θ
        + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ))
        = (fun z θ => (-1 : ℝ) * (a z θ * Work.Spaces.Dz X z θ
          + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ)) := by
      funext z θ; rw [neg_eq_neg_one_mul]
    rw [h1, Work.FTS.EllipticEst.RegQ.mixed_const_mul]
    simp
  have hS1 : AX = AP + AG := by
    rw [hAX, hAP, hAG, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u hu
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v hv
    have hpt : TA X u v = TA P u v + TA G u v := by
      simp only [hTA]
      rw [hXsplit (j - v + 1) (i - u) (by
        have hu' : u ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu
        have hv' : v ≤ j := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv
        omega)]
      ring
    rw [hpt]
  have hS2 : DX = DP + DG := by
    rw [hDX, hDP, hDG, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u hu
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v hv
    have hpt : TD X u v = TD P u v + TD G u v := by
      simp only [hTD]
      rw [hXsplit (j - v) (i - u + 1) (by
        have hu' : u ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu
        have hv' : v ≤ j := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv
        omega)]
      ring
    rw [hpt]
  have hS3 : CX = CP + CG := by
    rw [hCX, hCP, hCG, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u hu
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v hv
    have hpt : TC X u v = TC P u v + TC G u v := by
      simp only [hTC]
      rw [hXsplit (j - v) (i - u) (by
        have hu' : u ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu
        have hv' : v ≤ j := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv
        omega)]
      ring
    rw [hpt]
  have hTA00 : TA G 0 0 = a z θ * Work.Spaces.mixed (j + 1) i G z θ := by
    simp only [hTA, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul,
      Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
  have hTD00 : TD G 0 0 = d z θ * Work.Spaces.mixed j (i + 1) G z θ := by
    simp only [hTD, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul,
      Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
  have hPA : AG - a z θ * Work.Spaces.mixed (j + 1) i G z θ = R1 := by
    rw [hAG, hR1, ← hTA00]
    exact sum_peel i j (TA G)
  have hPD : DG - d z θ * Work.Spaces.mixed j (i + 1) G z θ = R2 := by
    rw [hDG, hR2, ← hTD00]
    exact sum_peel i j (TD G)
  have hle2i : ∀ u : ℕ, u ≤ i → |((i.choose u : ℝ))| ≤ 2 := by
    intro u hu
    have h0 : i.choose u ≤ 2 := choose_le_two hu hi2
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast h0
  have hle2j : ∀ v : ℕ, v ≤ j → |((j.choose v : ℝ))| ≤ 2 := by
    intro v hv
    have h0 : j.choose v ≤ 2 := choose_le_two hv hj2
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast h0
  have hta : ∀ u v : ℕ, u ≤ i → v ≤ j → 1 ≤ u + v → |TA G u v| ≤ K := by
    intro u v hu hv huv
    have h1 : |Work.Spaces.mixed v u a z θ| ≤ M := (hM z θ hz hθ0 hθ1 v u (by omega)).1
    have h2 : |Work.Spaces.mixed (j - v + 1) (i - u) G z θ| ≤ Ssum := hGle _ _ (by omega)
    have h3 : |((i.choose u : ℝ))| ≤ 2 := hle2i u hu
    have h4 : |((j.choose v : ℝ))| ≤ 2 := hle2j v hv
    have h5 : |Work.Spaces.mixed v u a z θ| ≤ |M| := le_trans h1 (le_abs_self M)
    have hAB : |((i.choose u : ℝ))| * |((j.choose v : ℝ))| ≤ 2 * 2 :=
      mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    have hCD : |Work.Spaces.mixed v u a z θ| * |Work.Spaces.mixed (j - v + 1) (i - u) G z θ|
        ≤ |M| * Ssum := mul_le_mul h5 h2 (abs_nonneg _) (abs_nonneg M)
    have e1 : |((i.choose u : ℝ) * (j.choose v : ℝ))
          * (Work.Spaces.mixed v u a z θ * Work.Spaces.mixed (j - v + 1) (i - u) G z θ)|
        = |((i.choose u : ℝ))| * |((j.choose v : ℝ))|
          * (|Work.Spaces.mixed v u a z θ| * |Work.Spaces.mixed (j - v + 1) (i - u) G z θ|) := by
      rw [abs_mul, abs_mul, abs_mul]
    simp only [hTA]
    rw [e1, hKdef]
    calc |((i.choose u : ℝ))| * |((j.choose v : ℝ))|
          * (|Work.Spaces.mixed v u a z θ| * |Work.Spaces.mixed (j - v + 1) (i - u) G z θ|)
        ≤ 2 * 2 * (|M| * Ssum) :=
          mul_le_mul hAB hCD (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = 4 * |M| * Ssum := by ring
  have htd : ∀ u v : ℕ, u ≤ i → v ≤ j → 1 ≤ u + v → |TD G u v| ≤ K := by
    intro u v hu hv huv
    have h1 : |Work.Spaces.mixed v u d z θ| ≤ M := (hM z θ hz hθ0 hθ1 v u (by omega)).2.1
    have h2 : |Work.Spaces.mixed (j - v) (i - u + 1) G z θ| ≤ Ssum := hGle _ _ (by omega)
    have h3 : |((i.choose u : ℝ))| ≤ 2 := hle2i u hu
    have h4 : |((j.choose v : ℝ))| ≤ 2 := hle2j v hv
    have h5 : |Work.Spaces.mixed v u d z θ| ≤ |M| := le_trans h1 (le_abs_self M)
    have hAB : |((i.choose u : ℝ))| * |((j.choose v : ℝ))| ≤ 2 * 2 :=
      mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    have hCD : |Work.Spaces.mixed v u d z θ| * |Work.Spaces.mixed (j - v) (i - u + 1) G z θ|
        ≤ |M| * Ssum := mul_le_mul h5 h2 (abs_nonneg _) (abs_nonneg M)
    have e1 : |((i.choose u : ℝ) * (j.choose v : ℝ))
          * (Work.Spaces.mixed v u d z θ * Work.Spaces.mixed (j - v) (i - u + 1) G z θ)|
        = |((i.choose u : ℝ))| * |((j.choose v : ℝ))|
          * (|Work.Spaces.mixed v u d z θ| * |Work.Spaces.mixed (j - v) (i - u + 1) G z θ|) := by
      rw [abs_mul, abs_mul, abs_mul]
    simp only [hTD]
    rw [e1, hKdef]
    calc |((i.choose u : ℝ))| * |((j.choose v : ℝ))|
          * (|Work.Spaces.mixed v u d z θ| * |Work.Spaces.mixed (j - v) (i - u + 1) G z θ|)
        ≤ 2 * 2 * (|M| * Ssum) :=
          mul_le_mul hAB hCD (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = 4 * |M| * Ssum := by ring
  have htc : ∀ u v : ℕ, u ≤ i → v ≤ j → |TC G u v| ≤ K := by
    intro u v hu hv
    have h1 : |Work.Spaces.mixed v u c z θ| ≤ M := (hM z θ hz hθ0 hθ1 v u (by omega)).2.2
    have h2 : |Work.Spaces.mixed (j - v) (i - u) G z θ| ≤ Ssum := hGle _ _ (by omega)
    have h3 : |((i.choose u : ℝ))| ≤ 2 := hle2i u hu
    have h4 : |((j.choose v : ℝ))| ≤ 2 := hle2j v hv
    have h5 : |Work.Spaces.mixed v u c z θ| ≤ |M| := le_trans h1 (le_abs_self M)
    have hAB : |((i.choose u : ℝ))| * |((j.choose v : ℝ))| ≤ 2 * 2 :=
      mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    have hCD : |Work.Spaces.mixed v u c z θ| * |Work.Spaces.mixed (j - v) (i - u) G z θ|
        ≤ |M| * Ssum := mul_le_mul h5 h2 (abs_nonneg _) (abs_nonneg M)
    have e1 : |((i.choose u : ℝ) * (j.choose v : ℝ))
          * (Work.Spaces.mixed v u c z θ * Work.Spaces.mixed (j - v) (i - u) G z θ)|
        = |((i.choose u : ℝ))| * |((j.choose v : ℝ))|
          * (|Work.Spaces.mixed v u c z θ| * |Work.Spaces.mixed (j - v) (i - u) G z θ|) := by
      rw [abs_mul, abs_mul, abs_mul]
    simp only [hTC]
    rw [e1, hKdef]
    calc |((i.choose u : ℝ))| * |((j.choose v : ℝ))|
          * (|Work.Spaces.mixed v u c z θ| * |Work.Spaces.mixed (j - v) (i - u) G z θ|)
        ≤ 2 * 2 * (|M| * Ssum) :=
          mul_le_mul hAB hCD (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = 4 * |M| * Ssum := by ring
  have hRA : |R1| ≤ 6 * K + 2 * K := by
    rw [hR1]
    have h1 : |∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TA G (u + 1) v|
        ≤ ((i * (j + 1) : ℕ) : ℝ) * K :=
      abs_double_sum_le i (j + 1) (fun u v => TA G (u + 1) v) K
        (fun u hu v hv => hta (u + 1) v (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu)
          (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv) (by omega))
    have h2 : |∑ v ∈ Finset.range j, TA G 0 (v + 1)| ≤ ((j : ℕ) : ℝ) * K :=
      abs_range_sum_le j (fun v => TA G 0 (v + 1)) K
        (fun v hv => hta 0 (v + 1) (by omega)
          (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv) (by omega))
    have h3 : ((i * (j + 1) : ℕ) : ℝ) ≤ 6 := by
      have h := Nat.mul_le_mul hi2 (show j + 1 ≤ 3 by omega)
      exact_mod_cast h
    have h4 : ((j : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hj2
    calc |(∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TA G (u + 1) v)
          + (∑ v ∈ Finset.range j, TA G 0 (v + 1))|
        ≤ |∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TA G (u + 1) v|
          + |∑ v ∈ Finset.range j, TA G 0 (v + 1)| := abs_add_le _ _
      _ ≤ ((i * (j + 1) : ℕ) : ℝ) * K + ((j : ℕ) : ℝ) * K := add_le_add h1 h2
      _ ≤ 6 * K + 2 * K :=
          add_le_add (mul_le_mul_of_nonneg_right h3 hKnn) (mul_le_mul_of_nonneg_right h4 hKnn)
  have hRD : |R2| ≤ 6 * K + 2 * K := by
    rw [hR2]
    have h1 : |∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TD G (u + 1) v|
        ≤ ((i * (j + 1) : ℕ) : ℝ) * K :=
      abs_double_sum_le i (j + 1) (fun u v => TD G (u + 1) v) K
        (fun u hu v hv => htd (u + 1) v (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu)
          (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv) (by omega))
    have h2 : |∑ v ∈ Finset.range j, TD G 0 (v + 1)| ≤ ((j : ℕ) : ℝ) * K :=
      abs_range_sum_le j (fun v => TD G 0 (v + 1)) K
        (fun v hv => htd 0 (v + 1) (by omega)
          (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv) (by omega))
    have h3 : ((i * (j + 1) : ℕ) : ℝ) ≤ 6 := by
      have h := Nat.mul_le_mul hi2 (show j + 1 ≤ 3 by omega)
      exact_mod_cast h
    have h4 : ((j : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hj2
    calc |(∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TD G (u + 1) v)
          + (∑ v ∈ Finset.range j, TD G 0 (v + 1))|
        ≤ |∑ u ∈ Finset.range i, ∑ v ∈ Finset.range (j + 1), TD G (u + 1) v|
          + |∑ v ∈ Finset.range j, TD G 0 (v + 1)| := abs_add_le _ _
      _ ≤ ((i * (j + 1) : ℕ) : ℝ) * K + ((j : ℕ) : ℝ) * K := add_le_add h1 h2
      _ ≤ 6 * K + 2 * K :=
          add_le_add (mul_le_mul_of_nonneg_right h3 hKnn) (mul_le_mul_of_nonneg_right h4 hKnn)
  have hRC : |CG| ≤ 9 * K := by
    rw [hCG]
    have h1 : |∑ u ∈ Finset.range (i + 1), ∑ v ∈ Finset.range (j + 1), TC G u v|
        ≤ (((i + 1) * (j + 1) : ℕ) : ℝ) * K :=
      abs_double_sum_le (i + 1) (j + 1) (TC G) K
        (fun u hu v hv => htc u v (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hu)
          (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hv))
    have h3 : (((i + 1) * (j + 1) : ℕ) : ℝ) ≤ 9 := by
      have h := Nat.mul_le_mul (show i + 1 ≤ 3 by omega) (show j + 1 ≤ 3 by omega)
      exact_mod_cast h
    exact le_trans h1 (mul_le_mul_of_nonneg_right h3 hKnn)
  have hMain : Work.Spaces.mixed j i (fun z θ => -(a z θ * Work.Spaces.Dz X z θ
          + d z θ * Work.Spaces.Dth X z θ + c z θ * X z θ)) z θ
        + (a z θ * Work.Spaces.mixed (j + 1) i G z θ
          + d z θ * Work.Spaces.mixed j (i + 1) G z θ)
        + Work.Spaces.mixed j i (fun z θ => a z θ * Work.Spaces.Dz P z θ
          + d z θ * Work.Spaces.Dth P z θ + c z θ * P z θ) z θ
      = -((AG - a z θ * Work.Spaces.mixed (j + 1) i G z θ)
          + (DG - d z θ * Work.Spaces.mixed j (i + 1) G z θ) + CG) := by
    rw [hneg, hB, hS1, hS2, hS3]
    ring
  rw [hMain, hPA, hPD]
  have hfin : |R1 + R2 + CG| ≤ (200 * (|M| + 1)) * Ssum := by
    have h3 := abs_add_three R1 R2 CG
    simp only [hKdef] at hRA hRD hRC
    have hMnn : 0 ≤ |M| := abs_nonneg M
    linarith [h3, hRA, hRD, hRC, hSnn, hMnn]
  simpa only [abs_neg] using hfin

end Work.FTS_RegExport.RXT.Sys
