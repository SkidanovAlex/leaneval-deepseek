import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.FBZhatP` — the six weight bounds for the pieces of `Ẑ`
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Pp0_bound {α Ce Cmu : ℝ} (hCe0 : 0 < Ce) (hCmu0 : 0 ≤ Cmu)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {σ : ℝ}
    (hE : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp0 α Φs E g σ) z θ|
        ≤ Ce * (1 + |Work.FTS.RegExportIface.RXT.μR α Φs E g σ|) * (z ^ 2 / (1 + z) ^ 2))
    (hmu : |Work.FTS.RegExportIface.RXT.μR α Φs E g σ| ≤ Cmu) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp0 α Φs E g σ) z θ| ≤ Ce * (1 + Cmu) * (z ^ 2 / (1 + z) ^ 2) := by
  intro j i hji z θ hz hθ0 hθ1
  refine le_trans (hE j i hji z θ hz hθ0 hθ1) ?_
  have h1 : (1 + |Work.FTS.RegExportIface.RXT.μR α Φs E g σ|) ≤ 1 + Cmu := by linarith
  have hz2 : 0 ≤ z ^ 2 / (1 + z) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCe0.le) hz2

theorem Pp1_bound {α Ce Cl : ℝ} (hCe0 : 0 < Ce) (hCl0 : 0 < Cl)
    (hβ0 : 0 < Work.FTS.Regularity.pExp α)
    {g : Work.FTS.Galerkin.Fam} {σ : ℝ}
    (hLgC3 : ContDiffOn ℝ 3 (LgF α g σ) (Set.Ioi 0))
    (hLgj : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter j (fun z _ => LgF α g σ z) z 0|
        ≤ Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hA1 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (al1f (Work.FTS.Regularity.pExp α)) z θ|
        ≤ Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp1 α g σ) z θ| ≤ 4 * (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) := by
  intro j i hji z θ hz hθ0 hθ1
  have hf : ContDiffOn ℝ (j + i) (Function.uncurry (fun z _ => LgF α g σ z))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_fst (hLgC3.of_le (Nat.cast_le.mpr (Nat.le_trans hji (by norm_num : 2 ≤ 3))))
  have hh : ContDiffOn ℝ (j + i)
      (Function.uncurry (al1f (Work.FTS.Regularity.pExp α))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_al1f (j + i) _
  have hbf : ∀ a b : ℕ, a + b ≤ j + i →
      |Work.Spaces.mixed b a (fun z _ => LgF α g σ z) z θ|
        ≤ Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [mixed_z_only_zero_apply, show Work.Elliptic.DzdIter b (LgF α g σ) z
          = Work.Spaces.DzIter b (fun z _ => LgF α g σ z) z 0 from
          (Work.Elliptic.DzIter_rad (LgF α g σ) b z 0).symm]
      exact hLgj b (by omega) z hz
    · rw [mixed_z_only_apply (LgF α g σ) ha z θ, abs_zero]
      exact mul_nonneg hCl0.le (by positivity)
  have hbh : ∀ a b : ℕ, a + b ≤ j + i →
      |Work.Spaces.mixed b a (al1f (Work.FTS.Regularity.pExp α)) z θ|
        ≤ Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2) :=
    fun a b hab => hA1 b a (by omega) z θ hz hθ0 hθ1
  have hmain := abs_mixed_mul_bound (j := j) (i := i) (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hf hh (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from
      ⟨hz, hθ0, hθ1⟩) (mul_nonneg hCl0.le (by positivity)) (by positivity) hbf hbh
  refine le_trans hmain ?_
  have hpow : (2 : ℝ) ^ (j + i) ≤ 4 := by
    calc (2 : ℝ) ^ (j + i) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
      _ = 4 := by norm_num
  have hCfCg : 0 ≤ (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
      * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) :=
    mul_nonneg (mul_nonneg hCl0.le (by positivity)) (by positivity)
  calc (2 : ℝ) ^ (j + i) * ((Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)))
      ≤ 4 * ((Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_right hpow hCfCg
    _ = 4 * (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + 1 / Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) := by ring

theorem Pp2_bound {α Ce Cl : ℝ} (hCe0 : 0 < Ce) (hCl0 : 0 < Cl)
    (hβ0 : 0 < Work.FTS.Regularity.pExp α)
    {g : Work.FTS.Galerkin.Fam} {σ : ℝ}
    (hKgC2 : ContDiffOn ℝ 2 (KgF α g σ) (Set.Ioi 0))
    (hKgj : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter j (fun z _ => KgF α g σ z) z 0|
        ≤ Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hA2 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (al2f (Work.FTS.Regularity.pExp α)) z θ|
        ≤ Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp2 α g σ) z θ| ≤ 4 * (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) := by
  intro j i hji z θ hz hθ0 hθ1
  have hf : ContDiffOn ℝ (j + i) (Function.uncurry (fun z _ => KgF α g σ z))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_fst (hKgC2.of_le (Nat.cast_le.mpr hji))
  have hh : ContDiffOn ℝ (j + i)
      (Function.uncurry (al2f (Work.FTS.Regularity.pExp α))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_al2f (j + i) _
  have hbf : ∀ a b : ℕ, a + b ≤ j + i →
      |Work.Spaces.mixed b a (fun z _ => KgF α g σ z) z θ|
        ≤ Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [mixed_z_only_zero_apply, show Work.Elliptic.DzdIter b (KgF α g σ) z
          = Work.Spaces.DzIter b (fun z _ => KgF α g σ z) z 0 from
          (Work.Elliptic.DzIter_rad (KgF α g σ) b z 0).symm]
      exact hKgj b (by omega) z hz
    · rw [mixed_z_only_apply (KgF α g σ) ha z θ, abs_zero]
      exact mul_nonneg hCl0.le (by positivity)
  have hbh : ∀ a b : ℕ, a + b ≤ j + i →
      |Work.Spaces.mixed b a (al2f (Work.FTS.Regularity.pExp α)) z θ|
        ≤ Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2) :=
    fun a b hab => hA2 b a (by omega) z θ hz hθ0 hθ1
  have hmain := abs_mixed_mul_bound (j := j) (i := i) (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hf hh (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from
      ⟨hz, hθ0, hθ1⟩) (mul_nonneg hCl0.le (by positivity)) (by positivity) hbf hbh
  refine le_trans hmain ?_
  have hpow : (2 : ℝ) ^ (j + i) ≤ 4 := by
    calc (2 : ℝ) ^ (j + i) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
      _ = 4 := by norm_num
  have hCfCg : 0 ≤ (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
      * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) :=
    mul_nonneg (mul_nonneg hCl0.le (by positivity)) (by positivity)
  calc (2 : ℝ) ^ (j + i) * ((Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)))
      ≤ 4 * ((Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_right hpow hCfCg
    _ = 4 * (Cl * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
        * (Ce * (1 + Work.FTS.Regularity.pExp α) * (z / (1 + z) ^ 2)) := by ring

theorem Pp3_bound {α Ce M2 : ℝ} (hCe0 : 0 < Ce) (hM0 : 0 ≤ M2)
    (hβ0 : 0 < Work.FTS.Regularity.pExp α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {σ : ℝ}
    (hps : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Vop (PtF α Φs E g σ))) Work.FTS.EllipticEst.Q0)
    (hVop : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.Construction.Vop (PtF α Φs E g σ)) z θ| ≤ M2 * min z 1)
    (hA1 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A1f z θ| ≤ Ce * (z / (1 + z) ^ 2)) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp3 α Φs E g σ) z θ|
        ≤ 4 * (2 * Work.FTS.Regularity.pExp α * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2)) := by
  intro j i hji z θ hz hθ0 hθ1
  have hf : ContDiffOn ℝ (j + i) (Function.uncurry (fun z θ => 2 * Work.FTS.Regularity.pExp α
      * Work.Construction.Vop (PtF α Φs E g σ) z θ)) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := 2 * Work.FTS.Regularity.pExp α)).mul
      ((hps.of_le (Nat.cast_le.mpr hji)).congr
        (fun p _ => by simp only [Function.uncurry]))
  have hh : ContDiffOn ℝ (j + i) (Function.uncurry A1f) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_A1f (j + i)
  have hbf : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a
      (fun z θ => 2 * Work.FTS.Regularity.pExp α
        * Work.Construction.Vop (PtF α Φs E g σ) z θ) z θ|
        ≤ 2 * Work.FTS.Regularity.pExp α * M2 * min z 1 := by
    intro a b hab
    rw [mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h2 := hVop a b (by omega) z θ hz hθ0 hθ1
    calc 2 * Work.FTS.Regularity.pExp α
          * |Work.Spaces.mixed b a (Work.Construction.Vop (PtF α Φs E g σ)) z θ|
        ≤ 2 * Work.FTS.Regularity.pExp α * (M2 * min z 1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * Work.FTS.Regularity.pExp α * M2 * min z 1 := by ring
  have hbh : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a A1f z θ|
      ≤ Ce * (z / (1 + z) ^ 2) := fun a b hab => hA1 b a (by omega) z θ hz hθ0 hθ1
  have hmain := abs_mixed_mul_bound (j := j) (i := i) (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hf hh (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from
      ⟨hz, hθ0, hθ1⟩) (by positivity) (by positivity) hbf hbh
  refine le_trans hmain ?_
  have hpow : (2 : ℝ) ^ (j + i) ≤ 4 := by
    calc (2 : ℝ) ^ (j + i) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
      _ = 4 := by norm_num
  have hCfCg : 0 ≤ (2 * Work.FTS.Regularity.pExp α * M2 * min z 1)
      * (Ce * (z / (1 + z) ^ 2)) := by positivity
  calc (2 : ℝ) ^ (j + i) * ((2 * Work.FTS.Regularity.pExp α * M2 * min z 1)
        * (Ce * (z / (1 + z) ^ 2)))
      ≤ 4 * ((2 * Work.FTS.Regularity.pExp α * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_right hpow hCfCg
    _ = 4 * (2 * Work.FTS.Regularity.pExp α * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2)) := by ring

theorem Pp4_bound {α Ce M2 : ℝ} (hCe0 : 0 < Ce) (hM0 : 0 ≤ M2)
    (hβ0 : 0 < Work.FTS.Regularity.pExp α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {σ : ℝ}
    (hps : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
      Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ
        / Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0)
    (hU : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (PtF α Φs E g σ) z θ / Real.sin (2 * θ)) z θ| ≤ M2 * min z 1)
    (hB1 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (B1f (Work.FTS.Regularity.pExp α)) z θ|
        ≤ Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2)) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp4 α Φs E g σ) z θ|
        ≤ 4 * (2 * M2 * min z 1) * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2)) := by
  intro j i hji z θ hz hθ0 hθ1
  have hf : ContDiffOn ℝ (j + i) (Function.uncurry (fun z θ => 2 *
      (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ
        / Real.sin (2 * θ)))) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := (2 : ℝ))).mul
      ((hps.of_le (Nat.cast_le.mpr hji)).congr
        (fun p _ => by simp only [Function.uncurry]))
  have hh : ContDiffOn ℝ (j + i) (Function.uncurry (B1f (Work.FTS.Regularity.pExp α)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_B1f (j + i) _
  have hbf : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a (fun z θ =>
      (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ
        / Real.sin (2 * θ))) z θ| ≤ 2 * M2 * min z 1 := by
    intro a b hab
    rw [mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h2 := hU a b (by omega) z θ hz hθ0 hθ1
    calc 2 * |Work.Spaces.mixed b a (fun z θ => Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ / Real.sin (2 * θ)) z θ|
        ≤ 2 * (M2 * min z 1) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * M2 * min z 1 := by ring
  have hbh : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a
      (B1f (Work.FTS.Regularity.pExp α)) z θ|
        ≤ Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2) :=
    fun a b hab => hB1 b a (by omega) z θ hz hθ0 hθ1
  have hmain := abs_mixed_mul_bound (j := j) (i := i) (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hf hh (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from
      ⟨hz, hθ0, hθ1⟩) (by positivity) (by positivity) hbf hbh
  refine le_trans hmain ?_
  have hpow : (2 : ℝ) ^ (j + i) ≤ 4 := by
    calc (2 : ℝ) ^ (j + i) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
      _ = 4 := by norm_num
  have hCfCg : 0 ≤ (2 * M2 * min z 1)
      * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2)) := by positivity
  calc (2 : ℝ) ^ (j + i) * ((2 * M2 * min z 1)
        * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2)))
      ≤ 4 * ((2 * M2 * min z 1) * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_right hpow hCfCg
    _ = 4 * (2 * M2 * min z 1) * (Ce * Work.FTS.Regularity.pExp α * (z / (1 + z) ^ 2)) := by ring

theorem Pp5_bound {α Ce M2 : ℝ} (hCe0 : 0 < Ce) (hM0 : 0 ≤ M2)
    (hβ0 : 0 < Work.FTS.Regularity.pExp α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {σ : ℝ}
    (hps : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ)))
      Work.FTS.EllipticEst.Q0)
    (hRop : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a
        (Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ)) z θ|
        ≤ M2 * min z 1)
    (hFh : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i Fhf z θ| ≤ Ce * (z / (1 + z) ^ 2)) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Pp5 α Φs E g σ) z θ|
        ≤ 4 * (2 * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2)) := by
  intro j i hji z θ hz hθ0 hθ1
  have hf : ContDiffOn ℝ (j + i) (Function.uncurry (fun z θ =>
      (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := (-2 : ℝ))).mul
      ((hps.of_le (Nat.cast_le.mpr hji)).congr
        (fun p _ => by simp only [Function.uncurry]))
  have hh : ContDiffOn ℝ (j + i) (Function.uncurry Fhf) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_Fhf (j + i)
  have hfun : (fun z θ => -2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
      (PtF α Φs E g σ) z θ) = fun z θ => (-2 : ℝ)
        * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ := by
    funext z θ; ring
  have hbf : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a (fun z θ =>
      -2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ) z θ|
        ≤ 2 * M2 * min z 1 := by
    intro a b hab
    rw [hfun, mixed_const_mul]
    have habs : |(-2 : ℝ) * Work.Spaces.mixed b a
        (Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ)) z θ|
        = 2 * |Work.Spaces.mixed b a
            (Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ)) z θ| := by
      rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    rw [habs]
    have h2 := hRop a b (by omega) z θ hz hθ0 hθ1
    calc 2 * |Work.Spaces.mixed b a
          (Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ)) z θ|
        ≤ 2 * (M2 * min z 1) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * M2 * min z 1 := by ring
  have hbh : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a Fhf z θ|
      ≤ Ce * (z / (1 + z) ^ 2) := fun a b hab => hFh b a (by omega) z θ hz hθ0 hθ1
  have hmain := abs_mixed_mul_bound (j := j) (i := i) (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 hf hh (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from
      ⟨hz, hθ0, hθ1⟩) (by positivity) (by positivity) hbf hbh
  refine le_trans hmain ?_
  have hpow : (2 : ℝ) ^ (j + i) ≤ 4 := by
    calc (2 : ℝ) ^ (j + i) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
      _ = 4 := by norm_num
  have hCfCg : 0 ≤ (2 * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2)) := by positivity
  calc (2 : ℝ) ^ (j + i) * ((2 * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2)))
      ≤ 4 * ((2 * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_right hpow hCfCg
    _ = 4 * (2 * M2 * min z 1) * (Ce * (z / (1 + z) ^ 2)) := by ring

end Work.FTS_RegExport.RXT.Sys
