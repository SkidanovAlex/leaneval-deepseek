import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.GdotCore` -- local calculus for the `g`-system (S5b, helpers)

Congruence of `D_z`, `D_θ`, `D_z^j`, `D_θ^i` and `mixed` on an open set of the `(z,θ)`-plane,
the `D_θ`-index shift, additivity of `mixed` at order `≤ 2` on the open quadrant, the splitting
of `D_z`/`D_θ` of a function agreeing with a sum `P + G`, the index arithmetic for the six
component pairs `idx`, and the elementary `Finset` estimate lemmas used by
`Work.FTS_RegExport.RXT.Sys.GdotExp.sys_bound`.
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

abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0


/-! ## Local calculus helpers (congruence and linearity on the open quadrant) -/

theorem Dth_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  simp only [Work.Spaces.Dth]
  rw [Work.Spaces.pth_congr_of_isOpen hV h hz]

theorem Dz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  simp only [Work.Spaces.Dz]
  rw [Work.Spaces.pz_congr_of_isOpen hV h hz]

theorem DthIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (k : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DthIter k f))
      (Function.uncurry (Work.Spaces.DthIter k f')) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro p hp
      simp only [Function.uncurry, Work.Spaces.DthIter_succ]
      rw [Dth_congr_of_isOpen hV ih hp]

theorem DzIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (k : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter k f))
      (Function.uncurry (Work.Spaces.DzIter k f')) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro p hp
      simp only [Function.uncurry, Work.Spaces.DzIter_succ]
      rw [Dz_congr_of_isOpen hV ih hp]

theorem mixed_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (j i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i f' z θ := by
  have h1 := DzIter_congr_of_isOpen hV (DthIter_congr_of_isOpen hV h i) j
  exact fun z θ hz => h1 hz

/-- `D_θ^q (D_θ X) = D_θ^{q+1} X`. -/
theorem DthIter_Dth (q : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter q (Work.Spaces.Dth X) = Work.Spaces.DthIter (q + 1) X := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [Work.Spaces.DthIter_succ q (Work.Spaces.Dth X), ih,
        Work.Spaces.DthIter_succ (q + 1) X]

/-- `mixed p q (D_θ X) = mixed p (q+1) X`. -/
theorem mixed_Dth_succ (p q : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed p q (Work.Spaces.Dth X) = Work.Spaces.mixed p (q + 1) X := by
  simp only [Work.Spaces.mixed]
  rw [DthIter_Dth]

/-- Additivity of `mixed` at a point of the open quadrant, at order `≤ 2`. -/
theorem mixed_add_pt {f₁ f₂ : ℝ → ℝ → ℝ}
    (h₁ : ContDiffOn ℝ 2 (Function.uncurry f₁) Q0)
    (h₂ : ContDiffOn ℝ 2 (Function.uncurry f₂) Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed j i (f₁ + f₂) z θ = Work.Spaces.mixed j i f₁ z θ + Work.Spaces.mixed j i f₂ z θ :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
    Work.FTS.EllipticEst.isOpen_Q0 h₁ h₂ i j (Nat.add_comm j i ▸ hji) (z, θ) hzθ

/-- On the open quadrant, `D_z` of a function agreeing with `P + G` splits. -/
theorem Dz_split_of_eqOn {X P G : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Q0)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Q0)
    (h : EqOn (Function.uncurry X)
      (Function.uncurry (fun z θ => P z θ + G z θ)) Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Q0 →
      Work.Spaces.Dz X z θ = Work.Spaces.Dz P z θ + Work.Spaces.Dz G z θ := by
  intro z θ hp
  have hdiffP : DifferentiableAt ℝ (fun z' => P z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hP.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by norm_num))
  have hdiffG : DifferentiableAt ℝ (fun z' => G z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by norm_num))
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Q0 :=
    (Continuous.prodMk_left θ).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  have hslice : (fun z' => X z' θ) =ᶠ[𝓝 z] (fun z' => P z' θ + G z' θ) := by
    filter_upwards [hnb] with z' hz'
    simpa only [Function.uncurry] using h hz'
  have h1 : Work.Spaces.pz X z θ = Work.Spaces.pz P z θ + Work.Spaces.pz G z θ := by
    simp only [Work.Spaces.pz]
    rw [hslice.deriv_eq,
      show (fun z' => P z' θ + G z' θ) = (fun z' => P z' θ) + (fun z' => G z' θ) from rfl,
      deriv_add hdiffP hdiffG]
  simp only [Work.Spaces.Dz]
  rw [h1]
  ring

/-- On the open quadrant, `D_θ` of a function agreeing with `P + G` splits. -/
theorem Dth_split_of_eqOn {X P G : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Q0)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Q0)
    (h : EqOn (Function.uncurry X)
      (Function.uncurry (fun z θ => P z θ + G z θ)) Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Q0 →
      Work.Spaces.Dth X z θ = Work.Spaces.Dth P z θ + Work.Spaces.Dth G z θ := by
  intro z θ hp
  have hdiffP : DifferentiableAt ℝ (fun θ' => P z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hP.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by norm_num))
  have hdiffG : DifferentiableAt ℝ (fun θ' => G z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by norm_num))
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Q0 :=
    (Continuous.prodMk_right z).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  have hslice : (fun θ' => X z θ') =ᶠ[𝓝 θ] (fun θ' => P z θ' + G z θ') := by
    filter_upwards [hnb] with θ' hθ'
    simpa only [Function.uncurry] using h hθ'
  have h1 : Work.Spaces.pth X z θ = Work.Spaces.pth P z θ + Work.Spaces.pth G z θ := by
    simp only [Work.Spaces.pth]
    rw [hslice.deriv_eq,
      show (fun θ' => P z θ' + G z θ') = (fun θ' => P z θ') + (fun θ' => G z θ') from rfl,
      deriv_add hdiffP hdiffG]
  simp only [Work.Spaces.Dth]
  rw [h1]
  ring

/-! ## Index arithmetic and elementary sum bounds -/

/-- Every pair `(p,q)` of total order `≤ 2` is one of the six `idx`-pairs. -/
theorem idx_exists {p q : ℕ} (h : p + q ≤ 2) :
    ∃ t : Fin 6, (idx t).1 = p ∧ (idx t).2 = q := by
  have hp2 : p ≤ 2 := by omega
  have hq2 : q ≤ 2 := by omega
  interval_cases q
  · interval_cases p
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨3, by decide, by decide⟩
  · interval_cases p
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨4, by decide, by decide⟩
    · omega
  · interval_cases p
    · exact ⟨5, by decide, by decide⟩
    · omega
    · omega

/-- Domination of the order-`≤ 2` jets by the `idx`-sum. -/
theorem mixed_le_sum_idx {G : ℝ → ℝ → ℝ} {z θ : ℝ} {p q : ℕ} (h : p + q ≤ 2) :
    |Work.Spaces.mixed p q G z θ| ≤ ∑ t : Fin 6, |Work.Spaces.mixed (idx t).1 (idx t).2 G z θ| := by
  obtain ⟨t, ht1, ht2⟩ := idx_exists h
  rw [← ht1, ← ht2]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun t : Fin 6 => |Work.Spaces.mixed (idx t).1 (idx t).2 G z θ|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ t)

/-- A binomial coefficient of order `≤ 2` is `≤ 2`. -/
theorem choose_le_two {i a : ℕ} (ha : a ≤ i) (hi : i ≤ 2) : i.choose a ≤ 2 := by
  interval_cases i <;> interval_cases a <;> decide

/-- Peel the `(0,0)`-term off a double `range`-sum. -/
theorem sum_peel (s t : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ u ∈ Finset.range (s + 1), ∑ v ∈ Finset.range (t + 1), F u v) - F 0 0
      = (∑ u ∈ Finset.range s, ∑ v ∈ Finset.range (t + 1), F (u + 1) v)
        + (∑ v ∈ Finset.range t, F 0 (v + 1)) := by
  rw [Finset.sum_range_succ' (fun u => ∑ v ∈ Finset.range (t + 1), F u v) s]
  rw [Finset.sum_range_succ' (fun v => F 0 v) t]
  ring

/-- A double `range`-sum with uniformly bounded terms. -/
theorem abs_double_sum_le (s t : ℕ) (F : ℕ → ℕ → ℝ) (K : ℝ)
    (hF : ∀ u ∈ Finset.range s, ∀ v ∈ Finset.range t, |F u v| ≤ K) :
    |∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, F u v| ≤ ((s * t : ℕ) : ℝ) * K := by
  calc |∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, F u v|
      ≤ ∑ u ∈ Finset.range s, |∑ v ∈ Finset.range t, F u v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, |F u v| :=
        Finset.sum_le_sum (fun u _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, K :=
        Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hF u hu v hv))
    _ = ((s * t : ℕ) : ℝ) * K := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- A single `range`-sum with uniformly bounded terms. -/
theorem abs_range_sum_le (t : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hF : ∀ v ∈ Finset.range t, |F v| ≤ K) :
    |∑ v ∈ Finset.range t, F v| ≤ ((t : ℕ) : ℝ) * K := by
  calc |∑ v ∈ Finset.range t, F v| ≤ ∑ v ∈ Finset.range t, |F v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ Finset.range t, K := Finset.sum_le_sum hF
    _ = ((t : ℕ) : ℝ) * K := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Work.FTS_RegExport.RXT.Sys
