import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.VolterraLong.Main
import Submission.Work.OddVolterra.Existence.JetBound
import Submission.Work.OddVolterra.Existence.data_eq_zero_of_eventuallyEq_zero
import Submission.Work.OddVolterra.Existence.xi_close_of_small

/-!
# (Reconstructed) The diagonal data of the odd Volterra system

**Provenance.**  The source of this module is missing from the seed, while its compiled artifact
was present and every importer of it was therefore an orphan.  The declarations below were
recovered from that artifact and then made to compile again: the large proof terms were taken
over verbatim (`G2_diag`, `exists_baseState_bound`, `norm_apply_le_fin4`,
`Kvec_diag_sub_apply_zero`, `abs_two_terms_le`) and the remaining ones were re-proved by hand
(`neg_pow_div_sqrt`, `K1_diag_eq`, `K2_diag_eq`, `continuous_diagPhi1/2`,
`exists_diagPhi_close`, `Kvec_diag_sub_apply_one`).  Only `godd_close_of_small`, whose recovered
proof term no longer elaborated and which nothing that compiles consumes, is not restored.

Contents: the explicit form of the diagonal Abel kernels (`diagPhi1`, `diagPhi2`,
`K1_diag_eq`, `K2_diag_eq`, `G2_diag`), their uniform continuity on bounded boxes
(`exists_diagPhi_close`), the bound on the base state (`exists_baseState_bound`) and the
auxiliary estimates `abs_two_terms_le`, `norm_apply_le_fin4`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Real

/-- The elementary identity behind the explicit form of the diagonal kernels. -/
theorem Work.OddVolterra.Existence.neg_pow_div_sqrt (n : ℕ) (x : ℝ) :
    (-x) ^ (n + 1) / Real.sqrt (2 * x) =
      (-1 : ℝ) ^ (n + 1) * x ^ n * Real.sqrt x / Real.sqrt 2 := by
  by_cases hx : x ≤ 0
  · have h1 : Real.sqrt (2 * x) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have h2 : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hx
    rw [h1, h2]; ring
  · have hx0 : 0 < x := not_le.mp hx
    have hsq : Real.sqrt x * Real.sqrt x = x := by rw [← sq, Real.sq_sqrt hx0.le]
    have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
    have hs2x : Real.sqrt (2 * x) = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    have hxdiv : x / Real.sqrt x = Real.sqrt x := by
      rw [div_eq_iff hsx]; exact hsq.symm
    have hxx : x ^ (n + 1) / Real.sqrt x = x ^ n * Real.sqrt x := by
      rw [pow_succ, mul_div_assoc, hxdiv]
    rw [hs2x, neg_pow]
    rw [show (-1 : ℝ) ^ (n + 1) * x ^ (n + 1) / (Real.sqrt 2 * Real.sqrt x)
        = (-1 : ℝ) ^ (n + 1) * (x ^ (n + 1) / Real.sqrt x) / Real.sqrt 2 by
      rw [div_mul_eq_div_div]; ring]
    rw [hxx]
    ring

/-- The first diagonal kernel in explicit form. -/
noncomputable def Work.OddVolterra.Existence.diagPhi1 (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * ↑(2 * n + 1).doubleFactorial * (p.1 * p.2) ^ n * Real.sqrt (p.1 * p.2) /
    Real.sqrt 2

/-- The second diagonal kernel in explicit form. -/
noncomputable def Work.OddVolterra.Existence.diagPhi2 (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (-1 : ℝ) ^ n * ↑(2 * n - 1).doubleFactorial * (p.1 * p.2) ^ (n - 1) *
    Real.sqrt (p.1 * p.2) * p.2 / Real.sqrt 2

theorem Work.OddVolterra.Existence.K1_diag_eq (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    Work.OddVolterra.K1 n h s s t =
      Work.OddVolterra.Existence.diagPhi1 n
        (Work.OddVolterra.line h s t, Work.OddVolterra.lineSlope h s t) := by
  set L : ℝ := Work.OddVolterra.line h s t with hL
  set S : ℝ := Work.OddVolterra.lineSlope h s t with hS
  have hKden : Work.OddVolterra.Kden h s s t = Real.sqrt (S * (2 * L)) := by
    rw [Work.OddVolterra.Kden, Work.OddVolterra.hquot_self]
    congr 1
    simp only [hL, hS, Work.OddVolterra.line, Work.OddVolterra.lineSlope]
    ring
  have hJ1 : Work.OddVolterra.J1 n h s s t =
      ↑(2 * n + 1).doubleFactorial * (-(L * S)) ^ (n + 1) := by
    rw [Work.OddVolterra.J1, if_pos rfl]
  rw [Work.OddVolterra.K1, hKden, hJ1]
  have hsq : Real.sqrt (S * (2 * L)) = Real.sqrt (2 * (L * S)) := by congr 1; ring
  rw [hsq, mul_div_assoc, Work.OddVolterra.Existence.neg_pow_div_sqrt n (L * S)]
  simp only [Work.OddVolterra.Existence.diagPhi1]
  ring

theorem Work.OddVolterra.Existence.K2_diag_eq (n : ℕ) (hn : 1 ≤ n) (h : ℝ → ℝ) (s t : ℝ) :
    Work.OddVolterra.K2 n h s s t =
      Work.OddVolterra.Existence.diagPhi2 n
        (Work.OddVolterra.line h s t, Work.OddVolterra.lineSlope h s t) := by
  set L : ℝ := Work.OddVolterra.line h s t with hL
  set S : ℝ := Work.OddVolterra.lineSlope h s t with hS
  have hKden : Work.OddVolterra.Kden h s s t = Real.sqrt (S * (2 * L)) := by
    rw [Work.OddVolterra.Kden, Work.OddVolterra.hquot_self]
    congr 1
    simp only [hL, hS, Work.OddVolterra.line, Work.OddVolterra.lineSlope]
    ring
  have hJ2 : Work.OddVolterra.J2 n h s s t =
      ↑(2 * n - 1).doubleFactorial * (-(L * S)) ^ n * S := by
    rw [Work.OddVolterra.J2, if_pos rfl]
  rw [Work.OddVolterra.K2, hKden, hJ2]
  have hsq : Real.sqrt (S * (2 * L)) = Real.sqrt (2 * (L * S)) := by congr 1; ring
  rw [hsq]
  have hstep : (↑(2 * n - 1).doubleFactorial * (-(L * S)) ^ n * S) / Real.sqrt (2 * (L * S))
      = ↑(2 * n - 1).doubleFactorial * S * ((-(L * S)) ^ n / Real.sqrt (2 * (L * S))) := by
    rw [mul_div_assoc]; ring
  rw [hstep]
  have hcore := Work.OddVolterra.Existence.neg_pow_div_sqrt (n - 1) (L * S)
  have hn1 : (n - 1) + 1 = n := by omega
  rw [hn1] at hcore
  rw [hcore]
  simp only [Work.OddVolterra.Existence.diagPhi2]
  ring

theorem Work.OddVolterra.Existence.continuous_diagPhi1 (n : ℕ) :
    Continuous (Work.OddVolterra.Existence.diagPhi1 n) := by
  unfold Work.OddVolterra.Existence.diagPhi1; fun_prop

theorem Work.OddVolterra.Existence.continuous_diagPhi2 (n : ℕ) :
    Continuous (Work.OddVolterra.Existence.diagPhi2 n) := by
  unfold Work.OddVolterra.Existence.diagPhi2; fun_prop

theorem Work.OddVolterra.Existence.exists_diagPhi_close (n : ℕ) {B η : ℝ} (hB : 0 ≤ B)
    (hη : 0 < η) :
    ∃ θ, 0 < θ ∧ ∀ (u u' v v' : ℝ), |u| ≤ B → |u'| ≤ B → |v| ≤ B → |v'| ≤ B →
      |u - u'| < θ → |v - v'| < θ →
      |Work.OddVolterra.Existence.diagPhi1 n (u, v) -
          Work.OddVolterra.Existence.diagPhi1 n (u', v')| < η ∧
      |Work.OddVolterra.Existence.diagPhi2 n (u, v) -
          Work.OddVolterra.Existence.diagPhi2 n (u', v')| < η := by
  have hK : IsCompact (Set.Icc (-B) B ×ˢ Set.Icc (-B) B) := isCompact_Icc.prod isCompact_Icc
  have huc1 := IsCompact.uniformContinuousOn_of_continuous hK
    (Work.OddVolterra.Existence.continuous_diagPhi1 n).continuousOn
  have huc2 := IsCompact.uniformContinuousOn_of_continuous hK
    (Work.OddVolterra.Existence.continuous_diagPhi2 n).continuousOn
  obtain ⟨θ1, hθ1, h1⟩ := Metric.uniformContinuousOn_iff.mp huc1 η hη
  obtain ⟨θ2, hθ2, h2⟩ := Metric.uniformContinuousOn_iff.mp huc2 η hη
  refine ⟨min θ1 θ2, lt_min hθ1 hθ2, ?_⟩
  intro u u' v v' hu hu' hv hv' hdu hdv
  have huK : (u, v) ∈ Set.Icc (-B) B ×ˢ Set.Icc (-B) B := ⟨abs_le.mp hu, abs_le.mp hv⟩
  have huK' : (u', v') ∈ Set.Icc (-B) B ×ˢ Set.Icc (-B) B := ⟨abs_le.mp hu', abs_le.mp hv'⟩
  have hdist : dist (u, v) (u', v') < min θ1 θ2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hdu hdv
  constructor
  · have h := h1 (u, v) huK (u', v') huK' (lt_of_lt_of_le hdist (min_le_left _ _))
    simpa [Real.dist_eq, abs_sub_comm] using h
  · have h := h2 (u, v) huK (u', v') huK' (lt_of_lt_of_le hdist (min_le_right _ _))
    simpa [Real.dist_eq, abs_sub_comm] using h

theorem Work.OddVolterra.Existence.G2_diag : ∀ (n : ℕ) (h : ℝ → ℝ) (s x y x' y' : ℝ),
  Work.OddVolterra.G2 n h s s x y x' y' = fun i =>
    Work.OddVolterra.Kvec n h s s x y x' y' i * ∫ (τ : ℝ) in 0..1, (√(τ * (1 - τ)))⁻¹ :=
fun n h s x y x' y' =>
  funext fun i =>
    id
      (have hfun :=
        funext fun τ =>
          Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  Work.OddVolterra.Kvec n h _a s x y x' y' i / √(τ * (1 - τ)) =
                    Work.OddVolterra.Kvec n h s s x y x' y' i * (√(τ * (1 - τ)))⁻¹)
                (have this :=
                  Mathlib.Tactic.Ring.of_eq
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf s rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => s ^ Nat.rawCast 1 * Nat.rawCast 1 = s ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (s ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf τ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => τ ^ Nat.rawCast 1 * Nat.rawCast 1 = τ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (τ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.sub_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf s rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => s ^ Nat.rawCast 1 * Nat.rawCast 1 = s ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (s ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf s rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => s ^ Nat.rawCast 1 * Nat.rawCast 1 = s ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (s ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.sub_pf
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul s (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1)))))
                              Mathlib.Tactic.Ring.Common.neg_zero)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                              (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero s (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_zero (τ ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.zero_mul 0) (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero (s ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                    (Mathlib.Tactic.Ring.Common.atom_pf s rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => s ^ Nat.rawCast 1 * Nat.rawCast 1 = s ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (s ^ Nat.rawCast 1 * Nat.rawCast 1))));
                this)))
            (Eq.mpr
              (id
                (congrArg (fun _a => _a = Work.OddVolterra.Kvec n h s s x y x' y' i * (√(τ * (1 - τ)))⁻¹)
                  (div_eq_mul_inv (Work.OddVolterra.Kvec n h s s x y x' y' i) √(τ * (1 - τ)))))
              (Eq.refl (Work.OddVolterra.Kvec n h s s x y x' y' i * (√(τ * (1 - τ)))⁻¹)));
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              intervalIntegral _a 0 1 MeasureTheory.volume =
                Work.OddVolterra.Kvec n h s s x y x' y' i * ∫ (τ : ℝ) in 0..1, (√(τ * (1 - τ)))⁻¹)
            hfun))
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = Work.OddVolterra.Kvec n h s s x y x' y' i * ∫ (τ : ℝ) in 0..1, (√(τ * (1 - τ)))⁻¹)
              (intervalIntegral.integral_const_mul (Work.OddVolterra.Kvec n h s s x y x' y' i) fun τ =>
                (√(τ * (1 - τ)))⁻¹)))
          (Eq.refl (Work.OddVolterra.Kvec n h s s x y x' y' i * ∫ (x : ℝ) in 0..1, (√(x * (1 - x)))⁻¹))))

theorem Work.OddVolterra.Existence.exists_baseState_bound : ∀ {a : ℝ},
  a ≤ 1 →
    ∃ B,
      1 ≤ B ∧
        ∀ s ∈ Set.Icc a 1,
          |Work.OddVolterra.baseState s 0| ≤ B ∧
            |Work.OddVolterra.baseState s 1| ≤ B ∧
              |Work.OddVolterra.baseState s 2| ≤ B ∧ |Work.OddVolterra.baseState s 3| ≤ B :=
fun {a} ha =>
  have h1 :=
    Continuous.continuousOn
      (Continuous.abs (ContDiff.continuous Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX));
  have h2 :=
    Continuous.continuousOn
      (Continuous.abs
        (ContDiff.continuous_deriv Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
          (of_eq_true (Eq.trans WithTop.one_le_coe._simp_2 le_top._simp_2))));
  Exists.casesOn (IsCompact.exists_bound_of_continuousOn isCompact_Icc h1) fun B1 hB1 =>
    Exists.casesOn (IsCompact.exists_bound_of_continuousOn isCompact_Icc h2) fun B2 hB2 =>
      Exists.intro (max (max B1 B2) 1)
        ⟨le_max_right (max B1 B2) 1, fun s hs =>
          have hb1 :=
            le_trans (Eq.mp (congrFun' (congrArg LE.le (abs_abs (Commons.Geometry.Ulam.profileX s))) B1) (hB1 s hs))
              (le_trans (le_max_left B1 B2) (le_max_left (max B1 B2) 1));
          have hb2 :=
            le_trans
              (Eq.mp (congrFun' (congrArg LE.le (abs_abs (deriv Commons.Geometry.Ulam.profileX s))) B2) (hB2 s hs))
              (le_trans (le_max_right B1 B2) (le_max_left (max B1 B2) 1));
          ⟨id hb1, ⟨id hb1, ⟨id hb2, id hb2⟩⟩⟩⟩

theorem Work.OddVolterra.Existence.norm_apply_le_fin4 : ∀ (z : Work.OddVolterra.St) (i : Fin 4), |z i| ≤ ‖z‖ :=
fun z i => norm_le_pi_norm z i

theorem Work.OddVolterra.Existence.Kvec_diag_sub_apply_zero : ∀ (n : ℕ) (h₁ h₂ : ℝ → ℝ) (s : ℝ)
  (z : Work.OddVolterra.St),
  Work.OddVolterra.Kvec n h₁ s s (z 0) (z 1) (z 2) (z 3) 0 - Work.OddVolterra.Kvec n h₂ s s (z 0) (z 1) (z 2) (z 3) 0 =
    -((Work.OddVolterra.K1 n h₁ s s (-z 0) - Work.OddVolterra.K1 n h₂ s s (-z 0)) * z 2 +
        (Work.OddVolterra.K1 n h₁ s s (z 1) - Work.OddVolterra.K1 n h₂ s s (z 1)) * z 3) :=
fun n h₁ h₂ s z =>
  id
    (of_eq_true
      (Eq.trans
        (congr
          (congrArg Eq
            (Eq.trans
              (Mathlib.Tactic.Ring.Common.sub_congr
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₁ s s (-z 0)) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (z 2) rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => z 2 ^ Nat.rawCast 1 * Nat.rawCast 1 = z 2 ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₁ s s (-z 0)) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_right (z 2) (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 1)))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                                (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₁ s s (z 1)) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (z 3) rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => z 3 ^ Nat.rawCast 1 * Nat.rawCast 1 = z 3 ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₁ s s (z 1)) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_right (z 3) (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 1)))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                                (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                      (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₁ s s (-z 0)) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.neg_mul (z 2) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))))
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₁ s s (z 1)) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.neg_mul (z 3) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1))))))
                      Mathlib.Tactic.Ring.Common.neg_zero)))
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₂ s s (-z 0)) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (z 2) rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => z 2 ^ Nat.rawCast 1 * Nat.rawCast 1 = z 2 ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_right (z 2) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₂ s s (-z 0))
                              (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 1)))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (z 2 ^ Nat.rawCast 1 *
                                (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₂ s s (z 1)) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (z 3) rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => z 3 ^ Nat.rawCast 1 * Nat.rawCast 1 = z 3 ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_right (z 3) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₂ s s (z 1)) (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 1)))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (z 3 ^ Nat.rawCast 1 *
                                (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                      (z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (z 2) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (-z 0)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))))
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul (z 3) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (z 1)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1))))))
                      Mathlib.Tactic.Ring.Common.neg_zero)))
                (Mathlib.Tactic.Ring.Common.sub_pf
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (z 2) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (-z 0)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 1)))))))
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul (z 3) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (z 1)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 1)))))))
                      Mathlib.Tactic.Ring.Common.neg_zero))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                    (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                      (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_gt
                      (z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                          (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                            0)))))))
              (Eq.trans
                (Mathlib.Tactic.RingNF.add_assoc_rev
                  (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                    (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                  (z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                  (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                      (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                    (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                (Eq.trans
                  (Mathlib.Tactic.RingNF.add_assoc_rev
                    (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                        (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                      z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                    (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                      (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                    (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))
                  (Eq.trans
                    (Mathlib.Tactic.RingNF.add_assoc_rev
                      (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                            (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                        Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                          (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                      (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1)) 0)
                    (Eq.trans
                      (congrFun'
                        (congrArg HAdd.hAdd
                          (congr
                            (congrArg HAdd.hAdd
                              (Eq.trans
                                (congr
                                  (congrArg HAdd.hAdd
                                    (congr
                                      (congrArg HAdd.hAdd
                                        (Eq.trans
                                          (Mathlib.Tactic.RingNF.mul_assoc_rev
                                            (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1) (z 2 ^ Nat.rawCast 1)
                                            (Int.negOfNat 1).rawCast)
                                          (Eq.trans
                                            (Eq.trans
                                              (congr
                                                (congrArg HMul.hMul
                                                  (congr
                                                    (congrArg HMul.hMul
                                                      (Eq.trans
                                                        (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₁ s s (-z 0)))
                                                          Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                        (pow_one (Work.OddVolterra.K1 n h₁ s s (-z 0)))))
                                                    (Eq.trans
                                                      (congrArg (HPow.hPow (z 2)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                      (pow_one (z 2)))))
                                                (Eq.trans Mathlib.Tactic.RingNF.int_rawCast_neg
                                                  (congrArg Neg.neg Mathlib.Tactic.RingNF.nat_rawCast_1)))
                                              (Mathlib.Tactic.RingNF.mul_neg (Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2)
                                                1))
                                            (congrArg Neg.neg (mul_one (Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2))))))
                                      (Eq.trans
                                        (Mathlib.Tactic.RingNF.mul_assoc_rev (z 2 ^ Nat.rawCast 1)
                                          (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1) (Nat.rawCast 1))
                                        (Eq.trans
                                          (congr
                                            (congrArg HMul.hMul
                                              (congr
                                                (congrArg HMul.hMul
                                                  (Eq.trans
                                                    (congrArg (HPow.hPow (z 2)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                    (pow_one (z 2))))
                                                (Eq.trans
                                                  (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₂ s s (-z 0)))
                                                    Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                  (pow_one (Work.OddVolterra.K1 n h₂ s s (-z 0))))))
                                            Mathlib.Tactic.RingNF.nat_rawCast_1)
                                          (mul_one (z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0)))))))
                                  (Eq.trans
                                    (Mathlib.Tactic.RingNF.mul_assoc_rev
                                      (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1) (z 3 ^ Nat.rawCast 1)
                                      (Int.negOfNat 1).rawCast)
                                    (Eq.trans
                                      (Eq.trans
                                        (congr
                                          (congrArg HMul.hMul
                                            (congr
                                              (congrArg HMul.hMul
                                                (Eq.trans
                                                  (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₁ s s (z 1)))
                                                    Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                  (pow_one (Work.OddVolterra.K1 n h₁ s s (z 1)))))
                                              (Eq.trans (congrArg (HPow.hPow (z 3)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                (pow_one (z 3)))))
                                          (Eq.trans Mathlib.Tactic.RingNF.int_rawCast_neg
                                            (congrArg Neg.neg Mathlib.Tactic.RingNF.nat_rawCast_1)))
                                        (Mathlib.Tactic.RingNF.mul_neg (Work.OddVolterra.K1 n h₁ s s (z 1) * z 3) 1))
                                      (congrArg Neg.neg (mul_one (Work.OddVolterra.K1 n h₁ s s (z 1) * z 3))))))
                                (Mathlib.Tactic.RingNF.add_neg
                                  (-(Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2) +
                                    z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0))
                                  (Work.OddVolterra.K1 n h₁ s s (z 1) * z 3))))
                            (Eq.trans
                              (Mathlib.Tactic.RingNF.mul_assoc_rev (z 3 ^ Nat.rawCast 1)
                                (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1) (Nat.rawCast 1))
                              (Eq.trans
                                (congr
                                  (congrArg HMul.hMul
                                    (congr
                                      (congrArg HMul.hMul
                                        (Eq.trans (congrArg (HPow.hPow (z 3)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                          (pow_one (z 3))))
                                      (Eq.trans
                                        (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₂ s s (z 1)))
                                          Mathlib.Tactic.RingNF.nat_rawCast_1)
                                        (pow_one (Work.OddVolterra.K1 n h₂ s s (z 1))))))
                                  Mathlib.Tactic.RingNF.nat_rawCast_1)
                                (mul_one (z 3 * Work.OddVolterra.K1 n h₂ s s (z 1)))))))
                        0)
                      (add_zero
                        (-(Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2) + z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0) -
                            Work.OddVolterra.K1 n h₁ s s (z 1) * z 3 +
                          z 3 * Work.OddVolterra.K1 n h₂ s s (z 1)))))))))
          (Eq.trans
            (Mathlib.Tactic.Ring.Common.neg_congr
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₁ s s (-z 0)) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₂ s s (-z 0)) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (-z 0)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (z 2) rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => z 2 ^ Nat.rawCast 1 * Nat.rawCast 1 = z 2 ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₁ s s (-z 0)) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (z 2) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero
                        (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (z 2) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₂ s s (-z 0)) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1))))))
                        (Mathlib.Tactic.Ring.Common.mul_zero
                          (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (z 2 ^ Nat.rawCast 1 *
                              (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                            0)))
                      (Mathlib.Tactic.Ring.Common.zero_mul (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (z 2 ^ Nat.rawCast 1 *
                            (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                      (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (z 2 ^ Nat.rawCast 1 *
                            (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₁ s s (z 1)) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (Work.OddVolterra.K1 n h₂ s s (z 1)) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (z 1)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (z 3) rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => z 3 ^ Nat.rawCast 1 * Nat.rawCast 1 = z 3 ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₁ s s (z 1)) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (z 3) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero
                        (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (z 3) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.mul_pf_left (Work.OddVolterra.K1 n h₂ s s (z 1)) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1))))))
                        (Mathlib.Tactic.Ring.Common.mul_zero
                          (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (z 3 ^ Nat.rawCast 1 *
                              (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                            0)))
                      (Mathlib.Tactic.Ring.Common.zero_mul (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (z 3 ^ Nat.rawCast 1 *
                            (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                      (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (z 3 ^ Nat.rawCast 1 *
                            (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * (z 2 ^ Nat.rawCast 1 * Nat.rawCast 1))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                    (z 2 ^ Nat.rawCast 1 *
                      (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * (z 3 ^ Nat.rawCast 1 * Nat.rawCast 1) +
                        (z 3 ^ Nat.rawCast 1 *
                            (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0))))))
              (Mathlib.Tactic.Ring.Common.neg_add
                (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₁ s s (-z 0)) (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.neg_mul (z 2) (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.negOfNat 1))))))
                (Mathlib.Tactic.Ring.Common.neg_add
                  (Mathlib.Tactic.Ring.Common.neg_mul (z 2) (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (-z 0)) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 1)))))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₁ s s (z 1)) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.neg_mul (z 3) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))))
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul (z 3) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.neg_mul (Work.OddVolterra.K1 n h₂ s s (z 1)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 1)))))))
                      Mathlib.Tactic.Ring.Common.neg_zero)))))
            (Eq.trans
              (Mathlib.Tactic.RingNF.add_assoc_rev
                (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 * (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                (z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 * (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                  (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
              (Eq.trans
                (Mathlib.Tactic.RingNF.add_assoc_rev
                  (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                      (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                    z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1))
                  (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                    (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                  (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))
                (Eq.trans
                  (Mathlib.Tactic.RingNF.add_assoc_rev
                    (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1 *
                          (z 2 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                        z 2 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                      Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1 *
                        (z 3 ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                    (z 3 ^ Nat.rawCast 1 * (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1 * Nat.rawCast 1)) 0)
                  (Eq.trans
                    (congrFun'
                      (congrArg HAdd.hAdd
                        (congr
                          (congrArg HAdd.hAdd
                            (Eq.trans
                              (congr
                                (congrArg HAdd.hAdd
                                  (congr
                                    (congrArg HAdd.hAdd
                                      (Eq.trans
                                        (Mathlib.Tactic.RingNF.mul_assoc_rev
                                          (Work.OddVolterra.K1 n h₁ s s (-z 0) ^ Nat.rawCast 1) (z 2 ^ Nat.rawCast 1)
                                          (Int.negOfNat 1).rawCast)
                                        (Eq.trans
                                          (Eq.trans
                                            (congr
                                              (congrArg HMul.hMul
                                                (congr
                                                  (congrArg HMul.hMul
                                                    (Eq.trans
                                                      (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₁ s s (-z 0)))
                                                        Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                      (pow_one (Work.OddVolterra.K1 n h₁ s s (-z 0)))))
                                                  (Eq.trans
                                                    (congrArg (HPow.hPow (z 2)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                    (pow_one (z 2)))))
                                              (Eq.trans Mathlib.Tactic.RingNF.int_rawCast_neg
                                                (congrArg Neg.neg Mathlib.Tactic.RingNF.nat_rawCast_1)))
                                            (Mathlib.Tactic.RingNF.mul_neg (Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2)
                                              1))
                                          (congrArg Neg.neg (mul_one (Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2))))))
                                    (Eq.trans
                                      (Mathlib.Tactic.RingNF.mul_assoc_rev (z 2 ^ Nat.rawCast 1)
                                        (Work.OddVolterra.K1 n h₂ s s (-z 0) ^ Nat.rawCast 1) (Nat.rawCast 1))
                                      (Eq.trans
                                        (congr
                                          (congrArg HMul.hMul
                                            (congr
                                              (congrArg HMul.hMul
                                                (Eq.trans
                                                  (congrArg (HPow.hPow (z 2)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                  (pow_one (z 2))))
                                              (Eq.trans
                                                (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₂ s s (-z 0)))
                                                  Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                (pow_one (Work.OddVolterra.K1 n h₂ s s (-z 0))))))
                                          Mathlib.Tactic.RingNF.nat_rawCast_1)
                                        (mul_one (z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0)))))))
                                (Eq.trans
                                  (Mathlib.Tactic.RingNF.mul_assoc_rev
                                    (Work.OddVolterra.K1 n h₁ s s (z 1) ^ Nat.rawCast 1) (z 3 ^ Nat.rawCast 1)
                                    (Int.negOfNat 1).rawCast)
                                  (Eq.trans
                                    (Eq.trans
                                      (congr
                                        (congrArg HMul.hMul
                                          (congr
                                            (congrArg HMul.hMul
                                              (Eq.trans
                                                (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₁ s s (z 1)))
                                                  Mathlib.Tactic.RingNF.nat_rawCast_1)
                                                (pow_one (Work.OddVolterra.K1 n h₁ s s (z 1)))))
                                            (Eq.trans (congrArg (HPow.hPow (z 3)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                              (pow_one (z 3)))))
                                        (Eq.trans Mathlib.Tactic.RingNF.int_rawCast_neg
                                          (congrArg Neg.neg Mathlib.Tactic.RingNF.nat_rawCast_1)))
                                      (Mathlib.Tactic.RingNF.mul_neg (Work.OddVolterra.K1 n h₁ s s (z 1) * z 3) 1))
                                    (congrArg Neg.neg (mul_one (Work.OddVolterra.K1 n h₁ s s (z 1) * z 3))))))
                              (Mathlib.Tactic.RingNF.add_neg
                                (-(Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2) +
                                  z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0))
                                (Work.OddVolterra.K1 n h₁ s s (z 1) * z 3))))
                          (Eq.trans
                            (Mathlib.Tactic.RingNF.mul_assoc_rev (z 3 ^ Nat.rawCast 1)
                              (Work.OddVolterra.K1 n h₂ s s (z 1) ^ Nat.rawCast 1) (Nat.rawCast 1))
                            (Eq.trans
                              (congr
                                (congrArg HMul.hMul
                                  (congr
                                    (congrArg HMul.hMul
                                      (Eq.trans (congrArg (HPow.hPow (z 3)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                        (pow_one (z 3))))
                                    (Eq.trans
                                      (congrArg (HPow.hPow (Work.OddVolterra.K1 n h₂ s s (z 1)))
                                        Mathlib.Tactic.RingNF.nat_rawCast_1)
                                      (pow_one (Work.OddVolterra.K1 n h₂ s s (z 1))))))
                                Mathlib.Tactic.RingNF.nat_rawCast_1)
                              (mul_one (z 3 * Work.OddVolterra.K1 n h₂ s s (z 1)))))))
                      0)
                    (add_zero
                      (-(Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2) + z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0) -
                          Work.OddVolterra.K1 n h₁ s s (z 1) * z 3 +
                        z 3 * Work.OddVolterra.K1 n h₂ s s (z 1)))))))))
        (eq_self
          (-(Work.OddVolterra.K1 n h₁ s s (-z 0) * z 2) + z 2 * Work.OddVolterra.K1 n h₂ s s (-z 0) -
              Work.OddVolterra.K1 n h₁ s s (z 1) * z 3 +
            z 3 * Work.OddVolterra.K1 n h₂ s s (z 1)))))

theorem Work.OddVolterra.Existence.Kvec_diag_sub_apply_one (n : ℕ) (h₁ h₂ : ℝ → ℝ) (s : ℝ)
    (z : Work.OddVolterra.St) :
    Work.OddVolterra.Kvec n h₁ s s (z 0) (z 1) (z 2) (z 3) 1 -
        Work.OddVolterra.Kvec n h₂ s s (z 0) (z 1) (z 2) (z 3) 1 =
      -((Work.OddVolterra.K2 n h₁ s s (-(z 0)) - Work.OddVolterra.K2 n h₂ s s (-(z 0))) * z 2 +
        (Work.OddVolterra.K2 n h₁ s s (z 1) - Work.OddVolterra.K2 n h₂ s s (z 1)) * z 3) := by
  simp only [Work.OddVolterra.Kvec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_fin_one]
  ring

theorem Work.OddVolterra.Existence.abs_two_terms_le : ∀ {a b x y tol Q : ℝ},
  |a| < tol → |b| < tol → |x| ≤ Q → |y| ≤ Q → 0 ≤ tol → |a * x + b * y| ≤ 2 * tol * Q :=
fun {a b x y tol Q} ha hb hx hy htol =>
  Trans.trans
    (Trans.trans
      (Trans.trans (abs_add_le (a * x) (b * y))
        (Eq.mpr (id (congrArg (fun _a => _a + |b * y| = |a| * |x| + |b| * |y|) (abs_mul a x)))
          (Eq.mpr (id (congrArg (fun _a => |a| * |x| + _a = |a| * |x| + |b| * |y|) (abs_mul b y)))
            (Eq.refl (|a| * |x| + |b| * |y|)))))
      (add_le_add (mul_le_mul (le_of_lt ha) hx (abs_nonneg x) htol) (mul_le_mul (le_of_lt hb) hy (abs_nonneg y) htol)))
    (Mathlib.Tactic.Ring.of_eq
      (Mathlib.Tactic.Ring.Common.add_congr
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.Common.atom_pf tol rfl
            (Eq.mpr
              (id (congrArg (fun _a => tol ^ Nat.rawCast 1 * Nat.rawCast 1 = tol ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (tol ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.atom_pf Q rfl
            (Eq.mpr (id (congrArg (fun _a => Q ^ Nat.rawCast 1 * Nat.rawCast 1 = Q ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (Q ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left tol (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right Q (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
              (Mathlib.Tactic.Ring.Common.mul_zero (tol ^ Nat.rawCast 1 * Nat.rawCast 1))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (tol ^ Nat.rawCast 1 * (Q ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
            (Mathlib.Tactic.Ring.Common.zero_mul (Q ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (tol ^ Nat.rawCast 1 * (Q ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.Common.atom_pf tol rfl
            (Eq.mpr
              (id (congrArg (fun _a => tol ^ Nat.rawCast 1 * Nat.rawCast 1 = tol ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (tol ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.atom_pf Q rfl
            (Eq.mpr (id (congrArg (fun _a => Q ^ Nat.rawCast 1 * Nat.rawCast 1 = Q ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (Q ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left tol (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right Q (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
              (Mathlib.Tactic.Ring.Common.mul_zero (tol ^ Nat.rawCast 1 * Nat.rawCast 1))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (tol ^ Nat.rawCast 1 * (Q ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
            (Mathlib.Tactic.Ring.Common.zero_mul (Q ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (tol ^ Nat.rawCast 1 * (Q ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
        (Mathlib.Tactic.Ring.Common.add_pf_add_overlap
          (Mathlib.Tactic.Ring.Common.add_overlap_pf tol (Nat.rawCast 1)
            (Mathlib.Tactic.Ring.Common.add_overlap_pf Q (Nat.rawCast 1)
              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))
          (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
      (Mathlib.Tactic.Ring.Common.mul_congr
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
          (Mathlib.Tactic.Ring.Common.atom_pf tol rfl
            (Eq.mpr
              (id (congrArg (fun _a => tol ^ Nat.rawCast 1 * Nat.rawCast 1 = tol ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (tol ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_right tol (Nat.rawCast 1)
                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (tol ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
            (Mathlib.Tactic.Ring.Common.zero_mul (tol ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (tol ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
        (Mathlib.Tactic.Ring.Common.atom_pf Q rfl
          (Eq.mpr (id (congrArg (fun _a => Q ^ Nat.rawCast 1 * Nat.rawCast 1 = Q ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
            (Eq.refl (Q ^ Nat.rawCast 1 * Nat.rawCast 1))))
        (Mathlib.Tactic.Ring.Common.add_mul
          (Mathlib.Tactic.Ring.Common.mul_add
            (Mathlib.Tactic.Ring.Common.mul_pf_left tol (Nat.rawCast 1)
              (Mathlib.Tactic.Ring.Common.mul_pf_right Q (Nat.rawCast 1)
                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))
            (Mathlib.Tactic.Ring.Common.mul_zero (tol ^ Nat.rawCast 1 * Nat.rawCast 2))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (tol ^ Nat.rawCast 1 * (Q ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
          (Mathlib.Tactic.Ring.Common.zero_mul (Q ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
            (tol ^ Nat.rawCast 1 * (Q ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))))
