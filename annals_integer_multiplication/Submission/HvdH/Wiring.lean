import Submission.HvdH.Interfaces

/-!
# Wiring (lead-owned): `theorem_1_1` from the area `Prop`s.
`wire` = compiler + multiplication program ⇒ the challenge statement (real proof, incl. the `IsBigO`).
`wired` = every area `Prop` (as hypotheses, in the dependency shape the areas prove them) ⇒ challenge.
-/

set_option autoImplicit false

namespace HvdH

open Computability Turing Real

/-- `m · size m + 1 ≤ 5 · m log m` for `m ≥ 3`. -/
theorem size_bound (m : ℕ) (hm : 3 ≤ m) :
    ((m * m.size + 1 : ℕ) : ℝ) ≤ 5 * ((m : ℝ) * Real.log m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog1 : (1 : ℝ) ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hm0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hsz : 1 ≤ m.size := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.size_eq_zero]; omega
  have hpow : 2 ^ (m.size - 1) ≤ m := by
    by_contra h
    have h' : m < 2 ^ (m.size - 1) := Nat.lt_of_not_le h
    have := Nat.size_le.mpr h'
    omega
  have hpowR : (2 : ℝ) ^ (m.size - 1) ≤ m := by exact_mod_cast hpow
  have hlog2 : ((m.size - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpowR
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hs : ((m.size : ℕ) : ℝ) ≤ 3 * Real.log m := by
    have e : ((m.size - 1 : ℕ) : ℝ) = (m.size : ℝ) - 1 := by
      rw [Nat.cast_sub hsz]; simp
    rw [e] at hlog2
    nlinarith
  have hA : (m : ℝ) * (m.size : ℝ) ≤ (m : ℝ) * (3 * Real.log m) :=
    mul_le_mul_of_nonneg_left hs (le_of_lt hm0)
  have hB : (1 : ℝ) ≤ (m : ℝ) * Real.log m := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  push_cast
  nlinarith

theorem wire (hC : CompilerThm) (hM : MulProgramC) :
    ∃ T : TM2ComputableInTime (IntegerMultiplication.encodeProd encodeNat encodeNat) encodeNat
        (fun (x, y) ↦ x * y),
      (fun n ↦ (T.time n : ℝ)) =O[Filter.atTop] (fun n ↦ n * log n) := by
  obtain ⟨P, C, hrun⟩ := hM
  obtain ⟨T, c, hT⟩ := hC (IntegerMultiplication.encodeProd encodeNat encodeNat)
    (fun a : ℕ × ℕ => encodeNat (a.1 * a.2)) P (fun n => C * (n * n.size + 1)) (fun a => hrun a.1 a.2)
  refine ⟨⟨T.toTM2ComputableAux, T.time, T.outputsFun⟩, ?_⟩
  refine Asymptotics.IsBigO.of_bound (5 * (c * (C + 1) : ℕ)) ?_
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have h1 : T.time n ≤ c * (C + 1) * (n * n.size + 1) := by
    have hsz : 1 ≤ n.size := by
      rw [Nat.one_le_iff_ne_zero, Ne, Nat.size_eq_zero]; omega
    have : n ≤ n * n.size := Nat.le_mul_of_pos_right n hsz
    calc T.time n ≤ c * (C * (n * n.size + 1) + n + 1) := hT n
      _ ≤ c * (C + 1) * (n * n.size + 1) := by
        rw [mul_assoc]; apply Nat.mul_le_mul_left; nlinarith
  have h2 := size_bound n hn
  have hpos : (0 : ℝ) ≤ (n : ℝ) * Real.log n := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hpos]
  calc (T.time n : ℝ) ≤ ((c * (C + 1) * (n * n.size + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((c * (C + 1) : ℕ) : ℝ) * ((n * n.size + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((c * (C + 1) : ℕ) : ℝ) * (5 * ((n : ℝ) * Real.log n)) := by
        apply mul_le_mul_of_nonneg_left h2; positivity
    _ = 5 * ((c * (C + 1) : ℕ) : ℝ) * ((n : ℝ) * Real.log n) := by ring

/-- Every area `Prop`, composed. -/
theorem wired (hComp : CompilerThm) (hKer : KernelLib) (hInt : KernelLib → IntLib)
    (hLay : KernelLib → IntLib → LayoutLib) (hFx : KernelLib → IntLib → FxLib) (hDFT : DFTMathProp)
    (hSyn : KernelLib → IntLib → LayoutLib → FxLib → SynFFTProp)
    (hConv : KernelLib → IntLib → LayoutLib → FxLib → SynFFTProp → ConvRProp)
    (hTr : KernelLib → IntLib → LayoutLib → FxLib → ConvRProp → TransformProp)
    (hResM : ResMath1DProp)
    (hRes : KernelLib → IntLib → LayoutLib → FxLib → DFTMathProp → ResMath1DProp → ResampleProp)
    (hPar : KernelLib → IntLib → ParamsProp)
    (hMain : KernelLib → IntLib → LayoutLib → FxLib → DFTMathProp → TransformProp → ResampleProp →
      ParamsProp → MainStepProp)
    (hRec : RecursionProp) (hAsm : AssemblyProp) :
    ∃ T : TM2ComputableInTime (IntegerMultiplication.encodeProd encodeNat encodeNat) encodeNat
        (fun (x, y) ↦ x * y),
      (fun n ↦ (T.time n : ℝ)) =O[Filter.atTop] (fun n ↦ n * log n) := by
  have I := hInt hKer
  have L := hLay hKer I
  have F := hFx hKer I
  have Sy := hSyn hKer I L F
  have Cv := hConv hKer I L F Sy
  have Tr := hTr hKer I L F Cv
  have Rs := hRes hKer I L F hDFT hResM
  have Pa := hPar hKer I
  have Mn := hMain hKer I L F hDFT Tr Rs Pa
  exact wire hComp (hAsm hKer I Mn hRec)

end HvdH
