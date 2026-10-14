import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## `Lop` is linear -/

/-- `Lop` commutes with multiplication by a constant (`deriv` does so unconditionally: see
`deriv_const_mul_field`). -/
theorem Lop_const_mul (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Lop (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop u θ := by
  funext θ
  rw [Work.Spaces.Lop, Work.Spaces.Lop, deriv_const_mul_field c]
  ring

/-- The iterates of `Lop` commute with multiplication by a constant. -/
theorem LopIter_const_mul (c : ℝ) (n : ℕ) (u : ℝ → ℝ) :
    Work.FTS.EllipticEst.LopIter n (fun θ => c * u θ)
      = fun θ => c * Work.FTS.EllipticEst.LopIter n u θ := by
  show (Work.Spaces.Lop^[n]) (fun θ => c * u θ)
      = fun θ => c * (Work.Spaces.Lop^[n]) u θ
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        Lop_const_mul c ((Work.Spaces.Lop^[n]) u)]

/-! ## The reference pointwise bound, with a constant uniform in the profile -/

theorem angular_summand_sq_le_le_unit (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
    (ha1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a θ| ≤ 1) (hK : ∀ m : ℕ, 0 ≤ K m)
    (hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (i j m : ℕ), α ≤ 1 → 1 ≤ i → i + j ≤ k → m ≤ i →
      ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f i j m hα1 hi1 hij hmi z θ hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hjk : j ≤ k := by omega
  have hmk : m ≤ k := by omega
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have ha2 : (a θ) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ hθIoo) 2
      rwa [sq_abs, one_pow] at h
    have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi1 hij
    have h0c : ((i.choose 0 : ℝ)) = 1 := by simp
    rw [h0c, Nat.sub_zero]
    simp only [Work.FTS.EllipticEst.LopIter_zero, Nat.cast_one, one_mul]
    calc (a θ * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (a θ) ^ 2 * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 1 * Work.Spaces.HkIntegrand α k f z θ :=
          mul_le_mul ha2 hmix (sq_nonneg _) (by norm_num)
      _ ≤ 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          have h1 : (1 : ℝ) ≤ K 0 + 1 := by linarith [hK 0]
          calc (1 : ℝ) * Work.Spaces.HkIntegrand α k f z θ
              ≤ (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ :=
                mul_le_mul_of_nonneg_right h1 hHe
            _ = 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
  · rcases Nat.lt_or_eq_of_le hmi with hlt | heq
    · -- 1 ≤ m < i, so 1 ≤ i - m
      have hpos' : 1 ≤ i - m := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h6 := angular_sq_mul_Wt_sq_le (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        (hK m) hθIoo hd
      have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ (i - m) j hpos' (by omega)
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.mixed j (i - m) f z θ
              * Work.Spaces.Wt α z θ) ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmix (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
    · -- m = i, so i - m = 0
      have hz0 : i - m = 0 := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h7 := angular_sq_mul_Wt_sq_le_radial (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        hα1 (hK m) hθIoo hd
      rw [hz0, Work.Spaces.mixed_zero_right] at h7
      have hz' : (Work.Spaces.DzIter j f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hjk
      rw [hz0, Work.Spaces.mixed_zero_right]
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.DzIter j f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring


end Work.FTS.EllipticEst.Blocks

namespace Work.FTS.Nonlinear.N4Fields

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary: `SmoothOpen` of an angular multiple, and the closed-quadrant transfer -/

/-- Multiplying a `SmoothOpen` function by a `C^∞` angular profile preserves `SmoothOpen`. -/
theorem smoothOpen_angMul {a : ℝ → ℝ} (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * G z θ) := by
  have haG : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
  have haC : ContDiff ℝ Work.Stability.smoothOrder a := haG.of_le le_top
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 :=
    haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => a p.2 * G p.1 p.2) Work.FTS.EllipticEst.Q0 := h1.mul hG
  exact h3

/-- A pointwise bound on the *open* quadrant extends to the *closed* quadrant `Iz ×ˢ Iθ`: on the
two boundary lines `z = 0` and `sin(2θ) = 0` both `ℋ^k`-integrands vanish
(`HkIntegrand_zero_fst`, `HkIntegrand_eq_zero_of_sin_eq_zero`). -/
theorem closed_of_interior {k : ℕ} {a : ℝ → ℝ} {C : ℝ}
    (hint : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f hα hα1 hf z hz θ hθ
  have hzge : (0 : ℝ) ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have hθb : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := by
    simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · rw [← h0, Work.FTS.LocData.HkIntegrand_zero_fst α k (fun z θ => a θ * f z θ) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k (fun z θ => a θ * f z θ) z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z θ hs, mul_zero]
    · have hθ1 : 0 < θ := by
        rcases eq_or_lt_of_le hθb.1 with h | h
        · exact absurd (by rw [← h]; simp) hs
        · exact h
      have hθ2 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθb.2 with h | h
        · exact h
        · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
            Real.sin_pi]) hs
      exact hint α f hα hα1 hf z θ hpos hθ1 hθ2

/-! ## Auxiliary: transfer of `HkSq` along a pointwise domination -/

/-- A pointwise domination of the `ℋ^k`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
theorem HkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-! ## The `B = 0` case: the profile vanishes on `Iθ` -/

/-- If `a` vanishes on `Iθ`, then every `D_θ`-iterate (of order `≥ 1`) of `(z,θ) ↦ a θ · f z θ`
vanishes on `Iz ×ˢ Iθ`.  (`D_θ` carries the factor `sin(2θ)`, which is `0` at the two endpoints
of `Iθ`, and on the open interval the `θ`-slice of `a·f` is locally `0`.) -/
theorem DthIter_angmul_eq_zero (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0) :
    ∀ i : ℕ, 1 ≤ i → ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.DthIter i (fun z θ => a θ * f z θ) z θ = 0 := by
  -- the one-step statement: `D_θ` kills any function vanishing on `Iθ` in the angular variable
  have hstep : ∀ (G : ℝ → ℝ → ℝ), (∀ z θ, θ ∈ Work.Spaces.Iθ → G z θ = 0) →
      ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dth G z θ = 0 := by
    intro G hG z θ hθ
    rw [Work.Spaces.Dth, Work.Spaces.pth]
    by_cases hs : Real.sin (2 * θ) = 0
    · rw [hs, zero_mul]
    · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
        refine ⟨?_, ?_⟩
        · rcases lt_or_eq_of_le hθ.1 with h | h
          · exact h
          · exact absurd (by rw [← h]; simp) hs
        · rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
              Real.sin_pi]) hs
      have hnb : (fun θ' : ℝ => G z θ') =ᶠ[nhds θ] (fun _ => (0 : ℝ)) := by
        have hmem : Work.Spaces.Iθ ∈ nhds θ :=
          Filter.mem_of_superset (Ioo_mem_nhds hθ'.1 hθ'.2)
            (fun θ' (hθ'' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) =>
              (⟨le_of_lt hθ''.1, le_of_lt hθ''.2⟩ : θ' ∈ Work.Spaces.Iθ))
        filter_upwards [hmem] with θ' hθ''
        exact hG z θ' hθ''
      rw [hnb.deriv_eq, deriv_const, mul_zero]
  intro i
  induction i with
  | zero => intro h; omega
  | succ m ih =>
      intro _ z θ hθ
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        exact hstep (fun z θ => a θ * f z θ)
          (fun z θ hθ => by rw [ha0 θ hθ, zero_mul]) z θ hθ
      · rw [Work.Spaces.DthIter_succ]
        exact hstep (Work.Spaces.DthIter m (fun z θ => a θ * f z θ))
          (fun z θ hθ => ih hpos z θ hθ) z θ hθ

/-! ## The corrected field lemma -/


end Work.FTS.Nonlinear.N4Fields
