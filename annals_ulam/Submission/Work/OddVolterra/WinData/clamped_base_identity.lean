import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.WinData.gcl_contDiffOn
import Submission.Work.OddVolterra.WinData.tcl_contDiffOn
import Submission.Work.OddVolterra.WinData.smooth_upgrade
import Submission.Work.OddVolterra.Existence.base_volterra

/-!
# The clamped base identity

For the window construction of the odd case (`Work.OddVolterra.WinData`) one needs the `h = 0`
(unperturbed) case of the clamped Volterra system: the ball's state `baseState` is an exact
solution of the clamped system, together with the `s`-derivative of that identity.

The first conjunct is `base_volterra` split at `19/20`: on the window all cut-offs are `1`, the
clamped `Θ` datum is the manifest kernel `ThetaM`, which agrees with the paper's `Theta` on the
open triangle, and `Xcl` carries the frozen tail `∫_{19/20}^1 ThetaM`.

The second conjunct is the `s`-derivative of that identity.  Its two sides are the functions `FL`
and `FR` below: `FL` is the chain-rule value of `d/ds (Gcl n 0 s (baseState s))` and `FR` is the
Leibniz value of the derivative of the right-hand side (moving lower limit).  They agree on the
open window because both are the derivatives of the two sides of the identity there, and on the
closed window by the one-sided argument at the two endpoints.
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Elementary facts: the zero perturbation and the base state -/

lemma cbi_iteratedDeriv_zero_fun (k : ℕ) (s : ℝ) :
    iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) s = 0 := by
  simp [iteratedDeriv_const]

lemma cbi_hsmall2 (k : ℕ) (hk : k ≤ 2) (s : ℝ) :
    |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) s| ≤ 1 / 100 := by
  rw [cbi_iteratedDeriv_zero_fun]; norm_num

lemma cbi_hsmall1 (k : ℕ) (hk : k ≤ 1) (s : ℝ) :
    |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) s| ≤ 1 / 100 :=
  cbi_hsmall2 k (le_trans hk (by norm_num)) s

lemma cbi_support_zero :
    Function.support (fun _ : ℝ => (0 : ℝ)) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) :=
  fun x hx => absurd rfl hx

lemma cbi_continuous_baseState : Continuous (baseState : ℝ → St) := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp [baseState] <;>
    first
      | exact Commons.Geometry.Ulam.continuous_profileX
      | exact Commons.Geometry.Ulam.continuous_deriv_profileX

lemma cbi_differentiableAt_baseState (s : ℝ) : DifferentiableAt ℝ (baseState : ℝ → St) s := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [baseState] <;>
    first
      | exact (Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX.differentiable
          (by simp)).differentiableAt
      | exact (Commons.Geometry.Ulam.hasDerivAt_deriv_profileX s).differentiableAt

lemma cbi_hasDerivAt_baseState (s : ℝ) : HasDerivAt baseState (deriv baseState s) s :=
  (cbi_differentiableAt_baseState s).hasDerivAt

lemma cbi_mem_window {s : ℝ} (h1 : (1 / 4 : ℝ) ≤ s) (h2 : s ≤ 19 / 20) :
    s ∈ Set.Icc wLo wHi :=
  ⟨h1, h2⟩

/-! ## The uncurried clamped data and their smoothness -/

/-- The state datum `Gcl n 0` as a function of `(s, z)`. -/
def GclU (n : ℕ) : ℝ × St → St := fun p => Gcl n 0 p.1 p.2

/-- The `Θ` datum `Tcl n 0` as a function of `(s, σ, z)`. -/
def TclU (n : ℕ) : ℝ × ℝ × St → St := fun p => Tcl n 0 p.1 p.2.1 p.2.2

lemma cbi_contDiff_GclU (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (GclU n) :=
  contDiffOn_univ.mp (gcl_contDiffOn n contDiff_const cbi_support_zero cbi_hsmall2)

lemma cbi_contDiff_TclU (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (TclU n) :=
  contDiffOn_univ.mp (tcl_contDiffOn n contDiff_const cbi_support_zero cbi_hsmall2)

lemma cbi_contDiff_Xcl (n : ℕ) (hn : 1 ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Xcl n 0 s) :=
  contDiffOn_univ.mp (contDiffOn_Xcl n hn contDiff_const cbi_support_zero cbi_hsmall1)

lemma cbi_contDiff_Snd_Gcl (n : ℕ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : St => Gcl n 0 s z) := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun z : St => (s, z)) :=
    contDiff_prodMk_right (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (e₀ := s)
  exact (cbi_contDiff_GclU n).comp hslice

/-! ## The two sides of the differentiated identity -/

/-- The left-hand side of the differentiated clamped identity at `s`. -/
def FL (n : ℕ) (s : ℝ) : St :=
  deriv (fun u => Gcl n 0 u (baseState s)) s +
    fderiv ℝ (fun z => Gcl n 0 s z) (baseState s) (deriv baseState s)

/-- The right-hand side of the differentiated clamped identity at `s`. -/
def FR (n : ℕ) (s : ℝ) : St :=
  - Tcl n 0 s s (baseState s) +
    (∫ σ in s..(19 / 20 : ℝ), deriv (fun u => Tcl n 0 u σ (baseState σ)) s) +
    deriv (fun u => Xcl n 0 u) s

/-! ## The chain rule for the clamped data -/

lemma cbi_deriv_slice_Gcl (n : ℕ) (s : ℝ) (z : St) :
    fderiv ℝ (GclU n) (s, z) ((1 : ℝ), (0 : St)) = deriv (fun u => Gcl n 0 u z) s := by
  have hA : HasFDerivAt (GclU n) (fderiv ℝ (GclU n) (s, z)) (s, z) :=
    (((cbi_contDiff_GclU n).contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun u : ℝ => (u, z)) ((1 : ℝ), (0 : St)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  have h := hA.comp_hasDerivAt s hc
  rw [← h.deriv]
  rfl

lemma cbi_deriv_slice_Tcl (n : ℕ) (s σ : ℝ) (z : St) :
    fderiv ℝ (TclU n) (s, σ, z) ((1 : ℝ), (0 : ℝ), (0 : St)) =
      deriv (fun u => Tcl n 0 u σ z) s := by
  have hA : HasFDerivAt (TclU n) (fderiv ℝ (TclU n) (s, σ, z)) (s, σ, z) :=
    (((cbi_contDiff_TclU n).contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun u : ℝ => (u, σ, z)) ((1 : ℝ), (0 : ℝ), (0 : St)) s :=
    (hasDerivAt_id s).prodMk ((hasDerivAt_const s σ).prodMk (hasDerivAt_const s z))
  have h := hA.comp_hasDerivAt s hc
  rw [← h.deriv]
  rfl

/-! ## The derivative of the left-hand side -/

lemma cbi_hasDerivAt_FL (n : ℕ) (s : ℝ) :
    HasDerivAt (fun u => Gcl n 0 u (baseState u)) (FL n s) s := by
  have hG := cbi_contDiff_GclU n
  have hA : HasFDerivAt (GclU n) (fderiv ℝ (GclU n) (s, baseState s)) (s, baseState s) :=
    ((hG.contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun u : ℝ => (u, baseState u)) ((1 : ℝ), deriv baseState s) s :=
    (hasDerivAt_id s).prodMk (cbi_hasDerivAt_baseState s)
  refine (hA.comp_hasDerivAt s hc).congr_deriv ?_
  -- the two partial derivatives
  have hL0 : (fderiv ℝ (GclU n) (s, baseState s)) ((1 : ℝ), (0 : St))
      = deriv (fun u => Gcl n 0 u (baseState s)) s :=
    cbi_deriv_slice_Gcl n s (baseState s)
  have hL2 : (fderiv ℝ (GclU n) (s, baseState s)) ((0 : ℝ), deriv baseState s)
      = fderiv ℝ (fun z => Gcl n 0 s z) (baseState s) (deriv baseState s) := by
    have hprod : HasFDerivAt (fun z : St => (s, z)) (ContinuousLinearMap.inr ℝ ℝ St)
        (baseState s) :=
      hasFDerivAt_prodMk_right s (baseState s)
    have hcomp : HasFDerivAt ((GclU n) ∘ (fun z : St => (s, z)))
        ((fderiv ℝ (GclU n) (s, baseState s)).comp (ContinuousLinearMap.inr ℝ ℝ St))
        (baseState s) :=
      HasFDerivAt.comp (x := baseState s) (f := fun z : St => (s, z)) hA hprod
    have h2 := congrArg (fun (g : St →L[ℝ] St) => g (deriv baseState s)) hcomp.fderiv
    have h3 : fderiv ℝ ((GclU n) ∘ (fun z : St => (s, z))) (baseState s) (deriv baseState s)
        = (fderiv ℝ (GclU n) (s, baseState s)) ((0 : ℝ), deriv baseState s) := by
      simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using h2
    exact h3.symm
  have hsplit : ((1 : ℝ), deriv baseState s)
      = ((1 : ℝ), (0 : St)) + ((0 : ℝ), deriv baseState s) := by
    ext <;> simp
  rw [hsplit, map_add, hL0, hL2, FL]

/-! ## The derivative of the right-hand side -/

lemma cbi_hasDerivAt_FR (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    HasDerivAt (fun u => (∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u)
      (FR n s) s := by
  have hint := Commons.Analysis.Calculus.volterraFixedPoint_hasDerivAt_volterra_integral_ext
    (E := St) (K := fun u (σ : ℝ) (z : St) => Tcl n 0 u σ z) (w := baseState)
    (a := 0) (b := (19 / 20 : ℝ)) (s := s)
    (contDiffOn_univ.mpr (cbi_contDiff_TclU n)) cbi_continuous_baseState
  have hX : HasDerivAt (fun u => Xcl n 0 u) (deriv (fun u => Xcl n 0 u) s) s :=
    (((cbi_contDiff_Xcl n hn).differentiable (by simp)).differentiableAt).hasDerivAt
  have hI : (∫ σ in s..(19 / 20 : ℝ),
        fderiv ℝ (fun p : ℝ × ℝ × St => Tcl n 0 p.1 p.2.1 p.2.2) (s, σ, baseState σ)
          ((1 : ℝ), (0 : ℝ), (0 : St)))
      = ∫ σ in s..(19 / 20 : ℝ), deriv (fun u => Tcl n 0 u σ (baseState σ)) s :=
    intervalIntegral.integral_congr fun σ _ => cbi_deriv_slice_Tcl n s σ (baseState σ)
  rw [hI] at hint
  refine (hint.add hX).congr_deriv ?_
  rw [FR]

/-! ## The base identity for the clamped data -/

lemma cbi_eq_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      Gcl n 0 s (baseState s) =
        (∫ σ in s..(19 / 20 : ℝ), Tcl n 0 s σ (baseState σ)) + Xcl n 0 s := by
  intro s hs
  have hsW : s ∈ Set.Icc wLo wHi := hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hab1 : s ≤ 19 / 20 := hs.2
  have hs1 : s < 1 := by linarith [hs.2]
  have hz0 : ‖baseState s - baseState s‖ ≤ wRho := by simp [wRho_pos.le]
  -- the clamps are `1`, so the clamped data are the model data
  have hGcl : Gcl n 0 s (baseState s) = Godd n 0 s (baseState s) :=
    Gcl_eq_Godd hsW hz0
  have hXcl : Xcl n 0 s
      = Xi n 0 s + ∫ σ in wHi..(1 : ℝ), KernelExt.ThetaM n 0 s σ (baseState σ) :=
    Xcl_eq hsW
  have hTcl : (∫ σ in s..(19 / 20 : ℝ), Tcl n 0 s σ (baseState σ))
      = ∫ σ in s..(19 / 20 : ℝ), KernelExt.ThetaM n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le hab1] at hσ
    exact Tcl_eq_ThetaM hsW (cbi_mem_window (by linarith [hs.1, hσ.1]) hσ.2)
      (by simp [wRho_pos.le])
  -- the unperturbed Volterra identity
  have hbase : Godd n 0 s (baseState s)
      = (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ)) + Xi n 0 s :=
    Work.OddVolterra.Existence.base_volterra n hn s hs01
  -- on the open triangle the manifest kernel is the paper's kernel
  have hTheta : ∀ σ ∈ Set.Ioo s 1,
      Theta n 0 s σ (baseState σ) = KernelExt.ThetaM n 0 s σ (baseState σ) := by
    intro σ hσ
    have hσ4 : (1 / 4 : ℝ) ≤ σ := le_of_lt (lt_of_le_of_lt hs.1 hσ.1)
    have hσ1 : σ ≤ 1 := le_of_lt hσ.2
    have hz : ‖baseState σ - baseState σ‖ ≤ 1 / 2 := by simp
    have hz0' : (1 : ℝ) / 5 < |baseState σ 0| :=
      one_fifth_lt_abs_coord hσ4 hσ1 hz 0 (Or.inl rfl)
    have hz1' : (1 : ℝ) / 5 < |baseState σ 1| :=
      one_fifth_lt_abs_coord hσ4 hσ1 hz 1 (Or.inr rfl)
    rw [← Work.OddVolterra.Window.ThetaM_eq_Theta (n := n) (hn := hn) (h := 0)
      (hh := contDiff_const) (hsσ := hσ.1) (δ := 1 / 8) (hδ := by norm_num) (z := baseState σ)]
    · intro a ha
      exact krad_pos_of_add_pos' cbi_support_zero cbi_hsmall1
        (a := a) (σ := σ) (t := -(baseState σ 0))
        (by linarith [ha.1, hs.1, hσ.1]) (by rw [abs_neg]; exact le_of_lt hz0')
    · intro a ha
      exact krad_pos_of_add_pos' cbi_support_zero cbi_hsmall1
        (a := a) (σ := σ) (t := baseState σ 1)
        (by linarith [ha.1, hs.1, hσ.1]) (le_of_lt hz1')
  have hman : (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ))
      = ∫ σ in s..(1 : ℝ), KernelExt.ThetaM n 0 s σ (baseState σ) :=
    intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs1) hTheta
  -- interval integrability of the manifest integrand on the two pieces
  have hI1 : IntervalIntegrable
      (fun σ : ℝ => KernelExt.ThetaM n 0 s σ (baseState σ)) volume s (19 / 20) :=
    intervalIntegrable_thetaM_of_curve n contDiff_const cbi_support_zero cbi_hsmall1
      (hs := by linarith [hs.1]) (hs' := by linarith [hs.2]) hab1
      (c := baseState) cbi_continuous_baseState.continuousOn
      (fun σ hσ => by
        have hσ4 : (1 / 4 : ℝ) ≤ σ := le_trans hs.1 hσ.1
        have hσ1 : σ ≤ 1 := by linarith [hσ.2]
        exact ⟨by linarith, by linarith,
          one_fifth_lt_abs_coord hσ4 hσ1 (by simp) 0 (Or.inl rfl),
          one_fifth_lt_abs_coord hσ4 hσ1 (by simp) 1 (Or.inr rfl)⟩)
  have hI2 : IntervalIntegrable
      (fun σ : ℝ => KernelExt.ThetaM n 0 s σ (baseState σ)) volume (19 / 20) 1 :=
    intervalIntegrable_thetaM_of_curve n contDiff_const cbi_support_zero cbi_hsmall1
      (hs := by linarith [hs.1]) (hs' := by linarith [hs.2]) (by norm_num)
      (c := baseState) cbi_continuous_baseState.continuousOn
      (fun σ hσ => by
        have hσ4 : (1 / 4 : ℝ) ≤ σ := by linarith [hσ.1]
        have hσ1 : σ ≤ 1 := hσ.2
        have hpx : (1 : ℝ) / Real.sqrt 2 ≤ Commons.Geometry.Ulam.profileX σ :=
          Work.OddVolterra.Existence.profileX_lower_c (by rw [abs_le]; constructor <;> linarith)
        have hgt := Work.OddVolterra.Existence.one_div_sqrt_two_sub_half_gt_one_fifth_c
        have hb0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
        have hb1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
        refine ⟨by linarith, by linarith, ?_, ?_⟩
        · rw [hb0, abs_of_nonneg (by linarith)]; linarith
        · rw [hb1, abs_of_nonneg (by linarith)]; linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  rw [hGcl, hbase, hman, hTcl, hXcl, ← hsplit]
  simp only [wHi]
  abel

/-! ## `FL = FR`: the differentiated identity -/

/-- The one-sided argument used at the two endpoints: if the clamped identity holds on a
one-sided neighbourhood of `s` and both sides are differentiable at `s`, then the two
sides of the differentiated identity agree at `s`. -/
lemma cbi_FL_eq_FR_of_side (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (S : Set ℝ) (hS : S ⊆ {s}ᶜ)
    (hne : (𝓝[S] s).NeBot)
    (hev : (fun u => Gcl n 0 u (baseState u)) =ᶠ[𝓝[S] s]
      (fun u => (∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u))
    (hseq : Gcl n 0 s (baseState s)
      = (∫ σ in s..(19 / 20 : ℝ), Tcl n 0 s σ (baseState σ)) + Xcl n 0 s) :
    FL n s = FR n s := by
  haveI := hne
  have hfun : (fun u : ℝ => Gcl n 0 u (baseState u) -
      ((∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u)) =
      (fun u : ℝ => Gcl n 0 u (baseState u)) -
        (fun u : ℝ => (∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u) := rfl
  have hslope : Filter.Tendsto
      (slope (fun u : ℝ => Gcl n 0 u (baseState u) -
        ((∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u)) s)
      (𝓝[S] s) (𝓝 (FL n s - FR n s)) :=
    (cbi_hasDerivAt_FL n s).sub (cbi_hasDerivAt_FR n hn s) |>.tendsto_slope.mono_left
      (nhdsWithin_mono s hS)
  have hslope0 : Filter.Tendsto
      (slope (fun u : ℝ => Gcl n 0 u (baseState u) -
        ((∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u)) s)
      (𝓝[S] s) (𝓝 (0 : St)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with u hu
    simp [slope, hu, hseq]
  exact sub_eq_zero.mp (tendsto_nhds_unique hslope hslope0)

/-- The differentiated identity at the right endpoint `1/4`: the clamped identity holds on
`(1/4, 19/20)`, a one-sided neighbourhood of `1/4`. -/
lemma cbi_FL_eq_FR_quarter (n : ℕ) (hn : 1 ≤ n) :
    FL n (1 / 4) = FR n (1 / 4) := by
  have hne : (𝓝[Set.Ioi (1 / 4 : ℝ)] (1 / 4)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  refine cbi_FL_eq_FR_of_side n hn (1 / 4) (Set.Ioi (1 / 4)) ?_ hne ?_ ?_
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx'
    linarith [Set.mem_Ioi.mp hx]
  · filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono
        (nhdsWithin_le_nhds (a := (1 / 4 : ℝ)) (s := Set.Ioi (1 / 4 : ℝ)))
        (Iio_mem_nhds (show (1 / 4 : ℝ) < 19 / 20 by norm_num))] with u hu hu2
    exact cbi_eq_Icc n hn u ⟨le_of_lt hu, le_of_lt hu2⟩
  · exact cbi_eq_Icc n hn (1 / 4) ⟨by norm_num, by norm_num⟩

/-- The differentiated identity at the left endpoint `19/20`. -/
lemma cbi_FL_eq_FR_wHi (n : ℕ) (hn : 1 ≤ n) :
    FL n (19 / 20) = FR n (19 / 20) := by
  have hne : (𝓝[Set.Iio (19 / 20 : ℝ)] (19 / 20)).NeBot := nhdsWithin_Iio_neBot le_rfl
  refine cbi_FL_eq_FR_of_side n hn (19 / 20) (Set.Iio (19 / 20)) ?_ hne ?_ ?_
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx'
    linarith [Set.mem_Iio.mp hx]
  · filter_upwards [
      Filter.Eventually.filter_mono
        (nhdsWithin_le_nhds (a := (19 / 20 : ℝ)) (s := Set.Iio (19 / 20 : ℝ)))
        (Ioi_mem_nhds (show (1 / 4 : ℝ) < 19 / 20 by norm_num)),
      self_mem_nhdsWithin] with u hu hu2
    exact cbi_eq_Icc n hn u ⟨le_of_lt hu, le_of_lt hu2⟩
  · exact cbi_eq_Icc n hn (19 / 20) ⟨by norm_num, by norm_num⟩

/-! ## The base identity -/

theorem clamped_base_identity (n : ℕ) (hn : 1 ≤ n) :
    (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      Work.OddVolterra.WinData.Gcl n 0 s (Work.OddVolterra.baseState s) =
        (∫ σ in s..(19 / 20 : ℝ),
          Work.OddVolterra.WinData.Tcl n 0 s σ (Work.OddVolterra.baseState σ)) +
          Work.OddVolterra.WinData.Xcl n 0 s) ∧
    (∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      deriv (fun u => Work.OddVolterra.WinData.Gcl n 0 u (Work.OddVolterra.baseState s)) s +
        fderiv ℝ (fun z => Work.OddVolterra.WinData.Gcl n 0 s z)
          (Work.OddVolterra.baseState s) (deriv Work.OddVolterra.baseState s) =
      - Work.OddVolterra.WinData.Tcl n 0 s s (Work.OddVolterra.baseState s) +
        (∫ σ in s..(19 / 20 : ℝ),
          deriv (fun u => Work.OddVolterra.WinData.Tcl n 0 u σ
            (Work.OddVolterra.baseState σ)) s) +
        deriv (fun u => Work.OddVolterra.WinData.Xcl n 0 u) s) := by
  constructor
  · exact cbi_eq_Icc n hn
  · intro s hs
    change FL n s = FR n s
    by_cases hmem : s ∈ Set.Ioo (1 / 4 : ℝ) (19 / 20)
    · have hA := cbi_hasDerivAt_FL n s
      have hB := cbi_hasDerivAt_FR n hn s
      have hev : (fun u => Gcl n 0 u (baseState u)) =ᶠ[𝓝 s]
          (fun u => (∫ σ in u..(19 / 20 : ℝ), Tcl n 0 u σ (baseState σ)) + Xcl n 0 u) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo hmem] with u hu
        exact cbi_eq_Icc n hn u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      rw [← hA.deriv, ← hB.deriv]
      exact Filter.EventuallyEq.deriv_eq hev
    · have hend : s = 1 / 4 ∨ s = 19 / 20 := by
        by_contra hc
        push_neg at hc
        exact hmem ⟨lt_of_le_of_ne hs.1 (Ne.symm hc.1), lt_of_le_of_ne hs.2 hc.2⟩
      rcases hend with h | h
      · rw [h]; exact cbi_FL_eq_FR_quarter n hn
      · rw [h]; exact cbi_FL_eq_FR_wHi n hn

/-- The differentiated clamped base identity in the `FL`/`FR` form, on the closed window:
this is the second conjunct of `clamped_base_identity`, with its two sides named. -/
lemma clamped_base_identity_deriv_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), FL n s = FR n s :=
  fun s hs => (clamped_base_identity n hn).2 s hs

end

end Work.OddVolterra.WinData
