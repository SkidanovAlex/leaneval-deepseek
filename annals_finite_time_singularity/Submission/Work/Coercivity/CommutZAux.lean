/-
# Auxiliary lemmas for the `D_z`-commutator estimate (working file)
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.dth_LGammaT_expansion
import Submission.Work.Coercivity.L12dens_integrableOn
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.angRad_mixed
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Coercivity.CommutZ_SumI

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity.CommutZ

set_option autoImplicit false

/-! ## Differentiation under the `θ`-integral -/

/-- Differentiation under the `θ`-integral for the `K`-average. -/
theorem hasDerivAt_Kav (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) {x : ℝ} (hx : -1 < x) :
    HasDerivAt (Kav f) (Kav (Spaces.pz f) x) x := by
  have hK : ContinuousOn Spaces.K (Set.Icc 0 (π / 2)) := by
    show ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) _
    fun_prop
  have hfun : Kav f = (fun y => ∫ θ in Spaces.Iθ, f y θ * Spaces.K θ) := by
    funext y
    simp only [Kav]
    exact integral_congr_ae (Eventually.of_forall fun θ => by ring)
  have hval : Kav (Spaces.pz f) x = ∫ θ in Spaces.Iθ, Spaces.pz f x θ * Spaces.K θ := by
    simp only [Kav]
    exact integral_congr_ae (Eventually.of_forall fun θ => by ring)
  have h := Work.Elliptic.hasDerivAt_integral_Iθ f Spaces.K hf hK hx
  rw [hfun, hval]
  exact h

/-! ## The density of `D_z f` -/

/-- The `L₁₂`-density of `D_z f` is the `K`-average of `∂_z f`, away from `s = 0`. -/
theorem L12dens_Dz_eq (f : ℝ → ℝ → ℝ) (s : ℝ) (hs : 0 < s) :
    FM.L12dens Spaces.K (Spaces.Dz f) s = Kav (Spaces.pz f) s := by
  have hs' : s ≠ 0 := ne_of_gt hs
  rw [FM.L12dens, Kav]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [Spaces.Dz]
  field_simp

/-- **The `D_z`-companion of `∂_z L₁₂(f) = -(K,f)/z`**: for `f` whose `K`-average vanishes
at infinity and whose `D_z f`-density is integrable, `L₁₂(D_z f)(z) = -(K,f)(z)`. -/
theorem L12f_Dz_eq {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) (hT : TailHyp f)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) : L12f (Spaces.Dz f) z = -(Kav f z) := by
  have hz0 : 0 < z := hz
  have hdens : ∀ s ∈ Set.Ioi z, FM.L12dens Spaces.K (Spaces.Dz f) s = Kav (Spaces.pz f) s :=
    fun s hs => L12dens_Dz_eq f s (lt_trans hz0 hs)
  have hint : IntegrableOn (Kav (Spaces.pz f)) (Set.Ioi z) :=
    (hT.hintDz.mono_set (Set.Ioi_subset_Ioi (le_of_lt hz0))).congr_fun
      (fun s hs => hdens s hs) measurableSet_Ioi
  have hftc : ∫ x in Set.Ioi z, Kav (Spaces.pz f) x = 0 - Kav f z :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx => hasDerivAt_Kav f hf (by have hzx : z ≤ x := hx; linarith)) hint hT.hlim
  have hL : L12f (Spaces.Dz f) z = ∫ s in Set.Ioi z, FM.L12dens Spaces.K (Spaces.Dz f) s := rfl
  rw [hL, setIntegral_congr_fun measurableSet_Ioi hdens, hftc]
  ring

/-! ## The pointwise expansion of the defect `E₂` -/

/-- **The pointwise `D_z`-commutator identity.**  With the analytic hypotheses `TailHyp`
(the `L₁₂`-densities integrable and the `K`-average vanishing at infinity) the defect
`E₂ = D_z 𝓛_Γ^T f - 𝓛_Γ^T(D_z f)` is the sum of the two multiplier terms and the
`Γ(θ)·(Gfun f z/c)` term. -/
theorem CommutZ_pointwise_E2 (α : ℝ) (hc : Spaces.c α ≠ 0) (f : ℝ → ℝ → ℝ)
    (hf : Spaces.SmoothNbhd f) (hT : TailHyp f) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Spaces.Iθ,
      E2fun α f z θ = mm z * f z θ + (3 / 2) * (mm z * Spaces.Dth f z θ)
        + (Spaces.Gam α θ / Spaces.c α) * Gfun f z := by
  intro z hz θ hθ
  have hz0 : 0 < z := hz
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hSum := CommutZ_SumI α f hf hT.hint z θ hz0 hθ
  have hL := congrFun (congrFun (LGammaT_eq_sum α (Spaces.Dz f)) z) θ
  have hid : L12f (Spaces.Dz f) z = -(Kav f z) := L12f_Dz_eq hf hT hz
  have hKavg : Kavg f z = Kav f z := rfl
  simp only [E2fun, hSum, hL]
  simp only [SumI, Z1, Z2, Z3, Z4, Z5, Z6, Z7, T1fun, T4fun, Transport, C0, L, Spaces.Dz]
  rw [hid, hKavg]
  simp only [Gfun, Lam1, Lam2, cfac, zdq, qfun, mm]
  field_simp
  ring

/-- `Kav (∂_z g) z = Kav (D_z g) z / z` for `z ≠ 0`: the two `K`-averages differ by the
factor `z` carried by `D_z`. -/
theorem Kav_pz_div (g : ℝ → ℝ → ℝ) (z : ℝ) (hz : z ≠ 0) :
    Kav (Spaces.pz g) z = Kav (Spaces.Dz g) z / z := by
  have hpt : ∀ θ : ℝ, Spaces.K θ * Spaces.pz g z θ = Spaces.K θ * (Spaces.Dz g z θ / z) := by
    intro θ
    have h : Spaces.Dz g z θ = z * Spaces.pz g z θ := rfl
    rw [h, mul_div_cancel_left₀ _ hz]
  have hpt2 : (fun θ : ℝ => Spaces.K θ * (Spaces.Dz g z θ / z))
      = (fun θ : ℝ => (Spaces.K θ * Spaces.Dz g z θ) / z) := by
    funext θ; ring
  simp only [Kav, hpt]
  rw [hpt2, MeasureTheory.integral_div]

/-- **The iterated tail identity**: `D_z^j L₁₂(f)(z) = -(K, D_z^{j-1}f)(z)`. -/
theorem CommutZ_pointwise_tail (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) (hT : TailHyp f) :
    ∀ (j : ℕ), 1 ≤ j → ∀ {z : ℝ}, z ∈ Set.Ioi 0 →
      DzIterZ j (fun y => L12f f y) z = -(Kav (Spaces.DzIter (j - 1) f) z) := by
  refine Nat.le_induction ?base ?step
  · intro z hz
    have hz0 : 0 < z := hz
    have hd : deriv (fun y => L12f f y) z = -(Kav f z / z) :=
      (L12f_zDeriv' f hf hT.hint hz0).deriv
    have h1 : DzIterZ 1 (fun y => L12f f y) z = z * deriv (fun y => L12f f y) z := rfl
    rw [h1, hd]
    have h0 : Spaces.DzIter (1 - 1) f = f := rfl
    rw [h0]
    field_simp
  · intro j hj ih z hz
    have hz0 : 0 < z := hz
    have hzne : z ≠ 0 := ne_of_gt hz0
    have hev : (fun y => DzIterZ j (fun y => L12f f y) y)
        =ᶠ[𝓝 z] (fun y => -(Kav (Spaces.DzIter (j - 1) f) y)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz) (fun y hy => ih (z := y) hy)
    have hder : deriv (fun y => DzIterZ j (fun y => L12f f y) y) z
        = -(Kav (Spaces.DzIter j f) z / z) := by
      rw [hev.deriv_eq]
      have h := hasDerivAt_Kav (Spaces.DzIter (j - 1) f)
        (Spaces.SmoothNbhd.DzIter hf (j - 1)) (by linarith : (-1 : ℝ) < z)
      have hKav : HasDerivAt (fun y => -Kav (Spaces.DzIter (j - 1) f) y)
          (-(Kav (Spaces.pz (Spaces.DzIter (j - 1) f)) z)) z := h.neg
      rw [hKav.deriv]
      rw [Kav_pz_div (Spaces.DzIter (j - 1) f) z hzne]
      have hDz : Spaces.DzIter j f = Spaces.Dz (Spaces.DzIter (j - 1) f) := by
        cases j with
        | zero => omega
        | succ k => rfl
      rw [hDz]
    have h1 : DzIterZ (j + 1) (fun y => L12f f y) z
        = z * deriv (fun y => DzIterZ j (fun y => L12f f y) y) z := rfl
    rw [h1, hder]
    have hsub : j + 1 - 1 = j := by omega
    rw [hsub]
    field_simp

/-! ## Elementary books for the assembly -/

/-- A finite set of real numbers (`AngEta α 0`, `AngEta α 1` and `AngGam α i`, `i ≤ n`) has a
common positive upper bound. -/
theorem CommutZ_ang_exists (α : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ CT.AngEta α 0 ≤ K ∧ CT.AngEta α 1 ≤ K
      ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n → CT.AngGam α i ≤ K := by
  refine ⟨|CT.AngEta α 0| + |CT.AngEta α 1| + ∑ i ∈ Finset.range (n + 1), |CT.AngGam α i| + 1,
    by positivity, ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ |CT.AngEta α 1| := abs_nonneg _
    have h2 : (0:ℝ) ≤ ∑ i ∈ Finset.range (n + 1), |CT.AngGam α i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [le_abs_self (CT.AngEta α 0)]
  · have h1 : (0:ℝ) ≤ |CT.AngEta α 0| := abs_nonneg _
    have h2 : (0:ℝ) ≤ ∑ i ∈ Finset.range (n + 1), |CT.AngGam α i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [le_abs_self (CT.AngEta α 1)]
  · intro i hi hin
    have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hin)
    have h1 : |CT.AngGam α i| ≤ ∑ j ∈ Finset.range (n + 1), |CT.AngGam α j| :=
      Finset.single_le_sum (f := fun j => |CT.AngGam α j|) (fun j _ => abs_nonneg _) hmem
    have h2 : (0:ℝ) ≤ |CT.AngEta α 0| := abs_nonneg _
    have h3 : (0:ℝ) ≤ |CT.AngEta α 1| := abs_nonneg _
    linarith [le_abs_self (CT.AngGam α i)]

/-- `DzIterZ` is homogeneous: iterating `z∂_z` commutes with scalar multiples. -/
theorem DzIterZ_const_mul (c : ℝ) (j : ℕ) (m : ℝ → ℝ) :
    DzIterZ j (fun z => c * m z) = fun z => c * DzIterZ j m z := by
  induction j with
  | zero => rfl
  | succ k ih =>
      funext z
      simp only [DzIterZ_succ, ih]
      rw [deriv_const_mul_field]
      ring

theorem DzIterZ_zero_fun (j : ℕ) (z : ℝ) : DzIterZ j (fun _ : ℝ => (0:ℝ)) z = 0 := by
  have h := DzIterZ_const_mul 0 j (fun _ : ℝ => (0:ℝ))
  have h2 := congrFun h z
  simpa using h2

end Work.Coercivity.CommutZ
