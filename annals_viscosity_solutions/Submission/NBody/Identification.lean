import Submission.NBody.Approximation
import Submission.NBody.Calibrating
import Submission.NBody.Continuation

/-!
# Identification of the limit of the approximating minimisers

`Submission.NBody.Approximation` shows that the `h`-minimisers `γ_k` from `q₀` to `p_k` have a
subsequence converging uniformly on `[0,T]` to a curve `ζ` which calibrates the horofunction `u`
(`actionOn_eq_ofReal_of_uniform_limit`).  This module proves that `ζ` is (the restriction of) the
calibrating curve `γ` of `u` shifted by `1`, i.e. `ζ t = γ (t+1)`.

The argument is the paper's: reversing the calibrating curve `γ|_{[0,1]}` produces a calibrating
curve `σ₀` through `q₀ = γ 1`; reversing `ζ` produces another one; their concatenation `κ` is an
`h`-minimiser through `q₀`.  The reversal `κ'` of `γ|_{[0,T+1]}` is also an `h`-minimiser, and the
two agree on `[T,T+1]`; the ODE uniqueness applied to time-reversed curves then gives `κ = κ'`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## Reversal of curves -/

/-- Reversal does not change the action. -/
lemma actionOn_comp_rev {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ : ℝ} :
    actionOn m h (fun t => γ (τ - t)) 0 τ = actionOn m h γ 0 τ := by
  unfold actionOn
  calc (∫⁻ t in Set.Ioc 0 τ,
          lagrangian m h ((fun s : ℝ => γ (τ - s)) t) (deriv (fun s : ℝ => γ (τ - s)) t))
      = ∫⁻ t in Set.Ioc 0 τ, lagrangian m h (γ (τ - t)) (-deriv γ (τ - t)) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
        rw [deriv_comp_const_sub]
    _ = ∫⁻ t in Set.Ioc 0 τ, lagrangian m h (γ (τ - t)) (deriv γ (τ - t)) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
        rw [lagrangian_neg]
    _ = ∫⁻ s in Set.Ioc 0 τ, lagrangian m h (γ s) (deriv γ s) :=
        setLIntegral_Ioc_comp_reflect (fun s => lagrangian m h (γ s) (deriv γ s)) τ

/-- The reversal of an absolutely continuous curve is absolutely continuous. -/
lemma absolutelyContinuousOnInterval_comp_rev {γ : ℝ → EN E N} {τ : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ 0 τ) :
    AbsolutelyContinuousOnInterval (fun t => γ (τ - t)) 0 τ := by
  have h1 : AbsolutelyContinuousOnInterval (fun t : ℝ => γ (τ - t)) τ 0 := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := 0) (b := τ) (c := -1) (d := τ) (by norm_num) hac
    have hfn : (fun t : ℝ => γ (-1 * t + τ)) = fun t : ℝ => γ (τ - t) := by
      funext t
      rw [show (-1:ℝ) * t + τ = τ - t by ring]
    rw [hfn] at h
    simpa using h
  exact h1.symm

/-- Reversal exchanges the endpoints of a calibrating curve and negates the calibration function. -/
lemma IsCalibrating.comp_rev {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {κ : ℝ → EN E N} {τ : ℝ} (hcal : IsCalibrating m h u κ 0 τ) :
    IsCalibrating m h (fun x => -u x) (fun s => κ (τ - s)) 0 τ := by
  rw [IsCalibrating] at hcal ⊢
  rw [actionOn_comp_rev, hcal]
  congr 1
  ring

/-! ## The right piece of a calibrating curve -/

/-- **The right sub-curve of a `u`-calibrating curve is `u`-calibrating.** -/
theorem IsCalibrating.sub_right {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {γ : ℝ → EN E N}
    {a b c : ℝ} (hd : Dominated m h u) (hcal : IsCalibrating m h u γ a b)
    (hac : AbsolutelyContinuousOnInterval γ a b) (hac' : a < c) (hcb : c < b) :
    IsCalibrating m h u γ c b := by
  have hfin : actionOn m h γ a b < ⊤ := hcal.actionOn_lt_top
  have hsum : actionOn m h γ a b = actionOn m h γ a c + actionOn m h γ c b :=
    actionOn_add γ hac'.le hcb.le
  have hX : actionOn m h γ a c < ⊤ := by
    rw [hsum] at hfin; exact (ENNReal.add_lt_top.mp hfin).1
  have hY : actionOn m h γ c b < ⊤ := by
    rw [hsum] at hfin; exact (ENNReal.add_lt_top.mp hfin).2
  have hac_ac : AbsolutelyContinuousOnInterval γ a c :=
    hac.mono (by
      rw [uIcc_of_le hac'.le, uIcc_of_le (hac'.le.trans hcb.le)]
      exact Set.Icc_subset_Icc_right hcb.le)
  have hac_cb : AbsolutelyContinuousOnInterval γ c b :=
    hac.mono (by
      rw [uIcc_of_le hcb.le, uIcc_of_le (hac'.le.trans hcb.le)]
      exact Set.Icc_subset_Icc_left hac'.le)
  have h1 : ENNReal.ofReal (u (γ c) - u (γ a)) ≤ actionOn m h γ a c :=
    (dominated_iff_le_actionOn.mp hd hac' hac_ac)
  have h2 : ENNReal.ofReal (u (γ b) - u (γ c)) ≤ actionOn m h γ c b :=
    (dominated_iff_le_actionOn.mp hd hcb hac_cb)
  set α := u (γ c) - u (γ a) with hαdef
  set β := u (γ b) - u (γ c) with hβdef
  have hαβ : u (γ b) - u (γ a) = α + β := by rw [hαdef, hβdef]; ring
  rw [IsCalibrating] at hcal
  have htot : (actionOn m h γ a c).toReal + (actionOn m h γ c b).toReal = max (α + β) 0 := by
    rw [← ENNReal.toReal_add hX.ne hY.ne, ← hsum, hcal, hαβ, ENNReal.toReal_ofReal']
  have hto1 : max α 0 ≤ (actionOn m h γ a c).toReal := by
    have := ENNReal.toReal_mono hX.ne h1
    rwa [ENNReal.toReal_ofReal'] at this
  have hto2 : max β 0 ≤ (actionOn m h γ c b).toReal := by
    have := ENNReal.toReal_mono hY.ne h2
    rwa [ENNReal.toReal_ofReal'] at this
  have hmax_ge : max (α + β) 0 ≤ max α 0 + max β 0 := by
    refine max_le (by linarith [le_max_left α 0, le_max_left β 0]) (by positivity)
  have hEqY : (actionOn m h γ c b).toReal = max β 0 := by
    have hkey : max α 0 + max β 0 = (actionOn m h γ a c).toReal + (actionOn m h γ c b).toReal :=
      le_antisymm (add_le_add hto1 hto2) (by rw [htot]; exact hmax_ge)
    linarith [hto2]
  show actionOn m h γ c b = ENNReal.ofReal (u (γ b) - u (γ c))
  rw [← ENNReal.ofReal_toReal hY.ne, hEqY]
  rcases le_total 0 β with hb | hb
  · rw [max_eq_left hb, ← hβdef]
  · rw [max_eq_right hb, ← hβdef, ENNReal.ofReal_eq_zero.mpr hb, ENNReal.ofReal_zero]

/-! ## Minimisers are solutions of the first-order state equation on the interior -/

/-- An `h`-minimiser with collision-free positions is a solution of the first-order state equation
on the interior of its interval. -/
lemma minimizer_hasDerivAt_state {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b) (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s => (γ s, deriv γ s)) (stateField m (γ t, deriv γ t)) t := by
  intro t ht
  obtain ⟨hat, htb⟩ := ht
  have hderiv := minimizer_hasDerivAt_deriv hm hh hab hac hnc hmin hfin
  set a' : ℝ := (a + t) / 2 with ha'
  set b' : ℝ := (t + b) / 2 with hb'
  have haa' : a < a' := by rw [ha']; linarith
  have ha't : a' < t := by rw [ha']; linarith
  have htb' : t < b' := by rw [hb']; linarith
  have hb'b : b' < b := by rw [hb']; linarith
  have hab' : a' < b' := lt_trans ha't htb'
  have hac' : AbsolutelyContinuousOnInterval γ a' b' :=
    hac.mono (by
      rw [uIcc_of_le hab'.le, uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc haa'.le hb'b.le)
  have hcont : ContinuousOn (deriv γ) (Set.Icc a' b') := fun s hs =>
    (hderiv s (Set.mem_Ioo.mpr ⟨lt_of_lt_of_le haa' hs.1, lt_of_le_of_lt hs.2 hb'b⟩)).continuousAt
      |>.continuousWithinAt
  have h1 : HasDerivAt γ (deriv γ t) t :=
    Commons.Analysis.Calculus.hasDerivAt_of_ae_deriv_eq_continuousOn hab' hac' hcont
      (Eventually.of_forall fun s _ => rfl) t (Set.mem_Ioo.mpr ⟨ha't, htb'⟩)
  have h2 : HasDerivAt (deriv γ) (weightedGrad m (U m) (γ t)) t :=
    hderiv t (Set.mem_Ioo.mpr ⟨hat, htb⟩)
  have hp := h1.prodMk h2
  simpa [stateField] using hp

/-- A calibrating curve of a dominated function is a solution of the first-order state equation at
every interior point, assuming Marchal's theorem (for collision-freeness). -/
lemma hasDerivAt_state_of_isCalibrating {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {γ : ℝ → EN E N} (hM : MarchalProperty (E := E) m h)
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hd : Dominated m h u)
    {a b : ℝ} (hab : a < b) (hac : AbsolutelyContinuousOnInterval γ a b)
    (hcal : IsCalibrating m h u γ a b) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s => (γ s, deriv γ s)) (stateField m (γ t, deriv γ t)) t := by
  intro t ht
  obtain ⟨hat, htb⟩ := ht
  obtain ⟨a', haa', ha't⟩ := exists_between hat
  obtain ⟨b', htb', hb'b⟩ := exists_between htb
  have hab' : a' < b' := lt_trans ha't htb'
  have ha'b : a' < b := lt_trans hab' hb'b
  have hac₁ : AbsolutelyContinuousOnInterval γ a' b :=
    hac.mono (by
      rw [uIcc_of_le ha'b.le, uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc haa'.le le_rfl)
  have hac₂ : AbsolutelyContinuousOnInterval γ a' b' :=
    hac.mono (by
      rw [uIcc_of_le hab'.le, uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc haa'.le hb'b.le)
  have hcal₁ : IsCalibrating m h u γ a' b := IsCalibrating.sub_right hd hcal hac haa' ha'b
  have hcal₂ : IsCalibrating m h u γ a' b' := IsCalibrating.sub hd hcal₁ hac₁ hab' hb'b
  have hmin' : IsHMinimizer m h γ a' b' := IsCalibrating.isHMinimizer hd hcal₂ hab' hac₂
  have hnc' : ∀ s ∈ Set.Icc a' b', WithoutCollisions (γ s) := fun s hs =>
    hM γ a b hab hac (IsCalibrating.isHMinimizer hd hcal hab hac) s
      (Set.mem_Ioo.mpr ⟨lt_of_lt_of_le haa' hs.1, lt_of_le_of_lt hs.2 hb'b⟩)
  have hfin' : actionPot m h (γ a') (γ b') < ⊤ :=
    lt_of_le_of_lt (actionPot_le_of_interval hab' rfl rfl hac₂) hcal₂.actionOn_lt_top
  exact minimizer_hasDerivAt_state hm hh hab' hac₂ hnc' hmin' hfin' t (Set.mem_Ioo.mpr ⟨ha't, htb'⟩)

/-- Reversal of a calibrating curve, stated with the “paper” calibration function `u`. -/
lemma IsCalibrating.rev_of {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {κ : ℝ → EN E N} {τ : ℝ} (hcal : IsCalibrating m h (fun x => -u x) κ 0 τ) :
    IsCalibrating m h u (fun s => κ (τ - s)) 0 τ := by
  rw [IsCalibrating] at hcal ⊢
  rw [actionOn_comp_rev, hcal]
  congr 1
  ring

/-! ## Identification of the limit -/

/-- **The uniform limit of the approximating minimisers is the calibrating curve shifted by `1`.**
The `h`-minimisers `γ_k` from `q₀ = γ 1` to `p_k` (with `τ_k → ∞`) converge, along a subsequence,
uniformly on `[0,T]` to the restriction of `s ↦ γ (s+1)`. -/
theorem exists_approx_to_calibrating_curve
    {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {γ : ℝ → EN E N} (hN : 0 < N)
    (hM : MarchalProperty (E := E) m h) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hlip : ∀ x z : EN E N, ENNReal.ofReal |u x - u z| ≤ actionPot m h x z)
    (hγac : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t)
    (hγcal : ∀ t : ℝ, 0 < t → IsCalibrating m h (fun x => -u x) γ 0 t)
    {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    {p : ℕ → EN E N} {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    (hτ0 : ∀ k, 0 < τ k) (h0 : ∀ k, γs k 0 = γ 1) (h1 : ∀ k, γs k (τ k) = p k)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hτtop : Tendsto τ atTop atTop)
    (huni : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p k) x) u atTop K)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    {T : ℝ} (hT : 0 < T) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun k => γs (φ k)) (fun t => γ (t + 1)) atTop (Set.Icc 0 T) := by
  have hdu : Dominated m h u := fun x y =>
    (ENNReal.ofReal_le_ofReal
      (le_trans (le_abs_self (u y - u x)) (le_of_eq (abs_sub_comm _ _)))).trans (hlip x y)
  set S : ℝ := T + 1 with hSdef
  have hS : T < S := by rw [hSdef]; linarith
  have hSpos : 0 < S := by linarith
  have hS1 : (0:ℝ) < S + 1 := by linarith
  obtain ⟨φ, ζ, hφ, hζ0, hζcont, hζac, hζconv, hζcal⟩ :=
    exists_calibrating_limit (m := m) (h := h) (u := u) (p := p) (q0 := γ 1)
      hN hm hh hdu huni hα hβ hest hτ0 h0 h1 hac hmin hτtop hSpos
  have hζcalI : IsCalibrating m h (fun x => -u x) ζ 0 S := by
    rw [IsCalibrating]
    rw [hζcal, hζ0]
    congr 1
    ring
  have hρcal : IsCalibrating m h u (fun s => ζ (S - s)) 0 S := IsCalibrating.rev_of hζcalI
  have hσcal : IsCalibrating m h u (fun s => γ (1 - s)) 0 1 :=
    IsCalibrating.rev_of (hγcal 1 one_pos)
  have hρac : AbsolutelyContinuousOnInterval (fun s => ζ (S - s)) 0 S :=
    absolutelyContinuousOnInterval_comp_rev hζac
  have hσacu : AbsolutelyContinuousOnInterval (fun s => γ (1 - s)) 0 1 :=
    absolutelyContinuousOnInterval_comp_rev (hγac 1 one_pos)
  have hσac' : AbsolutelyContinuousOnInterval (fun t => γ (1 - (t - S))) S (S + 1) := by
    have hcomp := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := fun s => γ (1 - s)) (a := 0) (b := 1) (c := 1) (d := -S) one_ne_zero hσacu
    have h2 : (0 - -S) / 1 = S := by ring
    have h3 : (1 - -S) / 1 = S + 1 := by ring
    rw [h2, h3] at hcomp
    simpa [sub_eq_add_neg, one_mul] using hcomp
  have hjoin1 : (fun s => ζ (S - s)) S = (fun s => γ (1 - s)) 0 := by
    show ζ (S - S) = γ (1 - 0)
    rw [sub_self, sub_zero, hζ0]
  have hjoin2 : (fun s => ζ (S - s)) S = (fun t => γ (1 - (t - S))) S := by
    show ζ (S - S) = γ (1 - (S - S))
    rw [sub_self, sub_zero, hζ0]
  have hmono₁ : u ((fun s => ζ (S - s)) 0) ≤ u ((fun s => ζ (S - s)) S) := by
    simp only [sub_zero, sub_self]
    rw [hζ0]
    by_contra hc'
    push_neg at hc'
    have hc'' : u (γ 1) - u (ζ S) < 0 := by linarith
    have h3 : ENNReal.ofReal |u (γ 1) - u (ζ S)| ≤ ENNReal.ofReal (u (γ 1) - u (ζ S)) := by
      calc ENNReal.ofReal |u (γ 1) - u (ζ S)| ≤ actionPot m h (γ 1) (ζ S) := hlip _ _
        _ ≤ actionOn m h ζ 0 S := actionPot_le_of_interval hSpos (by rw [hζ0]) rfl hζac
        _ = ENNReal.ofReal (u (γ 1) - u (ζ S)) := hζcal
    rw [ENNReal.ofReal_eq_zero.mpr hc''.le] at h3
    exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt hc''))).ne' (le_antisymm h3 bot_le)
  have hmono₂ : u ((fun s => γ (1 - s)) 0) ≤ u ((fun s => γ (1 - s)) 1) := by
    simp only [sub_zero, sub_self]
    by_contra hc'
    push_neg at hc'
    have hc'' : u (γ 0) - u (γ 1) < 0 := by linarith
    have hγ1 : actionOn m h γ 0 1 = ENNReal.ofReal (u (γ 0) - u (γ 1)) := by
      have h := hγcal 1 one_pos
      rw [IsCalibrating] at h
      convert h using 2
      ring
    have h3 : ENNReal.ofReal |u (γ 0) - u (γ 1)| ≤ ENNReal.ofReal (u (γ 0) - u (γ 1)) := by
      calc ENNReal.ofReal |u (γ 0) - u (γ 1)| ≤ actionPot m h (γ 0) (γ 1) := hlip _ _
        _ ≤ actionOn m h γ 0 1 := actionPot_le_of_interval one_pos rfl rfl (hγac 1 one_pos)
        _ = ENNReal.ofReal (u (γ 0) - u (γ 1)) := hγ1
    rw [ENNReal.ofReal_eq_zero.mpr hc''.le] at h3
    exact (ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt hc''))).ne' (le_antisymm h3 bot_le)
  -- the concatenated minimiser `κ` and the reversal `κ'` of `γ`
  let κ : ℝ → EN E N := fun t => if t ≤ S then ζ (S - t) else γ (1 - (t - S))
  let κ' : ℝ → EN E N := fun t => γ (S + 1 - t)
  have hκcal : IsCalibrating m h u κ 0 (S + 1) :=
    IsCalibrating.concat (γ₁ := fun s => ζ (S - s)) (γ₂ := fun s => γ (1 - s))
      (τ₁ := S) (τ₂ := 1) hSpos one_pos hjoin1 hmono₁ hmono₂ hρcal hσcal
  have hκac : AbsolutelyContinuousOnInterval κ 0 (S + 1) :=
    Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
      (a := 0) (c := S) (b := S + 1) hSpos.le (by linarith) hjoin2 hρac hσac'
  have hκmin : IsHMinimizer m h κ 0 (S + 1) := IsCalibrating.isHMinimizer hdu hκcal hS1 hκac
  have hκ'cal : IsCalibrating m h u κ' 0 (S + 1) := IsCalibrating.rev_of (hγcal (S + 1) hS1)
  have hκ'ac : AbsolutelyContinuousOnInterval κ' 0 (S + 1) :=
    absolutelyContinuousOnInterval_comp_rev (hγac (S + 1) hS1)
  have hκ'min : IsHMinimizer m h κ' 0 (S + 1) := IsCalibrating.isHMinimizer hdu hκ'cal hS1 hκ'ac
  -- the two curves agree to the right of `S`
  have hagree : ∀ s : ℝ, S ≤ s → κ s = κ' s := by
    intro s hs
    rcases eq_or_lt_of_le hs with hseq | hslt
    · subst hseq
      show (if S ≤ S then ζ (S - S) else γ (1 - (S - S))) = γ (S + 1 - S)
      rw [if_pos le_rfl, sub_self, hζ0]
      congr 1
      ring
    · show (if s ≤ S then ζ (S - s) else γ (1 - (s - S))) = γ (S + 1 - s)
      rw [if_neg (not_le.mpr hslt)]
      congr 1
      ring
  -- state solutions
  have hstateκ : ∀ t ∈ Set.Ioo (0:ℝ) (S + 1),
      HasDerivAt (fun s => (κ s, deriv κ s)) (stateField m (κ t, deriv κ t)) t :=
    hasDerivAt_state_of_isCalibrating hM hm hh hdu hS1 hκac hκcal
  have hstateκ' : ∀ t ∈ Set.Ioo (0:ℝ) (S + 1),
      HasDerivAt (fun s => (κ' s, deriv κ' s)) (stateField m (κ' t, deriv κ' t)) t :=
    hasDerivAt_state_of_isCalibrating hM hm hh hdu hS1 hκ'ac hκ'cal
  have hSmem : S ∈ Set.Ioo (0:ℝ) (S + 1) := Set.mem_Ioo.mpr ⟨hSpos, by linarith⟩
  have hκdiff : HasDerivAt κ (deriv κ S) S := by
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt S
      (hstateκ S hSmem)
    simpa [stateField, Function.comp_def] using h
  have hκ'diff : HasDerivAt κ' (deriv κ' S) S := by
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt S
      (hstateκ' S hSmem)
    simpa [stateField, Function.comp_def] using h
  have hderivS : deriv κ S = deriv κ' S := by
    have h1 : derivWithin κ (Set.Ici S) S = deriv κ S :=
      hκdiff.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici S)
    have h2 : derivWithin κ' (Set.Ici S) S = deriv κ' S :=
      hκ'diff.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici S)
    have h3 : derivWithin κ (Set.Ici S) S = derivWithin κ' (Set.Ici S) S :=
      derivWithin_congr (fun s hs => hagree s hs) (hagree S le_rfl)
    rw [← h1, h3, h2]
  -- reversed curves solve the reversed equation, and uniqueness
  let Z₁ : ℝ → EN E N × EN E N := fun s => (κ s, deriv κ s)
  let Z₂ : ℝ → EN E N × EN E N := fun s => (κ' s, deriv κ' s)
  have hkey : ∀ δ : ℝ, 0 < δ → ∀ t ∈ Set.Icc δ S, κ t = κ' t := by
    intro δ hδ t ht
    obtain ⟨htδ, htS⟩ := ht
    let W₁ : ℝ → EN E N × EN E N := fun s => Z₁ (S - s)
    let W₂ : ℝ → EN E N × EN E N := fun s => Z₂ (S - s)
    have hW0 : W₁ 0 = W₂ 0 := by
      show Z₁ (S - 0) = Z₂ (S - 0)
      rw [sub_zero]
      have hpos : κ S = κ' S := hagree S le_rfl
      show (κ S, deriv κ S) = (κ' S, deriv κ' S)
      rw [hpos, hderivS]
    have hu : ∀ s ∈ Set.Icc (0:ℝ) (S - δ), HasDerivAt W₁ (-stateField m (W₁ s)) s := by
      intro s hs
      obtain ⟨hs0, hsSd⟩ := hs
      have hmem : S - s ∈ Set.Ioo (0:ℝ) (S + 1) :=
        Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have hg : HasDerivAt (fun r : ℝ => S - r) (-1) s :=
        (hasDerivAt_id s).const_sub S
      have hcomp := HasDerivAt.scomp s (hstateκ (S - s) hmem) hg
      simpa only [W₁, Z₁, Function.comp_def, neg_one_smul] using hcomp
    have hv : ∀ s ∈ Set.Icc (0:ℝ) (S - δ), HasDerivAt W₂ (-stateField m (W₂ s)) s := by
      intro s hs
      obtain ⟨hs0, hsSd⟩ := hs
      have hmem : S - s ∈ Set.Ioo (0:ℝ) (S + 1) :=
        Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have hg : HasDerivAt (fun r : ℝ => S - r) (-1) s :=
        (hasDerivAt_id s).const_sub S
      have hcomp := HasDerivAt.scomp s (hstateκ' (S - s) hmem) hg
      simpa only [W₂, Z₂, Function.comp_def, neg_one_smul] using hcomp
    have hloc : ∀ s ∈ Set.Icc (0:ℝ) (S - δ), ∃ K : NNReal, ∃ U ∈ nhds (W₁ s),
        LipschitzOnWith K (fun z => -stateField m z) U := by
      intro s hs
      obtain ⟨hs0, hsSd⟩ := hs
      have hnc : WithoutCollisions (W₁ s).1 := by
        show WithoutCollisions (κ (S - s))
        exact hM κ 0 (S + 1) hS1 hκac hκmin (S - s)
          (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
      obtain ⟨K, U, hU, hL⟩ := exists_lipschitzOnWith_stateField m (W₁ s) hnc
      refine ⟨K, U, hU, ?_⟩
      rw [lipschitzOnWith_iff_dist_le_mul] at hL ⊢
      intro x hx y hy
      have hxy := hL x hx y hy
      rw [dist_eq_norm, dist_eq_norm] at hxy ⊢
      have hneg : -stateField m x - -stateField m y = -(stateField m x - stateField m y) := by
        abel
      rw [hneg, norm_neg]
      exact hxy
    have hEq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz
      (f := fun z : EN E N × EN E N => -stateField m z) (u := W₁) (v := W₂)
      (a := 0) (b := S - δ) (by linarith) hu hv hloc hW0
    have hmem : S - t ∈ Set.Icc (0:ℝ) (S - δ) := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h1 : W₁ (S - t) = W₂ (S - t) := hEq hmem
    have h2 : (W₁ (S - t)).1 = (W₂ (S - t)).1 := congrArg Prod.fst h1
    have h3 : (W₁ (S - t)).1 = κ t := by
      show κ (S - (S - t)) = κ t
      rw [show S - (S - t) = t by ring]
    have h4 : (W₂ (S - t)).1 = κ' t := by
      show κ' (S - (S - t)) = κ' t
      rw [show S - (S - t) = t by ring]
    rw [← h3, h2, h4]
  -- the identification on `[0,T]`
  have hEqOn : Set.EqOn ζ (fun t => γ (t + 1)) (Set.Icc 0 T) := by
    intro t ht
    obtain ⟨ht0, htT⟩ := ht
    by_cases h0t : t = 0
    · rw [h0t]
      simpa using hζ0
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0t)
      set t' : ℝ := S - t with ht'def
      have ht'pos : 0 < t' := by rw [ht'def]; linarith
      have ht'le : t' ≤ S := by rw [ht'def]; linarith
      have hkk := hkey (t' / 2) (by linarith) t' (Set.mem_Icc.mpr ⟨by linarith, ht'le⟩)
      have e1 : κ t' = ζ t := by
        show (if t' ≤ S then ζ (S - t') else γ (1 - (t' - S))) = ζ t
        rw [if_pos ht'le, show S - t' = t by rw [ht'def]; ring]
      have e2 : κ' t' = γ (t + 1) := by
        show γ (S + 1 - t') = γ (t + 1)
        rw [show S + 1 - t' = t + 1 by rw [ht'def]; ring]
      rwa [e1, e2] at hkk
  refine ⟨φ, hφ, ?_⟩
  have hmono := hζconv.mono (Set.Icc_subset_Icc le_rfl hS.le)
  exact hmono.congr_right hEqOn

/-! ## The quadratic expansion of a minimiser at its initial time -/

/-- **The initial velocity of an `h`-minimiser, with a quadratic remainder.**  An `h`-minimiser
`γ` on `[0,T]` has a right derivative `v` at `0`, and for any `K` bounding `‖∇U‖` on the image of
`[0,T/2]` one has `‖γ t - γ 0 - t • v‖ ≤ (K/2) t²` for `t ∈ [0,T/2]`. -/
lemma exists_initial_velocity_and_quadratic_bound {m : Fin N → ℝ} {h T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ t ∈ Set.Icc 0 T, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ 0 T)
    (hfin : actionPot m h (γ 0) (γ T) < ⊤) :
    ∃ v : EN E N, Tendsto (deriv γ) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      ∀ K : ℝ, 0 ≤ K → (∀ x ∈ γ '' Set.Icc 0 (T / 2), ‖∇_[m] (U m) x‖ ≤ K) →
        ∀ t ∈ Set.Icc 0 (T / 2), ‖γ t - γ 0 - t • v‖ ≤ (K / 2) * t ^ 2 := by
  classical
  have hc0 : (0 : ℝ) < T / 2 := by linarith
  have hcT : T / 2 < T := by linarith
  have hγcont : ContinuousOn γ (Set.Icc 0 T) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hT.le] at h
  have hgradcont : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc 0 T) :=
    continuousOn_weightedGrad_comp (continuousOn_fderiv_U_comp (m := m) hγcont hnc)
  have hgradc : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc 0 (T / 2)) :=
    hgradcont.mono (Set.Icc_subset_Icc_right hcT.le)
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc.image_of_continuousOn hgradc).isBounded.exists_norm_le
  have hK₀0 : 0 ≤ K₀ := le_trans (norm_nonneg _) (hK₀ _ ⟨0, ⟨le_rfl, hc0.le⟩, rfl⟩)
  have hK₀' : ∀ x ∈ γ '' Set.Icc 0 (T / 2), ‖∇_[m] (U m) x‖ ≤ K₀ := by
    rintro x ⟨t, ht, rfl⟩
    exact hK₀ (∇_[m] (U m) (γ t)) ⟨t, ht, rfl⟩
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (deriv γ) (∇_[m] (U m) (γ t)) t :=
    minimizer_hasDerivAt_deriv hm hh hT hac hnc hmin hfin
  -- the Lipschitz estimate on `(0,T/2)` with an arbitrary bound `K`
  have hmainK : ∀ K : ℝ, (∀ x ∈ γ '' Set.Icc 0 (T / 2), ‖∇_[m] (U m) x‖ ≤ K) →
      ∀ s ∈ Set.Ioo (0 : ℝ) (T / 2), ∀ t ∈ Set.Ioo (0 : ℝ) (T / 2), s ≤ t →
        dist (deriv γ s) (deriv γ t) ≤ K * dist s t := by
    intro K hK s hs t ht hst
    have htT : t < T := by linarith [ht.2, hcT]
    have hsub : Set.uIcc s t ⊆ Set.Icc 0 T := by
      rw [uIcc_of_le hst]
      exact Set.Icc_subset_Icc hs.1.le htT.le
    have hFTC : deriv γ t - deriv γ s = ∫ x in s..t, ∇_[m] (U m) (γ x) := by
      have h' : (∫ x in s..t, ∇_[m] (U m) (γ x)) = deriv γ t - deriv γ s := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := deriv γ)
          (f' := fun x => ∇_[m] (U m) (γ x)) (a := s) (b := t) ?_ ?_
        · intro x hx
          rw [uIcc_of_le hst] at hx
          exact hderiv x ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_le_of_lt hx.2 htT⟩
        · exact ContinuousOn.intervalIntegrable (hgradcont.mono hsub)
      exact h'.symm
    have hnorm : dist (deriv γ s) (deriv γ t) = ‖∫ x in s..t, ∇_[m] (U m) (γ x)‖ := by
      rw [dist_eq_norm, norm_sub_rev, hFTC]
    rw [hnorm, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    calc ‖∫ x in s..t, ∇_[m] (U m) (γ x)‖
        ≤ ∫ x in s..t, ‖∇_[m] (U m) (γ x)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hst
      _ ≤ ∫ x in s..t, K := by
          refine intervalIntegral.integral_mono_on hst ?_ ?_ ?_
          · exact (ContinuousOn.intervalIntegrable (hgradcont.mono hsub)).norm
          · exact intervalIntegrable_const
          · intro x hx
            exact hK _ ⟨x, ⟨le_trans hs.1.le hx.1, le_trans hx.2 ht.2.le⟩, rfl⟩
      _ = K * (t - s) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hlip₀ : ∀ s ∈ Set.Ioo (0 : ℝ) (T / 2), ∀ t ∈ Set.Ioo (0 : ℝ) (T / 2),
      dist (deriv γ s) (deriv γ t) ≤ K₀ * dist s t := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hmainK K₀ hK₀' s hs t ht hst
    · rw [dist_comm (deriv γ s) (deriv γ t), dist_comm s t]
      exact hmainK K₀ hK₀' t ht s hs hts
  obtain ⟨v, hv⟩ := tendsto_atRight_of_dist_le_mul (F := EN E N) (f := deriv γ)
    (a := 0) (c := T / 2) (K := K₀) hc0 hK₀0 hlip₀
  refine ⟨v, hv, ?_⟩
  intro K hK0 hKim
  have hvt : ∀ t ∈ Set.Ioo (0 : ℝ) (T / 2), ‖deriv γ t - v‖ ≤ K * t := by
    intro t ht
    have h1 : Tendsto (fun s : ℝ => dist (deriv γ t) (deriv γ s)) (𝓝[>] (0 : ℝ))
        (𝓝 (dist (deriv γ t) v)) :=
      (tendsto_const_nhds (x := deriv γ t)).dist hv
    have h2 : Tendsto (fun s : ℝ => K * (t - s)) (𝓝[>] (0 : ℝ)) (𝓝 (K * t)) := by
      have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      have hsub : Tendsto (fun s : ℝ => t - s) (𝓝[>] (0 : ℝ)) (𝓝 (t - 0)) :=
        tendsto_const_nhds.sub hid
      simpa using (tendsto_const_nhds (x := K)).mul hsub
    have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), dist (deriv γ t) (deriv γ s) ≤ K * (t - s) := by
      filter_upwards [Ioo_mem_nhdsGT (a := t) (b := (0 : ℝ)) ht.1] with s hs
      have hsT : s ∈ Set.Ioo (0 : ℝ) (T / 2) := ⟨hs.1, lt_trans hs.2 ht.2⟩
      have h := hmainK K hKim s hsT t ht hs.2.le
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.2.le)] at h
      rwa [dist_comm] at h
    have h4 := le_of_tendsto_of_tendsto h1 h2 h3
    rwa [dist_eq_norm] at h4
  -- the fundamental theorem of calculus for `γ`
  have hFTCγ : ∀ t ∈ Set.Icc (0 : ℝ) T, γ t - γ 0 = ∫ x in (0 : ℝ)..t, deriv γ x := by
    intro t ht
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT.le]
      exact Set.Icc_subset_Icc le_rfl ht.2
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector
      (f := γ) (a := 0) (b := t) (hac.mono hsub)
    exact h.symm
  intro t ht
  obtain ⟨ht0, htT2⟩ := ht
  have htT : t ≤ T := by linarith [htT2, hcT.le]
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) T := by
    rw [uIcc_of_le ht0, uIcc_of_le hT.le]
    exact Set.Icc_subset_Icc le_rfl htT
  have hInt : IntervalIntegrable (deriv γ) volume (0 : ℝ) t :=
    Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
      (hac.mono hsub)
  have h2 : γ t - γ 0 - t • v = ∫ x in (0 : ℝ)..t, (deriv γ x - v) := by
    rw [hFTCγ t ⟨ht0, htT⟩, intervalIntegral.integral_sub hInt intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
  calc ‖γ t - γ 0 - t • v‖
      = ‖∫ x in (0 : ℝ)..t, (deriv γ x - v)‖ := by rw [h2]
    _ ≤ ∫ x in (0 : ℝ)..t, ‖deriv γ x - v‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht0
    _ ≤ ∫ x in (0 : ℝ)..t, K * x := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo ht0 ?_ ?_ ?_
        · exact (hInt.sub intervalIntegrable_const).norm
        · exact (continuous_const.mul continuous_id).intervalIntegrable 0 t
        · intro x hx
          exact hvt x ⟨hx.1, lt_of_lt_of_le hx.2 htT2⟩
    _ = (K / 2) * t ^ 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring

/-- The auxiliary estimate used to pass from a quadratic bound to a bound on the derivative. -/
lemma norm_smul_inv_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {t : ℝ} (ht : 0 < t) {a b : F} {c : ℝ} (h : ‖a - t • b‖ ≤ c * t ^ 2) :
    ‖t⁻¹ • a - b‖ ≤ c * t := by
  have h1 : t⁻¹ • a - b = t⁻¹ • (a - t • b) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc t⁻¹ * ‖a - t • b‖ ≤ t⁻¹ * (c * t ^ 2) := mul_le_mul_of_nonneg_left h (inv_pos.mpr ht).le
    _ = c * t := by
        field_simp [ne_of_gt ht]

/-- `IsCalibrating` is invariant under translation of the curve. -/
lemma IsCalibrating.comp_add_const {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {γ : ℝ → EN E N}
    {a b : ℝ} (hcal : IsCalibrating m h u γ a b) :
    IsCalibrating m h u (fun t => γ (t + a)) 0 (b - a) := by
  rw [IsCalibrating] at hcal ⊢
  rw [actionOn_comp_add_const', hcal]
  congr 2 <;> ring

/-! ## The convergence of the initial velocities -/

/-- **The `C¹` approximation of the calibrating curve.**  The same subsequence `φ` of the
`h`-minimisers `γ_k` which converges uniformly to `γ (·+1)` on `[0,T]` has initial velocities
converging to `γ̇(1)`. -/
theorem exists_uniform_approx_and_velocity
    {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ} {γ : ℝ → EN E N} (hN : 0 < N)
    (hM : MarchalProperty (E := E) m h) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hlip : ∀ x z : EN E N, ENNReal.ofReal |u x - u z| ≤ actionPot m h x z)
    (hγac : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t)
    (hγcal : ∀ t : ℝ, 0 < t → IsCalibrating m h (fun x => -u x) γ 0 t)
    {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    {p : ℕ → EN E N} {τ : ℕ → ℝ} {γs : ℕ → ℝ → EN E N}
    (hτ0 : ∀ k, 0 < τ k) (h0 : ∀ k, γs k 0 = γ 1) (h1 : ∀ k, γs k (τ k) = p k)
    (hac : ∀ k, AbsolutelyContinuousOnInterval (γs k) 0 (τ k))
    (hmin : ∀ k, IsHMinimizer m h (γs k) 0 (τ k))
    (hτtop : Tendsto τ atTop atTop)
    (huni : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (p k) x) u atTop K)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hest : ∀ x z : EN E N, actionPot m h x z ≤
      ENNReal.ofReal (Real.sqrt (α * ‖x - z‖ + h * β * ‖x - z‖ ^ 2)))
    {T : ℝ} (hT : 0 < T) :
    ∃ (φ : ℕ → ℕ) (v : ℕ → EN E N), StrictMono φ ∧
      TendstoUniformlyOn (fun k => γs (φ k)) (fun t => γ (t + 1)) atTop (Set.Icc 0 T) ∧
      (∀ k, Tendsto (deriv (γs k)) (𝓝[>] (0 : ℝ)) (𝓝 (v k))) ∧
      Tendsto (fun k => v (φ k)) atTop (𝓝 (deriv γ 1)) := by
  classical
  have hd' : Dominated m h (fun x => -u x) := fun x y => by
    have h1 : ENNReal.ofReal (u x - u y) ≤ actionPot m h x y :=
      (ENNReal.ofReal_le_ofReal (le_abs_self (u x - u y))).trans (hlip x y)
    have h2 : -u y - -u x = u x - u y := by ring
    show ENNReal.ofReal (-u y - -u x) ≤ actionPot m h x y
    rw [h2]
    exact h1
  have hfinall : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  have hac2 : AbsolutelyContinuousOnInterval γ 0 2 := hγac 2 (by norm_num)
  have hmin2 : IsHMinimizer m h γ 0 2 :=
    IsCalibrating.isHMinimizer hd' (hγcal 2 (by norm_num)) (by norm_num) hac2
  have hq0nc : WithoutCollisions (γ 1) :=
    hM γ 0 2 (by norm_num) hac2 hmin2 1 ⟨by norm_num, by norm_num⟩
  -- `γs = γ (·+1)` is an `h`-minimiser
  have hγsac : ∀ δ : ℝ, 0 < δ → AbsolutelyContinuousOnInterval (fun t => γ (t + 1)) 0 δ := by
    intro δ hδ
    have hδ1 : (0 : ℝ) < δ + 1 := by linarith
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := 0) (b := δ + 1) (c := 1) (d := 1) one_ne_zero (hγac (δ + 1) hδ1)
    have h4 : (fun t : ℝ => γ (1 * t + 1)) = fun t : ℝ => γ (t + 1) := by
      funext t; rw [one_mul]
    rw [h4] at h
    refine h.mono ?_
    have h2 : ((0:ℝ) - 1) / 1 = -1 := by norm_num
    have h3 : (δ + 1 - 1) / 1 = δ := by ring
    rw [h2, h3, uIcc_of_le (by linarith : (-1 : ℝ) ≤ δ), uIcc_of_le hδ.le]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hγscal : ∀ δ : ℝ, 0 < δ → IsCalibrating m h (fun x => -u x) (fun t => γ (t + 1)) 0 δ := by
    intro δ hδ
    have h := IsCalibrating.sub_right (a := 0) (b := δ + 1) (c := 1) hd'
      (hγcal (δ + 1) (by linarith)) (hγac (δ + 1) (by linarith)) one_pos (by linarith)
    simpa using IsCalibrating.comp_add_const h
  have hγsm : ∀ δ : ℝ, 0 < δ → IsHMinimizer m h (fun t => γ (t + 1)) 0 δ := fun δ hδ =>
    IsCalibrating.isHMinimizer hd' (hγscal δ hδ) hδ (hγsac δ hδ)
  have hγsnc : ∀ δ : ℝ, 0 < δ → ∀ t ∈ Set.Icc 0 δ, WithoutCollisions (γ (t + 1)) := by
    intro δ hδ t ht
    obtain ⟨ht1, ht2⟩ := ht
    rcases eq_or_lt_of_le ht1 with h0' | h0'
    · rw [← h0', zero_add]; exact hq0nc
    · exact hM γ 0 (δ + 2) (by linarith) (hγac (δ + 2) (by linarith))
        (IsCalibrating.isHMinimizer hd' (hγcal (δ + 2) (by linarith)) (by linarith)
          (hγac (δ + 2) (by linarith)))
        (t + 1) ⟨by linarith, by linarith⟩
  -- the velocity of `γs` at `0` is `γ̇(1)`
  have hvγs : Tendsto (deriv (fun t => γ (t + 1))) (𝓝[>] (0 : ℝ)) (𝓝 (deriv γ 1)) := by
    have hstate : HasDerivAt (fun s => (γ s, deriv γ s)) (stateField m (γ 1, deriv γ 1)) 1 :=
      hasDerivAt_state_of_isCalibrating hM hm hh hd' (by norm_num) hac2
        (hγcal 2 (by norm_num)) 1 ⟨by norm_num, by norm_num⟩
    have hγd' : HasDerivAt (deriv γ) (∇_[m] (U m) (γ 1)) 1 := by
      have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt 1 hstate
      simpa [stateField, Function.comp_def] using h
    have hcont : Tendsto (fun u : ℝ => deriv γ u) (𝓝 (1 : ℝ)) (𝓝 (deriv γ 1)) :=
      hγd'.continuousAt
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have h1' : Tendsto (fun t : ℝ => t + 1) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add hid
      simpa [add_comm] using h
    have hcomp : Tendsto (fun t : ℝ => deriv γ (t + 1)) (𝓝[>] (0 : ℝ)) (𝓝 (deriv γ 1)) :=
      hcont.comp h1'
    refine hcomp.congr' (Eventually.of_forall fun t => ?_)
    exact (deriv_comp_add_const γ 1 t).symm
  -- the neighbourhood of the collision-free `q0` on which `∇U` is bounded
  obtain ⟨ρ, hρpos, hρnc⟩ := exists_ball_withoutCollisions (E := E) (N := N) hq0nc
  obtain ⟨ρ₂, hρ₂pos, K, hKb⟩ := exists_bound_weightedGrad (m := m) (E := E) (N := N) hq0nc
  set ρ₁ : ℝ := min ρ ρ₂ with hρ₁def
  have hρ₁pos : 0 < ρ₁ := lt_min hρpos hρ₂pos
  have hρ₁nc : ∀ y : EN E N, dist y (γ 1) ≤ ρ₁ → WithoutCollisions y :=
    fun y hy => hρnc y (le_trans hy (min_le_left _ _))
  have hKb₁ : ∀ y : EN E N, dist y (γ 1) ≤ ρ₁ → ‖weightedGrad m (U m) y‖ ≤ K :=
    fun y hy => hKb y (le_trans hy (min_le_right _ _))
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hKb₁ (γ 1) (by rw [dist_self]; exact hρ₁pos.le))
  -- a ball around `0` on which `γs` stays within half of `ρ₁` of `q0`
  have hcw : ContinuousWithinAt (fun t : ℝ => γ (t + 1)) (Set.Icc 0 T) 0 := by
    have h : ContinuousOn (fun t : ℝ => γ (t + 1)) (Set.uIcc 0 T) :=
      (hγsac T hT).continuousOn
    rw [uIcc_of_le hT.le] at h
    exact h.continuousWithinAt ⟨le_rfl, hT.le⟩
  have hq0shift : (fun t : ℝ => γ (t + 1)) 0 = γ 1 := by simp
  obtain ⟨δ, hδpos, hδprop⟩ := Metric.continuousWithinAt_iff.mp hcw (ρ₁ / 2) (by linarith)
  set t₁ : ℝ := min (δ / 4) (T / 2) with ht₁def
  have ht₁pos : 0 < t₁ := lt_min (by linarith) (by linarith)
  have h2t₁δ : 2 * t₁ < δ := by
    have h : t₁ ≤ δ / 4 := min_le_left _ _
    linarith
  have h2t₁T : 2 * t₁ ≤ T := by
    have h : t₁ ≤ T / 2 := min_le_right _ _
    linarith
  -- the subsequence and the velocities
  have hnc : ∀ k, ∀ t ∈ Set.Icc 0 (τ k / 2), WithoutCollisions (γs k t) := by
    intro k t ht
    rcases eq_or_lt_of_le ht.1 with h0' | h0'
    · rw [← h0', h0 k]; exact hq0nc
    · exact hM (γs k) 0 (τ k) (hτ0 k) (hac k) (hmin k) t
        ⟨h0', lt_of_le_of_lt ht.2 (by linarith [hτ0 k])⟩
  have hvel : ∀ k, ∃ v : EN E N, Tendsto (deriv (γs k)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    intro k
    have hτ2 : (0 : ℝ) < τ k / 2 := by linarith [hτ0 k]
    have hac2' : AbsolutelyContinuousOnInterval (γs k) 0 (τ k / 2) :=
      (hac k).mono (by
        rw [uIcc_of_le hτ2.le, uIcc_of_le (hτ0 k).le]
        exact Set.Icc_subset_Icc le_rfl (by linarith [hτ0 k]))
    have hmin2' : IsHMinimizer m h (γs k) 0 (τ k / 2) :=
      IsHMinimizer.sub_left (hac k) (hmin k)
        (IsHMinimizer.actionOn_lt_top (hmin k) (hfinall _ _)) hτ2 (by linarith [hτ0 k])
    obtain ⟨v, hv, _⟩ := exists_initial_velocity_and_quadratic_bound (T := τ k / 2) hm hh hτ2
      hac2' (hnc k) hmin2' (hfinall _ _)
    exact ⟨v, hv⟩
  set v : ℕ → EN E N := fun k => Classical.choose (hvel k) with hvdef
  have hvspec : ∀ k, Tendsto (deriv (γs k)) (𝓝[>] (0 : ℝ)) (𝓝 (v k)) :=
    fun k => Classical.choose_spec (hvel k)
  obtain ⟨φ, hφmono, hconv⟩ := exists_approx_to_calibrating_curve (hN := hN) hM hm hh hlip hγac
    hγcal hc hmc hτ0 h0 h1 hac hmin hτtop huni hα hβ hest hT
  refine ⟨φ, v, hφmono, hconv, hvspec, ?_⟩
  · -- velocity convergence
    have hKpos : (0 : ℝ) < 2 * K + 2 := by linarith
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [← Filter.eventually_atTop]
    set t : ℝ := min t₁ (ε / (2 * K + 2)) with htdef
    have htpos : 0 < t := lt_min ht₁pos (by positivity)
    have htle₁ : t ≤ t₁ := min_le_left _ _
    have htε : t ≤ ε / (2 * K + 2) := min_le_right _ _
    have htT : t ≤ T := by linarith [htle₁, h2t₁T]
    have htδ : 2 * t < δ := by linarith [htle₁, h2t₁δ]
    have h2t : (0 : ℝ) < 2 * t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    -- `γs([0,2t])` stays in the ball
    have hγsball : ∀ u ∈ Set.Icc 0 (2 * t), dist ((fun s : ℝ => γ (s + 1)) u) (γ 1) < ρ₁ / 2 := by
      intro u hu
      have hlt : dist u 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
        linarith [hu.2, htδ]
      have hmem : u ∈ Set.Icc 0 T := ⟨hu.1, le_trans hu.2 (by linarith [h2t, htT])⟩
      have h₁ := hδprop hmem hlt
      simpa only [zero_add] using h₁
    -- the quadratic bound for `γs` at `t`
    have hbs : ‖(fun s : ℝ => γ (s + 1)) t - (fun s : ℝ => γ (s + 1)) 0 - t • deriv γ 1‖
        ≤ (K / 2) * t ^ 2 := by
      obtain ⟨vs, hvs, hbnd⟩ := exists_initial_velocity_and_quadratic_bound (T := 2 * t) hm hh h2t
        (hγsac (2 * t) h2t) (hγsnc (2 * t) h2t) (hγsm (2 * t) h2t) (hfinall _ _)
      have hvs_eq : vs = deriv γ 1 := tendsto_nhds_unique hvs hvγs
      have himg : ∀ x ∈ (fun s : ℝ => γ (s + 1)) '' Set.Icc 0 ((2 * t) / 2),
          ‖∇_[m] (U m) x‖ ≤ K := by
        rintro x ⟨u, hu, rfl⟩
        have hu' : u ∈ Set.Icc 0 (2 * t) := by
          rw [show (2 * t) / 2 = t by ring] at hu
          exact ⟨hu.1, le_trans hu.2 (by linarith)⟩
        exact hKb₁ _ (le_of_lt (lt_of_lt_of_le (hγsball u hu') (by linarith)))
      have h := hbnd K hK0 himg t (by
        rw [show (2 * t) / 2 = t by ring]
        exact Set.mem_Icc.mpr ⟨htpos.le, le_rfl⟩)
      rwa [hvs_eq] at h
    -- eventually the minimisers are close to `γs`, and stay in the ball
    have hevent : ∀ᶠ k in atTop,
        (∀ u ∈ Set.Icc 0 T, dist (γs (φ k) u) (γ (u + 1)) < ε * t / 2) ∧
        (∀ u ∈ Set.Icc 0 (2 * t), dist (γs (φ k) u) (γ 1) < ρ₁) ∧
        (2 * t < τ (φ k)) := by
      have h1' : ∀ᶠ k in atTop, ∀ u ∈ Set.Icc 0 T, dist (γs (φ k) u) (γ (u + 1)) < ε * t / 2 := by
        have hpos : (0 : ℝ) < ε * t / 2 := by positivity
        filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) (ε * t / 2) hpos] with k hk
        intro u hu
        simpa [dist_comm] using hk u hu
      have h2' : ∀ᶠ k in atTop, ∀ u ∈ Set.Icc 0 T, dist (γs (φ k) u) (γ (u + 1)) < ρ₁ / 2 := by
        have hpos : (0 : ℝ) < ρ₁ / 2 := by linarith
        filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) (ρ₁ / 2) hpos] with k hk
        intro u hu
        simpa [dist_comm] using hk u hu
      have h3' : ∀ᶠ k in atTop, 2 * t < τ (φ k) :=
        hφmono.tendsto_atTop.eventually (hτtop.eventually_gt_atTop (2 * t))
      filter_upwards [h1', h2', h3'] with k hk1 hk2 hk3
      refine ⟨hk1, ?_, hk3⟩
      intro u hu
      have h3 : u ∈ Set.Icc 0 T := ⟨hu.1, le_trans hu.2 (by linarith [h2t, htT])⟩
      calc dist (γs (φ k) u) (γ 1)
          ≤ dist (γs (φ k) u) (γ (u + 1)) + dist (γ (u + 1)) (γ 1) := dist_triangle _ _ _
        _ < ρ₁ / 2 + ρ₁ / 2 := add_lt_add (hk2 u h3) (hγsball u hu)
        _ = ρ₁ := by ring
    filter_upwards [hevent] with k hk
    obtain ⟨hk1, hkball, hkτ⟩ := hk
    -- the quadratic bound for `γ_{φ k}` at `t`
    have hac2' : AbsolutelyContinuousOnInterval (γs (φ k)) 0 (2 * t) :=
      (hac (φ k)).mono (by
        rw [uIcc_of_le h2t.le, uIcc_of_le (hτ0 (φ k)).le]
        exact Set.Icc_subset_Icc le_rfl (by linarith [hkτ]))
    have hmin2' : IsHMinimizer m h (γs (φ k)) 0 (2 * t) :=
      IsHMinimizer.sub_left (hac (φ k)) (hmin (φ k))
        (IsHMinimizer.actionOn_lt_top (hmin (φ k)) (hfinall _ _)) h2t (by linarith [hkτ])
    have hnc2' : ∀ u ∈ Set.Icc 0 (2 * t), WithoutCollisions (γs (φ k) u) := by
      intro u hu
      rcases eq_or_lt_of_le hu.1 with h0'' | h0''
      · rw [← h0'', h0 (φ k)]; exact hq0nc
      · exact hM (γs (φ k)) 0 (τ (φ k)) (hτ0 (φ k)) (hac (φ k)) (hmin (φ k)) u
          ⟨h0'', lt_of_le_of_lt hu.2 (by linarith [hkτ])⟩
    obtain ⟨vk, hvk, hbndk⟩ := exists_initial_velocity_and_quadratic_bound (T := 2 * t) hm hh h2t
      hac2' hnc2' hmin2' (hfinall _ _)
    have hvk_eq : vk = v (φ k) := tendsto_nhds_unique hvk (hvspec (φ k))
    have himgk : ∀ x ∈ γs (φ k) '' Set.Icc 0 ((2 * t) / 2), ‖∇_[m] (U m) x‖ ≤ K := by
      rintro x ⟨u, hu, rfl⟩
      have hu' : u ∈ Set.Icc 0 (2 * t) := by
        rw [show (2 * t) / 2 = t by ring] at hu
        exact ⟨hu.1, le_trans hu.2 (by linarith)⟩
      exact hKb₁ _ (le_of_lt (hkball u hu'))
    have hbk := hbndk K hK0 himgk t (by
      rw [show (2 * t) / 2 = t by ring]
      exact Set.mem_Icc.mpr ⟨htpos.le, le_rfl⟩)
    rw [hvk_eq] at hbk
    -- assemble the three terms
    have hA : ‖v (φ k) - t⁻¹ • (γs (φ k) t - γs (φ k) 0)‖ ≤ (K / 2) * t := by
      have h := norm_smul_inv_sub_le (F := EN E N) htpos hbk
      rw [norm_sub_rev] at h
      exact h
    have hC : ‖t⁻¹ • ((fun s : ℝ => γ (s + 1)) t - (fun s : ℝ => γ (s + 1)) 0) - deriv γ 1‖
        ≤ (K / 2) * t := norm_smul_inv_sub_le (F := EN E N) htpos hbs
    have hB : ‖t⁻¹ • (γs (φ k) t - γs (φ k) 0)
        - t⁻¹ • ((fun s : ℝ => γ (s + 1)) t - (fun s : ℝ => γ (s + 1)) 0)‖
        = t⁻¹ * ‖γs (φ k) t - γ (t + 1)‖ := by
      have hsub : γs (φ k) t - γs (φ k) 0
          - ((fun s : ℝ => γ (s + 1)) t - (fun s : ℝ => γ (s + 1)) 0)
          = γs (φ k) t - γ (t + 1) := by
        rw [h0 (φ k)]
        simp only [zero_add]
        abel
      rw [← smul_sub, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    have htri := dist_triangle4 (v (φ k)) (t⁻¹ • (γs (φ k) t - γs (φ k) 0))
      (t⁻¹ • ((fun s : ℝ => γ (s + 1)) t - (fun s : ℝ => γ (s + 1)) 0)) (deriv γ 1)
    simp only [dist_eq_norm] at htri ⊢
    refine lt_of_le_of_lt htri ?_
    have hBle : t⁻¹ * ‖γs (φ k) t - γ (t + 1)‖ < ε / 2 := by
      have hlt : ‖γs (φ k) t - γ (t + 1)‖ < ε * t / 2 := by
        have h' := hk1 t (Set.mem_Icc.mpr ⟨htpos.le, htT⟩)
        rwa [dist_eq_norm] at h'
      have h2 := mul_lt_mul_of_pos_left hlt (inv_pos.mpr htpos)
      have heq : t⁻¹ * (ε * t / 2) = ε / 2 := by
        field_simp [ne_of_gt htpos]
      rwa [heq] at h2
    have hKt : K * t < ε / 2 := by
      have h1 : K * t ≤ K * (ε / (2 * K + 2)) := mul_le_mul_of_nonneg_left htε hK0
      have h2 : K * (ε / (2 * K + 2)) < ε / 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * K + 2)]
        nlinarith
      linarith
    have hA' : ‖v (φ k) - t⁻¹ • (γs (φ k) t - γs (φ k) 0)‖ < ε / 2 := by
      have : (K / 2) * t = K * t / 2 := by ring
      rw [this] at hA; linarith
    have hC' : ‖t⁻¹ • ((fun s : ℝ => γ (s + 1)) t - (fun s : ℝ => γ (s + 1)) 0) - deriv γ 1‖
        < ε / 2 := by
      have : (K / 2) * t = K * t / 2 := by ring
      rw [this] at hC; linarith
    linarith [hB ▸ hBle]

end Submission.NBody
