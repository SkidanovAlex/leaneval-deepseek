import Mathlib
import Submission.Work.NN.Final.Chart
import Submission.Work.NN.Final.ChartSmooth.contDiff_chart
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le
import Submission.Work.NN.Final.ChartComp.exists_bound_iteratedFDeriv_div_norm
import Submission.Work.NN.Final.ChartComp.exists_bound_iteratedFDeriv_norm
import Submission.Work.NN.Final.ChartComp.exists_bound_iteratedFDeriv_inv
import Submission.Work.NN.Final.ChartComp.exists_bound_iteratedFDeriv_log
import Submission.Work.NN.Final.ChartComp.exists_bound_iteratedFDeriv_radialStep
import Submission.Work.NN.Final.ChartComp.eventuallyEq_of_holderOn_one_lt
import Submission.Work.NN.Final.ChartComp.holderNorm_comp_le_pos
import Submission.Work.NN.Final.ChartComp.holderNorm_comp_univ

set_option maxHeartbeats 1000000

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set Filter

namespace Work.NN.Final.ChartComp

open Work.NN.Final Work.CR.Flat

variable {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n}

/-- `m ≤ ∞` for the "all finite orders" level `∞ = (⊤ : ℕ∞)` of smoothness. -/
lemma natCast_le_top_nat (m : ℕ) : ((m : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-! ## General helpers -/

lemma norm_prod_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {G H : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    (A : ContinuousMultilinearMap 𝕜 E G) (B : ContinuousMultilinearMap 𝕜 E H) :
    ‖A.prod B‖ ≤ ‖A‖ + ‖B‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := A.prod B) (M := ‖A‖ + ‖B‖)
    (by positivity) fun m => ?_
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖A m‖ ≤ ‖A‖ * ∏ i, ‖m i‖ := A.le_opNorm m
      _ ≤ (‖A‖ + ‖B‖) * ∏ i, ‖m i‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg B))
            (Finset.prod_nonneg fun i _ => norm_nonneg _)
  · calc ‖B m‖ ≤ ‖B‖ * ∏ i, ‖m i‖ := B.le_opNorm m
      _ ≤ (‖A‖ + ‖B‖) * ∏ i, ‖m i‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg A))
            (Finset.prod_nonneg fun i _ => norm_nonneg _)

lemma norm_iteratedFDeriv_clm_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) :
    ∀ (m : ℕ), 1 ≤ m → ∀ z : X, ‖iteratedFDeriv ℝ m (fun z => L z) z‖ ≤ ‖L‖ := by
  intro m hm z
  have hf : fderiv ℝ (fun z => L z) = fun _ => L := by
    ext1 v; simp only [ContinuousLinearMap.fderiv]
  rcases m with _ | _ | k
  · exact absurd hm (by omega)
  · rw [← norm_iteratedFDeriv_fderiv (f := fun z => L z) (x := z) (n := 0), hf,
      norm_iteratedFDeriv_zero]
  · rw [← norm_iteratedFDeriv_fderiv (f := fun z => L z) (x := z) (n := k + 1), hf,
      iteratedFDeriv_const_of_ne (by omega) L]
    simp

lemma norm_iteratedFDerivWithin_sub_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} (hs : UniqueDiffOn ℝ s) {f : E → F}
    (hf : DifferentiableOn ℝ f s) (c : F) {x : E} (hx : x ∈ s) :
    ∀ j : ℕ, 1 ≤ j →
      ‖iteratedFDerivWithin ℝ j (fun x => f x - c) s x‖ = ‖iteratedFDerivWithin ℝ j f s x‖ := by
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [← norm_iteratedFDerivWithin_fderivWithin (f := fun x => f x - c) hs hx,
    ← norm_iteratedFDerivWithin_fderivWithin (f := f) hs hx]
  congr 1
  refine iteratedFDerivWithin_congr ?_ hx m
  intro y hy
  have h1 : (fun x : E => f x - c) = (f - fun _ : E => c) := rfl
  rw [h1, fderivWithin_sub (hs y hy) (hf y hy) (differentiableWithinAt_const c)]
  simp

/-- Composition bound: if `f` has bounded derivatives of positive order on `s` and `g` has
bounded derivatives of positive order on `t`, then so does `g ∘ f`. -/
theorem exists_bound_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Set X} {t : Set ℝ} (hs : IsOpen s) (ht : IsOpen t) {f : X → ℝ} {g : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g t)
    (hst : Set.MapsTo f s t)
    (A : ℕ → ℝ) (hA : ∀ k, 1 ≤ k → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ k f s x‖ ≤ A k)
    (B : ℕ → ℝ) (hB : ∀ l, 1 ≤ l → ∀ r ∈ t, ‖iteratedFDerivWithin ℝ l g t r‖ ≤ B l) :
    ∃ C : ℕ → ℝ, ∀ m, 1 ≤ m → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ m (g ∘ f) s x‖ ≤ C m := by
  refine ⟨fun m => (m.factorial : ℝ) * max 1 (∑ i ∈ Finset.range (m+1), |B i|)
      * (max 1 (∑ i ∈ Finset.range (m+1), |A i|))^m, fun m hm x hx => ?_⟩
  set Cb : ℝ := max 1 (∑ i ∈ Finset.range (m+1), |B i|) with hCb
  set Db : ℝ := max 1 (∑ i ∈ Finset.range (m+1), |A i|) with hDb
  have hCb1 : 1 ≤ Cb := le_max_left _ _
  have hDb1 : 1 ≤ Db := le_max_left _ _
  have hCb0 : 0 ≤ Cb := le_trans zero_le_one hCb1
  have hDb0 : 0 < Db := lt_of_lt_of_le zero_lt_one hDb1
  have hCB : ∀ i ≤ m, B i ≤ Cb := by
    intro i hi
    have h1 : |B i| ≤ ∑ j ∈ Finset.range (m+1), |B j| :=
      Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    rw [hCb]
    exact le_trans (le_abs_self (B i)) (le_trans h1 (le_max_right _ _))
  have hCA : ∀ i ≤ m, A i ≤ Db := by
    intro i hi
    have h1 : |A i| ≤ ∑ j ∈ Finset.range (m+1), |A j| :=
      Finset.single_le_sum (f := fun j => |A j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    rw [hDb]
    exact le_trans (le_abs_self (A i)) (le_trans h1 (le_max_right _ _))
  have hdifft : DifferentiableOn ℝ g t := hg.differentiableOn (by simp)
  have hCbound : ∀ i ≤ m, ‖iteratedFDerivWithin ℝ i (fun r => g r - g (f x)) t (f x)‖ ≤ Cb := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [norm_iteratedFDerivWithin_zero]
      simp only [sub_self, norm_zero]
      exact hCb0
    · rw [norm_iteratedFDerivWithin_sub_const ht.uniqueDiffOn hdifft (g (f x)) (hst hx) i h]
      exact le_trans (hB i h (f x) (hst hx)) (hCB i hi)
  have hDbound : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ Db^i := by
    intro i h1 h2
    refine le_trans (hA i h1 x hx) (le_trans (hCA i h2) ?_)
    calc Db = Db^1 := (pow_one Db).symm
      _ ≤ Db^i := pow_le_pow_right₀ hDb1 h1
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := fun r => g r - g (f x)) (f := f)
    (n := m) (s := s) (t := t) (x := x) (N := (⊤ : ℕ∞))
    (hg.sub contDiffOn_const) hf (natCast_le_top_nat m) ht.uniqueDiffOn hs.uniqueDiffOn hst hx
    (C := Cb) (D := Db) hCbound hDbound
  have hdiffc : DifferentiableOn ℝ (g ∘ f) s :=
    (hg.differentiableOn (by simp)).comp (hf.differentiableOn (by simp)) hst
  have hshift : ‖iteratedFDerivWithin ℝ m ((fun r => g r - g (f x)) ∘ f) s x‖
      = ‖iteratedFDerivWithin ℝ m (g ∘ f) s x‖ := by
    have heq : ((fun r => g r - g (f x)) ∘ f) = fun y => (g ∘ f) y - (g (f x)) := by
      funext y; rfl
    rw [heq]
    exact norm_iteratedFDerivWithin_sub_const hs.uniqueDiffOn hdiffc (g (f x)) hx m hm
  rw [hshift] at key
  exact key

/-! ## The one-variable pieces -/

/-- The `S¹`-valued map `w ↦ w/‖w‖`. -/
noncomputable def dirn (w : ℂ) : ℂ := w / ((‖w‖ : ℝ) : ℂ)

/-- The one-variable version of `chartU`: `w ↦ radialStep * w/‖w‖`. -/
noncomputable def u0 (ρ : Fin n → ℝ) (i : Fin n) (w : ℂ) : ℂ :=
  ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ) * dirn w

/-- The one-variable version of `chartT`. -/
noncomputable def tau0 (ρ : Fin n → ℝ) (i : Fin n) (w : ℂ) : ℝ :=
  (1 - radialStep (ρ i / 8) (ρ i / 4) ‖w‖) * Real.log 4
    + radialStep (ρ i / 8) (ρ i / 4) ‖w‖ * (Real.log (ρ i) - Real.log ‖w‖)

/-- The outer one-variable function whose composite with `‖·‖` is `tau0`. -/
noncomputable def Tfun (ρ : Fin n → ℝ) (i : Fin n) (r : ℝ) : ℝ :=
  (1 - radialStep (ρ i / 8) (ρ i / 4) r) * Real.log 4
    + radialStep (ρ i / 8) (ρ i / 4) r * (Real.log (ρ i) - Real.log r)

/-- The insertion of a complex number in the `i`-th slot, as a continuous linear map. -/
def insCLM (i : Fin n) : ℂ →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℝ ℂ else (0 : ℂ →L[ℝ] ℂ))

lemma insCLM_apply (i : Fin n) (w : ℂ) : insCLM i w = Function.update (0 : Fin n → ℂ) i w := by
  funext j
  rw [insCLM, ContinuousLinearMap.pi_apply]
  by_cases h : j = i
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

lemma chartU_eq_u0 (z : Fin n → ℂ) : chartU ρ i z = u0 ρ i (z i) := by
  rw [chartU, u0, dirn]

lemma chartT_eq_tau0 (z : Fin n → ℂ) : chartT ρ i z = tau0 ρ i (z i) := by
  rw [chartT, tau0]

lemma tau0_eq_Tfun (w : ℂ) : tau0 ρ i w = Tfun ρ i ‖w‖ := by
  rw [tau0, Tfun]

section Bounds

/-- The `S¹`-valued map `w ↦ w/‖w‖` has norm at most one. -/
lemma norm_dirn_le (w : ℂ) : ‖dirn w‖ ≤ 1 := by
  have h1 : ‖((‖w‖ : ℝ) : ℂ)‖ = ‖w‖ := by simp
  by_cases h : w = 0
  · simp [dirn, h]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr h
    calc ‖dirn w‖ = ‖w * ((‖w‖ : ℝ) : ℂ)⁻¹‖ := by rw [dirn, div_eq_mul_inv]
      _ = ‖w‖ * ‖w‖⁻¹ := by rw [norm_mul, norm_inv, h1]
      _ = 1 := by rw [mul_inv_cancel₀ (ne_of_gt hpos)]
      _ ≤ 1 := le_rfl

/-- The `radialStep` factor has norm at most one. -/
lemma norm_radialStep_cast_le (a b r : ℝ) : ‖((radialStep a b r : ℝ) : ℂ)‖ ≤ 1 := by
  rw [show ‖((radialStep a b r : ℝ) : ℂ)‖ = |radialStep a b r| by simp,
    abs_of_nonneg (by rw [radialStep]; exact smoothCut_nonneg _)]
  rw [radialStep]
  exact smoothCut_le_one _

lemma contDiff_u0 (hρ : 0 < ρ i) : ContDiff ℝ (⊤ : ℕ∞) (u0 ρ i) := by
  have h1 : u0 ρ i = chartU ρ i ∘ insCLM i := by
    funext w
    rw [Function.comp_apply, insCLM_apply, chartU_eq_u0, Function.update_self]
  rw [h1]
  exact (ChartSmooth.contDiff_chartU (i := i) hρ).comp_continuousLinearMap (g := insCLM i)

lemma contDiff_tau0 (hρ : 0 < ρ i) : ContDiff ℝ (⊤ : ℕ∞) (tau0 ρ i) := by
  have h1 : tau0 ρ i = chartT ρ i ∘ insCLM i := by
    funext w
    rw [Function.comp_apply, insCLM_apply, chartT_eq_tau0, Function.update_self]
  rw [h1]
  exact (ChartSmooth.contDiff_chartT (i := i) hρ).comp_continuousLinearMap (g := insCLM i)

/-- The bound for `‖·‖` on `U'` used in the composition estimate. -/
lemma exists_norm_bound_on_U (hρ : 0 < ρ i) :
    ∃ A : ℕ → ℝ, ∀ k, 1 ≤ k → ∀ w : ℂ, ρ i / 16 < ‖w‖ →
      ‖iteratedFDerivWithin ℝ k (fun w : ℂ => ‖w‖) {w : ℂ | ρ i / 16 < ‖w‖} w‖ ≤ A k := by
  obtain ⟨Cn, hn0, hn⟩ := exists_bound_iteratedFDeriv_norm
  refine ⟨fun k => max (Cn k) 1 * (16 / ρ i) ^ (k - 1), fun k hk x hx => ?_⟩
  have hx0 : x ≠ 0 := fun h => by
    rw [h, norm_zero] at hx; linarith [show (0:ℝ) < ρ i / 16 by positivity]
  have hnorm : ρ i / 16 < ‖x‖ := hx
  have hpos : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hρ16 : (0:ℝ) < ρ i / 16 := by positivity
  have h1' : 1 / ‖x‖ < 16 / ρ i := by
    rw [show (16:ℝ) / ρ i = 1 / (ρ i / 16) from (one_div_div (ρ i) 16).symm, one_div, one_div,
      inv_lt_inv₀ hpos hρ16]
    exact hnorm
  rw [iteratedFDerivWithin_of_isOpen k (isOpen_lt continuous_const continuous_norm) hx]
  refine le_trans (hn k hk x hx0) ?_
  have h2 : (1 / ‖x‖) ^ (k - 1) ≤ (16 / ρ i) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) h1'.le _
  refine le_trans (mul_le_mul_of_nonneg_left h2 (le_of_lt (hn0 k))) ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- The bound for `s₁ ∘ ‖·‖` on `U'`. -/
lemma exists_bound_comp_s1 (hρ : 0 < ρ i) :
    ∃ Cs : ℕ → ℝ, ∀ m, 1 ≤ m → ∀ w : ℂ, ρ i / 16 < ‖w‖ →
      ‖iteratedFDerivWithin ℝ m ((radialStep (ρ i / 8) (ρ i / 3)) ∘ (fun w : ℂ => ‖w‖))
        {w : ℂ | ρ i / 16 < ‖w‖} w‖ ≤ Cs m := by
  obtain ⟨Cr, hr0, hr⟩ := exists_bound_iteratedFDeriv_radialStep (ρ i / 8) (ρ i / 3)
  obtain ⟨A, hA⟩ := exists_norm_bound_on_U (ρ := ρ) (i := i) hρ
  have hU'open : IsOpen {w : ℂ | ρ i / 16 < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have hU'pos : ∀ w ∈ {w : ℂ | ρ i / 16 < ‖w‖}, w ≠ 0 := by
    intro w hw h
    have hw' : ρ i / 16 < ‖w‖ := hw
    rw [h, norm_zero] at hw'
    linarith [show (0:ℝ) < ρ i / 16 by positivity]
  have hν : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w‖) {w : ℂ | ρ i / 16 < ‖w‖} :=
    fun x hx => ((contDiffAt_norm ℝ (hU'pos x hx)).contDiffWithinAt).of_le le_top
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (radialStep (ρ i / 8) (ρ i / 3)) Set.univ :=
    (ChartSmooth.contDiff_radialStep _ _).contDiffOn
  have hst : Set.MapsTo (fun w : ℂ => ‖w‖) {w : ℂ | ρ i / 16 < ‖w‖} Set.univ :=
    fun x _ => Set.mem_univ _
  have hBb : ∀ l, 1 ≤ l → ∀ r ∈ (Set.univ : Set ℝ),
      ‖iteratedFDerivWithin ℝ l (radialStep (ρ i / 8) (ρ i / 3)) Set.univ r‖ ≤ max (Cr l) 1 := by
    intro l hl r _
    rw [iteratedFDerivWithin_univ]
    exact le_trans (hr l r) (le_max_left _ _)
  exact exists_bound_comp hU'open isOpen_univ hν hg hst A hA (fun l => max (Cr l) 1) hBb

/-- The bound for `u0` on `U'`, from the product rule. -/
lemma exists_bound_u0_on_U (hρ : 0 < ρ i) :
    ∃ D : ℕ → ℝ, ∀ m, 1 ≤ m → ∀ w : ℂ, ρ i / 16 < ‖w‖ →
      ‖iteratedFDeriv ℝ m (u0 ρ i) w‖ ≤ D m := by
  obtain ⟨Cs, hCs⟩ := exists_bound_comp_s1 (ρ := ρ) (i := i) hρ
  obtain ⟨Cd, hd0, hd⟩ := exists_bound_iteratedFDeriv_div_norm
  have hU'open : IsOpen {w : ℂ | ρ i / 16 < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have hw0 : ∀ w : ℂ, ρ i / 16 < ‖w‖ → w ≠ 0 := by
    intro w hw h
    rw [h, norm_zero] at hw
    linarith [show (0:ℝ) < ρ i / 16 by positivity]
  have hν : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w‖) {w : ℂ | ρ i / 16 < ‖w‖} :=
    fun x hx => ((contDiffAt_norm ℝ (hw0 x hx)).contDiffWithinAt).of_le le_top
  have hf0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => radialStep (ρ i / 8) (ρ i / 3) ‖w‖)
      {w : ℂ | ρ i / 16 < ‖w‖} :=
    (ChartSmooth.contDiff_radialStep _ _).comp_contDiffOn hν
  have hf1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ))
      {w : ℂ | ρ i / 16 < ‖w‖} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf0
  have hg1 : ContDiffOn ℝ (⊤ : ℕ∞) dirn {w : ℂ | ρ i / 16 < ‖w‖} := by
    have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => (((‖w‖ : ℝ) : ℂ))⁻¹)
        {w : ℂ | ρ i / 16 < ‖w‖} :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hν.inv (fun x hx => ne_of_gt (norm_pos_iff.mpr (hw0 x hx))))).congr
        (fun x hx => (Complex.ofReal_inv ‖x‖).symm)
    refine (contDiff_id.contDiffOn.mul hc).congr (fun x hx => ?_)
    rw [dirn, div_eq_mul_inv]
    simp
  refine ⟨fun m => ∑ t ∈ Finset.range (m + 1), (m.choose t : ℝ)
      * (max (Cs t) 1) * (max (Cd (m - t)) 1 * (16 / ρ i) ^ (m - t)),
    fun m hm w hw => ?_⟩
  have hfbound : ∀ t ≤ m, ‖iteratedFDerivWithin ℝ t
      (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ))
      {w : ℂ | ρ i / 16 < ‖w‖} w‖ ≤ max (Cs t) 1 := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      rw [norm_iteratedFDerivWithin_zero]
      exact le_trans (norm_radialStep_cast_le _ _ _) (le_max_right _ _)
    · refine le_trans ?_ (le_max_left _ _)
      calc ‖iteratedFDerivWithin ℝ t
            (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ))
            {w : ℂ | ρ i / 16 < ‖w‖} w‖
          ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDerivWithin ℝ t
              ((radialStep (ρ i / 8) (ρ i / 3)) ∘ (fun w : ℂ => ‖w‖))
              {w : ℂ | ρ i / 16 < ‖w‖} w‖ :=
            Complex.ofRealCLM.norm_iteratedFDerivWithin_comp_left
              (f := fun w : ℂ => radialStep (ρ i / 8) (ρ i / 3) ‖w‖)
              (hf0.contDiffWithinAt hw) hU'open.uniqueDiffOn hw (natCast_le_top_nat t)
        _ = ‖iteratedFDerivWithin ℝ t
              ((radialStep (ρ i / 8) (ρ i / 3)) ∘ (fun w : ℂ => ‖w‖))
              {w : ℂ | ρ i / 16 < ‖w‖} w‖ := by
              rw [Complex.ofRealCLM_norm, one_mul]
        _ ≤ Cs t := hCs t h w hw
  have hgbound : ∀ j ≤ m, ‖iteratedFDerivWithin ℝ j dirn {w : ℂ | ρ i / 16 < ‖w‖} w‖
      ≤ max (Cd j) 1 * (16 / ρ i) ^ j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      rw [norm_iteratedFDerivWithin_zero]
      have h1 : (1:ℝ) ≤ max (Cd 0) 1 := le_max_right _ _
      have h2 : max (Cd 0) 1 * (16 / ρ i) ^ 0 = max (Cd 0) 1 := by ring
      rw [h2]
      exact le_trans (norm_dirn_le w) h1
    · rw [iteratedFDerivWithin_of_isOpen j hU'open hw]
      refine le_trans (hd j w (hw0 w hw)) ?_
      have hpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr (hw0 w hw)
      have hρ16 : (0:ℝ) < ρ i / 16 := by positivity
      have h1' : 1 / ‖w‖ < 16 / ρ i := by
        rw [show (16:ℝ) / ρ i = 1 / (ρ i / 16) from (one_div_div (ρ i) 16).symm, one_div, one_div,
          inv_lt_inv₀ hpos hρ16]
        exact hw
      have h2 : (1 / ‖w‖) ^ j ≤ (16 / ρ i) ^ j := pow_le_pow_left₀ (by positivity) h1'.le _
      refine le_trans (mul_le_mul_of_nonneg_left h2 (le_of_lt (hd0 j)))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hmul := norm_iteratedFDerivWithin_mul_le (f := fun w : ℂ =>
      ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ)) (g := dirn) hf1 hg1
    hU'open.uniqueDiffOn hw (natCast_le_top_nat m)
  have hcongr : iteratedFDerivWithin ℝ m (u0 ρ i) {w : ℂ | ρ i / 16 < ‖w‖} w
      = iteratedFDerivWithin ℝ m
        (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ) * dirn w)
        {w : ℂ | ρ i / 16 < ‖w‖} w := by congr 1
  rw [← iteratedFDerivWithin_of_isOpen m hU'open hw, hcongr]
  refine le_trans hmul (Finset.sum_le_sum fun t ht => ?_)
  have him : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have hjm : m - t ≤ m := Nat.sub_le _ _
  have h0 : (0:ℝ) ≤ max (Cs t) 1 := le_trans zero_le_one (le_max_right _ _)
  have hinner : ‖iteratedFDerivWithin ℝ t
        (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ))
        {w : ℂ | ρ i / 16 < ‖w‖} w‖
      * ‖iteratedFDerivWithin ℝ (m - t) dirn {w : ℂ | ρ i / 16 < ‖w‖} w‖
      ≤ max (Cs t) 1 * (max (Cd (m - t)) 1 * (16 / ρ i) ^ (m - t)) :=
    mul_le_mul (hfbound t him) (hgbound (m - t) hjm) (norm_nonneg _) h0
  calc (m.choose t : ℝ) * ‖iteratedFDerivWithin ℝ t
        (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ))
        {w : ℂ | ρ i / 16 < ‖w‖} w‖
        * ‖iteratedFDerivWithin ℝ (m - t) dirn {w : ℂ | ρ i / 16 < ‖w‖} w‖
      = (m.choose t : ℝ) * (‖iteratedFDerivWithin ℝ t
          (fun w : ℂ => ((radialStep (ρ i / 8) (ρ i / 3) ‖w‖ : ℝ) : ℂ))
          {w : ℂ | ρ i / 16 < ‖w‖} w‖
          * ‖iteratedFDerivWithin ℝ (m - t) dirn {w : ℂ | ρ i / 16 < ‖w‖} w‖) := by ring
    _ ≤ (m.choose t : ℝ) * (max (Cs t) 1 * (max (Cd (m - t)) 1 * (16 / ρ i) ^ (m - t))) :=
        mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
    _ = (m.choose t : ℝ) * (max (Cs t) 1)
        * (max (Cd (m - t)) 1 * (16 / ρ i) ^ (m - t)) := by ring


/-- Bound for the logarithm with a constant subtracted. -/
lemma norm_iteratedFDeriv_log_sub_const (c r : ℝ) (hr : 0 < r) (l : ℕ) (hl : 1 ≤ l) :
    ‖iteratedFDeriv ℝ l (fun r : ℝ => c - Real.log r) r‖ = ‖iteratedFDeriv ℝ l Real.log r‖ := by
  have hct : ContDiffAt ℝ (l : ℕ∞) (fun r : ℝ => Real.log r - c) r :=
    (Real.contDiffAt_log.mpr (ne_of_gt hr)).sub contDiffAt_const
  have h1 : (fun r : ℝ => c - Real.log r) = (fun r : ℝ => (-1 : ℝ) • (Real.log r - c)) := by
    funext s; ring
  have hf : DifferentiableOn ℝ Real.log (Set.Ioi 0) :=
    ((Real.contDiffOn_log (n := ⊤)).differentiableOn (by simp)).mono
      (by intro r hr; exact ne_of_gt hr)
  have h2 : ‖iteratedFDerivWithin ℝ l (fun r : ℝ => Real.log r - c) (Set.Ioi 0) r‖
      = ‖iteratedFDerivWithin ℝ l Real.log (Set.Ioi 0) r‖ :=
    norm_iteratedFDerivWithin_sub_const isOpen_Ioi.uniqueDiffOn hf c (Set.mem_Ioi.mpr hr) l hl
  rw [iteratedFDerivWithin_of_isOpen l isOpen_Ioi (Set.mem_Ioi.mpr hr),
    iteratedFDerivWithin_of_isOpen l isOpen_Ioi (Set.mem_Ioi.mpr hr)] at h2
  rw [h1, iteratedFDeriv_const_smul_apply' (i := l) (a := (-1 : ℝ)) hct, norm_smul, h2]
  simp

/-- Global bound for `u0`. -/
lemma exists_bound_u0 (hρ : 0 < ρ i) :
    ∃ D : ℕ → ℝ, ∀ m, 1 ≤ m → ∀ w : ℂ,
      ‖iteratedFDeriv ℝ m (u0 ρ i) w‖ ≤ D m := by
  obtain ⟨DU, hDU⟩ := exists_bound_u0_on_U (ρ := ρ) (i := i) hρ
  refine ⟨fun m => max (DU m) 0, fun m hm w => ?_⟩
  by_cases hw : ρ i / 8 ≤ ‖w‖
  · refine le_trans (hDU m hm w (by linarith [show (0:ℝ) < ρ i / 8 by positivity]))
      (le_max_left _ _)
  · push_neg at hw
    have hV : IsOpen {w : ℂ | ‖w‖ < ρ i / 8} := isOpen_lt continuous_norm continuous_const
    have hEq : Set.EqOn (0 : ℂ → ℂ) (u0 ρ i) {w : ℂ | ‖w‖ < ρ i / 8} := by
      intro x hx
      have hr : radialStep (ρ i / 8) (ρ i / 3) ‖x‖ = 0 :=
        radialStep_of_le (by linarith [show (0:ℝ) < ρ i / 8 by positivity]) (le_of_lt hx)
      simp [u0, dirn, hr]
    have h1 : iteratedFDerivWithin ℝ m (0 : ℂ → ℂ) {w : ℂ | ‖w‖ < ρ i / 8} w
        = iteratedFDerivWithin ℝ m (u0 ρ i) {w : ℂ | ‖w‖ < ρ i / 8} w :=
      iteratedFDerivWithin_congr hEq hw m
    rw [iteratedFDerivWithin_zero] at h1
    rw [← iteratedFDerivWithin_of_isOpen m hV hw, ← h1]
    simp only [Pi.zero_apply, norm_zero]
    exact le_max_right _ _


lemma contDiffOn_Tfun (hρ : 0 < ρ i) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Tfun ρ i) {r : ℝ | ρ i / 16 < r} := by
  have hpos : (0:ℝ) < ρ i / 16 := by positivity
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun r : ℝ => radialStep (ρ i / 8) (ρ i / 4) r)
      {r : ℝ | ρ i / 16 < r} := (ChartSmooth.contDiff_radialStep _ _).contDiffOn
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) Real.log {r : ℝ | ρ i / 16 < r} :=
    Real.contDiffOn_log.mono (fun r hr => by
      rw [Set.mem_setOf_eq] at hr
      exact ne_of_gt (lt_trans hpos hr))
  have h1 : ContDiffOn ℝ (⊤:ℕ∞) (fun r : ℝ => (1 - radialStep (ρ i / 8) (ρ i / 4) r) * Real.log 4)
      {r : ℝ | ρ i / 16 < r} := (contDiffOn_const.sub hs).mul contDiffOn_const
  have h2 : ContDiffOn ℝ (⊤:ℕ∞)
      (fun r : ℝ => radialStep (ρ i / 8) (ρ i / 4) r * (Real.log (ρ i) - Real.log r))
      {r : ℝ | ρ i / 16 < r} := hs.mul (contDiffOn_const.sub hlog)
  exact h1.add h2

lemma exists_bound_Tfun (hρ : 0 < ρ i) :
    ∃ B : ℕ → ℝ, ∀ l, 1 ≤ l → ∀ r : ℝ, ρ i / 16 < r →
      ‖iteratedFDerivWithin ℝ l (Tfun ρ i) {r : ℝ | ρ i / 16 < r} r‖ ≤ B l := by
  obtain ⟨Cl, hl0, hl⟩ := exists_bound_iteratedFDeriv_log
  have hpos16 : (0:ℝ) < ρ i / 16 := by positivity
  have hpos8 : (0:ℝ) < ρ i / 8 := by positivity
  have hpos4 : (0:ℝ) < ρ i / 4 := by positivity
  have htopen : IsOpen {r : ℝ | ρ i / 16 < r} := isOpen_lt continuous_const continuous_id
  have hT : ContDiffOn ℝ (⊤ : ℕ∞) (Tfun ρ i) {r : ℝ | ρ i / 16 < r} :=
    contDiffOn_Tfun (ρ := ρ) (i := i) hρ
  have hcomp : ∀ l, ∃ C, ∀ r ∈ Set.Icc (ρ i / 8) (ρ i / 4),
      ‖iteratedFDerivWithin ℝ l (Tfun ρ i) {r : ℝ | ρ i / 16 < r} r‖ ≤ C := by
    intro l
    have hsub : Set.Icc (ρ i / 8) (ρ i / 4) ⊆ {r : ℝ | ρ i / 16 < r} := by
      intro r hr; exact lt_of_lt_of_le (by linarith) hr.1
    exact isCompact_Icc.exists_bound_of_continuousOn
      ((hT.continuousOn_iteratedFDerivWithin (natCast_le_top_nat l) htopen.uniqueDiffOn).mono hsub)
  choose Cc hCc using hcomp
  refine ⟨fun l => max (Cl l * (16 / ρ i) ^ l) (Cc l), fun l hll r hr => ?_⟩
  rcases lt_trichotomy r (ρ i / 4) with hlt | heq | hgt
  · rcases lt_trichotomy r (ρ i / 8) with hlt' | heq' | hgt'
    · have hU : IsOpen {s : ℝ | s < ρ i / 8} := isOpen_lt continuous_id continuous_const
      have hEq : Set.EqOn (Tfun ρ i) (fun _ => Real.log 4) {s : ℝ | s < ρ i / 8} := by
        intro s hs
        rw [Tfun, radialStep_of_le (by linarith) hs.le]
        ring
      have h1 : iteratedFDerivWithin ℝ l (Tfun ρ i) {s : ℝ | s < ρ i / 8} r
          = iteratedFDerivWithin ℝ l (Tfun ρ i) {s : ℝ | ρ i / 16 < s} r := by
        rw [iteratedFDerivWithin_of_isOpen l hU hlt', iteratedFDerivWithin_of_isOpen l htopen hr]
      have h3 : iteratedFDerivWithin ℝ l (Tfun ρ i) {s : ℝ | s < ρ i / 8} r = 0 := by
        rw [iteratedFDerivWithin_congr hEq hlt' l,
          iteratedFDerivWithin_const_of_ne (𝕜 := ℝ) (s := {s : ℝ | s < ρ i / 8}) (by omega) (Real.log 4)]
        simp
      rw [← h1, h3, norm_zero]
      exact le_trans (le_of_lt (mul_pos (hl0 l) (pow_pos (by positivity) l))) (le_max_left _ _)
    · rw [heq']
      exact le_trans (hCc l _ ⟨le_rfl, by linarith⟩) (le_max_right _ _)
    · exact le_trans (hCc l _ ⟨hgt'.le, hlt.le⟩) (le_max_right _ _)
  · rw [heq]
    exact le_trans (hCc l _ ⟨by linarith, le_rfl⟩) (le_max_right _ _)
  · have hJ : IsOpen {s : ℝ | ρ i / 4 < s} := isOpen_lt continuous_const continuous_id
    have hEq : Set.EqOn (Tfun ρ i) (fun s : ℝ => Real.log (ρ i) - Real.log s)
        {s : ℝ | ρ i / 4 < s} := by
      intro s hs
      rw [Tfun, radialStep_of_ge (by linarith) hs.le]
      ring
    have hL : iteratedFDerivWithin ℝ l (Tfun ρ i) {s : ℝ | ρ i / 4 < s} r
        = iteratedFDeriv ℝ l (Tfun ρ i) r := iteratedFDerivWithin_of_isOpen l hJ hgt
    have hR : iteratedFDerivWithin ℝ l (fun s : ℝ => Real.log (ρ i) - Real.log s)
        {s : ℝ | ρ i / 4 < s} r
        = iteratedFDeriv ℝ l (fun s : ℝ => Real.log (ρ i) - Real.log s) r :=
      iteratedFDerivWithin_of_isOpen l hJ hgt
    have h3 : iteratedFDeriv ℝ l (Tfun ρ i) r
        = iteratedFDeriv ℝ l (fun s : ℝ => Real.log (ρ i) - Real.log s) r := by
      rw [← hL, ← hR]
      exact iteratedFDerivWithin_congr hEq hgt l
    have h4 := norm_iteratedFDeriv_log_sub_const (Real.log (ρ i)) r (by linarith) l hll
    have hpow : (1 / r) ^ l ≤ (16 / ρ i) ^ l := by
      refine pow_le_pow_left₀ (le_of_lt (one_div_pos.mpr (lt_trans hpos16 hr))) ?_ l
      rw [div_le_div_iff₀ (lt_trans hpos16 hr) (by linarith : (0:ℝ) < ρ i)]
      nlinarith [hr.le, hpos16]
    calc ‖iteratedFDerivWithin ℝ l (Tfun ρ i) {r : ℝ | ρ i / 16 < r} r‖
        = ‖iteratedFDeriv ℝ l Real.log r‖ := by
          rw [iteratedFDerivWithin_of_isOpen l htopen hr, h3, h4]
      _ ≤ Cl l * (1 / r) ^ l := hl l hll r (by linarith)
      _ ≤ Cl l * (16 / ρ i) ^ l := mul_le_mul_of_nonneg_left hpow (le_of_lt (hl0 l))
      _ ≤ max (Cl l * (16 / ρ i) ^ l) (Cc l) := le_max_left _ _

/-- Global bound for `tau0`. -/
lemma exists_bound_tau0 (hρ : 0 < ρ i) :
    ∃ D : ℕ → ℝ, ∀ m, 1 ≤ m → ∀ w : ℂ,
      ‖iteratedFDeriv ℝ m (tau0 ρ i) w‖ ≤ D m := by
  obtain ⟨B, hB⟩ := exists_bound_Tfun (ρ := ρ) (i := i) hρ
  obtain ⟨A, hA⟩ := exists_norm_bound_on_U (ρ := ρ) (i := i) hρ
  have hU'open : IsOpen {w : ℂ | ρ i / 16 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hw0 : ∀ w : ℂ, ρ i / 16 < ‖w‖ → w ≠ 0 := by
    intro w hw h
    rw [h, norm_zero] at hw
    linarith [show (0:ℝ) < ρ i / 16 by positivity]
  have hν : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w‖) {w : ℂ | ρ i / 16 < ‖w‖} :=
    fun x hx => ((contDiffAt_norm ℝ (hw0 x hx)).contDiffWithinAt).of_le le_top
  have hT : ContDiffOn ℝ (⊤ : ℕ∞) (Tfun ρ i) {r : ℝ | ρ i / 16 < r} :=
    contDiffOn_Tfun (ρ := ρ) (i := i) hρ
  have hst : Set.MapsTo (fun w : ℂ => ‖w‖) {w : ℂ | ρ i / 16 < ‖w‖} {r : ℝ | ρ i / 16 < r} :=
    fun x hx => hx
  obtain ⟨C, hC⟩ := exists_bound_comp hU'open (isOpen_lt continuous_const continuous_id) hν hT hst
    A hA B hB
  refine ⟨fun m => max (C m) 0, fun m hm w => ?_⟩
  by_cases hw : ρ i / 8 ≤ ‖w‖
  · have hmem : w ∈ {w : ℂ | ρ i / 16 < ‖w‖} :=
      lt_of_lt_of_le (by linarith [show (0:ℝ) < ρ i / 8 by positivity]) hw
    have hfun : tau0 ρ i = Tfun ρ i ∘ (fun w : ℂ => ‖w‖) := by
      funext x; rw [Function.comp_apply, tau0_eq_Tfun]
    rw [hfun, ← iteratedFDerivWithin_of_isOpen m hU'open hmem]
    exact le_trans (hC m hm w hmem) (le_max_left _ _)
  · push_neg at hw
    have hV : IsOpen {w : ℂ | ‖w‖ < ρ i / 8} := isOpen_lt continuous_norm continuous_const
    have hEq : Set.EqOn (fun _ : ℂ => Real.log 4) (tau0 ρ i) {w : ℂ | ‖w‖ < ρ i / 8} := by
      intro x hx
      have hr : radialStep (ρ i / 8) (ρ i / 4) ‖x‖ = 0 :=
        radialStep_of_le (by linarith [show (0:ℝ) < ρ i / 8 by positivity]) (le_of_lt hx)
      rw [tau0, hr]
      ring
    have h1 : iteratedFDerivWithin ℝ m (fun _ : ℂ => Real.log 4) {w : ℂ | ‖w‖ < ρ i / 8} w
        = iteratedFDerivWithin ℝ m (tau0 ρ i) {w : ℂ | ‖w‖ < ρ i / 8} w :=
      iteratedFDerivWithin_congr hEq hw m
    rw [iteratedFDerivWithin_const_of_ne (𝕜 := ℝ) (s := {w : ℂ | ‖w‖ < ρ i / 8}) (by omega)
      (Real.log 4)] at h1
    rw [← iteratedFDerivWithin_of_isOpen m hV hw, ← h1]
    simp only [Pi.zero_apply, norm_zero]
    exact le_max_right _ _


/-! ## Bounds for the chart -/

/-- The `update` of the `i`-th coordinate, as a continuous linear map. -/
def updCLM (i : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun j =>
    if j = i then ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ))

lemma updCLM_apply (i : Fin n) (x : Fin n → ℂ) (c : ℂ) :
    updCLM i (x, c) = Function.update x i c := by
  funext j
  rw [updCLM, ContinuousLinearMap.pi_apply]
  by_cases h : j = i
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

lemma norm_updCLM_le (i : Fin n) : ‖updCLM i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  rw [updCLM_apply, one_mul, Prod.norm_def]
  refine (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr fun j => ?_
  rw [Function.update_apply]
  split_ifs with h
  · exact le_max_right _ _
  · exact le_trans (norm_le_pi_norm p.1 j) (le_max_left _ _)

lemma norm_proj_le (i : Fin n) :
    ‖(ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact norm_le_pi_norm x i

/-- Left composition with a continuous linear map, for global iterated derivatives. -/
lemma norm_iteratedFDeriv_comp_clm_left {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : Y →L[ℝ] Z) {F : X → Y} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∀ (m : ℕ) (z : X), ‖iteratedFDeriv ℝ m (L ∘ F) z‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m F z‖ := by
  intro m z
  have h := L.norm_iteratedFDerivWithin_comp_left (s := Set.univ)
    ((hF.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) F Set.univ) z (Set.mem_univ z))
    uniqueDiffOn_univ (Set.mem_univ z) (natCast_le_top_nat m)
  rwa [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h

/-- Right composition with a continuous linear map, for global iterated derivatives. -/
lemma norm_iteratedFDeriv_comp_clm_right {X X' Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup X'] [NormedSpace ℝ X'] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (L : X' →L[ℝ] X) {F : X → Y} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∀ (m : ℕ) (z : X'), ‖iteratedFDeriv ℝ m (F ∘ L) z‖
      ≤ ‖iteratedFDeriv ℝ m F (L z)‖ * ‖L‖ ^ m := by
  intro m z
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (f := F) (s := Set.univ) L
    hF.contDiffOn uniqueDiffOn_univ (by simp) (x := z) (by simp) (i := m) (natCast_le_top_nat m)
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [h]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_fin]

/-- The chart maps have bounded derivatives of positive order. -/
lemma exists_bound_iteratedFDeriv_chartPoint (hρ : 0 < ρ i) :
    ∃ D : ℕ → ℝ, ∀ m, 1 ≤ m → ∀ z : Fin n → ℂ,
      ‖iteratedFDeriv ℝ m (chartPoint ρ i) z‖ ≤ D m := by
  obtain ⟨Du, hDu⟩ := exists_bound_u0 (ρ := ρ) (i := i) hρ
  obtain ⟨Dt, hDt⟩ := exists_bound_tau0 (ρ := ρ) (i := i) hρ
  have hu0c : ContDiff ℝ (⊤ : ℕ∞) (u0 ρ i) := contDiff_u0 (ρ := ρ) (i := i) hρ
  have htauc : ContDiff ℝ (⊤ : ℕ∞) (tau0 ρ i) := contDiff_tau0 (ρ := ρ) (i := i) hρ
  -- the two components
  have hΦ1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ => Function.update z i (u0 ρ i (z i))) := by
    have h1 : (fun z : Fin n → ℂ => Function.update z i (u0 ρ i (z i)))
        = updCLM i ∘ (fun z : Fin n → ℂ => (z, u0 ρ i (z i))) := by
      funext z; rw [Function.comp_apply, updCLM_apply]
    rw [h1]
    refine (updCLM i).contDiff.comp ?_
    exact contDiff_id.prodMk (hu0c.comp ((ContinuousLinearMap.proj (R := ℝ) i :
      (Fin n → ℂ) →L[ℝ] ℂ).contDiff))
  have hΦ2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℂ => tau0 ρ i (z i)) :=
    htauc.comp ((ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ).contDiff)
  refine ⟨fun m => (1 + (1 + Du m)) + Dt m, fun m hm z => ?_⟩
  have hpair : iteratedFDeriv ℝ m (chartPoint ρ i) z
      = (iteratedFDeriv ℝ m (fun z : Fin n → ℂ => Function.update z i (u0 ρ i (z i))) z).prod
        (iteratedFDeriv ℝ m (fun z : Fin n → ℂ => tau0 ρ i (z i)) z) := by
    rw [show chartPoint ρ i = (fun z : Fin n → ℂ =>
        (Function.update z i (u0 ρ i (z i)), tau0 ρ i (z i))) from by
      funext w; rw [chartPoint, chartU_eq_u0, chartT_eq_tau0]]
    exact iteratedFDeriv_prodMk (x := z) (hΦ1.contDiffAt) (hΦ2.contDiffAt) (natCast_le_top_nat m)
  rw [hpair]
  refine le_trans (norm_prod_le _ _) ?_
  have h1b : ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => Function.update z i (u0 ρ i (z i))) z‖
      ≤ 1 + (1 + Du m) := by
    have hfun : (fun z : Fin n → ℂ => Function.update z i (u0 ρ i (z i)))
        = updCLM i ∘ (fun z : Fin n → ℂ => (z, u0 ρ i (z i))) := by
      funext w; rw [Function.comp_apply, updCLM_apply]
    rw [hfun]
    have hstep := norm_iteratedFDeriv_comp_clm_left (updCLM i)
      (F := fun z : Fin n → ℂ => (z, u0 ρ i (z i))) (contDiff_id.prodMk
        (hu0c.comp ((ContinuousLinearMap.proj (R := ℝ) i :
          (Fin n → ℂ) →L[ℝ] ℂ).contDiff))) m z
    refine le_trans hstep ?_
    have hidb : ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => z) z‖ ≤ 1 :=
      le_trans (norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ (Fin n → ℂ)) m hm z)
        ContinuousLinearMap.norm_id_le
    have hu0b : ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => u0 ρ i (z i)) z‖ ≤ Du m := by
      refine le_trans (norm_iteratedFDeriv_comp_clm_right
        (ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ) hu0c m z) ?_
      have h1 : ‖(ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ m ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (norm_proj_le i)
      calc ‖iteratedFDeriv ℝ m (u0 ρ i) (z i)‖
            * ‖(ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ m
          ≤ ‖iteratedFDeriv ℝ m (u0 ρ i) (z i)‖ * 1 :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ m (u0 ρ i) (z i)‖ := by rw [mul_one]
        _ ≤ Du m := hDu m hm (z i)
    have hprod2 : ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => (z, u0 ρ i (z i))) z‖
        ≤ 1 + Du m := by
      have hprod := iteratedFDeriv_prodMk (f := fun z : Fin n → ℂ => z)
        (g := fun z : Fin n → ℂ => u0 ρ i (z i)) (x := z) contDiff_id.contDiffAt
        ((hu0c.comp ((ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ).contDiff)).contDiffAt)
        (natCast_le_top_nat m)
      rw [hprod]
      exact le_trans (norm_prod_le _ _) (add_le_add hidb hu0b)
    calc ‖updCLM i‖ * ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => (z, u0 ρ i (z i))) z‖
        ≤ 1 * ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => (z, u0 ρ i (z i))) z‖ :=
          mul_le_mul_of_nonneg_right (norm_updCLM_le i) (norm_nonneg _)
      _ ≤ 1 * (1 + Du m) := mul_le_mul_of_nonneg_left hprod2 (by norm_num)
      _ ≤ 1 + (1 + Du m) := by linarith
  have h2b : ‖iteratedFDeriv ℝ m (fun z : Fin n → ℂ => tau0 ρ i (z i)) z‖ ≤ Dt m := by
    refine le_trans (norm_iteratedFDeriv_comp_clm_right
      (ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ) htauc m z) ?_
    have h1 : ‖(ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ m ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_proj_le i)
    calc ‖iteratedFDeriv ℝ m (tau0 ρ i) (z i)‖
          * ‖(ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ m
        ≤ ‖iteratedFDeriv ℝ m (tau0 ρ i) (z i)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ m (tau0 ρ i) (z i)‖ := by rw [mul_one]
      _ ≤ Dt m := hDt m hm (z i)
  linarith


/-- Lipschitz bound for the chart. -/
lemma exists_lipschitz_chartPoint (hρ : 0 < ρ i) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Fin n → ℂ,
      ‖chartPoint ρ i x - chartPoint ρ i y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨D, hD⟩ := exists_bound_iteratedFDeriv_chartPoint (ρ := ρ) (i := i) hρ
  have hc : ContDiff ℝ (⊤ : ℕ∞) (chartPoint ρ i) := ChartSmooth.contDiff_chartPoint (i := i) hρ
  refine ⟨D 1, le_trans (norm_nonneg _) (hD 1 le_rfl 0), fun x y => ?_⟩
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (C := D 1)
    (fun z _ => (hc.differentiable (by simp)).differentiableAt) (fun z _ => ?_) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  rw [← norm_iteratedFDeriv_one (chartPoint ρ i)]
  exact hD 1 le_rfl z

/-- Hölder bound (exponent `α ≤ 1`) for the iterated derivatives of the chart. -/
lemma exists_holderE_chartPoint (hρ : 0 < ρ i) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ E : ℕ → ℝ, ∀ k, 1 ≤ k → ∀ x y : Fin n → ℂ,
      ‖iteratedFDeriv ℝ k (chartPoint ρ i) x - iteratedFDeriv ℝ k (chartPoint ρ i) y‖
        ≤ E k * ‖x - y‖ ^ α := by
  obtain ⟨D, hD⟩ := exists_bound_iteratedFDeriv_chartPoint (ρ := ρ) (i := i) hρ
  have hc : ContDiff ℝ (⊤ : ℕ∞) (chartPoint ρ i) := ChartSmooth.contDiff_chartPoint (i := i) hρ
  refine ⟨fun k => max (D (k+1)) (2 * D k), fun k hk x y => ?_⟩
  have hDk : 0 ≤ D k := le_trans (norm_nonneg _) (hD k hk 0)
  have hDk1 : 0 ≤ D (k+1) := le_trans (norm_nonneg _) (hD (k+1) (by omega) 0)
  rcases eq_or_ne x y with rfl | hne
  · simp [Real.zero_rpow hα.ne']
  · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rcases lt_or_ge (1:ℝ) ‖x - y‖ with hxy | hxy
    · have hone : (1:ℝ) ≤ ‖x - y‖ ^ α := Real.one_le_rpow hxy.le hα.le
      have hEk : 0 ≤ max (D (k+1)) (2 * D k) := le_trans hDk1 (le_max_left _ _)
      calc ‖iteratedFDeriv ℝ k (chartPoint ρ i) x - iteratedFDeriv ℝ k (chartPoint ρ i) y‖
          ≤ ‖iteratedFDeriv ℝ k (chartPoint ρ i) x‖ + ‖iteratedFDeriv ℝ k (chartPoint ρ i) y‖ :=
            norm_sub_le _ _
        _ ≤ D k + D k := add_le_add (hD k hk x) (hD k hk y)
        _ = 2 * D k := by ring
        _ ≤ (2 * D k) * ‖x - y‖ ^ α := le_mul_of_one_le_right (by linarith) hone
        _ ≤ max (D (k+1)) (2 * D k) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α)
    · have hle : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
        have h1 : ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) = ‖x - y‖ := by
          rw [← Real.rpow_add hpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
        have h2 : ‖x - y‖ ^ (1 - α) ≤ 1 :=
          Real.rpow_le_one (norm_nonneg (x - y)) hxy (sub_nonneg.mpr hα1)
        calc ‖x - y‖ = ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) := h1.symm
          _ ≤ ‖x - y‖ ^ α * 1 :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg (x - y)) α)
          _ = ‖x - y‖ ^ α := mul_one _
      have hdiff : ∀ z : Fin n → ℂ, DifferentiableAt ℝ
          (fun w => iteratedFDeriv ℝ k (chartPoint ρ i) w) z := by
        intro z
        have h1 : ContDiff ℝ (1 : WithTop ℕ∞)
            (fun w => iteratedFDeriv ℝ k (chartPoint ρ i) w) :=
          hc.iteratedFDeriv_right (i := k) (WithTop.coe_le_coe.mpr le_top)
        exact (h1.differentiable (by simp)).differentiableAt
      have hbound : ∀ z : Fin n → ℂ,
          ‖fderiv ℝ (fun w => iteratedFDeriv ℝ k (chartPoint ρ i) w) z‖ ≤ D (k+1) := by
        intro z
        rw [norm_fderiv_iteratedFDeriv]
        exact hD (k+1) (by omega) z
      have hmvt : ‖iteratedFDeriv ℝ k (chartPoint ρ i) x - iteratedFDeriv ℝ k (chartPoint ρ i) y‖
          ≤ D (k+1) * ‖x - y‖ := by
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
          (f := fun w => iteratedFDeriv ℝ k (chartPoint ρ i) w) (C := D (k+1))
          (fun z _ => hdiff z) (fun z _ => hbound z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
        simpa only [norm_sub_rev] using h
      refine le_trans hmvt ?_
      calc D (k+1) * ‖x - y‖ ≤ D (k+1) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left hle hDk1
        _ ≤ max (D (k+1)) (2 * D k) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)

/-- Elementary division inequality behind the Hölder estimate. -/
lemma div_rpow_le_mul_div_rpow' {r M p q α : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hα : 0 < α)
    (hp : 0 < p) (hpq : p ≤ M * q) : r / q ^ α ≤ M ^ α * (r / p ^ α) := by
  have hq : 0 < q := by
    by_contra h
    have hq0 : q ≤ 0 := le_of_not_gt h
    have : M * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM hq0
    linarith
  have hpq' : p ^ α ≤ M ^ α * q ^ α := by
    calc p ^ α ≤ (M * q) ^ α := Real.rpow_le_rpow hp.le hpq hα.le
      _ = M ^ α * q ^ α := Real.mul_rpow hM hq.le
  have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  have hqα : 0 < q ^ α := Real.rpow_pos_of_pos hq α
  rw [← mul_div_assoc, le_div_iff₀ hpα, div_mul_eq_mul_div, div_le_iff₀ hqα]
  calc r * p ^ α ≤ r * (M ^ α * q ^ α) := mul_le_mul_of_nonneg_left hpq' hr
    _ = M ^ α * r * q ^ α := by ring


/-! ## The main theorem -/

theorem holderNorm_comp_chartPoint {n : ℕ} {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (u : (Fin n → ℂ) × ℝ → ℂ) (s : Set (Fin n → ℂ)) (t : Set ((Fin n → ℂ) × ℝ)),
        IsOpen s → IsOpen t → Set.MapsTo (Work.NN.Final.chartPoint ρ i) s t →
        (∀ m : ℕ, ContDiffOn ℝ m u t) →
        Work.CR.Flat.holderNorm k α (u ∘ Work.NN.Final.chartPoint ρ i) s
          ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α u t := by
  obtain ⟨D, hD⟩ := exists_bound_iteratedFDeriv_chartPoint (ρ := ρ) (i := i) hρ
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_chartPoint (ρ := ρ) (i := i) hρ
  have hΦc : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (chartPoint ρ i) Set.univ :=
    fun m => (ChartSmooth.contDiff_chartPoint (i := i) hρ).contDiffOn.of_le (natCast_le_top_nat m)
  by_cases hα1 : α ≤ 1
  · obtain ⟨E, hE⟩ := exists_holderE_chartPoint (ρ := ρ) (i := i) hρ hα hα1
    obtain ⟨C, hC0, hC⟩ := holderNorm_comp_univ (Φ := chartPoint ρ i) hΦc L hL α hα
      D (fun k _ x => hD k (by omega) x) E hE
    exact ⟨C, hC0, fun k u s t hs ht hst hu => hC k s t u hs ht hst hu⟩
  · push_neg at hα1
    refine ⟨fun k => max 1 (L ^ α), fun k => lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro k u s t hs ht hst hu
    by_cases htop : Work.CR.Flat.holderNorm k α u t = ⊤
    · have hpos : ENNReal.ofReal (max 1 (L ^ α)) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
      rw [htop, ENNReal.mul_top hpos]
      exact le_top
    · have hM0 : 0 ≤ (Work.CR.Flat.holderNorm k α u t).toReal := ENNReal.toReal_nonneg
      have hhold : ∀ a ∈ t, ∀ b ∈ t,
          ‖u a - u b‖ ≤ (Work.CR.Flat.holderNorm k α u t).toReal * ‖a - b‖ ^ α := by
        intro a ha b hb
        rcases eq_or_ne a b with rfl | hab
        · simp [Real.zero_rpow hα.ne']
        · have hterm : ENNReal.ofReal (‖u a - u b‖ / ‖a - b‖ ^ α)
              ≤ Work.CR.Flat.holderNorm k α u t := by
            refine le_trans ?_ (holderSeminorm_le_holderNorm k α u t (Nat.zero_le k))
            simpa only [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub] using
              (le_holderSeminorm 0 α u t ha hb hab)
          have h2 := ENNReal.toReal_mono htop hterm
          rw [ENNReal.toReal_ofReal (by positivity)] at h2
          rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) α)] at h2
          exact h2
      have hcomp : ∀ x ∈ s, ∀ y ∈ s, ‖(u ∘ chartPoint ρ i) x - (u ∘ chartPoint ρ i) y‖
          ≤ ((Work.CR.Flat.holderNorm k α u t).toReal * L ^ α) * ‖x - y‖ ^ α := by
        intro x hx y hy
        have h1 := hhold (chartPoint ρ i x) (hst hx) (chartPoint ρ i y) (hst hy)
        have h2 := hL x y
        have h3 : ‖chartPoint ρ i x - chartPoint ρ i y‖ ^ α ≤ (L * ‖x - y‖) ^ α :=
          Real.rpow_le_rpow (norm_nonneg _) h2 hα.le
        have h4 : (L * ‖x - y‖) ^ α = L ^ α * ‖x - y‖ ^ α := Real.mul_rpow hL0 (norm_nonneg _)
        calc ‖(u ∘ chartPoint ρ i) x - (u ∘ chartPoint ρ i) y‖
            ≤ (Work.CR.Flat.holderNorm k α u t).toReal
                * ‖chartPoint ρ i x - chartPoint ρ i y‖ ^ α := h1
          _ ≤ (Work.CR.Flat.holderNorm k α u t).toReal * (L * ‖x - y‖) ^ α :=
              mul_le_mul_of_nonneg_left h3 hM0
          _ = ((Work.CR.Flat.holderNorm k α u t).toReal * L ^ α) * ‖x - y‖ ^ α := by
              rw [h4]; ring
      have hloc : ∀ x ∈ s, ∀ᶠ y in nhds x, (u ∘ chartPoint ρ i) y = (u ∘ chartPoint ρ i) x :=
        eventuallyEq_of_holderOn_one_lt (u := u ∘ chartPoint ρ i) (M := _) (α := α) hs hα1
          (mul_nonneg hM0 (Real.rpow_nonneg hL0 α)) hcomp
      have hzero : ∀ (j : ℕ), 1 ≤ j → ∀ x ∈ s,
          iteratedFDerivWithin ℝ j (u ∘ chartPoint ρ i) s x = 0 := by
        intro j hj x hx
        obtain ⟨W, hWmem, hWeq⟩ := Filter.eventually_iff_exists_mem.mp (hloc x hx)
        obtain ⟨U, hUs, hUopen, hxU⟩ := mem_nhds_iff.mp hWmem
        have hconst : (u ∘ chartPoint ρ i) =ᶠ[nhds x] (fun _ => (u ∘ chartPoint ρ i) x) :=
          Filter.eventually_of_mem (IsOpen.mem_nhds hUopen hxU) (fun y hy => hWeq y (hUs hy))
        have h1 : iteratedFDeriv ℝ j (u ∘ chartPoint ρ i) x = 0 := by
          have h2 := (hconst.iteratedFDeriv ℝ j).eq_of_nhds
          rw [h2, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega) ((u ∘ chartPoint ρ i) x)]
          simp
        rw [iteratedFDerivWithin_of_isOpen j hs hx, h1]
      have hzeroD : ∀ (j : ℕ), 1 ≤ j → iterDerivNorm j (u ∘ chartPoint ρ i) s = 0 := by
        intro j hj
        refine le_antisymm ?_ bot_le
        refine iSup₂_le fun x hx => ?_
        rw [hzero j hj x hx, norm_zero]
        simp
      have hzeroS : ∀ (j : ℕ), 1 ≤ j → holderSeminorm j α (u ∘ chartPoint ρ i) s = 0 := by
        intro j hj
        refine le_antisymm ?_ bot_le
        refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
        simp [hzero j hj x hx, hzero j hj y hy]
      have h1 : iterDerivNorm 0 (u ∘ chartPoint ρ i) s ≤ iterDerivNorm 0 u t := by
        rw [iterDerivNorm_zero, iterDerivNorm_zero]
        refine iSup₂_le fun x hx => le_iSup₂_of_le (chartPoint ρ i x) (hst hx) ?_
        simp [Function.comp_apply]
      have h2 : holderSeminorm 0 α (u ∘ chartPoint ρ i) s
          ≤ ENNReal.ofReal (L ^ α) * holderSeminorm 0 α u t := by
        refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
        by_cases h : chartPoint ρ i x = chartPoint ρ i y
        · have hfy : (u ∘ chartPoint ρ i) x = (u ∘ chartPoint ρ i) y := by
            simp only [Function.comp_apply]; rw [h]
          rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub, hfy, sub_self, norm_zero,
            zero_div, ENNReal.ofReal_zero]
          exact bot_le
        · have hle := le_holderSeminorm 0 α u t (hst hx) (hst hy) h
          calc ENNReal.ofReal
                (‖iteratedFDerivWithin ℝ 0 (u ∘ chartPoint ρ i) s x
                  - iteratedFDerivWithin ℝ 0 (u ∘ chartPoint ρ i) s y‖ / ‖x - y‖ ^ α)
              ≤ ENNReal.ofReal (L ^ α)
                  * ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 u t (chartPoint ρ i x)
                    - iteratedFDerivWithin ℝ 0 u t (chartPoint ρ i y)‖
                    / ‖chartPoint ρ i x - chartPoint ρ i y‖ ^ α) := by
                simp only [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
                rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL0 α)]
                refine ENNReal.ofReal_le_ofReal ?_
                exact div_rpow_le_mul_div_rpow'
                  (r := ‖u (chartPoint ρ i x) - u (chartPoint ρ i y)‖) (norm_nonneg _) hL0 hα
                  (norm_pos_iff.mpr (sub_ne_zero.mpr h)) (hL x y)
            _ ≤ ENNReal.ofReal (L ^ α) * holderSeminorm 0 α u t :=
                mul_le_mul_of_nonneg_left hle bot_le
      have hsum : holderNorm k α (u ∘ chartPoint ρ i) s
          = iterDerivNorm 0 (u ∘ chartPoint ρ i) s
            + holderSeminorm 0 α (u ∘ chartPoint ρ i) s := by
        rw [holderNorm, Finset.sum_eq_single 0]
        · intro b hb hne
          rw [hzeroD b (Nat.one_le_iff_ne_zero.mpr hne), hzeroS b (Nat.one_le_iff_ne_zero.mpr hne),
            add_zero]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h
      rw [hsum]
      have h3 : iterDerivNorm 0 u t + ENNReal.ofReal (L ^ α) * holderSeminorm 0 α u t
          ≤ max 1 (ENNReal.ofReal (L ^ α))
              * (iterDerivNorm 0 u t + holderSeminorm 0 α u t) := by
        rw [mul_add]
        refine add_le_add ?_ ?_
        · exact le_mul_of_one_le_left bot_le (le_max_left (1 : ENNReal) (ENNReal.ofReal (L ^ α)))
        · exact mul_le_mul_of_nonneg_right
            (le_max_right (1 : ENNReal) (ENNReal.ofReal (L ^ α))) bot_le
      have h4 : iterDerivNorm 0 u t + holderSeminorm 0 α u t ≤ holderNorm k α u t := by
        have hle := Finset.single_le_sum
          (f := fun j => iterDerivNorm j u t + holderSeminorm j α u t)
          (fun j _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos k))
        simpa [Work.CR.Flat.holderNorm] using hle
      calc iterDerivNorm 0 (u ∘ chartPoint ρ i) s + holderSeminorm 0 α (u ∘ chartPoint ρ i) s
          ≤ iterDerivNorm 0 u t + ENNReal.ofReal (L ^ α) * holderSeminorm 0 α u t :=
            add_le_add h1 h2
        _ ≤ max 1 (ENNReal.ofReal (L ^ α))
              * (iterDerivNorm 0 u t + holderSeminorm 0 α u t) := h3
        _ = ENNReal.ofReal (max 1 (L ^ α))
              * (iterDerivNorm 0 u t + holderSeminorm 0 α u t) := by
            rw [ENNReal.ofReal_max, ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal (max 1 (L ^ α)) * holderNorm k α u t :=
            mul_le_mul_of_nonneg_left h4 bot_le

end Bounds

end Work.NN.Final.ChartComp
