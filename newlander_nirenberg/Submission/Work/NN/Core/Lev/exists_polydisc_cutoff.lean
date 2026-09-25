import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds
import Submission.Work.NN.Core.Lev.exists_smooth_step_profile

noncomputable section

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal ContDiff
open Set

/-! ## Auxiliary facts about the smooth step profile and the quadratic `‖z j‖²` -/

lemma inner_self_eq_normSq (w : ℂ) : inner ℝ w w = Complex.normSq w := by
  rw [real_inner_self_eq_norm_sq, ← Complex.normSq_eq_norm_sq]

lemma contDiff_normSq_profile : ∀ m : ℕ, ContDiff ℝ m (fun w : ℂ => Complex.normSq w) := by
  intro m
  have h : (fun w : ℂ => Complex.normSq w)
      = fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w; rw [Complex.normSq_apply]; rfl
  rw [h]
  fun_prop

lemma contDiff_inner_self_coord {n : ℕ} (j : Fin n) (m : ℕ) :
    ContDiff ℝ m (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) := by
  have h : (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) = fun z => Complex.normSq (z j) := by
    funext z; exact inner_self_eq_normSq (z j)
  rw [h]
  exact (contDiff_normSq_profile m).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).contDiff

/-- Convexity of a polydisc. -/
lemma convex_polydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    Convex ℝ (Work.CR.Flat.polydisc c r) := by
  have h : Work.CR.Flat.polydisc c r = Set.univ.pi (fun j => Metric.ball (c j) (r j)) := by
    ext z; simp [Work.CR.Flat.polydisc, Metric.mem_ball, dist_eq_norm]
  rw [h]
  exact convex_pi fun j _ => convex_ball _ _

/-- The Fréchet derivative of `z ↦ inner ℝ (z j) (z j)` is
`2 • (innerSL ℝ (x j) ∘ proj j)`. -/
lemma fderiv_inner_self_coord_eq {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    fderiv ℝ (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) x
      = (2 : ℝ) • ((innerSL ℝ (x j)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)) := by
  have hc : HasFDerivAt (fun z : Fin n → ℂ => innerSL ℝ (z j))
      ((innerSL ℝ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)) x :=
    (ContinuousLinearMap.hasFDerivAt (innerSL ℝ)).comp x
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j))
  have hu : HasFDerivAt (fun z : Fin n → ℂ => z j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j) x :=
    ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)
  have h := hc.clm_apply hu
  have hfun : (fun z : Fin n → ℂ => inner ℝ (z j) (z j))
      = fun y : Fin n → ℂ => (innerSL ℝ (y j)) (y j) := by
    funext z; rw [innerSL_apply_apply]
  rw [hfun, h.fderiv]
  congr 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply]
  rw [innerSL_apply_apply, innerSL_apply_apply, real_inner_comm (x j) (v j)]
  ring

lemma norm_fderiv_inner_self_coord_le {n : ℕ} (j : Fin n) (x : Fin n → ℂ) :
    ‖fderiv ℝ (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) x‖ ≤ 2 * ‖x j‖ := by
  set L : (Fin n → ℂ) →L[ℝ] ℝ :=
    (innerSL ℝ (x j)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)
  have hL : ‖L‖ ≤ ‖x j‖ := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have hA : ‖(innerSL ℝ (x j) : ℂ →L[ℝ] ℝ)‖ ≤ ‖x j‖ := by
      refine le_trans (ContinuousLinearMap.le_opNorm (innerSL ℝ) (x j)) ?_
      calc ‖innerSL ℝ‖ * ‖x j‖ ≤ 1 * ‖x j‖ :=
            mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ) (norm_nonneg _)
        _ = ‖x j‖ := one_mul _
    have hB : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simpa using norm_le_pi_norm v j
    calc ‖(innerSL ℝ (x j) : ℂ →L[ℝ] ℝ)‖ *
          ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j‖
        ≤ ‖x j‖ * 1 := mul_le_mul hA hB (norm_nonneg _) (norm_nonneg _)
      _ = ‖x j‖ := mul_one _
  rw [fderiv_inner_self_coord_eq j x]
  change ‖(2 : ℝ) • L‖ ≤ 2 * ‖x j‖
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith

lemma norm_fderiv_inner_self_coord_sub_le {n : ℕ} (j : Fin n) (x y : Fin n → ℂ) :
    ‖fderiv ℝ (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) x
      - fderiv ℝ (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) y‖ ≤ 2 * ‖x j - y j‖ := by
  set Lx : (Fin n → ℂ) →L[ℝ] ℝ :=
    (innerSL ℝ (x j)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)
  set Ly : (Fin n → ℂ) →L[ℝ] ℝ :=
    (innerSL ℝ (y j)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)
  have hfac : fderiv ℝ (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) x
      - fderiv ℝ (fun z : Fin n → ℂ => inner ℝ (z j) (z j)) y = (2 : ℝ) • (Lx - Ly) := by
    rw [fderiv_inner_self_coord_eq j x, fderiv_inner_self_coord_eq j y,
      show (2:ℝ) • Lx - (2:ℝ) • Ly = (2:ℝ) • (Lx - Ly) from (smul_sub 2 Lx Ly).symm]
  have hsub : Lx - Ly = (innerSL ℝ (x j - y j)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j) := by
    rw [show Lx = (innerSL ℝ (x j)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j) from rfl,
      show Ly = (innerSL ℝ (y j)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j) from rfl,
      ← ContinuousLinearMap.sub_comp, map_sub]
  rw [hfac, hsub, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hL : ‖(innerSL ℝ (x j - y j)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)‖ ≤ ‖x j - y j‖ := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have hA : ‖(innerSL ℝ (x j - y j) : ℂ →L[ℝ] ℝ)‖ ≤ ‖x j - y j‖ := by
      refine le_trans (ContinuousLinearMap.le_opNorm (innerSL ℝ) (x j - y j)) ?_
      calc ‖innerSL ℝ‖ * ‖x j - y j‖ ≤ 1 * ‖x j - y j‖ :=
            mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ) (norm_nonneg _)
        _ = ‖x j - y j‖ := one_mul _
    have hB : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simpa using norm_le_pi_norm v j
    calc ‖(innerSL ℝ (x j - y j) : ℂ →L[ℝ] ℝ)‖ *
          ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j‖
        ≤ ‖x j - y j‖ * 1 := mul_le_mul hA hB (norm_nonneg _) (norm_nonneg _)
      _ = ‖x j - y j‖ := mul_one _
  linarith

/-- For a function `f : ℝ → ℝ` the Fréchet derivative is `deriv f t • 1`. -/
lemma fderiv_real_eq_smul_one (f : ℝ → ℝ) (t : ℝ) :
    fderiv ℝ f t = (deriv f t) • (1 : ℝ →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [fderiv_eq_smul_deriv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, smul_eq_mul]
  ring

/-- Complexification of a real-valued function: the derivative is the composition with
`Complex.ofRealCLM`. -/
lemma fderiv_ofReal_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun z => ((f z : ℝ) : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ f x) := by
  have h : HasFDerivAt (fun z => ((f z : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM (x := f x)).comp x hf.hasFDerivAt
  exact h.fderiv

lemma norm_ofRealCLM_le_one : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun r => ?_
  rw [one_mul, Complex.ofRealCLM_apply]
  exact le_of_eq (LinearIsometry.norm_map Complex.ofRealLI r)

/-- The `C^{1,α}` norm of a constant function. -/
lemma holderNorm_one_const_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) (α : ℝ) (c : ℂ) :
    Work.CR.Flat.holderNorm 1 α (fun _ : X => c) Ω ≤ ENNReal.ofReal ‖c‖ := by
  have h0 : Work.CR.Flat.iterDerivNorm 0 (fun _ : X => c) Ω ≤ ENNReal.ofReal ‖c‖ := by
    refine iSup₂_le fun x _ => ?_
    rw [norm_iteratedFDerivWithin_zero]
  have h0s : Work.CR.Flat.holderSeminorm 0 α (fun _ : X => c) Ω = 0 := by
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
    have hxy : iteratedFDerivWithin ℝ 0 (fun _ : X => c) Ω x
        = iteratedFDerivWithin ℝ 0 (fun _ : X => c) Ω y := rfl
    rw [hxy, sub_self, norm_zero, zero_div, ENNReal.ofReal_zero]
  have h1 : Work.CR.Flat.iterDerivNorm 1 (fun _ : X => c) Ω = 0 := by
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun x _ => ?_
    rw [iteratedFDerivWithin_const_of_ne (𝕜 := ℝ) (by norm_num : (1:ℕ) ≠ 0) c Ω]
    simp
  have h1s : Work.CR.Flat.holderSeminorm 1 α (fun _ : X => c) Ω = 0 := by
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
    rw [iteratedFDerivWithin_const_of_ne (𝕜 := ℝ) (by norm_num : (1:ℕ) ≠ 0) c Ω]
    simp
  rw [Work.CR.Flat.holderNorm]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  refine le_trans (add_le_add (add_le_add h0 (le_of_eq h0s))
    (add_le_add (le_of_eq h1) (le_of_eq h1s))) ?_
  simp

/-! ## More auxiliary lemmas for the assembly -/

lemma norm_ofRealCLM_comp_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) :
    ‖Complex.ofRealCLM.comp L‖ ≤ ‖L‖ := by
  calc ‖Complex.ofRealCLM.comp L‖
      ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right norm_ofRealCLM_le_one (norm_nonneg _)
    _ = ‖L‖ := one_mul _

/-- Chain rule for the composition of a real profile with a real-valued map. -/
lemma fderiv_comp_scalar {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ψ : ℝ → ℝ} {φ : X → ℝ} {x : X} (hΨ : DifferentiableAt ℝ Ψ (φ x))
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun z => Ψ (φ z)) x = (deriv Ψ (φ x)) • (fderiv ℝ φ x) := by
  have h := hΨ.hasFDerivAt.comp x hφ.hasFDerivAt
  have h' : fderiv ℝ (fun z => Ψ (φ z)) x = fderiv ℝ Ψ (φ x) ∘SL fderiv ℝ φ x := by
    simpa [Function.comp_def] using h.fderiv
  rw [h', fderiv_real_eq_smul_one]
  congr 1

lemma fderiv_comp_scalar_sub {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ψ : ℝ → ℝ} {φ : X → ℝ} {x y : X} (hΨx : DifferentiableAt ℝ Ψ (φ x))
    (hΨy : DifferentiableAt ℝ Ψ (φ y)) (hφx : DifferentiableAt ℝ φ x)
    (hφy : DifferentiableAt ℝ φ y) :
    fderiv ℝ (fun z => Ψ (φ z)) x - fderiv ℝ (fun z => Ψ (φ z)) y
      = (deriv Ψ (φ x)) • (fderiv ℝ φ x - fderiv ℝ φ y)
        + (deriv Ψ (φ x) - deriv Ψ (φ y)) • (fderiv ℝ φ y) := by
  rw [fderiv_comp_scalar hΨx hφx, fderiv_comp_scalar hΨy hφy, smul_sub, sub_smul]
  abel

/-- `(1 + 1/ε)^m ≤ 2^m (1 + (ε^m)⁻¹)` for `ε > 0`. -/
lemma one_add_inv_pow_le {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    (1 + 1 / ε) ^ m ≤ 2 ^ m * (1 + (ε ^ m)⁻¹) := by
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hinv : (0 : ℝ) ≤ (ε ^ m)⁻¹ := by positivity
  rcases lt_or_ge ε 1 with h | h
  · have h1 : 1 + 1 / ε ≤ 2 * (1 / ε) := by
      have hle : (1 : ℝ) ≤ 1 / ε := by
        rw [le_div_iff₀ hε, one_mul]; exact h.le
      linarith
    have h2 : (1 + 1 / ε) ^ m ≤ (2 * (1 / ε)) ^ m := pow_le_pow_left₀ (by positivity) h1 m
    have h3 : (2 * (1 / ε)) ^ m = 2 ^ m * (ε ^ m)⁻¹ := by
      rw [mul_pow, one_div, inv_pow]
    rw [h3] at h2
    nlinarith [h2, hinv, h2m]
  · have h1 : 1 + 1 / ε ≤ 2 := by
      have hle : 1 / ε ≤ (1 : ℝ) := by
        rw [div_le_one hε]; exact h
      linarith
    have h2 : (1 + 1 / ε) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) h1 m
    nlinarith [h2, hinv, h2m]

/-- Product bound for the `C^{1,α}` norm of a finite product. -/
lemma holderNorm_finset_prod_le_of_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) {α : ℝ} {ι : Type*} (u : Finset ι) (f : ι → X → ℂ)
    (N : ι → ℝ) (hN : ∀ i, 0 ≤ N i) (hf : ∀ i ∈ u, ContDiffOn ℝ 1 (f i) Ω)
    (hbd : ∀ i ∈ u, Work.CR.Flat.holderNorm 1 α (f i) Ω ≤ ENNReal.ofReal (N i)) :
    Work.CR.Flat.holderNorm 1 α (fun x => ∏ i ∈ u, f i x) Ω
      ≤ (ENNReal.ofReal 8) ^ u.card * ∏ i ∈ u, ENNReal.ofReal (N i) := by
  classical
  induction u using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty, pow_zero, mul_one]
    have h1 : (fun x => ∏ i ∈ (∅ : Finset ι), f i x) = fun _ : X => (1 : ℂ) := by
      funext x; simp
    rw [h1]
    refine le_trans (holderNorm_one_const_le Ω α 1) ?_
    simp
  | insert i u hi ih =>
    have hLHS : (fun x : X => ∏ j ∈ insert i u, f j x) = fun x => f i x * ∏ j ∈ u, f j x := by
      funext x; rw [Finset.prod_insert hi]
    have hfi : ContDiffOn ℝ 1 (f i) Ω := hf i (Finset.mem_insert_self i u)
    have hfu : ContDiffOn ℝ 1 (fun x => ∏ j ∈ u, f j x) Ω :=
      contDiffOn_prod fun j _ => hf j (Finset.mem_insert_of_mem ‹j ∈ u›)
    have hbdu := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hbd j (Finset.mem_insert_of_mem hj))
    have hRHSne : ((ENNReal.ofReal 8) ^ u.card * ∏ j ∈ u, ENNReal.ofReal (N j)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ?_
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hN j)]
      exact ENNReal.ofReal_ne_top
    have hfinu : Work.CR.Flat.holderNorm 1 α (fun x => ∏ j ∈ u, f j x) Ω ≠ ⊤ :=
      ne_top_of_le_ne_top hRHSne hbdu
    have hfii : Work.CR.Flat.holderNorm 1 α (f i) Ω ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbd i (Finset.mem_insert_self i u))
    have hmul := Work.CR.Flat.Holder.holderNorm_mul_le (k := 1) hfi hfu hΩ hfii hfinu
    have hconst : ((↑(1 : ℕ) : ℝ≥0∞) + 1) * 2 ^ (1 + 1) = ENNReal.ofReal 8 := by norm_num
    rw [hconst] at hmul
    rw [hLHS, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    calc Work.CR.Flat.holderNorm 1 α (fun x => f i x * ∏ j ∈ u, f j x) Ω
        ≤ ENNReal.ofReal 8 * Work.CR.Flat.holderNorm 1 α (f i) Ω
            * Work.CR.Flat.holderNorm 1 α (fun x => ∏ j ∈ u, f j x) Ω := hmul
      _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (N i)
            * ((ENNReal.ofReal 8) ^ u.card * ∏ j ∈ u, ENNReal.ofReal (N j)) := by
          gcongr
          exact hbd i (Finset.mem_insert_self i u)
      _ = (ENNReal.ofReal 8) ^ (u.card + 1)
            * (ENNReal.ofReal (N i) * ∏ j ∈ u, ENNReal.ofReal (N j)) := by
          rw [pow_succ]; ring


theorem exists_polydisc_cutoff {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Rmin Rmax : ℝ} (hRmin : 0 < Rmin) (hRmax : 0 < Rmax) :
    ∃ K : ℝ, 0 < K ∧ ∃ p : ℝ, 0 < p ∧
      ∀ (R : Fin n → ℝ) (ε : ℝ),
        (∀ j, Rmin ≤ R j) → (∀ j, R j ≤ Rmax) → 0 < ε →
        ∃ χ : (Fin n → ℂ) → ℝ,
          (∀ m : ℕ, ContDiff ℝ m χ) ∧
          (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
          (∀ z, (∀ j, ‖z j‖ ≤ R j) → χ z = 1) ∧
          (∀ z, (∃ j, R j + ε ≤ ‖z j‖) → χ z = 0) ∧
          Work.CR.Flat.holderNorm 1 α (fun z => (χ z : ℂ))
            (Work.CR.Flat.polydisc 0 (fun j => R j + ε))
            ≤ ENNReal.ofReal (K * (1 + Real.rpow ε (-p))) := by
  obtain ⟨Ψ, hΨcd, hΨrng, hΨone, hΨzero, CΨ, hCΨpos, hCΨb, hCΨlip⟩ :=
    exists_smooth_step_profile
  have hdiffΨ : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hΨdiff : ∀ t, DifferentiableAt ℝ Ψ t := fun t =>
    ((hΨcd 1).differentiable hdiffΨ).differentiableAt
  set C₀ : ℝ := (Rmax + 1) / Rmin + 1 with hC₀
  have hC₀pos : 0 < C₀ := by rw [hC₀]; positivity
  set K₀ : ℝ := 3 + 5 * CΨ * C₀ + CΨ * C₀ ^ 2 with hK₀
  have hK₀pos : 0 < K₀ := by rw [hK₀]; positivity
  have hp : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have h2n : 0 < 2 * n := Nat.mul_pos (by norm_num) hn
    exact_mod_cast h2n
  refine ⟨(8 : ℝ) ^ n * 2 ^ (3 * n) * K₀ ^ n, by positivity, ((2 * n : ℕ) : ℝ), hp, ?_⟩
  intro R ε hRlow hRhigh hε
  have hRpos : ∀ j, 0 < R j := fun j => lt_of_lt_of_le hRmin (hRlow j)
  set D : Fin n → ℝ := fun j => (R j + ε) ^ 2 - (R j) ^ 2 with hD
  have hDval : ∀ j, D j = ε * (2 * R j + ε) := by intro j; rw [hD]; ring
  have hDpos : ∀ j, 0 < D j := by
    intro j; rw [hDval j]; nlinarith [hRpos j, hε]
  have hDlb : ∀ j, 2 * Rmin * ε ≤ D j := by
    intro j; rw [hDval j]; nlinarith [hRlow j, hε]
  set q : Fin n → (Fin n → ℂ) → ℝ := fun j z => inner ℝ (z j) (z j) with hq
  have hqeq : ∀ j z, q j z = ‖z j‖ ^ 2 := fun j z => real_inner_self_eq_norm_sq (z j)
  have hqfun : ∀ j, (fun z : Fin n → ℂ => q j z) = fun z => inner ℝ (z j) (z j) := by
    intro j; funext z; rw [hq]
  have hqcd : ∀ (j : Fin n) (m : ℕ), ContDiff ℝ m (fun z : Fin n → ℂ => q j z) := by
    intro j m; rw [hqfun j]; exact contDiff_inner_self_coord j m
  have hqdiff : ∀ j, Differentiable ℝ (fun z : Fin n → ℂ => q j z) := fun j =>
    (hqcd j 1).differentiable hdiffΨ
  set φ : Fin n → (Fin n → ℂ) → ℝ := fun j z => (q j z - R j ^ 2) / D j with hφ
  set G : Fin n → (Fin n → ℂ) → ℝ := fun j z => Ψ (φ j z) with hG
  set Gc : Fin n → (Fin n → ℂ) → ℂ := fun j z => ((G j z : ℝ) : ℂ) with hGc
  set χ : (Fin n → ℂ) → ℝ := fun z => ∏ j, G j z with hχ
  set Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 (fun j => R j + ε) with hΩ
  have hΩopen : IsOpen Ω := by rw [hΩ]; exact Work.CR.Flat.isOpen_polydisc 0 _
  have hΩconv : Convex ℝ Ω := by rw [hΩ]; exact convex_polydisc 0 _
  have hΩud : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  have hmem : ∀ z, z ∈ Ω ↔ ∀ j, ‖z j‖ < R j + ε := by
    intro z; rw [hΩ, Work.CR.Flat.mem_polydisc]; simp
  have hφj : ∀ j, φ j = fun z : Fin n → ℂ => (q j z - R j ^ 2) / D j := by
    intro j; funext z; rw [hφ]
  have hφcd : ∀ (j : Fin n) (m : ℕ), ContDiff ℝ m (φ j) := by
    intro j m; rw [hφj j]
    exact ((hqcd j m).sub contDiff_const).div_const _
  have hφdiff : ∀ j, Differentiable ℝ (φ j) := fun j =>
    (hφcd j 1).differentiable hdiffΨ
  have hGj : ∀ j, G j = fun z => Ψ (φ j z) := by intro j; funext z; rw [hG]
  have hGcd : ∀ (j : Fin n) (m : ℕ), ContDiff ℝ m (G j) := by
    intro j m; rw [hGj j]; exact (hΨcd m).comp (hφcd j m)
  have hGccd : ∀ (j : Fin n) (m : ℕ), ContDiff ℝ m (Gc j) := by
    intro j m; rw [hGc]; exact Complex.ofRealCLM.contDiff.comp (hGcd j m)
  have hχcd : ∀ m : ℕ, ContDiff ℝ m χ := by
    intro m; rw [hχ]; exact contDiff_prod fun j _ => hGcd j m
  have hχrng : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := by
    intro z
    have h01 : ∀ j, 0 ≤ G j z ∧ G j z ≤ 1 := fun j => hΨrng (φ j z)
    constructor
    · rw [hχ]; exact Finset.prod_nonneg fun j _ => (h01 j).1
    · rw [hχ]
      change ∏ j, G j z ≤ 1
      induction (Finset.univ : Finset (Fin n)) using Finset.induction with
      | empty => simp
      | insert i s his ih =>
        rw [Finset.prod_insert his]
        have hg0 : 0 ≤ ∏ j ∈ s, G j z := Finset.prod_nonneg fun j _ => (h01 j).1
        nlinarith [(h01 i).1, (h01 i).2, hg0, ih]
  have hχone : ∀ z, (∀ j, ‖z j‖ ≤ R j) → χ z = 1 := by
    intro z hz; rw [hχ]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hGj j]
    refine hΨone _ ?_
    rw [hφj j]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (le_of_lt (hDpos j))
    rw [hqeq j z]; nlinarith [hz j, hRpos j, norm_nonneg (z j)]
  have hχzero : ∀ z, (∃ j, R j + ε ≤ ‖z j‖) → χ z = 0 := by
    intro z hz; obtain ⟨j, hj⟩ := hz; rw [hχ]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [hGj j]
    refine hΨzero _ ?_
    rw [hφj j, le_div_iff₀ (hDpos j), one_mul]
    have hDj : D j = (R j + ε) ^ 2 - (R j) ^ 2 := by rw [hD]
    rw [hDj, hqeq j z]
    nlinarith [hj, hRpos j, norm_nonneg (z j), hε]
  set E : ℝ := 1 + 1 / ε with hE
  have hEge1 : 1 ≤ E := by
    rw [hE]
    have h1e : (0 : ℝ) < 1 / ε := by positivity
    linarith
  have hEpos : 0 < E := lt_of_lt_of_le one_pos hEge1
  set A : ℝ := (Rmax + ε) / (Rmin * ε) + 1 with hA
  set B : ℝ := 1 / (Rmin * ε) + 1 with hB
  have hApos : 0 < A := by
    rw [hA]
    have h1e : (0 : ℝ) < (Rmax + ε) / (Rmin * ε) := by positivity
    linarith
  have hBpos : 0 < B := by
    rw [hB]
    have h1e : (0 : ℝ) < 1 / (Rmin * ε) := by positivity
    linarith
  have hden : (0 : ℝ) < 2 * Rmin * ε := by nlinarith [hRmin, hε]
  have hAle : ∀ j, 2 * (R j + ε) / D j ≤ A := by
    intro j
    have hnum : (0 : ℝ) ≤ 2 * (R j + ε) := by linarith [hRpos j, hε]
    have h1 : 2 * (R j + ε) / D j ≤ 2 * (R j + ε) / (2 * Rmin * ε) :=
      div_le_div₀ hnum le_rfl hden (hDlb j)
    have h2 : 2 * (R j + ε) / (2 * Rmin * ε) = (R j + ε) / (Rmin * ε) := by
      field_simp
    have h3 : (R j + ε) / (Rmin * ε) ≤ (Rmax + ε) / (Rmin * ε) := by
      gcongr; linarith [hRhigh j]
    rw [hA]; linarith
  have hBle : ∀ j, 2 / D j ≤ B := by
    intro j
    have h1 : 2 / D j ≤ 2 / (2 * Rmin * ε) :=
      div_le_div₀ (by norm_num) le_rfl hden (hDlb j)
    have h2 : 2 / (2 * Rmin * ε) = 1 / (Rmin * ε) := by field_simp
    rw [hB]; linarith
  have hA_E : A ≤ C₀ * E := by
    rw [hA, hC₀, hE]
    have h1 : (Rmax + ε) / (Rmin * ε) = Rmax / (Rmin * ε) + 1 / Rmin := by
      field_simp
    have h7 : ((Rmax + 1) / Rmin + 1) * (1 + 1 / ε)
        = (Rmax + 1) / Rmin + (Rmax + 1) / (Rmin * ε) + 1 + 1 / ε := by
      rw [add_mul, one_mul, mul_add, mul_one, div_mul_div_comm, mul_one]
      ring
    rw [h1, h7]
    have h4 : Rmax / (Rmin * ε) ≤ (Rmax + 1) / (Rmin * ε) := by gcongr; linarith
    have h5 : 1 / Rmin ≤ (Rmax + 1) / Rmin := by gcongr; linarith
    linarith
  have hB_E : B ≤ C₀ * E := by
    rw [hB, hC₀, hE]
    have h7 : ((Rmax + 1) / Rmin + 1) * (1 + 1 / ε)
        = (Rmax + 1) / Rmin + (Rmax + 1) / (Rmin * ε) + 1 + 1 / ε := by
      rw [add_mul, one_mul, mul_add, mul_one, div_mul_div_comm, mul_one]
      ring
    rw [h7]
    have h4 : 1 / (Rmin * ε) ≤ (Rmax + 1) / (Rmin * ε) := by gcongr; linarith
    have h5 : (0 : ℝ) ≤ (Rmax + 1) / Rmin := by positivity
    linarith
  have hEtriv : E ≤ 1 + E ^ 2 := by nlinarith [hEge1, sq_nonneg (E - 1)]
  have hA2 : A ^ 2 ≤ (C₀ * E) ^ 2 := pow_le_pow_left₀ hApos.le hA_E 2
  have hN_K₀ : 3 + 4 * CΨ * A + CΨ * (B + A ^ 2) ≤ K₀ * (1 + E ^ 2) := by
    rw [hK₀]
    have hE2 : E ^ 2 ≤ 1 + E ^ 2 := by linarith
    have h4 : 4 * CΨ * A ≤ 4 * CΨ * C₀ * (1 + E ^ 2) := by
      calc 4 * CΨ * A ≤ 4 * CΨ * (C₀ * E) :=
            mul_le_mul_of_nonneg_left hA_E (by positivity)
        _ = (4 * CΨ * C₀) * E := by ring
        _ ≤ (4 * CΨ * C₀) * (1 + E ^ 2) :=
            mul_le_mul_of_nonneg_left hEtriv (by positivity)
        _ = 4 * CΨ * C₀ * (1 + E ^ 2) := by ring
    have h5 : CΨ * B ≤ CΨ * C₀ * (1 + E ^ 2) := by
      calc CΨ * B ≤ CΨ * (C₀ * E) := mul_le_mul_of_nonneg_left hB_E hCΨpos.le
        _ = (CΨ * C₀) * E := by ring
        _ ≤ (CΨ * C₀) * (1 + E ^ 2) :=
            mul_le_mul_of_nonneg_left hEtriv (by positivity)
        _ = CΨ * C₀ * (1 + E ^ 2) := by ring
    have h6 : CΨ * A ^ 2 ≤ CΨ * C₀ ^ 2 * (1 + E ^ 2) := by
      calc CΨ * A ^ 2 ≤ CΨ * (C₀ * E) ^ 2 := mul_le_mul_of_nonneg_left hA2 hCΨpos.le
        _ = (CΨ * C₀ ^ 2) * E ^ 2 := by ring
        _ ≤ (CΨ * C₀ ^ 2) * (1 + E ^ 2) :=
            mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = CΨ * C₀ ^ 2 * (1 + E ^ 2) := by ring
    have h7 : 3 ≤ 3 * (1 + E ^ 2) := by nlinarith [sq_nonneg E]
    calc 3 + 4 * CΨ * A + CΨ * (B + A ^ 2)
        = 3 + 4 * CΨ * A + CΨ * B + CΨ * A ^ 2 := by ring
      _ ≤ 3 * (1 + E ^ 2) + 4 * CΨ * C₀ * (1 + E ^ 2) + CΨ * C₀ * (1 + E ^ 2)
            + CΨ * C₀ ^ 2 * (1 + E ^ 2) := by
          linarith [h7, h4, h5, h6]
      _ = (3 + 5 * CΨ * C₀ + CΨ * C₀ ^ 2) * (1 + E ^ 2) := by ring
  have hφd : ∀ j x, fderiv ℝ (φ j) x
      = (D j)⁻¹ • (fderiv ℝ (fun z : Fin n → ℂ => q j z) x) := by
    intro j x
    rw [hφj j]
    have hfun : (fun z : Fin n → ℂ => (q j z - R j ^ 2) / D j)
        = fun z => (D j)⁻¹ * (q j z - R j ^ 2) := by
      funext z; rw [div_eq_inv_mul]
    rw [hfun]
    have hdiff : DifferentiableAt ℝ (fun z : Fin n → ℂ => q j z - R j ^ 2) x :=
      (hqdiff j).differentiableAt.sub_const _
    rw [fderiv_const_mul hdiff (D j)⁻¹, fderiv_sub_const]
  have hL1 : ∀ j, ∀ x ∈ Ω, ‖fderiv ℝ (φ j) x‖ ≤ 2 * (R j + ε) / D j := by
    intro j x hx
    rw [hφd j x, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hDpos j))]
    have hq1 : ‖fderiv ℝ (fun z : Fin n → ℂ => q j z) x‖ ≤ 2 * ‖x j‖ := by
      rw [hqfun j]; exact norm_fderiv_inner_self_coord_le j x
    have hxj : ‖x j‖ < R j + ε := (hmem x).mp hx j
    have hDinv : (0 : ℝ) < (D j)⁻¹ := inv_pos.mpr (hDpos j)
    refine le_trans (mul_le_mul_of_nonneg_left hq1 hDinv.le) ?_
    rw [inv_mul_eq_div]
    exact div_le_div₀ (by linarith [hRpos j, hε]) (by linarith) (hDpos j) le_rfl
  have hL2 : ∀ j, ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖fderiv ℝ (φ j) x - fderiv ℝ (φ j) y‖ ≤ (2 / D j) * ‖x - y‖ := by
    intro j x hx y hy
    rw [hφd j x, hφd j y]
    have hfac2 : (D j)⁻¹ • (fderiv ℝ (fun z : Fin n → ℂ => q j z) x)
        - (D j)⁻¹ • (fderiv ℝ (fun z : Fin n → ℂ => q j z) y)
        = (D j)⁻¹ • ((fderiv ℝ (fun z : Fin n → ℂ => q j z) x)
          - (fderiv ℝ (fun z : Fin n → ℂ => q j z) y)) := (smul_sub _ _ _).symm
    rw [hfac2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hDpos j))]
    have hq2 : ‖fderiv ℝ (fun z : Fin n → ℂ => q j z) x
        - fderiv ℝ (fun z : Fin n → ℂ => q j z) y‖ ≤ 2 * ‖x j - y j‖ := by
      rw [hqfun j]; exact norm_fderiv_inner_self_coord_sub_le j x y
    have hxy : ‖x j - y j‖ ≤ ‖x - y‖ := by
      simpa using norm_le_pi_norm (x - y) j
    have hDinv : (0 : ℝ) < (D j)⁻¹ := inv_pos.mpr (hDpos j)
    have h1 : (D j)⁻¹ * ‖fderiv ℝ (fun z : Fin n → ℂ => q j z) x
        - fderiv ℝ (fun z : Fin n → ℂ => q j z) y‖ ≤ (D j)⁻¹ * (2 * ‖x - y‖) := by
      refine le_trans (mul_le_mul_of_nonneg_left hq2 hDinv.le) ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hDinv.le
    refine le_trans h1 ?_
    have he : (D j)⁻¹ * (2 * ‖x - y‖) = (2 / D j) * ‖x - y‖ := by
      field_simp
    rw [he]
  have hφlip : ∀ j, ∀ x ∈ Ω, ∀ y ∈ Ω,
      |φ j x - φ j y| ≤ (2 * (R j + ε) / D j) * ‖x - y‖ := by
    intro j x hx y hy
    have h1 : φ j x - φ j y = (q j x - q j y) / D j := by rw [hφj j]; ring
    have h2 : |q j x - q j y| ≤ 2 * (R j + ε) * ‖x - y‖ := by
      have hq2 : q j x - q j y = (‖x j‖ - ‖y j‖) * (‖x j‖ + ‖y j‖) := by
        rw [hqeq j x, hqeq j y]; ring
      rw [hq2, abs_mul]
      have hb1 : |‖x j‖ - ‖y j‖| ≤ ‖x - y‖ :=
        le_trans (abs_norm_sub_norm_le _ _) (by simpa using norm_le_pi_norm (x - y) j)
      have hb2 : |‖x j‖ + ‖y j‖| ≤ 2 * (R j + ε) := by
        rw [abs_of_nonneg (by positivity)]
        have hx1 : ‖x j‖ < R j + ε := (hmem x).mp hx j
        have hy1 : ‖y j‖ < R j + ε := (hmem y).mp hy j
        linarith
      calc |‖x j‖ - ‖y j‖| * |‖x j‖ + ‖y j‖| ≤ ‖x - y‖ * (2 * (R j + ε)) :=
            mul_le_mul hb1 hb2 (abs_nonneg _) (norm_nonneg _)
        _ = 2 * (R j + ε) * ‖x - y‖ := by ring
    rw [h1, abs_div, abs_of_pos (hDpos j), div_le_iff₀ (hDpos j)]
    have h3 : (2 * (R j + ε) / D j * ‖x - y‖) * D j = 2 * (R j + ε) * ‖x - y‖ := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt (hDpos j))]
    rw [h3]
    exact h2
  have hGderiv : ∀ j x, fderiv ℝ (G j) x
      = (deriv Ψ (φ j x)) • (fderiv ℝ (φ j) x) := by
    intro j x
    rw [hGj j]
    exact fderiv_comp_scalar (hΨdiff (φ j x)) ((hφdiff j).differentiableAt)
  have hGderiv2 : ∀ j x y, fderiv ℝ (G j) x - fderiv ℝ (G j) y
      = (deriv Ψ (φ j x)) • (fderiv ℝ (φ j) x - fderiv ℝ (φ j) y)
        + (deriv Ψ (φ j x) - deriv Ψ (φ j y)) • (fderiv ℝ (φ j) y) := by
    intro j x y
    rw [hGj j]
    exact fderiv_comp_scalar_sub (hΨdiff (φ j x)) (hΨdiff (φ j y))
      (hφdiff j).differentiableAt (hφdiff j).differentiableAt
  have hfac : ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (Gc j) Ω
        ≤ ENNReal.ofReal (3 + 4 * CΨ * A + CΨ * (B + A ^ 2)) := by
    intro j
    have hGcfd : ∀ x, fderiv ℝ (Gc j) x = Complex.ofRealCLM.comp (fderiv ℝ (G j) x) := by
      intro x
      rw [hGc]
      exact fderiv_ofReal_comp (((hGcd j 1).differentiable hdiffΨ).differentiableAt)
    refine le_trans (holderNorm_one_le_of_deriv_bounds (M₀ := 1) (M₁ := CΨ * A)
      (M₂ := CΨ * (B + A ^ 2)) hΩopen hΩconv hα0 hα1
      (hGccd j 1) (by norm_num) (mul_nonneg hCΨpos.le hApos.le)
      (mul_nonneg hCΨpos.le (add_nonneg hBpos.le (sq_nonneg A)))
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy => ?_))
      (le_of_eq (by congr 1; ring))
    · rw [hGc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΨrng (φ j x)).1]
      exact (hΨrng (φ j x)).2
    · rw [hGcfd x]
      refine le_trans (norm_ofRealCLM_comp_le _) ?_
      rw [hGderiv j x, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hCΨb (φ j x)) (le_trans (hL1 j x hx) (hAle j))
        (norm_nonneg _) hCΨpos.le
    · rw [hGcfd x, hGcfd y, ← ContinuousLinearMap.comp_sub]
      refine le_trans (norm_ofRealCLM_comp_le _) ?_
      rw [hGderiv2 j x y]
      have ht1 : ‖(deriv Ψ (φ j x)) • (fderiv ℝ (φ j) x - fderiv ℝ (φ j) y)‖
          ≤ CΨ * ((2 / D j) * ‖x - y‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hCΨb (φ j x)) (hL2 j x hx y hy) (norm_nonneg _) hCΨpos.le
      have ht2 : ‖(deriv Ψ (φ j x) - deriv Ψ (φ j y)) • (fderiv ℝ (φ j) y)‖
          ≤ (CΨ * ((2 * (R j + ε) / D j) * ‖x - y‖)) * A := by
        rw [norm_smul, Real.norm_eq_abs]
        have h1 : |deriv Ψ (φ j x) - deriv Ψ (φ j y)|
            ≤ CΨ * ((2 * (R j + ε) / D j) * ‖x - y‖) :=
          le_trans (hCΨlip _ _) (mul_le_mul_of_nonneg_left (hφlip j x hx y hy) hCΨpos.le)
        have h2 : ‖fderiv ℝ (φ j) y‖ ≤ A := le_trans (hL1 j y hy) (hAle j)
        exact mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg hCΨpos.le (mul_nonneg
            (div_nonneg (by linarith [hRpos j, hε]) (hDpos j).le) (norm_nonneg _)))
      have hxy0 : 0 ≤ ‖x - y‖ := norm_nonneg _
      have h3 : CΨ * ((2 / D j) * ‖x - y‖) ≤ CΨ * (B * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hBle j) hxy0) hCΨpos.le
      have h4 : (CΨ * ((2 * (R j + ε) / D j) * ‖x - y‖)) * A ≤ (CΨ * (A * ‖x - y‖)) * A := by
        have hstep : (2 * (R j + ε) / D j) * ‖x - y‖ ≤ A * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (hAle j) hxy0
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hCΨpos.le) hApos.le
      calc ‖(deriv Ψ (φ j x)) • (fderiv ℝ (φ j) x - fderiv ℝ (φ j) y)
            + (deriv Ψ (φ j x) - deriv Ψ (φ j y)) • (fderiv ℝ (φ j) y)‖
          ≤ ‖(deriv Ψ (φ j x)) • (fderiv ℝ (φ j) x - fderiv ℝ (φ j) y)‖
            + ‖(deriv Ψ (φ j x) - deriv Ψ (φ j y)) • (fderiv ℝ (φ j) y)‖ := norm_add_le _ _
        _ ≤ CΨ * ((2 / D j) * ‖x - y‖) + (CΨ * ((2 * (R j + ε) / D j) * ‖x - y‖)) * A :=
              add_le_add ht1 ht2
        _ ≤ CΨ * (B * ‖x - y‖) + (CΨ * (A * ‖x - y‖)) * A := add_le_add h3 h4
        _ = (CΨ * (B + A ^ 2)) * ‖x - y‖ := by ring
  -- product bound and assembly
  have hprod := holderNorm_finset_prod_le_of_bound (Ω := Ω) hΩud (u := Finset.univ)
    (f := Gc) (N := fun _ : Fin n => 3 + 4 * CΨ * A + CΨ * (B + A ^ 2))
    (fun _ => by positivity) (fun j _ => (hGccd j 1).contDiffOn) (fun j _ => hfac j)
  have hsum : (fun z => (χ z : ℂ)) = fun z => ∏ j, Gc j z := by
    funext z
    show ((∏ j, G j z : ℝ) : ℂ) = ∏ j, ((G j z : ℝ) : ℂ)
    exact map_prod Complex.ofRealHom (fun j => G j z) Finset.univ
  have hE2n : (1 + E ^ 2) ^ n ≤ 2 ^ n * E ^ (2 * n) := by
    have h1 : 1 + E ^ 2 ≤ 2 * E ^ 2 := by nlinarith [hEge1]
    calc (1 + E ^ 2) ^ n ≤ (2 * E ^ 2) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = 2 ^ n * E ^ (2 * n) := by rw [mul_pow, ← pow_mul]
  have hEpow : E ^ (2 * n) ≤ 2 ^ (2 * n) * (1 + (ε ^ (2 * n))⁻¹) := by
    have h := one_add_inv_pow_le hε (2 * n)
    rw [hE]
    exact h
  have hrpow : Real.rpow ε (-(((2 * n : ℕ) : ℝ))) = (ε ^ (2 * n))⁻¹ := by
    have h1 : Real.rpow ε (-(((2 * n : ℕ) : ℝ)))
        = (Real.rpow ε (((2 * n : ℕ) : ℝ)))⁻¹ := Real.rpow_neg hε.le (((2 * n : ℕ) : ℝ))
    rw [h1]
    exact congrArg Inv.inv (Real.rpow_natCast ε (2 * n))
  have hNpow : (3 + 4 * CΨ * A + CΨ * (B + A ^ 2)) ^ n
      ≤ K₀ ^ n * 2 ^ (3 * n) * (1 + (ε ^ (2 * n))⁻¹) := by
    have h1 : (3 + 4 * CΨ * A + CΨ * (B + A ^ 2)) ^ n ≤ (K₀ * (1 + E ^ 2)) ^ n :=
      pow_le_pow_left₀ (by positivity) hN_K₀ n
    rw [mul_pow] at h1
    have h2 : K₀ ^ n * (1 + E ^ 2) ^ n ≤ K₀ ^ n * (2 ^ n * E ^ (2 * n)) :=
      mul_le_mul_of_nonneg_left hE2n (by positivity)
    have h3 : K₀ ^ n * (2 ^ n * E ^ (2 * n))
        ≤ K₀ ^ n * (2 ^ n * (2 ^ (2 * n) * (1 + (ε ^ (2 * n))⁻¹))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEpow (by positivity)) (by positivity)
    have h4 : K₀ ^ n * (2 ^ n * (2 ^ (2 * n) * (1 + (ε ^ (2 * n))⁻¹)))
        = K₀ ^ n * 2 ^ (3 * n) * (1 + (ε ^ (2 * n))⁻¹) := by
      have h5 : 2 ^ n * (2 ^ (2 * n) * (1 + (ε ^ (2 * n))⁻¹))
          = 2 ^ (3 * n) * (1 + (ε ^ (2 * n))⁻¹) := by
        have hexp : n + 2 * n = 3 * n := by ring
        rw [← mul_assoc, ← pow_add, hexp]
      rw [h5]; ring
    linarith [h1, h2, h3, h4]
  refine ⟨χ, hχcd, hχrng, hχone, hχzero, ?_⟩
  have hmain : Work.CR.Flat.holderNorm 1 α (fun z => (χ z : ℂ)) Ω
      ≤ ENNReal.ofReal ((8 : ℝ) ^ n * (3 + 4 * CΨ * A + CΨ * (B + A ^ 2)) ^ n) := by
    rw [← hsum] at hprod
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    refine le_trans hprod ?_
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 8),
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3 + 4 * CΨ * A + CΨ * (B + A ^ 2)),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (8:ℝ) ^ n)]
  refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
  rw [hrpow]
  calc (8 : ℝ) ^ n * (3 + 4 * CΨ * A + CΨ * (B + A ^ 2)) ^ n
      ≤ (8 : ℝ) ^ n * (K₀ ^ n * 2 ^ (3 * n) * (1 + (ε ^ (2 * n))⁻¹)) :=
        mul_le_mul_of_nonneg_left hNpow (by positivity)
    _ = ((8 : ℝ) ^ n * 2 ^ (3 * n) * K₀ ^ n) * (1 + (ε ^ (2 * n))⁻¹) := by ring

end Work.NN.Core.Lev
