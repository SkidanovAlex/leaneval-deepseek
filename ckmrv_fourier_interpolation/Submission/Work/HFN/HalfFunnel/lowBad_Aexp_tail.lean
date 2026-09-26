/-
# The tail `K - 𝒢` on the bad-line region is `O((1+t)^M e^{-πt})`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the `E₈` and
Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022)) expand the kernel
`z ↦ K^{(d)}(τ,z)` at the cusp `z = i∞`: for `t` above all poles of `z ↦ K^{(d)}(τ,z)` one has

  `K^{(d)}(τ,it) = 𝒢(τ,it) + O((1+t)^M e^{-πt})`,

with `𝒢` the non-decaying part.  In the workspace this is the cusp expansion
`Work.Asymptotics.Aexp (Gcusp ℓ d) τ t`, and the estimate is available on every *compact* set of
parameters (`Work.Asymptotics.kernel_axis_bound`, via `Work.Asymptotics.CuspExp`).

The region `lowBadSet = {τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2, |Re τ| > 3/4}` of the bad-line part of the
low strip is **not** compact in `𝒟` (it accumulates at `Re τ = ±1`), so `kernel_axis_bound`
does not apply to it directly.  This file bridges the gap:

* the closure `badStrip = {1/2 ≤ Im τ ≤ 2, |Re τ| ≤ 1}` of `lowBadSet` *is* compact, and
  `kernel_axis_bound` gives the estimate `C₀ (1+t)^M₀ e^{-πt}` for `t ≥ T` and `τ ∈ badStrip`;
* for the remaining window `3 ≤ t ≤ max T 3` the difference `K - 𝒢` is continuous on the
  compact set `badStrip × [3, max T 3]`, hence bounded — for `t ≥ 3` the contour point `z = it`
  lies above *every* point of the `SL(2,ℤ)`-orbit of `τ` (`Im γτ ≤ 2` for `τ ∈ badStrip`), so
  the coincidence divisor `j τ = j (it)` is avoided and `Work.Asymptotics.continuousOn_Kfun_clean`
  applies; and `𝒢` is continuous because all its coefficient functions are (`Gcusp` is an
  explicit polynomial combination of the atoms `φ_k, E₂, E₄, E₆, Δ, ψ₂, ψ₄`, all continuous).
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.cuspExpansionKernel
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Kernels.KernelGrowth.PhiVec_InP
import Submission.Work.Asymptotics.GcuspInP

noncomputable section

set_option maxHeartbeats 1000000

open UpperHalfPlane
open scoped Topology

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-! ## The point `i t`, as a continuous function of `t` -/

/-- The point `i · max t 1` of `ℍ`; for `t ≥ 1` it is `Kernels.imagAxis t _`, and it is a
continuous function of `t` (whereas `Kernels.imagAxis` carries a proof of `0 < t`). -/
def iAxisFun (t : ℝ) : ℍ :=
  ⟨((max t 1 : ℝ) : ℂ) * Complex.I, by simp [Complex.mul_im]⟩

lemma iAxisFun_coe (t : ℝ) : ((iAxisFun t : ℍ) : ℂ) = ((max t 1 : ℝ) : ℂ) * Complex.I := rfl

lemma iAxisFun_im (t : ℝ) : (iAxisFun t).im = max t 1 := by
  rw [← UpperHalfPlane.coe_im, iAxisFun_coe, Complex.mul_im]; simp

lemma continuous_iAxisFun : Continuous iAxisFun := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous (fun t : ℝ => UpperHalfPlane.coe (iAxisFun t))
  simp only [iAxisFun_coe]
  fun_prop

lemma iAxisFun_eq_imagAxis {t : ℝ} (ht : 1 ≤ t) :
    iAxisFun t = Work.Kernels.imagAxis t (lt_of_lt_of_le one_pos ht) := by
  apply UpperHalfPlane.ext
  rw [iAxisFun_coe, show ((max t 1 : ℝ) : ℂ) = (t : ℂ) from by rw [max_eq_left ht]]
  rfl

/-! ## The compact strip containing the bad-line region -/

/-- The closure of the bad-line region inside the low strip: the compact Euclidean rectangle
`{1/2 ≤ Im τ ≤ 2, |Re τ| ≤ 1}`. -/
def badStrip : Set ℍ := {τ | (1 / 2 : ℝ) ≤ τ.im ∧ τ.im ≤ 2 ∧ |τ.re| ≤ 1}

lemma mem_badStrip {τ : ℍ} (hτ : lowBadSet τ) : τ ∈ badStrip := by
  obtain ⟨hD, h1, h2, -⟩ := hτ
  exact ⟨h1, h2, abs_le.mpr ⟨by linarith [hD.1], by linarith [hD.2.1]⟩⟩

lemma isClosed_badStrip : IsClosed badStrip := by
  have h1 : IsClosed {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h2 : IsClosed {τ : ℍ | τ.im ≤ 2} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have h3 : IsClosed {τ : ℍ | |τ.re| ≤ 1} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h : badStrip = {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ 2} ∩
      {τ : ℍ | |τ.re| ≤ 1} := by
    ext τ; simp [badStrip, and_assoc]
  rw [h]
  exact (h1.inter h2).inter h3

lemma badStrip_bounded : Bornology.IsBounded badStrip := by
  rw [Metric.isBounded_iff_subset_closedBall UpperHalfPlane.I]
  refine ⟨10, fun τ hτ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hτ
  rw [Metric.mem_closedBall]
  have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
    have hre : ((τ : ℂ) - Complex.I).re = τ.re := by simp
    have him : ((τ : ℂ) - Complex.I).im = τ.im - 1 := by simp
    rw [hre, him] at h
    have h4 : |τ.im - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (τ.im * UpperHalfPlane.I.im) := by
    have hI : UpperHalfPlane.I.im = 1 := by
      rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_I]; simp
    rw [hI, mul_one, Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [h1]
  have hstep : dist τ UpperHalfPlane.I ≤
      ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * UpperHalfPlane.I.im) := by
    simpa [UpperHalfPlane.coe_I, Complex.dist_eq] using
      UpperHalfPlane.dist_le_dist_coe_div_sqrt τ UpperHalfPlane.I
  calc dist τ UpperHalfPlane.I
      ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * UpperHalfPlane.I.im) := hstep
    _ ≤ 5 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
    _ = 10 := by norm_num

lemma isCompact_badStrip : IsCompact badStrip := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_badStrip, badStrip_bounded⟩

/-! ## No coincidence on the contour above height `3` -/

/-- **For `τ` in the compact strip and `t ≥ 3` the point `i t` avoids the orbit of `τ`.**

If `j τ = j (i t)` then `i t = γ • τ` for some `γ ∈ SL(2,ℤ)`, and comparing imaginary parts
gives `τ.im = t / (c²t² + d²)` with `c = γ_{10}`, `d = γ_{11}` integers (`γ_{ij}` the entries
of `γ`).  If `c ≠ 0` this is at most `1/t ≤ 1/3`, and if `c = 0` then `d = ±1` forces `τ.im = t`;
both contradict `1/2 ≤ τ.im ≤ 2` and `t ≥ 3`. -/
lemma jInvariantFun_ne_iAxisFun_of_mem_badStrip {τ : ℍ} (hτ : τ ∈ badStrip) {t : ℝ}
    (ht : 3 ≤ t) : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (iAxisFun t) := by
  intro h
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have him : τ.im = (γ • (iAxisFun t)).im := by rw [hγ]
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply] at him
  rw [iAxisFun_im, max_eq_left ht1, iAxisFun_coe] at him
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ) with hcdef
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hddef
  have hns : Complex.normSq (((γ 1 0 : ℤ) : ℂ) * ((↑((max t 1 : ℝ)) : ℂ) * Complex.I)
      + ((γ 1 1 : ℤ) : ℂ)) = (c * t) ^ 2 + d ^ 2 := by
    rw [hcdef, hddef]
    rw [show ((γ 1 0 : ℤ) : ℂ) = ((c : ℝ) : ℂ) from by rw [hcdef]; norm_num,
      show ((γ 1 1 : ℤ) : ℂ) = ((d : ℝ) : ℂ) from by rw [hddef]; norm_num]
    rw [max_eq_left ht1, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero,
      sub_zero]
    ring
  rw [hns] at him
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- `c = 0`: the orbit point is a translate of `τ`, so `τ.im = t`
    have h10 : γ 1 0 = 0 := by
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := by rw [← hcdef]; exact hc0
      exact_mod_cast this
    have hdet : γ 0 0 * γ 1 1 = 1 := by
      have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h' := γ.2; rwa [Matrix.det_fin_two] at h'
      rw [h10, mul_zero, sub_zero] at hd; exact hd
    have hd1 : d ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h11⟩ | ⟨-, h11⟩
      · rw [hddef, h11]; norm_num
      · rw [hddef, h11]; norm_num
    rw [hc0, hd1] at him
    norm_num at him
    linarith [hτ.2.1]
  · -- `c ≠ 0`: `τ.im ≤ 1/t ≤ 1/3`
    have hk : γ 1 0 ≠ 0 := by
      intro h0; exact hc0 (by rw [hcdef, h0]; norm_num)
    have hc1 : (1 : ℝ) ≤ c ^ 2 := by
      have h1 : (1 : ℤ) ≤ |γ 1 0| := Int.one_le_abs hk
      have h2 : (1 : ℝ) ≤ |c| := by
        rw [hcdef, ← Int.cast_abs]
        exact_mod_cast h1
      nlinarith [h2, sq_abs c]
    have htpos : 0 < t := by linarith
    have hle : τ.im ≤ 1 / t := by
      rw [him]
      have hge : t ^ 2 ≤ (c * t) ^ 2 + d ^ 2 := by nlinarith [hc1, sq_nonneg d, htpos]
      have h1 : t / ((c * t) ^ 2 + d ^ 2) ≤ t / t ^ 2 :=
        div_le_div_of_nonneg_left (le_of_lt htpos) (by positivity) hge
      have h2 : t / t ^ 2 = 1 / t := by field_simp
      linarith [h1, h2.le, h2.ge]
    have ht2 : ((1 : ℝ) / 2) ≤ 1 / t := le_trans hτ.1 hle
    have htle : t ≤ 2 := by
      have h2 : (2 : ℝ)⁻¹ ≤ t⁻¹ := by simpa using ht2
      have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) htpos).mp h2
      simpa using h
    linarith

/-! ## Continuity of the coefficient functions `Gcusp ℓ d i j` -/

private lemma continuous_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := by
  have hxi2 : Continuous (fun τ : ℍ => Work.Kernels.xi2Fun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.xi2Fun τ) =
        fun τ => Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
    rw [h]
    exact ((Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4).add
      ((Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4)
  have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have h : (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi2Fun τ * ℓ.L τ +
        (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ +
      (SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (hxi2.mul ℓ.holo.continuous).add (((hU.add hV).neg).mul ℓ.holo_S.continuous)

private lemma continuous_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := by
  have hxi4 : Continuous (fun τ : ℍ => Work.Kernels.xi4Fun τ) := by
    have h : (fun τ : ℍ => Work.Kernels.xi4Fun τ) = fun τ =>
        Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2 := rfl
    rw [h]
    have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
      (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
    have hW : Continuous (fun τ : ℍ => Work.Kernels.WFun τ) :=
      (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
    have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
      (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
    exact ((hU.pow 2).add (hW.pow 2)).sub ((hV.pow 2).const_mul 2)
  have hU : Continuous (fun τ : ℍ => Work.Kernels.UFun τ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (fun τ : ℍ => Work.Kernels.VFun τ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have hW : Continuous (fun τ : ℍ => Work.Kernels.WFun τ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
  have h : (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = fun τ =>
      Work.Kernels.xi4Fun τ * ℓ.L τ +
        (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
          * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ +
      (SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun) τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (hxi4.mul ℓ.holo.continuous).add
    (((hU.pow 2).add (hV.pow 2)).sub ((hW.pow 2).const_mul 2) |>.mul ℓ.holo_S.continuous)

private lemma continuous_Gcusp8 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Continuous (fun τ : ℍ => Gcusp8 ℓ i j τ) := by
  have hphi : ∀ k : Fin 3, Continuous (fun τ : ℍ => Work.Kernels.phiVec τ k) :=
    fun k => (Work.Kernels.KernelGrowth.PhiVec_InP k).1.continuous
  have hE4 : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hE6 : Continuous (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
    (ModularForm.holo' ModularForm.E₆).continuous
  have hpsi4 : Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := continuous_psi4 ℓ
  unfold Gcusp8
  split_ifs <;> fun_prop

private lemma continuous_Gcusp24 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Continuous (fun τ : ℍ => Gcusp24 ℓ i j τ) := by
  have hphi : ∀ k : Fin 3, Continuous (fun τ : ℍ => Work.Kernels.phiVec τ k) :=
    fun k => (Work.Kernels.KernelGrowth.PhiVec_InP k).1.continuous
  have hE4 : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hE6 : Continuous (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
    (ModularForm.holo' ModularForm.E₆).continuous
  have hDel : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  have hpsi2 : Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := continuous_psi2 ℓ
  have hpsi4 : Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := continuous_psi4 ℓ
  unfold Gcusp24
  split_ifs <;> fun_prop

private lemma continuous_Gcusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (_hd : d = 8 ∨ d = 24)
    (i j : Fin 2) : Continuous (fun τ : ℍ => Gcusp ℓ d i j τ) := by
  have h8 : Continuous (fun τ : ℍ => Gcusp8 ℓ i j τ) := continuous_Gcusp8 ℓ i j
  have h24 : Continuous (fun τ : ℍ => Gcusp24 ℓ i j τ) := continuous_Gcusp24 ℓ i j
  unfold Gcusp
  split_ifs with h
  · exact h8
  · exact h24

/-! ## Continuity of the tail integrand on the compact strip -/

private lemma continuousOn_Kaxis_badStrip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (T : ℝ) :
    ContinuousOn (fun p : ℍ × ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2)
      (badStrip ×ˢ Set.Icc (3 : ℝ) (max T 3)) := by
  have hΦ : ContinuousOn (fun p : ℍ × ℝ => (p.1, iAxisFun p.2))
      (badStrip ×ˢ Set.Icc (3 : ℝ) (max T 3)) :=
    (continuous_fst.prodMk (continuous_iAxisFun.comp continuous_snd)).continuousOn
  have hmaps : Set.MapsTo (fun p : ℍ × ℝ => (p.1, iAxisFun p.2))
      (badStrip ×ˢ Set.Icc (3 : ℝ) (max T 3))
      {q : ℍ × ℍ | Work.Kernels.jInvariantFun q.1 ≠ Work.Kernels.jInvariantFun q.2} := by
    intro p hp
    exact jInvariantFun_ne_iAxisFun_of_mem_badStrip hp.1 (le_trans (by norm_num) hp.2.1)
  have hKfun : ContinuousOn (fun p : ℍ × ℝ => Work.Kernels.Kfun ℓ d p.1 (iAxisFun p.2))
      (badStrip ×ˢ Set.Icc (3 : ℝ) (max T 3)) := by
    have h := (Work.Asymptotics.continuousOn_Kfun_clean ℓ d hd).comp hΦ hmaps
    exact h
  refine hKfun.congr (fun p hp => ?_)
  have ht : 0 < p.2 := lt_of_lt_of_le (by norm_num) hp.2.1
  rw [Work.Kernels.Kaxis, dif_pos ht]
  congr 1
  exact (iAxisFun_eq_imagAxis (le_trans (by norm_num) hp.2.1)).symm

/-! ## The main theorem -/

/-- **The tail bound `K - 𝒢 = O((1+t)^M e^{-πt})` on the bad-line region.**

There are `C > 0` and `M ≥ 0` such that for every `τ ∈ lowBadSet` and every `t ≥ lowT = 3` the
difference between the CKMRV kernel along the contour and its non-decaying cusp expansion is
bounded by `C (1+t)^M e^{-πt}`. -/
theorem lowBad_Aexp_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, Work.Asymptotics.HalfFunnel.lowT ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  -- the cusp expansion on the compact strip, for `t ≥ T`
  obtain ⟨C₀, M₀, T, hC₀, hM₀, -, htail⟩ := kernel_axis_bound ℓ d hd isCompact_badStrip
  -- the window `3 ≤ t ≤ max T 3`: continuity on a compact set
  have hAexpcont : Continuous (fun p : ℍ × ℝ => Aexp (Gcusp ℓ d) p.1 p.2) := by
    have hGc : ∀ i j : Fin 2, Continuous (fun τ : ℍ => Gcusp ℓ d i j τ) :=
      fun i j => continuous_Gcusp ℓ d hd i j
    unfold Aexp
    fun_prop
  have hdiffcont : ContinuousOn (fun p : ℍ × ℝ =>
      Kaxis (Kfun ℓ d) p.1 p.2 - Aexp (Gcusp ℓ d) p.1 p.2)
      (badStrip ×ˢ Set.Icc (3 : ℝ) (max T 3)) :=
    (continuousOn_Kaxis_badStrip ℓ d hd T).sub hAexpcont.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_badStrip.prod isCompact_Icc).exists_bound_of_continuousOn hdiffcont
  -- assembly
  set C : ℝ := max C₀ (B * Real.exp (Real.pi * max T 3)) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCle : C₀ ≤ C := by
    rw [hCdef]; linarith [le_max_left C₀ (B * Real.exp (Real.pi * max T 3))]
  have hCge : B * Real.exp (Real.pi * max T 3) ≤ C := by
    rw [hCdef]; linarith [le_max_right C₀ (B * Real.exp (Real.pi * max T 3))]
  refine ⟨C, M₀, hCpos, hM₀, fun τ hτ t ht => ?_⟩
  have hτc : τ ∈ badStrip := mem_badStrip hτ
  have ht3 : (3 : ℝ) ≤ t := ht
  have hnn : (0 : ℝ) ≤ (1 + t) ^ M₀ * Real.exp (-(Real.pi * t)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  rcases le_or_gt t T with htT | htT
  · -- window
    have hmem : t ∈ Set.Icc (3 : ℝ) (max T 3) :=
      ⟨ht3, le_trans htT (le_max_left T 3)⟩
    have hb := hB (τ, t) ⟨hτc, hmem⟩
    refine le_trans hb ?_
    have h1 : (1 : ℝ) ≤ 1 + t := by linarith
    have hMa : (1 : ℝ) ≤ (1 + t) ^ M₀ := Real.one_le_rpow h1 hM₀
    have hexp : Real.exp (-(Real.pi * max T 3)) ≤ Real.exp (-(Real.pi * t)) := by
      apply Real.exp_le_exp.mpr
      have hle : t ≤ max T 3 := le_trans htT (le_max_left T 3)
      nlinarith [Real.pi_pos, hle]
    have h0 : B = (B * Real.exp (Real.pi * max T 3)) * Real.exp (-(Real.pi * max T 3)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [h0]
    calc (B * Real.exp (Real.pi * max T 3)) * Real.exp (-(Real.pi * max T 3))
        ≤ C * Real.exp (-(Real.pi * max T 3)) :=
          mul_le_mul_of_nonneg_right hCge (Real.exp_pos _).le
      _ ≤ C * ((1 + t) ^ M₀ * Real.exp (-(Real.pi * t))) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          have hstep : Real.exp (-(Real.pi * max T 3))
              ≤ (1 + t) ^ M₀ * Real.exp (-(Real.pi * t)) := by
            have hm := mul_le_mul hMa hexp (Real.exp_pos _).le
              (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) M₀)
            simpa using hm
          exact hstep
      _ = C * (1 + t) ^ M₀ * Real.exp (-(Real.pi * t)) := by ring
  · -- beyond the threshold of the cusp expansion
    have hb := htail τ hτc t (le_of_lt htT)
    refine le_trans hb ?_
    have hCp : C₀ * (1 + t) ^ M₀ ≤ C * (1 + t) ^ M₀ :=
      mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (by linarith) M₀)
    calc C₀ * (1 + t) ^ M₀ * Real.exp (-(Real.pi * t))
        = (C₀ * (1 + t) ^ M₀) * Real.exp (-(Real.pi * t)) := rfl
      _ ≤ (C * (1 + t) ^ M₀) * Real.exp (-(Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hCp (Real.exp_pos _).le
      _ = C * (1 + t) ^ M₀ * Real.exp (-(Real.pi * t)) := rfl

end Work.HFN.HalfFunnel
