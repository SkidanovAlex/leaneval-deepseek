import Mathlib
import Submission.Work.GM.S2.hhat_decay_defs

/-!
# Derivative bounds for the amplitude `hhatAmp` (GM Lemma 4.3(2), first half)

The amplitude of `hhat` is

`hhatAmp ξ u = w(u)² · e^{-2πi ξ u}`   (`Submission.Work.GM.S2.hhatAmp`),

a fixed bump `w²` times a pure oscillation of frequency proportional to `ξ`.  GM Lemma 4.3(2)
needs the family `ξ ↦ hhatAmp ξ` to have `k`-th derivatives bounded by `C_k (1+|ξ|)^k`, uniformly
in `u`.  That is exactly the statement proved here.

The proof is elementary.  Writing `ψ = w²` and `E_σ(u) = e^{iσu}`, the Leibniz rule gives

`(d/du)^k (ψ · E_σ)(u) = Σ_{i≤k} C(k,i) ψ^{(i)}(u) (iσ)^{k-i} E_σ(u)`,

`|E_σ| = 1`, and `|ψ^{(i)}|` is bounded uniformly in `u` because `w` is `C^∞` with all
derivatives bounded (`Submission.LargeValues.bumpW_deriv_bdd`).  This yields the crude bound
`C_k (1+|σ|)^k`; substituting `σ = -2πξ` gives the statement.
-/

namespace Work.GM.S2

open Complex

noncomputable section

/-- The complexification `u ↦ (w u : ℂ)` of the Guth–Maynard bump. -/
noncomputable def bwC (u : ℝ) : ℂ := (Submission.LargeValues.bumpW u : ℂ)

/-- `ψ = w²` viewed in `ℂ`: the weight appearing in `hhatAmp`. -/
noncomputable def psiC (u : ℝ) : ℂ := ((Submission.LargeValues.bumpW u ^ 2 : ℝ) : ℂ)

/-- The pure oscillation `u ↦ e^{iσu}` (the Fourier kernel `hhatKernel` with `σ = -2πξ`). -/
noncomputable def eExp (σ : ℝ) (u : ℝ) : ℂ := Complex.exp (Complex.I * ((σ * u : ℝ) : ℂ))

/-! ### The complexification of the bump -/

lemma ofRealLI_comp_bumpW : (Complex.ofRealLI : ℝ → ℂ) ∘ Submission.LargeValues.bumpW = bwC := by
  funext u; simp [bwC]

lemma contDiff_bwC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bwC := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (Submission.LargeValues.bumpW x : ℂ))
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Complex.ofRealCLM (Submission.LargeValues.bumpW x)) :=
    ContDiff.continuousLinearMap_comp Complex.ofRealCLM Submission.LargeValues.bumpW_contDiff
  exact h

lemma contDiffAt_bwC (j : ℕ) (u : ℝ) : ContDiffAt ℝ (j : WithTop ℕ∞) bwC u :=
  contDiff_bwC.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))

/-- Complexifying the bump does not change the size of its iterated derivatives (a norm
preservation, because `u ↦ (u : ℂ)` is a linear isometry). -/
lemma norm_iteratedDeriv_bwC (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j bwC x‖ = ‖iteratedDeriv j Submission.LargeValues.bumpW x‖ := by
  have h := LinearIsometry.norm_iteratedFDeriv_comp_left (f := Submission.LargeValues.bumpW)
      (x := x) (i := j) Complex.ofRealLI
      ((Submission.LargeValues.bumpW_contDiff.contDiffAt).of_le
        (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))) le_rfl
  rw [ofRealLI_comp_bumpW] at h
  rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv (n := j) (f := bwC) (x := x),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv (n := j) (f := Submission.LargeValues.bumpW)
        (x := x)] at h

lemma psiC_eq : psiC = bwC * bwC := by
  funext u
  simp only [Pi.mul_apply, psiC, bwC, Complex.ofReal_pow]
  ring

lemma contDiff_psiC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psiC := by
  rw [psiC_eq]
  exact contDiff_bwC.mul contDiff_bwC

lemma contDiffAt_psiC (j : ℕ) (u : ℝ) : ContDiffAt ℝ (j : WithTop ℕ∞) psiC u :=
  contDiff_psiC.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))

lemma psiC_deriv_bdd (j : ℕ) : ∃ C, 0 ≤ C ∧ ∀ u, ‖iteratedDeriv j psiC u‖ ≤ C := by
  have hbw : ∀ i, ∃ C, 0 ≤ C ∧ ∀ u, ‖iteratedDeriv i bwC u‖ ≤ C := by
    intro i
    obtain ⟨C, hC0, hC⟩ := Submission.LargeValues.bumpW_deriv_bdd i
    refine ⟨C, hC0, fun u => ?_⟩
    rw [norm_iteratedDeriv_bwC]
    exact hC u
  choose c hc0 hc using hbw
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c i * c (j - i), ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (by positivity) (hc0 i)) (hc0 (j - i))
  · intro u
    rw [psiC_eq,
      iteratedDeriv_mul (f := bwC) (g := bwC) (𝔸 := ℂ) (contDiffAt_bwC j u) (contDiffAt_bwC j u)]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i hi => ?_))
    have h1 := hc i u
    have h2 := hc (j - i) u
    have hcinn : (0:ℝ) ≤ c i := hc0 i
    have hcin2 : (0:ℝ) ≤ c (j - i) := hc0 (j - i)
    have hch : (0:ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have hAB : ‖iteratedDeriv i bwC u‖ * ‖iteratedDeriv (j - i) bwC u‖ ≤ c i * c (j - i) :=
      mul_le_mul h1 h2 (norm_nonneg _) hcinn
    calc (j.choose i : ℝ) * ‖iteratedDeriv i bwC u‖ * ‖iteratedDeriv (j - i) bwC u‖
        = (j.choose i : ℝ) * (‖iteratedDeriv i bwC u‖ * ‖iteratedDeriv (j - i) bwC u‖) := by ring
      _ ≤ (j.choose i : ℝ) * (c i * c (j - i)) := mul_le_mul_of_nonneg_left hAB hch
      _ = (j.choose i : ℝ) * c i * c (j - i) := by ring

/-! ### The oscillation `e^{iσu}` -/

lemma hasDerivAt_eExp (σ : ℝ) (u : ℝ) :
    HasDerivAt (eExp σ) (eExp σ u * (Complex.I * (σ : ℂ))) u := by
  have hg : HasDerivAt (fun x : ℝ => Complex.I * ((σ * x : ℝ) : ℂ)) (Complex.I * (σ:ℂ)) u := by
    have h1 : HasDerivAt (fun x : ℝ => ((σ * x : ℝ) : ℂ)) ((σ:ℝ) : ℂ) u := by
      simpa using ((hasDerivAt_id (x := u) (𝕜 := ℝ)).const_mul σ).ofReal_comp
    simpa using h1.const_mul Complex.I
  have h2 := (Complex.hasDerivAt_exp (Complex.I * ((σ * u : ℝ) : ℂ))).comp u hg
  show HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * ((σ * x : ℝ) : ℂ)))
    (Complex.exp (Complex.I * ((σ * u : ℝ) : ℂ)) * (Complex.I * (σ:ℂ))) u
  exact h2

lemma contDiff_eExp (σ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eExp σ) := by
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun u : ℝ => Complex.exp (Complex.I * ((σ * u : ℝ) : ℂ)))
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => σ * u) :=
    contDiff_const_smul (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) σ
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ((σ * u : ℝ) : ℂ)) :=
    ContDiff.continuousLinearMap_comp Complex.ofRealCLM hlin
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => Complex.I * ((σ * u : ℝ) : ℂ)) :=
    h1.const_smul Complex.I
  exact Complex.contDiff_exp.comp h2

lemma contDiffAt_eExp (σ : ℝ) (j : ℕ) (u : ℝ) : ContDiffAt ℝ (j : WithTop ℕ∞) (eExp σ) u :=
  (contDiff_eExp σ).contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))

lemma norm_eExp (σ : ℝ) (u : ℝ) : ‖eExp σ u‖ = 1 := by
  rw [eExp, Complex.norm_exp]
  have : (Complex.I * ((σ * u : ℝ) : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero]

lemma iteratedDeriv_eExp (σ : ℝ) (m : ℕ) :
    iteratedDeriv m (eExp σ) = fun u => (Complex.I * (σ:ℂ))^m * eExp σ u := by
  induction m with
  | zero => funext u; simp [iteratedDeriv_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    rw [deriv_const_mul ((Complex.I * (σ:ℂ))^m) ((hasDerivAt_eExp σ u).differentiableAt),
        (hasDerivAt_eExp σ u).deriv]
    simp only [eExp, pow_succ]
    ring

lemma norm_iteratedDeriv_eExp (σ : ℝ) (m : ℕ) (u : ℝ) :
    ‖iteratedDeriv m (eExp σ) u‖ = |σ|^m := by
  rw [iteratedDeriv_eExp, norm_mul, norm_pow, norm_eExp, mul_one]
  congr 1
  rw [norm_mul, Complex.norm_I, one_mul]
  simp

/-! ### The product bound -/

/-- Uniform derivative bound for `u ↦ ψ(u) e^{iσu}`, the amplitude with the substitution
`σ = -2πξ` not yet made. -/
lemma exists_bound_mul_eExp (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (σ : ℝ) (u : ℝ),
      ‖iteratedDeriv k (fun u => psiC u * eExp σ u) u‖ ≤ D * (1 + |σ|) ^ k := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ i u, ‖iteratedDeriv i psiC u‖ ≤ C i := by
    choose c hc0 hc using psiC_deriv_bdd
    exact ⟨c, hc0, hc⟩
  let M : ℝ := ∑ i ∈ Finset.range (k + 1), C i
  have hM0 : 0 ≤ M := by
    dsimp [M]; exact Finset.sum_nonneg (fun i _ => hC0 i)
  refine ⟨(k + 1 : ℝ) * (2:ℝ)^k * M, by positivity, ?_⟩
  intro σ u
  change ‖iteratedDeriv k (psiC * eExp σ) u‖ ≤ (k + 1 : ℝ) * (2:ℝ)^k * M * (1 + |σ|)^k
  rw [iteratedDeriv_mul (f := psiC) (g := eExp σ) (𝔸 := ℂ)
      (contDiffAt_psiC k u) (contDiffAt_eExp σ k u)]
  refine le_trans (norm_sum_le _ _) ?_
  calc (∑ i ∈ Finset.range (k + 1),
          ‖(↑(k.choose i) : ℂ) * iteratedDeriv i psiC u * iteratedDeriv (k - i) (eExp σ) u‖)
      ≤ ∑ i ∈ Finset.range (k + 1), (2:ℝ)^k * M * (1 + |σ|)^k :=
        Finset.sum_le_sum (fun i hi => ?_)
    _ = ((k : ℝ) + 1) * ((2:ℝ)^k * M * (1 + |σ|)^k) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
    _ = (k + 1 : ℝ) * (2:ℝ)^k * M * (1 + |σ|)^k := by ring
  · rw [norm_mul, norm_mul, Complex.norm_natCast]
    have hCi : C i ≤ M := by
      dsimp [M]; exact Finset.single_le_sum (fun j _ => hC0 j) hi
    have hA : ‖iteratedDeriv i psiC u‖ ≤ M := le_trans (hC i u) hCi
    have hB : ‖iteratedDeriv (k - i) (eExp σ) u‖ = |σ|^(k-i) := norm_iteratedDeriv_eExp σ (k-i) u
    have hch : (k.choose i : ℝ) ≤ (2:ℝ)^k := by
      have h := Nat.choose_le_two_pow k i
      have h2 : ((k.choose i : ℕ) : ℝ) ≤ ((2:ℕ)^k : ℝ) := by exact_mod_cast h
      simpa using h2
    have hσk : |σ|^(k-i) ≤ (1 + |σ|)^k := by
      have h1 : |σ| ≤ 1 + |σ| := le_add_of_nonneg_left (by norm_num)
      have h2 : |σ|^(k-i) ≤ (1 + |σ|)^(k-i) := pow_le_pow_left₀ (abs_nonneg σ) h1 (k-i)
      have h3 : (1 + |σ|)^(k-i) ≤ (1 + |σ|)^k :=
        pow_le_pow_right₀ (by linarith [abs_nonneg σ]) (by omega)
      exact le_trans h2 h3
    rw [hB]
    have hAb : (k.choose i : ℝ) * ‖iteratedDeriv i psiC u‖ ≤ (2:ℝ)^k * M :=
      mul_le_mul hch hA (norm_nonneg _) (by positivity)
    calc (k.choose i : ℝ) * ‖iteratedDeriv i psiC u‖ * |σ|^(k-i)
        ≤ ((2:ℝ)^k * M) * (1 + |σ|)^k :=
          mul_le_mul hAb hσk (pow_nonneg (abs_nonneg σ) _) (mul_nonneg (by positivity) hM0)
      _ = (2:ℝ)^k * M * (1 + |σ|)^k := by ring

/-! ### The statement -/

theorem hhat_amp_deriv_bound (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ξ u : ℝ),
      ‖iteratedDeriv k (Work.GM.S2.hhatAmp ξ) u‖ ≤ D * (1 + |ξ|) ^ k := by
  obtain ⟨D0, hD0, hbound⟩ := exists_bound_mul_eExp k
  refine ⟨D0 * (1 + 2 * Real.pi)^k, mul_nonneg hD0 (pow_nonneg (by positivity) k), ?_⟩
  intro ξ u
  have hfun : hhatAmp ξ = fun u => psiC u * eExp (-(2 * Real.pi * ξ)) u := by
    funext v
    simp only [hhatAmp, psiC]
    congr 1
    simp only [hhatKernel, eExp]
    congr 1
    push_cast
    ring_nf
  have hσ : |-(2 * Real.pi * ξ)| = 2 * Real.pi * |ξ| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos Real.pi_pos]
  have hpow : (1 + 2 * Real.pi * |ξ|)^k ≤ (1 + 2 * Real.pi)^k * (1 + |ξ|)^k := by
    have h1 : 1 + 2 * Real.pi * |ξ| ≤ (1 + 2 * Real.pi) * (1 + |ξ|) := by
      nlinarith [Real.pi_pos, abs_nonneg ξ]
    calc (1 + 2 * Real.pi * |ξ|)^k ≤ ((1 + 2 * Real.pi) * (1 + |ξ|))^k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = (1 + 2 * Real.pi)^k * (1 + |ξ|)^k := mul_pow _ _ _
  calc ‖iteratedDeriv k (hhatAmp ξ) u‖
      = ‖iteratedDeriv k (fun u => psiC u * eExp (-(2 * Real.pi * ξ)) u) u‖ := by rw [hfun]
    _ ≤ D0 * (1 + |-(2 * Real.pi * ξ)|)^k := hbound _ u
    _ = D0 * (1 + 2 * Real.pi * |ξ|)^k := by rw [hσ]
    _ ≤ D0 * ((1 + 2 * Real.pi)^k * (1 + |ξ|)^k) := mul_le_mul_of_nonneg_left hpow hD0
    _ = (D0 * (1 + 2 * Real.pi)^k) * (1 + |ξ|)^k := by ring

end

end Work.GM.S2
