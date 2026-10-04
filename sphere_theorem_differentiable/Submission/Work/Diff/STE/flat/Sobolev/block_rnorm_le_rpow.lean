import Mathlib
import Submission.Work.Diff.STE.flat.Sobolev

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp `L^{2p}` bound for a single dyadic block — with the *real* exponent `(1 / 2 : ℝ)`

This module proves the estimate *intended* by the requested lemma
`Work.Diff.STE.flat.Sobolev.block_rnorm_le` (at `Submission/Work/Diff/STE/flat/Sobolev/
block_rnorm_le.lean`), namely, for `p ≥ 1`, `j ≥ n(1/2 - 1/(2p))` (`n = card ι`), a dyadic block
`blockCoeff m γ` and a coefficient family `γ` with `Σ_k (wt k)^j ‖γ k‖² < ∞`:

`‖seriesFun (blockCoeff m γ)‖_{L^{2p}} ≤ 6^{n(1/2-1/(2p))} · 2^{-m(j - n(1/2-1/(2p)))} ·
  (blockMass j m γ)^{1/2}`.

## Why a separate module

The requested statement writes the last factor as `(blockMass j m γ) ^ (1 / 2)`.  Without a type
ascription, Lean elaborates the exponent `1 / 2` as **natural** number division
(`(1 : ℕ) / 2 = 0`, definitionally), so the requested right-hand side is
`6^{nθ} · 2^{-m(j - nθ)} · (blockMass j m γ) ^ (0 : ℕ) = 6^{nθ} · 2^{-m(j - nθ)}`, i.e. a constant
*independent of `γ`*.  The requested statement is therefore **false** (see
`Work.Diff.STE.flat.Sobolev.block_rnorm_le_requested_false` in `block_rnorm_le.lean`, which
machine-checks the negation): taking `ι = Fin 1`, `p = 1`, `j = 0`, `m = 0` and
`γ = n • δ₀` gives `(blockMass 0 0 γ) ^ (1/2) = 1` while the left-hand side is `n`.

The present theorem is the same claim with the genuine real exponent `(1 / 2 : ℝ) = √·`; it is the
per-block Littlewood–Paley estimate that the corrected sharp Sobolev embedding
`Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le` consumes (see
`Submission/Work/Diff/STE/flat/Sobolev/rnorm_seriesFun_rpow_le.lean`).

⚠️  A bare `^ (1 / 2)` on a real base elaborates to `ℕ`-division, i.e. to the exponent `0`.  Always
write `(1 / 2 : ℝ)` (or use `Real.sqrt`).

## Route

* the block is finitely supported (on the annulus `m`), so `seriesFun (blockCoeff m γ)` converges
  absolutely and, by Parseval for absolutely convergent Fourier series
  (`Work.Diff.STE.integral_normSq_seriesFun`),
  `∫ ‖seriesFun (blockCoeff m γ)‖² = Σ_k ‖blockCoeff m γ k‖² =: T`;
* `L^∞`–`L²` interpolation (inlined below as the private
  `rnorm_le_of_sup_l2_rpow_aux`; the same statement is proved in
  `Submission/Work/Diff/STE/flat/Sobolev/rnorm_le_of_sup_l2.lean` as
  `Work.Diff.STE.flat.Sobolev.rnorm_le_of_sup_l2_rpow`) gives
  `rnorm (2p) f ≤ (Σ_k ‖blockCoeff m γ k‖)^{1-1/p} T^{1/(2p)}`, and Cauchy–Schwarz over the
  annulus with the dyadic counting constant `#annulus m ≤ 6^n 2^{mn}`
  (`Work.Diff.STE.flat.Sobolev.block_l1_sq_le`) bounds the `ℓ¹` norm by `√(6^n 2^{mn}) √T`, so
  `rnorm (2p) f ≤ (6^n 2^{mn})^θ T^{1/2}` with `θ = 1/2 - 1/(2p)`;
* on the annulus the weight satisfies `wt k ≥ 2^{2m}`, so `T^{1/2} ≤ 2^{-mj}(blockMass j m γ)^{1/2}`.

Multiplying the last two bounds and combining the two `2`-powers
(`6^{nθ} 2^{mnθ} · 2^{-mj} = 6^{nθ} 2^{-m(j-nθ)}`) gives the statement.
-/

noncomputable section

namespace Work.Diff.STE.flat.Sobolev

open MeasureTheory BigOperators

/-! ## Toolbox: integrability on the cube, and the pointwise interpolation step -/

/-- `x ↦ ‖f x‖ ^ q` is integrable on the unit cube for a continuous `f` and `q ≥ 0`: the cube is
contained in the compact product `∏ (Icc 0 1)`. -/
private lemma integrableOn_unitCube_norm_rpow {ι : Type*} [Fintype ι]
    (q : ℝ) (hq0 : 0 ≤ q) {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    Integrable (fun x : ι → ℝ => ‖f x‖ ^ q)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have hbig : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : Work.Diff.STE.unitCube (ι := ι) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  have hcont : Continuous fun x : ι → ℝ => ‖f x‖ ^ q :=
    (Real.continuous_rpow_const hq0).comp hf.norm
  exact (ContinuousOn.integrableOn_compact hbig hcont.continuousOn).mono_set hsub

/-- `x ↦ P ^ (q - 2) * ‖f x‖ ^ 2` is integrable on the unit cube for a continuous `f`. -/
private lemma integrableOn_unitCube_const_mul_norm_sq {ι : Type*} [Fintype ι]
    (P q : ℝ) {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    Integrable (fun x : ι → ℝ => P ^ (q - 2) * ‖f x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have hbig : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : Work.Diff.STE.unitCube (ι := ι) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  have hcont : Continuous fun x : ι → ℝ => P ^ (q - 2) * ‖f x‖ ^ 2 :=
    continuous_const.mul (hf.norm.pow 2)
  exact (ContinuousOn.integrableOn_compact hbig hcont.continuousOn).mono_set hsub

/-- The pointwise `L^∞`–`L²` interpolation step: for `q ≥ 2` and `‖f x‖ ≤ P`,
`‖f x‖ ^ q ≤ P ^ (q - 2) * ‖f x‖ ^ 2`. -/
private lemma norm_rpow_le_mul_sup {ι : Type*} {f : (ι → ℝ) → ℂ} {q P : ℝ}
    (hq : 2 ≤ q) (hsup : ∀ x, ‖f x‖ ≤ P) (x : ι → ℝ) :
    ‖f x‖ ^ q ≤ P ^ (q - 2) * ‖f x‖ ^ 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  rcases eq_or_lt_of_le (norm_nonneg (f x)) with h0 | hpos
  · rw [← h0, Real.zero_rpow (ne_of_gt hq0)]
    simp
  · have h2 : ‖f x‖ ^ 2 = ‖f x‖ ^ (2 : ℝ) := (Real.rpow_ofNat _ 2).symm
    rw [h2]
    calc ‖f x‖ ^ q = ‖f x‖ ^ (2 + (q - 2)) := by congr 1; ring
      _ = ‖f x‖ ^ (2 : ℝ) * ‖f x‖ ^ (q - 2) := Real.rpow_add hpos 2 (q - 2)
      _ ≤ ‖f x‖ ^ (2 : ℝ) * P ^ (q - 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg _) 2)
            exact Real.rpow_le_rpow (norm_nonneg _) (hsup x) (by linarith)
      _ = P ^ (q - 2) * ‖f x‖ ^ (2 : ℝ) := by ring

/-- **`L^q` interpolation from a sup bound and the `L²` norm.**  On the unit cube `(0,1]^ι`
(measure `1`), let `f` be continuous with `‖f x‖ ≤ P` for all `x` and `Q = ∫_{cube} ‖f‖²`.  If
`P ^ 2 ≤ C * Q` (i.e. `P ≤ √C √Q`) and `q ≥ 2`, then
`(∫_{cube} ‖f‖^q)^{1/q} ≤ C^{1/2 - 1/q} Q^{1/2}` — the `L^∞`–`L^q` interpolation
`‖f‖_{L^q} ≤ ‖f‖_∞^{1-2/q} ‖f‖_{L²}^{2/q}` combined with `P ≤ √C √Q`.

This is the statement intended by `rnorm_le_of_sup_l2`; note that the exponent of `Q` here is
*explicitly* real (`(1 : ℝ) / 2`), which is what makes the statement true. -/
private lemma rnorm_le_of_sup_l2_rpow_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (hq : 2 ≤ q) (f : (ι → ℝ) → ℂ) (hf : Continuous f)
    (P C Q : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hsup : ∀ x, ‖f x‖ ≤ P) (hPC : P ^ 2 ≤ C * Q)
    (hint : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ 2 = Q) :
    Work.Diff.STE.flat.rnorm q f ≤ C ^ (1 / 2 - 1 / q) * Q ^ ((1 : ℝ) / 2) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hexp1_nn : 0 ≤ 1 - 2 / q := by
    rw [sub_nonneg, div_le_one hq0]
    exact hq
  have hexp2 : (1 : ℝ) / 2 * (1 - 2 / q) = 1 / 2 - 1 / q := by field_simp
  have hexp3 : (q - 2) * (1 / q) = 1 - 2 / q := by field_simp
  -- the pointwise bound, integrated
  have hAint : Integrable (fun x : ι → ℝ => ‖f x‖ ^ q)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    integrableOn_unitCube_norm_rpow q (le_of_lt hq0) hf
  have hBint : Integrable (fun x : ι → ℝ => P ^ (q - 2) * ‖f x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    integrableOn_unitCube_const_mul_norm_sq P q hf
  have hle1 : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ q ≤ P ^ (q - 2) * Q := by
    calc ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ q
        ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), P ^ (q - 2) * ‖f x‖ ^ 2 :=
          integral_mono_ae hAint hBint
            (Filter.Eventually.of_forall fun x => norm_rpow_le_mul_sup hq hsup x)
      _ = P ^ (q - 2) * ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ 2 := by
            rw [integral_const_mul]
      _ = P ^ (q - 2) * Q := by rw [hint]
  -- take the `1/q`-th power
  have hA_nn : 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ q :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) q
  have hinvq_nn : 0 ≤ 1 / q := div_nonneg zero_le_one (le_of_lt hq0)
  have hstep1 : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ q) ^ (1 / q)
      ≤ (P ^ (q - 2) * Q) ^ (1 / q) := Real.rpow_le_rpow hA_nn hle1 hinvq_nn
  have hfactor : (P ^ (q - 2) * Q) ^ (1 / q) = P ^ (1 - 2 / q) * Q ^ (1 / q) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hP _) hQ, ← Real.rpow_mul hP, hexp3]
  -- `P ^ (1 - 2/q) ≤ C ^ (1/2 - 1/q) * Q ^ (1/2 - 1/q)`
  have hPle : P ≤ C ^ ((1 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2) := by
    have h1 : P ≤ Real.sqrt (C * Q) := (Real.sqrt_sq hP).symm.trans_le (Real.sqrt_le_sqrt hPC)
    rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow] at h1
    exact h1
  have hstep2 : P ^ (1 - 2 / q) ≤ C ^ (1 / 2 - 1 / q) * Q ^ (1 / 2 - 1 / q) := by
    have h2 := Real.rpow_le_rpow hP hPle hexp1_nn
    rw [Real.mul_rpow (Real.rpow_nonneg hC _) (Real.rpow_nonneg hQ _),
        ← Real.rpow_mul hC, ← Real.rpow_mul hQ, hexp2] at h2
    exact h2
  -- `Q ^ (1/2 - 1/q) * Q ^ (1/q) = Q ^ (1/2)`
  have hQexp : Q ^ (1 / 2 - 1 / q) * Q ^ (1 / q) = Q ^ ((1 : ℝ) / 2) := by
    rcases eq_or_lt_of_le hQ with h | h
    · rw [← h, Real.zero_rpow (ne_of_gt (one_div_pos.mpr hq0)), mul_zero]
      rw [Real.zero_rpow (by norm_num : ((1 : ℝ) / 2) ≠ 0)]
    · rw [← Real.rpow_add h]
      congr 1
      ring
  calc Work.Diff.STE.flat.rnorm q f
      = (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x‖ ^ q) ^ (1 / q) := rfl
    _ ≤ (P ^ (q - 2) * Q) ^ (1 / q) := hstep1
    _ = P ^ (1 - 2 / q) * Q ^ (1 / q) := hfactor
    _ ≤ (C ^ (1 / 2 - 1 / q) * Q ^ (1 / 2 - 1 / q)) * Q ^ (1 / q) :=
        mul_le_mul_of_nonneg_right hstep2 (Real.rpow_nonneg hQ _)
    _ = C ^ (1 / 2 - 1 / q) * (Q ^ (1 / 2 - 1 / q) * Q ^ (1 / q)) := by ring
    _ = C ^ (1 / 2 - 1 / q) * Q ^ ((1 : ℝ) / 2) := by rw [hQexp]


/-- The block `blockCoeff m γ` is dominated (`ℓ¹`) by `γ`: it vanishes off the annulus and equals
`γ` there. -/
private lemma summable_norm_blockCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (γ : (ι → ℤ) → ℂ) (hγ : Summable fun k : ι → ℤ => ‖γ k‖) :
    Summable fun k : ι → ℤ => ‖blockCoeff m γ k‖ := by
  refine hγ.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
  by_cases hk : k ∈ annulus m
  · rw [blockCoeff_apply_mem m γ hk]
  · rw [blockCoeff_apply_not_mem m γ hk, norm_zero]
    exact norm_nonneg _

/-- The sup-norm of `seriesFun (blockCoeff m γ)` is at most the `ℓ¹` norm of the block (the
characters have modulus one, so this is the triangle inequality for absolutely convergent
series). -/
private lemma norm_seriesFun_block_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (γ : (ι → ℤ) → ℂ) (hγ : Summable fun k : ι → ℤ => ‖γ k‖) (x : ι → ℝ) :
    ‖Work.Diff.STE.seriesFun (blockCoeff m γ) x‖
      ≤ ∑' k : ι → ℤ, ‖blockCoeff m γ k‖ := by
  have h1 := summable_norm_blockCoeff m γ hγ
  have h2 : Summable fun k : ι → ℤ => ‖blockCoeff m γ k * Work.Diff.STE.fourierExp k x‖ :=
    h1.congr fun k => by rw [norm_mul, Work.Diff.STE.BesselCont.norm_fourierExp_char, mul_one]
  calc ‖Work.Diff.STE.seriesFun (blockCoeff m γ) x‖
      = ‖∑' k : ι → ℤ, blockCoeff m γ k * Work.Diff.STE.fourierExp k x‖ := rfl
    _ ≤ ∑' k : ι → ℤ, ‖blockCoeff m γ k * Work.Diff.STE.fourierExp k x‖ :=
        norm_tsum_le_tsum_norm h2
    _ = ∑' k : ι → ℤ, ‖blockCoeff m γ k‖ :=
        tsum_congr fun k => by
          rw [norm_mul, Work.Diff.STE.BesselCont.norm_fourierExp_char, mul_one]

/-- **The `ℓ²` mass of a dyadic block against its weighted mass.**  The weight `wt k = ⟨k⟩²` is at
least `2^{2m}` on the annulus `m`, so for `j ≥ 0` we have `(wt k)^j ≥ 2^{2mj}` there; the block
vanishes off the annulus.  Hence `Σ_k ‖blockCoeff m γ k‖² ≤ 2^{-2mj} blockMass j m γ` and taking
square roots gives the stated form.  (Summability is inherited from the weighted mass of `γ`:
the weights are `≥ 1`, so `Σ_k ‖γ k‖²` is summable too.)

Note the explicit real exponents `((1 : ℝ) / 2)`: a bare `^ (1 / 2)` on a real base would be
elaborated as the natural power `^ ((1 : ℕ) / 2) = ^ 0 = 1`. -/
private lemma block_l2_sqrt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℝ) (hj : 0 ≤ j) (m : ℕ) (γ : (ι → ℤ) → ℂ)
    (hM : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) :
    (∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (2 : ℝ) ^ (-(m : ℝ) * j) * (blockMass j m γ) ^ ((1 : ℝ) / 2) := by
  -- the weights are `≥ 1` (as `j ≥ 0`), so both `Σ ‖blockCoeff‖²` and the weighted mass of the
  -- block are summable, by comparison with the weighted mass of `γ`
  have hone : ∀ k : ι → ℤ, (1 : ℝ) ≤ (Work.Diff.STE.wt k) ^ j :=
    fun k => Real.one_le_rpow (Work.Diff.STE.wt_one_le k) hj
  have hdom : ∀ k : ι → ℤ,
      (Work.Diff.STE.wt k) ^ j * ‖blockCoeff m γ k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2 := by
    intro k
    by_cases hk : k ∈ annulus m
    · rw [blockCoeff_apply_mem m γ hk]
    · rw [blockCoeff_apply_not_mem m γ hk, norm_zero, sq, mul_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)
  have hsumW : Summable fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ j * ‖blockCoeff m γ k‖ ^ 2 :=
    hM.of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _))
      hdom
  have hsumT : Summable fun k : ι → ℤ => ‖blockCoeff m γ k‖ ^ 2 :=
    hsumW.of_nonneg_of_le (fun k => sq_nonneg _) fun k =>
      le_mul_of_one_le_left (sq_nonneg _) (hone k)
  -- the weighted mass of the block dominates its `ℓ²` mass with the factor `2^{2mj}`
  have hkey : (2 : ℝ) ^ (2 * (m : ℝ) * j) * (∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2)
      ≤ blockMass j m γ := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_)
      (hsumT.mul_left ((2 : ℝ) ^ (2 * (m : ℝ) * j))) hsumW
    by_cases hk : k ∈ annulus m
    · have hann : (2 : ℝ) ^ (2 * m) ≤ Work.Diff.STE.wt k := hk.1
      have hpow : (2 : ℝ) ^ (2 * (m : ℝ) * j) = ((2 : ℝ) ^ (2 * m)) ^ j := by
        rw [← Real.rpow_natCast (2 : ℝ) (2 * m), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hann hj) (sq_nonneg _)
    · rw [blockCoeff_apply_not_mem m γ hk, norm_zero, sq, mul_zero, mul_zero]
      simp
  -- divide by `2^{2mj}` and take square roots
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * (m : ℝ) * j) := Real.rpow_pos_of_pos (by norm_num) _
  have hTle : (∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2)
      ≤ (2 : ℝ) ^ (-(2 * (m : ℝ) * j)) * blockMass j m γ := by
    have h1 : (∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2)
        ≤ blockMass j m γ / (2 : ℝ) ^ (2 * (m : ℝ) * j) :=
      (le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hkey)
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm] at h1
    exact h1
  calc (∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ((2 : ℝ) ^ (-(2 * (m : ℝ) * j)) * blockMass j m γ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (tsum_nonneg fun k => sq_nonneg _) hTle (by norm_num)
    _ = ((2 : ℝ) ^ (-(2 * (m : ℝ) * j))) ^ ((1 : ℝ) / 2)
          * (blockMass j m γ) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (blockMass_nonneg j m γ)
    _ = (2 : ℝ) ^ (-(m : ℝ) * j) * (blockMass j m γ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring

/-- The integer lattice box `∏ᵢ [-K, K] ⊆ ℤ^ι`. -/
private def latBox {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => Finset.Icc (-(K : ℤ)) (K : ℤ)

private lemma latBox_card_Icc (K : ℕ) : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
  rw [Int.card_Icc]
  have h : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private lemma latBox_card {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℕ) :
    (latBox (ι := ι) K).card = (2 * K + 1) ^ (Fintype.card ι) := by
  rw [latBox, Fintype.card_piFinset]
  simp only [latBox_card_Icc]
  rw [Finset.prod_const, Finset.card_univ]

/-- The frequency box `{k : ι → ℤ | ∀ i, |k i| ≤ 2^{m+1} - 1}`, the ambient finite set of the
`m`-th dyadic annulus. -/
private def latFreqBox {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) : Finset (ι → ℤ) :=
  latBox (ι := ι) (2 ^ (m + 1) - 1)

private lemma latFreqBox_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (k : ι → ℤ) :
    k ∈ latFreqBox m ↔ ∀ i, |k i| ≤ ((2 ^ (m + 1) - 1 : ℕ) : ℤ) := by
  simp only [latFreqBox, latBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

private lemma latFreqBox_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    (latFreqBox (ι := ι) m).card ≤ 6 ^ (Fintype.card ι) * 2 ^ (m * Fintype.card ι) := by
  rw [latFreqBox, latBox_card]
  have hA : 2 * (2 ^ (m + 1) - 1) + 1 ≤ 6 * 2 ^ m := by
    have h1 : 1 ≤ (2 : ℕ) ^ (m + 1) := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    have h3 : 2 * (2 ^ (m + 1) - 1) + 1 = 2 * 2 ^ (m + 1) - 1 := by omega
    have h4 : 2 * 2 ^ (m + 1) = 4 * 2 ^ m := by rw [h2]; ring
    rw [h3, h4]
    omega
  calc (2 * (2 ^ (m + 1) - 1) + 1) ^ Fintype.card ι
      ≤ (6 * 2 ^ m) ^ Fintype.card ι := Nat.pow_le_pow_left hA _
    _ = 6 ^ Fintype.card ι * (2 ^ m) ^ Fintype.card ι := by rw [mul_pow]
    _ = 6 ^ Fintype.card ι * 2 ^ (m * Fintype.card ι) := by rw [← pow_mul]

private lemma annulus_subset_latFreqBox {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) {k : ι → ℤ}
    (hk : k ∈ Work.Diff.STE.flat.annulus m) : k ∈ latFreqBox m := by
  rw [latFreqBox_mem]
  intro i
  have hsq_le : ((k i : ℤ) : ℝ) ^ 2 ≤ Work.Diff.STE.wt k := by
    have hsum : ((k i : ℤ) : ℝ) ^ 2 ≤ ∑ j : ι, ((k j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℤ) : ℝ)) (Finset.mem_univ i)
    simp only [Work.Diff.STE.wt]
    linarith
  have hsq_lt : ((k i : ℤ) : ℝ) ^ 2 < (2 : ℝ) ^ (2 * (m + 1)) := by
    linarith [hsq_le, hk.2]
  have hpow : (2 : ℝ) ^ (2 * (m + 1)) = ((2 : ℝ) ^ (m + 1)) ^ 2 := by
    rw [show 2 * (m + 1) = (m + 1) * 2 by omega, pow_mul]
  have habs : |((k i : ℤ) : ℝ)| < (2 : ℝ) ^ (m + 1) := by
    rw [hpow, sq_lt_sq] at hsq_lt
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (m + 1))] at hsq_lt
  have hint : |k i| < (2 : ℤ) ^ (m + 1) := by
    rw [← Int.cast_abs] at habs
    exact_mod_cast habs
  have hK : ((2 ^ (m + 1) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (m + 1) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow : (1 : ℕ) ≤ 2 ^ (m + 1))]
    push_cast
    ring
  rw [hK]
  omega

/-- The `ℓ¹` norm of a dyadic block is controlled by its `ℓ²` norm with the dyadic counting
constant: the block is supported on the annulus `m`, whose elements satisfy `|k i| ≤ 2^{m+1}-1`,
so it has at most `(2^{m+2}-1)^{card ι} ≤ (6 * 2^m)^{card ι}` points, and Cauchy–Schwarz on that
finite box gives the claim. -/
private lemma block_l1_sq_le_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (γ : (ι → ℤ) → ℂ) :
    (∑' k : ι → ℤ, ‖Work.Diff.STE.flat.blockCoeff m γ k‖) ^ 2
      ≤ (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι))
        * ∑' k : ι → ℤ, ‖Work.Diff.STE.flat.blockCoeff m γ k‖ ^ 2 := by
  classical
  have hsupp : ∀ k : ι → ℤ, k ∉ latFreqBox m → blockCoeff m γ k = 0 := by
    intro k hk
    by_cases han : k ∈ annulus m
    · exact absurd (annulus_subset_latFreqBox m han) hk
    · exact blockCoeff_apply_not_mem m γ han
  have h1 : (∑' k : ι → ℤ, ‖blockCoeff m γ k‖) = ∑ k ∈ latFreqBox m, ‖blockCoeff m γ k‖ :=
    tsum_eq_sum (s := latFreqBox m) (fun k hk => by rw [hsupp k hk, norm_zero])
  have h2 : (∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2)
      = ∑ k ∈ latFreqBox m, ‖blockCoeff m γ k‖ ^ 2 :=
    tsum_eq_sum (s := latFreqBox m) (fun k hk => by rw [hsupp k hk, norm_zero]; simp)
  have hCS : (∑ k ∈ latFreqBox (ι := ι) m, ‖blockCoeff m γ k‖) ^ 2
      ≤ ((latFreqBox (ι := ι) m).card : ℝ)
        * ∑ k ∈ latFreqBox (ι := ι) m, ‖blockCoeff m γ k‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (latFreqBox (ι := ι) m) (fun _ : ι → ℤ => (1 : ℝ))
      (fun k => ‖blockCoeff m γ k‖)
    simpa using h
  have hnn : 0 ≤ ∑ k ∈ latFreqBox (ι := ι) m, ‖blockCoeff m γ k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hcard : ((latFreqBox (ι := ι) m).card : ℝ)
      ≤ (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)) := by
    have hnat : ((latFreqBox (ι := ι) m).card : ℝ)
        ≤ (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ (m * Fintype.card ι) := by
      exact_mod_cast latFreqBox_card_le (ι := ι) m
    calc ((latFreqBox (ι := ι) m).card : ℝ)
        ≤ (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ (m * Fintype.card ι) := hnat
      _ = (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)) := by
          congr 1
          rw [← Nat.cast_mul, Real.rpow_natCast]
  calc (∑' k : ι → ℤ, ‖blockCoeff m γ k‖) ^ 2
      = (∑ k ∈ latFreqBox (ι := ι) m, ‖blockCoeff m γ k‖) ^ 2 := by rw [h1]
    _ ≤ ((latFreqBox (ι := ι) m).card : ℝ)
          * ∑ k ∈ latFreqBox (ι := ι) m, ‖blockCoeff m γ k‖ ^ 2 := hCS
    _ ≤ ((6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)))
          * ∑ k ∈ latFreqBox (ι := ι) m, ‖blockCoeff m γ k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hnn
    _ = (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι))
          * ∑' k : ι → ℤ, ‖blockCoeff m γ k‖ ^ 2 := by rw [← h2]

/-- The final bookkeeping of the two `2`-powers: the dyadic counting constant
`6^{card ι} · 2^{m·card ι}` raised to the Sobolev exponent `θ = 1/2 - 1/(2p)`, multiplied by the
`ℓ²`→weight factor `2^{-mj}`, is `6^{card ι·θ} · 2^{-m(j - card ι·θ)}`. -/
private lemma rpow_factor {ι : Type*} [Fintype ι] (p j : ℝ) (m : ℕ) :
    ((6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)))
          ^ (1 / 2 - 1 / (2 * p)) * (2 : ℝ) ^ (-(m : ℝ) * j)
      = (6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
        * (2 : ℝ) ^ (-(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))) := by
  have hA : ((6 : ℝ) ^ (Fintype.card ι)) ^ (1 / 2 - 1 / (2 * p))
      = (6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))) := by
    rw [← Real.rpow_natCast (6 : ℝ) (Fintype.card ι),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  have hB : ((2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι))) ^ (1 / 2 - 1 / (2 * p))
      = (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι) * (1 / 2 - 1 / (2 * p))) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hC : (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι) * (1 / 2 - 1 / (2 * p)))
        * (2 : ℝ) ^ (-(m : ℝ) * j)
      = (2 : ℝ) ^ (-(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (m : ℝ) * (Fintype.card ι) * (1 / 2 - 1 / (2 * p)) + -(m : ℝ) * j
        = -(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))) by ring]
  rw [Real.mul_rpow (by positivity) (by positivity), hA, hB, mul_assoc, hC]

/-- **The sharp `L^{2p}` bound for a single dyadic block** (the true statement: the last factor
carries the *real* exponent `(1 / 2 : ℝ)`).

For `p ≥ 1` real, a real level `j ≥ n(1/2 - 1/(2p))` (`n = card ι`), a dyadic level `m : ℕ` and a
coefficient family `γ` with `Σ_k ‖γ k‖ < ∞` and `Σ_k ⟨k⟩^{2j} ‖γ k‖² < ∞`,

`‖seriesFun (blockCoeff m γ)‖_{L^{2p}} ≤ 6^{n(1/2-1/(2p))} 2^{-m(j-n(1/2-1/(2p)))}
  (blockMass j m γ)^{1/2}`.

This is `Work.Diff.STE.flat.Sobolev.block_rnorm_le` with the exponent of the last factor written
`(1 / 2 : ℝ)`; as requested (a bare `(1 / 2)`) that exponent is `ℕ`-division and the statement is
false (see `Work.Diff.STE.flat.Sobolev.block_rnorm_le_requested_false`). -/
theorem block_rnorm_le_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 1 ≤ p) (j : ℝ)
    (hj : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) ≤ j)
    (m : ℕ) (γ : (ι → ℤ) → ℂ) (hγ : Summable fun k : ι → ℤ => ‖γ k‖)
    (hM : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) :
    Work.Diff.STE.flat.rnorm (2 * p)
        (Work.Diff.STE.seriesFun (Work.Diff.STE.flat.blockCoeff m γ))
      ≤ (6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
        * (2 : ℝ) ^ (-(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))
        * (Work.Diff.STE.flat.blockMass j m γ) ^ (1 / 2 : ℝ) := by
  -- `θ = 1/2 - 1/(2p) ≥ 0` and hence `j ≥ 0` (this is the only use of `hj`)
  have hθ : (0 : ℝ) ≤ 1 / 2 - 1 / (2 * p) := by
    have h2p : (2 : ℝ) ≤ 2 * p := by linarith
    have h1 : 1 / (2 * p) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2p
    linarith
  have hj0 : (0 : ℝ) ≤ j := by
    have hc : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hc hθ, hj]
  let b : (ι → ℤ) → ℂ := Work.Diff.STE.flat.blockCoeff m γ
  -- support facts for the block
  have hb1 : Summable fun k : ι → ℤ => ‖b k‖ := summable_norm_blockCoeff m γ hγ
  have hcont : Continuous (Work.Diff.STE.seriesFun b) := continuous_seriesFun b hb1
  have hsup : ∀ x : ι → ℝ, ‖Work.Diff.STE.seriesFun b x‖ ≤ ∑' k : ι → ℤ, ‖b k‖ :=
    fun x => norm_seriesFun_block_le m γ hγ x
  have hP : (0 : ℝ) ≤ ∑' k : ι → ℤ, ‖b k‖ := tsum_nonneg fun k => norm_nonneg _
  have hT : (0 : ℝ) ≤ ∑' k : ι → ℤ, ‖b k‖ ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hint : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.seriesFun b x‖ ^ 2
      = ∑' k : ι → ℤ, ‖b k‖ ^ 2 := Work.Diff.STE.integral_normSq_seriesFun b hb1
  have hCS : (∑' k : ι → ℤ, ‖b k‖) ^ 2
      ≤ (6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι))
        * ∑' k : ι → ℤ, ‖b k‖ ^ 2 := block_l1_sq_le_aux m γ
  have hq : (2 : ℝ) ≤ 2 * p := by linarith
  have hmain := rnorm_le_of_sup_l2_rpow_aux (2 * p) hq (Work.Diff.STE.seriesFun b) hcont
    (∑' k : ι → ℤ, ‖b k‖)
    ((6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)))
    (∑' k : ι → ℤ, ‖b k‖ ^ 2) hP (by positivity) hT hsup hCS hint
  have hmass : (∑' k : ι → ℤ, ‖b k‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (2 : ℝ) ^ (-(m : ℝ) * j) * (Work.Diff.STE.flat.blockMass j m γ) ^ ((1 : ℝ) / 2) :=
    block_l2_sqrt_le j hj0 m γ hM
  have hCn : (0 : ℝ) ≤ ((6 : ℝ) ^ (Fintype.card ι)
      * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι))) ^ (1 / 2 - 1 / (2 * p)) :=
    Real.rpow_nonneg (by positivity) _
  calc Work.Diff.STE.flat.rnorm (2 * p) (Work.Diff.STE.seriesFun b)
      ≤ ((6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)))
            ^ (1 / 2 - 1 / (2 * p)) * (∑' k : ι → ℤ, ‖b k‖ ^ 2) ^ ((1 : ℝ) / 2) := hmain
    _ ≤ ((6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)))
            ^ (1 / 2 - 1 / (2 * p))
          * ((2 : ℝ) ^ (-(m : ℝ) * j)
              * (Work.Diff.STE.flat.blockMass j m γ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hmass hCn
    _ = (((6 : ℝ) ^ (Fintype.card ι) * (2 : ℝ) ^ ((m : ℝ) * (Fintype.card ι)))
            ^ (1 / 2 - 1 / (2 * p)) * (2 : ℝ) ^ (-(m : ℝ) * j))
          * (Work.Diff.STE.flat.blockMass j m γ) ^ ((1 : ℝ) / 2) := by ring
    _ = ((6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
          * (2 : ℝ) ^ (-(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))))
          * (Work.Diff.STE.flat.blockMass j m γ) ^ ((1 : ℝ) / 2) := by
        rw [rpow_factor p j m]

end Work.Diff.STE.flat.Sobolev
