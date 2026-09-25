import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.Maximal.mstWideLat_apply_int
import Submission.Work.Maximal.mstModelFn_modSeq_gen
import Submission.Work.Maximal.mstModSeq_period_emod
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs

/-!
# Auxiliary lemmas for the maximal bound of the wide level model (`mstWideModel_lr_maximal`)

Two pieces of the large-scale half of the level-`s` `ℓʳ` estimate:

* `six_le_mstQ'` / `mstWideC_mul_Q_le`: the *Nyquist* arithmetic.  The wide scale
  `c_s = mstWideC P s = Q_s^{3d}` (`Q_s = mstQ' s ≥ 6`, `d = P.natDegree ≥ 2`) satisfies
  `Q_s / (2 c_s) ≤ 1/4`, which is the condition `δ * Q ≤ 1/4` of the lattice sampling principle
  `hLattice` with `δ = 1/(2 c_s)` and modulus `Q = Q_s`.

* `mstWideLat_unfold`: the *values* of the band-limited interpolant of the wide multiplier at the
  integers, in the form needed for the residue-class decomposition.  For a point `n ≡ m (mod Q_s)`
  the value `mstWideLat (mstModSeq G E g m) g.support (-n)` of the interpolant (whose data is the
  *folded* input `F_m = mstModSeq G E g m`) equals the value at `n` of the *weighted arc-sum*
  multiplier `Π^G_s = Σ_{β∈E} star (G β) ϱ_s(·−β)` applied to the original input `g`.  The two
  inputs agree on the residue class by `mstModSeq_period_emod` (the arcs of `E` are `Q_s`-torsion),
  and the two multipliers are related by the `Φ ≡ 1` instance of the folding identity
  `mstModelFn_modSeq_gen`.  It is this identity which, applied to the lattice sum arising from the
  sampling principle, converts the values of the interpolant into (the values of) `mstWidePiG`, whose
  `ℓʳ`-bound with the `log (s+2)` loss is MST's (79) (`mstWidePiG_lr_bound`).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

set_option maxHeartbeats 1600000 in
/-- `opMul` depends on the sequence only through its values. -/
theorem opMul_congr_seq {Φ : Lp ℂ ⊤ haarT} {g₁ g₂ : ℤ → ℂ} (h : g₁ = g₂)
    (hg₁ : Memℓp g₁ 2) (hg₂ : Memℓp g₂ 2) :
    opMul Φ g₁ hg₁ = opMul Φ g₂ hg₂ := by
  have hsub : (⟨g₁, hg₁⟩ : {g : ℤ → ℂ // Memℓp g 2}) = ⟨g₂, hg₂⟩ := Subtype.ext h
  have hft : ftLp g₁ hg₁ = ftLp g₂ hg₂ :=
    congrArg (fun p : {g : ℤ → ℂ // Memℓp g 2} =>
      (fourierBasis (T := 1)).repr.symm p) hsub
  have hop : opMulLp Φ g₁ hg₁ = opMulLp Φ g₂ hg₂ := by
    rw [opMulLp, opMulLp, hft]
  exact congrArg (fun F : Lp ℂ 2 haarT => fun n : ℤ =>
    ((fourierBasis (T := 1)).repr F : ℤ → ℂ) n) hop

/-- `mstQ' s ≥ 6` (the level denominator bound `(⌈e^{(s+1)^{1/10}}⌉)!` is at least `3!`). -/
theorem six_le_mstQ' (s : ℕ) : 6 ≤ mstQ' s := by
  rw [mstQ']
  have h1 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) s]) (by norm_num)
  have h2 : (2 : ℝ) < Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) :=
    lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr h1)
  have h3 : 3 ≤ ⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊ := by
    have h4 : (2 : ℝ) < (⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊ : ℝ) :=
      lt_of_lt_of_le h2 (Nat.le_ceil _)
    have h5 : 2 < ⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊ := by exact_mod_cast h4
    omega
  have hfac : Nat.factorial 3 = 6 := by norm_num [Nat.factorial]
  calc (6 : ℕ) = Nat.factorial 3 := hfac.symm
    _ ≤ Nat.factorial ⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊ := Nat.factorial_le h3

/-- **The Nyquist arithmetic of the wide scale.**  With `Q_s = mstQ' s ≥ 6` and
`c_s = mstWideC P s = Q_s^{3d}`, `d ≥ 2`, one has `Q_s / (2 c_s) ≤ 1/4`. -/
theorem mstWideC_mul_Q_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (s : ℕ) :
    (1 / (2 * mstWideC P s)) * ((mstQ' s : ℕ) : ℝ) ≤ 1 / 4 := by
  have hQ6 : (6 : ℝ) ≤ ((mstQ' s : ℕ) : ℝ) := by exact_mod_cast six_le_mstQ' s
  have hQ0 : (0 : ℝ) < ((mstQ' s : ℕ) : ℝ) := by linarith
  have hc : mstWideC P s = ((mstQ' s : ℕ) : ℝ) ^ (3 * P.natDegree) := rfl
  have hsplit : ((mstQ' s : ℕ) : ℝ) ^ (3 * P.natDegree)
      = ((mstQ' s : ℕ) : ℝ) ^ (3 * P.natDegree - 1) * ((mstQ' s : ℕ) : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hexp : 5 ≤ 3 * P.natDegree - 1 := by omega
  have h2le : (2 : ℝ) ≤ ((mstQ' s : ℕ) : ℝ) ^ (3 * P.natDegree - 1) := by
    calc (2 : ℝ) ≤ 6 ^ 5 := by norm_num
      _ ≤ ((mstQ' s : ℕ) : ℝ) ^ 5 := by
          exact pow_le_pow_left₀ (by norm_num) hQ6 5
      _ ≤ ((mstQ' s : ℕ) : ℝ) ^ (3 * P.natDegree - 1) :=
          pow_le_pow_right₀ (by linarith) hexp
  have hcge : 2 * ((mstQ' s : ℕ) : ℝ) ≤ mstWideC P s := by
    rw [hc, hsplit]
    nlinarith [mul_le_mul_of_nonneg_right h2le hQ0.le]
  have hcpos : 0 < 2 * mstWideC P s := by
    have h := one_le_mstWideC P s
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
  linarith

/-- **The values of the interpolant of the wide multiplier are the weighted arc-sum operator.**
For `n ≡ m (mod Q)` the band-limited interpolant of the wide bump applied to the *folded* input
`mstModSeq G E g m` takes at `-n` the value at `n` of the weighted arc-sum multiplier
`mstWidePiG` applied to `g`. -/
theorem mstWideLat_unfold (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (g : ℤ →₀ ℂ) {Q : ℕ} (hQpos : 0 < Q)
    (hQE : ∀ β ∈ mstAnnulus l s, fourier (Q : ℤ) β = 1)
    (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hφ : MemLp (mstWideBump P χ η s) ⊤ haarT)
    (hπ : MemLp (mstWidePiG P l χ η s) ⊤ haarT)
    (m : ℤ) :
    ∀ n : ℤ, n % (Q : ℤ) = m % (Q : ℤ) →
      mstWideLat P χ η s
          (mstModSeq (fun β : Circ => star (mstG P β)) (mstAnnulus l s) (⇑g) m)
          g.support (-(n : ℝ))
        = opMul (hπ.toLp (mstWidePiG P l χ η s)) (⇑g) (memℓp_finsupp g) n := by
  intro n hn
  set G : Circ → ℂ := fun β => star (mstG P β) with hG
  set E : Finset Circ := mstAnnulus l s with hE
  set F : ℤ → ℂ := mstModSeq G E (⇑g) m with hF
  have hg2 : Memℓp (⇑g : ℤ → ℂ) 2 := memℓp_finsupp g
  have hFmem : Memℓp F 2 := by rw [hF]; exact memℒp_mstModSeq hg2 m
  have hFsupp : ∀ k : ℤ, k ∉ g.support → F k = 0 := by
    intro k hk
    rw [hF]
    simp only [mstModSeq_apply]
    rw [show (⇑g : ℤ → ℂ) k = 0 from by simpa using Finsupp.notMem_support_iff.mp hk]
    ring
  -- Step 1: the value of the interpolant is the single-bump multiplier applied to `F`
  have hstep1 : mstWideLat P χ η s F g.support (-(n : ℝ))
      = opMul (hφ.toLp (mstWideBump P χ η s)) F hFmem n := by
    have h := mstWideLat_apply_int P χ η s F g.support hηc hηsup hFsupp hFmem hφ (-n)
    simpa only [Int.cast_neg, neg_neg] using h
  -- Step 2: the folding identity for the profile `Φ ≡ 1`
  have hB : MemLp (fun ξ : Circ => (fun _ : Circ => (1 : ℂ)) ξ * mstWideBump P χ η s ξ)
      ⊤ haarT :=
    MemLp.ae_eq (Filter.Eventually.of_forall (fun ξ => by simp)) hφ
  have hfold := mstModelFn_modSeq_gen G (fun _ : Circ => (1 : ℂ)) (mstWideBump P χ η s) E
    (⇑g) hg2 hπ hB n
  -- Step 3: `hB.toLp (1 · ϱ_s)` and `hφ.toLp ϱ_s` are the same multiplier
  have hsym : ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
      opMul (hB.toLp (fun ξ : Circ => (fun _ : Circ => (1 : ℂ)) ξ * mstWideBump P χ η s ξ))
          f hf n
        = opMul (hφ.toLp (mstWideBump P χ η s)) f hf n := by
    intro f hf
    refine congrFun (opMul_congr_ae ?_ f hf) n
    filter_upwards [MemLp.coeFn_toLp hB, MemLp.coeFn_toLp hφ] with ξ h1 h2
    rw [h1, h2]
    simp
  -- Step 4: the folded input on the residue class of `n` is `F`
  have hper : F = mstModSeq G E (⇑g) n := by
    have h1 := mstModSeq_period_emod (G := G) (E := E) hQpos hQE (⇑g) n
    have h2 := mstModSeq_period_emod (G := G) (E := E) hQpos hQE (⇑g) m
    rw [hF, h2, ← hn, h1]
  calc mstWideLat P χ η s F g.support (-(n : ℝ))
      = opMul (hφ.toLp (mstWideBump P χ η s)) F hFmem n := hstep1
    _ = opMul (hB.toLp (fun ξ : Circ => (fun _ : Circ => (1 : ℂ)) ξ
            * mstWideBump P χ η s ξ)) F hFmem n := (hsym F hFmem).symm
    _ = opMul (hB.toLp (fun ξ : Circ => (fun _ : Circ => (1 : ℂ)) ξ
            * mstWideBump P χ η s ξ))
          (mstModSeq G E (⇑g) n) (memℒp_mstModSeq hg2 n) n :=
          congrFun (opMul_congr_seq hper hFmem (memℒp_mstModSeq hg2 n)) n
    _ = opMul (hπ.toLp (mstWidePiG P l χ η s)) (⇑g) (memℓp_finsupp g) n := hfold.symm

/-- `eLpNorm` to the `r`-th power is the `r`-th moment against the counting measure. -/
lemma eLpNorm_rpow_eq_lintegral_count {r : ℝ} (hr : 0 < r) (f : ℤ → ℂ) :
    (MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count) ^ r
      = ∫⁻ n : ℤ, ‖f n‖ₑ ^ r ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top (measurable_of_countable _).aestronglyMeasurable, ENNReal.toReal_ofReal hr.le]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]

/-- **Numerical absorption.**  For `r ≥ 1` the product `a^r b^r b c^r d^r` is dominated by the
`r`-th power of `(a+b+c+d+e+1)^6`. -/
lemma rpow_absorb {r : ℝ} (hr : 1 ≤ r) {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    a ^ r * b ^ r * b * c ^ r * d ^ r
      ≤ ((a + b + c + d + e + 1) ^ 6) ^ r := by
  set Z : ℝ := a + b + c + d + e + 1 with hZ
  have hZ1 : 1 ≤ Z := by rw [hZ]; linarith
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ1
  have hZpos : (0:ℝ) < Z := lt_of_lt_of_le zero_lt_one hZ1
  have haZ : a ≤ Z := by rw [hZ]; linarith
  have hbZ : b ≤ Z := by rw [hZ]; linarith
  have hcZ : c ≤ Z := by rw [hZ]; linarith
  have hdZ : d ≤ Z := by rw [hZ]; linarith
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hstep1 : a ^ r * b ^ r * b * c ^ r * d ^ r ≤ Z ^ r * Z ^ r * Z * Z ^ r * Z ^ r := by
    gcongr
  have hA : Z ^ r * Z ^ r * Z ^ r * Z ^ r = Z ^ (4 * r) := by
    rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
    congr 1
    ring
  have hstep2 : Z ^ r * Z ^ r * Z * Z ^ r * Z ^ r = Z ^ (4 * r + 1) := by
    rw [Real.rpow_add hZpos, Real.rpow_one,
      show Z ^ r * Z ^ r * Z * Z ^ r * Z ^ r = Z ^ r * Z ^ r * Z ^ r * Z ^ r * Z by ring, hA]
  have hstep3 : Z ^ (4 * r + 1) ≤ Z ^ (6 * r) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hstep4 : Z ^ (6 * r) = (Z ^ 6) ^ r := by
    rw [Real.rpow_mul hZ0]; norm_num
  calc a ^ r * b ^ r * b * c ^ r * d ^ r
      ≤ Z ^ r * Z ^ r * Z * Z ^ r * Z ^ r := hstep1
    _ = Z ^ (4 * r + 1) := hstep2
    _ ≤ Z ^ (6 * r) := hstep3
    _ = (Z ^ 6) ^ r := hstep4

end

end Work.Maximal
