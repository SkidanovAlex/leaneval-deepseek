import Mathlib
import Submission.Work.KMTAreas.A7HiRep.Defs
import Submission.Work.KMTAreas.A7G.chainPartLowpass
import Submission.Port.Aesm

namespace Work.KMTAreas.A7HiRep

/-! ## The smoothing defect of the IW cutoff is dominated by the next annulus

Write `eta = kmtEta`, `eta_k = etaCut eta k` (so `eta_k x = eta (x / 2^k)`, the symbol of the
Ionescu--Wainger projection at height `k`).  The family `T_m` is *nested* but not idempotent: its
"smoothing defect" has symbol `Phi_m (1 - Phi_m)`, while the increment one scale finer has symbol
`Phi_{m+1} - Phi_m`.  The facts proved here are that the defect is *pointwise dominated by the
increment*,

  `eta t * (1 - eta t) <= eta t - eta (2 t)`   (i.e. `eta (2 t) <= eta t ^ 2`),

and its `C`-norm consequence.  Together with the PROVED nesting `T_a T_b = T_{max(a,b)}` for
`a != b` (`A7G.kmtProj_comp`) this is the quantitative replacement for the (false) exact
orthogonality of the increments: the adjacent cross terms are `Delta_m Delta_{m+1} =
T_{m+1} - T_{m+1}^2`, whose symbol is now controlled by the adjacent annulus symbol.  See
`NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` sections 4 and 6. -/

/-- The real bump `eta = kmtEta` satisfies `eta (2 t) <= eta t ^ 2`. -/
lemma kmtBump_two_mul_le_sq (t : ℝ) :
    ((Work.KMTContract.kmtBump : ℝ → ℝ) (2 * t)) ≤ ((Work.KMTContract.kmtBump : ℝ → ℝ) t) ^ 2 := by
  by_cases h : (1 : ℝ) ≤ |2 * t|
  · have hz : Work.KMTContract.kmtEta (2 * t) = 0 := Work.KMTContract.kmtEta_zero h
    have hz' : ((Work.KMTContract.kmtBump : ℝ → ℝ) (2 * t) : ℂ) = 0 := hz
    have hz'' : (Work.KMTContract.kmtBump : ℝ → ℝ) (2 * t) = 0 := by exact_mod_cast hz'
    rw [hz'']; positivity
  · have hle : |2 * t| < 1 := lt_of_not_ge h
    have ht : |t| ≤ 1 / 2 := by
      have h2 : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
      rw [h2] at hle; linarith
    have hone : Work.KMTContract.kmtEta t = 1 := Work.KMTContract.kmtEta_one ht
    have hone' : ((Work.KMTContract.kmtBump : ℝ → ℝ) t : ℂ) = 1 := hone
    have hone'' : (Work.KMTContract.kmtBump : ℝ → ℝ) t = 1 := by exact_mod_cast hone'
    rw [hone'', one_pow]
    exact Work.KMTContract.kmtEta_le_one (2 * t)


/-- **The smoothing defect factorises through the annulus increment.**  With
`Phi_k = periodize (etaCut eta k)` (the symbol of the IW projection at height `k`) and `k' < k`
(so `k` is the *coarser* cutoff, `2^k <= 1/4`, `Phi_k * Phi_{k'} = Phi_{k'}` — the PROVED nesting
`Work.KMTAreas.A7G.periodize_etaCut_mul_eq`),

  `Phi_k * (1 - Phi_k) = (Phi_k - Phi_{k'}) * (1 - Phi_k)`

pointwise.  The left side is the symbol of the *smoothing defect* `T_k - T_k^2` (the failure of
idempotency, and the reason the increments are not exactly orthogonal), the first factor on the
right is the *annulus increment*, and the second is a symbol with values in `[0,1]`.  So the defect
is the increment composed with a *bounded* operator: this is the exact quantitative replacement for
the missing idempotency, and the input that the martingale comparison of
`NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` sections 4 and 6 needs. -/
theorem periodize_etaCut_defect_factor {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 4) {k' : ℤ} (hk' : k' < k) :
    Work.Analysis.IonescuWainger.periodize (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)
        * (1 - Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))
      = (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)
          - Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k'))
        * (1 - Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) := by
  have hmul := Work.KMTAreas.A7G.periodize_etaCut_mul_eq hk' hk
  funext ξ
  have hAB : Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) ξ
      * Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k') ξ
      = Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k') ξ := by
    simpa only [Pi.mul_apply] using congrFun hmul ξ
  have hBA : Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k') ξ
      * Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) ξ
      = Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k') ξ := by
    rw [mul_comm]; exact hAB
  have hzero : Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k') ξ
      * (1 - Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) ξ) = 0 := by
    rw [mul_sub, mul_one, hBA, sub_self]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
  linear_combination hzero

/-- The `iwSymbolSet`-level form of the defect factorization: the comb symbol of the smoothing
defect equals the comb symbol of the annulus increment times `(1 - Phi_k)`.  This is the input the
*operator*-level statement `T_k - T_k^2 = (T_k - T_{k'}) o (I - T_k)` consumes (via the
multiplicativity of `iwSymbolSet`, `Work.Analysis.IonescuWainger.iwSymbolSet_mul`). -/
theorem iwSymbolSet_defect_factor {ρ : ℝ} {l : ℕ} {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 4)
    {k' : ℤ} (hk' : k' < k) :
    Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)
          * (1 - Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)))
      = Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        ((Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)
            - Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k'))
          * (1 - Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) :=
  congrArg (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    (periodize_etaCut_defect_factor hk hk')

/-- **The smoothing defect is dominated by the increment**: for the real cutoff `eta = kmtEta`,
`eta t * (1 - eta t) <= eta t - eta (2 t)` for every `t : R`. -/
lemma kmtBump_defect_le (t : ℝ) :
    (Work.KMTContract.kmtBump : ℝ → ℝ) t * (1 - (Work.KMTContract.kmtBump : ℝ → ℝ) t)
      ≤ (Work.KMTContract.kmtBump : ℝ → ℝ) t - (Work.KMTContract.kmtBump : ℝ → ℝ) (2 * t) := by
  have h1 : (0 : ℝ) ≤ (Work.KMTContract.kmtBump : ℝ → ℝ) t := Work.KMTContract.kmtEta_nonneg t
  have h2 : (Work.KMTContract.kmtBump : ℝ → ℝ) t ≤ 1 := Work.KMTContract.kmtEta_le_one t
  have h3 := kmtBump_two_mul_le_sq t
  nlinarith [h1, h2, h3, sq_nonneg ((Work.KMTContract.kmtBump : ℝ → ℝ) t)]

/-- **The `C`-norm form of the defect domination** for the complex cutoff `eta = kmtEta`. -/
lemma kmtEta_defect_norm_le (t : ℝ) :
    ‖Work.KMTContract.kmtEta t * (1 - Work.KMTContract.kmtEta t)‖
      ≤ ‖Work.KMTContract.kmtEta t - Work.KMTContract.kmtEta (2 * t)‖ := by
  have h := kmtBump_defect_le t
  have h2 : Work.KMTContract.kmtEta t * (1 - Work.KMTContract.kmtEta t)
      = (((Work.KMTContract.kmtBump : ℝ → ℝ) t
          * (1 - (Work.KMTContract.kmtBump : ℝ → ℝ) t) : ℝ) : ℂ) := by
    rw [Work.KMTContract.kmtEta]; push_cast; ring
  have h3 : Work.KMTContract.kmtEta t - Work.KMTContract.kmtEta (2 * t)
      = ((((Work.KMTContract.kmtBump : ℝ → ℝ) t
          - (Work.KMTContract.kmtBump : ℝ → ℝ) (2 * t)) : ℝ) : ℂ) := by
    rw [Work.KMTContract.kmtEta, Work.KMTContract.kmtEta]; push_cast; ring
  rw [h2, h3, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by
      have h1 : (0 : ℝ) ≤ (Work.KMTContract.kmtBump : ℝ → ℝ) t := Work.KMTContract.kmtEta_nonneg t
      have h2' : (Work.KMTContract.kmtBump : ℝ → ℝ) t ≤ 1 := Work.KMTContract.kmtEta_le_one t
      nlinarith),
    abs_of_nonneg (by
      have h3 := kmtBump_two_mul_le_sq t
      have h1 : (0 : ℝ) ≤ (Work.KMTContract.kmtBump : ℝ → ℝ) t := Work.KMTContract.kmtEta_nonneg t
      have h2' : (Work.KMTContract.kmtBump : ℝ → ℝ) t ≤ 1 := Work.KMTContract.kmtEta_le_one t
      nlinarith [h1, h2', h3, sq_nonneg ((Work.KMTContract.kmtBump : ℝ → ℝ) t)])]
  exact h



/-- **Two points of a sequence give a chain**, so the jump `a K - a 0` is at most the chain part.
(Public copy of the private helper of `A7HiRep/lowpassVarGRepCrux.lean`.) -/
lemma two_point_le_chainPart {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) (K : ℕ) :
    ‖a K - a 0‖ₑ ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (r : ℝ) := by
      have h1 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact this.ne'
  refine le_iSup_of_le 1 ?_
  refine le_iSup_of_le (fun i : ℕ => if i = 0 then 0 else K) ?_
  refine le_iSup_of_le ?_ ?_
  · refine monotone_nat_of_le_succ fun i => ?_
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · have h1 : i ≠ 0 := h.ne'
      have h2 : i + 1 ≠ 0 := by omega
      simp only [h1, h2, if_false]
      exact le_rfl
  · have hval : (fun i : Fin 1 =>
          a ((fun i : ℕ => if i = 0 then 0 else K) (i + 1))
            - a ((fun i : ℕ => if i = 0 then 0 else K) i))
        = fun _ : Fin 1 => a K - a 0 := by
      funext i
      have hi : (i : ℕ) = 0 := by omega
      rw [hi]
      simp
    rw [hval]
    have h1' := Work.KMTAreas.A7.ofReal_norm_toLp r hr 1 (fun _ : Fin 1 => a K - a 0)
    rw [Fin.sum_univ_one] at h1'
    rw [h1', one_div]
    exact le_of_eq (ENNReal.rpow_rpow_inv hr0 _).symm

/-- **The partial sums of the annuli of the walk are dominated by the chain part** (the two-point
chain `(0,K)` plus the telescope `Finset.sum_range_sub`).  In particular the *values-supremum* /
Men'shov piece of the chapter is a pointwise consequence of `chainPart`: if `chainPartSqFunPos`
holds then so does `A7Hi2.lacunaryMaxPiece` (combine with the PROVED forward square-function bound
`A7Lpd.bandSquareUnif`).  See `NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` section 8. -/
lemma partialSum_le_chainPart (ρ : ℝ) (l₁ m₀ : ℕ) (r : NNReal) (hr : 2 ≤ r) (f : ℤ → ℂ)
    (x : ℤ) :
    (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K, (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      ≤ Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
  refine iSup_le fun K => ?_
  rw [Finset.sum_range_sub (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x) K]
  exact two_point_le_chainPart hr (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x) K




lemma tsum_mul_le_rpow_mul_rpow {p q : ℝ} (hpq : Real.HolderConjugate p q) (f g : ℤ → ENNReal) :
    ∑' j : ℤ, f j * g j
      ≤ (∑' j : ℤ, f j ^ p) ^ (1 / p) * (∑' j : ℤ, g j ^ q) ^ (1 / q) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq MeasureTheory.Measure.count hpq
    (f := fun j : ℤ => f j) (g := fun j : ℤ => g j)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  simpa only [Pi.mul_apply, MeasureTheory.lintegral_count] using h

lemma enorm_le_kernel_mul_Lp {p : ℝ} (hp : 1 < p) {d k : ℤ → ℂ} {A B : ENNReal}
    (hkA : ∑' j : ℤ, ‖k j‖ₑ ≤ A) (hkB : ∀ j, ‖k j‖ₑ ≤ B)
    (hconv : ∀ x, ‖d x‖ₑ ≤ ∑' j : ℤ, ‖k j‖ₑ * ‖d (x - j)‖ₑ) (x : ℤ) :
    ‖d x‖ₑ ≤ A ^ (1 - 1 / p) * B ^ (1 / p) * (∑' j : ℤ, ‖d (x - j)‖ₑ ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1pos : 0 < p - 1 := by linarith
  have hpp : p ≠ 0 := ne_of_gt hp0
  have hq1 : 1 / (p / (p - 1)) = 1 - 1 / p := by field_simp
  have hpq : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hHolder := tsum_mul_le_rpow_mul_rpow hpq
    (fun j : ℤ => ‖k j‖ₑ ^ (1 / p) * ‖d (x - j)‖ₑ)
    (fun j : ℤ => ‖k j‖ₑ ^ (1 / (p / (p - 1))))
  have ha : (fun j : ℤ => (‖k j‖ₑ ^ (1 / p) * ‖d (x - j)‖ₑ) ^ p)
      = fun j : ℤ => ‖k j‖ₑ * ‖d (x - j)‖ₑ ^ p := by
    funext j
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
      show 1 / p * p = 1 by field_simp <;> ring, ENNReal.rpow_one]
  have hb : (fun j : ℤ => (‖k j‖ₑ ^ (1 / (p / (p - 1)))) ^ (p / (p - 1)))
      = fun j : ℤ => ‖k j‖ₑ := by
    funext j
    rw [← ENNReal.rpow_mul,
      show 1 / (p / (p - 1)) * (p / (p - 1)) = 1 by field_simp <;> ring, ENNReal.rpow_one]
  have hc : (fun j : ℤ => (‖k j‖ₑ ^ (1 / p) * ‖d (x - j)‖ₑ) * ‖k j‖ₑ ^ (1 / (p / (p - 1))))
      = fun j : ℤ => ‖k j‖ₑ * ‖d (x - j)‖ₑ := by
    funext j
    have h1 : ‖k j‖ₑ ^ (1 / p) * ‖k j‖ₑ ^ (1 / (p / (p - 1))) = ‖k j‖ₑ := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / p) (1 / (p / (p - 1)))
          (by positivity) (by positivity),
        show 1 / p + 1 / (p / (p - 1)) = 1 by field_simp <;> ring, ENNReal.rpow_one]
    rw [mul_assoc, mul_comm (‖d (x - j)‖ₑ) (‖k j‖ₑ ^ (1 / (p / (p - 1)))), ← mul_assoc, h1]
  rw [hc, ha, hb] at hHolder
  rw [hq1] at hHolder
  have hB : (∑' j : ℤ, ‖k j‖ₑ * ‖d (x - j)‖ₑ ^ p) ≤ B * (∑' j : ℤ, ‖d (x - j)‖ₑ ^ p) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum (fun j => by gcongr; exact hkB j)
  have h1mp : 0 ≤ 1 - 1 / p := by
    have : 1 / p ≤ 1 := by rw [div_le_one hp0]; linarith
    linarith
  calc ‖d x‖ₑ ≤ ∑' j : ℤ, ‖k j‖ₑ * ‖d (x - j)‖ₑ := hconv x
    _ ≤ (∑' j : ℤ, ‖k j‖ₑ * ‖d (x - j)‖ₑ ^ p) ^ (1 / p) *
          (∑' j : ℤ, ‖k j‖ₑ) ^ (1 - 1 / p) :=
        hHolder.trans (by gcongr)
    _ ≤ (B * (∑' j : ℤ, ‖d (x - j)‖ₑ ^ p)) ^ (1 / p) * A ^ (1 - 1 / p) := by
        apply mul_le_mul
        · exact ENNReal.rpow_le_rpow hB (by positivity)
        · exact ENNReal.rpow_le_rpow hkA h1mp
        · positivity
        · positivity
    _ = B ^ (1 / p) * (∑' j : ℤ, ‖d (x - j)‖ₑ ^ p) ^ (1 / p) * A ^ (1 - 1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    _ = A ^ (1 - 1 / p) * B ^ (1 / p) * (∑' j : ℤ, ‖d (x - j)‖ₑ ^ p) ^ (1 / p) := by
        ring


/-- **The sparse bookkeeping of the hypothesis `2 ≤ Cρ₀`.**  For the target's hypothesis
`GoodMajorArcs ρ Cρ₀ l₁ (-(m₀:ℤ))` with `2 ≤ Cρ₀` (i.e. `m₀ ≥ 2 · 2^{ρ l₁}`) the *frequency measure*
`#(iwArithFreqs ρ l₁) · 2^{-m₀}` of the Ionescu--Wainger arc set is bounded by a constant depending
only on `ρ`.  This is the quantitative content of the "sparse regime": by `iw_height_card_le` one has
`#(iwArithFreqs ρ l₁) ≤ C(ρ) 2^{2^{ρ l₁}}` while `2^{-m₀} ≤ 2^{-2·2^{ρ l₁}}`, so

  `#(iwArithFreqs ρ l₁) · 2^{-m₀} ≤ C(ρ) 2^{-2^{ρ l₁}} ≤ C(ρ)`.

It is what makes the frequency measures `|supp(σ_{m+1} - σ_m)| ≤ C #(ℚ/ℤ)_{≤l₁} 2^{-(m₀+m)}` of the
increments of the low-pass family summable *geometrically and uniformly in `l₁, m₀`*, which is the
input of the total-variation (spreading) argument for the target. -/
theorem card_two_pow_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ) (Cρ₀ : ℝ), 2 ≤ Cρ₀ →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) →
      2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
        * (2 : ℝ) ^ (-(m₀ : ℤ)) ≤ C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.Analysis.IonescuWainger.iw_height_card_le hρ
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro l₁ m₀ Cρ₀ hCρ₀ hgood
  have hT : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by positivity
  have hm₀ : 2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by
    have h := hgood
    simp only [Work.Analysis.IonescuWainger.GoodMajorArcs] at h
    push_cast at h
    nlinarith
  have hstep : (2 : ℝ) ^ (-(m₀ : ℤ)) ≤ (2 : ℝ) ^ (-(2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by
    rw [← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    push_cast
    linarith
  have hcard := hC₀ l₁
  calc 2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
        * (2 : ℝ) ^ (-(m₀ : ℤ))
      ≤ 2 * (C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))))
          * (2 : ℝ) ^ (-(2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by
        have h1 : (2 : ℝ) * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            ≤ 2 * (C₀ * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ)))) :=
          mul_le_mul_of_nonneg_left hcard (by norm_num)
        exact mul_le_mul h1 hstep (by positivity) (by positivity)
      _ = 2 * C₀ * ((2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ)))
            * (2 : ℝ) ^ (-(2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))) := by ring
      _ = 2 * C₀ * (2 : ℝ) ^ (((2 : ℝ) ^ (ρ * (l₁ : ℝ)))
            + (-(2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))) := by
        rw [Real.rpow_add (by norm_num)]
      _ = 2 * C₀ * (2 : ℝ) ^ (-((2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by ring_nf
      _ ≤ 2 * C₀ * 1 := by
        have hle : (2 : ℝ) ^ (-((2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
        have := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 2 * C₀)
        linarith
      _ = 2 * C₀ := by ring

/-- **Each increment is dominated pointwise by the square function** (immediate from the definition
`sqFun = (∑'_m ‖Δ_m f x‖²)^{1/2}`).  This is the pointwise input of the total-variation argument:
it turns `∑_m ‖Δ_m f x‖` into `∑_m (something) · (the local ℓᵖ-mass of `sqFun`)`. -/
lemma increment_enorm_le_sqFun (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (m : ℕ) (x : ℤ) :
    ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (m + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x‖ₑ
      ≤ Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f x := by
  rw [Work.KMTAreas.A7Hi.sqFun]
  have hle : ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (m + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x‖ₑ ^ (2 : ℝ)
      ≤ ∑' j : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (j + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ j f x‖ₑ ^ (2 : ℝ) :=
    ENNReal.le_tsum (f := fun j : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (j + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ j f x‖ₑ ^ (2 : ℝ)) m
  refine (le_trans (le_of_eq ?_) (ENNReal.rpow_le_rpow hle (by norm_num))) 
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-! ## The shift of the low-pass family, and the geometric weight sum

The two lemmas below are the bookkeeping of the *total-variation* (finiteness) layer of the
target: the family at the base level `m₀ + J` is the `J`-shift of the family at `m₀` (so its square
function is a *sub-sum* of the square function at `m₀`), and the frequency measures
`#(ℚ/ℤ)_{≤l₁}·2^{-(m₀+m)}` of the increments have a *summable* `θ`-power, uniformly in `l₁, m₀`
on the good major arcs.  The latter is what makes the frequency-measure (Nikolskii) bound
`Work.KMTAreas.A7HiRep.incBernsteinPointwise` summable over the scales. -/

/-- `2^{-m} = (1/2)^m`. -/
lemma two_pow_neg_eq_half_nat (m : ℕ) : (2 : ℝ) ^ (-(m : ℤ)) = ((1 / 2 : ℝ)) ^ m := by
  rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]

/-- `2^{-(m₀+m)} = (1/2)^{m₀+m}`. -/
lemma two_pow_neg_eq_half (m₀ m : ℕ) :
    (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ))) = ((1 / 2 : ℝ)) ^ (m₀ + m) := by
  rw [show -((m₀ : ℤ) + (m : ℤ)) = (-(m₀ : ℤ)) + (-(m : ℤ)) by ring, zpow_add₀ (by norm_num),
    two_pow_neg_eq_half_nat, two_pow_neg_eq_half_nat, ← pow_add]

/-- `(a^m)^θ = (a^θ)^m` for `0 ≤ a`. -/
lemma rpow_pow_comm {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (θ : ℝ) :
    (a ^ m) ^ θ = (a ^ θ) ^ m := by
  conv_lhs => rw [← Real.rpow_natCast a m]
  conv_rhs => rw [← Real.rpow_natCast (a ^ θ) m]
  rw [← Real.rpow_mul ha, mul_comm, Real.rpow_mul ha]

/-- The low-pass family at the base level `m₀ + J` is the `J`-shift of the family at `m₀`. -/
lemma lpf_shift (ρ : ℝ) (l₁ m₀ J : ℕ) (f : ℤ → ℂ) (k : ℕ) :
    Work.KMTAreas.A7Hi.lpf ρ l₁ (m₀ + J) k f = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (k + J) f := by
  unfold Work.KMTAreas.A7Hi.lpf
  exact congrArg (fun h : ℤ => Work.KMTContract.kmtProj ρ l₁ h f) (by push_cast; ring)

/-- **The square function at the shifted base level is dominated by the square function at the
original level**: `sqFun ρ l₁ (m₀+J) f ≤ sqFun ρ l₁ m₀ f` pointwise, because the increments of the
shifted family are the increments `Δ_{J+m} f` of the original family. -/
theorem sqFun_shift_le (ρ : ℝ) (l₁ m₀ J : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7Hi.sqFun ρ l₁ (m₀ + J) f x ≤ Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f x := by
  rw [Work.KMTAreas.A7Hi.sqFun, Work.KMTAreas.A7Hi.sqFun]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hfun : (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ (m₀ + J) (m + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ (m₀ + J) m f x‖ₑ ^ (2 : ℝ))
      = fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (m + J + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (m + J) f x‖ₑ ^ (2 : ℝ) := by
    funext m
    rw [lpf_shift ρ l₁ m₀ J f (m + 1), lpf_shift ρ l₁ m₀ J f m,
      show m + 1 + J = m + J + 1 from by omega]
  rw [hfun]
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun m : ℕ => m + J)
    (fun a b h => Nat.add_right_cancel h)
    (fun k : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (k + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ k f x‖ₑ ^ (2 : ℝ))

/-- **The geometric weight sum of the increments' frequency measures.**  For every `θ > 0` there is
`C = C(ρ,θ) > 0` such that on the good major arcs the `θ`-powers of the frequency measures
`2·#(ℚ/ℤ)_{≤l₁}·2^{-(m₀+m)}` of the increments form a summable family, uniformly in `l₁` and
`m₀`, with total at most `C`.  This is the summability that turns the Nikolskii bound
`incBernsteinPointwise` into an estimate for the *total variation* of the walk. -/
theorem incrementWeightSum (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (θ : ℝ) (hθ : 0 < θ)
    {Cρ₀ : ℝ} (hCρ₀ : 2 ≤ Cρ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) →
      (∑' m : ℕ, ENNReal.ofReal
          ((2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ)))) ^ θ)) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := card_two_pow_le ρ hρ hρ1
  have hhalf_lt : ((1 / 2 : ℝ)) ^ θ < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hθ
  have hhalf_nonneg : (0 : ℝ) ≤ ((1 / 2 : ℝ)) ^ θ := Real.rpow_nonneg (by norm_num) _
  have hbase : (0 : ℝ) < 1 - ((1 / 2 : ℝ)) ^ θ := by linarith
  refine ⟨C₁ ^ θ / (1 - ((1 / 2 : ℝ)) ^ θ), by positivity, ?_⟩
  intro l₁ m₀ hgood
  have hbound : ∀ m : ℕ,
      ENNReal.ofReal ((2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ)))) ^ θ)
        ≤ ENNReal.ofReal (C₁ ^ θ * (((1 / 2 : ℝ)) ^ θ) ^ m) := by
    intro m
    refine ENNReal.ofReal_le_ofReal ?_
    rw [two_pow_neg_eq_half m₀ m]
    have hsplit : 2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * ((1 / 2 : ℝ)) ^ (m₀ + m)
        = (2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * ((1 / 2 : ℝ)) ^ m₀) * ((1 / 2 : ℝ)) ^ m := by
      rw [pow_add]; ring
    rw [hsplit]
    have hle : 2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
        * ((1 / 2 : ℝ)) ^ m₀ ≤ C₁ := by
      have h := hC₁ l₁ m₀ Cρ₀ hCρ₀ hgood
      rwa [two_pow_neg_eq_half_nat m₀] at h
    calc (2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * ((1 / 2 : ℝ)) ^ m₀ * ((1 / 2 : ℝ)) ^ m) ^ θ
        ≤ (C₁ * ((1 / 2 : ℝ)) ^ m) ^ θ :=
          Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_right hle (by positivity)) hθ.le
      _ = C₁ ^ θ * (((1 / 2 : ℝ)) ^ θ) ^ m := by
          rw [Real.mul_rpow hC₁pos.le (by positivity), rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc (∑' m : ℕ, ENNReal.ofReal ((2 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ)))) ^ θ))
      ≤ ∑' m : ℕ, ENNReal.ofReal (C₁ ^ θ * (((1 / 2 : ℝ)) ^ θ) ^ m) :=
        ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (C₁ ^ θ) * (∑' m : ℕ, ENNReal.ofReal ((((1 / 2 : ℝ)) ^ θ) ^ m)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun m => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C₁ ^ θ) * ENNReal.ofReal (1 - ((1 / 2 : ℝ)) ^ θ)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        have hsum := hasSum_geometric_of_norm_lt_one (K := ℝ)
          (by rw [Real.norm_eq_abs, abs_of_nonneg hhalf_nonneg]; exact hhalf_lt)
        have hsumm : Summable (fun m : ℕ => (((1 / 2 : ℝ)) ^ θ) ^ m) := hsum.summable
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsumm, hsum.tsum_eq]
    _ = ENNReal.ofReal (C₁ ^ θ / (1 - ((1 / 2 : ℝ)) ^ θ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        rfl

/-- **Adding a constant to a walk does not change its chain part** (the jumps are unchanged). -/
theorem chainPart_add_const (r : NNReal) (c : ℂ) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => c + a m) = Work.KMTAreas.A7Hi.chainPart r a := by
  have hkey : ∀ (J : ℕ) (N : ℕ → ℕ),
      ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) => (c + a (N (i + 1))) - (c + a (N i))))‖
        = ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) => a (N (i + 1)) - a (N i)))‖ := by
    intro J N
    congr 2
    have h : (fun (i : Fin J) => (c + a (N (i + 1))) - (c + a (N i)))
        = fun (i : Fin J) => a (N (i + 1)) - a (N i) := by
      funext i
      rw [add_sub_add_left_eq_sub]
    rw [h]
  unfold Work.KMTAreas.A7Hi.chainPart
  have hEq : (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
        ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) => (c + a (N (i + 1))) - (c + a (N i))))‖)
      = ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
        ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) => a (N (i + 1)) - a (N i)))‖ := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      rw [hkey J N]
      exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
    · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      rw [← hkey J N]
      exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  rw [hEq]

/-- **Homogeneity of `eLpNorm` for `ℝ≥0∞`-valued functions under multiplication by a constant.** -/
lemma eLpNorm_ennreal_const_mul {p : ℝ} (hp : 0 < p) (c : ENNReal) {F : ℤ → ENNReal} :
    MeasureTheory.eLpNorm (fun x : ℤ => c * F x) (ENNReal.ofReal p) MeasureTheory.Measure.count
      = c * MeasureTheory.eLpNorm F (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpT,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpT]
  simp only [enorm_eq_self]
  have hq0 : (0 : ℝ) < (ENNReal.ofReal p).toReal := ENNReal.toReal_pos hp0 hpT
  have hpow : (fun x : ℤ => (c * F x) ^ (ENNReal.ofReal p).toReal)
      = fun x : ℤ => c ^ (ENNReal.ofReal p).toReal * F x ^ (ENNReal.ofReal p).toReal := by
    funext x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
  rw [hpow, MeasureTheory.lintegral_const_mul'' _
      ((measurable_of_countable F).pow_const (ENNReal.ofReal p).toReal).aemeasurable,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    show (ENNReal.ofReal p).toReal * (1 / (ENNReal.ofReal p).toReal) = 1 by
      rw [mul_one_div, div_self hq0.ne'], ENNReal.rpow_one]

/-! ## The target is equivalent to its extreme case `Cρ₀ = 2`

`GoodMajorArcs ρ Cρ l k` unfolds to `(k:ℝ) ≤ -Cρ · 2^{ρl}`, which is *monotone decreasing in `Cρ`*
(`A7Hi.goodMajorArcs_mono`).  Hence an instance of the target at `Cρ₀ = 2` — the *weakest*
hypothesis, i.e. the *most* pairs `(l₁,m₀)` — implies the target for every `Cρ₀ ≥ 2` with the same
constant, and conversely.  So the target may be attacked in the single form
`m₀ ≥ 2^{ρl₁+1}` (see `NOTES_A7HiRep_chainPartSqFunPos_SESSION8.md` §S8.6, where it is also noted
that this threshold is the non-aliasing threshold up to `+1`). -/
theorem chainPartSqFunPos_of_extreme (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) {Cρ₀ : ℝ} (hCρ₀ : 2 ≤ Cρ₀)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ 2 l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p
              MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p
              MeasureTheory.Measure.count := by
  obtain ⟨C, hC, hh⟩ := h
  exact ⟨C, hC, fun l₁ m₀ hgood f =>
    hh l₁ m₀ (Work.KMTAreas.A7Hi.goodMajorArcs_mono hCρ₀ hgood) f⟩

end Work.KMTAreas.A7HiRep
