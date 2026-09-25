import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstEta_lipschitz
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_triv_lp
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_pointwise
import Submission.Work.BourgainPlan.Maximal.mstProf_scale_decay
import Submission.Work.Maximal.arcSymbolW_lp_bound_of_coeff
import Submission.Work.Maximal.latglue_basic

/-!
# The narrow-to-wide replacement with `s`-dependent constants, for *every* level `s`

The landed `mstNuS_sub_mstWideModel_pointwise` / `_triv_lp` / `_lr_tail` control the difference
`A_k − Ω_k` only for `s` above a torsion/separation threshold.  The finitely many levels below it
still need a bound; this module supplies it:

* `mstAnnulus_mstG_le`: `‖mstG P β‖ ≤ max 1 (D (s+1)^{-δl})` on the whole annulus, uniformly in `s`;
* `mstNuS_sub_mstWideModel_pointwise_all`: the Lipschitz bound `|η(a_s u) − η(b_s u)| ≤ L R_s |u|`
  together with the profile decay `|ζ| |Φ_{2^k}(ζ)| ≤ CΦ 2^{-k/d}` gives, for **every** `s` and
  `k ≥ 1`, the symbol bound `‖ν^s_{2^k} − Ω^s_{2^k}‖ ≤ Cpt s · 2^{-k/d}` (the constant `Cpt s`
  contains the scale ratio `R_s = 2^{s(d−χ)} + c_s`);
* `mstNuS_sub_mstWideModel_triv_lp_all`: the `ℓ^q`-Young bound for the difference, for every `s`,
  with an explicit weight `W` on the annulus replacing the Gauss bound.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Maximal

noncomputable section

open Work.BourgainPlan.Maximal
open Work.BourgainPlan.IonescuWainger

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- **The weight bound for `mstG` on the annulus, uniform in the level.**  For `s = 0` the crude
bound `‖mstG P β‖ ≤ 1` (`mstG_norm_le_one`) is used, for `s ≥ 1` the Gauss hypothesis. -/
lemma mstAnnulus_mstG_le (P : Polynomial ℤ) (l : ℕ) (hl : 1 ≤ l)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Circ), β ∈ mstU l (s + 1) \ mstU l s →
      ‖mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l))) :
    ∀ s : ℕ, ∀ β ∈ mstAnnulus l s,
      ‖mstG P β‖ ≤ max 1 (D * ((s : ℝ) + 1) ^ (-(δ * l))) := by
  intro s β hβ
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    exact le_trans (mstG_norm_le_one P β) (le_max_left _ _)
  · rw [mstAnnulus_eq l s hs] at hβ
    exact le_trans (hGauss s β hβ) (le_max_right _ _)

/-- **The pointwise narrow-to-wide replacement for every level.**  With `a_s = 2^{s(d−χ)}`,
`b_s = c_s` and `R_s = a_s + b_s`, the Lipschitz property of `η` gives
`‖η(a_s u) − η(b_s u)‖ ≤ L R_s |u|`, and the profile decay `‖ζ‖ ‖Φ_{2^k}(ζ)‖ ≤ CΦ 2^{-k/d}`
turns this into a *geometric* pointwise bound on the symbol difference, valid for every `s` and
every `k ≥ 1` (no separation/torsion hypothesis on `s` is needed). -/
theorem mstNuS_sub_mstWideModel_pointwise_all (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (l : ℕ) (hl : 1 ≤ l) (χ : ℝ) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Circ), β ∈ mstU l (s + 1) \ mstU l s →
      ‖mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l))) :
    ∃ Cpt : ℕ → ℝ, (∀ s : ℕ, 0 < Cpt s) ∧ ∀ s k : ℕ, 1 ≤ k → ∀ ξ : Circ,
      ‖mstNuS P l P.natDegree χ η k s ξ - mstWideModel P l χ η k s ξ‖
        ≤ Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) := by
  classical
  have hd0 : (0 : ℝ) < (P.natDegree : ℝ) := by
    exact_mod_cast (by omega : 0 < P.natDegree)
  obtain ⟨L, hLpos, hL⟩ := mstEta_lipschitz η hηc hηsup
  obtain ⟨CΦ, hCΦpos, hCΦ⟩ := mstProf_scale_decay P hd
  refine ⟨fun s => max 1 (D * ((s : ℝ) + 1) ^ (-(δ * l))) * L
      * ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) + mstWideC P s)
      * ((mstAnnulus l s).card : ℝ) * CΦ + 1, fun s => by
        have hmwc : (0 : ℝ) < mstWideC P s := lt_of_lt_of_le zero_lt_one (one_le_mstWideC P s)
        positivity, ?_⟩
  intro s k hk ξ
  set W : ℝ := max 1 (D * ((s : ℝ) + 1) ^ (-(δ * l))) with hWdef
  set R : ℝ := (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) + mstWideC P s with hRdef
  have hWnn : 0 ≤ W := le_trans zero_le_one (le_max_left _ _)
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    have h1 : (0 : ℝ) ≤ mstWideC P s := le_trans zero_le_one (one_le_mstWideC P s)
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) :=
      Real.rpow_nonneg (by norm_num) _
    linarith
  have hW : ∀ β ∈ mstAnnulus l s, ‖mstG P β‖ ≤ W := by
    intro β hβ
    simpa only [hWdef] using mstAnnulus_mstG_le P l hl hδ D hD hGauss s β hβ
  -- the Lipschitz bound at the two scales
  have hdiff : ∀ ζ : Circ,
      ‖mstEta P.natDegree χ η s ζ - mstWideBump P χ η s ζ‖ ≤ L * R * ‖ζ‖ := by
    intro ζ
    have hLb := hL ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ)
      (mstWideC P s * iwRep ζ)
    have heq : mstEta P.natDegree χ η s ζ - mstWideBump P χ η s ζ
        = η ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ)
            - η (mstWideC P s * iwRep ζ) := by
      rw [mstEta_apply, mstWideBump_apply]
    rw [heq]
    have habs : |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ
          - mstWideC P s * iwRep ζ|
        = |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) - mstWideC P s| * |iwRep ζ| := by
      rw [← sub_mul, abs_mul]
    have hle : |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) - mstWideC P s| ≤ R := by
      rw [hRdef, abs_sub_le_iff]
      have ha : (0 : ℝ) ≤ (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hb : (0 : ℝ) ≤ mstWideC P s := le_trans zero_le_one (one_le_mstWideC P s)
      constructor <;> linarith
    calc ‖η _ - η _‖
        ≤ L * |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ
            - mstWideC P s * iwRep ζ| := hLb
      _ = L * (|(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) - mstWideC P s| * |iwRep ζ|) := by
          rw [habs]
      _ ≤ L * (R * |iwRep ζ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) hLpos.le
      _ = L * R * ‖ζ‖ := by rw [norm_eq_abs_iwRep]; ring
  -- the profile decay
  have hprof : ∀ ζ : Circ, ‖ζ‖ * ‖mstProf P (2 ^ k) ζ‖
      ≤ CΦ * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) :=
    fun ζ => by simpa only [neg_div] using hCΦ k hk ζ
  -- the termwise bound
  have hterm : ∀ β ∈ mstAnnulus l s,
      ‖star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
          * (mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β)))‖
        ≤ W * L * R * (CΦ * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ)))) := by
    intro β hβ
    have hinner : ‖mstProf P (2 ^ k) (ξ - β)‖
        * ‖mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β)‖
        ≤ L * R * (CΦ * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ)))) := by
      have hg := hdiff (ξ - β)
      have hp := hprof (ξ - β)
      calc ‖mstProf P (2 ^ k) (ξ - β)‖
              * ‖mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β)‖
          ≤ ‖mstProf P (2 ^ k) (ξ - β)‖ * (L * R * ‖ξ - β‖) :=
            mul_le_mul_of_nonneg_left hg (norm_nonneg _)
        _ = L * R * (‖ξ - β‖ * ‖mstProf P (2 ^ k) (ξ - β)‖) := by ring
        _ ≤ L * R * (CΦ * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ)))) :=
            mul_le_mul_of_nonneg_left hp (mul_nonneg hLpos.le hRnn)
    rw [norm_mul, norm_mul, norm_star, norm_star]
    refine le_trans (mul_le_mul (hW β hβ) hinner (by positivity) hWnn) (le_of_eq ?_)
    ring
  rw [show mstNuS P l P.natDegree χ η k s ξ - mstWideModel P l χ η k s ξ
      = ∑ β ∈ mstAnnulus l s, (star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
            * mstEta P.natDegree χ η s (ξ - β))
          - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
            * mstWideBump P χ η s (ξ - β))) from ?_]
  · calc ‖∑ β ∈ mstAnnulus l s, (star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
            * mstEta P.natDegree χ η s (ξ - β))
          - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
            * mstWideBump P χ η s (ξ - β)))‖
        ≤ ∑ β ∈ mstAnnulus l s, ‖star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
            * mstEta P.natDegree χ η s (ξ - β))
          - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
            * mstWideBump P χ η s (ξ - β))‖ := norm_sum_le _ _
      _ ≤ ∑ _β ∈ mstAnnulus l s,
            W * L * R * (CΦ * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ)))) :=
          Finset.sum_le_sum (fun β hβ => by
            rw [show star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
                  * mstEta P.natDegree χ η s (ξ - β))
                - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
                  * mstWideBump P χ η s (ξ - β))
                = star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
                  * (mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β)))
              from by ring]
            exact hterm β hβ)
      _ = ((mstAnnulus l s).card : ℝ)
            * (W * L * R * (CΦ * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (W * L * R * ((mstAnnulus l s).card : ℝ) * CΦ)
            * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) := by ring
      _ ≤ (W * L * R * ((mstAnnulus l s).card : ℝ) * CΦ + 1)
            * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
          linarith
      _ = (max 1 (D * ((s : ℝ) + 1) ^ (-(δ * l))) * L
            * ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) + mstWideC P s)
            * ((mstAnnulus l s).card : ℝ) * CΦ + 1)
            * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) := by
          rw [hWdef, hRdef]
  · rw [mstNuS_apply, mstWideModel_apply]
    rw [show mstLevel l (s + 1) \ mstLevel l s = mstAnnulus l s from rfl]
    rw [← Finset.sum_sub_distrib]

/-- **The trivial (Young/`ℓ¹`-coefficient) `ℓ^q` bound for the narrow-to-wide difference, at every
level `s`.**  The only hypothesis on the level is a bound `W` for the weights `‖mstG P β‖` on the
annulus; the constant is `K W ♯(annulus)`. -/
theorem mstNuS_sub_mstWideModel_triv_lp_all (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT)
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp (mstWideModel P l χ η k s) ⊤ haarT)
    {K : ℝ} (hK : 0 < K)
    (hcoeff : ∀ k s : ℕ, Summable (fun m : ℤ => ‖∫ ξ : Circ,
        (star (mstProf P (2 ^ k) ξ) * (mstEta P.natDegree χ η s ξ - mstWideBump P χ η s ξ))
          * star (fourier m ξ) ∂haarT‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Circ,
        (star (mstProf P (2 ^ k) ξ) * (mstEta P.natDegree χ η s ξ - mstWideBump P χ η s ξ))
          * star (fourier m ξ) ∂haarT‖) ≤ K)
    {q : ℝ} (hq : 1 ≤ q) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∀ W : ℝ, 0 < W →
      (∀ β ∈ mstAnnulus l s, ‖mstG P β‖ ≤ W) → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => ‖opMul
          (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
          (memℓp_finsupp g) m
        - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g)
          (memℓp_finsupp g) m‖ₑ)
        (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (K * W * ((mstAnnulus l s).card : ℝ))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  classical
  refine ⟨K, hK, ?_⟩
  intro s W hWpos hw k g
  have hEta_ml : MemLp (mstEta P.natDegree χ η s) ⊤ haarT :=
    memLp_mstEta_of_continuous P P.natDegree χ η hηc.continuous s
  have hWide_ml : MemLp (mstWideBump P χ η s) ⊤ haarT :=
    (mstWideBump_memLp_and_narrow P χ η hηc.continuous hηsup s).1
  have hProf_ml : MemLp (mstProf P (2 ^ k)) ⊤ haarT := memLp_mstProf_symbol P (2 ^ k)
  set φ : Circ → ℂ := fun ζ => star (mstProf P (2 ^ k) ζ)
      * (mstEta P.natDegree χ η s ζ - mstWideBump P χ η s ζ) with hφdef
  have hφml : MemLp φ ⊤ haarT := by
    rw [hφdef]
    exact hProf_ml.star.mul (hEta_ml.sub hWide_ml)
  set w : Circ → ℂ := fun β => star (mstG P β) with hwdef
  have hw' : ∀ β ∈ mstAnnulus l s, ‖w β‖ ≤ W := by
    intro β hβ
    rw [hwdef, norm_star]
    exact hw β hβ
  have hcsum : Summable fun m : ℤ => ‖∫ ξ : Circ, φ ξ * star (fourier m ξ) ∂haarT‖ := by
    simpa only [hφdef] using (hcoeff k s).1
  have hcK : (∑' m : ℤ, ‖∫ ξ : Circ, φ ξ * star (fourier m ξ) ∂haarT‖) ≤ K := by
    simpa only [hφdef] using (hcoeff k s).2
  have hLp : mstNuSCls P l P.natDegree χ η k s (hνsml k s)
      - (hΩml k s).toLp (mstWideModel P l χ η k s)
      = arcSymbolWLp (fun β : Circ => β) w (mstAnnulus l s) φ hφml := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_sub (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
        ((hΩml k s).toLp (mstWideModel P l χ η k s)),
      mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s),
      MemLp.coeFn_toLp (hΩml k s),
      arcSymbolWLp_coeFn (fun β : Circ => β) w (mstAnnulus l s) φ hφml] with ξ hsub h1 h2 h3
    rw [hsub, Pi.sub_apply, h1, h2, h3]
    rw [mstNuS_apply, mstWideModel_apply, arcSymbolW_apply, hφdef, hwdef,
      show mstAnnulus l s = mstLevel l (s + 1) \ mstLevel l s from rfl]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun β _ => by ring)
  have hout : (fun m : ℤ => ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
        (⇑g) (memℓp_finsupp g) m
      - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s))
        (⇑g) (memℓp_finsupp g) m‖ₑ)
      = fun m : ℤ => ‖opMul
        (arcSymbolWLp (fun β : Circ => β) w (mstAnnulus l s) φ hφml)
        (⇑g) (memℓp_finsupp g) m‖ₑ := by
    funext m
    rw [show opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
          (memℓp_finsupp g) m
        - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m
        = opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s))
          (⇑g) (memℓp_finsupp g) m from by
        rw [← Pi.sub_apply, opMul_sub],
      hLp]
  rw [hout, MeasureTheory.eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable]
  refine (arcSymbolW_lp_bound_of_coeff (p := q) hq (φ := φ) hφml
      (c := fun m : ℤ => ∫ ξ : Circ, φ ξ * star (fourier m ξ) ∂haarT) hcsum (fun _ => rfl)
      (W := W) (K := K) hWpos.le hcK w (mstAnnulus l s) hw' g).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact le_of_eq (by ring)

end

end Work.Maximal
