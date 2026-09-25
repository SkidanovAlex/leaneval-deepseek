import Mathlib
import Submission.Work.Maximal.latglue_basic
import Submission.Work.Maximal.latglue_diff
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_lr_tail
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_coeff
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_pointwise

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

open Work.BourgainPlan.Maximal
open Work.BourgainPlan.IonescuWainger

/-! ## Elementary `rpow`/geometric-series tools for the `s`-dependent tail sum -/

/-- The general term of the tail sum is the general term of a geometric series, with ratio
`2^{−θ/d}`: `(b · 2^{−(K+j)/d})^θ = b^θ · 2^{−θK/d} · (2^{−θ/d})^j`. -/
private lemma tail_geom_term (θ : ℝ) (d : ℕ) (K : ℕ) (b : ℝ) (hb : 0 ≤ b) (j : ℕ) :
    (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (d : ℝ)))) ^ θ
      = b ^ θ * (2 : ℝ) ^ (-(θ * (K : ℝ) / (d : ℝ)))
          * ((2 : ℝ) ^ (-(θ / (d : ℝ)))) ^ j := by
  rw [Real.mul_rpow hb (Real.rpow_nonneg (by norm_num) _)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring_nf

/-- The geometric tail `j ↦ a (b 2^{−(K+j)/d})^θ` is summable for every `0 < θ < 1`. -/
private lemma tail_geom_summable (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (d : ℕ) (hd : 1 ≤ d)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun j : ℕ => a * (b * (2 : ℝ) ^ (-(((K : ℝ) + (j : ℝ)) / (d : ℝ)))) ^ θ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  set r : ℝ := (2 : ℝ) ^ (-(θ / (d : ℝ))) with hrdef
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hrdef]
    exact (Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mpr
      (Or.inl ⟨by norm_num, by
        have h : 0 < θ / (d : ℝ) := div_pos hθ0 hd0
        linarith⟩)
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg (le_of_lt hrpos)]; exact hr1
  set c : ℝ := a * b ^ θ * (2 : ℝ) ^ (-(θ * (K : ℝ) / (d : ℝ))) with hcdef
  refine ((summable_geometric_of_norm_lt_one hnorm).mul_left c).congr (fun j => ?_)
  rw [tail_geom_term θ d K b hb j, hcdef]
  ring

/-- The lift of the level-`0` bump is `x ↦ η (-x)` (the version in
`mstNuS_sub_mstWideModel_lr_tail` is `private`, hence reproduced here). -/
private lemma circleLift_mstEta_zero_eq_neg_aux {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) = fun x : ℝ => η (-x) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Work.BourgainPlan.Thm52.circleLift_of_mem hx, mstEta_zero_eq]
    rcases eq_or_ne x (1 / 2) with h | h
    · subst h
      rw [iwRep_neg_half, hηsup (1 / 2) (by norm_num), hηsup (-(1 / 2)) (by norm_num)]
    · have hx' : -(1 / 2 : ℝ) < x ∧ x < 1 / 2 := ⟨hx.1, lt_of_le_of_ne hx.2 h⟩
      have hmem : -x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) :=
        ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
      have hcoe : -((x : ℝ) : Circ) = ((-x : ℝ) : Circ) :=
        (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
      rw [hcoe, iwRep_coe_of_mem hmem]
  · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
    symm
    refine hηsup (-x) ?_
    have habs : (1 : ℝ) / 2 ≤ |x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rwa [abs_neg]

/-- **The narrow-to-wide replacement in the tail of the scales, at *every* level `s`** (the
`s`-unrestricted companion of the landed `Work.Maximal.mstNuS_sub_mstWideModel_lr_tail`, whose
constant is uniform in `s` but which holds only for `s` above a threshold `s₀`).

For every `1 < r < 2` there is a function `C : ℕ → ℝ` with `C s > 0` for all `s` such that for
**every** level `s` and every finitely supported `g`,

  `‖ sup_{k ≥ 2^{κ_s}} |(A_k − Ω_k) g| ‖_{ℓʳ(ℤ)} ≤ C s · ‖g‖_{ℓʳ(ℤ)}`,

where `A_k = opMul (mstNuSCls P l d χ η k s)` is the narrow level-`s` model and
`Ω_k = opMul ((hΩml k s).toLp (mstWideModel P l χ η k s))` the wide level model.

Route (an adaptation of the proof of the landed `mstNuS_sub_mstWideModel_lr_tail`, with the
tail-arithmetic and the threshold `s₀` replaced by explicit `s`-dependent finite sums; the helper
lemmas are in `Submission.Work.Maximal.latglue_basic` and `latglue_diff`):

* `mstNuS_sub_mstWideModel_pointwise_all` gives, for every `s` and every `k ≥ 1`, the pointwise
  symbol bound `‖ν^s_{2^k} − Ω^s_{2^k}‖ ≤ Cpt s · 2^{−k/d}` (`d = P.natDegree`), hence by
  Plancherel (`eLpNorm_two_opMul_le`) the `ℓ²` operator bound `Cpt s · 2^{−k/d}` on the difference
  class (the a.e. symbol bound is obtained from `Lp.coeFn_sub`, `mstNuSCls_coeFn`,
  `MemLp.coeFn_toLp`);
* `mstNuS_sub_mstWideModel_triv_lp_all`, with `q = (1+r)/2` and the annulus weight
  `W_s = max 1 (D (s+1)^{−δl})` from `mstAnnulus_mstG_le`, gives the `ℓ^q` bound
  `A_s = K · W_s · ♯(mstAnnulus l s)` uniformly in `k` (coefficient hypothesis from
  `mstNuS_sub_mstWideModel_coeff`);
* Riesz–Thorin (`opMulFinsuppLM_interp` with `(r := q) (p := r)`) gives the per-scale bound
  `‖(A_k − Ω_k) g‖_{ℓʳ} ≤ A_s^{1−θ} (Cpt s · 2^{−k/d})^θ ‖g‖_{ℓʳ}`,
  `θ = (1/q − 1/r)/(1/q − 1/2) ∈ (0,1)`;
* `Mexp j := A_s^{1−θ} (Cpt s · 2^{−(K₀+j)/d})^θ` with `K₀ = 2^{mstKappa P s}` is summable
  (geometric, ratio `2^{−θ/d} ∈ (0,1)`), and `tail_sup_le_of_per_k_lat` bounds the supremum over the
  tail by `(∑' j, Mexp j) ‖g‖_{ℓʳ}`; take `C s = (∑' j, Mexp j) + 1` (the `+1` also covers the
  empty-annulus case, where both sides vanish). -/
theorem mstNuS_sub_mstWideModel_lr_tail_all (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp
      (Work.Maximal.mstWideModel P l χ η k s) ⊤ (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℕ → ℝ, (∀ s : ℕ, 0 < C s) ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
              (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
            - Work.BourgainPlan.IonescuWainger.opMul
              ((hΩml k s).toLp (Work.Maximal.mstWideModel P l χ η k s))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C s)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  classical
  -- ## 0. elementary consequences of the hypotheses
  have hd1 : 1 ≤ P.natDegree := by omega
  have hχd : χ ≤ (P.natDegree : ℝ) := by
    have h1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd1
    linarith
  have hδl : 0 < δ * l := mul_pos hδ (by exact_mod_cast hl)
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  -- ## 1. a bound for `η` and the `C²`-ness of the level-`0` lift
  obtain ⟨Mb, hMbpos, hηbd⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, ‖η x‖ ≤ M := by
    obtain ⟨Cb, hCb⟩ := (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
      hηc.continuous.continuousOn
    refine ⟨max Cb 1, by positivity, fun x => ?_⟩
    by_cases hx : |x| ≤ 1 / 2
    · exact le_trans (hCb x (by rw [Set.mem_Icc]; exact abs_le.mp hx)) (le_max_left _ _)
    · have hx' : (1 / 2 : ℝ) ≤ |x| := le_of_lt (lt_of_not_ge hx)
      rw [hηsup x hx']
      exact le_trans (by simp : ‖(0 : ℂ)‖ ≤ 1) (le_max_right _ _)
  have hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η 0)) := by
    rw [circleLift_mstEta_zero_eq_neg_aux hηsup]
    exact hηc.comp contDiff_neg
  -- ## 2. the pointwise symbol estimate, at every level
  obtain ⟨Cpt, hCptpos, hpt⟩ :=
    mstNuS_sub_mstWideModel_pointwise_all P hd l hl χ η hηc hηsup hδ D hD hGauss
  -- ## 3. the coefficient-kernel bound
  obtain ⟨Kc, hKcpos, hcoeffN⟩ :=
    mstNuS_sub_mstWideModel_coeff P P.natDegree χ η Mb hMbpos hχd hηbd hη2 hcd0
  have hcoeff : ∀ k s : ℕ, Summable (fun m : ℤ => ‖∫ ξ : Circ,
        (star (mstProf P (2 ^ k) ξ)
          * (mstEta P.natDegree χ η s ξ - mstWideBump P χ η s ξ)) * star (fourier m ξ) ∂haarT‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Circ, (star (mstProf P (2 ^ k) ξ)
          * (mstEta P.natDegree χ η s ξ - mstWideBump P χ η s ξ)) * star (fourier m ξ) ∂haarT‖)
        ≤ Kc :=
    fun k s => hcoeffN (2 ^ k) s (Nat.one_le_two_pow)
  -- ## 4. the two exponents
  set q : ℝ := (1 + r) / 2 with hqdef
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqr : q < r := by rw [hqdef]; linarith
  set θ : ℝ := (1 / q - 1 / r) / (1 / q - 1 / 2) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    have h1 : (1 : ℝ) / r < 1 / q :=
      one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < q) hqr
    exact div_pos (by linarith) (by
      have h2 : (1 : ℝ) / 2 < 1 / q :=
        one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < q) (by linarith : q < 2)
      linarith)
  have hθlt : θ < 1 := by
    rw [hθdef, div_lt_one (by
      have h2 : (1 : ℝ) / 2 < 1 / q :=
        one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < q) (by linarith : q < 2)
      linarith)]
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < r) hr2
    linarith
  -- ## 5. the trivial `ℓ^q` bound for the difference, at every level
  obtain ⟨_, _, htriv⟩ := mstNuS_sub_mstWideModel_triv_lp_all P l χ η hηc hηsup hνsml hΩml
    (K := Kc) hKcpos hcoeff (q := q) hq1.le
  -- ## 6. the `s`-dependent constants and the geometric majorant
  set Wt : ℕ → ℝ := fun s => max 1 (D * ((s : ℝ) + 1) ^ (-(δ * l))) with hWtdef
  set As : ℕ → ℝ := fun s => Kc * Wt s * ((mstAnnulus l s).card : ℝ) with hAsdef
  set Al : ℕ → ℝ := fun s => max (As s) 1 with hAldef
  set Mn : ℕ → ℕ → ℝ := fun s j => (Al s) ^ (1 - θ)
      * (Cpt s * (2 : ℝ) ^ (-(((((2 ^ mstKappa P s) + j : ℕ)) : ℝ) / (P.natDegree : ℝ)))) ^ θ
    with hMndef
  have hAlpos : ∀ s : ℕ, 0 < Al s :=
    fun s => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hWpos : ∀ s : ℕ, 0 < Wt s :=
    fun s => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hWle : ∀ s : ℕ, ∀ β ∈ mstAnnulus l s, ‖mstG P β‖ ≤ Wt s := by
    intro s β hβ
    simpa only [hWtdef] using mstAnnulus_mstG_le P l hl hδ D hD hGauss s β hβ
  have hMnn : ∀ s j : ℕ, 0 ≤ Mn s j := by
    intro s j
    rw [hMndef]
    exact mul_nonneg (Real.rpow_nonneg (hAlpos s).le _)
      (Real.rpow_nonneg
        (mul_nonneg (hCptpos s).le (Real.rpow_nonneg (by norm_num) _)) _)
  have hMsumm : ∀ s : ℕ, Summable (Mn s) := by
    intro s
    have ha : 0 ≤ (Al s) ^ (1 - θ) := Real.rpow_nonneg (hAlpos s).le _
    have hb : 0 ≤ Cpt s := (hCptpos s).le
    have h := tail_geom_summable θ hθpos hθlt P.natDegree hd1 (2 ^ mstKappa P s)
      ((Al s) ^ (1 - θ)) (Cpt s) ha hb
    refine h.congr (fun j => ?_)
    simp only [hMndef, Nat.cast_add]
  refine ⟨fun s => (∑' j : ℕ, Mn s j) + 1, ?_, ?_⟩
  · -- positivity of the constant
    intro s
    have h : 0 ≤ ∑' j : ℕ, Mn s j := tsum_nonneg (hMnn s)
    linarith
  · -- the main bound
    intro s g
    have hsumm := hMsumm s
    -- ## 7. the per-scale bound
    have hper : ∀ k : ℕ, 2 ^ mstKappa P s ≤ k →
        MeasureTheory.eLpNorm (fun m : ℤ => opMul
              (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              (⇑g) (memℓp_finsupp g) m
            - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s))
              (⇑g) (memℓp_finsupp g) m)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Al s ^ (1 - θ)
            * (Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ)))) ^ θ)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      intro k hk
      have hk1 : 1 ≤ k := le_trans Nat.one_le_two_pow hk
      have hεnn : 0 ≤ Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) :=
        mul_nonneg (hCptpos s).le (Real.rpow_nonneg (by norm_num) _)
      have hsymb : ∀ᵐ ξ ∂haarT, ‖((mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s) : Lp ℂ ⊤ haarT) : Circ → ℂ) ξ‖
          ≤ Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) := by
        filter_upwards [Lp.coeFn_sub (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              ((hΩml k s).toLp (mstWideModel P l χ η k s)),
            mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s),
            MemLp.coeFn_toLp (hΩml k s)] with ξ h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
        exact hpt s k hk1 ξ
      have h2g : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm ((opMulFinsuppLM
            (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
              - (hΩml k s).toLp (mstWideModel P l χ η k s))) f)
            (ENNReal.ofReal 2) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))))
            * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        intro f
        rw [opMulFinsuppLM_apply]
        exact eLpNorm_two_opMul_le (memℓp_finsupp f) hεnn hsymb
      have hqg : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm ((opMulFinsuppLM
            (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
              - (hΩml k s).toLp (mstWideModel P l χ η k s))) f)
            (ENNReal.ofReal q) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Al s)
            * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
        intro f
        have h' := htriv s (Wt s) (hWpos s) (hWle s) k f
        rw [opMulFinsuppLM_apply, ← opMul_sub, ← eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable]
        simp only [hAldef, hAsdef]
        exact h'.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
      have hrg := opMulFinsuppLM_interp (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s)) (r := q) (p := r) (A := Al s)
        (B := Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))))
        hq1 hqr hr2 (hAlpos s)
        (mul_pos (hCptpos s) (Real.rpow_pos_of_pos (by norm_num) _)) hqg h2g g
      have hkey : Al s ^ (1 - (1 / q - 1 / r) / (1 / q - 1 / 2))
            * (Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))))
              ^ ((1 / q - 1 / r) / (1 / q - 1 / 2))
          = Al s ^ (1 - θ)
            * (Cpt s * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ)))) ^ θ := by
        rw [hθdef]
      have hTk : (opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s))) g
          = fun m : ℤ => opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
                (⇑g) (memℓp_finsupp g) m
              - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m := by
        rw [opMulFinsuppLM_apply, ← opMul_sub]
        funext m
        rfl
      rw [hkey, hTk] at hrg
      exact hrg
    -- ## 8. the per-`j` bounds and the summation
    have hperj : ∀ j : ℕ,
        MeasureTheory.eLpNorm (fun m : ℤ =>
            opMul (mstNuSCls P l P.natDegree χ η (2 ^ mstKappa P s + j) s
                (hνsml (2 ^ mstKappa P s + j) s)) (⇑g) (memℓp_finsupp g) m
              - opMul ((hΩml (2 ^ mstKappa P s + j) s).toLp
                  (mstWideModel P l χ η (2 ^ mstKappa P s + j) s)) (⇑g) (memℓp_finsupp g) m)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Mn s j)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      intro j
      have h' := hper (2 ^ mstKappa P s + j) (Nat.le_add_right _ _)
      simpa only [hMndef] using h'
    have hfin := tail_sup_le_of_per_k_lat (2 ^ mstKappa P s)
      (fun k m => opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
          (⇑g) (memℓp_finsupp g) m
        - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m)
      (⇑g) (Mn s) hr.le hperj (hMnn s) hsumm
    refine hfin.trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    linarith

end

end Work.Maximal
