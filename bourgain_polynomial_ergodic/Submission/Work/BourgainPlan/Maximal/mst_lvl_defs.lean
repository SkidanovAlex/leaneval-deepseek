import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.rmELpNormSupLe
import Submission.Work.BourgainPlan.Maximal.major_arc_nbd_bound
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_hilbert
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.iw_superset_bound
import Submission.Work.BourgainPlan.Maximal.iwRangeBound_of_endpoint
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_triv
import Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_l2
import Submission.Work.BourgainPlan.Maximal.mstU_rep
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mstU_annulus_tiling
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mst_err1_prof_coeff
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_star
import Submission.Work.BourgainPlan.Maximal.mikhlin_multiplier_lift
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff
import Submission.Work.BourgainPlan.Maximal.mz_finsupp_sqfun
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## The symbols of the level-`s` pieces -/

/-- `MemLp · ⊤` is closed under pointwise products (`MemLp.mul` is unusably slow for `⊤` unless
the Hölder exponents are given explicitly). -/
lemma memLp_mul_top {f g : Circ → ℂ} (hf : MemLp f ⊤ haarT) (hg : MemLp g ⊤ haarT) :
    MemLp (f * g) ⊤ haarT := by
  have h : MemLp (g * f) ⊤ haarT :=
    MemLp.mul (f := f) (φ := g) (p := ⊤) (q := ⊤) (r := ⊤) hg hf
  simpa only [Pi.mul_apply, mul_comm] using h

/-- The conjugate profile `star (Φ_N)` read on the circle. -/
def mstStarProf (P : Polynomial ℤ) (N : ℕ) : Circ → ℂ := fun ζ => star (mstProf P N ζ)

@[simp] lemma mstStarProf_apply (P : Polynomial ℤ) (N : ℕ) (ζ : Circ) :
    mstStarProf P N ζ = star (mstProf P N ζ) := rfl

lemma memLp_mstStarProf (P : Polynomial ℤ) (N : ℕ) : MemLp (mstStarProf P N) ⊤ haarT :=
  memLp_comp_iwRep (g := fun θ : ℝ => star (polyProfile P N θ))
    (memLp_restrict_Ioc_of_continuous (Complex.continuous_conj.comp (continuous_polyProfile P N)))

/-- The (unweighted) profile-times-bump of the MST level model: `star (Φ_N) · η_s`. -/
def mstPiBump (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (N s : ℕ) : Circ → ℂ :=
  mstStarProf P N * mstEta d χ η s

@[simp] lemma mstPiBump_apply (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (N s : ℕ) (ζ : Circ) :
    mstPiBump P d χ η N s ζ = star (mstProf P N ζ) * mstEta d χ η s ζ := by
  simp only [mstPiBump, Pi.mul_apply, mstStarProf_apply]

lemma memLp_mstPiBump (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (N s : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT) : MemLp (mstPiBump P d χ η N s) ⊤ haarT :=
  memLp_mul_top (memLp_mstStarProf P N) hηml

lemma mstNuS_eq_arcSymbolW (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ) :
    mstNuS P l d χ η n s
      = arcSymbolW (fun β : Circ => β) (fun β => star (mstG P β))
          (mstLevel l (s + 1) \ mstLevel l s) (mstPiBump P d χ η (2 ^ n) s) := by
  funext ξ
  simp only [mstNuS, mstModelFn_apply, arcSymbolW_apply, mstPiBump_apply]

/-- The conjugate of the signed lacunary profile-difference symbol, read on the circle. -/
def mstStarThetaEps (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) : Circ → ℂ :=
  fun ζ => star (mstThetaEps P i M ε (iwRep ζ))

@[simp] lemma mstStarThetaEps_apply (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) (ζ : Circ) :
    mstStarThetaEps P i M ε ζ = star (mstThetaEps P i M ε (iwRep ζ)) := rfl

/-- The signed lacunary profile-difference symbol times the level bump: the symbol of the
signed block sums in the Rademacher–Menshov reduction of MST Theorem 7. -/
def mstThetaBump (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (i M s : ℕ) (ε : ℕ → ℂ) :
    Circ → ℂ :=
  mstStarThetaEps P i M ε * mstEta d χ η s

@[simp] lemma mstThetaBump_apply (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (i M s : ℕ) (ε : ℕ → ℂ) (ζ : Circ) :
    mstThetaBump P d χ η i M s ε ζ
      = star (mstThetaEps P i M ε (iwRep ζ)) * mstEta d χ η s ζ := by
  simp only [mstThetaBump, Pi.mul_apply, mstStarThetaEps_apply]

/-- The telescoping identity: the signed sum of block differences of `mstPiBump` is the single
symbol `mstThetaBump` of the signed lacunary profile differences. -/
lemma mstPiBump_block_sum (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (i M s : ℕ) (ε : ℕ → ℂ) (ζ : Circ) :
    (∑ j ∈ Finset.range M, ε j * (mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s ζ
        - mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s ζ))
      = mstThetaBump P d χ η i M s (fun j => star (ε j)) ζ := by
  have hlhs : (∑ j ∈ Finset.range M, ε j * (mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s ζ
        - mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s ζ))
      = (∑ j ∈ Finset.range M, star (star (ε j)) * (star (mstProf P (2 ^ ((j + 1) * 2 ^ i)) ζ)
          - star (mstProf P (2 ^ (j * 2 ^ i)) ζ))) * mstEta d χ η s ζ := by
    rw [Finset.sum_congr rfl (fun j _ => ?_), Finset.sum_mul]
    · simp only [mstPiBump_apply, star_star]
      ring
  rw [hlhs, mstThetaBump_apply]
  congr 1
  simp only [mstThetaEps_apply]
  rw [star_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [star_mul, star_sub, mstProf_apply, mstProf_apply]; ring)

/-! ## Narrowness and `MemLp` of the level symbols -/

lemma continuous_mstThetaEps (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    Continuous (mstThetaEps P i M ε) := by
  unfold mstThetaEps
  exact continuous_finsetSum _ (fun j _ =>
    continuous_const.mul ((continuous_polyProfile P _).sub (continuous_polyProfile P _)))

/-- **The level bump `η_s` is supported in the ball of radius `exp(−(s+1)^{1/10})`** for large `s`:
if `‖ξ‖ > iwEps (mstRho l) ((s+1)^l)` then `mstEta d χ η s ξ = 0`. -/
lemma mstEta_narrow (l : ℕ) (hl : 1 ≤ l) (d : ℕ) (hd : 1 ≤ d) {χ : ℝ} (hχd : χ < (d : ℝ))
    (η : ℝ → ℂ) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ ξ : Circ,
      iwEps (mstRho l) ((s + 1) ^ l) < ‖ξ‖ → mstEta d χ η s ξ = 0 := by
  have hσ : 0 < (d : ℝ) - χ := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨s₁, hs₁⟩ := exists_rpow_ten_add_one_lt ((d : ℝ) - χ) hσ
  refine ⟨s₁, fun s hs ξ hξ => ?_⟩
  have hlt : 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))
      < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := inv_two_mul_two_rpow_lt_exp (hs₁ s hs)
  have hE : iwEps (mstRho l) ((s + 1) ^ l)
      = Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
    rw [iwEps, mstRho_pow_eq l hl (s + 1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hE] at hξ
  by_contra hne
  have hb := mstEta_ne_zero_abs_iwRep d χ η hη2 s hne
  rw [norm_eq_abs_iwRep] at hξ
  have h2 : (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((d : ℝ) - χ)))
      = 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [h2] at hb
  linarith

lemma memLp_star_mstThetaEps (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    MemLp (mstStarThetaEps P i M ε) ⊤ haarT :=
  memLp_comp_iwRep (g := fun θ : ℝ => star (mstThetaEps P i M ε θ))
    (memLp_restrict_Ioc_of_continuous
      (Complex.continuous_conj.comp (continuous_mstThetaEps P i M ε)))

lemma memLp_mstThetaBump (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (i M s : ℕ)
    (ε : ℕ → ℂ) (hηml : MemLp (mstEta d χ η s) ⊤ haarT) :
    MemLp (mstThetaBump P d χ η i M s ε) ⊤ haarT :=
  memLp_mul_top (memLp_star_mstThetaEps P i M ε) hηml

/-- The level symbol of the signed block sums vanishes wherever the level bump does. -/
lemma mstThetaBump_eq_zero_of_mstEta_eq_zero (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (i M s : ℕ) (ε : ℕ → ℂ) {ζ : Circ} (h : mstEta d χ η s ζ = 0) :
    mstThetaBump P d χ η i M s ε ζ = 0 := by
  rw [mstThetaBump_apply, h, mul_zero]

/-! ## The arc-symbol difference -/

lemma arcSymbolLp_sdiff {φ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) {E F : Finset Circ}
    (hFE : F ⊆ E) :
    arcSymbolLp φ hφ (E \ F) = arcSymbolLp φ hφ E - arcSymbolLp φ hφ F := by
  refine Lp.ext ?_
  filter_upwards [arcSymbolLp_coeFn φ hφ (E \ F), arcSymbolLp_coeFn φ hφ E,
    arcSymbolLp_coeFn φ hφ F, Lp.coeFn_sub (arcSymbolLp φ hφ E) (arcSymbolLp φ hφ F)]
    with ξ h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3, arcSymbol_apply, arcSymbol_apply, arcSymbol_apply]
  exact eq_sub_of_add_eq (Finset.sum_sdiff hFE)

lemma opArc_sdiff {φ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) {E F : Finset Circ} (hFE : F ⊆ E)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    opArc φ hφ (E \ F) f hf = opArc φ hφ E f hf - opArc φ hφ F f hf := by
  simp only [opArc]
  rw [arcSymbolLp_sdiff (φ := φ) hφ hFE]
  exact (opMul_sub _ _ f hf).symm

/-! ## The signed block sum is `ℓᵖ`-bounded (MST Theorem 7, step (iii)) -/

lemma iteratedDeriv_two_star (η : ℝ → ℂ) :
    iteratedDeriv 2 (fun x : ℝ => star (η x)) = fun x => star (iteratedDeriv 2 η x) := by
  funext x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv.star']

/-- **MST Theorem 7, step (iii)**: the arc multiplier over the level-`s` annulus with the signed
lacunary profile-difference symbol times the level bump is `ℓᵖ`-bounded with a constant
`C log(s+2)`, uniformly in the signs and in the number of terms.  Two applications of the
Ionescu–Wainger range bound (MST Theorem 3) to the two nested arc sets `𝒰(s+1)` and `𝒰(s)`, with
the multiplier norms supplied by `MSTThetaBound` applied to the conjugate bump `star ∘ η`. -/
theorem mstThetaBump_opArc_lp (hTheta : MSTThetaBound) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    {p : ℝ} (hp : 1 < p) (r₀ : ℕ) (hr₀ : 2 ≤ r₀) (hp_hi : p ≤ 2 * (r₀ : ℝ))
    (hp_lo : (2 * (r₀ : ℝ)) / (2 * (r₀ : ℝ) - 1) ≤ p)
    (hηml : ∀ s : ℕ, MemLp (mstEta P.natDegree χ η s) ⊤ haarT) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ (i M' : ℕ) (ε : ℕ → ℂ),
      (∀ j : ℕ, ‖ε j‖ ≤ 1) → ∀ (f : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (opArc (mstThetaBump P P.natDegree χ η i M' s ε)
          (memLp_mstThetaBump P P.natDegree χ η i M' s ε (hηml s))
          (mstLevel l (s + 1) \ mstLevel l s) (⇑f) (memℓp_finsupp f))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨A₀, hA₀pos, hA₀⟩ := hTheta P hd hc r₀ hr₀
  have hRB : iwRangeBound := iwRangeBound_of_endpoint iwEndpoint2r_proof
  obtain ⟨Crb, hCrbpos, Nrb, hNrb⟩ :=
    hRB (mstRho l) (mstRho_pos l hl) r₀ hr₀
  obtain ⟨sn, hsn⟩ := mstEta_narrow (l := l) (hl := hl) (d := P.natDegree)
    (hd := by omega) (χ := χ) (hχd := by
      have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      linarith) (η := η) (hη2 := hη0)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨2 * Crb * (A₀ * M) / Real.log 2, div_pos (by positivity) hlog2pos,
    max sn (max Nrb 1), ?_⟩
  intro s hs i M' ε hε f
  have hsn' : sn ≤ s := le_trans (le_max_left _ _) hs
  have hN : Nrb ≤ s := by
    refine le_trans ?_ hs
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hs1 : 1 ≤ s := by
    refine le_trans ?_ hs
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hA0M : 0 ≤ A₀ * M := le_of_lt (mul_pos hA₀pos hM)
  let Ψ : Circ → ℂ := mstThetaBump P P.natDegree χ η i M' s ε
  have hΨml : MemLp Ψ ⊤ haarT :=
    memLp_mstThetaBump P P.natDegree χ η i M' s ε (hηml s)
  have hstar : (fun ξ : Circ => star (mstThetaSym P P.natDegree χ (fun x => star (η x))
      i M' s ε ξ)) = Ψ := by
    funext ξ
    dsimp only [Ψ]
    rw [mstThetaSym_apply, mstThetaBump_apply, mstEta_apply, mstEta_apply, star_mul, star_star]
    ring
  have hTheta' := hA₀ P.natDegree χ (fun x : ℝ => star (η x)) M hM
    (Complex.conjCLE.contDiff.comp hηc)
    (fun x => by rw [norm_star]; exact hηbd x)
    (fun x => by rw [deriv.star', norm_star]; exact hder1 x)
    (fun x => by rw [iteratedDeriv_two_star, norm_star]; exact hder2 x)
    (fun x hx => by rw [star_eq_zero]; exact hη0 x hx)
    i M' s ε hε
  have hMult : IWMult r₀ Ψ (A₀ * M) := hstar ▸ hTheta'.2
  have hMult' : IWMult r₀ (fun ξ => star (Ψ ξ)) (A₀ * M) := by
    have hpt : ∀ ξ : Circ, star (Ψ ξ)
        = mstThetaSym P P.natDegree χ (fun x => star (η x)) i M' s ε ξ := by
      intro ξ
      rw [← congrFun hstar ξ, star_star]
    rw [show (fun ξ : Circ => star (Ψ ξ))
        = mstThetaSym P P.natDegree χ (fun x => star (η x)) i M' s ε from funext hpt]
    exact hTheta'.1
  have hnarrow : ∀ ξ : Circ, iwEps (mstRho l) ((s + 1) ^ l) < ‖ξ‖ → Ψ ξ = 0 := by
    intro ξ hξ
    exact mstThetaBump_eq_zero_of_mstEta_eq_zero P P.natDegree χ η i M' s ε
      (hsn s hsn' ξ hξ)
  have hEpsPos : 0 < iwEps (mstRho l) ((s + 1) ^ l) := Real.exp_pos _
  have hN1 : Nrb ≤ (s + 1) ^ l := by
    calc Nrb ≤ s := hN
      _ ≤ s + 1 := by omega
      _ = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ l := Nat.pow_le_pow_right (by omega) hl
  have hb1 : MeasureTheory.eLpNorm (opArc Ψ hΨml (mstU l (s + 1)) (⇑f) (memℓp_finsupp f))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Crb * (A₀ * M))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have h := hNrb ((s + 1) ^ l) hN1 (iwEps (mstRho l) ((s + 1) ^ l)) hEpsPos le_rfl
      Ψ hΨml hnarrow (A₀ * M) hA0M hMult hMult' p hp_lo hp_hi (⇑f) (memℓp_finsupp f)
    refine eLpNorm_le_of_lintegral_rpow_le_count (lt_trans zero_lt_one hp) (by positivity) ?_
    simpa only [mstU_apply] using h
  have hN2 : Nrb ≤ s ^ l := le_trans hN (Nat.le_self_pow (by omega) s)
  have hEpsLe2 : iwEps (mstRho l) ((s + 1) ^ l) ≤ iwEps (mstRho l) (s ^ l) := by
    rw [iwEps, iwEps]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_le_neg_iff]
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (le_of_lt (mstRho_pos l hl))
    exact Nat.cast_le.mpr (Nat.pow_le_pow_left (by omega) l)
  have hb2 : MeasureTheory.eLpNorm (opArc Ψ hΨml (mstU l s) (⇑f) (memℓp_finsupp f))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Crb * (A₀ * M))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have h := hNrb (s ^ l) hN2 (iwEps (mstRho l) ((s + 1) ^ l)) hEpsPos hEpsLe2
      Ψ hΨml hnarrow (A₀ * M) hA0M hMult hMult' p hp_lo hp_hi (⇑f) (memℓp_finsupp f)
    refine eLpNorm_le_of_lintegral_rpow_le_count (lt_trans zero_lt_one hp) (by positivity) ?_
    simpa only [mstU_apply] using h
  have hle : mstU l s ⊆ mstU l (s + 1) := by
    have h := mstLevel_mono l s
    rwa [mstLevel_succ, mstLevel, if_neg (by omega : ¬ s = 0)] at h
  have heq : mstU l (s + 1) \ mstU l s = mstLevel l (s + 1) \ mstLevel l s := by
    rw [mstLevel_succ, mstLevel, if_neg (by omega : ¬ s = 0)]
  have hsdiff : opArc Ψ hΨml (mstLevel l (s + 1) \ mstLevel l s) (⇑f) (memℓp_finsupp f)
      = opArc Ψ hΨml (mstU l (s + 1)) (⇑f) (memℓp_finsupp f)
        - opArc Ψ hΨml (mstU l s) (⇑f) (memℓp_finsupp f) := by
    rw [← heq]
    exact opArc_sdiff hΨml hle _ _
  refine (le_of_eq (congrArg (fun t => MeasureTheory.eLpNorm t (ENNReal.ofReal p)
      MeasureTheory.Measure.count) hsdiff)).trans ?_
  refine (eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hp.le)).trans ?_
  refine (add_le_add hb1 hb2).trans ?_
  have hsum : ENNReal.ofReal (Crb * (A₀ * M))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count
      + ENNReal.ofReal (Crb * (A₀ * M))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count
      = ENNReal.ofReal (2 * Crb * (A₀ * M))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    ring
  rw [hsum]
  have hcoef : 2 * Crb * (A₀ * M)
      ≤ (2 * Crb * (A₀ * M) / Real.log 2) * Real.log ((s : ℝ) + 2) := by
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hlog : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hpos : 0 < 2 * Crb * (A₀ * M) := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2pos]
    exact mul_le_mul_of_nonneg_left hlog hpos.le
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoef) (bot_le)
/-! ## Linearity of the arc symbol in its function argument -/

/-- A `ℂ`-linear combination of functions on the circle. -/
def linComb {ι : Type*} (s : Finset ι) (c : ι → ℂ) (δ : ι → Circ → ℂ) : Circ → ℂ :=
  ∑ i ∈ s, c i • δ i

lemma linComb_empty {ι : Type*} (c : ι → ℂ) (δ : ι → Circ → ℂ) :
    linComb ∅ c δ = 0 := by
  simp only [linComb, Finset.sum_empty]

lemma linComb_insert {ι : Type*} [DecidableEq ι] {a : ι} {s : Finset ι} (ha : a ∉ s)
    (c : ι → ℂ) (δ : ι → Circ → ℂ) :
    linComb (insert a s) c δ = c a • δ a + linComb s c δ := by
  simp only [linComb, Finset.sum_insert ha]

lemma memLp_linComb {ι : Type*} (s : Finset ι) (c : ι → ℂ) (δ : ι → Circ → ℂ)
    (hδ : ∀ i, MemLp (δ i) ⊤ haarT) : MemLp (linComb s c δ) ⊤ haarT := by
  rw [show linComb s c δ = fun ζ : Circ => ∑ i ∈ s, (c i • δ i) ζ from by
    funext ζ
    simp only [linComb, Finset.sum_apply]]
  exact memLp_finsetSum s (fun i _ => (hδ i).const_smul (c i))

lemma arcSymbolLp_congr_memLp {φ : Circ → ℂ} (h1 h2 : MemLp φ ⊤ haarT) (E : Finset Circ) :
    arcSymbolLp φ h1 E = arcSymbolLp φ h2 E := by
  refine Lp.ext ?_
  filter_upwards [arcSymbolLp_coeFn φ h1 E, arcSymbolLp_coeFn φ h2 E] with ξ a b
  exact a.trans b.symm

lemma arcSymbolLp_congr {φ ψ : Circ → ℂ} (h : φ = ψ) (hφ : MemLp φ ⊤ haarT)
    (hψ : MemLp ψ ⊤ haarT) (E : Finset Circ) :
    arcSymbolLp φ hφ E = arcSymbolLp ψ hψ E := by
  subst h
  exact arcSymbolLp_congr_memLp hφ hψ E

lemma arcSymbol_zero (E : Finset Circ) : arcSymbol (0 : Circ → ℂ) E = 0 := by
  funext ξ
  simp only [arcSymbol_apply, Pi.zero_apply, Finset.sum_const_zero]

lemma arcSymbolLp_zero (h0 : MemLp (0 : Circ → ℂ) ⊤ haarT) (E : Finset Circ) :
    arcSymbolLp (0 : Circ → ℂ) h0 E = 0 := by
  refine Lp.ext ?_
  filter_upwards [arcSymbolLp_coeFn (0 : Circ → ℂ) h0 E] with ξ h1
  rw [h1, arcSymbol_zero]
  simp

lemma arcSymbolLp_sub {φ ψ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) (hψ : MemLp ψ ⊤ haarT)
    (E : Finset Circ) :
    arcSymbolLp φ hφ E - arcSymbolLp ψ hψ E = arcSymbolLp (φ - ψ) (hφ.sub hψ) E := by
  refine Lp.ext ?_
  filter_upwards [arcSymbolLp_coeFn φ hφ E, arcSymbolLp_coeFn ψ hψ E,
    arcSymbolLp_coeFn (φ - ψ) (hφ.sub hψ) E,
    Lp.coeFn_sub (arcSymbolLp φ hφ E) (arcSymbolLp ψ hψ E)] with ξ h1 h2 h3 h4
  rw [h4, Pi.sub_apply, h1, h2, arcSymbol_apply, arcSymbol_apply, h3, arcSymbol_apply]
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

lemma arcSymbolLp_add {φ ψ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) (hψ : MemLp ψ ⊤ haarT)
    (E : Finset Circ) :
    arcSymbolLp (φ + ψ) (hφ.add hψ) E = arcSymbolLp φ hφ E + arcSymbolLp ψ hψ E := by
  refine Lp.ext ?_
  filter_upwards [arcSymbolLp_coeFn (φ + ψ) (hφ.add hψ) E, arcSymbolLp_coeFn φ hφ E,
    arcSymbolLp_coeFn ψ hψ E, Lp.coeFn_add (arcSymbolLp φ hφ E) (arcSymbolLp ψ hψ E)]
    with ξ h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, arcSymbol_apply, arcSymbol_apply, arcSymbol_apply]
  simp only [Pi.add_apply, Finset.sum_add_distrib]

lemma arcSymbolLp_smul (c : ℂ) {φ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) (E : Finset Circ) :
    arcSymbolLp (c • φ) (hφ.const_smul c) E = c • arcSymbolLp φ hφ E := by
  refine Lp.ext ?_
  filter_upwards [arcSymbolLp_coeFn (c • φ) (hφ.const_smul c) E, arcSymbolLp_coeFn φ hφ E,
    Lp.coeFn_smul c (arcSymbolLp φ hφ E)] with ξ h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, arcSymbol_apply, arcSymbol_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

lemma arcSymbolLp_linComb {ι : Type*} (s : Finset ι) (c : ι → ℂ) (δ : ι → Circ → ℂ)
    (hδ : ∀ i, MemLp (δ i) ⊤ haarT) (E : Finset Circ) :
    ∀ (hsum : MemLp (linComb s c δ) ⊤ haarT),
      arcSymbolLp (linComb s c δ) hsum E = ∑ i ∈ s, c i • arcSymbolLp (δ i) (hδ i) E := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro hsum
      have h0 : MemLp (0 : Circ → ℂ) ⊤ haarT := by
        rw [linComb_empty] at hsum
        exact hsum
      rw [arcSymbolLp_congr (linComb_empty c δ) hsum h0 E, arcSymbolLp_zero h0 E,
        Finset.sum_empty]
  | insert a s ha ih =>
      intro hsum
      have hrest : MemLp (linComb s c δ) ⊤ haarT := memLp_linComb s c δ hδ
      have hsum' : MemLp (c a • δ a + linComb s c δ) ⊤ haarT :=
        ((hδ a).const_smul (c a)).add hrest
      rw [arcSymbolLp_congr (linComb_insert ha c δ) hsum hsum' E,
        arcSymbolLp_add ((hδ a).const_smul (c a)) hrest E, arcSymbolLp_smul (c a) (hδ a) E,
        ih hrest, Finset.sum_insert ha]

/-- **The signed sum of block differences of the `Π`-symbols is the arc symbol of
`mstThetaBump`** — the telescoping identity at the level of `L^∞(𝕋)`-classes. -/
lemma mstPiCls_block_signed_sum (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (i M s : ℕ)
    (ε : ℕ → ℂ) (E : Finset Circ) (hηml : MemLp (mstEta d χ η s) ⊤ haarT) :
    (∑ j ∈ Finset.range M, ε j •
        (arcSymbolLp (mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s)
            (memLp_mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s hηml) E
          - arcSymbolLp (mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s)
            (memLp_mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s hηml) E))
      = arcSymbolLp (mstThetaBump P d χ η i M s (fun j => star (ε j)))
          (memLp_mstThetaBump P d χ η i M s (fun j => star (ε j)) hηml) E := by
  set δ : ℕ → Circ → ℂ := fun j => mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s
      - mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s with hδdef
  set hδ : ∀ j, MemLp (δ j) ⊤ haarT := fun j =>
    (memLp_mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s hηml).sub
      (memLp_mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s hηml) with hδ2
  have hstep : ∀ j ∈ Finset.range M,
      ε j • (arcSymbolLp (mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s)
            (memLp_mstPiBump P d χ η (2 ^ ((j + 1) * 2 ^ i)) s hηml) E
          - arcSymbolLp (mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s)
            (memLp_mstPiBump P d χ η (2 ^ (j * 2 ^ i)) s hηml) E)
        = ε j • arcSymbolLp (δ j) (hδ j) E := by
    intro j hj
    rw [arcSymbolLp_sub]
  rw [Finset.sum_congr rfl hstep]
  have hfin : MemLp (linComb (Finset.range M) ε δ) ⊤ haarT :=
    memLp_linComb (Finset.range M) ε δ hδ
  rw [← arcSymbolLp_linComb (Finset.range M) ε δ hδ E hfin]
  refine arcSymbolLp_congr ?_ _ _ E
  funext ζ
  rw [linComb, Finset.sum_apply]
  simp only [hδdef, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact mstPiBump_block_sum P d χ η i M s ε ζ
/-! ## The `Π`-symbols and the signed block sums -/

/-- The `L^∞(𝕋)`-class of the level-`s` block symbol `star (Φ_N) · η_s` over the annulus. -/
def mstPiCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT) (N : ℕ) : Lp ℂ ⊤ haarT :=
  arcSymbolLp (mstPiBump P d χ η N s) (memLp_mstPiBump P d χ η N s hηml)
    (mstLevel l (s + 1) \ mstLevel l s)

lemma mstPiCls_apply (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT) (N : ℕ) :
    mstPiCls P l d χ η s hηml N
      = arcSymbolLp (mstPiBump P d χ η N s) (memLp_mstPiBump P d χ η N s hηml)
          (mstLevel l (s + 1) \ mstLevel l s) := rfl

/-- The signed sum of the block differences of the `Π`-operators is the arc multiplier with the
signed lacunary symbol `mstThetaBump`. -/
lemma opMulFinsuppLM_block_signed_sum (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT) (i M : ℕ) (ε : ℕ → ℂ) (g : ℤ →₀ ℂ) :
    (fun m : ℤ => ∑ j ∈ Finset.range M,
        ε j * ((opMulFinsuppLM (mstPiCls P l d χ η s hηml (2 ^ ((j + 1) * 2 ^ i)))
          - opMulFinsuppLM (mstPiCls P l d χ η s hηml (2 ^ (j * 2 ^ i)))) g m))
      = opArc (mstThetaBump P d χ η i M s (fun j => star (ε j)))
          (memLp_mstThetaBump P d χ η i M s (fun j => star (ε j)) hηml)
          (mstLevel l (s + 1) \ mstLevel l s) (⇑g) (memℓp_finsupp g) := by
  have h1 : (fun m : ℤ => ∑ j ∈ Finset.range M,
        ε j * ((opMulFinsuppLM (mstPiCls P l d χ η s hηml (2 ^ ((j + 1) * 2 ^ i)))
          - opMulFinsuppLM (mstPiCls P l d χ η s hηml (2 ^ (j * 2 ^ i)))) g m))
      = fun m : ℤ => ∑ j ∈ Finset.range M,
          ε j * (opMul (mstPiCls P l d χ η s hηml (2 ^ ((j + 1) * 2 ^ i))
            - mstPiCls P l d χ η s hηml (2 ^ (j * 2 ^ i))) (⇑g) (memℓp_finsupp g) m) := by
    funext m
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [LinearMap.sub_apply, opMulFinsuppLM_apply, opMulFinsuppLM_apply, opMul_sub]
  rw [h1]
  have h2 : (fun m : ℤ => ∑ j ∈ Finset.range M,
        ε j * (opMul (mstPiCls P l d χ η s hηml (2 ^ ((j + 1) * 2 ^ i))
          - mstPiCls P l d χ η s hηml (2 ^ (j * 2 ^ i))) (⇑g) (memℓp_finsupp g) m))
      = opMul (∑ j ∈ Finset.range M, ε j •
          (mstPiCls P l d χ η s hηml (2 ^ ((j + 1) * 2 ^ i))
            - mstPiCls P l d χ η s hηml (2 ^ (j * 2 ^ i)))) (⇑g) (memℓp_finsupp g) := by
    funext m
    rw [opMul_finset_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h2]
  have h3 : (∑ j ∈ Finset.range M, ε j •
        (mstPiCls P l d χ η s hηml (2 ^ ((j + 1) * 2 ^ i))
          - mstPiCls P l d χ η s hηml (2 ^ (j * 2 ^ i))))
      = arcSymbolLp (mstThetaBump P d χ η i M s (fun j => star (ε j)))
          (memLp_mstThetaBump P d χ η i M s (fun j => star (ε j)) hηml)
          (mstLevel l (s + 1) \ mstLevel l s) := by
    simp only [mstPiCls]
    exact mstPiCls_block_signed_sum P l d χ η i M s ε _ hηml
  rw [h3]
  rfl

/-- **MST Theorem 7, step (iv): the level-`i` Rademacher–Menshov square function of the block
operators is `ℓᵖ`-bounded with constant `C log(s+2)`.**  Marcinkiewicz–Zygmund
(`mz_finsupp_sqfun`) reduces to the signed sums, whose bound is the Ionescu–Wainger bound
`mstThetaBump_opArc_lp`. -/
theorem mst_lvl_level_bound (hTheta : MSTThetaBound) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    {p : ℝ} (hp : 1 < p) (r₀ : ℕ) (hr₀ : 2 ≤ r₀) (hp_hi : p ≤ 2 * (r₀ : ℝ))
    (hp_lo : (2 * (r₀ : ℝ)) / (2 * (r₀ : ℝ) - 1) ≤ p)
    (hηml : ∀ s : ℕ, MemLp (mstEta P.natDegree χ η s) ⊤ haarT) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ (i : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal (rmLevel (mstKappa P s) i
          (fun j : ℕ => ‖opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ j)) g m‖)))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨Ciw, hCiwpos, siw, hIWi⟩ :=
    mstThetaBump_opArc_lp hTheta P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2
      hp r₀ hr₀ hp_hi hp_lo hηml
  obtain ⟨Cmz, hCmzpos, hmz⟩ := mz_finsupp_sqfun (p := p) hp.le
  refine ⟨Cmz * Ciw, mul_pos hCmzpos hCiwpos, max siw 1, ?_⟩
  intro s hs i g
  have hsiw : siw ≤ s := le_trans (le_max_left _ _) hs
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  set M' : ℕ := 2 ^ (mstKappa P s - i) with hM'def
  obtain ⟨hCiwnn, hlogpos⟩ : 0 ≤ Ciw * Real.log ((s : ℝ) + 2) ∧
      0 < Real.log ((s : ℝ) + 2) :=
    ⟨le_of_lt (mul_pos hCiwpos (Real.log_pos (by linarith))), Real.log_pos (by linarith)⟩
  have hsign : ∀ (ε : Fin M' → Bool) (g' : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => ∑ j : Fin M',
          (if ε j then (1 : ℂ) else -1) *
            ((opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (((j : ℕ) + 1) * 2 ^ i)))
                - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j : ℕ) * 2 ^ i))))
              g' m)) (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g') (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro ε g'
    set esgn : ℕ → ℂ := fun j => if h : j < M' then (if ε ⟨j, h⟩ then (1 : ℂ) else -1) else 0
      with heps
    have hpoint : (fun m : ℤ => ∑ j : Fin M', (if ε j then (1 : ℂ) else -1) *
          ((opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (((j : ℕ) + 1) * 2 ^ i)))
              - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j : ℕ) * 2 ^ i))))
            g' m))
        = fun m : ℤ => ∑ j ∈ Finset.range M', esgn j *
            ((opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j + 1) * 2 ^ i)))
                - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i))))
              g' m) := by
      funext m
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => esgn j * ((opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s)
            (2 ^ ((j + 1) * 2 ^ i)))
          - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i)))) g' m)) M']
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [heps]
      rw [dif_pos j.isLt]
    rw [hpoint]
    rw [opMulFinsuppLM_block_signed_sum P l P.natDegree χ η s (hηml s) i M' esgn g']
    refine hIWi s hsiw i M' (fun j => star (esgn j)) ?_ g'
    intro j
    have hEsgn : esgn j
        = (if h : j < M' then (if ε ⟨j, h⟩ then (1 : ℂ) else -1) else 0) := by
      rw [heps]
    rw [hEsgn]
    by_cases h : j < M'
    · rw [dif_pos h]
      by_cases h2 : ε ⟨j, h⟩
      · rw [if_pos h2]; simp
      · rw [if_neg h2]; simp
    · rw [dif_neg h]; simp
  have hmz' := hmz (fun j : Fin M' =>
      (opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (((j : ℕ) + 1) * 2 ^ i)))
        - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j : ℕ) * 2 ^ i)))))
    (Ciw * Real.log ((s : ℝ) + 2)) hCiwnn hsign g
  rw [show Cmz * (Ciw * Real.log ((s : ℝ) + 2))
      = (Cmz * Ciw) * Real.log ((s : ℝ) + 2) by ring] at hmz'
  refine le_trans ?_ hmz'
  refine eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun m => ?_)
  rw [enorm_eq_self, enorm_eq_self]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rmLevel]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ‖(opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j + 1) * 2 ^ i)))
        - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i)))) g m‖ ^ 2) M']
  refine Finset.sum_le_sum (fun j hj => ?_)
  have h1 : |‖opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j + 1) * 2 ^ i))) g m‖
        - ‖opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i))) g m‖|
      ≤ ‖(opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j + 1) * 2 ^ i)))
        - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i)))) g m‖ := by
    rw [← Real.norm_eq_abs]
    exact abs_norm_sub_norm_le _ _
  calc |‖opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j + 1) * 2 ^ i))) g m‖
        - ‖opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i))) g m‖| ^ 2
      ≤ ‖(opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ ((j + 1) * 2 ^ i)))
        - opMulFinsuppLM (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ (j * 2 ^ i)))) g m‖ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2

/-! ## The discrete average `M_J` as a positive contraction -/

lemma lintegral_count_add_const (f : ℤ → ℝ≥0∞) (c : ℤ) :
    ∫⁻ m : ℤ, f (m + c) ∂MeasureTheory.Measure.count
      = ∫⁻ m : ℤ, f m ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact Equiv.tsum_eq (Equiv.addRight c) f

lemma eLpNorm'_count_add_const (f : ℤ → ℝ≥0∞) (q : ℝ) (c : ℤ) :
    MeasureTheory.eLpNorm' (fun m : ℤ => f (m + c)) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm' f q MeasureTheory.Measure.count := by
  simp only [MeasureTheory.eLpNorm', enorm_eq_self]
  congr 1
  exact lintegral_count_add_const (fun m : ℤ => f m ^ q) c

lemma eLpNorm_count_add_const (f : ℤ → ℝ≥0∞) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤)
    (c : ℤ) :
    MeasureTheory.eLpNorm (fun m : ℤ => f (m + c)) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm f q MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_eLpNorm' hq0 hqt AEStronglyMeasurable.of_discrete,
    MeasureTheory.eLpNorm_eq_eLpNorm' hq0 hqt AEStronglyMeasurable.of_discrete]
  exact eLpNorm'_count_add_const f q.toReal c

/-- **The norm bound for the discrete average**: `‖M_J h m‖ ≤ J⁻¹ Σ_{i<J} ‖h (m + P(i))‖`. -/
lemma enorm_discAvgZC_le (P : Polynomial ℤ) (J : ℕ) (h : ℤ → ℂ) (m : ℤ) :
    ‖discAvgZC P J h m‖ₑ ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹)
      * ∑ i ∈ Finset.range J, ‖h (m + P.eval (i : ℤ))‖ₑ := by
  have hstep : ‖discAvgZC P J h m‖ ≤ ((J : ℕ) : ℝ)⁻¹
      * ∑ i ∈ Finset.range J, ‖h (m + P.eval (i : ℤ))‖ := by
    rw [discAvgZC]
    calc ‖((J : ℂ)⁻¹) * ∑ i ∈ Finset.range J, h (m + P.eval (i : ℤ))‖
        ≤ ‖((J : ℂ)⁻¹)‖ * ‖∑ i ∈ Finset.range J, h (m + P.eval (i : ℤ))‖ := norm_mul_le _ _
      _ = ((J : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ Finset.range J, h (m + P.eval (i : ℤ))‖ := by
          rw [norm_inv, Complex.norm_natCast, inv_eq_one_div]
      _ ≤ ((J : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range J, ‖h (m + P.eval (i : ℤ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  refine le_trans (le_of_eq (ofReal_norm _).symm) ?_
  refine le_trans (ENNReal.ofReal_le_ofReal hstep) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  simp only [ofReal_norm]


/-- **The discrete average `M_J` is a contraction on the maximal function**: the `ℓᵖ` norm of
`sup_k |M_J (T_k)|` is bounded by that of `sup_k |T_k|`, because `M_J` is a positive average of
translations (the counting measure is translation invariant and `M_J` is an `ℓᵖ`-contraction). -/
lemma eLpNorm_discAvg_iSup_le (P : Polynomial ℤ) (J K : ℕ) (hJ : 0 < J) (T : ℕ → ℤ → ℂ)
    {p : ℝ} (hp : 1 ≤ p) :
    MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range K, ‖discAvgZC P J (T k) m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range K, ‖T k m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  set U : ℤ → ℝ≥0∞ := fun m => ⨆ k ∈ Finset.range K, ‖T k m‖ₑ with hU
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hppos
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint : ∀ m, (⨆ k ∈ Finset.range K, ‖discAvgZC P J (T k) m‖ₑ)
      ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ)) := by
    intro m
    refine iSup₂_le (fun k hk => ?_)
    refine (enorm_discAvgZC_le P J (T k) m).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum (fun i hi => le_iSup₂ (f := fun k _ => ‖T k (m + P.eval (i : ℤ))‖ₑ) k hk)
  have hpoint' : ∀ m : ℤ,
      ‖(⨆ k ∈ Finset.range K, ‖discAvgZC P J (T k) m‖ₑ)‖ₑ
        ≤ ‖ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * ∑ i ∈ Finset.range J,
            U (m + P.eval (i : ℤ))‖ₑ := by
    intro m
    rw [enorm_eq_self, enorm_eq_self]
    exact hpoint m
  have h1 : MeasureTheory.eLpNorm (fun m : ℤ =>
        ⨆ k ∈ Finset.range K, ‖discAvgZC P J (T k) m‖ₑ) (ENNReal.ofReal p)
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * MeasureTheory.eLpNorm
          (fun m : ℤ => ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ))) (ENNReal.ofReal p)
          MeasureTheory.Measure.count := by
    refine (eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete hpoint').trans (le_of_eq ?_)
    exact Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal hc hp0 hpt
  have h2 : MeasureTheory.eLpNorm (fun m : ℤ => ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ∑ i ∈ Finset.range J, MeasureTheory.eLpNorm
          (fun m : ℤ => U (m + P.eval (i : ℤ))) (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
      (ENNReal.one_le_ofReal.mpr hp) (fun i _ => (measurable_of_countable _).aemeasurable)
  have h3 : ∀ i : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => U (m + P.eval (i : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count := fun i =>
    eLpNorm_count_add_const U hp0 hpt (P.eval (i : ℤ))
  have hsum : (∑ i ∈ Finset.range J, MeasureTheory.eLpNorm (fun m : ℤ => U (m + P.eval (i : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count)
      = (J : ℝ≥0∞) * MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have harith : ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * (J : ℝ≥0∞)
      = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (((J : ℕ) : ℝ)⁻¹ * (J : ℝ)) = 1 by field_simp]
    simp
  calc MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range K, ‖discAvgZC P J (T k) m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) * MeasureTheory.eLpNorm
          (fun m : ℤ => ∑ i ∈ Finset.range J, U (m + P.eval (i : ℤ))) (ENNReal.ofReal p)
          MeasureTheory.Measure.count := h1
    _ ≤ ENNReal.ofReal (((J : ℕ) : ℝ)⁻¹) *
          ((J : ℝ≥0∞) * MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq hsum)) bot_le
    _ = MeasureTheory.eLpNorm U (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [← mul_assoc, harith, one_mul]


/-! ## The trivial `ℓʳ` bound for the level model (summable coefficient kernel) -/

/-- The Fourier coefficients of the level model `ν^s_{2^n}`: the translated
profile-times-bump `mstPiBump` with the weights `star (G β) star (fourier m β)`. -/
theorem fourierCoeff_mstNuS_eq (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT) (m : ℤ) :
    fourierCoeff (mstNuS P l d χ η n s) m
      = (∑ β ∈ mstLevel l (s + 1) \ mstLevel l s, star (mstG P β) * star (fourier m β))
          * fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m := by
  classical
  have hmem : MemLp (mstPiBump P d χ η (2 ^ n) s) ⊤ haarT :=
    memLp_mstPiBump P d χ η (2 ^ n) s hηml
  have hpt : mstNuS P l d χ η n s =ᵐ[haarT]
      fun ξ => ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
        star (mstG P β) * arcTranslate β (mstPiBump P d χ η (2 ^ n) s) ξ := by
    filter_upwards with ξ
    rw [mstNuS_apply]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    simp only [mstPiBump_apply, arcTranslate_apply]
  have hint : ∀ β ∈ mstLevel l (s + 1) \ mstLevel l s,
      Integrable (fun ξ : Circ => star (mstG P β)
        * arcTranslate β (mstPiBump P d χ η (2 ^ n) s) ξ) haarT := by
    intro β _
    exact ((memLp_arcTranslate hmem β).integrable le_top).const_mul _
  have hfun : (fun ξ => ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
        star (mstG P β) * arcTranslate β (mstPiBump P d χ η (2 ^ n) s) ξ)
      = ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
        (fun ξ => star (mstG P β) * arcTranslate β (mstPiBump P d χ η (2 ^ n) s) ξ) := by
    funext ξ; simp
  rw [fourierCoeff_congr_ae hpt, hfun, fourierCoeff.sum _ _ hint]
  simp only [Finset.sum_apply]
  have hterm : ∀ β : Circ,
      fourierCoeff (fun ξ => star (mstG P β)
        * arcTranslate β (mstPiBump P d χ η (2 ^ n) s) ξ) m
        = star (mstG P β) * (star (fourier m β)
            * fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m) := by
    intro β
    rw [fourierCoeff.const_mul,
      fourierCoeff_eq_integral_mul_star (arcTranslate β (mstPiBump P d χ η (2 ^ n) s)) m,
      fourierCoeff_arcTranslate (mstPiBump P d χ η (2 ^ n) s) hmem β m,
      fourierCoeff_eq_integral_mul_star (mstPiBump P d χ η (2 ^ n) s) m]
  rw [Finset.sum_congr rfl (fun β _ => hterm β)]
  rw [Finset.sum_congr rfl (fun β _ => (mul_assoc _ _ _).symm), Finset.sum_mul]

/-- The `ℓ¹` norm of the coefficient kernel of the level model `ν^s_{2^n}` is at most
`#annulus` times that of the profile-times-bump. -/
theorem tsum_fourierCoeff_mstNuS_le (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ)
    (hηml : MemLp (mstEta d χ η s) ⊤ haarT) {K : ℝ}
    (hK : Summable (fun m : ℤ => ‖fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m‖))
    (hKb : (∑' m : ℤ, ‖fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m‖) ≤ K) :
    Summable (fun m : ℤ => ‖fourierCoeff (mstNuS P l d χ η n s) m‖) ∧
      (∑' m : ℤ, ‖fourierCoeff (mstNuS P l d χ η n s) m‖)
        ≤ (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * K := by
  have hpt : ∀ m : ℤ, ‖fourierCoeff (mstNuS P l d χ η n s) m‖
      ≤ (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ))
          * ‖fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m‖ := by
    intro m
    rw [fourierCoeff_mstNuS_eq P l d χ η n s hηml m, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖∑ β ∈ mstLevel l (s + 1) \ mstLevel l s, star (mstG P β) * star (fourier m β)‖
        ≤ ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s, ‖star (mstG P β) * star (fourier m β)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _β ∈ mstLevel l (s + 1) \ mstLevel l s, (1 : ℝ) := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [norm_mul]
          have h2 : ‖star ((fourier m) β)‖ = (1 : ℝ) := by
            simpa using norm_fourier_apply' m β
          rw [h2, mul_one]
          simpa using mstG_norm_le_one P β
      _ = (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) := by simp
  have hsum : Summable (fun m : ℤ => ‖fourierCoeff (mstNuS P l d χ η n s) m‖) :=
    Summable.of_nonneg_of_le (f := fun m : ℤ => (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ))
        * ‖fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m‖)
      (g := fun m : ℤ => ‖fourierCoeff (mstNuS P l d χ η n s) m‖)
      (fun m => norm_nonneg _) (fun m => hpt m) (hK.mul_left _)
  refine ⟨hsum, ?_⟩
  calc (∑' m : ℤ, ‖fourierCoeff (mstNuS P l d χ η n s) m‖)
      ≤ ∑' m : ℤ, (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ))
          * ‖fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m‖ :=
        Summable.tsum_le_tsum (fun m => hpt m) hsum (hK.mul_left _)
    _ = (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ))
          * ∑' m : ℤ, ‖fourierCoeff (mstPiBump P d χ η (2 ^ n) s) m‖ := tsum_mul_left
    _ ≤ (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) * K :=
        mul_le_mul_of_nonneg_left hKb (Nat.cast_nonneg _)


/-! ## The Rademacher–Menshov reduction of the `sup` -/

lemma rm_iSup_bound (κ : ℕ) (T : ℕ → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) {p : ℝ} (hp : 1 ≤ p)
    (g : ℤ →₀ ℂ) :
    MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range (2 ^ κ + 1), ‖T k g m‖ₑ)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun m : ℤ => ‖T 0 g m‖ₑ) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
        + ENNReal.ofReal 2 * ∑ i ∈ Finset.range (κ + 1),
            MeasureTheory.eLpNorm (fun m : ℤ =>
              ENNReal.ofReal (rmLevel κ i (fun j => ‖T j g m‖))) (ENNReal.ofReal p)
              MeasureTheory.Measure.count := by
  have h := rmELpNormSupLe (μ := MeasureTheory.Measure.count) κ hp
    (fun j (m : ℤ) => ‖T j g m‖) (fun j => (measurable_of_countable _).aemeasurable)
    (fun j m => norm_nonneg _)
  simpa only [ofReal_norm] using h

/-! ## The arithmetic of the Rademacher–Menshov levels -/

lemma mstKappa_add_one_le (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    ∃ Sκ : ℕ, ∀ s : ℕ, Sκ ≤ s → mstKappa P s + 1 ≤ s + 1 := by
  obtain ⟨N₁, hN₁⟩ := rpow_ten_add_one_le_mul (1 / (40 * (P.natDegree : ℝ))) (by positivity)
  refine ⟨max N₁ (40 * P.natDegree + 1), fun s hs => ?_⟩
  have hdR1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hsN : N₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs40 : 40 * P.natDegree + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsR : (40 * (P.natDegree : ℝ)) ≤ (s : ℝ) := by
    have : ((40 * P.natDegree + 1 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs40
    push_cast at this
    linarith
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hx : ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ 1 / (40 * (P.natDegree : ℝ)) * (s : ℝ) :=
    hN₁ s hsN
  have hfloor : ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1
      ≤ 2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    have h1 : ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have h2 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / 10 : ℝ) := (Real.one_rpow _).symm
        _ ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    linarith
  have hκ : (mstKappa P s : ℝ) ≤ (s : ℝ) := by
    rw [mstKappa]
    push_cast
    calc (20 : ℝ) * (P.natDegree : ℝ) * (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1)
        ≤ 20 * (P.natDegree : ℝ) * (2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
          have : (0 : ℝ) ≤ 20 * (P.natDegree : ℝ) := by positivity
          nlinarith [hfloor]
      _ ≤ 20 * (P.natDegree : ℝ) * (2 * (1 / (40 * (P.natDegree : ℝ)) * (s : ℝ))) := by
          have h3 : 2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
              ≤ 2 * (1 / (40 * (P.natDegree : ℝ)) * (s : ℝ)) := by linarith
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (s : ℝ) := by
          field_simp
          ring
  have : (mstKappa P s + 1 : ℕ) ≤ s + 1 := by
    have h4 : ((mstKappa P s + 1 : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  exact this

/-- For every `B > 0` and all large `s`, `(s+1)^{1/10} ≤ B·√(s+1)`. -/
lemma rpow_ten_le_mul_sqrt (B : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ B * Real.sqrt ((s : ℝ) + 1) := by
  refine ⟨⌈(1 / B) ^ (5 / 2 : ℝ)⌉₊, fun s hs => ?_⟩
  have hx : (0 : ℝ) < ((s : ℝ) + 1) := by positivity
  have hceil : (1 / B) ^ (5 / 2 : ℝ) ≤ ((s : ℝ) + 1) := by
    have h1 : ((⌈(1 / B) ^ (5 / 2 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (show ⌈(1 / B) ^ (5 / 2 : ℝ)⌉₊ ≤ s from hs)
    linarith [Nat.le_ceil ((1 / B) ^ (5 / 2 : ℝ))]
  have hkey : ((s : ℝ) + 1) ^ (-(2 / 5 : ℝ)) ≤ B := by
    have h : (1 / B) ≤ ((s : ℝ) + 1) ^ (2 / 5 : ℝ) := by
      have h5 := Real.rpow_le_rpow (by positivity) hceil (by norm_num : (0 : ℝ) ≤ 2 / 5)
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / B),
        show (5 / 2 : ℝ) * (2 / 5) = 1 by norm_num, Real.rpow_one] at h5
      exact h5
    rw [Real.rpow_neg hx.le, inv_le_comm₀ (Real.rpow_pos_of_pos hx _) hB]
    simpa only [one_div] using h
  have hsplit : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      = Real.sqrt ((s : ℝ) + 1) * ((s : ℝ) + 1) ^ (-(2 / 5 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    norm_num
  rw [hsplit]
  calc Real.sqrt ((s : ℝ) + 1) * ((s : ℝ) + 1) ^ (-(2 / 5 : ℝ))
      ≤ Real.sqrt ((s : ℝ) + 1) * B := mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg _)
    _ = B * Real.sqrt ((s : ℝ) + 1) := by ring

/-- **The error sum is summable**: `2^{κ_s+1} · exp(−√(s+1)/4) ≤ 1` for all large `s`
(`κ_s ≍ (s+1)^{1/10}` is subexponential against `exp(−√·/4)`). -/
lemma mstKappa_exp_le_one (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
      (2 : ℝ) ^ (mstKappa P s + 1) * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)) ≤ 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  obtain ⟨N₁, hN₁⟩ := rpow_ten_le_mul_sqrt
    (1 / (320 * (P.natDegree : ℝ) * Real.log 2)) (by positivity)
  refine ⟨max N₁ (4096 * P.natDegree ^ 2 + 1), fun s hs => ?_⟩
  have hdR1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hsN : N₁ ≤ s := le_trans (le_max_left _ _) hs
  have hsbig : 4096 * P.natDegree ^ 2 + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hpow : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      ≤ 1 / (320 * (P.natDegree : ℝ) * Real.log 2) * Real.sqrt ((s : ℝ) + 1) := hN₁ s hsN
  have hfloor : ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1
      ≤ 2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    have h1 : ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have h2 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / 10 : ℝ) := (Real.one_rpow _).symm
        _ ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
    linarith
  have hκ : (mstKappa P s : ℝ) * Real.log 2 ≤ Real.sqrt ((s : ℝ) + 1) / 8 := by
    rw [mstKappa]
    push_cast
    calc (20 : ℝ) * (P.natDegree : ℝ) * (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1)
          * Real.log 2
        ≤ 20 * (P.natDegree : ℝ) * (2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ)) * Real.log 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hlog2.le
          exact mul_le_mul_of_nonneg_left hfloor (by positivity)
      _ = 40 * (P.natDegree : ℝ) * Real.log 2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by ring
      _ ≤ 40 * (P.natDegree : ℝ) * Real.log 2
            * (1 / (320 * (P.natDegree : ℝ) * Real.log 2) * Real.sqrt ((s : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = Real.sqrt ((s : ℝ) + 1) / 8 := by
          have hd0 : (P.natDegree : ℝ) ≠ 0 := by positivity
          field_simp
          ring_nf
  have hsqrt64 : (64 : ℝ) ≤ Real.sqrt ((s : ℝ) + 1) := by
    have h3 : 4096 * P.natDegree ^ 2 ≤ s := by omega
    have h4 : ((4096 * P.natDegree ^ 2 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast h3
    push_cast at h4
    have h1 : (64 : ℝ) ^ 2 ≤ (s : ℝ) + 1 := by nlinarith [hdR1, h4]
    nlinarith [h1, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1),
      Real.sqrt_nonneg ((s : ℝ) + 1)]
  have h2 : (2 : ℝ) ^ (mstKappa P s + 1)
      = Real.exp (((mstKappa P s : ℝ) + 1) * Real.log 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) (mstKappa P s + 1),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have key : (2 : ℝ) ^ (mstKappa P s + 1) * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4))
      = Real.exp (((mstKappa P s : ℝ) + 1) * Real.log 2 - Real.sqrt ((s : ℝ) + 1) / 4) := by
    rw [h2, ← Real.exp_add, sub_eq_add_neg]
  rw [key, Real.exp_le_one_iff]
  have h64 : Real.log 2 ≤ Real.sqrt ((s : ℝ) + 1) / 64 := by linarith
  linarith [hκ, h64]

lemma mstKappa_mono (P : Polynomial ℤ) : Monotone (mstKappa P) := by
  intro a b hab
  unfold mstKappa
  refine Nat.mul_le_mul_left _ ?_
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have h : ((a : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ ((b : ℝ) + 1) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  exact Nat.add_le_add_right (Nat.floor_mono h) 1

lemma mstU_card_mono (l : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (mstU l a).card ≤ (mstU l b).card := by
  refine Finset.card_le_card ?_
  rw [mstU_apply, mstU_apply]
  exact sigmaN_nested (mstRho l) (Nat.pow_le_pow_left hab l)

lemma eLpNorm_ofReal_norm (x : ℤ → ℂ) (q : ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal ‖x m‖) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm x q MeasureTheory.Measure.count := by
  rw [← MeasureTheory.eLpNorm_enorm x AEStronglyMeasurable.of_discrete]
  congr 1
  funext m
  exact ofReal_norm _

lemma eLpNorm_enorm (x : ℤ → ℂ) (q : ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun m : ℤ => ‖x m‖ₑ) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm x q MeasureTheory.Measure.count := by
  exact MeasureTheory.eLpNorm_enorm x AEStronglyMeasurable.of_discrete

/-- The `ℓᵖ` norm of a finitely supported sequence read through `opMul` is the norm of the
`opMulFinsuppLM` image (definitional unfolding, packaged to avoid `delta` in rewrites). -/
lemma eLpNorm_opMulFinsuppLM (Φ : Lp ℂ ⊤ haarT) (g : ℤ →₀ ℂ) (q : ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ) q MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (opMulFinsuppLM Φ g) q MeasureTheory.Measure.count :=
  eLpNorm_enorm (opMulFinsuppLM Φ g) q


end

end Work.BourgainPlan.Maximal
