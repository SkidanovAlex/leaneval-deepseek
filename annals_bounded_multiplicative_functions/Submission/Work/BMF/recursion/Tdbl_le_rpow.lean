import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.TdblDefs
import Submission.Work.BMF.recursion.Weyl_factor
import Submission.Work.BMF.recursion.integral_normSq_eq_card
import Submission.Work.BMF.recursion.norm_sum_pow_le
import Submission.Vinogradov.Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The first Hölder step of Wooley's recursion: `Tdbl ≤ J_{S,k}(Q)^{1-1/S}`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.BMF.recursion

noncomputable section

open MeasureTheory
open Classical

/-- Value of a `Fin` constructed by `Fin.mk`. -/
lemma fin_val_mk {n a : ℕ} (h : a < n) : ((⟨a, h⟩ : Fin n)).val = a := rfl

/-! ## Elementary facts about the two Weyl sums involved -/

private lemma continuous_Weyl (k Q : ℕ) : Continuous (Weyl k Q) := by
  show Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
    ∑ x : Tup 1 Q, UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ)
  exact continuous_finsetSum _ (fun x _ =>
    (UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x)).continuous)

lemma continuous_Duo (k Q : ℕ) : Continuous (Duo k Q) := by
  show Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
    ∑ x ∈ Finset.Icc 1 Q, UnitAddTorus.mFourier ((2 : ℤ) • mom1 k x) θ)
  exact continuous_finsetSum _ (fun x _ =>
    (UnitAddTorus.mFourier ((2 : ℤ) • mom1 k x)).continuous)

lemma memLp_torus_of_continuous {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : UnitAddTorus (Fin (k + 1)) → E} (hf : Continuous f) (p : ENNReal) :
    MemLp f p (volume : Measure (UnitAddTorus (Fin (k + 1)))) := by
  refine Continuous.memLp_of_hasCompactSupport hf ?_
  unfold HasCompactSupport tsupport
  exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (Set.subset_univ _)

lemma isProbabilityMeasure_torus_volume (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  rw [volume_eq_pi d]
  infer_instance

lemma integral_one_prob {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : (∫ _x : α, (1 : ℝ) ∂μ) = 1 := by
  rw [MeasureTheory.integral_const]
  simp [Measure.real_def]

lemma Duo_apply (k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    Duo k Q θ = ∑ a : Finset.Icc 1 Q, UnitAddTorus.mFourier ((2 : ℤ) • mom1 k a.1) θ := by
  rw [Duo]
  exact (Finset.sum_attach (Finset.Icc 1 Q)
    (fun v => UnitAddTorus.mFourier ((2 : ℤ) • mom1 k v) θ)).symm

lemma Duo_pow_eq (S k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    (Duo k Q θ) ^ S
      = ∑ v : Tup S Q,
          UnitAddTorus.mFourier ((2 : ℤ) • Submission.Vinogradov.powerSums k v) θ := by
  rw [Duo_apply k Q θ]
  rw [← sum_fin_fun_prod
    (fun a : Finset.Icc 1 Q => UnitAddTorus.mFourier ((2 : ℤ) • mom1 k a.1) θ) S]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← mFourier_finset_sum Finset.univ (fun i : Fin S => (2 : ℤ) • mom1 k (v i).1) θ]
  have h : (∑ i : Fin S, (2 : ℤ) • mom1 k (v i).1)
      = (2 : ℤ) • Submission.Vinogradov.powerSums k v := by
    rw [← Finset.smul_sum, ← powerSums_eq_sum_mom1 (k := k) v]
  rw [h]

lemma key_pointwise (S k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    ‖Submission.Vinogradov.ExpSum (s := S - 2) (k := k) (X := Q) θ * Duo k Q θ‖ ^ 2
      = Wnorm k Q θ ^ (2 * (S - 2)) * Dnorm k Q θ ^ 2 := by
  have hW : ‖Submission.Vinogradov.ExpSum (s := S - 2) (k := k) (X := Q) θ‖
      = Wnorm k Q θ ^ (S - 2) := by
    rw [Weyl_factor k (S - 2) Q]
    simp [Wnorm, norm_pow]
  rw [norm_mul, mul_pow, hW]
  have h1 : (Wnorm k Q θ ^ (S - 2)) ^ 2 = Wnorm k Q θ ^ (2 * (S - 2)) := by
    rw [← pow_mul, Nat.mul_comm (S - 2) 2]
  rw [h1]
  rfl

/-! ## The two mean-value identities -/

theorem Weyl_pow_integral (S k Q : ℕ) :
    (∫ θ : UnitAddTorus (Fin (k + 1)), (Wnorm k Q θ) ^ (2 * S))
      = LeanEval.NumberTheory.VinogradovMeanValue.J S k Q := by
  have hpw : ∀ θ : UnitAddTorus (Fin (k + 1)),
      Wnorm k Q θ ^ (2 * S)
        = ‖Submission.Vinogradov.ExpSum (s := S) (k := k) (X := Q) θ‖ ^ 2 := by
    intro θ
    have hW : ‖Submission.Vinogradov.ExpSum (s := S) (k := k) (X := Q) θ‖
        = Wnorm k Q θ ^ S := by
      rw [Weyl_factor k S Q]
      simp [Wnorm, norm_pow]
    rw [hW]
    exact (show (Wnorm k Q θ ^ S) ^ 2 = Wnorm k Q θ ^ (2 * S) by
      rw [← pow_mul, Nat.mul_comm S 2]).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall fun θ => hpw θ)]
  have hexp : (∫ θ : UnitAddTorus (Fin (k + 1)),
        ‖Submission.Vinogradov.ExpSum (s := S) (k := k) (X := Q) θ‖ ^ 2)
      = ∫ θ : UnitAddTorus (Fin (k + 1)),
        ‖∑ x : Tup S Q, UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ‖ ^ 2 :=
    rfl
  rw [hexp, integral_normSq_eq_card (k + 1) (Tup S Q)
    (Submission.Vinogradov.powerSums (k := k))]
  rw [Submission.Vinogradov.filter_mom_eq_filter_matches S k Q,
    ← Submission.Vinogradov.J_eq_filter_card]

theorem Duo_pow_integral (S k Q : ℕ) :
    (∫ θ : UnitAddTorus (Fin (k + 1)), (Dnorm k Q θ) ^ (2 * S))
      = LeanEval.NumberTheory.VinogradovMeanValue.J S k Q := by
  have hpw : ∀ θ : UnitAddTorus (Fin (k + 1)),
      Dnorm k Q θ ^ (2 * S)
        = ‖∑ v : Tup S Q,
            UnitAddTorus.mFourier ((2 : ℤ) • Submission.Vinogradov.powerSums k v) θ‖ ^ 2 := by
    intro θ
    have h1 : ‖(Duo k Q θ) ^ S‖ ^ 2 = ‖Duo k Q θ‖ ^ (2 * S) := by
      rw [Complex.norm_pow, ← pow_mul, Nat.mul_comm S 2]
    rw [Dnorm, ← h1, Duo_pow_eq S k Q θ]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun θ => hpw θ)]
  rw [integral_normSq_eq_card (k + 1) (Tup S Q)
    (fun v => (2 : ℤ) • Submission.Vinogradov.powerSums k v)]
  have hset : ((Finset.univ : Finset (Tup S Q × Tup S Q)).filter
        (fun p => (2 : ℤ) • Submission.Vinogradov.powerSums k p.1
          = (2 : ℤ) • Submission.Vinogradov.powerSums k p.2))
      = ((Finset.univ : Finset (Tup S Q × Tup S Q)).filter
        (fun p => Submission.Vinogradov.powerSums k p.1
          = Submission.Vinogradov.powerSums k p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      funext j
      have hj := congrFun h j
      simp only [Pi.smul_apply] at hj
      exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (by simpa [smul_eq_mul] using hj)
    · intro h
      rw [h]
  rw [hset, Submission.Vinogradov.filter_mom_eq_filter_matches S k Q,
    ← Submission.Vinogradov.J_eq_filter_card]

/-! ## The two analytic steps -/

lemma rpow_pow_conv (S : ℕ) (hS : 3 ≤ S) {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (2 * (S - 2))) ^ ((S : ℝ) / ((S : ℝ) - 2)) = a ^ (2 * S) := by
  rw [← Real.rpow_natCast a (2 * (S - 2)), ← Real.rpow_natCast a (2 * S),
    ← Real.rpow_mul ha]
  have hne : ((S : ℝ) - 2) ≠ 0 := by
    have h : (2 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 2 < S)
    linarith
  have hexp : ((2 * (S - 2) : ℕ) : ℝ) * ((S : ℝ) / ((S : ℝ) - 2)) = ((2 * S : ℕ) : ℝ) := by
    have h1 : ((2 * (S - 2) : ℕ) : ℝ) = 2 * ((S : ℝ) - 2) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ S), Nat.cast_ofNat]
    have h2 : ((2 * S : ℕ) : ℝ) = 2 * (S : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [h1, h2]
    field_simp
  rw [hexp]

lemma rpow_sq_conv (S : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (a ^ 2) ^ ((S : ℝ) / 2) = a ^ S := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_natCast a S, ← Real.rpow_mul ha]
  congr 1
  ring

theorem holder_lp_step {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (S : ℕ) (hS : 3 ≤ S) {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfLp : MemLp (fun x => f x ^ (2 * (S - 2)))
      (ENNReal.ofReal ((S : ℝ) / ((S : ℝ) - 2))) μ)
    (hgLp : MemLp (fun x => g x ^ 2) (ENNReal.ofReal ((S : ℝ) / 2)) μ) :
    (∫ x, f x ^ (2 * (S - 2)) * g x ^ 2 ∂μ)
      ≤ (∫ x, f x ^ (2 * S) ∂μ) ^ (((S : ℝ) - 2) / (S : ℝ))
        * (∫ x, g x ^ S ∂μ) ^ (2 / (S : ℝ)) := by
  have hS2 : (2 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 2 < S)
  have hne : ((S : ℝ) - 2) ≠ 0 := by linarith
  have hp : (1 : ℝ) < (S : ℝ) / ((S : ℝ) - 2) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < (S : ℝ) - 2)]
    linarith
  have hconj : ((S : ℝ) / ((S : ℝ) - 2)).HolderConjugate ((S : ℝ) / 2) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    rw [inv_div, inv_div]
    field_simp
    ring
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (f := fun x => f x ^ (2 * (S - 2))) (g := fun x => g x ^ 2)
    (Filter.Eventually.of_forall (fun x => pow_nonneg (hf x) _))
    (Filter.Eventually.of_forall (fun x => pow_nonneg (hg x) _)) hfLp hgLp
  have hF : (∫ x, (f x ^ (2 * (S - 2))) ^ ((S : ℝ) / ((S : ℝ) - 2)) ∂μ)
      = ∫ x, f x ^ (2 * S) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => rpow_pow_conv S hS (hf x))
  have hG : (∫ x, (g x ^ 2) ^ ((S : ℝ) / 2) ∂μ) = ∫ x, g x ^ S ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => rpow_sq_conv S (hg x))
  have hinv1 : 1 / ((S : ℝ) / ((S : ℝ) - 2)) = ((S : ℝ) - 2) / (S : ℝ) := by
    rw [one_div_div]
  have hinv2 : 1 / ((S : ℝ) / 2) = 2 / (S : ℝ) := by
    rw [one_div_div]
  rw [hF, hG, hinv1, hinv2] at hholder
  exact hholder

theorem jensen_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    (S : ℕ) (hS : 2 ≤ S) {g : α → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hgLp : MemLp (fun x => g x ^ S) (ENNReal.ofReal 2) μ) :
    (∫ x, g x ^ S ∂μ) ^ (2 / (S : ℝ))
      ≤ (∫ x, g x ^ (2 * S) ∂μ) ^ (1 / (S : ℝ)) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (f := fun x => g x ^ S) (g := fun _x : α => (1 : ℝ))
    (Filter.Eventually.of_forall (fun x => pow_nonneg (hg x) _))
    (Filter.Eventually.of_forall (fun _x => zero_le_one))
    hgLp (MeasureTheory.memLp_const (1 : ℝ))
  have hsq : (∫ x, (g x ^ S) ^ (2 : ℝ) ∂μ) = ∫ x, g x ^ (2 * S) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show (g x ^ S) ^ (2 : ℝ) = g x ^ (2 * S)
      rw [← Real.rpow_natCast (g x) S, ← Real.rpow_natCast (g x) (2 * S),
        ← Real.rpow_mul (hg x)]
      have hexp : ((S : ℝ) * 2) = ((2 * S : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [hexp])
  have hone : (∫ x, (1 : ℝ) ^ (2 : ℝ) ∂μ) = 1 := by
    simp only [Real.one_rpow, integral_one_prob μ]
  rw [hsq, hone] at hholder
  simp only [mul_one, Real.one_rpow] at hholder
  have hbase : (0 : ℝ) ≤ ∫ x, g x ^ S ∂μ := integral_nonneg (fun x => pow_nonneg (hg x) S)
  have h2S : (0 : ℝ) ≤ ∫ x, g x ^ (2 * S) ∂μ :=
    integral_nonneg (fun x => pow_nonneg (hg x) (2 * S))
  have hpos : (0 : ℝ) ≤ 2 / (S : ℝ) := by
    have : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
    positivity
  have hfin := Real.rpow_le_rpow hbase hholder hpos
  rw [← Real.rpow_mul h2S] at hfin
  have hexp : (1 / 2 : ℝ) * (2 / (S : ℝ)) = 1 / (S : ℝ) := by
    have hS0 : (S : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
      linarith
    field_simp
  rw [hexp] at hfin
  exact hfin


/-! ## The factorisation of the exponential sum over `Idx S Q` -/

lemma sum_Phi_factor (S k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    (∑ i : Idx S Q, UnitAddTorus.mFourier (Phi S k Q i) θ)
      = Submission.Vinogradov.ExpSum (s := S - 2) (k := k) (X := Q) θ * Duo k Q θ := by
  rw [Fintype.sum_prod_type]
  simp only [Phi, UnitAddTorus.mFourier_add]
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul, Duo_apply k Q θ]
  rfl

/-! ## The combinatorial core -/

/-- The `S`-tuple `(v,v,x₀,…,x_{S-3})` encoded by `(x,v) ∈ Idx S Q`. -/
def expand (S Q : ℕ) (i : Idx S Q) : Tup S Q :=
  fun j => if hj : j.val < 2 then i.2
    else i.1 ⟨j.val - 2, by have h := j.isLt; omega⟩

lemma expand_zero {S Q : ℕ} (hS : 2 ≤ S) (i : Idx S Q) :
    expand S Q i ⟨0, by omega⟩ = i.2 := by
  simp [expand]

lemma expand_one {S Q : ℕ} (hS : 2 ≤ S) (i : Idx S Q) :
    expand S Q i ⟨1, by omega⟩ = i.2 := by
  simp [expand]

lemma expand_tail {S Q : ℕ} (i : Idx S Q) (r : Fin (S - 2)) :
    expand S Q i ⟨r.val + 2, by have := r.isLt; omega⟩ = i.1 r := by
  simp only [expand]
  rw [dif_neg (by
    rw [fin_val_mk]
    omega)]
  refine congrArg i.1 (Fin.ext ?_)
  rw [fin_val_mk]
  omega

lemma expand_reconstruct {S Q : ℕ} (hS : 2 ≤ S) (x : Tup S Q)
    (hx : x ⟨0, by omega⟩ = x ⟨1, by omega⟩) :
    expand S Q ((fun r : Fin (S - 2) => x ⟨r.val + 2, by have := r.isLt; omega⟩),
      x ⟨0, by omega⟩) = x := by
  funext j
  simp only [expand]
  by_cases hj : j.val < 2
  · rw [dif_pos hj]
    rcases (by omega : j.val = 0 ∨ j.val = 1) with h | h
    · rw [show j = (⟨0, by omega⟩ : Fin S) from Fin.ext (by simp [h])]
    · rw [show j = (⟨1, by omega⟩ : Fin S) from Fin.ext (by simp [h]), ← hx]
  · rw [dif_neg hj]
    show x ⟨(j.val - 2) + 2, by omega⟩ = x j
    refine congrArg x (Fin.ext ?_)
    rw [fin_val_mk]
    omega

lemma expand_injective {S Q : ℕ} (hS : 2 ≤ S) : Function.Injective (expand S Q) := by
  intro i i' h
  have h0 : i.2 = i'.2 := by
    have := congrFun h ⟨0, by omega⟩
    rwa [expand_zero hS i, expand_zero hS i'] at this
  have ht : i.1 = i'.1 := by
    funext r
    have := congrFun h ⟨r.val + 2, by have := r.isLt; omega⟩
    rwa [expand_tail i r, expand_tail i' r] at this
  exact Prod.ext ht h0

/-- Splitting a sum over `Fin S` into its first two terms and the rest. -/
lemma sum_univ_first_two {M : Type*} [AddCommMonoid M] {S : ℕ} (hS : 2 ≤ S) (f : Fin S → M) :
    ∑ j : Fin S, f j = f ⟨0, by omega⟩ + f ⟨1, by omega⟩
      + ∑ r : Fin (S - 2), f ⟨r.val + 2, by have := r.isLt; omega⟩ := by
  have h : 2 + (S - 2) = S := by omega
  have step1 : (∑ j : Fin S, f j) = ∑ i : Fin (2 + (S - 2)), f (Fin.cast h i) :=
    (Fintype.sum_equiv (finCongr h) (fun i : Fin (2 + (S - 2)) => f (Fin.cast h i))
      (fun j : Fin S => f j) (fun i => by rw [finCongr_apply])).symm
  rw [step1, Fin.sum_univ_add, Fin.sum_univ_two]
  have e0 : f (Fin.cast h (Fin.castAdd (S - 2) (0 : Fin 2))) = f ⟨0, by omega⟩ :=
    congrArg f (by ext; simp [Fin.val_cast, Fin.val_castAdd])
  have e1 : f (Fin.cast h (Fin.castAdd (S - 2) (1 : Fin 2))) = f ⟨1, by omega⟩ :=
    congrArg f (by ext; simp [Fin.val_cast, Fin.val_castAdd])
  have e2 : (∑ r : Fin (S - 2), f (Fin.cast h (Fin.natAdd 2 r)))
      = ∑ r : Fin (S - 2), f ⟨r.val + 2, by have := r.isLt; omega⟩ :=
    Finset.sum_congr rfl (fun r _ =>
      congrArg f (by ext; simp only [Fin.val_cast, Fin.val_natAdd]; omega))
  rw [e0, e1, e2]

lemma powerSums_expand {S k Q : ℕ} (hS : 2 ≤ S) (i : Idx S Q) :
    Submission.Vinogradov.powerSums k (expand S Q i) = Phi S k Q i := by
  rw [powerSums_eq_sum_mom1 (k := k) (expand S Q i)]
  show (∑ j : Fin S, mom1 k ((expand S Q i) j).1)
      = Submission.Vinogradov.powerSums k i.1 + (2 : ℤ) • mom1 k i.2.1
  rw [sum_univ_first_two hS (fun j : Fin S => mom1 k ((expand S Q i) j).1)]
  have htail : (∑ r : Fin (S - 2),
        mom1 k ((expand S Q i) ⟨r.val + 2, by have := r.isLt; omega⟩).1)
        = Submission.Vinogradov.powerSums k i.1 := by
    rw [show (∑ r : Fin (S - 2),
          mom1 k ((expand S Q i) ⟨r.val + 2, by have := r.isLt; omega⟩).1)
        = ∑ r : Fin (S - 2), mom1 k (i.1 r).1 from
      Finset.sum_congr rfl (fun r _ => by rw [expand_tail i r])]
    exact (powerSums_eq_sum_mom1 (k := k) i.1).symm
  rw [htail, expand_zero hS i, expand_one hS i, two_zsmul]
  abel

/-- **The combinatorial identity behind `Tdbl`.** -/
theorem Tdbl_card_eq (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) :
    Tdbl S k Q hk hkS =
      ((Finset.univ : Finset (Idx S Q × Idx S Q)).filter
        (fun q => Phi S k Q q.1 = Phi S k Q q.2)).card := by
  have hS : 2 ≤ S := by omega
  have hTdbl : Tdbl S k Q hk hkS = ((Finset.univ : Finset (PairSpace S Q)).filter (fun p =>
      Matches S k Q p ∧ p.1 ⟨0, by omega⟩ = p.1 ⟨1, by omega⟩ ∧
        p.2 ⟨0, by omega⟩ = p.2 ⟨1, by omega⟩)).card := rfl
  have hinj : Set.InjOn (fun q : Idx S Q × Idx S Q => (expand S Q q.1, expand S Q q.2))
      ↑((Finset.univ : Finset (Idx S Q × Idx S Q)).filter
        (fun q => Phi S k Q q.1 = Phi S k Q q.2)) := by
    intro q _ q' _ h
    have h1 : q.1 = q'.1 := expand_injective hS (Prod.ext_iff.mp h).1
    have h2 : q.2 = q'.2 := expand_injective hS (Prod.ext_iff.mp h).2
    exact Prod.ext h1 h2
  have himage : ((Finset.univ : Finset (Idx S Q × Idx S Q)).filter
        (fun q => Phi S k Q q.1 = Phi S k Q q.2)).image
        (fun q : Idx S Q × Idx S Q => (expand S Q q.1, expand S Q q.2))
      = (Finset.univ : Finset (PairSpace S Q)).filter (fun p =>
          Matches S k Q p ∧ p.1 ⟨0, by omega⟩ = p.1 ⟨1, by omega⟩ ∧
            p.2 ⟨0, by omega⟩ = p.2 ⟨1, by omega⟩) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨(Submission.Vinogradov.powerSums_eq_iff_matches (expand S Q q.1)
        (expand S Q q.2)).mp ?_, ?_, ?_⟩
      · rw [powerSums_expand hS q.1, powerSums_expand hS q.2]
        exact hq
      · show expand S Q q.1 ⟨0, by omega⟩ = expand S Q q.1 ⟨1, by omega⟩
        rw [expand_zero hS q.1, expand_one hS q.1]
      · show expand S Q q.2 ⟨0, by omega⟩ = expand S Q q.2 ⟨1, by omega⟩
        rw [expand_zero hS q.2, expand_one hS q.2]
    · rintro ⟨hm, h1, h2⟩
      refine ⟨(((fun r : Fin (S - 2) => p.1 ⟨r.val + 2, by have := r.isLt; omega⟩),
          p.1 ⟨0, by omega⟩),
        ((fun r : Fin (S - 2) => p.2 ⟨r.val + 2, by have := r.isLt; omega⟩),
          p.2 ⟨0, by omega⟩)), ?_, ?_⟩
      · rw [← powerSums_expand hS ((fun r : Fin (S - 2) =>
            p.1 ⟨r.val + 2, by have := r.isLt; omega⟩), p.1 ⟨0, by omega⟩),
          ← powerSums_expand hS ((fun r : Fin (S - 2) =>
            p.2 ⟨r.val + 2, by have := r.isLt; omega⟩), p.2 ⟨0, by omega⟩),
          expand_reconstruct hS p.1 h1, expand_reconstruct hS p.2 h2]
        exact (Submission.Vinogradov.powerSums_eq_iff_matches p.1 p.2).mpr hm
      · refine Prod.ext ?_ ?_
        · exact expand_reconstruct hS p.1 h1
        · exact expand_reconstruct hS p.2 h2
  rw [hTdbl, ← himage, Finset.card_image_of_injOn hinj]

/-- `Tdbl` as the `L²`-norm squared of the exponential sum over `Idx S Q`. -/
lemma Tdbl_eq_integral (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) :
    (Tdbl S k Q hk hkS : ℝ)
      = ∫ θ : UnitAddTorus (Fin (k + 1)),
          Wnorm k Q θ ^ (2 * (S - 2)) * Dnorm k Q θ ^ 2 := by
  rw [Tdbl_card_eq S k Q hk hkS]
  rw [← integral_normSq_eq_card (k + 1) (Idx S Q) (Phi S k Q)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show ‖∑ i : Idx S Q, UnitAddTorus.mFourier (Phi S k Q i) θ‖ ^ 2
      = Wnorm k Q θ ^ (2 * (S - 2)) * Dnorm k Q θ ^ 2
  rw [sum_Phi_factor S k Q θ]
  exact key_pointwise S k Q θ

/-! ## Final arithmetic -/

lemma final_arith (S : ℕ) (hS : 3 ≤ S) (Jv : ℝ) (hJ : 0 ≤ Jv) :
    Jv ^ (((S : ℝ) - 2) / (S : ℝ)) * Jv ^ (1 / (S : ℝ)) = Jv ^ (1 - 1 / (S : ℝ)) := by
  have hS0 : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
  have hne : ((S : ℝ) - 2) / (S : ℝ) + 1 / (S : ℝ) ≠ 0 := by
    have h : ((S : ℝ) - 2) / (S : ℝ) + 1 / (S : ℝ) = ((S : ℝ) - 1) / (S : ℝ) := by
      field_simp
      ring
    rw [h]
    apply div_ne_zero
    · have : (1 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 1 < S)
      linarith
    · exact ne_of_gt hS0
  rw [← Real.rpow_add' hJ hne]
  congr 1
  field_simp
  ring

/-! ## The main theorem -/

/-- **First Hölder step of the recursion** (Wooley, Michigan Math. J. **40** (1993), 175–180, §2,
case (a)).  `Tdbl S k Q hk hkS` counts the matching pairs of `S`-tuples in `[1,Q]` whose two first
coordinates agree on each side; then `Tdbl ≤ J_{S,k}(Q)^{1-1/S}`. -/
theorem Tdbl_le_rpow (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (hQ : 1 ≤ Q) :
    (Tdbl S k Q hk hkS : ℝ) ≤
      (LeanEval.NumberTheory.VinogradovMeanValue.J S k Q) ^ (1 - 1 / (S : ℝ)) := by
  haveI hprob : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin (k + 1)))) :=
    isProbabilityMeasure_torus_volume (k + 1)
  have hmain := Tdbl_eq_integral S k Q hk hkS
  rcases lt_or_eq_of_le (show 2 ≤ S by omega) with hS3 | hS2
  · have hS3' : 3 ≤ S := by omega
    have hnonnegW : ∀ θ : UnitAddTorus (Fin (k + 1)), 0 ≤ Wnorm k Q θ := fun θ => norm_nonneg _
    have hnonnegD : ∀ θ : UnitAddTorus (Fin (k + 1)), 0 ≤ Dnorm k Q θ := fun θ => norm_nonneg _
    have hmemF : MemLp (fun θ : UnitAddTorus (Fin (k + 1)) => Wnorm k Q θ ^ (2 * (S - 2)))
        (ENNReal.ofReal ((S : ℝ) / ((S : ℝ) - 2))) volume :=
      memLp_torus_of_continuous ((continuous_Weyl k Q).norm.pow _) _
    have hmemG2 : MemLp (fun θ : UnitAddTorus (Fin (k + 1)) => Dnorm k Q θ ^ 2)
        (ENNReal.ofReal ((S : ℝ) / 2)) volume :=
      memLp_torus_of_continuous ((continuous_Duo k Q).norm.pow _) _
    have hmemGS : MemLp (fun θ : UnitAddTorus (Fin (k + 1)) => Dnorm k Q θ ^ S)
        (ENNReal.ofReal 2) volume :=
      memLp_torus_of_continuous ((continuous_Duo k Q).norm.pow _) _
    have h1 := holder_lp_step (α := UnitAddTorus (Fin (k + 1))) (μ := volume)
      S hS3' (f := Wnorm k Q) (g := Dnorm k Q) hnonnegW hnonnegD hmemF hmemG2
    have h2 := jensen_prob (α := UnitAddTorus (Fin (k + 1))) (μ := volume)
      S (by omega) (g := Dnorm k Q) hnonnegD hmemGS
    have hJ0 : (0 : ℝ) ≤ LeanEval.NumberTheory.VinogradovMeanValue.J S k Q :=
      Submission.Vinogradov.J_nonneg S k Q
    have hIntW : (0 : ℝ) ≤ ∫ θ : UnitAddTorus (Fin (k + 1)), Wnorm k Q θ ^ (2 * S) :=
      integral_nonneg (fun θ => pow_nonneg (norm_nonneg _) _)
    calc (Tdbl S k Q hk hkS : ℝ)
        = ∫ θ : UnitAddTorus (Fin (k + 1)),
            Wnorm k Q θ ^ (2 * (S - 2)) * Dnorm k Q θ ^ 2 := hmain
      _ ≤ (∫ θ : UnitAddTorus (Fin (k + 1)), Wnorm k Q θ ^ (2 * S)) ^ (((S : ℝ) - 2) / (S : ℝ))
            * (∫ θ : UnitAddTorus (Fin (k + 1)), Dnorm k Q θ ^ S) ^ (2 / (S : ℝ)) := h1
      _ ≤ (∫ θ : UnitAddTorus (Fin (k + 1)), Wnorm k Q θ ^ (2 * S)) ^ (((S : ℝ) - 2) / (S : ℝ))
            * (∫ θ : UnitAddTorus (Fin (k + 1)), Dnorm k Q θ ^ (2 * S)) ^ (1 / (S : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hIntW _)
      _ = (LeanEval.NumberTheory.VinogradovMeanValue.J S k Q) ^ (((S : ℝ) - 2) / (S : ℝ))
            * (LeanEval.NumberTheory.VinogradovMeanValue.J S k Q) ^ (1 / (S : ℝ)) := by
          rw [Weyl_pow_integral S k Q, Duo_pow_integral S k Q]
      _ = (LeanEval.NumberTheory.VinogradovMeanValue.J S k Q) ^ (1 - 1 / (S : ℝ)) :=
          final_arith S hS3' _ hJ0
  · subst hS2
    have hnonnegD : ∀ θ : UnitAddTorus (Fin (k + 1)), 0 ≤ Dnorm k Q θ := fun θ => norm_nonneg _
    have hmemG : MemLp (fun θ : UnitAddTorus (Fin (k + 1)) => Dnorm k Q θ ^ (2 : ℕ))
        (ENNReal.ofReal 2) volume :=
      memLp_torus_of_continuous ((continuous_Duo k Q).norm.pow _) _
    have h2 := jensen_prob (α := UnitAddTorus (Fin (k + 1))) (μ := volume)
      2 (le_refl 2) (g := Dnorm k Q) hnonnegD hmemG
    have hexp2 : (2 : ℝ) / ((2 : ℕ) : ℝ) = 1 := by norm_num
    calc (Tdbl 2 k Q hk hkS : ℝ)
        = (∫ θ : UnitAddTorus (Fin (k + 1)), Dnorm k Q θ ^ 2) ^ ((2 : ℝ) / ((2 : ℕ) : ℝ)) := by
          rw [hmain, hexp2, Real.rpow_one]
          simp
      _ ≤ (∫ θ : UnitAddTorus (Fin (k + 1)), Dnorm k Q θ ^ (2 * 2)) ^
            ((1 : ℝ) / ((2 : ℕ) : ℝ)) := h2
      _ = (LeanEval.NumberTheory.VinogradovMeanValue.J 2 k Q) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) := by
          rw [Duo_pow_integral 2 k Q]
      _ = (LeanEval.NumberTheory.VinogradovMeanValue.J 2 k Q) ^ (1 - 1 / (2 : ℝ)) := by
          norm_num

end

end Work.BMF.recursion
