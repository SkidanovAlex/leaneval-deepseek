import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.discrete_maximal_lp

/-!
# The one-sided discrete Hardy--Littlewood maximal inequality on `ℤ`

This file proves `Work.BourgainPlan.Maximal.latDiscMax_lintegral_rpow_le`: the one-sided
("forward") discrete Hardy--Littlewood maximal operator

`latDiscMax a x = sup_{n ≥ 1} (1/n) Σ_{k<n} a (x + k)`

maps `ℓ^p(ℤ)` to `ℓ^p(ℤ)` for every `1 < p < ∞`, for `ℝ≥0∞`-valued `a`.

The reduction is as follows.  Write `a` as the increasing supremum of its finite caps
`a ⊓ ofReal M` (`M = 0, 1, 2, …`); each cap is a nonnegative *real*-valued function.  For such a
function the forward (one-sided) maximal function is dominated by the **two-sided** discrete
maximal function of `Commons.Analysis.HardyLittlewood.discrete_maximal_lp`, which is bounded on
`ℓ^p` for `1 < p < ∞` (`Commons.Analysis.HardyLittlewood.discrete_maximal_lp`).  Monotone
convergence for `lintegral`, together with the commutation of `x ↦ x ^ p` with suprema of
monotone families, then passes to the limit over `M`.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The one-sided ("forward") discrete Hardy--Littlewood maximal function on `ℤ`. -/
def latDiscMax (a : ℤ → ENNReal) (x : ℤ) : ENNReal :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), ((n : ENNReal))⁻¹ * ∑ k ∈ Finset.range n, a (x + (k : ℤ))

/-- The two-sided discrete maximal function on `ℤ`, in the form appearing in
`Commons.Analysis.HardyLittlewood.discrete_maximal_lp`. -/
def twoSidedDiscMax (g : ℤ → ℝ) (x : ℤ) : ENNReal :=
  ⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
    ((b - a + 1).toNat : ENNReal)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ

/-- `x ↦ x ^ q` (`q ≥ 0`) commutes with suprema of monotone `ℕ`-indexed families in `ℝ≥0∞`. -/
lemma rpow_iSup_of_monotone {q : ℝ} (hq : 0 ≤ q) {F : ℕ → ENNReal} (hF : Monotone F) :
    (⨆ n, F n) ^ q = ⨆ n, (F n) ^ q := by
  have h1 : Tendsto F atTop (𝓝 (⨆ n, F n)) := tendsto_atTop_iSup hF
  have h2 : Tendsto (fun n => (F n) ^ q) atTop (𝓝 ((⨆ n, F n) ^ q)) :=
    ((ENNReal.continuous_rpow_const (y := q)).tendsto (⨆ n, F n)).comp h1
  have h3 : Tendsto (fun n => (F n) ^ q) atTop (𝓝 (⨆ n, (F n) ^ q)) :=
    tendsto_atTop_iSup (fun i j hij => ENNReal.rpow_le_rpow (hF hij) hq)
  exact tendsto_nhds_unique h2 h3

/-- Monotonicity of the one-sided discrete maximal function in the function argument. -/
lemma latDiscMax_mono {c c' : ℤ → ENNReal} (h : ∀ y, c y ≤ c' y) (x : ℤ) :
    latDiscMax c x ≤ latDiscMax c' x := by
  unfold latDiscMax
  refine iSup_le fun n => iSup_le fun hn => ?_
  have hs : ∑ k ∈ Finset.range n, c (x + (k : ℤ)) ≤ ∑ k ∈ Finset.range n, c' (x + (k : ℤ)) :=
    Finset.sum_le_sum fun k _ => h (x + (k : ℤ))
  refine le_trans (mul_le_mul_right hs ((n : ENNReal)⁻¹)) ?_
  exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

/-- Reindexing a sum over `Finset.range` as a sum over the interval `Icc x b`. -/
private lemma sum_range_add_eq_sum_Icc {M : Type*} [AddCommMonoid M] (h : ℤ → M) {x b : ℤ}
    (hxb : x ≤ b) :
    ∑ j ∈ Finset.range ((b - x + 1).toNat), h (x + (j : ℤ)) = ∑ k ∈ Finset.Icc x b, h k := by
  have hN : (((b - x + 1).toNat : ℤ)) = b - x + 1 := Int.toNat_of_nonneg (by omega)
  have himg : (Finset.range ((b - x + 1).toNat)).image (fun j : ℕ => x + (j : ℤ))
      = Finset.Icc x b := by
    ext k
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjN : (j:ℤ) < b - x + 1 := by rw [← hN, Int.ofNat_lt]; exact hj
      constructor <;> omega
    · intro hk
      refine ⟨(k - x).toNat, ?_, ?_⟩
      · rw [Int.toNat_lt (by omega)]; rw [hN]; omega
      · rw [Int.toNat_of_nonneg (by omega)]; ring
  rw [← himg, Finset.sum_image]
  intro p _ q _ hpq
  simp only at hpq
  omega

/-- The one-sided maximal function of a *capped* sequence is dominated by the two-sided
maximal function of the corresponding nonnegative real sequence. -/
private lemma cap_le_twoSided (a : ℤ → ENNReal) (M : ℕ) (x : ℤ) :
    latDiscMax (fun y : ℤ => a y ⊓ ENNReal.ofReal (M : ℝ)) x
      ≤ twoSidedDiscMax (fun y : ℤ => (a y ⊓ ENNReal.ofReal (M : ℝ)).toReal) x := by
  set c : ℤ → ENNReal := fun y => a y ⊓ ENNReal.ofReal (M : ℝ) with hc
  set v : ℤ → ℝ := fun y => (c y).toReal with hv
  have hcv : ∀ y, ENNReal.ofReal (v y) = c y := by
    intro y; rw [hv, hc]
    exact ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt inf_le_right ENNReal.ofReal_lt_top))
  have hvnn : ∀ y, 0 ≤ v y := fun y => ENNReal.toReal_nonneg
  have henorm : ∀ y, ‖v y‖ₑ = c y := by
    intro y; rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hvnn y), hcv y]
  unfold latDiscMax
  refine iSup_le fun n => iSup_le fun hn => ?_
  have hreindex : ∑ k ∈ Finset.range n, ‖v (x + (k:ℤ))‖ₑ
      = ∑ k ∈ Finset.Icc x (x + (n:ℤ) - 1), ‖v k‖ₑ := by
    have hn' : ((x + (n:ℤ) - 1 - x + 1).toNat) = n := by
      have : x + (n:ℤ) - 1 - x + 1 = (n:ℤ) := by ring
      rw [this, Int.toNat_natCast]
    conv_lhs => rw [← hn']
    exact sum_range_add_eq_sum_Icc (x := x) (b := x + (n:ℤ) - 1) (fun k => ‖v k‖ₑ) (by omega)
  have hcoef : (((x + (n:ℤ) - 1 - x + 1).toNat : ℕ) : ENNReal) = (n : ENNReal) := by
    have : x + (n:ℤ) - 1 - x + 1 = (n:ℤ) := by ring
    rw [this, Int.toNat_natCast]
  calc (n:ENNReal)⁻¹ * ∑ k ∈ Finset.range n, c (x + (k:ℤ))
      = (n:ENNReal)⁻¹ * ∑ k ∈ Finset.range n, ‖v (x + (k:ℤ))‖ₑ := by
        congr 1; exact Finset.sum_congr rfl fun k _ => (henorm (x + (k:ℤ))).symm
    _ = (n:ENNReal)⁻¹ * ∑ k ∈ Finset.Icc x (x + (n:ℤ) - 1), ‖v k‖ₑ := by rw [hreindex]
    _ = (((x + (n:ℤ) - 1 - x + 1).toNat : ℕ) : ENNReal)⁻¹
          * ∑ k ∈ Finset.Icc x (x + (n:ℤ) - 1), ‖v k‖ₑ := by rw [hcoef]
    _ ≤ twoSidedDiscMax v x :=
        le_iSup_of_le x (le_iSup_of_le (x + (n:ℤ) - 1)
          (le_iSup_of_le ⟨le_rfl, by omega⟩ le_rfl))

/-- Capping `a` at the levels `M = 0, 1, 2, …` and taking the supremum recovers the one-sided
maximal function exactly. -/
private lemma eq_iSup_cap (a : ℤ → ENNReal) (x : ℤ) :
    latDiscMax a x = ⨆ M : ℕ, latDiscMax (fun y : ℤ => a y ⊓ ENNReal.ofReal (M : ℝ)) x := by
  have hcap_sup : ∀ y : ℤ, (⨆ M : ℕ, (a y ⊓ ENNReal.ofReal (M:ℝ))) = a y := by
    intro y
    rw [← inf_iSup_eq, show (⨆ M : ℕ, ENNReal.ofReal (M : ℝ)) = ⊤ from by
      rw [← ENNReal.iSup_natCast]; exact iSup_congr fun M => ENNReal.ofReal_natCast M]
    simp
  refine le_antisymm ?_ ?_
  · unfold latDiscMax
    refine iSup_le fun n => iSup_le fun hn => ?_
    have hsum : ∑ k ∈ Finset.range n, a (x + (k:ℤ))
        = ⨆ M : ℕ, ∑ k ∈ Finset.range n, (a (x + (k:ℤ)) ⊓ ENNReal.ofReal (M:ℝ)) := by
      rw [← ENNReal.finsetSum_iSup_of_monotone
        (s := Finset.range n)
        (f := fun k (M : ℕ) => a (x + (k:ℤ)) ⊓ ENNReal.ofReal (M:ℝ))
        (fun k i j hij => inf_le_inf_left _ (ENNReal.ofReal_mono (by exact_mod_cast hij)))]
      exact Finset.sum_congr rfl fun k _ => (hcap_sup (x + (k:ℤ))).symm
    calc (n:ENNReal)⁻¹ * ∑ k ∈ Finset.range n, a (x + (k:ℤ))
        = (n:ENNReal)⁻¹ * (⨆ M : ℕ, ∑ k ∈ Finset.range n,
            (a (x + (k:ℤ)) ⊓ ENNReal.ofReal (M:ℝ))) := by rw [hsum]
      _ = ⨆ M : ℕ, (n:ENNReal)⁻¹ * ∑ k ∈ Finset.range n,
            (a (x + (k:ℤ)) ⊓ ENNReal.ofReal (M:ℝ)) := by rw [ENNReal.mul_iSup]
      _ ≤ ⨆ M : ℕ, latDiscMax (fun y : ℤ => a y ⊓ ENNReal.ofReal (M : ℝ)) x :=
          iSup_mono fun M => le_iSup_of_le n (le_iSup_of_le hn le_rfl)
  · exact iSup_le fun M =>
      latDiscMax_mono (c := fun y : ℤ => a y ⊓ ENNReal.ofReal (M : ℝ)) (c' := a)
        (fun y => inf_le_left) x

theorem latDiscMax_lintegral_rpow_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ → ENNReal),
      ∫⁻ x : ℤ, (⨆ n : ℕ, ⨆ (_ : 0 < n), ((n : ENNReal))⁻¹ * ∑ k ∈ Finset.range n, a (x + (k : ℤ))) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * ∫⁻ x : ℤ, (a x) ^ p ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.HardyLittlewood.discrete_maximal_lp hp
  refine ⟨C ^ p, Real.rpow_pos_of_pos hCpos p, fun a => ?_⟩
  have hp0 : 0 ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hC' : ∀ g : ℤ → ℝ, ∫⁻ x : ℤ, (twoSidedDiscMax g x) ^ p ∂Measure.count
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ p ∂Measure.count :=
    fun g => hC g
  change ∫⁻ x : ℤ, (latDiscMax a x) ^ p ∂Measure.count
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, (a x) ^ p ∂Measure.count
  set cap : ℕ → ℤ → ENNReal := fun M y => a y ⊓ ENNReal.ofReal (M : ℝ) with hcap
  set gM : ℕ → ℤ → ℝ := fun M y => (cap M y).toReal with hgM
  have hcap_mono : ∀ {i j : ℕ}, i ≤ j → ∀ y, cap i y ≤ cap j y := by
    intro i j hij y
    rw [hcap]
    exact inf_le_inf_left _ (ENNReal.ofReal_mono (by exact_mod_cast hij))
  have hofReal : ∀ M y, ENNReal.ofReal (gM M y) = cap M y := by
    intro M y
    rw [hgM, hcap]
    exact ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt inf_le_right ENNReal.ofReal_lt_top))
  have h_enorm : ∀ M y, ‖gM M y‖ₑ = cap M y := by
    intro M y
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg, hofReal]
  have hmono : ∀ x : ℤ, Monotone fun M : ℕ => latDiscMax (cap M) x :=
    fun x i j hij => latDiscMax_mono (hcap_mono hij) x
  have hpt : ∀ M x, latDiscMax (cap M) x ≤ twoSidedDiscMax (gM M) x := by
    intro M x
    rw [hcap, hgM]
    exact cap_le_twoSided a M x
  have hsup : ∀ x : ℤ, latDiscMax a x = ⨆ M : ℕ, latDiscMax (cap M) x := by
    intro x
    rw [hcap]
    exact eq_iSup_cap a x
  have h1 : ∫⁻ x : ℤ, (latDiscMax a x) ^ p ∂Measure.count
      = ∫⁻ x : ℤ, (⨆ M : ℕ, (latDiscMax (cap M) x) ^ p) ∂Measure.count := by
    apply lintegral_congr; intro x
    rw [hsup x]
    exact rpow_iSup_of_monotone hp0 (hmono x)
  have h2 : ∫⁻ x : ℤ, (⨆ M : ℕ, (latDiscMax (cap M) x) ^ p) ∂Measure.count
      = ⨆ M : ℕ, ∫⁻ x : ℤ, (latDiscMax (cap M) x) ^ p ∂Measure.count :=
    lintegral_iSup (fun M => measurable_of_countable _)
      (fun i j hij x => ENNReal.rpow_le_rpow (hmono x hij) hp0)
  have h3 : ⨆ M : ℕ, ∫⁻ x : ℤ, (latDiscMax (cap M) x) ^ p ∂Measure.count
      ≤ ⨆ M : ℕ, ∫⁻ x : ℤ, (twoSidedDiscMax (gM M) x) ^ p ∂Measure.count :=
    iSup_le fun M =>
      le_trans (lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt M x) hp0)
        (le_iSup (fun M : ℕ => ∫⁻ x : ℤ, (twoSidedDiscMax (gM M) x) ^ p ∂Measure.count) M)
  have h4 : ⨆ M : ℕ, ∫⁻ x : ℤ, (twoSidedDiscMax (gM M) x) ^ p ∂Measure.count
      ≤ ⨆ M : ℕ, ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count :=
    iSup_le fun M =>
      le_trans (hC' (gM M))
        (le_iSup (fun M : ℕ =>
          ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count) M)
  have h5 : (⨆ M : ℕ, ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count)
      = ENNReal.ofReal (C ^ p)
        * ⨆ M : ℕ, ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count :=
    (ENNReal.mul_iSup _ _).symm
  have h6 : (⨆ M : ℕ, ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count)
      = ∫⁻ x : ℤ, (⨆ M : ℕ, ‖gM M x‖ₑ ^ p) ∂Measure.count := by
    rw [lintegral_iSup (fun M => measurable_of_countable _)]
    exact fun i j hij x => ENNReal.rpow_le_rpow (by
      show ‖gM i x‖ₑ ≤ ‖gM j x‖ₑ
      rw [h_enorm i x, h_enorm j x]; exact hcap_mono hij x) hp0
  have h7 : ∫⁻ x : ℤ, (⨆ M : ℕ, ‖gM M x‖ₑ ^ p) ∂Measure.count
      = ∫⁻ x : ℤ, (a x) ^ p ∂Measure.count := by
    apply lintegral_congr; intro x
    rw [← rpow_iSup_of_monotone hp0 (F := fun M : ℕ => ‖gM M x‖ₑ)
      (fun i j hij => by
        show ‖gM i x‖ₑ ≤ ‖gM j x‖ₑ
        rw [h_enorm i x, h_enorm j x]; exact hcap_mono hij x)]
    rw [iSup_congr fun M => h_enorm M x,
      show (⨆ M : ℕ, (a x ⊓ ENNReal.ofReal (M:ℝ))) = a x from by
        rw [← inf_iSup_eq, show (⨆ M : ℕ, ENNReal.ofReal (M : ℝ)) = ⊤ from by
          rw [← ENNReal.iSup_natCast]; exact iSup_congr fun M => ENNReal.ofReal_natCast M]
        simp]
  calc ∫⁻ x : ℤ, (latDiscMax a x) ^ p ∂Measure.count
      = ∫⁻ x : ℤ, (⨆ M : ℕ, (latDiscMax (cap M) x) ^ p) ∂Measure.count := h1
    _ = ⨆ M : ℕ, ∫⁻ x : ℤ, (latDiscMax (cap M) x) ^ p ∂Measure.count := h2
    _ ≤ ⨆ M : ℕ, ∫⁻ x : ℤ, (twoSidedDiscMax (gM M) x) ^ p ∂Measure.count := h3
    _ ≤ ⨆ M : ℕ, ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count := h4
    _ = ENNReal.ofReal (C ^ p) * ⨆ M : ℕ, ∫⁻ x : ℤ, ‖gM M x‖ₑ ^ p ∂Measure.count := h5
    _ = ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, (⨆ M : ℕ, ‖gM M x‖ₑ ^ p) ∂Measure.count := by rw [h6]
    _ = ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, (a x) ^ p ∂Measure.count := by rw [h7]

end

end Work.BourgainPlan.Maximal
