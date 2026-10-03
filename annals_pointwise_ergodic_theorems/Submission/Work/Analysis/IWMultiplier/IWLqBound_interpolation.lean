/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.VecDefs
import Submission.Work.Analysis.Interpolation.BilinearThreeLines
import Submission.Commons.Analysis.DiscreteCZ.eLpNorm_count_eq_tsum
import Submission.Port.Aesm

/-!
# Riesz--Thorin interpolation for the vector-valued Ionescu--Wainger multiplier

...
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [local instance] Classical.propDecidable

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger
open Work.Analysis.Interpolation

local notation "countZ" => (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)

/-! ## Hölder's inequality for the pairing -/

/-- **Hölder's inequality for the inner-product pairing on `ℓ^p(ℤ;H)`.**  For Hölder conjugate
extended exponents `p, q` and a finitely supported test sequence `v`,
`‖∑_n ⟪u n, v n⟫‖ ≤ ‖u‖_{ℓ^p} ‖v‖_{ℓ^q}`. -/
theorem pairingEnorm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : ℤ → H) (hv : (Function.support v).Finite)
    {p q : ENNReal} (hpq : ENNReal.HolderConjugate p q) :
    pairingEnorm u v ≤ eLpNorm u p countZ * eLpNorm v q countZ := by
  classical
  haveI : p.HolderTriple q 1 := hpq
  set s : Finset ℤ := hv.toFinset with hs
  have hv0 : ∀ n : ℤ, n ∉ s → v n = 0 := by
    intro n hn
    by_contra hne
    exact hn (by rw [hs]; exact hv.mem_toFinset.mpr hne)
  have htsum : (∑' n : ℤ, ⟪u n, v n⟫_ℂ) = ∑ n ∈ s, ⟪u n, v n⟫_ℂ :=
    tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s)
      (fun n hn => by rw [hv0 n hn, inner_zero_right])
  have htsum2 : (∑' n : ℤ, ‖⟪u n, v n⟫_ℂ‖ₑ) = ∑ n ∈ s, ‖⟪u n, v n⟫_ℂ‖ₑ :=
    tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s)
      (fun n hn => by rw [hv0 n hn, inner_zero_right, enorm_zero])
  have hholder : eLpNorm (fun n : ℤ => ⟪u n, v n⟫_ℂ) 1 countZ
      ≤ (1 : ℝ≥0) * eLpNorm u p countZ * eLpNorm v q countZ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (f := u) (g := v) (b := fun x y : H => ⟪x, y⟫_ℂ)
      (c := 1)
      (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) AEStronglyMeasurable.of_discrete AEStronglyMeasurable.of_discrete (Filter.Eventually.of_forall fun x => by
        rw [one_mul]
        exact nnnorm_inner_le_nnnorm (u x) (v x))
  calc pairingEnorm u v = ‖∑' n : ℤ, ⟪u n, v n⟫_ℂ‖ₑ := rfl
    _ = ‖∑ n ∈ s, ⟪u n, v n⟫_ℂ‖ₑ := by rw [htsum]
    _ ≤ ∑ n ∈ s, ‖⟪u n, v n⟫_ℂ‖ₑ := enorm_sum_le s _
    _ = ∑' n : ℤ, ‖⟪u n, v n⟫_ℂ‖ₑ := htsum2.symm
    _ = ∫⁻ n : ℤ, ‖⟪u n, v n⟫_ℂ‖ₑ ∂countZ := (lintegral_count _).symm
    _ = eLpNorm (fun n : ℤ => ⟪u n, v n⟫_ℂ) 1 countZ := eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm).symm
    _ ≤ (1 : ℝ≥0) * eLpNorm u p countZ * eLpNorm v q countZ := hholder
    _ = eLpNorm u p countZ * eLpNorm v q countZ := by rw [ENNReal.coe_one, one_mul]

/-! ## Duality of the pairing bound -/

/-- The inner square of a vector, in `ofReal` form. -/
lemma inner_self_eq_ofReal_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : ⟪x, x⟫_ℂ = (((‖x‖ ^ 2 : ℝ)) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, ← map_pow (algebraMap ℝ ℂ) ‖x‖ 2]
  rfl

/-- **Duality of the `ℓ^p` norm with respect to the inner-product pairing.**  If the pairing of a
fixed sequence `φ` against every finitely supported test sequence `g` is bounded by
`A ‖g‖_{ℓ^{p'}}`, then `‖φ‖_{ℓ^p} ≤ A` (for `1 < p < ∞` and `p'` the Hölder conjugate of `p`).

The dual test sequence is the saturated one, `g n = ‖φ n‖^{p-2} • φ n` on a finite set. -/
theorem eLpNorm_le_of_pairing_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {p p' : ℝ} (hp : 1 < p) (hconj : p.HolderConjugate p')
    (φ : ℤ → H) {A : ENNReal}
    (h : ∀ g : ℤ → H, (Function.support g).Finite →
      pairingEnorm φ g ≤ A * eLpNorm g (ENNReal.ofReal p') countZ) :
    eLpNorm φ (ENNReal.ofReal p) countZ ≤ A := by
  classical
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hinv : p⁻¹ + p'⁻¹ = 1 := Real.HolderConjugate.inv_add_inv_eq_one hconj
  have hp'pos : 0 < p' := by
    have h1 : 0 < p'⁻¹ := by
      have h2 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
      linarith
    exact inv_pos.mp h1
  have hp'eq : p' = p / (p - 1) := by
    have h2 : p'⁻¹ = (p - 1) / p := by
      rw [show p'⁻¹ = 1 - p⁻¹ by linarith, inv_eq_one_div]
      field_simp
    calc p' = (p'⁻¹)⁻¹ := (inv_inv p').symm
      _ = ((p - 1) / p)⁻¹ := by rw [h2]
      _ = p / (p - 1) := by field_simp
  have hp'mul : (p - 1) * p' = p := by
    rw [hp'eq, ← mul_div_assoc, mul_comm (p - 1) p]
    exact mul_div_cancel_right₀ p (by linarith : (p : ℝ) - 1 ≠ 0)
  have hinvsum : 1 / p' + 1 / p = 1 := by rw [one_div, one_div]; linarith
  -- the key estimate for each finite set
  have key : ∀ s : Finset ℤ, (∑ n ∈ s, ‖φ n‖ₑ ^ p) ≤ A ^ p := by
    intro s
    set S : ENNReal := ∑ n ∈ s, ‖φ n‖ₑ ^ p with hS
    have hterm : ∀ n : ℤ, ‖φ n‖ₑ ^ p = ENNReal.ofReal (‖φ n‖ ^ p) := fun n => by
      rw [← ofReal_norm, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
    have hScast : S = ENNReal.ofReal (∑ n ∈ s, ‖φ n‖ ^ p) := by
      rw [hS, show (∑ n ∈ s, ‖φ n‖ₑ ^ p) = ∑ n ∈ s, ENNReal.ofReal (‖φ n‖ ^ p) from
          Finset.sum_congr rfl fun n _ => hterm n,
        ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) _)]
    have hSfin : S < ⊤ := by rw [hScast]; exact ENNReal.ofReal_lt_top
    set g : ℤ → H := fun n => if n ∈ s then ((‖φ n‖ ^ (p - 2) : ℝ) : ℂ) • φ n else 0 with hg
    have hg_supp : (Function.support g).Finite := by
      refine Set.Finite.subset (Finset.finite_toSet s) ?_
      intro n hn
      simp only [Function.mem_support] at hn
      by_contra hnt
      refine hn ?_
      simp only [hg]
      exact if_neg (fun hmem => hnt (by exact hmem))
    have hpair : pairingEnorm φ g = S := by
      have h1 : (∑' n : ℤ, ⟪φ n, g n⟫_ℂ) = ((∑ n ∈ s, ‖φ n‖ ^ p : ℝ) : ℂ) := by
        rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s)
          (fun n hn => by simp only [hg]; rw [if_neg hn, inner_zero_right]),
          Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        simp only [hg]
        rw [if_pos hn, inner_smul_right, inner_self_eq_norm_sq_to_K,
          ← map_pow (algebraMap ℝ ℂ) ‖φ n‖ 2,
          show (algebraMap ℝ ℂ) (‖φ n‖ ^ 2) = (((‖φ n‖ ^ 2 : ℝ)) : ℂ) from rfl,
          show ‖φ n‖ ^ 2 = ‖φ n‖ ^ (2 : ℝ) from (Real.rpow_natCast ‖φ n‖ 2).symm,
          ← Complex.ofReal_mul,
          ← Real.rpow_add' (norm_nonneg _) (by linarith : (p - 2) + 2 ≠ 0),
          show (p - 2) + 2 = p by ring]
      rw [pairingEnorm, h1, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) _),
        hScast]
    have hen : eLpNorm g (ENNReal.ofReal p') countZ = S ^ (1 / p') := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hp'pos)
            ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp'pos.le, lintegral_count]
      have hsum : (∑' n : ℤ, ‖g n‖ₑ ^ p') = ∑ n ∈ s, ‖φ n‖ₑ ^ p := by
        rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s)
          (fun n hn => by
            simp only [hg]; rw [if_neg hn, enorm_zero, ENNReal.zero_rpow_of_pos hp'pos])]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnorm : ‖g n‖ₑ = ENNReal.ofReal (‖φ n‖ ^ (p - 1)) := by
          rw [← ofReal_norm]
          congr 1
          simp only [hg]
          rw [if_pos hn, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
          calc ‖φ n‖ ^ (p - 2) * ‖φ n‖ = ‖φ n‖ ^ (p - 2) * ‖φ n‖ ^ (1 : ℝ) := by
                rw [Real.rpow_one]
            _ = ‖φ n‖ ^ ((p - 2) + 1) :=
                (Real.rpow_add' (norm_nonneg _) (by linarith : (p - 2) + 1 ≠ 0)).symm
            _ = ‖φ n‖ ^ (p - 1) := by rw [show (p - 2) + 1 = p - 1 by ring]
        rw [hnorm, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp'pos.le,
          ← Real.rpow_mul (norm_nonneg _) (p - 1) p', hp'mul]
        exact (hterm n).symm
      rw [hsum, ← hS]
    have hle : S ≤ A * S ^ (1 / p') := by
      have hh := h g hg_supp
      rwa [hpair, hen] at hh
    by_cases hAtop : A = ⊤
    · rw [hAtop, ENNReal.top_rpow_of_pos hp_pos]
      exact le_top
    by_cases hS0 : S = 0
    · rw [hS0]
      exact bot_le
    have hSpos : 0 < S := pos_iff_ne_zero.mpr hS0
    have h1 : S ^ (1 / p') * S ^ (1 / p) = S := by
      rw [← ENNReal.rpow_add (1 / p') (1 / p) hS0 (ne_of_lt hSfin), hinvsum, ENNReal.rpow_one]
    have h2 : S ^ (1 / p') ≠ 0 := ne_of_gt (ENNReal.rpow_pos hSpos (ne_of_lt hSfin))
    have h3 : S ^ (1 / p') < ⊤ := by
      rw [show S = ENNReal.ofReal S.toReal from (ENNReal.ofReal_toReal (ne_of_lt hSfin)).symm,
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)]
      exact ENNReal.ofReal_lt_top
    have h4 : S ^ (1 / p) ≤ A := by
      refine (ENNReal.mul_le_mul_iff_right h2 (ne_of_lt h3)).mp ?_
      have hgoal : S ^ (1 / p') * S ^ (1 / p) ≤ S ^ (1 / p') * A := by
        rw [h1, mul_comm (S ^ (1 / p')) A]
        exact hle
      exact hgoal
    calc S = (S ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
      _ ≤ A ^ p := ENNReal.rpow_le_rpow h4 hp_pos.le
  have hT : (∑' n : ℤ, ‖φ n‖ₑ ^ p) ≤ A ^ p := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le key
  rw [Commons.Analysis.DiscreteCZ.eLpNorm_count_eq_tsum hp_pos]
  calc (∑' n : ℤ, ‖φ n‖ₑ ^ p) ^ (1 / p) ≤ (A ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hT (by positivity)
    _ = A := by
        rw [← ENNReal.rpow_mul, show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]

/-! ## The convolution and the pairing as finite sums -/

section Expansion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The IW convolution of a sequence vanishing off a finset is the finite sum over that finset. -/
theorem iwConv_apply_eq_sum (A : Finset Circle) (Φ : Circle → ℂ) (f : ℤ → H) (s : Finset ℤ)
    (hs : ∀ m : ℤ, m ∉ s → f m = 0) (n : ℤ) :
    iwConv A Φ f n = ∑ m ∈ s, (iwKernel (iwSymbolSet A Φ) (n - m)) • f m := by
  classical
  rw [iwConv_apply]
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (s := s.image (fun m => n - m)) (fun j hj => ?_)]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [show n - (n - m) = m by ring]
    · intro m _ m' _ h
      linarith
  · have hzero : f (n - j) = 0 := by
      by_contra hne
      exact hj (Finset.mem_image.mpr ⟨n - j, by_contra fun hc => hne (hs _ hc), by ring⟩)
    rw [hzero, smul_zero]

/-- **The pairing family as an explicit finite sum.**  With the `f`-side family carrying the
`star`-conjugated parameter (which is what makes the pairing holomorphic), the pairing of the
IW convolution of the family against the `g`-family expands into the finite double sum over the
supports. -/
theorem pairingFamily_eq_sum (A : Finset Circle) (Φ : Circle → ℂ) (f g : ℤ → H)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (t₀ t₁ u₀ u₁ : ℝ) (z : ℂ) :
    (∑' n : ℤ, ⟪iwConv A Φ (vecFam f t₀ t₁ (star z)) n, vecFam g u₀ u₁ z n⟫_ℂ)
      = ∑ n ∈ hg.toFinset, ∑ m ∈ hf.toFinset,
          star (iwKernel (iwSymbolSet A Φ) (n - m)) *
            vecCoef (f m) (expFamily (t₀ : ℂ) (t₁ : ℂ) z) *
            vecCoef (g n) (expFamily (u₀ : ℂ) (u₁ : ℂ) z) * ⟪f m, g n⟫_ℂ := by
  classical
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := hg.toFinset) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hfsupp : ∀ m : ℤ, m ∉ hf.toFinset → vecFam f t₀ t₁ (star z) m = 0 := by
      intro m hm
      rw [vecFam_apply, show f m = 0 from by_contra fun hc => hm (hf.mem_toFinset.mpr hc),
        vecCoef_zero, zero_smul]
    rw [iwConv_apply_eq_sum A Φ (vecFam f t₀ t₁ (star z)) hf.toFinset hfsupp n, sum_inner]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [vecFam_star_apply, vecFam_apply, inner_smul_left, inner_smul_left, inner_smul_right]
    rw [show (starRingEnd ℂ) (star (vecCoef (f m) (expFamily (t₀ : ℂ) (t₁ : ℂ) z)))
        = vecCoef (f m) (expFamily (t₀ : ℂ) (t₁ : ℂ) z) from star_star _,
      starRingEnd_apply]
    ring
  · have hzero : g n = 0 := by
      by_contra hne
      exact hn (hg.mem_toFinset.mpr hne)
    rw [show vecFam g u₀ u₁ z n = 0 by rw [vecFam_apply, hzero, vecCoef_zero, zero_smul],
      inner_zero_right]

end Expansion

/-! ## The pairing family: definition, analyticity, boundedness on the strip -/

section PairingFamily

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The analytic family to which Hadamard's three-lines theorem is applied: the pairing of the IW
convolution of the `f`-family (with `star`-conjugated parameter) against the `g`-family. -/
noncomputable def pairingFamily (A : Finset Circle) (Φ : Circle → ℂ) (f g : ℤ → H)
    (t₀ t₁ u₀ u₁ : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, ⟪iwConv A Φ (vecFam f t₀ t₁ (star z)) n, vecFam g u₀ u₁ z n⟫_ℂ

theorem pairingFamily_eq_sum' (A : Finset Circle) (Φ : Circle → ℂ) (f g : ℤ → H)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (t₀ t₁ u₀ u₁ : ℝ) (z : ℂ) :
    pairingFamily A Φ f g t₀ t₁ u₀ u₁ z
      = ∑ n ∈ hg.toFinset, ∑ m ∈ hf.toFinset,
          star (iwKernel (iwSymbolSet A Φ) (n - m)) *
            vecCoef (f m) (expFamily (t₀ : ℂ) (t₁ : ℂ) z) *
            vecCoef (g n) (expFamily (u₀ : ℂ) (u₁ : ℂ) z) * ⟪f m, g n⟫_ℂ :=
  pairingFamily_eq_sum A Φ f g hf hg t₀ t₁ u₀ u₁ z

attribute [fun_prop] differentiable_vecCoef_expFamily

theorem differentiable_pairingFamily (A : Finset Circle) (Φ : Circle → ℂ) (f g : ℤ → H)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (t₀ t₁ u₀ u₁ : ℝ) : Differentiable ℂ (pairingFamily A Φ f g t₀ t₁ u₀ u₁) := by
  classical
  have hfun : pairingFamily A Φ f g t₀ t₁ u₀ u₁
      = fun z : ℂ => ∑ n ∈ hg.toFinset, ∑ m ∈ hf.toFinset,
          star (iwKernel (iwSymbolSet A Φ) (n - m)) *
            vecCoef (f m) (expFamily (t₀ : ℂ) (t₁ : ℂ) z) *
            vecCoef (g n) (expFamily (u₀ : ℂ) (u₁ : ℂ) z) * ⟪f m, g n⟫_ℂ := by
    funext z
    exact pairingFamily_eq_sum' A Φ f g hf hg t₀ t₁ u₀ u₁ z
  rw [hfun]
  fun_prop

/-- Exponent convexity of `rpow`: a real power with exponent between `a` and `b`. -/
lemma rpow_le_max_rpow {r : ℝ} (hr : 0 < r) {a b s : ℝ} (ha : min a b ≤ s) (hb : s ≤ max a b) :
    r ^ s ≤ max (r ^ a) (r ^ b) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab] at ha
    rw [max_eq_right hab] at hb
    rcases le_total 1 r with h1 | h1
    · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hb) (le_max_right _ _)
    · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hr h1 ha) (le_max_left _ _)
  · rw [min_eq_right hab] at ha
    rw [max_eq_left hab] at hb
    rcases le_total 1 r with h1 | h1
    · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hb) (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hr h1 ha) (le_max_right _ _)

/-- The scalar coefficient of the family is bounded on the strip `0 ≤ Re z ≤ 1`. -/
lemma norm_vecCoef_expFamily_le {x : H} (t₀ t₁ : ℝ) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1) :
    ‖vecCoef x (expFamily (t₀ : ℂ) (t₁ : ℂ) z)‖
      ≤ max 1 (max (‖x‖ ^ (t₀ - 1)) (‖x‖ ^ (t₁ - 1))) := by
  by_cases hx : x = 0
  · rw [hx, vecCoef_zero, norm_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  · rw [norm_vecCoef x _, if_neg hx]
    have hre : (expFamily (t₀ : ℂ) (t₁ : ℂ) z).re - 1
        = (1 - z.re) * (t₀ - 1) + z.re * (t₁ - 1) := by
      rw [expFamily_ofReal_re]; ring
    rw [hre]
    refine le_trans (rpow_le_max_rpow (norm_pos_iff.mpr hx) ?_ ?_) (le_max_right _ _)
    · rcases le_total (t₀ - 1) (t₁ - 1) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    · rcases le_total (t₀ - 1) (t₁ - 1) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith

theorem bddAbove_pairingFamily (A : Finset Circle) (Φ : Circle → ℂ) (f g : ℤ → H)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (t₀ t₁ u₀ u₁ : ℝ) :
    BddAbove ((norm ∘ pairingFamily A Φ f g t₀ t₁ u₀ u₁)
      '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  classical
  refine ⟨∑ n ∈ hg.toFinset, ∑ m ∈ hf.toFinset,
      ‖iwKernel (iwSymbolSet A Φ) (n - m)‖ *
        max 1 (max (‖f m‖ ^ (t₀ - 1)) (‖f m‖ ^ (t₁ - 1))) *
        max 1 (max (‖g n‖ ^ (u₀ - 1)) (‖g n‖ ^ (u₁ - 1))) * ‖⟪f m, g n⟫_ℂ‖, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hz
  simp only [Function.comp_apply]
  rw [pairingFamily_eq_sum' A Φ f g hf hg t₀ t₁ u₀ u₁ z]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
  have h1 := norm_vecCoef_expFamily_le (H := H) (x := f m) t₀ t₁ hz.1 hz.2
  have h2 := norm_vecCoef_expFamily_le (H := H) (x := g n) u₀ u₁ hz.1 hz.2
  rw [norm_mul, norm_mul, norm_mul, norm_star]
  gcongr

end PairingFamily

/-! ## The interpolation theorem -/

/-- `min a b ≤ a ^ (1 - θ) * b ^ θ` for `θ ∈ [0,1]`: the interpolated constant dominates the
smaller of the two endpoint constants. -/
lemma min_le_mul_rpow {a b : NNReal} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min a b ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    rcases eq_or_ne a 0 with ha | ha
    · rw [ha]; positivity
    · calc a = a ^ (1 - θ) * a ^ θ := by
            rw [← NNReal.rpow_add ha, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
        _ ≤ a ^ (1 - θ) * b ^ θ :=
            mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow hab h0) (by positivity)
  · rw [min_eq_right hab]
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb]; positivity
    · calc b = b ^ (1 - θ) * b ^ θ := by
            rw [← NNReal.rpow_add hb, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
        _ ≤ a ^ (1 - θ) * b ^ θ :=
            mul_le_mul_of_nonneg_right (NNReal.rpow_le_rpow hab (by linarith)) (by positivity)

/-- The Hölder conjugate of a real exponent, transported to `ℝ≥0∞`. -/
lemma ennreal_holderConjugate_ofReal {a b : ℝ} (h : a.HolderConjugate b) :
    ENNReal.HolderConjugate (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  rw [ENNReal.holderConjugate_iff]
  have ha : (0:ℝ) < a := h.left_pos
  have hb : (0:ℝ) < b := h.symm.left_pos
  rw [← ENNReal.ofReal_inv_of_pos ha, ← ENNReal.ofReal_inv_of_pos hb,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    Real.HolderConjugate.inv_add_inv_eq_one h, ENNReal.ofReal_one]

/-- `ofReal` of a real monomial against the corresponding extended product of finite elements. -/
lemma ofReal_toReal_mul_rpow {m : ℝ} (hm : 0 ≤ m) {U V : ENNReal} (hU : U < ⊤) (hV : V < ⊤)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β)
      = ENNReal.ofReal m * U ^ α * V ^ β := by
  have h1 : U ^ α = ENNReal.ofReal (U.toReal ^ α) := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hU),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  have h2 : V ^ β = ENNReal.ofReal (V.toReal ^ β) := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hV),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hβ,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  rw [h1, h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hm]

/-- If an `ℓ^p` norm (counting measure) vanishes, the sequence vanishes. -/
lemma eq_zero_of_eLpNorm_eq_zero {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {p : ℝ} (hp : 0 < p) {u : ℤ → H} (h : eLpNorm u (ENNReal.ofReal p) countZ = 0) :
    ∀ n, u n = 0 := by
  have hsm : AEStronglyMeasurable u countZ := AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[countZ] 0 :=
    (eLpNorm_eq_zero_iff (ENNReal.ofReal_ne_zero_iff.mpr hp)).mp h
  intro n
  by_contra hn
  have hsub : ({n} : Set ℤ) ⊆ {m : ℤ | u m ≠ 0} := by
    intro m hm
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact hn
  have hle : countZ {n} ≤ countZ {m : ℤ | u m ≠ 0} := measure_mono hsub
  rw [Measure.count_singleton] at hle
  have hne : countZ {m : ℤ | u m ≠ 0} ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ENNReal) < 1) hle)
  exact hne (ae_iff.mp h0)

/-- **Riesz--Thorin interpolation for the vector-valued Ionescu--Wainger multiplier.**  A bound for
the multiplier at the two exponents `q₀, q₁` implies the bound at every intermediate exponent, the
constants being combined log-convexly. -/
theorem IWLqBound_interpolation (A : Finset IonescuWainger.Circle) (Φ : IonescuWainger.Circle → ℂ)
    {q q₀ q₁ : ENNReal} {C₀ C₁ : NNReal} {θ : ℝ} (h0 : IWLqBound A Φ q₀ C₀)
    (h1 : IWLqBound A Φ q₁ C₁) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq₀ : 1 ≤ q₀.toReal) (hq₁ : 1 ≤ q₁.toReal)
    (hq : (q.toReal)⁻¹ = (1 - θ) * (q₀.toReal)⁻¹ + θ * (q₁.toReal)⁻¹) :
    IWLqBound A Φ q (C₀ ^ (1 - θ) * C₁ ^ θ) := by
  classical
  set p₀ : ℝ := q₀.toReal with hp₀def
  set p₁ : ℝ := q₁.toReal with hp₁def
  set p : ℝ := q.toReal with hpdef
  have hp₀1 : 1 ≤ p₀ := hq₀
  have hp₁1 : 1 ≤ p₁ := hq₁
  have hp₀_pos : 0 < p₀ := lt_of_lt_of_le zero_lt_one hp₀1
  have hp₁_pos : 0 < p₁ := lt_of_lt_of_le zero_lt_one hp₁1
  have hq₀_ne_top : q₀ ≠ ⊤ := by intro h; rw [h] at hp₀def; rw [hp₀def] at hp₀1; norm_num at hp₀1
  have hq₁_ne_top : q₁ ≠ ⊤ := by intro h; rw [h] at hp₁def; rw [hp₁def] at hp₁1; norm_num at hp₁1
  have hq' : p⁻¹ = (1 - θ) * p₀⁻¹ + θ * p₁⁻¹ := hq
  have hp_pos : 0 < p := by
    have h : 0 < p⁻¹ := by
      rw [hq']
      rcases eq_or_lt_of_le hθ0 with h' | h'
      · rw [← h']; simpa using inv_pos.mpr hp₀_pos
      · have ha : 0 ≤ (1 - θ) * p₀⁻¹ := mul_nonneg (by linarith) (le_of_lt (inv_pos.mpr hp₀_pos))
        have hb : 0 < θ * p₁⁻¹ := mul_pos h' (inv_pos.mpr hp₁_pos)
        linarith
    rwa [inv_pos] at h
  have hq_ne_top : q ≠ ⊤ := by intro h; rw [h] at hpdef; rw [hpdef] at hp_pos; norm_num at hp_pos
  have hp_ge1 : 1 ≤ p := by
    have h1'' : p⁻¹ ≤ 1 := by
      rw [hq']
      have h1' : p₀⁻¹ ≤ 1 := by
        rw [← inv_one]; exact (inv_le_inv₀ hp₀_pos (by norm_num)).mpr hp₀1
      have h2' : p₁⁻¹ ≤ 1 := by
        rw [← inv_one]; exact (inv_le_inv₀ hp₁_pos (by norm_num)).mpr hp₁1
      nlinarith
    have h2 : p⁻¹ ≤ ((1:ℝ))⁻¹ := by rw [inv_one]; exact h1''
    exact (inv_le_inv₀ hp_pos (by norm_num)).mp h2
  have hCeq : ENNReal.ofReal (((C₀ ^ (1 - θ) * C₁ ^ θ : NNReal)) : ℝ)
      = (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ := by
    rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hθ0,
      ENNReal.coe_rpow_of_nonneg _ (by linarith : (0:ℝ) ≤ 1 - θ)]
  have hq_eq : q = ENNReal.ofReal p := by
    rw [hpdef]; exact (ENNReal.ofReal_toReal hq_ne_top).symm
  intro H inst₁ inst₂ inst₃ f hf
  rw [hCeq, hq_eq]
  -- the degenerate cases `θ = 0` and `θ = 1`
  rcases eq_or_lt_of_le hθ0 with hθ0' | hθ0'
  · subst hθ0'
    have hp_eq : p = p₀ := inv_inj.mp (by simpa using hq')
    have hqq : ENNReal.ofReal p = q₀ := by
      rw [show q₀ = ENNReal.ofReal p₀ from (ENNReal.ofReal_toReal hq₀_ne_top).symm, ← hp_eq]
    rw [hqq, sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
    have := h0 H f hf
    rwa [ENNReal.ofReal_coe_nnreal] at this
  rcases eq_or_lt_of_le hθ1 with hθ1' | hθ1'
  · subst hθ1'
    have hp_eq : p = p₁ := inv_inj.mp (by simpa using hq')
    have hqq : ENNReal.ofReal p = q₁ := by
      rw [show q₁ = ENNReal.ofReal p₁ from (ENNReal.ofReal_toReal hq₁_ne_top).symm, ← hp_eq]
    rw [hqq, sub_self, ENNReal.rpow_zero, ENNReal.rpow_one, one_mul]
    have := h1 H f hf
    rwa [ENNReal.ofReal_coe_nnreal] at this
  -- the case `p = 1`
  by_cases hp1 : p = 1
  · have hpp0 : p₀ = 1 := by
      have h : (1:ℝ) = (1 - θ) * p₀⁻¹ + θ * p₁⁻¹ := by rw [← hq', hp1, inv_one]
      have h1' : (1 - θ) * p₀⁻¹ ≤ (1 - θ) * 1 := mul_le_mul_of_nonneg_left
        (by rw [← inv_one]; exact (inv_le_inv₀ hp₀_pos (by norm_num)).mpr hp₀1) (by linarith)
      have h2' : θ * p₁⁻¹ ≤ θ * 1 := mul_le_mul_of_nonneg_left
        (by rw [← inv_one]; exact (inv_le_inv₀ hp₁_pos (by norm_num)).mpr hp₁1) hθ0
      have he : (1 - θ) * p₀⁻¹ = (1 - θ) * 1 := by linarith
      have hlt : (1 - θ) ≠ 0 := by linarith
      have hinv : p₀⁻¹ = 1 := mul_left_cancel₀ hlt he
      rw [← inv_inv p₀, hinv, inv_one]
    have hpp1 : p₁ = 1 := by
      have h : (1:ℝ) = (1 - θ) * p₀⁻¹ + θ * p₁⁻¹ := by rw [← hq', hp1, inv_one]
      have h1' : (1 - θ) * p₀⁻¹ ≤ (1 - θ) * 1 := mul_le_mul_of_nonneg_left
        (by rw [← inv_one]; exact (inv_le_inv₀ hp₀_pos (by norm_num)).mpr hp₀1) (by linarith)
      have h2' : θ * p₁⁻¹ ≤ θ * 1 := mul_le_mul_of_nonneg_left
        (by rw [← inv_one]; exact (inv_le_inv₀ hp₁_pos (by norm_num)).mpr hp₁1) hθ0
      have he : θ * p₁⁻¹ = θ * 1 := by linarith
      have hlt : θ ≠ 0 := ne_of_gt hθ0'
      have hinv : p₁⁻¹ = 1 := mul_left_cancel₀ hlt he
      rw [← inv_inv p₁, hinv, inv_one]
    have hq1 : ENNReal.ofReal p = 1 := by rw [hp1, ENNReal.ofReal_one]
    have hq₀1 : q₀ = 1 := by
      rw [show q₀ = ENNReal.ofReal p₀ from (ENNReal.ofReal_toReal hq₀_ne_top).symm, hpp0,
        ENNReal.ofReal_one]
    have hq₁1 : q₁ = 1 := by
      rw [show q₁ = ENNReal.ofReal p₁ from (ENNReal.ofReal_toReal hq₁_ne_top).symm, hpp1,
        ENNReal.ofReal_one]
    rw [hq1]
    have hm0 : eLpNorm (iwConv A Φ f) 1 countZ ≤ (C₀ : ENNReal) * eLpNorm f 1 countZ := by
      have hh := h0 H f hf
      rwa [hq₀1, ENNReal.ofReal_coe_nnreal] at hh
    have hm1 : eLpNorm (iwConv A Φ f) 1 countZ ≤ (C₁ : ENNReal) * eLpNorm f 1 countZ := by
      have hh := h1 H f hf
      rwa [hq₁1, ENNReal.ofReal_coe_nnreal] at hh
    rcases le_total (C₀ : NNReal) C₁ with hle | hle
    · have hmin0 : C₀ ≤ C₀ ^ (1 - θ) * C₁ ^ θ := by
        simpa [min_eq_left hle] using min_le_mul_rpow (a := C₀) (b := C₁) hθ0 hθ1
      have hmin : (C₀ : ENNReal) ≤ (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ := by
        rw [← ENNReal.coe_rpow_of_nonneg _ hθ0, ← ENNReal.coe_rpow_of_nonneg _ (by linarith : (0:ℝ) ≤ 1 - θ),
          ← ENNReal.coe_mul, ENNReal.coe_le_coe]
        exact hmin0
      exact le_trans hm0 (mul_le_mul_of_nonneg_right hmin bot_le)
    · have hmin0 : C₁ ≤ C₀ ^ (1 - θ) * C₁ ^ θ := by
        simpa [min_eq_right hle] using min_le_mul_rpow (a := C₀) (b := C₁) hθ0 hθ1
      have hmin : (C₁ : ENNReal) ≤ (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ := by
        rw [← ENNReal.coe_rpow_of_nonneg _ hθ0, ← ENNReal.coe_rpow_of_nonneg _ (by linarith : (0:ℝ) ≤ 1 - θ),
          ← ENNReal.coe_mul, ENNReal.coe_le_coe]
        exact hmin0
      exact le_trans hm1 (mul_le_mul_of_nonneg_right hmin bot_le)
  -- main case: `1 < p`
  have hp_gt1 : 1 < p := lt_of_le_of_ne hp_ge1 (Ne.symm hp1)
  set p' : ℝ := (1 - p⁻¹)⁻¹ with hp'def
  have hp'inv : p'⁻¹ = 1 - p⁻¹ := by rw [hp'def, inv_inv]
  have hp'pos : 0 < p' := by
    rw [hp'def, inv_pos]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp_gt1)
  have hp'mul : p' * (1 - p⁻¹) = 1 := by
    rw [hp'def]; exact inv_mul_cancel₀ (by linarith [sub_pos.mpr (inv_lt_one_of_one_lt₀ hp_gt1)])
  have hpconj : p.HolderConjugate p' := by
    rw [Real.holderConjugate_iff]
    exact ⟨hp_gt1, by rw [hp'inv]; ring⟩
  set p₀' : ℝ := (1 - p₀⁻¹)⁻¹ with hp₀'def
  set p₁' : ℝ := (1 - p₁⁻¹)⁻¹ with hp₁'def
  set t₀ : ℝ := p * p₀⁻¹ with ht₀def
  set t₁ : ℝ := p * p₁⁻¹ with ht₁def
  set u₀ : ℝ := p' * p₀'⁻¹ with hu₀def
  set u₁ : ℝ := p' * p₁'⁻¹ with hu₁def
  have ht : (1 - θ) * t₀ + θ * t₁ = 1 := by
    rw [ht₀def, ht₁def]
    exact interp_self (ne_of_gt hp_pos) (by rw [one_div]; exact hq')
  have hu₀' : u₀ = p' * (1 - p₀⁻¹) := by rw [hu₀def, hp₀'def, inv_inv]
  have hu₁' : u₁ = p' * (1 - p₁⁻¹) := by rw [hu₁def, hp₁'def, inv_inv]
  have hu : (1 - θ) * u₀ + θ * u₁ = 1 := by
    rw [hu₀', hu₁']
    have h1 : (1 - θ) * (1 - p₀⁻¹) + θ * (1 - p₁⁻¹) = 1 - p⁻¹ := by
      rw [hq']; ring
    rw [show (1 - θ) * (p' * (1 - p₀⁻¹)) + θ * (p' * (1 - p₁⁻¹))
        = p' * ((1 - θ) * (1 - p₀⁻¹) + θ * (1 - p₁⁻¹)) by ring, h1]
    exact hp'mul
  -- the two side bounds
  have ht₀_pos : 0 < t₀ := by rw [ht₀def]; positivity
  have ht₁_pos : 0 < t₁ := by rw [ht₁def]; positivity
  set U : ENNReal := eLpNorm f (ENNReal.ofReal p) countZ with hUdef
  -- the main estimate
  have hmain : eLpNorm (iwConv A Φ f) (ENNReal.ofReal p) countZ ≤
      (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ * U := by
    rcases eq_or_ne C₀ 0 with hC₀ | hC₀
    · have hq₀_eq : q₀ = ENNReal.ofReal p₀ := (ENNReal.ofReal_toReal hq₀_ne_top).symm
      have hh := h0 H f hf
      simp only [hC₀, NNReal.coe_zero, ENNReal.ofReal_zero, zero_mul] at hh
      rw [hq₀_eq] at hh
      have hz : iwConv A Φ f = 0 := funext fun n =>
        eq_zero_of_eLpNorm_eq_zero hp₀_pos (le_antisymm hh bot_le) n
      rw [hz]
      simp
    rcases eq_or_ne C₁ 0 with hC₁ | hC₁
    · have hq₁_eq : q₁ = ENNReal.ofReal p₁ := (ENNReal.ofReal_toReal hq₁_ne_top).symm
      have hh := h1 H f hf
      simp only [hC₁, NNReal.coe_zero, ENNReal.ofReal_zero, zero_mul] at hh
      rw [hq₁_eq] at hh
      have hz : iwConv A Φ f = 0 := funext fun n =>
        eq_zero_of_eLpNorm_eq_zero hp₁_pos (le_antisymm hh bot_le) n
      rw [hz]
      simp
    have hC₀pos : (0 : ENNReal) < (C₀ : ENNReal) := by
      rw [← ENNReal.coe_zero, ENNReal.coe_lt_coe]; exact pos_iff_ne_zero.mpr hC₀
    have hC₁pos : (0 : ENNReal) < (C₁ : ENNReal) := by
      rw [← ENNReal.coe_zero, ENNReal.coe_lt_coe]; exact pos_iff_ne_zero.mpr hC₁
    have hCne : ((C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ) ≠ 0 :=
      mul_ne_zero (ne_of_gt (ENNReal.rpow_pos hC₀pos ENNReal.coe_ne_top))
        (ne_of_gt (ENNReal.rpow_pos hC₁pos ENNReal.coe_ne_top))
    refine eLpNorm_le_of_pairing_le (A := (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ * U)
      (φ := iwConv A Φ f) hp_gt1 hpconj fun g hg => ?_
    set V : ENNReal := eLpNorm g (ENNReal.ofReal p') countZ with hVdef
    by_cases hU0 : U = 0
    · have hf0 : f = 0 := funext fun n =>
        eq_zero_of_eLpNorm_eq_zero hp_pos (by rw [← hUdef]; exact hU0) n
      have hT0 : iwConv A Φ f = 0 := by
        funext n
        rw [iwConv_apply]
        simp [hf0]
      rw [hT0]
      simp [pairingEnorm]
    by_cases hV0 : V = 0
    · have hg0 : g = 0 := funext fun n =>
        eq_zero_of_eLpNorm_eq_zero hp'pos (by rw [← hVdef]; exact hV0) n
      rw [hg0, hV0]
      simp [pairingEnorm]
    by_cases hUt : U = ⊤
    · have hRHS : (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ * U * V = ⊤ := by
        rw [hUt, ENNReal.mul_top hCne, ENNReal.top_mul (by rw [hVdef]; exact hV0)]
      rw [hRHS]
      exact le_top
    by_cases hVt : V = ⊤
    · have hRHS : (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ * U * V = ⊤ := by
        rw [hVt, ENNReal.mul_top (mul_ne_zero hCne (by rw [hUdef]; exact hU0))]
      rw [hRHS]
      exact le_top
    -- the main case: the three-lines argument
    have hUpos : 0 < U := pos_iff_ne_zero.mpr hU0
    have hVpos : 0 < V := pos_iff_ne_zero.mpr hV0
    have hUfin : U < ⊤ := lt_top_iff_ne_top.mpr hUt
    have hVfin : V < ⊤ := lt_top_iff_ne_top.mpr hVt
    set Ffun : ℂ → ℂ := pairingFamily A Φ f g t₀ t₁ u₀ u₁ with hFfundef
    have hFdiff : Differentiable ℂ Ffun :=
      differentiable_pairingFamily A Φ f g hf hg t₀ t₁ u₀ u₁
    have hFbdd : BddAbove ((norm ∘ Ffun) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
      bddAbove_pairingFamily A Φ f g hf hg t₀ t₁ u₀ u₁
    have hsuppF : ∀ z : ℂ, (Function.support (vecFam f t₀ t₁ (star z))).Finite := fun z =>
      hf.subset (fun m hm => by
        simp only [Function.mem_support] at hm ⊢
        intro h0'
        exact hm (by rw [vecFam_apply, h0', vecCoef_zero, zero_smul]))
    have hsuppG : ∀ z : ℂ, (Function.support (vecFam g u₀ u₁ z)).Finite := fun z =>
      hg.subset (fun m hm => by
        simp only [Function.mem_support] at hm ⊢
        intro h0'
        exact hm (by rw [vecFam_apply, h0', vecCoef_zero, zero_smul]))
    have hu₀nonneg : 0 ≤ u₀ := by
      rw [hu₀']
      refine mul_nonneg (le_of_lt hp'pos) ?_
      rw [sub_nonneg, ← inv_one]
      exact (inv_le_inv₀ hp₀_pos (by norm_num)).mpr hp₀1
    have hu₁nonneg : 0 ≤ u₁ := by
      rw [hu₁']
      refine mul_nonneg (le_of_lt hp'pos) ?_
      rw [sub_nonneg, ← inv_one]
      exact (inv_le_inv₀ hp₁_pos (by norm_num)).mpr hp₁1
    -- the left edge
    have hedge0 : ∀ z ∈ Complex.re ⁻¹' {0},
        ‖Ffun z‖ ≤ (C₀ : ℝ) * U.toReal ^ t₀ * V.toReal ^ u₀ := by
      intro z hz
      have hz0 : z.re = 0 := hz
      have hE : ‖Ffun z‖ₑ ≤ (C₀ : ENNReal) * U ^ t₀ * V ^ u₀ := by
        rw [show ‖Ffun z‖ₑ = pairingEnorm (iwConv A Φ (vecFam f t₀ t₁ (star z)))
            (vecFam g u₀ u₁ z) from rfl]
        by_cases hp₀one : p₀ = 1
        · have hq₀one : q₀ = 1 := by
            rw [show q₀ = ENNReal.ofReal p₀ from (ENNReal.ofReal_toReal hq₀_ne_top).symm,
              hp₀one, ENNReal.ofReal_one]
          have hu₀0 : u₀ = 0 := by rw [hu₀', hp₀one, inv_one, sub_self, mul_zero]
          have hholder := pairingEnorm_le (iwConv A Φ (vecFam f t₀ t₁ (star z)))
            (vecFam g u₀ u₁ z) (hsuppG z)
            (show ENNReal.HolderConjugate (1 : ENNReal) (⊤ : ENNReal) from inferInstance)
          have h1 : eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) 1 countZ ≤
              (C₀ : ENNReal) * eLpNorm (vecFam f t₀ t₁ (star z)) 1 countZ := by
            have hh := h0 H (vecFam f t₀ t₁ (star z)) (hsuppF z)
            rw [hq₀one, ENNReal.ofReal_coe_nnreal] at hh
            exact hh
          have h2 : eLpNorm (vecFam f t₀ t₁ (star z)) 1 countZ = U ^ t₀ := by
            have h2' := eLpNorm_vecFam_re_zero (f := f) (p₀ := 1) (p₁ := p₁) (p := p)
              one_pos hp₁_pos hp_pos (μ := countZ) (z := star z) (by simpa using hz0)
            rw [← hUdef, div_one, ENNReal.ofReal_one] at h2'
            have ht₀p : t₀ = p := by rw [ht₀def, hp₀one, inv_one, mul_one]
            have ht₁p : t₁ = p / p₁ := by rw [ht₁def, div_eq_mul_inv]
            rw [ht₀p, ht₁p]
            exact h2'
          have h3 : eLpNorm (vecFam g u₀ u₁ z) (⊤ : ENNReal) countZ ≤ V ^ u₀ := by
            rw [hu₀0, ENNReal.rpow_zero, eLpNorm_exponent_top (hf := by pw_aesm)]
            refine eLpNormEssSup_le_of_ae_enorm_bound (C := 1) ?_
            refine Filter.Eventually.of_forall fun n => ?_
            have hzexp : (expFamily ((0 : ℝ) : ℂ) (u₁ : ℂ) z).re = 0 := by
              rw [expFamily_ofReal_re, hz0]; ring
            exact enorm_vecFam_le_one hzexp n
          refine le_trans hholder ?_
          calc eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) 1 countZ *
                eLpNorm (vecFam g u₀ u₁ z) (⊤ : ENNReal) countZ
              ≤ ((C₀ : ENNReal) * U ^ t₀) * V ^ u₀ := by
                refine mul_le_mul (le_trans h1 (le_of_eq (by rw [h2]))) h3 bot_le bot_le
            _ = (C₀ : ENNReal) * U ^ t₀ * V ^ u₀ := rfl
        · have hp₀gt1 : 1 < p₀ := lt_of_le_of_ne hp₀1 (Ne.symm hp₀one)
          have hp₀'pos : 0 < p₀' := by
            rw [hp₀'def, inv_pos]
            exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp₀gt1)
          have hholder := pairingEnorm_le (iwConv A Φ (vecFam f t₀ t₁ (star z)))
            (vecFam g u₀ u₁ z) (hsuppG z)
            (ennreal_holderConjugate_ofReal (show p₀.HolderConjugate p₀' from by
              rw [Real.holderConjugate_iff]
              exact ⟨hp₀gt1, by rw [hp₀'def, inv_inv]; ring⟩))
          have h1 : eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) (ENNReal.ofReal p₀) countZ ≤
              (C₀ : ENNReal) * eLpNorm (vecFam f t₀ t₁ (star z)) (ENNReal.ofReal p₀) countZ := by
            have hh := h0 H (vecFam f t₀ t₁ (star z)) (hsuppF z)
            rwa [show q₀ = ENNReal.ofReal p₀ from (ENNReal.ofReal_toReal hq₀_ne_top).symm,
              ENNReal.ofReal_coe_nnreal] at hh
          have h2 : eLpNorm (vecFam f t₀ t₁ (star z)) (ENNReal.ofReal p₀) countZ = U ^ t₀ := by
            have h2' := eLpNorm_vecFam_re_zero (f := f) (p₀ := p₀) (p₁ := p₁) (p := p)
              hp₀_pos hp₁_pos hp_pos (μ := countZ) (z := star z) (by simpa using hz0)
            rw [← hUdef] at h2'
            have ht₀p : t₀ = p / p₀ := by rw [ht₀def, div_eq_mul_inv]
            have ht₁p : t₁ = p / p₁ := by rw [ht₁def, div_eq_mul_inv]
            rw [ht₀p, ht₁p]
            exact h2'
          have h3 : eLpNorm (vecFam g u₀ u₁ z) (ENNReal.ofReal p₀') countZ ≤ V ^ u₀ := by
            have h3' := eLpNorm_vecFam_re_zero_left (f := g) (t₀ := u₀) (t₁ := u₁) (p₀ := p₀') (p := p')
              (by rw [hu₀def, div_eq_mul_inv]) hp₀'pos hp'pos (μ := countZ) (z := z) hz0
            rw [← hVdef, div_eq_mul_inv, ← hu₀def] at h3'
            exact le_of_eq h3'
          refine le_trans hholder ?_
          calc eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) (ENNReal.ofReal p₀) countZ *
                eLpNorm (vecFam g u₀ u₁ z) (ENNReal.ofReal p₀') countZ
              ≤ ((C₀ : ENNReal) * U ^ t₀) * V ^ u₀ := by
                refine le_trans (mul_le_mul_of_nonneg_right h1 bot_le) ?_
                rw [h2]
                exact mul_le_mul_of_nonneg_left h3 bot_le
            _ = (C₀ : ENNReal) * U ^ t₀ * V ^ u₀ := rfl
      rw [← ofReal_norm] at hE
      rw [← ENNReal.ofReal_coe_nnreal (p := C₀), ← ofReal_toReal_mul_rpow (m := (C₀ : ℝ))
        (U := U) (V := V) (by positivity) hUfin hVfin ht₀_pos.le hu₀nonneg] at hE
      rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
    -- the right edge
    have hedge1 : ∀ z ∈ Complex.re ⁻¹' {1},
        ‖Ffun z‖ ≤ (C₁ : ℝ) * U.toReal ^ t₁ * V.toReal ^ u₁ := by
      intro z hz
      have hz1 : z.re = 1 := hz
      have hE : ‖Ffun z‖ₑ ≤ (C₁ : ENNReal) * U ^ t₁ * V ^ u₁ := by
        rw [show ‖Ffun z‖ₑ = pairingEnorm (iwConv A Φ (vecFam f t₀ t₁ (star z)))
            (vecFam g u₀ u₁ z) from rfl]
        by_cases hp₁one : p₁ = 1
        · have hq₁one : q₁ = 1 := by
            rw [show q₁ = ENNReal.ofReal p₁ from (ENNReal.ofReal_toReal hq₁_ne_top).symm,
              hp₁one, ENNReal.ofReal_one]
          have hu₁0 : u₁ = 0 := by rw [hu₁', hp₁one, inv_one, sub_self, mul_zero]
          have hholder := pairingEnorm_le (iwConv A Φ (vecFam f t₀ t₁ (star z)))
            (vecFam g u₀ u₁ z) (hsuppG z)
            (show ENNReal.HolderConjugate (1 : ENNReal) (⊤ : ENNReal) from inferInstance)
          have h1 : eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) 1 countZ ≤
              (C₁ : ENNReal) * eLpNorm (vecFam f t₀ t₁ (star z)) 1 countZ := by
            have hh := h1 H (vecFam f t₀ t₁ (star z)) (hsuppF z)
            rw [hq₁one, ENNReal.ofReal_coe_nnreal] at hh
            exact hh
          have h2 : eLpNorm (vecFam f t₀ t₁ (star z)) 1 countZ = U ^ t₁ := by
            have h2' := eLpNorm_vecFam_re_one (f := f) (p₀ := p₀) (p₁ := 1) (p := p)
              hp₀_pos one_pos hp_pos (μ := countZ) (z := star z)
              (by rw [show (star z).re = z.re from rfl, hz1])
            rw [← hUdef, div_one, ENNReal.ofReal_one] at h2'
            have ht₁p : t₁ = p := by rw [ht₁def, hp₁one, inv_one, mul_one]
            have ht₀p : t₀ = p / p₀ := by rw [ht₀def, div_eq_mul_inv]
            rw [show t₁ = p from ht₁p, show t₀ = p / p₀ from ht₀p]
            exact h2'
          have h3 : eLpNorm (vecFam g u₀ u₁ z) (⊤ : ENNReal) countZ ≤ V ^ u₁ := by
            rw [hu₁0, ENNReal.rpow_zero, eLpNorm_exponent_top (hf := by pw_aesm)]
            refine eLpNormEssSup_le_of_ae_enorm_bound (C := 1) ?_
            refine Filter.Eventually.of_forall fun n => ?_
            have hzexp : (expFamily (u₀ : ℂ) ((0 : ℝ) : ℂ) z).re = 0 := by
              rw [expFamily_ofReal_re, hz1]; ring
            exact enorm_vecFam_le_one hzexp n
          refine le_trans hholder ?_
          calc eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) 1 countZ *
                eLpNorm (vecFam g u₀ u₁ z) (⊤ : ENNReal) countZ
              ≤ ((C₁ : ENNReal) * U ^ t₁) * V ^ u₁ := by
                refine mul_le_mul (le_trans h1 (le_of_eq (by rw [h2]))) h3 bot_le bot_le
            _ = (C₁ : ENNReal) * U ^ t₁ * V ^ u₁ := rfl
        · have hp₁gt1 : 1 < p₁ := lt_of_le_of_ne hp₁1 (Ne.symm hp₁one)
          have hp₁'pos : 0 < p₁' := by
            rw [hp₁'def, inv_pos]
            exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp₁gt1)
          have hholder := pairingEnorm_le (iwConv A Φ (vecFam f t₀ t₁ (star z)))
            (vecFam g u₀ u₁ z) (hsuppG z)
            (ennreal_holderConjugate_ofReal (show p₁.HolderConjugate p₁' from by
              rw [Real.holderConjugate_iff]
              exact ⟨hp₁gt1, by rw [hp₁'def, inv_inv]; ring⟩))
          have h1 : eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) (ENNReal.ofReal p₁) countZ ≤
              (C₁ : ENNReal) * eLpNorm (vecFam f t₀ t₁ (star z)) (ENNReal.ofReal p₁) countZ := by
            have hh := h1 H (vecFam f t₀ t₁ (star z)) (hsuppF z)
            rwa [show q₁ = ENNReal.ofReal p₁ from (ENNReal.ofReal_toReal hq₁_ne_top).symm,
              ENNReal.ofReal_coe_nnreal] at hh
          have h2 : eLpNorm (vecFam f t₀ t₁ (star z)) (ENNReal.ofReal p₁) countZ = U ^ t₁ := by
            have h2' := eLpNorm_vecFam_re_one (f := f) (p₀ := p₀) (p₁ := p₁) (p := p)
              hp₀_pos hp₁_pos hp_pos (μ := countZ) (z := star z)
              (by rw [show (star z).re = z.re from rfl, hz1])
            rw [← hUdef] at h2'
            have ht₀p : t₀ = p / p₀ := by rw [ht₀def, div_eq_mul_inv]
            have ht₁p : t₁ = p / p₁ := by rw [ht₁def, div_eq_mul_inv]
            rw [ht₀p, ht₁p]
            exact h2'
          have h3 : eLpNorm (vecFam g u₀ u₁ z) (ENNReal.ofReal p₁') countZ ≤ V ^ u₁ := by
            have h3' := eLpNorm_vecFam_re_one_right (f := g) (t₀ := u₀) (t₁ := u₁) (p₁ := p₁') (p := p')
              (by rw [hu₁def, div_eq_mul_inv]) hp₁'pos hp'pos (μ := countZ) (z := z) hz1
            rw [← hVdef, div_eq_mul_inv, ← hu₁def] at h3'
            exact le_of_eq h3'
          refine le_trans hholder ?_
          calc eLpNorm (iwConv A Φ (vecFam f t₀ t₁ (star z))) (ENNReal.ofReal p₁) countZ *
                eLpNorm (vecFam g u₀ u₁ z) (ENNReal.ofReal p₁') countZ
              ≤ ((C₁ : ENNReal) * U ^ t₁) * V ^ u₁ := by
                refine le_trans (mul_le_mul_of_nonneg_right h1 bot_le) ?_
                rw [h2]
                exact mul_le_mul_of_nonneg_left h3 bot_le
            _ = (C₁ : ENNReal) * U ^ t₁ * V ^ u₁ := rfl
      rw [← ofReal_norm] at hE
      rw [← ENNReal.ofReal_coe_nnreal (p := C₁), ← ofReal_toReal_mul_rpow (m := (C₁ : ℝ))
        (U := U) (V := V) (by positivity) hUfin hVfin ht₁_pos.le hu₁nonneg] at hE
      rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
    have hhad := norm_le_interp_of_strip_edges hθ0 hθ1 hFdiff hFbdd hedge0 hedge1
    have hFθ : Ffun (θ : ℂ) = ∑' n : ℤ, ⟪iwConv A Φ f n, g n⟫_ℂ := by
      rw [hFfundef]
      show (∑' n : ℤ, ⟪iwConv A Φ (vecFam f t₀ t₁ (star (θ : ℂ))) n,
        vecFam g u₀ u₁ (θ : ℂ) n⟫_ℂ) = _
      have htC : (1 - (θ : ℂ)) * (t₀ : ℂ) + (θ : ℂ) * (t₁ : ℂ) = 1 := by
        have h : (1 - (θ : ℂ)) * (t₀ : ℂ) + (θ : ℂ) * (t₁ : ℂ)
            = (((1 - θ) * t₀ + θ * t₁ : ℝ) : ℂ) := by
          push_cast; ring
        rw [h, ht, Complex.ofReal_one]
      have huC : (1 - (θ : ℂ)) * (u₀ : ℂ) + (θ : ℂ) * (u₁ : ℂ) = 1 := by
        have h : (1 - (θ : ℂ)) * (u₀ : ℂ) + (θ : ℂ) * (u₁ : ℂ)
            = (((1 - θ) * u₀ + θ * u₁ : ℝ) : ℂ) := by
          push_cast; ring
        rw [h, hu, Complex.ofReal_one]
      rw [← starRingEnd_apply, Complex.conj_ofReal, vecFam_self htC, vecFam_self huC]
    have harith : ((C₀ : ℝ) * U.toReal ^ t₀ * V.toReal ^ u₀) ^ (1 - θ)
        * ((C₁ : ℝ) * U.toReal ^ t₁ * V.toReal ^ u₁) ^ θ
        = (C₀ : ℝ) ^ (1 - θ) * (C₁ : ℝ) ^ θ * U.toReal * V.toReal :=
      rpow_interp_arith (by positivity) (by positivity)
        (ENNReal.toReal_pos hU0 hUt) (ENNReal.toReal_pos hV0 hVt) ht hu
    have hconv : ENNReal.ofReal (((C₀ : ℝ) * U.toReal ^ t₀ * V.toReal ^ u₀) ^ (1 - θ)
        * ((C₁ : ℝ) * U.toReal ^ t₁ * V.toReal ^ u₁) ^ θ)
        = (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ * U * V := by
      rw [harith, ofReal_arith_convert (by positivity) (by positivity) hUfin hVfin hθ0 hθ1,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    calc pairingEnorm (iwConv A Φ f) g
        = ‖Ffun (θ : ℂ)‖ₑ := by rw [pairingEnorm, hFθ]
      _ = ENNReal.ofReal ‖Ffun (θ : ℂ)‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (((C₀ : ℝ) * U.toReal ^ t₀ * V.toReal ^ u₀) ^ (1 - θ)
            * ((C₁ : ℝ) * U.toReal ^ t₁ * V.toReal ^ u₁) ^ θ) :=
          ENNReal.ofReal_le_ofReal hhad
      _ = (C₀ : ENNReal) ^ (1 - θ) * (C₁ : ENNReal) ^ θ * U * V := hconv
  exact hmain
end Work.Analysis.IWMultiplier
