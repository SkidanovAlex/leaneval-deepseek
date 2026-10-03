import Mathlib
import Submission.Work.KMTPlan.A6Clean.charSumParseval
import Submission.Work.KMTPlan.A6Clean.VrScalarDomination
import Submission.Work.A6HighLow.ennreal_mixed_minkowski_rpow

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. Parseval for the `Q`-torsion character sums -/

/-- `‖star z‖ₑ = ‖z‖ₑ` for `z : ℂ`. -/
private lemma enorm_star_complex (z : ℂ) : ‖star z‖ₑ = ‖z‖ₑ := by
  simp only [← ofReal_norm, norm_star]

/-- Every `Q`-torsion element of the circle is `i/Q mod 1` for some `i : ZMod Q`. -/
private lemma torsion_exists {Q : ℕ} [NeZero Q] {α : AddCircle (1 : ℝ)}
    (hα : (Q : ℕ) • α = 0) : ∃ i : ZMod Q, (ZMod.toAddCircle i : AddCircle (1 : ℝ)) = α := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = α :=
    ⟨Quotient.out α, QuotientAddGroup.out_eq' α⟩
  rw [← hx] at hα
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hα
  obtain ⟨m, hm⟩ := hα
  rw [zsmul_one, nsmul_eq_mul] at hm
  refine ⟨(m : ZMod Q), ?_⟩
  rw [ZMod.toAddCircle_intCast, ← hx]
  congr 1
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  rw [hm]
  field_simp

/-- The `ZMod Q`-index set of a `Q`-torsion `Finset` of the circle. -/
private noncomputable def torsionIdx (Q : ℕ) [NeZero Q] (A : Finset Circ) : Finset (ZMod Q) :=
  Finset.univ.filter (fun i => (ZMod.toAddCircle i : Circ) ∈ A)

private lemma torsionIdx_image {Q : ℕ} [NeZero Q] {A : Finset Circ}
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0) :
    A = (torsionIdx Q A).image ZMod.toAddCircle := by
  classical
  ext α
  constructor
  · intro hα
    obtain ⟨i, hi⟩ := torsion_exists (Q := Q) (hA α hα)
    refine Finset.mem_image.mpr ⟨i, ?_, hi⟩
    rw [torsionIdx, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, by rw [hi]; exact hα⟩
  · intro hα
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
    rw [torsionIdx, Finset.mem_filter] at hi
    exact hi.2

private lemma sum_fourier_transport {Q : ℕ} [NeZero Q] {A : Finset Circ}
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0) (k : ℤ) (d : Circ → ℂ) :
    (∑ α ∈ A, fourier (T := 1) k α * d α)
      = ∑ i ∈ torsionIdx Q A, ZMod.stdAddChar (i * (k : ZMod Q)) * d (ZMod.toAddCircle i) := by
  classical
  conv_lhs => rw [torsionIdx_image hA]
  rw [Finset.sum_image (fun x _ y _ hxy => ZMod.toAddCircle_injective Q hxy)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.KMTPlan.A6.StdAddCharFourier i k]

private lemma sum_zmod_val {Q : ℕ} [NeZero Q] (h : ℕ → ENNReal) :
    (∑ θ : ZMod Q, h θ.val) = ∑ n₀ ∈ Finset.range Q, h n₀ := by
  refine Finset.sum_bij (fun θ _ => θ.val) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a _ b _ hab
    rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
  · intro b hb
    exact ⟨((b : ℕ) : ZMod Q), Finset.mem_univ _,
      ZMod.val_cast_of_lt (Finset.mem_range.mp hb)⟩
  · intro a _; rfl

private lemma parseval_torsion_neg {Q : ℕ} [NeZero Q] (A : Finset Circ)
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0) (d : Circ → ℂ) :
    (∑ θ : ZMod Q, ‖∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * d α‖ₑ ^ (2 : ℝ))
      = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖d α‖ ^ 2) := by
  classical
  set B := torsionIdx Q A with hB
  set dz : ZMod Q → ℂ := fun i => d (ZMod.toAddCircle i) with hdz
  have hkey : ∀ θ : ZMod Q, (∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * d α)
      = ∑ i ∈ B, ZMod.stdAddChar (-(i * θ)) * dz i := by
    intro θ
    rw [sum_fourier_transport hA (-(θ.val : ℤ)) d, hB]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hcast : ((↑(-(θ.val : ℤ)) : ZMod Q)) = -θ := by
      rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hcast, mul_neg]
  calc (∑ θ : ZMod Q, ‖∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * d α‖ₑ ^ (2 : ℝ))
      = ∑ θ : ZMod Q, ENNReal.ofReal (‖∑ i ∈ B, ZMod.stdAddChar (-(i * θ)) * dz i‖ ^ 2) := by
        refine Finset.sum_congr rfl (fun θ _ => ?_)
        rw [hkey θ, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∑ θ : ZMod Q, ‖∑ i ∈ B, ZMod.stdAddChar (-(i * θ)) * dz i‖ ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg (fun θ _ => sq_nonneg _)).symm
    _ = ENNReal.ofReal ((Q : ℝ) * ∑ i ∈ B, ‖dz i‖ ^ 2) := by
        rw [sum_normSq_charSum]
    _ = (Q : ENNReal) * ENNReal.ofReal (∑ i ∈ B, ‖dz i‖ ^ 2) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg Q), ENNReal.ofReal_natCast]
    _ = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖d α‖ ^ 2) := by
        congr 1
        rw [hB]
        conv_rhs => rw [torsionIdx_image hA]
        rw [Finset.sum_image (fun x _ y _ hxy => ZMod.toAddCircle_injective Q hxy)]

private lemma parseval_torsion_pos {Q : ℕ} [NeZero Q] (A : Finset Circ)
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0) (d : Circ → ℂ) :
    (∑ θ : ZMod Q, ‖∑ α ∈ A, fourier (T := 1) (θ.val : ℤ) α * d α‖ₑ ^ (2 : ℝ))
      = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖d α‖ ^ 2) := by
  classical
  have hconj : ∀ θ : ZMod Q,
      (∑ α ∈ A, fourier (T := 1) (θ.val : ℤ) α * d α)
        = star (∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * star (d α)) := by
    intro θ
    rw [star_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [star_mul, star_star]
    have h1 : star (fourier (T := 1) (-(θ.val : ℤ)) α) = fourier (T := 1) (θ.val : ℤ) α := by
      rw [fourier_neg]; simp
    rw [h1]
    exact mul_comm _ _
  calc (∑ θ : ZMod Q, ‖∑ α ∈ A, fourier (T := 1) (θ.val : ℤ) α * d α‖ₑ ^ (2 : ℝ))
      = ∑ θ : ZMod Q,
          ‖∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * star (d α)‖ₑ ^ (2 : ℝ) := by
        refine Finset.sum_congr rfl (fun θ _ => ?_)
        rw [hconj θ, enorm_star_complex]
    _ = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖star (d α)‖ ^ 2) :=
        parseval_torsion_neg A hA (fun α => star (d α))
    _ = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖d α‖ ^ 2) := by
        simp only [norm_star]

/-- **Parseval, positive sign, range-`Q` indexing.** -/
private lemma parseval_torsion_range {Q : ℕ} [NeZero Q] (A : Finset Circ)
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0) (d : Circ → ℂ) :
    (∑ n₀ ∈ Finset.range Q, ‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * d α‖ₑ ^ (2 : ℝ))
      = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖d α‖ ^ 2) := by
  rw [← sum_zmod_val (fun n₀ => ‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * d α‖ₑ ^ (2 : ℝ))]
  exact parseval_torsion_pos A hA d

/-- **Parseval in the `eLpNorm` form** (negative sign). -/
private lemma parseval_torsion_eLpNorm {Q : ℕ} [NeZero Q] (A : Finset Circ)
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0) (d : Circ → ℂ) :
    (MeasureTheory.eLpNorm (fun θ : ZMod Q =>
        ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * d α) 2
        (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℝ)
      = ENNReal.ofReal (∑ α ∈ A, ‖d α‖ ^ 2) := by
  have hQne : (Q : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact NeZero.ne Q
  have hQtop : (Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Q
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [eLpNorm_zmodProb_two_sq]
  rw [show (∑ θ : ZMod Q,
        ‖(∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * d α)‖ₑ ^ (2:ℕ))
      = ∑ θ : ZMod Q,
        ‖(∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * d α)‖ₑ ^ (2:ℝ) from
    Finset.sum_congr rfl (fun θ _ => (ENNReal.rpow_natCast _ 2).symm)]
  rw [parseval_torsion_neg A hA d, ← mul_assoc, ENNReal.inv_mul_cancel hQne hQtop, one_mul]

/-- `(Σ_i ‖v_i‖^r)^(1/r) = (Σ_i ‖v_i‖ₑ^r)^(1/r)` in `ℝ≥0∞` (the `ℓ^r` chain sum). -/
private lemma ofReal_chain_eq {r : NNReal} (hr : 1 ≤ r) {J : ℕ} (k : Fin (J + 1) → ℕ)
    (a : ℕ → ℂ) :
    ENNReal.ofReal ((∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)))
      = (∑ i : Fin J, (‖a (k i.succ) - a (k i.castSucc)‖ₑ) ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hS : (0 : ℝ) ≤ ∑ i : Fin J, ‖a (k i.succ) - a (k i.castSucc)‖ ^ (r : ℝ) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [← ENNReal.ofReal_rpow_of_nonneg (p := 1 / (r : ℝ)) hS (by positivity)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hrpos.le, ofReal_norm]

/-! ## 2. The character-sum datum against the residue data -/

/-- The main theorem. -/
theorem charSumResidueTwo {Q : ℕ} [NeZero Q] (R : NNReal) (hR : 2 ≤ R)
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (hA : ∀ α ∈ A, (Q : ℕ) • α = 0)
    (φ : Work.Analysis.IonescuWainger.Circle → ℂ) (hφ : ∀ α, ‖φ α‖ = 1)
    (c : ℕ → Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.KMTPlan.A6.VrLiftDataP (R : ℝ) Q
        (fun n θ => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c n α)
      ≤ Work.KMTAreas.A7.residueLp 2 Q
          (fun _ n₀ => PointwiseErgodicTheorems.variationalNorm R
            (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α))) 0
        + Work.KMTAreas.A7.residueLp 2 Q
          (fun _ n₀ => PointwiseErgodicTheorems.variationalNorm R
            (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α))) 0 := by
  classical
  have hQne : (Q : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact NeZero.ne Q
  have hQtop : (Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Q
  have hR1nn : (1 : NNReal) ≤ R := le_trans (by norm_num) hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1nn
  have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  set W : ℤ → ℕ → ENNReal := fun x n₀ => PointwiseErgodicTheorems.variationalNorm R
      (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) with hW
  set X : ENNReal := Work.KMTAreas.A7.residueLp 2 Q W 0 with hX
  have hXsq : X ^ (2 : ℝ) = (Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q, (W 0 n₀) ^ (2 : ℝ) := by
    rw [hX]
    simp only [Work.KMTAreas.A7.residueLp, ENNReal.rpow_eq_pow]
    rw [ENNReal.rpow_neg_one, ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hhalf : X = ((Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q, (W 0 n₀) ^ (2 : ℝ))
      ^ ((1 : ℝ) / 2) := by
    rw [← hXsq, ← ENNReal.rpow_mul,
      show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, ENNReal.rpow_one]
  unfold Work.KMTPlan.A6.VrLiftDataP
  simp only [ENNReal.rpow_eq_pow]
  refine add_le_add ?_ ?_
  · -- ## the supremum part
    refine iSup_le fun n => ?_
    refine (ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < 2 by norm_num)).mp ?_
    have h1 : (MeasureTheory.eLpNorm (fun θ : ZMod Q =>
          ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c n α) 2
          (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℝ)
        = ENNReal.ofReal (∑ α ∈ A, ‖c n α‖ ^ 2) :=
      parseval_torsion_eLpNorm A hA (c n)
    have h2 : ENNReal.ofReal (∑ α ∈ A, ‖c n α‖ ^ 2)
        = (Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q,
            (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)‖ₑ) ^ (2 : ℝ) := by
      have hb : (∑ n₀ ∈ Finset.range Q,
            (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)‖ₑ) ^ (2 : ℝ))
          = (Q : ENNReal) * ENNReal.ofReal (∑ α ∈ A, ‖φ α * c n α‖ ^ 2) :=
        parseval_torsion_range A hA (fun α => φ α * c n α)
      rw [hb]
      rw [show (∑ α ∈ A, ‖φ α * c n α‖ ^ 2) = ∑ α ∈ A, ‖c n α‖ ^ 2 from
        Finset.sum_congr rfl (fun α _ => by rw [norm_mul, hφ α, one_mul])]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hQne hQtop, one_mul]
    have h3 : (∑ n₀ ∈ Finset.range Q,
          (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)‖ₑ) ^ (2 : ℝ))
        ≤ ∑ n₀ ∈ Finset.range Q, (W 0 n₀) ^ (2 : ℝ) := by
      refine Finset.sum_le_sum (fun n₀ _ => ?_)
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [hW]
      exact Work.KMTAreas.A7.enorm_apply_le_variationalNorm (r := R)
        (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) n
    calc (MeasureTheory.eLpNorm (fun θ : ZMod Q =>
          ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c n α) 2
          (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℝ)
        = ENNReal.ofReal (∑ α ∈ A, ‖c n α‖ ^ 2) := h1
      _ = (Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q,
            (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)‖ₑ) ^ (2 : ℝ) := h2
      _ ≤ (Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q, (W 0 n₀) ^ (2 : ℝ) :=
          mul_le_mul' le_rfl h3
      _ = X ^ (2 : ℝ) := hXsq.symm
  · -- ## the chain part
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    -- the difference of the two residue slices is the slice of the coefficient differences
    have hbinc : ∀ (i : Fin J) (n₀ : ℕ),
        ((fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.succ)
          - (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.castSucc))
        = ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
            * (φ α * (c (k i.succ) α - c (k i.castSucc) α)) := by
      intro i n₀
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    have hnorm : ∀ (i : Fin J) (n₀ : ℕ),
        (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
            * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ)
          = ‖((fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.succ)
              - (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.castSucc))‖ₑ := by
      intro i n₀
      rw [hbinc i n₀]
    have hredEq : ∀ i : Fin J,
        ((fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c (k i.succ) α)
          - (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c (k i.castSucc) α))
        = fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α) := by
      intro i
      funext θ
      simp only [Pi.sub_apply]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    -- the per-index Parseval identity in squared form
    have hsq : ∀ i : Fin J,
        (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℝ)
        = (Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q,
            (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
              * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (2 : ℝ) := by
      intro i
      have h1 : (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℝ)
          = ENNReal.ofReal (∑ α ∈ A, ‖c (k i.succ) α - c (k i.castSucc) α‖ ^ 2) :=
        parseval_torsion_eLpNorm A hA (fun α => c (k i.succ) α - c (k i.castSucc) α)
      have h2 : ENNReal.ofReal (∑ α ∈ A, ‖c (k i.succ) α - c (k i.castSucc) α‖ ^ 2)
          = (Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q,
              (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
                * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (2 : ℝ) := by
        have hb : (∑ n₀ ∈ Finset.range Q,
              (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
                * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (2 : ℝ))
            = (Q : ENNReal) * ENNReal.ofReal
                (∑ α ∈ A, ‖φ α * (c (k i.succ) α - c (k i.castSucc) α)‖ ^ 2) :=
          parseval_torsion_range A hA
            (fun α => φ α * (c (k i.succ) α - c (k i.castSucc) α))
        rw [hb]
        rw [show (∑ α ∈ A, ‖φ α * (c (k i.succ) α - c (k i.castSucc) α)‖ ^ 2)
            = ∑ α ∈ A, ‖c (k i.succ) α - c (k i.castSucc) α‖ ^ 2 from
          Finset.sum_congr rfl (fun α _ => by rw [norm_mul, hφ α, one_mul])]
        rw [← mul_assoc, ENNReal.inv_mul_cancel hQne hQtop, one_mul]
      rw [h1, h2]
    -- the chain domination by the variational norm
    have hchain : ∀ n₀ : ℕ,
        (∑ i : Fin J, (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
            * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ))
          ^ (1 / (R : ℝ)) ≤ W 0 n₀ := by
      intro n₀
      have hAPPeq : (∑ i : Fin J, (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
              * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ))
            ^ (1 / (R : ℝ))
          = (∑ i : Fin J, (‖(fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.succ)
                - (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.castSucc)‖ₑ)
              ^ (R : ℝ)) ^ (1 / (R : ℝ)) := by
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1
        exact hnorm i n₀
      have h := ofReal_chain_sum_le_variationalNorm (r := R) hR1nn k hk
        (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α))
      rw [hW]
      calc (∑ i : Fin J, (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
              * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ))
            ^ (1 / (R : ℝ))
          = (∑ i : Fin J, (‖(fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.succ)
                - (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.castSucc)‖ₑ)
              ^ (R : ℝ)) ^ (1 / (R : ℝ)) := hAPPeq
        _ = ENNReal.ofReal ((∑ i : Fin J,
              ‖(fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.succ)
                - (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) (k i.castSucc)‖
                ^ (R : ℝ)) ^ (1 / (R : ℝ))) :=
            (ofReal_chain_eq hR1nn k
              (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α))).symm
        _ ≤ PointwiseErgodicTheorems.variationalNorm R
              (fun n => ∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α * (φ α * c n α)) := h
    -- the per-index `R`-th power in the Minkowski form
    have hterm : ∀ i : Fin J,
        (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (R : ℝ)
        = ((Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q,
            (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
              * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (2 : ℝ)) ^ ((R : ℝ) / 2) := by
      intro i
      calc (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (R : ℝ)
          = ((MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℝ)) ^ ((R : ℝ) / 2) := by
            rw [← ENNReal.rpow_mul, show (2 : ℝ) * ((R : ℝ) / 2) = (R : ℝ) by ring]
        _ = _ := by rw [hsq i]
    have hmink := Work.A6HighLow.ennreal_mixed_minkowski_rpow (R : ℝ) hR2 (J := J) (Q := Q)
      (a := fun i (n₀ : ℕ) => ‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
        * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ)
    have hstep : (∑ n₀ ∈ Finset.range Q, (∑ i : Fin J,
          (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
            * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ))
            ^ (2 / (R : ℝ)))
        ≤ ∑ n₀ ∈ Finset.range Q, (W 0 n₀) ^ (2 : ℝ) := by
      refine Finset.sum_le_sum (fun n₀ _ => ?_)
      calc (∑ i : Fin J, (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
            * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ)) ^ (2 / (R : ℝ))
          = ((∑ i : Fin J, (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
              * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ))
              ^ (1 / (R : ℝ))) ^ (2 : ℝ) := by
            rw [← ENNReal.rpow_mul, show (1 / (R : ℝ)) * 2 = 2 / (R : ℝ) by ring]
        _ ≤ (W 0 n₀) ^ (2 : ℝ) := ENNReal.rpow_le_rpow (hchain n₀) (by norm_num)
    have hredBound : (∑ i : Fin J,
          (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
            * (c (k i.succ) α - c (k i.castSucc) α)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (R : ℝ)) ^ (1 / (R : ℝ)) ≤ X :=
      calc (∑ i : Fin J,
            (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
              * (c (k i.succ) α - c (k i.castSucc) α)) 2
              (Work.KMTPlan.A6.zmodProb Q)) ^ (R : ℝ)) ^ (1 / (R : ℝ))
          = (∑ i : Fin J, ((Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q,
              (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
                * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (2 : ℝ))
                ^ ((R : ℝ) / 2)) ^ (1 / (R : ℝ)) := by
            rw [Finset.sum_congr rfl (fun i _ => hterm i)]
        _ ≤ ((Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q, (∑ i : Fin J,
              (‖∑ α ∈ A, fourier (T := 1) (n₀ : ℤ) α
                * (φ α * (c (k i.succ) α - c (k i.castSucc) α))‖ₑ) ^ (R : ℝ))
                ^ (2 / (R : ℝ))) ^ ((1 : ℝ) / 2) := hmink
        _ ≤ ((Q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range Q, (W 0 n₀) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
            ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hstep) (by norm_num)
        _ = X := hhalf.symm
    -- transfer to the difference form of the goal
    have hgoalEq : (∑ i : Fin J, (MeasureTheory.eLpNorm
          ((fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c (k i.succ) α)
            - (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α * c (k i.castSucc) α))
          2 (Work.KMTPlan.A6.zmodProb Q)) ^ (R : ℝ)) ^ (1 / (R : ℝ))
        = (∑ i : Fin J,
            (MeasureTheory.eLpNorm (fun θ : ZMod Q => ∑ α ∈ A, fourier (T := 1) (-(θ.val : ℤ)) α
              * (c (k i.succ) α - c (k i.castSucc) α)) 2
              (Work.KMTPlan.A6.zmodProb Q)) ^ (R : ℝ)) ^ (1 / (R : ℝ)) := by
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 1
      congr 1
      exact hredEq i
    exact (le_of_eq hgoalEq).trans hredBound

end Work.KMTPlan.A6Clean
