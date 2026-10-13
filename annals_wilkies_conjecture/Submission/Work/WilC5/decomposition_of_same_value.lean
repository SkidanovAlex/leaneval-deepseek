/-
  WilC5 — the decomposition `w = z (1 + ε)` of vdDMM Lemma 4.2.

  Given two elements `w`, `z` of a model `M ⊨ TR` with `z ≠ 0` and `v(w) = v(z)`
  (`Work.WilC5.SameArch w z`), the quotient `w / z` is a *unit* of the standard real valuation
  (`Work.WilC5.SameArch_iff_IsUnitVal_div`), hence of finite value, so the standard-part theorem
  `Work.WilC5.stdPart` gives a real `r` with `w / z - c_r` infinitesimal.  The real `r` is nonzero
  (otherwise `w / z` would be both a unit and infinitesimal), and dividing by the *constant*
  `c_r = realConst M r` — which is a unit because `r ≠ 0` — turns that infinitesimal into the
  infinitesimal `ε` of the decomposition

      `w = (c_r · z) · (1 + ε)`.

  The auxiliary facts about constants used here — that `r ↦ c_r` respects multiplication, absolute
  values, is injective, and that a nonzero constant is bounded below by `1/(K+1)` — are proved in
  the section `ConstAux` below (the first by the same transfer argument that gives `realConst_add`
  in `stdPart.lean`, the last by the Archimedean property of `ℝ`).
-/
import Mathlib
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.RealConst

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. More arithmetic of the constants `c_r = realConst M r`. -/

section ConstAux
variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]

/-- `c_{r*s} = c_r * c_s`. -/
private def mulSent (r s : ℝ) : LRc.BoundedFormula Empty 0 :=
  Term.bdEqual (constTermL (α := Empty ⊕ Fin 0) (r * s))
    (tMulL (constTermL (α := Empty ⊕ Fin 0) r) (constTermL (α := Empty ⊕ Fin 0) s))

private theorem mulSent_realize {M : Type} [LRc.Structure M] (r s : ℝ) :
    (mulSent r s).Realize (emptyVar : Empty → M) Fin.elim0 ↔
      realConst M (r * s) = mulEL (realConst M r) (realConst M s) := by
  rw [mulSent, BoundedFormula.realize_bdEqual]
  simp only [realize_constTermL, realize_tMulL]

theorem realConst_mul (r s : ℝ) :
    realConst M (r * s) = realConst M r * realConst M s := by
  have h := (mulSent_realize (M := M) r s).mp
    (transfer_sent (M := M) inferInstance (mulSent r s) (by
      rw [mulSent_realize]
      simp only [realConst_real, mulEL_real]))
  simpa only [mulEL_eq_mul] using h

theorem realConst_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ realConst M r := by
  have h := realConst_le (M := M) 0 r hr
  rwa [realConst_zero] at h

theorem realConst_nonpos {r : ℝ} (hr : r ≤ 0) : realConst M r ≤ 0 := by
  have h := realConst_le (M := M) r 0 hr
  rwa [realConst_zero] at h

/-- The constants commute with absolute value. -/
theorem realConst_abs (r : ℝ) : realConst M |r| = |realConst M r| := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, abs_of_nonneg (realConst_nonneg hr)]
  · rw [abs_of_nonpos hr, realConst_neg, abs_of_nonpos (realConst_nonpos hr)]

/-- The map `r ↦ c_r` is injective at zero: a nonzero real constant is nonzero in `M`. -/
theorem realConst_ne_zero {r : ℝ} (hr : r ≠ 0) : realConst M r ≠ 0 := by
  intro h
  have h1 := realConst_mul (M := M) r r⁻¹
  rw [mul_inv_cancel₀ hr, realConst_one, h, zero_mul] at h1
  exact one_ne_zero h1

/-- A nonzero real constant is bounded **below** by `1/(K+1)`, i.e. is a unit of the standard
real valuation.  This is the Archimedean property of `ℝ` transferred through the monotone
embedding `realConst`. -/
theorem exists_inv_le_abs_realConst (r : ℝ) (hr : r ≠ 0) :
    ∃ K : ℕ, ((K : M) + 1)⁻¹ ≤ |realConst M r| := by
  have hrpos : 0 < |r| := abs_pos.mpr hr
  obtain ⟨n, hn⟩ := exists_nat_ge (|r|⁻¹ : ℝ)
  have hnposR : (0 : ℝ) < n := lt_of_lt_of_le (inv_pos.mpr hrpos) hn
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have hle : (n : ℝ)⁻¹ ≤ |r| := by
    have h := (inv_le_inv₀ hnposR (inv_pos.mpr hrpos)).mpr hn
    simpa using h
  obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hnpos)
  refine ⟨K, ?_⟩
  have hle' : ((K : ℝ) + 1)⁻¹ ≤ |r| := by
    have h := hle
    rw [hK, Nat.cast_succ] at h
    exact h
  have h1 : realConst M ((K : ℝ) + 1)⁻¹ ≤ realConst M |r| := realConst_le _ _ hle'
  have h2 : realConst M ((K : ℝ) + 1)⁻¹ = ((K : M) + 1)⁻¹ := by
    rw [realConst_inv _ (by positivity)]
    have hcast : realConst M ((K : ℝ) + 1) = (K : M) + 1 := by
      rw [show ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℝ) by push_cast; ring, realConst_natCast,
        Nat.cast_succ]
    rw [hcast]
  rw [h2, realConst_abs] at h1
  exact h1

end ConstAux

/-! ## 2. Dividing an infinitesimal by a nonzero constant. -/

section DivConst
variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

/-- If `c ≠ 0` is bounded below by some `1/(K+1)` (in particular if `c` is a nonzero constant of a
model of `TR`) and `x` is infinitesimal, then `x / c` is infinitesimal. -/
theorem isInfinitesimal_div_const {c x : M} (_hc : c ≠ 0)
    (hclow : ∃ K : ℕ, ((K : M) + 1)⁻¹ ≤ |c|) (hx : IsInfinitesimal x) :
    IsInfinitesimal (x / c) := by
  intro N
  obtain ⟨K, hK⟩ := hclow
  have hcpos : 0 < |c| := lt_of_lt_of_le (by positivity) hK
  have hbase : (((N * K + N + K : ℕ)) : M) + 1 = ((N : M) + 1) * ((K : M) + 1) := by
    push_cast; ring
  have hxN : |x| ≤ ((((N * K + N + K : ℕ)) : M) + 1)⁻¹ := hx _
  have hstep : |x| ≤ ((N : M) + 1)⁻¹ * |c| := by
    rw [hbase, mul_inv] at hxN
    calc |x| ≤ ((N : M) + 1)⁻¹ * ((K : M) + 1)⁻¹ := hxN
      _ ≤ ((N : M) + 1)⁻¹ * |c| := mul_le_mul_of_nonneg_left hK (by positivity)
  rw [abs_div, div_le_iff₀ hcpos]
  exact hstep

end DivConst

/-! ## 3. The decomposition. -/

theorem decomposition_of_same_value {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    {w z : M} (hz : z ≠ 0) (hwz : Work.WilC5.SameArch w z) :
    ∃ r : ℝ, r ≠ 0 ∧ ∃ ε : M, Work.WilC5.IsInfinitesimal ε ∧
      w = (Work.WilC5.realConst M r * z) * (1 + ε) := by
  -- `w / z` is a unit of the standard real valuation, hence of finite value.
  have hunit : IsUnitVal (w / z) := (SameArch_iff_IsUnitVal_div hz).mp hwz
  obtain ⟨N₀, hN₀low, hN₀high⟩ := hunit
  -- its standard part `r`
  obtain ⟨r, hr⟩ := stdPart (M := M) (show IsFiniteVal (w / z) from ⟨N₀, hN₀high⟩)
  -- `r` is nonzero: otherwise `w / z` would be both a unit and infinitesimal.
  have hrne : r ≠ 0 := by
    intro h0
    rw [h0, realConst_zero, sub_zero] at hr
    have h1 : |w / z| ≤ ((N₀ : M) + 2)⁻¹ := by
      have h := hr (N₀ + 1)
      have hc : (((N₀ + 1 : ℕ) : M) + 1) = ((N₀ : M) + 2) := by push_cast; ring
      rwa [hc] at h
    have h2 : ((N₀ : M) + 2)⁻¹ < ((N₀ : M) + 1)⁻¹ := by
      have hlt : (N₀ : M) + 1 < (N₀ : M) + 2 := by linarith
      have := (inv_lt_inv₀ (show (0 : M) < (N₀ : M) + 2 by positivity)
        (show (0 : M) < (N₀ : M) + 1 by positivity)).mpr hlt
      simpa using this
    linarith
  refine ⟨r, hrne, (w / z - realConst M r) / realConst M r, ?_, ?_⟩
  · exact isInfinitesimal_div_const (realConst_ne_zero hrne)
      (exists_inv_le_abs_realConst r hrne) hr
  · have hcne : realConst M r ≠ 0 := realConst_ne_zero hrne
    have key : realConst M r * (1 + (w / z - realConst M r) / realConst M r) = w / z := by
      have h1 : realConst M r * ((w / z - realConst M r) / realConst M r)
          = w / z - realConst M r := mul_div_cancel₀ _ hcne
      rw [mul_add, mul_one, h1]
      ring
    have hwz : w = z * (w / z) := (mul_div_cancel₀ w hz).symm
    calc w = z * (w / z) := hwz
      _ = z * (realConst M r * (1 + (w / z - realConst M r) / realConst M r)) := by rw [key]
      _ = (realConst M r * z) * (1 + (w / z - realConst M r) / realConst M r) := by ring

end Work.WilC5
