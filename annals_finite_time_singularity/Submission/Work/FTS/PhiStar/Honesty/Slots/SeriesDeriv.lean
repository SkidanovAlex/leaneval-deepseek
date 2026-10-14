import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.Honesty.Slots.Series
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

variable {α : ℝ} {G : ℝ → ℝ → ℝ} {a b : ℝ}

/-! ### The termwise derivative identity and the identification with `psiSeries` -/

/-- **A uniform bound over all derivative orders `r ≤ m`.** -/
theorem eFam_iteratedDeriv_le_all (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, r ≤ m → ∀ j : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |iteratedDeriv r (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ C * ((j : ℝ) + 1) ^ (4 * m + 4) := by
  classical
  have hC : ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |iteratedDeriv r (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ C * ((j : ℝ) + 1) ^ (4 * r + 4) :=
    fun r => Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le r
  choose Cr hCrpos hCr using hC
  refine ⟨(∑ r ∈ Finset.range (m + 1), Cr r) + 1, ?_, ?_⟩
  · have h0 : 0 ≤ ∑ r ∈ Finset.range (m + 1), Cr r :=
      Finset.sum_nonneg fun r _ => (hCrpos r).le
    linarith
  · intro r hr j θ hθ
    have h1 : |iteratedDeriv r (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ Cr r * ((j : ℝ) + 1) ^ (4 * r + 4) := hCr r j θ hθ
    have hj1 : (1:ℝ) ≤ (j:ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have h2 : ((j:ℝ)+1) ^ (4 * r + 4 : ℕ) ≤ ((j:ℝ)+1) ^ (4 * m + 4 : ℕ) := by
      rw [← Real.rpow_natCast ((j:ℝ)+1) (4 * r + 4),
        ← Real.rpow_natCast ((j:ℝ)+1) (4 * m + 4)]
      exact Real.rpow_le_rpow_of_exponent_le hj1
        (by exact_mod_cast (show 4 * r + 4 ≤ 4 * m + 4 by omega))
    have h3 : Cr r ≤ (∑ r' ∈ Finset.range (m + 1), Cr r') + 1 := by
      have hmem : r ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
      have hle : Cr r ≤ ∑ r' ∈ Finset.range (m + 1), Cr r' :=
        Finset.single_le_sum (fun i _ => (hCrpos i).le) hmem
      linarith
    calc |iteratedDeriv r (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ Cr r * ((j:ℝ)+1) ^ (4 * r + 4 : ℕ) := h1
      _ ≤ Cr r * ((j:ℝ)+1) ^ (4 * m + 4 : ℕ) :=
          mul_le_mul_of_nonneg_left h2 (hCrpos r).le
      _ ≤ ((∑ r' ∈ Finset.range (m + 1), Cr r') + 1) * ((j:ℝ)+1) ^ (4 * m + 4 : ℕ) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)

/-- `pthIter` of a function is the corresponding iterated derivative of its `θ`-slice. -/
theorem pthIter_eq_iteratedDeriv (m : ℕ) (f : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, Work.Spaces.pthIter m f z θ = iteratedDeriv m (fun θ' => f z θ') θ := by
  induction m with
  | zero => intro z θ; rfl
  | succ m ih =>
      intro z θ
      show deriv (fun θ' => Work.Spaces.pthIter m f z θ') θ
        = iteratedDeriv (m + 1) (fun θ' => f z θ') θ
      rw [iteratedDeriv_succ]
      congr 1
      funext θ'
      exact ih z θ'

/-- **`∂_θ^m ψ` is the `(0,m)` slot series.** -/
theorem pthIter_psiSeries_eq_dzS (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) (m : ℕ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
      Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G) z θ
        = dzS α G 0 m z θ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := eFam_iteratedDeriv_le_all m
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    Work.FTS.PhiStar.Honesty.acoeff_DzIter_le hα hα4 ha hab hG hsupp 0 (4 * m + 8)
  intro z θ hz hθ
  have hsumm : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(4 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) 1).mpr h1
    refine h2.congr (fun n => ?_)
    push_cast
    ring_nf
  have hcB : Summable (fun j : ℕ =>
      |modRad α G j z| * (C₁ * ((j : ℝ) + 1) ^ (4 * m + 4))) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (by positivity))
      (fun j => ?_) (hsumm.mul_left (C₂ * C₁))
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h0 : modRad α G 0 z = 0 := Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α G hFs z hz
      rw [h0, abs_zero, zero_mul]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
    · have h1 : |Work.Spaces.DzIter 0 (fun z' _ => modRad α G j z') z 0|
          ≤ C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z :=
        hC₂ j hj z hz
      have h1' : |modRad α G j z|
          ≤ C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z := by
        simpa only [Work.Spaces.DzIter_zero] using h1
      have hΦ : phiWt α z ≤ 1 := phiWt_le_one hα (le_of_lt hz)
      have h3 : ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * ((j : ℝ) + 1) ^ (4 * m + 4 : ℕ)
          = ((j : ℝ) + 1) ^ (-(4 : ℝ)) := by
        rw [← Real.rpow_natCast ((j:ℝ)+1) (4 * m + 4),
          ← Real.rpow_add (show (0:ℝ) < (j:ℝ) + 1 by positivity)]
        congr 1
        push_cast
        ring
      have hC2nn : 0 ≤ C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) := by positivity
      calc |modRad α G j z| * (C₁ * ((j : ℝ) + 1) ^ (4 * m + 4))
          ≤ (C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z)
            * (C₁ * ((j : ℝ) + 1) ^ (4 * m + 4)) :=
            mul_le_mul_of_nonneg_right h1' (by positivity)
        _ ≤ (C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)))
            * (C₁ * ((j : ℝ) + 1) ^ (4 * m + 4)) := by
            have hh : C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z
                ≤ C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) := by
              simpa using mul_le_mul_of_nonneg_left hΦ hC2nn
            exact mul_le_mul_of_nonneg_right hh (by positivity)
        _ = C₂ * C₁ * ((j : ℝ) + 1) ^ (-(4 : ℝ)) := by
            rw [show (C₂ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)))
                  * (C₁ * ((j : ℝ) + 1) ^ (4 * m + 4))
                = C₂ * C₁ * (((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ))
                  * ((j : ℝ) + 1) ^ (4 * m + 4)) by ring, h3]
  have hq : ∀ j : ℕ, ContDiffOn ℝ m (Work.FTS.PhiStar.Gegenbauer.eFam j)
      (Set.Ioo 0 (π/2)) := fun j => (contDiff_eFam_all j m).contDiffOn
  have hqb : ∀ j r : ℕ, r ≤ m → ∀ y : ℝ, y ∈ Set.Ioo 0 (π/2) →
      |iteratedDeriv r (Work.FTS.PhiStar.Gegenbauer.eFam j) y|
        ≤ C₁ * ((j : ℝ) + 1) ^ (4 * m + 4) :=
    fun j r hr y hy => hC₁ r hr j y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hder := (Work.FTS.PhiStar.FlatWAux.Fam2Diff.TsumContDiff (k := m)
    (c := fun j => modRad α G j z) (q := fun j θ' => Work.FTS.PhiStar.Gegenbauer.eFam j θ')
    (B := fun j => C₁ * ((j : ℝ) + 1) ^ (4 * m + 4)) (a := 0) (b := Real.pi / 2)
    (by linarith [Real.pi_pos]) (fun j => by positivity) hcB hq hqb).2
  have h := hder m le_rfl θ hθ
  have hfun : (fun θ' => ∑' j : ℕ, modRad α G j z * Work.FTS.PhiStar.Gegenbauer.eFam j θ')
      = fun θ' => Work.FTS.PhiStar.Series.psiSeries α G z θ' := by
    funext θ'
    rfl
  rw [pthIter_eq_iteratedDeriv, ← hfun, h]
  rfl

/-- **The `z`-derivative of the slot series.** -/
theorem dzS_hasDerivAt_z (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) (l m : ℕ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
      HasDerivAt (fun z' => dzS α G l m z' θ) (dzS α G (l + 1) m z θ / z) z := by
  intro z θ hz hθ
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.FTS.PhiStar.Honesty.acoeff_DzIter_le hα hα4 ha hab hG hsupp l (4 * m + 12)
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.FTS.PhiStar.Honesty.acoeff_DzIter_le hα hα4 ha hab hG hsupp (l + 1) (4 * m + 12)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le m
  have hz2 : 0 < 2 / z := by positivity
  have hC0nn : 0 ≤ C₀ := hC₀pos.le
  have hC1nn : 0 ≤ C₁ := hC₁pos.le
  have hC2nn : 0 ≤ C₂ := hC₂pos.le
  have hprod0 : 0 ≤ C₁ * (2 / z) := mul_nonneg hC1nn hz2.le
  set Cm : ℝ := max C₀ (C₁ * (2 / z)) + 1 with hCm
  have hCml : C₀ ≤ Cm := by rw [hCm]; linarith [le_max_left C₀ (C₁ * (2 / z))]
  have hCmr : C₁ * (2 / z) ≤ Cm := by rw [hCm]; linarith [le_max_right C₀ (C₁ * (2 / z))]
  have hCmp : 0 < Cm := lt_of_lt_of_le hC₀pos hCml
  set B : ℕ → ℝ := fun j => Cm * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) with hBdef
  have hB0 : ∀ j : ℕ, 0 ≤ B j := fun j => by
    rw [hBdef]
    exact mul_nonneg hCmp.le (Real.rpow_nonneg (by positivity) _)
  have hsumm : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(8 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(8 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(8 : ℝ))) 1).mpr h1
    refine h2.congr (fun n => ?_)
    push_cast
    ring_nf
  have hcB : Summable (fun j : ℕ =>
      |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ| * B j) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (hB0 j))
      (fun j => ?_) (hsumm.mul_left (C₂ * Cm))
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
        ≤ C₂ * ((j : ℝ) + 1) ^ (4 * m + 4) := hC₂ j θ hθI
    have h3 : ((j : ℝ) + 1) ^ (4 * m + 4 : ℕ) * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ))
        = ((j : ℝ) + 1) ^ (-(8 : ℝ)) := by
      rw [← Real.rpow_natCast ((j:ℝ)+1) (4 * m + 4),
        ← Real.rpow_add (show (0:ℝ) < (j:ℝ) + 1 by positivity)]
      congr 1
      push_cast
      ring
    rw [hBdef]
    calc |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
          * (Cm * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)))
        ≤ (C₂ * ((j : ℝ) + 1) ^ (4 * m + 4))
          * (Cm * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ))) :=
          mul_le_mul_of_nonneg_right h2 (hB0 j)
      _ = C₂ * Cm * (((j : ℝ) + 1) ^ (4 * m + 4 : ℕ)
            * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ))) := by ring
      _ = C₂ * Cm * ((j : ℝ) + 1) ^ (-(8 : ℝ)) := by rw [h3]
  have hq : ∀ j : ℕ, ContDiffOn ℝ 1
      (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0)
      (Set.Ioo (z / 2) (2 * z)) := by
    intro j
    have h2 := DzIter_contDiffOn_two_var hα hG ha hsupp j l 1
    refine h2.comp (contDiffOn_id.prodMk
      (contDiffOn_const (c := (0:ℝ)) (s := Set.Ioo (z/2) (2*z))))
      (fun y hy => ⟨by show (0:ℝ) < y; linarith [hy.1, hz], trivial⟩)
  have hqb : ∀ j r : ℕ, r ≤ 1 → ∀ y : ℝ, y ∈ Set.Ioo (z / 2) (2 * z) →
      |iteratedDeriv r (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) y|
        ≤ B j := by
    intro j r hr y hy
    have hypos : 0 < y := by linarith [hy.1]
    have hy1 : 1 / y ≤ 2 / z := by
      rw [div_le_div_iff₀ hypos hz]
      linarith [hy.1]
    have hΦ : phiWt α y ≤ 1 := phiWt_le_one hα (le_of_lt hypos)
    have hx0 : 0 ≤ ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    interval_cases r
    · rw [iteratedDeriv_zero, hBdef]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rw [DzIter_modRad_zero (α := α) hFs l y 0 hypos, abs_zero]
        exact mul_nonneg hCmp.le hx0
      · have h1 : |Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0|
            ≤ C₀ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) := by
          have h := hC₀ j hj y hypos
          exact h.trans (by
            have hnn : 0 ≤ C₀ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) :=
              mul_nonneg hC0nn hx0
            have hstep := mul_le_mul_of_nonneg_left hΦ hnn
            rwa [mul_one] at hstep)
        exact h1.trans (mul_le_mul_of_nonneg_right hCml hx0)
    · rw [iteratedDeriv_one, hBdef]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rw [deriv_DzIter_zOnly (α := α) (G := G) l 0 y hypos,
          DzIter_modRad_zero (α := α) hFs (l+1) y 0 hypos, zero_div, abs_zero]
        exact mul_nonneg hCmp.le hx0
      · rw [deriv_DzIter_zOnly (α := α) (G := G) l j y hypos, abs_div, abs_of_pos hypos]
        have h1 : |Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') y 0|
            ≤ C₁ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) := by
          have h := hC₁ j hj y hypos
          exact h.trans (by
            have hnn : 0 ≤ C₁ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) :=
              mul_nonneg hC1nn hx0
            have hstep := mul_le_mul_of_nonneg_left hΦ hnn
            rwa [mul_one] at hstep)
        have hnn : 0 ≤ C₁ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) :=
          mul_nonneg hC1nn hx0
        calc |Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') y 0| / y
            ≤ (C₁ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ))) / y :=
              div_le_div_of_nonneg_right h1 hypos.le
          _ = C₁ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) * (1 / y) := by
              rw [div_eq_mul_inv, one_div]
          _ ≤ C₁ * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) * (2 / z) :=
              mul_le_mul_of_nonneg_left hy1 hnn
          _ = (C₁ * (2 / z)) * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) := by ring
          _ ≤ Cm * ((j : ℝ) + 1) ^ (-(((4 * m + 12 : ℕ)) : ℝ)) :=
              mul_le_mul_of_nonneg_right hCmr hx0
  have htu := Work.FTS.PhiStar.FlatWAux.Fam2Diff.TsumContDiff (k := 1)
      (c := fun j => iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)
      (q := fun j y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0)
      (B := B) (a := z / 2) (b := 2 * z) (by linarith) hB0 hcB hq hqb
  have hcont : ContDiffOn ℝ 1 (fun y => ∑' j : ℕ,
      iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
        * Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) (Set.Ioo (z/2) (2*z)) :=
    htu.1
  have hder := htu.2
  have hmain : HasDerivAt (fun y => ∑' j : ℕ,
      iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
        * Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0)
      ((∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
        * Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0) / z) z := by
    have hdiff : DifferentiableAt ℝ (fun y => ∑' j : ℕ,
        iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
          * Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) z :=
      (hcont.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt
        (by norm_num)
    refine hdiff.hasDerivAt.congr_deriv ?_
    have h := hder 1 le_rfl z ⟨by linarith, by linarith⟩
    have hrw : (∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
          * iteratedDeriv 1 (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) z)
        = (∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
          * Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0) / z := by
      have h1 : ∀ j : ℕ, iteratedDeriv 1
            (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) z
          = Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0 / z := fun j => by
        rw [iteratedDeriv_one, deriv_DzIter_zOnly (α := α) (G := G) l j z hz]
      rw [show (∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
            * iteratedDeriv 1 (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) z)
          = ∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
            * (Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0 / z) from
        tsum_congr (fun j => by rw [h1 j])]
      rw [show (∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
            * (Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0 / z))
          = ∑' j : ℕ, (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
            * Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0) / z from
        tsum_congr (fun j => (mul_div_assoc _ _ _).symm)]
      exact tsum_div_const
    rw [iteratedDeriv_one, hrw] at h
    exact h
  have hfun : (fun y => dzS α G l m y θ)
      = fun y => ∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
          * Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0 := by
    funext y
    rw [dzS]
    exact tsum_congr (fun j => by ring)
  rw [hfun]
  have hval : (∑' j : ℕ, iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ
        * Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0) / z
      = dzS α G (l + 1) m z θ / z := by
    congr 1
    rw [dzS]
    exact tsum_congr (fun j => by ring)
  rw [hval] at hmain
  exact hmain

/-- **`D_z^l ∂_θ^m ψ` is the `(l,m)` slot series.** -/
theorem DzIter_psiSeries_eq_dzS (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) (m : ℕ) :
    ∀ l : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
      Work.Spaces.DzIter l (Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G)) z θ
        = dzS α G l m z θ := by
  intro l
  induction l with
  | zero =>
      intro z θ hz hθ
      simpa only [Work.Spaces.DzIter_zero] using
        pthIter_psiSeries_eq_dzS hα hα4 hG ha hab hsupp hFs m z θ hz hθ
  | succ l ih =>
      intro z θ hz hθ
      have h1 : Work.Spaces.DzIter (l + 1)
            (Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G)) z θ
          = z * deriv (fun y => Work.Spaces.DzIter l
              (Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G)) y θ) z := rfl
      rw [h1]
      have hev : (fun y => Work.Spaces.DzIter l
            (Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G)) y θ)
          =ᶠ[𝓝 z] (fun y => dzS α G l m y θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih y θ hy hθ
      rw [hev.deriv_eq, (dzS_hasDerivAt_z hα hα4 hG ha hab hsupp hFs l m z θ hz hθ).deriv]
      field_simp

end Work.FTS.PhiStar.Honesty
