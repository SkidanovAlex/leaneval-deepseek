import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.acoeff_DzIter_le
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.Series.DecayRem
import Submission.Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## 4. The slot series of `psiSeries α G` for a compactly supported source -/

noncomputable section

/-- The radial mode functions of the modal series. -/
noncomputable def modRad (α : ℝ) (G : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => Work.FTS.PhiStar.Series.acoeff α j G z

/-- The `(l,m)` slot series of `psiSeries α G`, written with `D_z` powers. -/
noncomputable def dzS (α : ℝ) (G : ℝ → ℝ → ℝ) (l m : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑' j : ℕ, (Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
    * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)

variable {α : ℝ} {G : ℝ → ℝ → ℝ} {a b : ℝ}

/-- The mode coefficients of a compactly supported smooth source are `C^∞` on `(0,∞)`. -/
theorem cmode_smoothOn (hα : 0 < α) (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0) (j n : ℕ) :
    ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Series.cmode j G z) (Set.Ioi 0) := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry G) :=
    contDiff_infty.mpr (fun n => hG.1 n)
  exact (Work.FTS.ClassCHon.CmpSupp.cmode_facts ha hsm hsupp).1 j n

/-- The radial mode functions are `C^∞` on `(0,∞)`. -/
theorem modRad_smoothOn (hα : 0 < α) (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (j n : ℕ) : ContDiffOn ℝ n (modRad α G j) (Set.Ioi 0) :=
  Work.FTS.PhiStar.FlatWAux.contDiffOn_radGreen α j n
    (cmode_smoothOn hα hG ha hsupp j n)

/-- The `m = 0` mode vanishes, and so do all its `D_z`-derivatives. -/
theorem DzIter_modRad_zero (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0)
    (l : ℕ) : ∀ z θ : ℝ, 0 < z →
      Work.Spaces.DzIter l (fun z' _ => modRad α G 0 z') z θ = 0 := by
  induction l with
  | zero =>
      intro z θ hz
      exact Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α G hFs z hz
  | succ l ih =>
      intro z θ hz
      have hev : (fun z' => Work.Spaces.DzIter l (fun z' _ => modRad α G 0 z') z' θ)
          =ᶠ[𝓝 z] 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz'
      show z * deriv (fun z' => Work.Spaces.DzIter l (fun z' _ => modRad α G 0 z') z' θ) z = 0
      rw [hev.deriv_eq]
      simp

/-! ### Boundedness and continuity of the slot series -/

/-- The weight profile is bounded by `1` on `[0,∞)`. -/
theorem phiWt_le_one {α : ℝ} (hα : 0 < α) {z : ℝ} (hz : 0 ≤ z) : phiWt α z ≤ 1 := by
  have h2α : (0:ℝ) < 2 / α := by positivity
  have h7α : (0:ℝ) < 7 / α := by positivity
  by_cases hz1 : z ≤ 1
  · have hz2 : z ^ (2 / α) ≤ 1 := Real.rpow_le_one hz hz1 h2α.le
    have hden : 1 ≤ (1 + z) ^ (7 / α) := Real.one_le_rpow (by linarith) h7α.le
    have hpos : 0 < (1 + z) ^ (7 / α) := lt_of_lt_of_le one_pos hden
    calc phiWt α z = z ^ (2 / α) / (1 + z) ^ (7 / α) := rfl
      _ ≤ 1 / 1 := div_le_div₀ (by positivity) hz2 one_pos hden
      _ = 1 := by norm_num
  · have hz1' : (1:ℝ) ≤ z := le_of_lt (not_le.mp hz1)
    have hden : z ^ (7 / α) ≤ (1 + z) ^ (7 / α) := Real.rpow_le_rpow (by linarith) (by linarith) h7α.le
    have hpos : 0 < (1 + z) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
    have hzpos : 0 < z ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
    calc phiWt α z = z ^ (2 / α) / (1 + z) ^ (7 / α) := rfl
      _ ≤ z ^ (2 / α) / z ^ (7 / α) := div_le_div_of_nonneg_left (by positivity) hzpos hden
      _ = z ^ (2 / α - 7 / α) := by rw [← Real.rpow_sub (by linarith) (2 / α) (7 / α)]
      _ = z ^ (-5 / α) := by ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1'
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hα.le)

/-- `D_z^l` of a `C^∞` (in both variables) function is again `C^∞`. -/
theorem DzIter_contDiffOn_two_var (hα : 0 < α) (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0) (j l n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ =>
      Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z θ)) (Set.Ioi 0 ×ˢ Set.univ) := by
  induction l generalizing n with
  | zero =>
      have h := modRad_smoothOn hα hG ha hsupp j n
      exact h.comp contDiffOn_fst (fun p hp => hp.1)
  | succ l ih =>
      have h' : ContDiffOn ℝ (n + 1) (Function.uncurry (fun z θ : ℝ =>
          Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z θ)) (Set.Ioi 0 ×ˢ Set.univ) :=
        ih (n + 1)
      have hcu := Work.FTS.PhiStar.Honesty.currySmooth_fin_end
        (V := Set.Ioi 0 ×ˢ (Set.univ : Set ℝ)) (isOpen_Ioi.prod isOpen_univ) n h'
      have hmono : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ =>
          Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z θ))
          (Set.Ioi 0 ×ˢ Set.univ) := by
        refine hcu.2.2.1.congr (fun p _ => ?_)
        rfl
      exact hmono

/-- **The slot series is bounded by a multiple of `Φ`.** -/
theorem dzS_abs_le (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) (l m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
      |dzS α G l m z θ| ≤ C * phiWt α z := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.FTS.PhiStar.Honesty.acoeff_DzIter_le hα hα4 ha hab hG hsupp l (4 * m + 8)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le m
  have hsumm : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(4 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) 1).mpr h1
    refine h2.congr (fun n => ?_)
    push_cast
    ring_nf
  have hT0 : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(4 : ℝ)) :=
    tsum_nonneg fun j => Real.rpow_nonneg (by positivity) _
  refine ⟨C₁ * C₂ * (∑' j : ℕ, ((j : ℝ) + 1) ^ (-(4 : ℝ))) + 1, by positivity, ?_⟩
  intro z θ hz hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hΦ : 0 ≤ phiWt α z := phiWt_nonneg (le_of_lt hz)
  have hpt : ∀ j : ℕ,
      |(Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
        * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)|
        ≤ (C₁ * C₂ * phiWt α z) * ((j : ℝ) + 1) ^ (-(4 : ℝ)) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [DzIter_modRad_zero (α := α) hFs l z 0 hz]
      simp only [zero_mul, abs_zero]
      positivity
    · have h1 : |Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0|
          ≤ C₁ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z := hC₁ j hj z hz
      have h2 : |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ|
          ≤ C₂ * ((j : ℝ) + 1) ^ (4 * m + 4 : ℕ) := hC₂ j θ hθI
      have h4 : |(Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)|
          ≤ (C₁ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z)
            * (C₂ * ((j : ℝ) + 1) ^ (4 * m + 4)) := by
        rw [abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      refine h4.trans (le_of_eq ?_)
      rw [← Real.rpow_natCast ((j:ℝ)+1) (4 * m + 4)]
      rw [show C₁ * ((j:ℝ)+1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α z
            * (C₂ * ((j:ℝ)+1) ^ ((4 * m + 4 : ℕ) : ℝ))
          = (C₁ * C₂ * phiWt α z) *
            (((j:ℝ)+1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * ((j:ℝ)+1) ^ ((4 * m + 4 : ℕ) : ℝ)) by ring,
        ← Real.rpow_add (show (0:ℝ) < (j:ℝ) + 1 by positivity),
        show -((4 * m + 8 : ℕ) : ℝ) + ((4 * m + 4 : ℕ) : ℝ) = -(4:ℝ) by push_cast; ring]
  have hle : |dzS α G l m z θ| ≤ (C₁ * C₂ * phiWt α z)
      * (∑' j : ℕ, ((j : ℝ) + 1) ^ (-(4 : ℝ))) := by
    have hmaj : Summable (fun j : ℕ =>
        (C₁ * C₂ * phiWt α z) * ((j : ℝ) + 1) ^ (-(4 : ℝ))) := hsumm.mul_left _
    have hsum2 : Summable (fun j : ℕ =>
        (Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)) :=
      Summable.of_norm_bounded hmaj (fun j => by simpa using hpt j)
    have h1 : ‖∑' j : ℕ, (Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)‖
        ≤ ∑' j : ℕ, ‖(Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)‖ :=
      norm_tsum_le_tsum_norm (f := fun j : ℕ =>
        (Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ))
        hsum2.norm
    have h2 : (∑' j : ℕ, ‖(Work.Spaces.DzIter l (fun z' _ => modRad α G j z') z 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) θ)‖)
        ≤ ∑' j : ℕ, (C₁ * C₂ * phiWt α z) * ((j : ℝ) + 1) ^ (-(4 : ℝ)) :=
      Summable.tsum_le_tsum (fun j => by simpa using hpt j)
        hsum2.norm hmaj
    have h3 := h1.trans h2
    rw [tsum_mul_left] at h3
    rw [Real.norm_eq_abs] at h3
    exact h3
  refine hle.trans ?_
  nlinarith [hT0, hC₁pos, hC₂pos, hΦ, phiWt_le_one hα (le_of_lt hz)]

/-! ### Continuity and the two derivative identities -/

/-- The `D_z`-iterates of the radial modes, seen as functions of `z` alone. -/
theorem deriv_DzIter_zOnly (l j : ℕ) :
    ∀ z : ℝ, 0 < z →
      deriv (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) z
        = Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0 / z := by
  intro z hz
  have h : Work.Spaces.DzIter (l + 1) (fun z' _ => modRad α G j z') z 0
      = z * deriv (fun y => Work.Spaces.DzIter l (fun z' _ => modRad α G j z') y 0) z := rfl
  rw [h, mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-- **Continuity of the slot series on the open quadrant.** -/
theorem dzS_continuousOn (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) (l m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => dzS α G l m p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.FTS.PhiStar.Honesty.acoeff_DzIter_le hα hα4 ha hab hG hsupp l (4 * m + 8)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.FTS.PhiStar.Series.eFam_iteratedDeriv_le m
  have hsumm : Summable (fun j : ℕ => (C₁ * C₂) * ((j : ℝ) + 1) ^ (-(4 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) 1).mpr h1
    have h3 : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(4 : ℝ))) := by
      refine h2.congr (fun n => ?_)
      push_cast
      ring_nf
    exact h3.mul_left _
  refine continuousOn_tsum (f := fun j (p : ℝ × ℝ) =>
      (Work.Spaces.DzIter l (fun z' _ => modRad α G j z') p.1 0)
        * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) p.2)) ?_ hsumm ?_
  · intro j
    have hz : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DzIter l (fun z' _ => modRad α G j z') p.1 0)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
      ((DzIter_contDiffOn_two_var hα hG ha hsupp j l 0).continuousOn).comp
        (continuousOn_fst.prodMk continuousOn_const)
        (fun p hp => ⟨hp.1, trivial⟩)
    have hθ : ContinuousOn (fun p : ℝ × ℝ =>
        iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) :=
      (continuous_iteratedDeriv_eFam m j).comp_continuousOn continuousOn_snd
    exact hz.mul hθ
  · intro j p hp
    have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
    have hΦ : phiWt α p.1 ≤ 1 := phiWt_le_one hα (le_of_lt hp.1)
    have hΦnn : 0 ≤ phiWt α p.1 := phiWt_nonneg (le_of_lt hp.1)
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [DzIter_modRad_zero (α := α) hFs l p.1 0 hp.1]
      simp only [zero_mul, norm_zero]
      positivity
    · have h1 : |Work.Spaces.DzIter l (fun z' _ => modRad α G j z') p.1 0|
          ≤ C₁ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α p.1 :=
        hC₁ j hj p.1 hp.1
      have h2 : |iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) p.2|
          ≤ C₂ * ((j : ℝ) + 1) ^ (4 * m + 4) := hC₂ j p.2 hθI
      have h3 : ‖(Work.Spaces.DzIter l (fun z' _ => modRad α G j z') p.1 0)
          * (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j) p.2)‖
          ≤ C₁ * ((j : ℝ) + 1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α p.1
            * (C₂ * ((j : ℝ) + 1) ^ (4 * m + 4)) := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      refine h3.trans ?_
      have hexp : -((4 * m + 8 : ℕ) : ℝ) + ((4 * m + 4 : ℕ) : ℝ) = -(4:ℝ) := by
        push_cast
        ring
      have hjp : (0:ℝ) < (j : ℝ) + 1 := by positivity
      rw [← Real.rpow_natCast ((j:ℝ)+1) (4 * m + 4)]
      have hkey : C₁ * ((j:ℝ)+1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * phiWt α p.1
            * (C₂ * ((j:ℝ)+1) ^ ((4 * m + 4 : ℕ) : ℝ))
          = (C₁ * C₂ * phiWt α p.1) *
            (((j:ℝ)+1) ^ (-((4 * m + 8 : ℕ) : ℝ)) * ((j:ℝ)+1) ^ ((4 * m + 4 : ℕ) : ℝ)) := by
        ring
      rw [hkey, ← Real.rpow_add hjp, hexp]
      have hC12 : (0:ℝ) ≤ C₁ * C₂ := by positivity
      have hb : C₁ * C₂ * phiWt α p.1 ≤ C₁ * C₂ := by
        have := mul_le_mul_of_nonneg_left hΦ hC12
        simpa using this
      exact mul_le_mul_of_nonneg_right hb
        (Real.rpow_nonneg (show (0:ℝ) ≤ (j:ℝ) + 1 by positivity) _)
end

end Work.FTS.PhiStar.Honesty
