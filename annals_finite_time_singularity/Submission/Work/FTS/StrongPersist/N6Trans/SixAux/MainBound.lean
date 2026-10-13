import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the `∃ C` pipeline lemma

Instantiation of `main_bound_core`: the constant `Cf` (signed radial IBP), `C6` (plain sup at
order `≤ 4`), `Cm` (mixed sup at order `≤ 4`) and the two exceptional `L²` constants
`excC11`, `excC02` are pulled from the corresponding `∃ C` lemmas, the pointwise package
`SupPkg` is built from them (`CoefThMem 1 f` supplying the `∂_θf`-bound), and the final
constant is
`(Cf + 1030) · ((C6 + Cm + 1 + √(10·excC11) + √(10·excC02)) + (Cm + C6 + 1) + 1)`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem main_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.VocabO.CoefThMem 1 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    a + b ≤ 6 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ C * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
          * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  obtain ⟨Cf, hCf0, hflux⟩ := Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix
  obtain ⟨C6, hC60, hsup6⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.supSix
  obtain ⟨Cm, hCm0, hmixSup⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
  set E1 : ℝ := Real.sqrt (10 * excC11) with hE1
  set E2 : ℝ := Real.sqrt (10 * excC02) with hE2
  have hE10 : 0 ≤ E1 := by rw [hE1]; exact Real.sqrt_nonneg _
  have hE20 : 0 ≤ E2 := by rw [hE2]; exact Real.sqrt_nonneg _
  set Kc : ℝ := C6 + Cm + 1 + E1 + E2 with hKc
  set Lc : ℝ := Cm + C6 + 1 with hLc
  set D : ℝ := Kc + Lc + 1 with hDdef
  have hKc0 : 0 ≤ Kc := by rw [hKc]; linarith [hC60, hCm0, hE10, hE20]
  have hLc0 : 0 ≤ Lc := by rw [hLc]; linarith [hC60, hCm0]
  have hD0 : 0 ≤ D := by rw [hDdef]; linarith [hKc0, hLc0]
  have hD1 : (1 : ℝ) ≤ D := by rw [hDdef]; linarith [hKc0, hLc0]
  have hCpos : 0 < (Cf + 1030) * D :=
    mul_pos (by linarith) (by linarith [hD1])
  refine ⟨(Cf + 1030) * D, hCpos, ?_⟩
  intro α f g a b q hα hα1 hfs hfm hfc hgs hgm hgm7 hgd hab hq0 hqγ hqη
  set A : ℝ := Work.Spaces.HkNorm α 6 f with hA
  set B : ℝ := Work.Spaces.HkNorm α 6 g with hB
  set T : ℝ := Work.FTS.VocabO.CoefTh 1 f with hT
  have hA0 : 0 ≤ A := by rw [hA]; exact Work.Spaces.HkNorm_nonneg α 6 f
  have hB0 : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkNorm_nonneg α 6 g
  have hT0 : 0 ≤ T := by rw [hT]; exact Work.FTS.TransportS.coefTh_nonneg 1 f
  have hαpos : 0 < α ^ (-(1 / 2 : ℝ)) := alpha_rpow_neg_half_pos hα
  have hα1' : 1 ≤ α ^ (-(1 / 2 : ℝ)) := one_le_alpha_rpow_neg_half hα hα1
  have hB2 : B ^ 2 = Work.Spaces.HkSq α 6 g := by
    rw [hB]; exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)
  set Kf : ℝ := Kc * α ^ (-(1 / 2 : ℝ)) * A + T with hKf
  set Kg : ℝ := Lc * α ^ (-(1 / 2 : ℝ)) * B with hKg
  set Λ : ℝ := D * α ^ (-(1 / 2 : ℝ)) * (A + T) with hΛ
  have hKf0 : 0 ≤ Kf := by rw [hKf]; positivity
  have hKg0 : 0 ≤ Kg := by rw [hKg]; positivity
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hΛ1 : Kf ≤ Λ := by
    have hcoef : Kc ≤ D := by rw [hDdef]; linarith [hLc0]
    have h1 : Kc * α ^ (-(1 / 2 : ℝ)) * A ≤ D * α ^ (-(1 / 2 : ℝ)) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hαpos.le) hA0
    have hprod : (1 : ℝ) ≤ D * α ^ (-(1 / 2 : ℝ)) := by
      have := mul_le_mul hD1 hα1' (by norm_num : (0 : ℝ) ≤ 1) hD0
      simpa using this
    have h2 : T ≤ D * α ^ (-(1 / 2 : ℝ)) * T := by
      calc T = 1 * T := by ring
        _ ≤ D * α ^ (-(1 / 2 : ℝ)) * T := mul_le_mul_of_nonneg_right hprod hT0
    rw [hKf, hΛ]
    calc Kc * α ^ (-(1 / 2 : ℝ)) * A + T
        ≤ D * α ^ (-(1 / 2 : ℝ)) * A + D * α ^ (-(1 / 2 : ℝ)) * T := add_le_add h1 h2
      _ = D * α ^ (-(1 / 2 : ℝ)) * (A + T) := by ring
  have hΛ2 : Kg * A ≤ Λ * B := by
    have hcoef : Lc ≤ D := by rw [hDdef]; linarith [hKc0]
    have hAT : A ≤ A + T := by linarith [hT0]
    have h1 : Lc * α ^ (-(1 / 2 : ℝ)) ≤ D * α ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hαpos.le
    have h2 : A * B ≤ (A + T) * B := mul_le_mul_of_nonneg_right hAT hB0
    have hAB0 : 0 ≤ A * B := mul_nonneg hA0 hB0
    have hDa0 : 0 ≤ D * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hD0 hαpos.le
    calc Kg * A = ((Lc * α ^ (-(1 / 2 : ℝ))) * (A * B)) := by rw [hKg]; ring
      _ ≤ (D * α ^ (-(1 / 2 : ℝ))) * ((A + T) * B) := mul_le_mul h1 h2 hAB0 hDa0
      _ = D * α ^ (-(1 / 2 : ℝ)) * (A + T) * B := by ring
      _ = Λ * B := by rw [hΛ]
  have hΛE1 : E1 * α ^ (-(1 / 2 : ℝ)) * A ≤ Λ := by
    have hcoef : E1 ≤ D := by rw [hDdef, hKc]; linarith [hC60, hCm0, hE20, hLc0]
    have h1 : E1 * α ^ (-(1 / 2 : ℝ)) * A ≤ D * α ^ (-(1 / 2 : ℝ)) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hαpos.le) hA0
    have h2 : D * α ^ (-(1 / 2 : ℝ)) * A ≤ D * α ^ (-(1 / 2 : ℝ)) * (A + T) :=
      mul_le_mul_of_nonneg_left (by linarith [hT0]) (mul_nonneg hD0 hαpos.le)
    rw [hΛ]
    linarith
  have hΛE2 : E2 * α ^ (-(1 / 2 : ℝ)) * A ≤ Λ := by
    have hcoef : E2 ≤ D := by rw [hDdef, hKc]; linarith [hC60, hCm0, hE10, hLc0]
    have h1 : E2 * α ^ (-(1 / 2 : ℝ)) * A ≤ D * α ^ (-(1 / 2 : ℝ)) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hαpos.le) hA0
    have h2 : D * α ^ (-(1 / 2 : ℝ)) * A ≤ D * α ^ (-(1 / 2 : ℝ)) * (A + T) :=
      mul_le_mul_of_nonneg_left (by linarith [hT0]) (mul_nonneg hD0 hαpos.le)
    rw [hΛ]
    linarith
  -- ## the pointwise package
  have hsupF_pure : ∀ b2 : ℕ, b2 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b2 f z θ| ≤ Kf := by
    intro b2 hb2 z θ hz hθ hθ2
    have h := hsup6 α f hα hα1 hfs hfm b2 0 (by omega) z θ hz hθ hθ2
    rw [← hA] at h
    simp only [Work.Spaces.mixed_zero_right] at h
    have hcoef : C6 ≤ Kc := by rw [hKc]; linarith [hCm0, hE10, hE20]
    have h1 : C6 * α ^ (-(1 / 2 : ℝ)) * A ≤ Kc * α ^ (-(1 / 2 : ℝ)) * A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hαpos.le) hA0
    have h2 : Kc * α ^ (-(1 / 2 : ℝ)) * A ≤ Kf := by rw [hKf]; linarith [hT0]
    linarith [h, h1, h2]
  have hsupG_pure : ∀ b2 : ℕ, b2 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b2 g z θ| ≤ Kg := by
    intro b2 hb2 z θ hz hθ hθ2
    have h := hsup6 α g hα hα1 hgs hgm b2 0 (by omega) z θ hz hθ hθ2
    rw [← hB] at h
    simp only [Work.Spaces.mixed_zero_right] at h
    have hcoef : C6 ≤ Lc := by rw [hLc]; linarith [hCm0]
    have h1 : C6 * α ^ (-(1 / 2 : ℝ)) * B ≤ Lc * α ^ (-(1 / 2 : ℝ)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hαpos.le) hB0
    have h2 : Lc * α ^ (-(1 / 2 : ℝ)) * B ≤ Kg := by rw [hKg]
    linarith [h, h1, h2]
  have hsupF_mix : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed j i f z θ| ≤ Kf := by
    intro j i hi hij z θ hz hθ hθ2
    have h := hmixSup α f hα hα1 hfs hfm j i hi hij z θ hz hθ hθ2
    rw [← hA] at h
    have h1 : Cm * A ≤ Cm * (α ^ (-(1 / 2 : ℝ)) * A) := by
      have := le_alpha_rpow_neg_half_mul hα hα1 hA0
      linarith [mul_le_mul_of_nonneg_left this hCm0.le]
    have h2 : Cm * (α ^ (-(1 / 2 : ℝ)) * A) ≤ Kc * α ^ (-(1 / 2 : ℝ)) * A := by
      have hcoef : Cm ≤ Kc := by rw [hKc]; linarith [hC60, hE10, hE20]
      calc Cm * (α ^ (-(1 / 2 : ℝ)) * A)
          ≤ Kc * (α ^ (-(1 / 2 : ℝ)) * A) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = Kc * α ^ (-(1 / 2 : ℝ)) * A := by ring
    have h3 : Kc * α ^ (-(1 / 2 : ℝ)) * A ≤ Kf := by rw [hKf]; linarith [hT0]
    linarith [h, h1, h2, h3]
  have hsupG_mix : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed j i g z θ| ≤ Kg := by
    intro j i hi hij z θ hz hθ hθ2
    have h := hmixSup α g hα hα1 hgs hgm j i hi hij z θ hz hθ hθ2
    rw [← hB] at h
    have h1 : Cm * B ≤ Cm * (α ^ (-(1 / 2 : ℝ)) * B) := by
      have := le_alpha_rpow_neg_half_mul hα hα1 hB0
      linarith [mul_le_mul_of_nonneg_left this hCm0.le]
    have h2 : Cm * (α ^ (-(1 / 2 : ℝ)) * B) ≤ Lc * α ^ (-(1 / 2 : ℝ)) * B := by
      have hcoef : Cm ≤ Lc := by rw [hLc]; linarith [hC60]
      calc Cm * (α ^ (-(1 / 2 : ℝ)) * B)
          ≤ Lc * (α ^ (-(1 / 2 : ℝ)) * B) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = Lc * α ^ (-(1 / 2 : ℝ)) * B := by ring
    calc |Work.Spaces.mixed j i g z θ| ≤ Cm * B := h
      _ ≤ Cm * (α ^ (-(1 / 2 : ℝ)) * B) := h1
      _ ≤ Lc * α ^ (-(1 / 2 : ℝ)) * B := h2
      _ = Kg := by rw [hKg]
  have hsup_pth_f : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth f z θ| ≤ Kf := by
    intro z θ hz hθ hθ2
    obtain ⟨K, hK⟩ := hfc 0 0 (by norm_num)
    have h1 : |Work.Spaces.mixed 0 0 (Work.Spaces.pth f) z θ|
        ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 0 (Work.Spaces.pth f)) :=
      Work.FTS.H2.le_supAbsO hz hθ hθ2 hK
    have h2 : Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 0 (Work.Spaces.pth f))
        ≤ Work.FTS.VocabO.CoefTh 1 f :=
      Work.FTS.TransportS.supAbsO_le_coefTh (l := 1) (f := f) (b := 0) (i := 0) (by norm_num)
    have h3 : Work.FTS.VocabO.CoefTh 1 f ≤ Kf := by
      rw [hKf, ← hT]
      have hnn : 0 ≤ Kc * α ^ (-(1 / 2 : ℝ)) * A := by positivity
      linarith
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using
      le_trans h1 (le_trans h2 h3)
  have hpkg : SupPkg α f g Kf Kg :=
    ⟨hsupF_pure, hsupG_pure, hsupF_mix, hsupG_mix, hsup_pth_f⟩
  -- ## the signed radial IBP hypothesis
  have hflux' : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ Cf * (Kf * Work.Spaces.HkSq α 6 g) := by
    refine (hflux α f g a b q Kf hα hα1 hq0 hqγ hqη hab hfs hgs hgm hgm7 hgd
      (fun z θ hz hθ hθ2 => hsupF_pure 0 (by norm_num) z θ hz hθ hθ2)
      (fun z θ hz hθ hθ2 => ?_)).trans_eq ?_
    · have h := hsupF_pure 1 (by norm_num) z θ hz hθ hθ2
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
    · ring
  -- ## the core bound
  have hcore := main_bound_core (q := q) (Cf := Cf) (Kf := Kf) (Kg := Kg) (Λ := Λ)
    hα hα1 hfs hfm hgs hgm hgm7 hgd hpkg hKf0 hKg0 hΛ1 hΛ2 hΛE1 hΛE2 hCf0.le hflux'
    hq0 hqγ hqη hab
  -- ## the arithmetic
  refine le_trans hcore ?_
  have h16 : (((a : ℝ) + 1) * ((b : ℝ) + 1)) ≤ 16 := by
    have hab' : (a : ℝ) + b ≤ 6 := by exact_mod_cast hab
    have hsq : 0 ≤ ((a : ℝ) - b) ^ 2 := sq_nonneg _
    have h4 : 4 * (a : ℝ) * b ≤ ((a : ℝ) + b) ^ 2 := by nlinarith [hsq]
    have h36 : ((a : ℝ) + b) ^ 2 ≤ 36 := by nlinarith [hab', sq_nonneg ((a : ℝ) + b)]
    nlinarith [h4, h36]
  have hconst : max Cf 1 + 64 * (((a : ℝ) + 1) * ((b : ℝ) + 1)) + 1 ≤ Cf + 1030 := by
    have hmax : max Cf 1 ≤ Cf + 1 := max_le (by linarith) (by linarith)
    have h64 : 64 * (((a : ℝ) + 1) * ((b : ℝ) + 1)) ≤ 1024 := by linarith [h16]
    linarith
  have hΛB : Λ * Work.Spaces.HkSq α 6 g = D * α ^ (-(1 / 2 : ℝ)) * (A + T) * B ^ 2 := by
    rw [hΛ, ← hB2]
  calc (max Cf 1 + 64 * (((a : ℝ) + 1) * ((b : ℝ) + 1)) + 1)
        * (Λ * Work.Spaces.HkSq α 6 g)
      ≤ (Cf + 1030) * (D * α ^ (-(1 / 2 : ℝ)) * (A + T) * B ^ 2) := by
        rw [hΛB]
        refine mul_le_mul_of_nonneg_right hconst ?_
        positivity
    _ = (Cf + 1030) * D * α ^ (-(1 / 2 : ℝ)) * (A + T) * B ^ 2 := by ring

end Work.FTS.StrongPersist.N6Trans.SixAux
