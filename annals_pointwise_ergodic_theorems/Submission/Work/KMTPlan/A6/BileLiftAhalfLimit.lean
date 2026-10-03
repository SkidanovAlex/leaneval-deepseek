import Mathlib
import Submission.Work.KMTPlan.A6.BileLiftDefs
import Submission.Work.Analysis.Concentration.Basic
import Submission.Work.KMTPlan.A6.riemannSum_limit_engine
import Submission.Work.KMTPlan.A6.psiLift_estimates

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open MeasureTheory Filter Polynomial Finset
open scoped ENNReal BigOperators Topology
open Work.Analysis.Concentration

lemma bile_sq_inv_sqrt (R : ℕ) :
    ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * ((Real.sqrt (R : ℝ))⁻¹ : ℂ) = ((R : ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg R), Complex.ofReal_natCast]

noncomputable def bileLiftA {Q : ℕ} (z : ZMod Q) (n : ℕ) : ℝ := (z.val : ℝ) - (n : ℝ)

noncomputable def bileLiftB (P : Polynomial ℤ) {Q : ℕ} (z : ZMod Q) (n : ℕ) : ℝ :=
  (z.val : ℝ) - ((Polynomial.eval (n : ℤ) P : ℤ) : ℝ)

noncomputable def bileLiftD (P : Polynomial ℤ) {Q : ℕ} (N : ℕ) (u v : ZMod Q → ℂ) (z : ZMod Q)
    (n : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * (u (z - (n : ZMod Q)) * v (z - polyEvalZMod P Q (n : ZMod Q)))

noncomputable def bileLiftPhi (P : Polynomial ℤ) (ψ : ℝ → ℂ) {Q : ℕ} (N : ℕ) (u v : ZMod Q → ℂ)
    (z : ZMod Q) : ℕ → ℝ → ℂ :=
  fun R t => ∑ n ∈ Finset.Icc (N / 2 + 1) N,
    ψ (t + bileLiftA z n / (R : ℝ)) * ψ (t + bileLiftB P z n / (R : ℝ)) * bileLiftD P N u v z n

noncomputable def bileLiftPsi (P : Polynomial ℤ) (ψ : ℝ → ℂ) {Q : ℕ} (N : ℕ) (u v : ZMod Q → ℂ)
    (z : ZMod Q) : ℝ → ℝ :=
  fun t => ‖ψ t‖ ^ 2 * ‖∑ n ∈ Finset.Icc (N / 2 + 1) N, bileLiftD P N u v z n‖

lemma bileLiftD_sum (P : Polynomial ℤ) {Q : ℕ} [NeZero Q] (N : ℕ) (u v : ZMod Q → ℂ) (z : ZMod Q) :
    ∑ n ∈ Finset.Icc (N / 2 + 1) N, bileLiftD P N u v z n = bileHalvedAvg P N u v z := by
  have h1 : ∀ n : ℕ, u (z - ((n : ℤ) : ZMod Q)) = u (z - (n : ZMod Q)) := by
    intro n; rw [Int.cast_natCast]
  have h2 : ∀ n : ℕ,
      v (z - ((Polynomial.eval (n : ℤ) P : ℤ) : ZMod Q)) = v (z - polyEvalZMod P Q (n : ZMod Q)) := by
    intro n; rw [polyEvalZMod_natCast]
  simp only [bileLiftD, bileHalvedAvg, h1, h2]
  rw [Finset.mul_sum]

lemma bileLiftSum_residue_aux (P : Polynomial ℤ) (ψ : SchwartzMap ℝ ℂ) {Q : ℕ} [NeZero Q] (N R : ℕ)
    (u v : ZMod Q → ℂ) (z : ZMod Q) (m : ℤ) :
    bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)
      = ((R : ℂ))⁻¹ * bileLiftPhi P (ψ : ℝ → ℂ) N u v z R (((Q : ℝ) * (m : ℝ)) / (R : ℝ)) := by
  have hd1 : ∀ n : ℕ,
      ((((z.val : ℤ) + (Q : ℤ) * m - (n : ℤ) : ℤ)) : ℝ) / (R : ℝ)
        = ((Q : ℝ) * (m : ℝ)) / (R : ℝ) + bileLiftA z n / (R : ℝ) := by
    intro n
    have h : ((((z.val : ℤ) + (Q : ℤ) * m - (n : ℤ) : ℤ)) : ℝ)
        = (Q : ℝ) * (m : ℝ) + bileLiftA z n := by
      simp only [bileLiftA]; push_cast; ring
    rw [h, add_div]
  have hd2 : ∀ n : ℕ,
      ((((z.val : ℤ) + (Q : ℤ) * m - (Polynomial.eval (n : ℤ) P : ℤ) : ℤ)) : ℝ) / (R : ℝ)
        = ((Q : ℝ) * (m : ℝ)) / (R : ℝ) + bileLiftB P z n / (R : ℝ) := by
    intro n
    have h : ((((z.val : ℤ) + (Q : ℤ) * m - (Polynomial.eval (n : ℤ) P : ℤ) : ℤ)) : ℝ)
        = (Q : ℝ) * (m : ℝ) + bileLiftB P z n := by
      simp only [bileLiftB]; push_cast; ring
    rw [h, add_div]
  have hu : ∀ n : ℕ, ((((z.val : ℤ) + (Q : ℤ) * m - (n : ℤ) : ℤ)) : ZMod Q) = z - (n : ZMod Q) := by
    intro n
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  have hv : ∀ n : ℕ, ((((z.val : ℤ) + (Q : ℤ) * m - (Polynomial.eval (n : ℤ) P : ℤ) : ℤ)) : ZMod Q)
      = z - polyEvalZMod P Q (n : ZMod Q) := by
    intro n
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val, ← polyEvalZMod_natCast]
  simp only [bileLiftSum, bileLift, bileLiftPhi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hd1 n, hd2 n, hu n, hv n]
  rw [show ((R : ℂ))⁻¹ = ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * ((Real.sqrt (R : ℝ))⁻¹ : ℂ)
        from (bile_sq_inv_sqrt R).symm]
  simp only [bileLiftD]
  ring

lemma bile_eLpNorm_count_one (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm f (1 : ℝ≥0∞) MeasureTheory.Measure.count = ∑' x : ℤ, ‖f x‖ₑ := by
  rw [Commons.MeasureTheory.Function.eLpNorm_count (by norm_num) (by norm_num)]
  simp [ENNReal.toReal_one, ENNReal.rpow_one]

lemma bile_integral_normSq_psi (ψ : SchwartzMap ℝ ℂ)
    (hψ : MeasureTheory.eLpNorm (ψ : ℝ → ℂ) 2 MeasureTheory.volume = 1) :
    ∫ t : ℝ, ‖(ψ t : ℂ)‖ ^ 2 = 1 := by
  have hm : MemLp (ψ : ℝ → ℂ) 2 (volume : Measure ℝ) := ψ.memLp 2 volume
  have h := hψ
  rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hm] at h
  simp only [ENNReal.toReal_ofNat] at h
  have hX : (∫ t : ℝ, ‖(ψ t : ℂ)‖ ^ (2:ℝ)) ^ ((2:ℝ)⁻¹) = 1 := (ENNReal.ofReal_eq_one.mp h)
  have h2 := Real.rpow_mul (show (0:ℝ) ≤ ∫ t : ℝ, ‖(ψ t : ℂ)‖ ^ (2:ℝ) by positivity) ((2:ℝ)⁻¹) 2
  rw [show ((2:ℝ)⁻¹ * 2) = 1 by norm_num, Real.rpow_one] at h2
  have key : (∫ t : ℝ, ‖(ψ t : ℂ)‖ ^ (2:ℝ)) = 1 := by rw [h2, hX]; norm_num
  simpa only [Real.rpow_ofNat] using key

lemma bile_tsum_int_residue {Q : ℕ} [NeZero Q] (g : ℤ → ℝ≥0∞) :
    ∑' x : ℤ, g x = ∑ z : ZMod Q, ∑' m : ℤ, g ((z.val : ℤ) + (Q : ℤ) * m) := by
  have hQne : (Q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
  let e : ZMod Q × ℤ ≃ ℤ :=
    { toFun := fun p => (p.1.val : ℤ) + (Q : ℤ) * p.2
      invFun := fun x => ((x : ZMod Q), x / (Q : ℤ))
      left_inv := by
        rintro ⟨z, m⟩
        simp only [Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · show (((z.val : ℤ) + (Q : ℤ) * m : ℤ) : ZMod Q) = z
          push_cast
          rw [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero]
        · show ((z.val : ℤ) + (Q : ℤ) * m) / (Q : ℤ) = m
          rw [Int.add_mul_ediv_left (z.val : ℤ) m hQne,
            Int.ediv_eq_zero_of_lt (Int.natCast_nonneg z.val) (by exact_mod_cast ZMod.val_lt z),
            zero_add]
      right_inv := by
        intro x
        show ((x : ZMod Q).val : ℤ) + (Q : ℤ) * (x / (Q : ℤ)) = x
        rw [ZMod.val_intCast]
        exact Int.emod_add_mul_ediv x (Q : ℤ) }
  have h1 : (∑' p : ZMod Q × ℤ, g (e p)) = ∑' x : ℤ, g x := Equiv.tsum_eq e g
  rw [← h1, ENNReal.tsum_prod', tsum_fintype]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  refine tsum_congr (fun m => ?_)
  dsimp only [e]
  rfl

theorem BileLiftAhalfLimit (P : Polynomial ℤ) (ψ : SchwartzMap ℝ ℂ)
    (hψ : MeasureTheory.eLpNorm (ψ : ℝ → ℂ) 2 MeasureTheory.volume = 1)
    {Q N : ℕ} [NeZero Q] (hQ : 1 ≤ Q) (hN : Q ≤ N) (u v : ZMod Q → ℂ) :
    Filter.Tendsto (fun R : ℕ => MeasureTheory.eLpNorm
        (Work.KMTPlan.A6.bileLiftSum P (ψ : ℝ → ℂ) R N u v) 1 MeasureTheory.Measure.count)
      Filter.atTop
      (nhds (ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (Work.KMTPlan.A6.bileHalvedAvg P N u v)))) := by
  have hQpos : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
  have hψint : ∫ t : ℝ, ‖(ψ t : ℂ)‖ ^ 2 = 1 := bile_integral_normSq_psi ψ hψ
  have hz : ∀ z : ZMod Q, Filter.Tendsto (fun R : ℕ => ∑' m : ℤ,
      ENNReal.ofReal ((R : ℝ)⁻¹ * ‖bileLiftPhi P (ψ : ℝ → ℂ) N u v z R
        (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖))
      Filter.atTop (nhds (ENNReal.ofReal ((Q : ℝ)⁻¹ * ‖bileHalvedAvg P N u v z‖))) := by
    intro z
    obtain ⟨A, hA, h1, h2, h3, h4⟩ :=
      psiLift_estimates (Finset.Icc (N / 2 + 1) N) ψ (bileLiftD P N u v z) (bileLiftA z) (bileLiftB P z)
    have hconv : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℝ,
        |‖bileLiftPhi P (ψ : ℝ → ℂ) N u v z R t‖ - bileLiftPsi P (ψ : ℝ → ℂ) N u v z t| ≤ ε := by
      intro ε hε
      obtain ⟨R₀, hR₀⟩ := h4 ε hε
      refine ⟨R₀, fun R hR t => ?_⟩
      have hpe : bileLiftPsi P (ψ : ℝ → ℂ) N u v z t
          = ‖(ψ t) ^ 2 * (∑ n ∈ Finset.Icc (N / 2 + 1) N, bileLiftD P N u v z n)‖ := by
        simp only [bileLiftPsi, norm_mul, norm_pow]
      rw [hpe]
      exact (abs_norm_sub_norm_le _ _).trans (hR₀ R hR t)
    have heng := riemannSum_limit_engine Q hQpos (bileLiftPhi P (ψ : ℝ → ℂ) N u v z)
      (bileLiftPsi P (ψ : ℝ → ℂ) N u v z) A hA h1 h2 h3 hconv
    have hint : ∫ t : ℝ, bileLiftPsi P (ψ : ℝ → ℂ) N u v z t = ‖bileHalvedAvg P N u v z‖ := by
      have hc := bileLiftD_sum (P := P) (N := N) (u := u) (v := v) z
      simp only [bileLiftPsi, hc]
      rw [MeasureTheory.integral_mul_const, hψint, one_mul]
    rw [hint] at heng
    exact heng
  have hLHS : ∀ R : ℕ, MeasureTheory.eLpNorm
        (bileLiftSum P (ψ : ℝ → ℂ) R N u v) 1 MeasureTheory.Measure.count
      = ∑ z : ZMod Q, ∑' m : ℤ,
          ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖ₑ := by
    intro R
    rw [bile_eLpNorm_count_one, bile_tsum_int_residue (Q := Q)]
  have hz2 : ∀ z : ZMod Q, Filter.Tendsto (fun R : ℕ => ∑' m : ℤ,
        ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖ₑ)
      Filter.atTop (nhds (ENNReal.ofReal ((Q : ℝ)⁻¹ * ‖bileHalvedAvg P N u v z‖))) := by
    intro z
    have hpoint : ∀ (R : ℕ) (m : ℤ),
        ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖ₑ
          = ENNReal.ofReal ((R : ℝ)⁻¹ * ‖bileLiftPhi P (ψ : ℝ → ℂ) N u v z R
              (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖) := by
      intro R m
      rw [show ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖ₑ
            = ENNReal.ofReal ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖
          from by simp [enorm_eq_nnnorm],
        bileLiftSum_residue_aux P ψ N R u v z m, norm_mul, norm_inv, Complex.norm_natCast]
    have hcongr : (fun R : ℕ => ∑' m : ℤ,
          ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖ₑ)
        = (fun R : ℕ => ∑' m : ℤ, ENNReal.ofReal ((R : ℝ)⁻¹ * ‖bileLiftPhi P (ψ : ℝ → ℂ) N u v z R
              (((Q : ℝ) * (m : ℝ)) / (R : ℝ))‖)) := by
      funext R
      exact tsum_congr (fun m => hpoint R m)
    rw [hcongr]
    exact hz z
  have htotal : Filter.Tendsto (fun R : ℕ => ∑ z : ZMod Q, ∑' m : ℤ,
        ‖bileLiftSum P (ψ : ℝ → ℂ) R N u v ((z.val : ℤ) + (Q : ℤ) * m)‖ₑ)
      Filter.atTop (nhds (∑ z : ZMod Q, ENNReal.ofReal ((Q : ℝ)⁻¹ * ‖bileHalvedAvg P N u v z‖))) :=
    tendsto_finsetSum Finset.univ (fun z _ => hz2 z)
  have hval : (∑ z : ZMod Q, ENNReal.ofReal ((Q : ℝ)⁻¹ * ‖bileHalvedAvg P N u v z‖))
      = ENNReal.ofReal (LpNormZMod Q 1 (bileHalvedAvg P N u v)) := by
    have hlp : LpNormZMod Q 1 (bileHalvedAvg P N u v)
        = (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖bileHalvedAvg P N u v z‖ := by
      simp only [LpNormZMod, div_one, Real.rpow_one]
    have hsum1 : (∑ z : ZMod Q, ENNReal.ofReal ((Q : ℝ)⁻¹ * ‖bileHalvedAvg P N u v z‖))
        = ∑ z : ZMod Q, ENNReal.ofReal ((Q : ℝ)⁻¹) * ENNReal.ofReal ‖bileHalvedAvg P N u v z‖ :=
      Finset.sum_congr rfl (fun z _ => ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hQ0)))
    have hsum2 : ENNReal.ofReal (LpNormZMod Q 1 (bileHalvedAvg P N u v))
        = ∑ z : ZMod Q, ENNReal.ofReal ((Q : ℝ)⁻¹) * ENNReal.ofReal ‖bileHalvedAvg P N u v z‖ := by
      rw [hlp, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hQ0)),
        ENNReal.ofReal_sum_of_nonneg (fun z _ => norm_nonneg _), Finset.mul_sum]
    exact hsum1.trans hsum2.symm
  rw [funext hLHS, ← hval]
  exact htotal

end Work.KMTPlan.A6
