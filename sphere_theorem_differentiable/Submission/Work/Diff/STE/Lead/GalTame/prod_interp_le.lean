import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.holder2_int
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.Lead.GalTame.gnSharpClean

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp product interpolation inequality (`prod_interp_le`)

An interpolation estimate for a product of one iterated partial derivative of each of two
`1`-periodic smooth functions: for `α + β = m`,

  `∫_{cube} ‖∂^a f · ∂^b g‖² ≤ C · S² · (A + B)`

whenever `‖f‖_∞, ‖g‖_∞ ≤ S`, `ENormSq m f ≤ A` and `ENormSq m g ≤ B`.

The route is Hölder's inequality with the conjugate exponents `m/α` and `m/β` (whose
reciprocals sum to `1` because `α + β = m`), the sharp Gagliardo–Nirenberg inequality
`gnSharp` for each factor separately, the elementary sharp `H^j` interpolation, and the
weighted AM–GM inequality `A^{α/m}B^{β/m} ≤ A + B`.  The two degenerate cases `α = 0` and
`β = 0` are handled by the sup bound alone.
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators
open scoped ContDiff

set_option maxHeartbeats 1600000

/-- `x ^ θ ≤ max x 1` for `0 ≤ x`, `0 ≤ θ ≤ 1`. -/
private lemma rpow_le_max_one {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ^ θ ≤ max x 1 := by
  rcases le_total x 1 with h | h
  · have h1 : x ^ θ ≤ (1 : ℝ) ^ θ := Real.rpow_le_rpow hx h hθ0
    rw [Real.one_rpow] at h1
    exact h1.trans (le_max_right _ _)
  · have h1 : x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hθ1
    rw [Real.rpow_one] at h1
    exact h1.trans (le_max_left _ _)

/-- Weighted AM–GM in the form used below: `A ^ θ * B ^ (1 - θ) ≤ A + B`. -/
private lemma geom_mean_le_add {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : A ^ θ * B ^ (1 - θ) ≤ A + B := by
  have h1 : A ^ θ * B ^ (1 - θ) ≤ θ * A + (1 - θ) * B :=
    Real.geom_mean_le_arith_mean2_weighted hθ0 (by linarith) hA hB (by ring)
  have h2 : θ * A ≤ A := by nlinarith
  have h3 : (1 - θ) * B ≤ B := by nlinarith
  linarith

/-- `(a / b) * (b / a) = 1` for nonzero `a`, `b`. -/
private lemma div_mul_div_swap (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a / b) * (b / a) = 1 := by
  field_simp

theorem prod_interp_le {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f g : (ι → ℝ) → ℂ) (S A B : ℝ)
        (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
        (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g)
        (hfp : Work.Diff.STE.Periodic1 f) (hgp : Work.Diff.STE.Periodic1 g)
        (hS : 0 ≤ S) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
        (hfs : ∀ x : ι → ℝ, ‖f x‖ ≤ S) (hgs : ∀ x : ι → ℝ, ‖g x‖ ≤ S)
        (hfe : Work.Diff.STE.ENormSq m f ≤ A) (hge : Work.Diff.STE.ENormSq m g ≤ B),
        ∀ (α β : ℕ) (hαβ : α + β = m) (a : Fin α → ι) (b : Fin β → ι),
          ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2
            ≤ C * (S ^ 2 * (A + B)) := by
  classical
  obtain ⟨CG, hCG0, hCG⟩ := gnSharp (ι := ι) m
  refine ⟨(max CG 1 + 1) * (max CG 1 + 1), by positivity, ?_⟩
  have hC1 : (1 : ℝ) ≤ (max CG 1 + 1) * (max CG 1 + 1) := by
    have h := le_max_right CG 1
    nlinarith
  intro f g S A B hf hg hfp hgp hS hA0 hB0 hfs hgs hfe hge α β hαβ a b
  have hcontF : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x‖ ^ 2) :=
    ((Work.Diff.STE.cm_contDiff_pdList (List.ofFn a) 0 f
      (hf.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.norm).pow 2
  have hcontG : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec β b g x‖ ^ 2) :=
    ((Work.Diff.STE.cm_contDiff_pdList (List.ofFn b) 0 g
      (hg.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.norm).pow 2
  -- the common final step: `Y ≤ C * (S^2 * (A + B))` for `Y ≤ S^2 * Z`, `Z ≤ A + B`
  have htail : ∀ Y Z : ℝ, Y ≤ S ^ 2 * Z → Z ≤ A + B →
      Y ≤ (max CG 1 + 1) * (max CG 1 + 1) * (S ^ 2 * (A + B)) := by
    intro Y Z hYZ hZ
    have h1 : S ^ 2 * Z ≤ S ^ 2 * (A + B) := mul_le_mul_of_nonneg_left hZ (sq_nonneg S)
    have h2 : S ^ 2 * (A + B)
        ≤ (max CG 1 + 1) * (max CG 1 + 1) * (S ^ 2 * (A + B)) := by
      have h3 : (1 : ℝ) * (S ^ 2 * (A + B))
          ≤ ((max CG 1 + 1) * (max CG 1 + 1)) * (S ^ 2 * (A + B)) :=
        mul_le_mul_of_nonneg_right hC1 (by positivity)
      linarith
    linarith
  rcases Nat.eq_zero_or_pos α with hα0 | hα1
  · -- ## `α = 0`: only the sup bound on `f` and the energy of `g` are used
    have hβm : β = m := by omega
    rw [← hβm] at hge
    have hof : (List.ofFn a : List ι) = [] := List.ofFn_eq_nil_iff.mpr hα0
    have hpd : Work.Diff.STE.pdVec α a f = f := by
      simp only [Work.Diff.STE.pdVec, hof, Work.Diff.STE.pdList, List.foldr_nil]
    rw [show (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
        = fun x : ι → ℝ => ‖f x‖ ^ 2 * ‖Work.Diff.STE.pdVec β b g x‖ ^ 2 from by
      funext x
      rw [show Work.Diff.STE.pdVec α a f x = f x from congrFun hpd x, norm_mul, mul_pow]]
    refine htail _ (Work.Diff.STE.ENormSq β g) ?_ ?_
    · calc ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖f x‖ ^ 2 * ‖Work.Diff.STE.pdVec β b g x‖ ^ 2
          ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι),
              S ^ 2 * ‖Work.Diff.STE.pdVec β b g x‖ ^ 2 := by
            refine integral_mono_of_nonneg ?_ ?_ ?_
            · filter_upwards with x; positivity
            · exact Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
                (continuous_const.mul hcontG)
            · filter_upwards with x
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hfs x) 2)
                (by positivity)
        _ = S ^ 2 * ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec β b g x‖ ^ 2 := by
            rw [integral_const_mul]
        _ ≤ S ^ 2 * Work.Diff.STE.ENormSq β g := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg S)
            have h := Work.Diff.STE.cm_integral_pdList_le_ENormSq (List.ofFn b) g
            simpa [Work.Diff.STE.pdVec] using h
    · exact le_trans hge (by linarith)
  · rcases Nat.eq_zero_or_pos β with hβ0 | hβ1
    · -- ## `β = 0`: symmetric
      have hαm : α = m := by omega
      rw [← hαm] at hfe
      have hof : (List.ofFn b : List ι) = [] := List.ofFn_eq_nil_iff.mpr hβ0
      have hpd : Work.Diff.STE.pdVec β b g = g := by
        simp only [Work.Diff.STE.pdVec, hof, Work.Diff.STE.pdList, List.foldr_nil]
      rw [show (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
          = fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x‖ ^ 2 * ‖g x‖ ^ 2 from by
        funext x
        rw [show Work.Diff.STE.pdVec β b g x = g x from congrFun hpd x, norm_mul, mul_pow]]
      refine htail _ (Work.Diff.STE.ENormSq α f) ?_ ?_
      · calc ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x‖ ^ 2 * ‖g x‖ ^ 2
            ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec α a f x‖ ^ 2 * S ^ 2 := by
              refine integral_mono_of_nonneg ?_ ?_ ?_
              · filter_upwards with x; positivity
              · exact Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
                  (hcontF.mul continuous_const)
              · filter_upwards with x
                exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgs x) 2)
                  (by positivity)
          _ = (∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec α a f x‖ ^ 2) * S ^ 2 := by
              rw [integral_mul_const]
          _ ≤ Work.Diff.STE.ENormSq α f * S ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg S)
              have h := Work.Diff.STE.cm_integral_pdList_le_ENormSq (List.ofFn a) f
              simpa [Work.Diff.STE.pdVec] using h
          _ = S ^ 2 * Work.Diff.STE.ENormSq α f := by ring
      · exact le_trans hfe (by linarith)
    · -- ## `α, β ≥ 1`: sharp interpolation between the two energies
      have hαm : α ≤ m := by omega
      have hβm : β ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα1
      have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ1
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hαne : (α : ℝ) ≠ 0 := ne_of_gt hαR
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβR
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
      have hθ0 : 0 ≤ (α : ℝ) / (m : ℝ) := by positivity
      have hθ1 : (α : ℝ) / (m : ℝ) ≤ 1 := by
        rw [div_le_one hmR]; exact_mod_cast hαm
      have hφ0 : 0 ≤ (β : ℝ) / (m : ℝ) := by positivity
      have hφ1 : (β : ℝ) / (m : ℝ) ≤ 1 := by
        rw [div_le_one hmR]; exact_mod_cast hβm
      have hsum : (α : ℝ) / (m : ℝ) + (β : ℝ) / (m : ℝ) = 1 := by
        rw [← add_div, ← Nat.cast_add, hαβ, div_self hmne]
      have hφeq : (β : ℝ) / (m : ℝ) = 1 - (α : ℝ) / (m : ℝ) := by linarith
      -- Hölder's inequality with the exponents `m/α`, `m/β`
      have hbE1 : 1 ≤ (m : ℝ) / (α : ℝ) := by
        rw [le_div_iff₀ hαR, one_mul]; exact_mod_cast hαm
      have hcE1 : 1 ≤ (m : ℝ) / (β : ℝ) := by
        rw [le_div_iff₀ hβR, one_mul]; exact_mod_cast hβm
      have hone : 1 / ((m : ℝ) / (α : ℝ)) = (α : ℝ) / (m : ℝ) := one_div_div _ _
      have hone' : 1 / ((m : ℝ) / (β : ℝ)) = (β : ℝ) / (m : ℝ) := one_div_div _ _
      have hbc : 1 / ((m : ℝ) / (α : ℝ)) + 1 / ((m : ℝ) / (β : ℝ)) = 1 := by
        rw [hone, hone']; exact hsum
      have hHolder := Work.Diff.STE.GN.holder2_int ((m : ℝ) / (α : ℝ)) ((m : ℝ) / (β : ℝ))
          hbE1 hcE1 hbc
          (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x‖ ^ 2)
          (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec β b g x‖ ^ 2)
          hcontF hcontG (fun x => by positivity) (fun x => by positivity)
      have hLHS : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
          = ∫ x in Work.Diff.STE.unitCube (ι := ι),
              (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) * (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [norm_mul, mul_pow]
      -- ### the `f`-factor
      have hFbase : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) ^ ((m : ℝ) / (α : ℝ)))
          = ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ)) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [show (‖Work.Diff.STE.pdVec α a f x‖ ^ (2 : ℕ) : ℝ)
              = ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 : ℝ) from (Real.rpow_natCast _ 2).symm]
        rw [← Real.rpow_mul (norm_nonneg _) 2 ((m : ℝ) / (α : ℝ))]
        congr 1
        ring
      have hGNf : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ)))
          ≤ CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A := by
        have h := hCG S f hf hfp hfs α hα1 hαm a
        exact h.trans (mul_le_mul_of_nonneg_left hfe (by positivity))
      have hexp1 : (2 * (m : ℝ) / (α : ℝ) - 2) * ((α : ℝ) / (m : ℝ))
          = 2 - 2 * ((α : ℝ) / (m : ℝ)) := by
        calc (2 * (m : ℝ) / (α : ℝ) - 2) * ((α : ℝ) / (m : ℝ))
            = 2 * (((m : ℝ) / (α : ℝ)) * ((α : ℝ) / (m : ℝ))) - 2 * ((α : ℝ) / (m : ℝ)) := by
              ring
          _ = 2 * 1 - 2 * ((α : ℝ) / (m : ℝ)) := by
              rw [div_mul_div_swap (m : ℝ) (α : ℝ) hmne hαne]
          _ = 2 - 2 * ((α : ℝ) / (m : ℝ)) := by ring
      have hstepF : (CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A) ^ ((α : ℝ) / (m : ℝ))
          = CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
              * A ^ ((α : ℝ) / (m : ℝ)) := by
        rw [Real.mul_rpow (mul_nonneg hCG0 (Real.rpow_nonneg hS _)) hA0,
            Real.mul_rpow hCG0 (Real.rpow_nonneg hS _)]
        rw [← Real.rpow_mul hS (2 * (m : ℝ) / (α : ℝ) - 2) ((α : ℝ) / (m : ℝ))]
        rw [hexp1]
      have hstepF2 : CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
            * A ^ ((α : ℝ) / (m : ℝ))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) := by
        have hle := rpow_le_max_one hCG0 hθ0 hθ1
        have h1 : (0 : ℝ) ≤ S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) := Real.rpow_nonneg hS _
        have h2 : (0 : ℝ) ≤ A ^ ((α : ℝ) / (m : ℝ)) := Real.rpow_nonneg hA0 _
        calc CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
                * A ^ ((α : ℝ) / (m : ℝ))
            = CG ^ ((α : ℝ) / (m : ℝ))
                * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) := by ring
          _ ≤ (max CG 1)
                * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg h1 h2)
      have hFb : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) ^ ((m : ℝ) / (α : ℝ))) ^ (1 / ((m : ℝ) / (α : ℝ)))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) := by
        have hstep1 : (∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ))) ^ ((α : ℝ) / (m : ℝ))
            ≤ (CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A) ^ ((α : ℝ) / (m : ℝ)) :=
          Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hGNf
            (by positivity)
        calc (∫ x in Work.Diff.STE.unitCube (ι := ι),
              (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) ^ ((m : ℝ) / (α : ℝ))) ^ (1 / ((m : ℝ) / (α : ℝ)))
            = (∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ))) ^ ((α : ℝ) / (m : ℝ)) := by
              rw [hFbase, hone]
          _ ≤ (CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A) ^ ((α : ℝ) / (m : ℝ)) := hstep1
          _ = CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
                * A ^ ((α : ℝ) / (m : ℝ)) := hstepF
          _ ≤ (max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) :=
              hstepF2
      -- ### the `g`-factor
      have hGbase : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) ^ ((m : ℝ) / (β : ℝ)))
          = ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ)) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [show (‖Work.Diff.STE.pdVec β b g x‖ ^ (2 : ℕ) : ℝ)
              = ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 : ℝ) from (Real.rpow_natCast _ 2).symm]
        rw [← Real.rpow_mul (norm_nonneg _) 2 ((m : ℝ) / (β : ℝ))]
        congr 1
        ring
      have hGNg : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ)))
          ≤ CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B := by
        have h := hCG S g hg hgp hgs β hβ1 hβm b
        exact h.trans (mul_le_mul_of_nonneg_left hge (by positivity))
      have hexp2 : (2 * (m : ℝ) / (β : ℝ) - 2) * ((β : ℝ) / (m : ℝ))
          = 2 - 2 * ((β : ℝ) / (m : ℝ)) := by
        calc (2 * (m : ℝ) / (β : ℝ) - 2) * ((β : ℝ) / (m : ℝ))
            = 2 * (((m : ℝ) / (β : ℝ)) * ((β : ℝ) / (m : ℝ))) - 2 * ((β : ℝ) / (m : ℝ)) := by
              ring
          _ = 2 * 1 - 2 * ((β : ℝ) / (m : ℝ)) := by
              rw [div_mul_div_swap (m : ℝ) (β : ℝ) hmne hβne]
          _ = 2 - 2 * ((β : ℝ) / (m : ℝ)) := by ring
      have hstepG : (CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B) ^ ((β : ℝ) / (m : ℝ))
          = CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
              * B ^ ((β : ℝ) / (m : ℝ)) := by
        rw [Real.mul_rpow (mul_nonneg hCG0 (Real.rpow_nonneg hS _)) hB0,
            Real.mul_rpow hCG0 (Real.rpow_nonneg hS _)]
        rw [← Real.rpow_mul hS (2 * (m : ℝ) / (β : ℝ) - 2) ((β : ℝ) / (m : ℝ))]
        rw [hexp2]
      have hstepG2 : CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
            * B ^ ((β : ℝ) / (m : ℝ))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) := by
        have hle := rpow_le_max_one hCG0 hφ0 hφ1
        have h1 : (0 : ℝ) ≤ S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) := Real.rpow_nonneg hS _
        have h2 : (0 : ℝ) ≤ B ^ ((β : ℝ) / (m : ℝ)) := Real.rpow_nonneg hB0 _
        calc CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
                * B ^ ((β : ℝ) / (m : ℝ))
            = CG ^ ((β : ℝ) / (m : ℝ))
                * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) := by ring
          _ ≤ (max CG 1)
                * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg h1 h2)
      have hGb : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) ^ ((m : ℝ) / (β : ℝ))) ^ (1 / ((m : ℝ) / (β : ℝ)))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) := by
        have hstep1 : (∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ))) ^ ((β : ℝ) / (m : ℝ))
            ≤ (CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B) ^ ((β : ℝ) / (m : ℝ)) :=
          Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hGNg
            (by positivity)
        calc (∫ x in Work.Diff.STE.unitCube (ι := ι),
              (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) ^ ((m : ℝ) / (β : ℝ))) ^ (1 / ((m : ℝ) / (β : ℝ)))
            = (∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ))) ^ ((β : ℝ) / (m : ℝ)) := by
              rw [hGbase, hone']
          _ ≤ (CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B) ^ ((β : ℝ) / (m : ℝ)) := hstep1
          _ = CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
                * B ^ ((β : ℝ) / (m : ℝ)) := hstepG
          _ ≤ (max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) :=
              hstepG2
      -- ### assembly
      have hAMGM : A ^ ((α : ℝ) / (m : ℝ)) * B ^ ((β : ℝ) / (m : ℝ)) ≤ A + B := by
        have h := geom_mean_le_add hA0 hB0 hθ0 hθ1
        rw [← hφeq] at h
        exact h
      have hScomb : S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
          = S ^ 2 := by
        have h2 : (2 - 2 * ((α : ℝ) / (m : ℝ))) + (2 - 2 * ((β : ℝ) / (m : ℝ))) = 2 := by
          linarith [hsum]
        have hne : (2 - 2 * ((α : ℝ) / (m : ℝ))) + (2 - 2 * ((β : ℝ) / (m : ℝ))) ≠ 0 := by
          rw [h2]; norm_num
        calc S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
            = S ^ ((2 - 2 * ((α : ℝ) / (m : ℝ))) + (2 - 2 * ((β : ℝ) / (m : ℝ)))) :=
              (Real.rpow_add' hS hne).symm
          _ = S ^ (2 : ℝ) := by rw [h2]
          _ = S ^ 2 := Real.rpow_natCast _ 2
      have hBound : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
          ≤ ((max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))))
            * ((max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ)))) := by
        rw [hLHS]
        exact hHolder.trans (mul_le_mul hFb hGb (by positivity) (by positivity))
      refine hBound.trans ?_
      have hmax0 : (0 : ℝ) ≤ max CG 1 := le_trans hCG0 (le_max_left CG 1)
      calc ((max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))))
            * ((max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))))
          = ((max CG 1) * (max CG 1))
              * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))))
              * (A ^ ((α : ℝ) / (m : ℝ)) * B ^ ((β : ℝ) / (m : ℝ))) := by ring
        _ = ((max CG 1) * (max CG 1)) * S ^ 2
              * (A ^ ((α : ℝ) / (m : ℝ)) * B ^ ((β : ℝ) / (m : ℝ))) := by
            rw [hScomb]
        _ ≤ ((max CG 1) * (max CG 1)) * S ^ 2 * (A + B) := by
            have h1 : (0 : ℝ) ≤ ((max CG 1) * (max CG 1)) * S ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left hAMGM h1
        _ ≤ ((max CG 1 + 1) * (max CG 1 + 1)) * (S ^ 2 * (A + B)) := by
            have h1 : (max CG 1) * (max CG 1) ≤ (max CG 1 + 1) * (max CG 1 + 1) := by
              nlinarith [hmax0]
            have h2 : (0 : ℝ) ≤ S ^ 2 * (A + B) := by positivity
            calc ((max CG 1) * (max CG 1)) * S ^ 2 * (A + B)
                = ((max CG 1) * (max CG 1)) * (S ^ 2 * (A + B)) := by ring
              _ ≤ ((max CG 1 + 1) * (max CG 1 + 1)) * (S ^ 2 * (A + B)) :=
                  mul_le_mul_of_nonneg_right h1 h2

/-! ## The main theorem -/

end Work.Diff.STE.Lead.GalTame
