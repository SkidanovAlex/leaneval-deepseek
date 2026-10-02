/-
# ZeroFreeTables — t23simple

`Work.ZeroFreeTables.GlueSimple`: in the range `λ₁ ≤ 2/5` the exceptional real zero of a real
non-principal Dirichlet character is *simple*.

Route (Heath-Brown §6, repeated-zero case, with the **convexity** supply of Lemma 3.1 instead of
the Burgess one — `l52HypConvexityFixed`, constant `1/4 + 10⁻⁶`, whose import path avoids the
still-evolving Burgess area):

* if `2 ≤ zeroMult χ₁ β₁`, the window sum at `β₁` carries the doubled zero (`winSum_two_mul`),
  so HB Lemma 6.3 in the repeated-zero form (`hb6Repeated`) with the triangle test function
  `f(t) = max (1-t) 0` on `[0,1]` gives
  `0 ≤ 2∫₀¹ e^{λ₁t}f − 4∫₀¹ f + f(0)(2c + 3ε)`, i.e. (with `∫f = 1/2`, `f 0 = 1`,
  `c = 1/4 + 10⁻⁶`, `ε = 1/100`) `2∫₀¹ e^{λ₁t} max (1-t) 0 ≥ 2 − 2c − 3ε > 6/5`;
* but `λ₁ ≤ 2/5` gives `2∫₀¹ e^{λ₁t} max (1-t) 0 ≤ 6/5` (`t23triBound`, triangle Taylor bound);
* contradiction, so the multiplicity, being non-zero, is `1`.

The point conditions at `β₁` (`|1-β₁| ≤ δ` and HB's §6 range `|1-β₁| ≤ √(log log q)/log q`)
are supplied by `t23guard`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.hb6Repeated
import Submission.Work.ZeroFreeTables.winSum_two_mul
import Submission.Work.ZeroFreeTables.l52HypConvexityFixed
import Submission.Work.LinnikAreas.triangle_hFnn
import Submission.Work.ZeroFreeTables.t23triBound
import Submission.Work.ZeroFreeTables.t23guard
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
open MeasureTheory intervalIntegral
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The triangle test function on `[0,1]` -/

private lemma tri_cont : ContinuousOn (fun t : ℝ => max (1 - t) 0) (Set.Ici 0) :=
  ((continuous_const.sub continuous_id).max continuous_const).continuousOn

private lemma tri_supp : ∀ t : ℝ, 1 ≤ t → max (1 - t) 0 = 0 :=
  fun t ht => max_eq_right (by linarith)

private lemma tri_diff : ContDiffOn ℝ 2 (fun t : ℝ => max (1 - t) 0) (Set.Ioo 0 1) := by
  have h1 : ContDiffOn ℝ 2 (fun t : ℝ => 1 - t) (Set.Ioo (0:ℝ) 1) := by fun_prop
  refine h1.congr ?_
  intro t ht
  rw [Set.mem_Ioo] at ht
  exact max_eq_left (by linarith [ht.2])

private lemma tri_deriv_two : ∀ t ∈ Set.Ioo (0:ℝ) 1,
    iteratedDeriv 2 (fun t : ℝ => max (1 - t) 0) t = 0 := by
  intro t ht
  have hs : Set.Ioo (0:ℝ) 1 ∈ nhds t := IsOpen.mem_nhds isOpen_Ioo ht
  have hev : (fun s : ℝ => max (1 - s) 0) =ᶠ[nhds t] (fun s : ℝ => 1 - s) := by
    filter_upwards [hs] with s hs'
    rw [Set.mem_Ioo] at hs'
    exact max_eq_left (by linarith [hs'.2])
  have hlin : iteratedDeriv 2 (fun s : ℝ => 1 - s) t = 0 := by
    rw [show (fun s : ℝ => 1 - s) = (fun s : ℝ => 1 + (-(id s))) from rfl,
      iteratedDeriv_const_add (f := fun s : ℝ => -(id s)) (c := 1) (show (0:ℕ) < 2 by norm_num)]
    rw [iteratedDeriv_fun_neg, iteratedDeriv_id]
    norm_num
  rw [hev.iteratedDeriv_eq]
  exact hlin

private lemma tri_bnd : ∀ t ∈ Set.Ioo (0:ℝ) 1,
    ‖iteratedDeriv 2 (fun t : ℝ => max (1 - t) 0) t‖ ≤ 0 :=
  fun t ht => by rw [tri_deriv_two t ht, norm_zero]

private lemma tri_nonneg : ∀ t : ℝ, 0 ≤ max (1 - t) 0 := fun t => le_max_right _ _

private lemma tri_at_zero : (0:ℝ) < max (1 - (0:ℝ)) 0 := by norm_num

private lemma tri_int : (∫ t in (0:ℝ)..1, max (1 - t) 0) = 1 / 2 := by
  have hcongr : (∫ t in (0:ℝ)..1, max (1 - t) 0) = ∫ t in (0:ℝ)..1, (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact max_eq_left (by linarith [ht.2])
  rw [hcongr]
  have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 1)
    (f := fun _ : ℝ => (1:ℝ)) (g := fun s : ℝ => s)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul] at hsub
  rw [hsub]; norm_num

/-- **`GlueSimple`.**  The exceptional real zero of a real non-principal character is simple in
the range `λ₁ ≤ 2/5`; see the file header for the route. -/
theorem t23simple : Work.ZeroFreeTables.GlueSimple := by
  obtain ⟨δ, hδ0, hδ1, q₀L, hL52⟩ := l52HypConvexityFixed
  obtain ⟨q₀G, hG⟩ := t23guard δ hδ0
  have hFnn : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..1,
        Complex.exp (-(z * (t : ℂ))) * (((max (1 - t) 0 : ℝ)) : ℂ)).re :=
    fun z hz => Work.LinnikAreas.triangle_hFnn (by norm_num : (0:ℝ) < 1) z hz
  obtain ⟨q₀R, hR⟩ := hb6Repeated (x₀ := 1) (B := 0) (c := 1/4 + 1/1000000)
    (ε := 1/100) (δ := δ) (by norm_num) (le_refl 0) (by norm_num) hδ0 hδ1
    tri_cont tri_supp tri_diff tri_bnd tri_at_zero tri_nonneg hFnn
  refine ⟨max (max (max q₀R q₀L) q₀G) 4, ?_⟩
  intro q hq hqne χ₁ β₁ hχ1 hsq hβ1lt hzm hmin hlam
  have hqR : q₀R ≤ q := by omega
  have hqL : q₀L ≤ q := by omega
  have hqG : q₀G ≤ q := by omega
  by_contra hne
  have hge : 2 ≤ zeroMult χ₁ (β₁ : ℂ) := by
    have h1 : 1 ≤ zeroMult χ₁ (β₁ : ℂ) := Nat.one_le_iff_ne_zero.mpr hzm
    omega
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hlam_eq : lamOf q (β₁ : ℂ) = (1 - β₁) * Real.log (q : ℝ) := by simp [lamOf]
  -- the two point conditions at `β₁`
  obtain ⟨hδbd, hptbd⟩ := hG q hqG β₁ hβ1lt (by rw [← hlam_eq]; exact hlam)
  -- the real form of the minimality at `β₁`
  have hminre : ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u.re ≤ β₁ := by
    intro u hu himu
    have hle : lamOf q (β₁ : ℂ) ≤ lamOf q u := hmin u hu (le_trans himu (by norm_num))
    rw [lamOf, lamOf] at hle
    have h2 := (mul_le_mul_iff_of_pos_right hlogq).mp hle
    simp only [Complex.ofReal_re] at h2
    linarith
  -- the window sum carries the doubled zero
  have hwin := winSum_two_mul (q := q) χ₁ hχ1 (f := fun t : ℝ => max (1 - t) 0) (x₀ := 1)
    (L := Real.log (q : ℝ)) (δ := δ) (β₁ := β₁) (le_of_lt hlogq) hδ1 hFnn hδbd hge hminre
  -- HB Lemma 3.1 (convexity form) at this modulus
  have H : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/4 + 1/1000000) (1/100) δ :=
    hL52 q hqL χ₁ hχ1 (1/100) (by norm_num) (by norm_num)
  have hreal : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq
  -- HB Lemma 6.3, repeated-zero form
  have hcore := hR (q := q) hqR χ₁ hχ1 hreal (β₁ := β₁) hδbd hptbd H hwin
  -- the numeric contradiction: `λ₁ ≤ 2/5` caps the integral at `3/5`
  have hlam_le : Real.log (q : ℝ) * (1 - β₁) ≤ 2 / 5 := by
    rw [mul_comm, ← hlam_eq]; exact hlam
  have hnum : 2 * (∫ t in (0:ℝ)..1,
      Real.exp ((Real.log (q : ℝ) * (1 - β₁)) * t) * max (1 - t) 0) ≤ 6 / 5 :=
    t23triBound (Real.log (q : ℝ) * (1 - β₁)) hlam_le
  rw [tri_int, show max (1 - (0:ℝ)) 0 = 1 by norm_num] at hcore
  linarith [hcore, hnum]

end Work.ZeroFreeTables
