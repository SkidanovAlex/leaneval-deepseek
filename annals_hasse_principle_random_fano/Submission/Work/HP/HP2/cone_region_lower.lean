import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.tau_basic
import Submission.Work.HP.HP2.cone_lip
import Submission.Work.HP.HP2.cone_vero_sphere
import Submission.Work.HP.HP2.cone_cap_volume

/-!
# Lower bound for the volume of the cone region `{x : ‖x‖ ≤ R, a ∈ 𝒞_{ν(x)}^{(α)}}`

`Work.HP.HP2.cone_region_lower` is the Archimedean input of the random Fano hypersurface paper:
if the form `f_a` has a nonzero real zero, then the cone region contains the cone over a spherical
cap of angular radius `≍ 1/α` around the direction `u₀` of that zero, hence has volume
`≫ R^(n+1)/α^n`.

The three ingredients are
* `Work.HP.HP2.cone_lip` : `f_a` is `C(d,n) ‖a‖`-Lipschitz on the unit ball,
* `Work.HP.HP2.cone_vero_sphere` : `‖ν(u)‖ ≥ c₁(d,n) > 0` on the unit sphere,
* `Work.HP.HP2.cone_cap_volume` : the cone over a spherical cap of chord radius `δ ≤ 1` has volume
  `≫ δ^n`,
and the reduction of the radius-`R` region to the unit region is `Work.HP.cone_volume`, which
expresses the volume as `R^(n+1) τ(a;α)/α`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Work.HP.HP2

/-- `rNorm` vanishes exactly at the origin. -/
lemma rNorm_pos_of_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ≠ 0) : 0 < rNorm v :=
  lt_of_le_of_ne (rNorm_nonneg v) (fun h => hv (rNorm_eq_zero.mp h.symm))

/-- `formEval` with integer coefficients is `formEvalR` with the realified coefficient vector. -/
lemma formEval_eq_formEvalR (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℝ) :
    formEval d n a x = formEvalR d n (toR a) x := rfl

/-- `ν_{d,n}(0) = 0` for `d ≥ 1` (every degree-`d` monomial with `d ≥ 1` vanishes at the origin). -/
lemma veronese_zero (d n : ℕ) (hd : 1 ≤ d) :
    veronese d n (0 : Fin (n + 1) → ℝ) = 0 := by
  funext m
  obtain ⟨i, hi⟩ : ∃ i, (m.1 i : ℕ) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : ∑ i, (m.1 i : ℕ) = 0 := Finset.sum_eq_zero (fun i _ => h i)
    omega
  have h0 : (∏ i : Fin (n + 1), (0 : ℝ) ^ ((m.1 i : ℕ))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi)
  simpa [veronese] using h0

/-- If the form `f_a` has a nonzero integer zero, the cone region contains a cap of angular radius
`c / α` around the direction of that zero, and hence has volume `≥ c' R^(n+1) / α^n`.

Route.  `RealSol d n a` gives `x₀ ≠ 0` with `formEval d n a x₀ = 0`; set `u₀ = x₀ / ‖x₀‖`, so
`formEvalR d n (toR a) u₀ = 0` (homogeneity).  The form is Lipschitz on the unit ball
(`|Q(u) − Q(v)| ≤ C(d,n) * ‖a‖ * ‖u − v‖`, from `Work.HP.HP2.cone_lip` with `R = 1`) and
`rNorm (veronese d n u) ≥ c₁ > 0` for `rNorm u = 1` (`Work.HP.HP2.cone_vero_sphere`).  Hence for
`rNorm (u − u₀) ≤ δ := min (c₁/(2Cα)) 1`
`|Q(u)| ≤ C‖a‖·δ ≤ ‖a‖ rNorm (ν u) / (2α)`, i.e. `a ∈ C_{ν(u)}^{(α)}`.  By homogeneity the whole
cone over that cap lies in the region, and the cap of chord radius `δ` has volume `≫ δ^n` inside
the unit ball (`Work.HP.HP2.cone_cap_volume`).  Scaling by `R` multiplies by `R^(n+1)`
(`Work.HP.cone_volume`). -/
theorem cone_region_lower (d n : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Mon d n → ℤ) (α R : ℝ), RealSol d n a → 1 ≤ α → 1 ≤ R →
      c * R ^ (n + 1) / α ^ n ≤
        (MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ R ∧
          (toR a) ∈ Cgam (veronese d n x) α}).toReal := by
  obtain ⟨C, hCpos, hclip⟩ := cone_lip d n
  obtain ⟨c₁, hc₁pos, hc₁⟩ := cone_vero_sphere d n
  obtain ⟨κ, hκpos, hκ⟩ := cone_cap_volume n
  refine ⟨κ * (min (c₁ / (2 * C)) 1) ^ n, by positivity, ?_⟩
  intro a α R hsol hα hR
  -- the direction `u₀` of a real zero of `f_a`
  obtain ⟨x₀, hx₀ne, hx₀zero⟩ := hsol
  have hx₀pos : 0 < rNorm x₀ := rNorm_pos_of_ne_zero hx₀ne
  set t₀ : ℝ := (rNorm x₀)⁻¹ with ht₀def
  have ht₀pos : 0 < t₀ := inv_pos.mpr hx₀pos
  set u₀ : Fin (n + 1) → ℝ := fun i => t₀ * x₀ i with hu₀def
  have hu₀norm : rNorm u₀ = 1 := by
    rw [hu₀def, rNorm_const_mul, abs_of_pos ht₀pos]
    rw [ht₀def, inv_mul_cancel₀ (ne_of_gt hx₀pos)]
  have hQ₀ : formEvalR d n (toR a) u₀ = 0 := by
    rw [hu₀def, formEvalR_const_mul, ← formEval_eq_formEvalR, hx₀zero]
    ring
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- the angular radius `δ'` of the cap, clamped to `1`
  set Kc : ℝ := c₁ / (2 * C) with hKcdef
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  set δ : ℝ := Kc / α with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set δ' : ℝ := min δ 1 with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos one_pos
  have hδ'le1 : δ' ≤ 1 := min_le_right _ _
  set T : Set (Fin (n + 1) → ℝ) :=
    {u | rNorm u ≤ 1 ∧ (toR a) ∈ Cgam (veronese d n u) α} with hTdef
  set S : Set (Fin (n + 1) → ℝ) :=
    {x | rNorm x ≤ 1 ∧ rNorm (x - rNorm x • u₀) ≤ δ' * rNorm x} with hSdef
  have h4 : C * eNorm a * δ = eNorm a * c₁ / (2 * α) := by
    rw [hδdef, hKcdef]; field_simp; try ring
  -- the cap-cone lies in the cone region
  have hsub : S ⊆ T := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨hx1, ?_⟩
    rcases eq_or_ne x 0 with hx0 | hx0
    · rw [hx0, veronese_zero d n hd]
      simp [Cgam, dotR, rNorm]
    · have hxrpos : 0 < rNorm x := rNorm_pos_of_ne_zero hx0
      set t : ℝ := rNorm x with htdef
      have htpos : 0 < t := hxrpos
      set y : Fin (n + 1) → ℝ := fun i => t⁻¹ * x i with hydef
      have hynorm : rNorm y = 1 := by
        rw [hydef, rNorm_const_mul, abs_of_pos (inv_pos.mpr htpos),
          inv_mul_cancel₀ (ne_of_gt htpos)]
      have hxy : x = fun i => t * y i := by
        funext i
        rw [hydef]
        simp only [htdef]
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hxrpos), one_mul]
      have hcapy : rNorm (y - u₀) ≤ δ' := by
        have hnorm' : rNorm (fun i => t * y i) = t := by
          rw [rNorm_const_mul, abs_of_pos htpos, hynorm, mul_one]
        have hscale : rNorm (x - rNorm x • u₀) = t * rNorm (y - u₀) := by
          rw [hxy]
          have hfun : (fun i => t * y i) - rNorm (fun i => t * y i) • u₀
              = fun i => t * (y i - u₀ i) := by
            funext i
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hnorm']
            ring
          rw [hfun, rNorm_const_mul, abs_of_pos htpos]
          rfl
        have h2 : t * rNorm (y - u₀) ≤ t * δ' := by
          rw [← hscale, ← htdef]
          rw [mul_comm δ' t] at hx2
          exact hx2
        exact le_of_mul_le_mul_left h2 htpos
      have hQy : |formEvalR d n (toR a) y| ≤ eNorm a * c₁ / (2 * α) := by
        have h1 : |formEvalR d n (toR a) y - formEvalR d n (toR a) u₀|
            ≤ C * eNorm a * rNorm (y - u₀) :=
          hclip a y u₀ (le_of_eq hynorm) (le_of_eq hu₀norm)
        rw [hQ₀, sub_zero] at h1
        have hAnn : 0 ≤ eNorm a := Real.sqrt_nonneg _
        have hCnn : 0 ≤ C * eNorm a := mul_nonneg hCpos.le hAnn
        have h2 : C * eNorm a * rNorm (y - u₀) ≤ C * eNorm a * δ' :=
          mul_le_mul_of_nonneg_left hcapy hCnn
        have h3 : C * eNorm a * δ' ≤ C * eNorm a * δ :=
          mul_le_mul_of_nonneg_left (min_le_left δ 1) hCnn
        linarith
      have hycone : (toR a) ∈ Cgam (veronese d n y) α := by
        simp only [Cgam, Set.mem_ofPred_eq]
        rw [dotR_veronese, rNorm_toR]
        have hle := hc₁ y hynorm
        have hAnn : 0 ≤ eNorm a := Real.sqrt_nonneg _
        calc |formEvalR d n (toR a) y| ≤ eNorm a * c₁ / (2 * α) := hQy
          _ ≤ eNorm a * rNorm (veronese d n y) / (2 * α) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hAnn) (by linarith)
          _ = rNorm (veronese d n y) * eNorm a / (2 * α) := by ring
      rw [hxy]
      exact (Cgam_veronese_const_mul a htpos y).mpr hycone
  -- the volume of the cap-cone
  have hvol : ENNReal.ofReal (κ * δ' ^ n) ≤ volume S := hκ u₀ hu₀norm δ' hδ'pos hδ'le1
  have hmono : volume S ≤ volume T := measure_mono hsub
  have hfin : volume T ≠ ⊤ := cone_region_volume_ne_top a α
  have hle_real : κ * δ' ^ n ≤ (volume T).toReal := by
    have h1 : (ENNReal.ofReal (κ * δ' ^ n)).toReal ≤ (volume T).toReal :=
      ENNReal.toReal_mono hfin (le_trans hvol hmono)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  -- `δ'` dominates `min Kc 1 / α`
  have hK'le : (min Kc 1) / α ≤ δ' := by
    rw [hδ'def, hδdef]
    apply le_min
    · exact div_le_div_of_nonneg_right (min_le_left Kc 1) hαpos.le
    · calc (min Kc 1) / α ≤ 1 / α := div_le_div_of_nonneg_right (min_le_right Kc 1) hαpos.le
        _ ≤ 1 := by rw [div_le_one hαpos]; linarith
  have hpow : (min Kc 1 / α) ^ n ≤ δ' ^ n :=
    pow_le_pow_left₀ (div_nonneg (le_of_lt (lt_min hKcpos one_pos)) hαpos.le) hK'le n
  have hδ'pow : (min Kc 1) ^ n / α ^ n ≤ δ' ^ n := by
    rw [div_pow] at hpow
    exact hpow
  have hcle : κ * (min Kc 1) ^ n / α ^ n ≤ (volume T).toReal := by
    have h1 : κ * (min Kc 1) ^ n / α ^ n ≤ κ * δ' ^ n := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hδ'pow hκpos.le
    linarith [hle_real]
  -- scaling in `R`
  have hconv : (volume {x : Fin (n + 1) → ℝ | rNorm x ≤ R ∧
        (toR a) ∈ Cgam (veronese d n x) α}).toReal = R ^ (n + 1) * (volume T).toReal := by
    rw [cone_volume d n a hαpos hRpos]
    rw [show tauArch d n (toR a) α = α * (volume T).toReal from rfl]
    field_simp
  calc κ * (min (c₁ / (2 * C)) 1) ^ n * R ^ (n + 1) / α ^ n
      = R ^ (n + 1) * (κ * (min Kc 1) ^ n / α ^ n) := by rw [hKcdef]; ring
    _ ≤ R ^ (n + 1) * (volume T).toReal :=
        mul_le_mul_of_nonneg_left hcle (pow_nonneg (by linarith) _)
    _ = (volume {x : Fin (n + 1) → ℝ | rNorm x ≤ R ∧
        (toR a) ∈ Cgam (veronese d n x) α}).toReal := hconv.symm

end Work.HP.HP2
