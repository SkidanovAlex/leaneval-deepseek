import Mathlib
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FIRed6Axis.NearMassDefs
import Submission.Work.FIRed6Axis.tau_divisors_cube_le
import Submission.Work.FIRed6Axis.tau_sum_le_divisor_count
import Submission.Work.FIRed6Axis.nearArg_axis_transverse
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.card_zmod_sq_add_sq_zero_le
import Submission.Work.FIArea6.card_fiber_mod_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIRed6Axis

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# The (5.16) mass bound for the near-axis zone

Assembled from

* `Work.FIRed6Axis.tau_divisors_cube_le` — the pointwise `τ`-localization
  `τ(n) ≤ 4 ∑_{d ∣ n, d³ ≤ n} τ(d)³` for squarefree `n`;
* `Work.FIRed6Axis.tau_sum_le_divisor_count` — its summation over the annulus;
* `Work.FIRed6Axis.nearArg_axis_transverse` — the near zone is axis-aligned;
* the `d`-refined box count `nm_card_box_dvd_gnorm_le` below;
* the final numerics `nm_near_mass_sum_arith` below
  (with the `τ⁴`-sum bound `Work.FIArea2.sum_tau_pow_div_le 4`).
-/

/-! ## 0. The `d`-refined box count -/

private lemma nm_gnorm_zcast (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  rw [Work.FIPlan.gnorm, hnorm,
    Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ z.re ^ 2 + z.im ^ 2)]


private lemma nm_card_box_dvd_gnorm_le (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (d : ℕ) (hd : 1 ≤ d) (hdsq : Squarefree d) (S : Finset GaussianInt)
    (hre : ∀ z ∈ S, |((z.re : ℤ) : ℝ)| ≤ u)
    (him : ∀ z ∈ S, |((z.im : ℤ) : ℝ)| ≤ v)
    (hdvd : ∀ z ∈ S, d ∣ Work.FIPlan.gnorm z) :
    (S.card : ℝ) ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
      * (2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1) := by
  haveI : NeZero d := ⟨by omega⟩
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  set res : GaussianInt → ZMod d × ZMod d :=
    fun z => ((z.re : ZMod d), (z.im : ZMod d)) with hres
  set R : Finset (ZMod d × ZMod d) := S.image res with hRdef
  -- (1) each residue class meets `S` in at most `(2u/d+1)(2v/d+1)` points
  have hfib : ∀ r ∈ R, ((S.filter (fun z => res z = r)).card : ℝ)
      ≤ (2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1) := by
    intro r hr
    obtain ⟨z₀, hz₀S, rfl⟩ := Finset.mem_image.mp hr
    set T : Finset GaussianInt := S.filter (fun z => res z = res z₀) with hTdef
    have hTsub : ∀ z ∈ T, z ∈ S ∧ res z = res z₀ := by
      intro z hz; rw [hTdef, Finset.mem_filter] at hz; exact hz
    have hcard1 : T.card ≤ (T.image (fun z => z.re)).card * (T.image (fun z => z.im)).card := by
      have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
        intro p q hpq
        exact Zsqrtd.ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
      calc T.card = (T.image (fun z : GaussianInt => (z.re, z.im))).card :=
            (Finset.card_image_of_injective T hinj).symm
        _ ≤ ((T.image (fun z => z.re)) ×ˢ (T.image (fun z => z.im))).card := by
            apply Finset.card_le_card
            intro p hp
            obtain ⟨z, hz, hpz⟩ := Finset.mem_image.mp hp
            rw [← hpz, Finset.mem_product]
            exact ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
        _ = (T.image (fun z => z.re)).card * (T.image (fun z => z.im)).card :=
            Finset.card_product _ _
    have hrecard : ((T.image (fun z => z.re)).card : ℝ) ≤ 2 * u / (d : ℝ) + 1 := by
      apply Work.FIArea6.card_le_of_modEq_interval (t := -u) (ρ := u) _ hdpos z₀.re hu
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have h1 : (z.re : ZMod d) = (z₀.re : ZMod d) := congrArg Prod.fst (hTsub z hz).2
        exact (ZMod.intCast_eq_intCast_iff z.re z₀.re d).mp h1
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have h2 := hre z (hTsub z hz).1
        rw [abs_le] at h2
        constructor <;> linarith [h2.1, h2.2]
    have himcard : ((T.image (fun z => z.im)).card : ℝ) ≤ 2 * v / (d : ℝ) + 1 := by
      apply Work.FIArea6.card_le_of_modEq_interval (t := -v) (ρ := v) _ hdpos z₀.im hv
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have h1 : (z.im : ZMod d) = (z₀.im : ZMod d) := congrArg Prod.snd (hTsub z hz).2
        exact (ZMod.intCast_eq_intCast_iff z.im z₀.im d).mp h1
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have h2 := him z (hTsub z hz).1
        rw [abs_le] at h2
        constructor <;> linarith [h2.1, h2.2]
    have hcu : (0 : ℝ) ≤ 2 * u / (d : ℝ) + 1 := by
      have : (0 : ℝ) ≤ 2 * u / (d : ℝ) := div_nonneg (by linarith) hdR.le
      linarith
    have hcv : (0 : ℝ) ≤ 2 * v / (d : ℝ) + 1 := by
      have : (0 : ℝ) ≤ 2 * v / (d : ℝ) := div_nonneg (by linarith) hdR.le
      linarith
    calc (T.card : ℝ)
        ≤ ((T.image (fun z => z.re)).card : ℝ) * ((T.image (fun z => z.im)).card : ℝ) := by
          exact_mod_cast hcard1
      _ ≤ (2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1) :=
          mul_le_mul hrecard himcard (by positivity) hcu
  -- (2) split `S` into its residue classes
  have hdecomp : (S.card : ℝ)
      = ∑ r ∈ R, ((S.filter (fun z => res z = r)).card : ℝ) := by
    have hmap : Set.MapsTo res ↑S ↑R := fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmap, Nat.cast_sum]
  have hbound1 : (S.card : ℝ)
      ≤ (R.card : ℝ) * ((2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1)) := by
    rw [hdecomp]
    calc ∑ r ∈ R, ((S.filter (fun z => res z = r)).card : ℝ)
        ≤ ∑ _r ∈ R, ((2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1)) :=
          Finset.sum_le_sum hfib
      _ = (R.card : ℝ) * ((2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) the residue classes of `S` lie in the solution set of `r² + s² = 0 (mod d)`
  have hRsub : R ⊆ Finset.univ.filter
      (fun r : ZMod d × ZMod d => r.1 ^ 2 + r.2 ^ 2 = 0) := by
    intro r hr
    obtain ⟨z, hzs, rfl⟩ := Finset.mem_image.mp hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hgn := nm_gnorm_zcast z
    have hdvd : (d : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by
      rw [← hgn]
      exact Int.natCast_dvd_natCast.mpr (hdvd z hzs)
    have hz0 : ((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod d) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re ^ 2 + z.im ^ 2) d).mpr hdvd
    rw [show (z.re : ZMod d) ^ 2 + (z.im : ZMod d) ^ 2
        = ((z.re ^ 2 + z.im ^ 2 : ℤ) : ZMod d) by push_cast; ring]
    exact hz0
  have hRcard : R.card ≤ ∏ p ∈ d.primeFactors, (2 * p - 1) :=
    le_trans (Finset.card_le_card hRsub)
      (Work.FIArea6.card_zmod_sq_add_sq_zero_le d hdsq)
  have hRcast : (R.card : ℝ) ≤ ∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ) := by
    calc (R.card : ℝ) ≤ ((∏ p ∈ d.primeFactors, (2 * p - 1) : ℕ) : ℝ) := by
          exact_mod_cast hRcard
      _ = ∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ) := by push_cast; ring
  have hprod0 : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ) := by
    apply Finset.prod_nonneg; intro p hp; positivity
  calc (S.card : ℝ) ≤ (R.card : ℝ) * ((2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1)) := hbound1
    _ ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          * ((2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hRcast (by positivity)
    _ = (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          * (2 * u / (d : ℝ) + 1) * (2 * v / (d : ℝ) + 1) := by ring



/-! ## 1. Geometry -/

private lemma nm_abs_re_le_sqrt_gnorm (z : GaussianInt) :
    |((z.re : ℤ) : ℝ)| ≤ Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
  rw [← Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
  calc |((z.re : ℤ) : ℝ)| = |z.toComplex.re| := by rw [Work.FIArea4.ofReal_re_eq_re]
    _ ≤ ‖z.toComplex‖ := Complex.abs_re_le_norm _

private lemma nm_abs_im_le_sqrt_gnorm (z : GaussianInt) :
    |((z.im : ℤ) : ℝ)| ≤ Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
  rw [← Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
  calc |((z.im : ℤ) : ℝ)| = |z.toComplex.im| := by rw [Work.FIArea4.ofReal_im_eq_im]
    _ ≤ ‖z.toComplex‖ := Complex.abs_im_le_norm _

private lemma nm_abs_re_le_nearBoxR {N : ℝ} {z : GaussianInt}
    (hz : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N) :
    |((z.re : ℤ) : ℝ)| ≤ nearBoxR N := by
  rw [nearBoxR]
  exact le_trans (nm_abs_re_le_sqrt_gnorm z) (Real.sqrt_le_sqrt hz)

private lemma nm_abs_im_le_nearBoxR {N : ℝ} {z : GaussianInt}
    (hz : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N) :
    |((z.im : ℤ) : ℝ)| ≤ nearBoxR N := by
  rw [nearBoxR]
  exact le_trans (nm_abs_im_le_sqrt_gnorm z) (Real.sqrt_le_sqrt hz)

private lemma nm_norm_toComplex_le_sqrt_two_mul {N : ℝ} {z : GaussianInt}
    (hz : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N) :
    ‖z.toComplex‖ ≤ Real.sqrt (2 * N) := by
  rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
  exact Real.sqrt_le_sqrt hz

/-- `4ϑ‖z‖ ≤ 6ϑ√N` for `|z|² ≤ 2N`, i.e. `4ϑ|z| ≤ nearBoxT ϑ N`. -/
private lemma nm_four_mul_norm_le_nearBoxT (N ϑ : ℝ) (hϑ : 0 ≤ ϑ) {z : GaussianInt}
    (hz : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N) :
    4 * ϑ * ‖z.toComplex‖ ≤ nearBoxT ϑ N := by
  have hsq : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N := Real.sqrt_mul (by norm_num) N
  have h4 : (4 : ℝ) * Real.sqrt 2 ≤ 6 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h2 : ‖z.toComplex‖ ≤ Real.sqrt 2 * Real.sqrt N := by
    rw [← hsq]; exact nm_norm_toComplex_le_sqrt_two_mul hz
  have h3 : 4 * ϑ * ‖z.toComplex‖ ≤ 4 * ϑ * (Real.sqrt 2 * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hs : (0 : ℝ) ≤ ϑ * Real.sqrt N := mul_nonneg hϑ (Real.sqrt_nonneg N)
  have h5 : 4 * ϑ * (Real.sqrt 2 * Real.sqrt N) ≤ 6 * ϑ * Real.sqrt N := by
    nlinarith [hs, h4]
  rw [nearBoxT]
  linarith

/-- **The near zone lies in one of the two axis-parallel boxes.** -/
private lemma nm_nearArg_transverse_le (N ϑ : ℝ) (hϑ : 0 ≤ ϑ) {z : GaussianInt}
    (hz : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N) (h : nearArg (4 * ϑ) z) :
    |((z.im : ℤ) : ℝ)| ≤ nearBoxT ϑ N ∨ |((z.re : ℤ) : ℝ)| ≤ nearBoxT ϑ N := by
  rcases nearArg_axis_transverse (c := 4 * ϑ) (by linarith) h with h1 | h1
  · exact Or.inl (le_trans h1 (nm_four_mul_norm_le_nearBoxT N ϑ hϑ hz))
  · exact Or.inr (le_trans h1 (nm_four_mul_norm_le_nearBoxT N ϑ hϑ hz))

/-! ## 2. The per-`d` count -/

private lemma nm_card_filter_dvd_le_split (N ϑ : ℝ) (hϑ : 0 ≤ ϑ) (T : Finset GaussianInt)
    (hT : ∀ z ∈ T, ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N ∧ nearArg (4 * ϑ) z) (d : ℕ) :
    ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z ∧
            |((z.im : ℤ) : ℝ)| ≤ nearBoxT ϑ N)).card : ℝ)
        + ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z ∧
            |((z.re : ℤ) : ℝ)| ≤ nearBoxT ϑ N)).card : ℝ) := by
  set P : GaussianInt → Prop := fun z => d ∣ Work.FIPlan.gnorm z with hPdef
  set Q : GaussianInt → Prop := fun z => d ∣ Work.FIPlan.gnorm z ∧
      |((z.im : ℤ) : ℝ)| ≤ nearBoxT ϑ N with hQdef
  set R : GaussianInt → Prop := fun z => d ∣ Work.FIPlan.gnorm z ∧
      |((z.re : ℤ) : ℝ)| ≤ nearBoxT ϑ N with hRdef
  have hsub : T.filter P ⊆ T.filter Q ∪ T.filter R := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_union] at hz ⊢
    rcases nm_nearArg_transverse_le N ϑ hϑ (hT z hz.1).1 (hT z hz.1).2 with h | h
    · exact Or.inl ⟨hz.1, hz.2, h⟩
    · exact Or.inr ⟨hz.1, hz.2, h⟩
  have h1 : ((T.filter P).card : ℝ) ≤ ((T.filter Q ∪ T.filter R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 : (((T.filter Q ∪ T.filter R).card : ℕ) : ℝ)
      ≤ ((T.filter Q).card : ℝ) + ((T.filter R).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (T.filter Q) (T.filter R)
  linarith

/-! ## 3. The squarefree weight comparison `τ(d)³·ρ(d) ≤ τ(d)⁴·d` -/

private lemma nm_two_pow_omega_le_tau (d : ℕ) (hd : d ≠ 0) :
    (2 : ℝ) ^ d.primeFactors.card ≤ ((d.divisors.card : ℕ) : ℝ) := by
  have hfac : ∀ p ∈ d.primeFactors, 1 ≤ d.factorization p := by
    intro p hp
    have hp' : p ∈ d.factorization.support := by rwa [Nat.support_factorization]
    have := Finsupp.mem_support_iff.mp hp'
    omega
  calc (2 : ℝ) ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, (2 : ℝ) :=
        (Finset.prod_const (2 : ℝ)).symm
    _ ≤ ∏ p ∈ d.primeFactors, ((d.factorization p + 1 : ℕ) : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp; norm_num
        · intro p hp
          have h1 : (1 : ℝ) ≤ (d.factorization p : ℝ) := by
            exact_mod_cast hfac p hp
          push_cast
          linarith
    _ = ((d.divisors.card : ℕ) : ℝ) := by
        rw [Nat.card_divisors hd]; push_cast; ring

private lemma nm_tau_cube_mul_prod_le (d : ℕ) (hd : 1 ≤ d) (hdsq : Squarefree d) :
    (((d.divisors.card : ℕ) : ℝ)) ^ 3
        * (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
      ≤ (((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ) := by
  have hd0 : d ≠ 0 := by omega
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have htau0 : (0 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrho1 : (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ d.primeFactors.card * (d : ℝ) := by
    calc (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
        ≤ ∏ p ∈ d.primeFactors, ((2 * p : ℕ) : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro p hp; positivity
          · intro p hp
            have hle : (2 * p - 1 : ℕ) ≤ 2 * p := by omega
            exact_mod_cast hle
      _ = ∏ p ∈ d.primeFactors, (2 * (p : ℝ)) := by
          apply Finset.prod_congr rfl; intro p hp; push_cast; ring
      _ = (2 : ℝ) ^ d.primeFactors.card * ∏ p ∈ d.primeFactors, (p : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ = (2 : ℝ) ^ d.primeFactors.card * (d : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hdsq]
  have hrho : (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
      ≤ ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) := by
    calc (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
        ≤ (2 : ℝ) ^ d.primeFactors.card * (d : ℝ) := hrho1
      _ ≤ (((d.divisors.card : ℕ) : ℝ)) * (d : ℝ) :=
          mul_le_mul_of_nonneg_right (nm_two_pow_omega_le_tau d hd0) hdR
  calc (((d.divisors.card : ℕ) : ℝ)) ^ 3
        * (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
      ≤ (((d.divisors.card : ℕ) : ℝ)) ^ 3
          * ((((d.divisors.card : ℕ) : ℝ)) * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hrho (by positivity)
    _ = (((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ) := by ring

/-! ## 4. The reduction -/

private lemma nm_near_mass_reduction (N ϑ : ℝ) (hN : 1 ≤ N) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (T : Finset GaussianInt)
    (hT : ∀ z ∈ T, N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
        ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * N ∧
        Squarefree (Work.FIPlan.gnorm z) ∧ nearArg (4 * ϑ) z) :
    (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 8 * ∑ d ∈ Finset.Icc 1 (nearMassX N),
          (((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ)
            * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := by
  have hu0 : 0 ≤ nearBoxR N := nearBoxR_nonneg N
  have hv0 : 0 ≤ nearBoxT ϑ N := nearBoxT_nonneg ϑ N hϑ0.le
  have hX : ∀ d : ℕ, d ^ 3 ≤ 2 * N → d ≤ nearMassX N := by
    intro d hd
    exact le_nearMassX (by linarith) hd
  -- step 1
  have hstep1 :
      (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ 4 * ∑ d ∈ Finset.Icc 1 (nearMassX N),
            (((d.divisors.card : ℕ) : ℝ)) ^ 3
              * (((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := by
    refine tau_sum_le_divisor_count N (nearMassX N) T tau_divisors_cube_le hX ?_ ?_
    · intro z hz
      refine ⟨?_, (hT z hz).2.1⟩
      have h1 : (1 : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by linarith [(hT z hz).1, hN]
      exact_mod_cast h1
    · intro z hz
      exact (hT z hz).2.2.1
  -- step 2
  have hper : ∀ d ∈ Finset.Icc 1 (nearMassX N),
      (((d.divisors.card : ℕ) : ℝ)) ^ 3
          * (((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
        ≤ 2 * ((((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ)
            * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)) := by
    intro d hdmem
    rw [Finset.mem_Icc] at hdmem
    obtain ⟨hd1, hdX⟩ := hdmem
    by_cases hsq : Squarefree d
    · have hcnt1 : ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z ∧
            |((z.im : ℤ) : ℝ)| ≤ nearBoxT ϑ N)).card : ℝ)
          ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := by
        apply nm_card_box_dvd_gnorm_le (nearBoxR N) (nearBoxT ϑ N) hu0 hv0 d hd1 hsq
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact nm_abs_re_le_nearBoxR (hT z hz.1).2.1
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact hz.2.2
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact hz.2.1
      have hcnt2' : ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z ∧
            |((z.re : ℤ) : ℝ)| ≤ nearBoxT ϑ N)).card : ℝ)
          ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxT ϑ N / (d : ℝ) + 1) * (2 * nearBoxR N / (d : ℝ) + 1) := by
        apply nm_card_box_dvd_gnorm_le (nearBoxT ϑ N) (nearBoxR N) hv0 hu0 d hd1 hsq
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact hz.2.2
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact nm_abs_im_le_nearBoxR (hT z hz.1).2.1
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact hz.2.1
      have hcnt2 : ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z ∧
            |((z.re : ℤ) : ℝ)| ≤ nearBoxT ϑ N)).card : ℝ)
          ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := by
        have heq : (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxT ϑ N / (d : ℝ) + 1) * (2 * nearBoxR N / (d : ℝ) + 1)
            = (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := by
          ring
        rw [heq] at hcnt2'
        exact hcnt2'
      have hsplit := nm_card_filter_dvd_le_split N ϑ hϑ0.le T
        (fun z hz => ⟨(hT z hz).2.1, (hT z hz).2.2.2⟩) d
      have hA : ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
          ≤ 2 * ((∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)) := by
        linarith [hsplit, hcnt1, hcnt2]
      have hρτ : (((d.divisors.card : ℕ) : ℝ)) ^ 3
            * (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          ≤ (((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ) := by
        have h := nm_tau_cube_mul_prod_le d hd1 hsq
        linarith [h]
      have hτ0 : (0 : ℝ) ≤ (((d.divisors.card : ℕ) : ℝ)) ^ 3 := by positivity
      have hb0 : (0 : ℝ) ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := by
        apply mul_nonneg (mul_nonneg _ _) _
        · apply Finset.prod_nonneg; intro p hp; positivity
        · have : (0 : ℝ) ≤ 2 * nearBoxR N / (d : ℝ) :=
            div_nonneg (by linarith) (Nat.cast_nonneg d)
          linarith
        · have : (0 : ℝ) ≤ 2 * nearBoxT ϑ N / (d : ℝ) :=
            div_nonneg (by linarith) (Nat.cast_nonneg d)
          linarith
      calc (((d.divisors.card : ℕ) : ℝ)) ^ 3
            * ((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
          ≤ (((d.divisors.card : ℕ) : ℝ)) ^ 3 * (2 * ((∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hA hτ0
        _ = 2 * ((((d.divisors.card : ℕ) : ℝ)) ^ 3
              * (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ)))
              * ((2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)) := by ring
        _ ≤ 2 * ((((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ))
              * ((2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hρτ (by norm_num)
        _ = 2 * ((((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ)
              * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)) := by ring
    · have hempty : T.filter (fun z => d ∣ Work.FIPlan.gnorm z) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        intro hne
        obtain ⟨z, hz⟩ := hne
        rw [Finset.mem_filter] at hz
        exact hsq (Squarefree.squarefree_of_dvd hz.2 (hT z hz.1).2.2.1)
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
      apply mul_nonneg (by norm_num)
      apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg d)) _) _
      · have : (0 : ℝ) ≤ 2 * nearBoxR N / (d : ℝ) :=
          div_nonneg (by linarith) (Nat.cast_nonneg d)
        linarith
      · have : (0 : ℝ) ≤ 2 * nearBoxT ϑ N / (d : ℝ) :=
          div_nonneg (by linarith) (Nat.cast_nonneg d)
        linarith
  calc (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 4 * ∑ d ∈ Finset.Icc 1 (nearMassX N),
            (((d.divisors.card : ℕ) : ℝ)) ^ 3
              * (((T.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ) := hstep1
    _ ≤ 4 * ∑ d ∈ Finset.Icc 1 (nearMassX N),
          2 * ((((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ)
            * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum hper
    _ = 8 * ∑ d ∈ Finset.Icc 1 (nearMassX N),
          (((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ)
            * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring



private lemma nm_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

private lemma nm_log_two_add_ge_one (N : ℝ) (hN : 1 ≤ N) : (1 : ℝ) ≤ Real.log (2 + N) := by
  have h1 : (3 : ℝ) ≤ 2 + N := by linarith
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h1
  have h3 : (1 : ℝ) < Real.log 3 := Work.FIRed6Axis.one_lt_log_three
  linarith

/-- **The final numerical assembly of the near-axis mass bound.** -/
private theorem nm_near_mass_sum_arith (C4 : ℝ) (hC4 : 0 < C4)
    (hb : ∀ X : ℕ, (∑ d ∈ Finset.Icc 1 X, ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
        ≤ C4 * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ϑ : ℝ, 1 ≤ N → 0 < ϑ → ϑ ≤ 1 →
      (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ)
          * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1))
        ≤ C * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)
            * (Real.log (2 + N)) ^ (20 : ℕ) := by
  refine ⟨1000 * C4 * 5 ^ (16 : ℕ), by positivity, ?_⟩
  intro N ϑ hN hϑ0 hϑ1
  have hN0 : (0 : ℝ) < N := by linarith
  have h2N0 : (0 : ℝ) < 2 * N := by linarith
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hL1 : (1 : ℝ) ≤ Real.log (2 + N) := nm_log_two_add_ge_one N hN
  have hsqN : Real.sqrt N * Real.sqrt N = N := by
    have h := Real.sq_sqrt hN0.le
    rw [pow_two] at h; exact h
  have hsqrt_le_half : Real.sqrt N ≤ (2 * N) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hN0.le (by linarith) (by norm_num)
  have h23_0 : (0 : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h2N0.le _
  have h13_0 : (0 : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg h2N0.le _
  have h13_pos : (0 : ℝ) < (2 * N) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos h2N0 _
  have hpow_half_third : (2 * N) ^ ((1 : ℝ) / 2) * (2 * N) ^ ((1 : ℝ) / 3)
      = (2 * N) ^ ((5 : ℝ) / 6) := by
    rw [← Real.rpow_add h2N0]; norm_num
  have h2_56 : (2 : ℝ) ^ ((5 : ℝ) / 6) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (5 : ℝ) / 6 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have h2_23 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (2 : ℝ) / 3 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hsplit_56 : (2 * N) ^ ((5 : ℝ) / 6) = (2 : ℝ) ^ ((5 : ℝ) / 6) * N ^ ((5 : ℝ) / 6) :=
    Real.mul_rpow (by norm_num) hN0.le
  have hsplit_23 : (2 * N) ^ ((2 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) :=
    Real.mul_rpow (by norm_num) hN0.le
  have hN56 : 0 ≤ N ^ ((5 : ℝ) / 6) := Real.rpow_nonneg hN0.le _
  have hN23 : 0 ≤ N ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hN0.le _
  have hXle : ((nearMassX N : ℕ) : ℝ) ≤ 2 * (2 * N) ^ ((1 : ℝ) / 3) :=
    nearMassX_le_rpow N hN
  have hX1 : (1 : ℝ) ≤ ((nearMassX N : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 * N) ^ ((1 : ℝ) / 3) := Real.one_le_rpow (by linarith) (by norm_num)
    have h2 : (2 * N) ^ ((1 : ℝ) / 3) ≤ ((nearMassX N : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  have hu_le : nearBoxR N ≤ 2 * Real.sqrt N := by
    rw [nearBoxR]
    have h1 : Real.sqrt (2 * N) ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * N) = 2 * Real.sqrt N := by
      rw [show (4 : ℝ) * N = 2 ^ 2 * N by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hv_eq : nearBoxT ϑ N = 6 * ϑ * Real.sqrt N := rfl
  have hc1 : 4 * nearBoxR N * nearBoxT ϑ N ≤ 48 * ϑ * N := by
    rw [hv_eq]
    have hpn : 0 ≤ ϑ * Real.sqrt N := mul_nonneg hϑ0.le hsN
    nlinarith [hu_le, hsqN, nearBoxR_nonneg N, hϑ0, hsN, hpn]
  have hc2 : 2 * nearBoxR N * ((nearMassX N : ℕ) : ℝ) ≤ 16 * N ^ ((5 : ℝ) / 6) := by
    have h1 : 2 * nearBoxR N ≤ 4 * (2 * N) ^ ((1 : ℝ) / 2) := by
      nlinarith [hu_le, hsqrt_le_half, nearBoxR_nonneg N]
    have h2 : 2 * nearBoxR N * ((nearMassX N : ℕ) : ℝ)
        ≤ (4 * (2 * N) ^ ((1 : ℝ) / 2)) * (2 * (2 * N) ^ ((1 : ℝ) / 3)) :=
      mul_le_mul h1 hXle (Nat.cast_nonneg _) (by linarith)
    have h3 : (4 * (2 * N) ^ ((1 : ℝ) / 2)) * (2 * (2 * N) ^ ((1 : ℝ) / 3))
        = 8 * (2 * N) ^ ((5 : ℝ) / 6) := by
      rw [← hpow_half_third]; ring
    have h4 : 8 * (2 * N) ^ ((5 : ℝ) / 6) ≤ 16 * N ^ ((5 : ℝ) / 6) := by
      rw [hsplit_56]
      nlinarith [h2_56, hN56]
    linarith [h2, h3, h4]
  have hc3 : 2 * nearBoxT ϑ N * ((nearMassX N : ℕ) : ℝ) ≤ 48 * N ^ ((5 : ℝ) / 6) := by
    have h1 : 2 * nearBoxT ϑ N ≤ 12 * (2 * N) ^ ((1 : ℝ) / 2) := by
      rw [hv_eq]
      nlinarith [hsqrt_le_half, hsN, hϑ0, hϑ1]
    have h2 : 2 * nearBoxT ϑ N * ((nearMassX N : ℕ) : ℝ)
        ≤ (12 * (2 * N) ^ ((1 : ℝ) / 2)) * (2 * (2 * N) ^ ((1 : ℝ) / 3)) :=
      mul_le_mul h1 hXle (Nat.cast_nonneg _) (by linarith)
    have h3 : (12 * (2 * N) ^ ((1 : ℝ) / 2)) * (2 * (2 * N) ^ ((1 : ℝ) / 3))
        = 24 * (2 * N) ^ ((5 : ℝ) / 6) := by
      rw [← hpow_half_third]; ring
    have h4 : 24 * (2 * N) ^ ((5 : ℝ) / 6) ≤ 48 * N ^ ((5 : ℝ) / 6) := by
      rw [hsplit_56]
      nlinarith [h2_56, hN56]
    linarith [h2, h3, h4]
  have hc4 : ((nearMassX N : ℕ) : ℝ) ^ 2 ≤ 8 * N ^ ((2 : ℝ) / 3) := by
    have h1 : ((nearMassX N : ℕ) : ℝ) ^ 2 ≤ (2 * (2 * N) ^ ((1 : ℝ) / 3)) ^ 2 := by
      have hXn : (0 : ℝ) ≤ ((nearMassX N : ℕ) : ℝ) := Nat.cast_nonneg _
      exact pow_le_pow_left₀ hXn hXle 2
    have h2 : (2 * (2 * N) ^ ((1 : ℝ) / 3)) ^ 2
        = 4 * ((2 * N) ^ ((1 : ℝ) / 3)) ^ 2 := by
      rw [mul_pow]; norm_num
    have h3 : ((2 * N) ^ ((1 : ℝ) / 3)) ^ 2 = (2 * N) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((2 * N) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul h2N0.le]
      norm_num
    have h4 : (2 * N) ^ ((2 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) := hsplit_23
    have h5 : 4 * ((2 : ℝ) ^ ((2 : ℝ) / 3) * N ^ ((2 : ℝ) / 3)) ≤ 8 * N ^ ((2 : ℝ) / 3) := by
      nlinarith [h2_23, hN23]
    linarith [h1, h2, h3, h4, h5]
  have hS1b : (∑ d ∈ Finset.Icc 1 (nearMassX N),
      ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
      ≤ C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ) := hb (nearMassX N)
  have hS2b : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
      ≤ ((nearMassX N : ℕ) : ℝ)
        * ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ) := by
    calc (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
        ≤ ∑ d ∈ Finset.Icc 1 (nearMassX N),
            ((nearMassX N : ℕ) : ℝ) * (((d.divisors.card : ℝ)) ^ 4 / (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd1 : (0 : ℝ) < (d : ℝ) := by
            have : 0 < d := by omega
            exact_mod_cast this
          have hdX : (d : ℝ) ≤ ((nearMassX N : ℕ) : ℝ) := by exact_mod_cast hd.2
          have hxd : 1 ≤ ((nearMassX N : ℕ) : ℝ) / (d : ℝ) := by
            rw [le_div_iff₀ hd1, one_mul]; exact hdX
          have hτ : 0 ≤ ((d.divisors.card : ℝ)) ^ 4 := by positivity
          have heq : ((nearMassX N : ℕ) : ℝ) * (((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
              = ((d.divisors.card : ℝ)) ^ 4 * (((nearMassX N : ℕ) : ℝ) / (d : ℝ)) := by
            field_simp
          rw [heq]
          exact le_mul_of_one_le_right hτ hxd
      _ = ((nearMassX N : ℕ) : ℝ)
            * ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ) := by
          rw [Finset.mul_sum]
  have hS3b : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ))
      ≤ ((nearMassX N : ℕ) : ℝ)
        * ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 := by
    calc (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 (nearMassX N),
            ((nearMassX N : ℕ) : ℝ) * ((d.divisors.card : ℝ)) ^ 4 := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hdX : (d : ℝ) ≤ ((nearMassX N : ℕ) : ℝ) := by exact_mod_cast hd.2
          have hτ : 0 ≤ ((d.divisors.card : ℝ)) ^ 4 := by positivity
          nlinarith [hdX, hτ]
      _ = ((nearMassX N : ℕ) : ℝ)
            * ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 := by
          rw [Finset.mul_sum]
  have hexp : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ)
        * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1))
      = 4 * nearBoxR N * nearBoxT ϑ N
          * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
        + 2 * nearBoxR N * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
        + 2 * nearBoxT ϑ N * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
        + (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ)) := by
    have hterm : ∀ d ∈ Finset.Icc 1 (nearMassX N),
        ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ)
            * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1)
          = 4 * nearBoxR N * nearBoxT ϑ N * (((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
            + 2 * nearBoxR N * ((d.divisors.card : ℝ)) ^ 4
            + 2 * nearBoxT ϑ N * ((d.divisors.card : ℝ)) ^ 4
            + ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : (d : ℝ) ≠ 0 := by
        have : 0 < d := by omega
        positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hlog : Real.log ((nearMassX N : ℕ) : ℝ) + 2 ≤ 5 * Real.log (2 + N) := by
    have hXpos : (0 : ℝ) < ((nearMassX N : ℕ) : ℝ) := by linarith
    have h1 : Real.log ((nearMassX N : ℕ) : ℝ) ≤ Real.log (2 * (2 * N) ^ ((1 : ℝ) / 3)) :=
      Real.log_le_log hXpos hXle
    have h2 : Real.log (2 * (2 * N) ^ ((1 : ℝ) / 3))
        = Real.log 2 + ((1 : ℝ) / 3) * Real.log (2 * N) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt h13_pos), Real.log_rpow h2N0]
    have h3 : Real.log (2 * N) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) (ne_of_gt hN0)
    have h4 : Real.log N ≤ Real.log (2 + N) := Real.log_le_log hN0 (by linarith)
    have h5 : Real.log 2 ≤ 1 := nm_log_two_le_one
    nlinarith [h1, h2, h3, h4, h5, hL1]
  have hlogpow : (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)
      ≤ 5 ^ (16 : ℕ) * (Real.log (2 + N)) ^ (20 : ℕ) := by
    have h1 : (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)
        ≤ (5 * Real.log (2 + N)) ^ (16 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hlog 16
    have h2 : (5 * Real.log (2 + N)) ^ (16 : ℕ)
        = 5 ^ (16 : ℕ) * (Real.log (2 + N)) ^ (16 : ℕ) := by rw [mul_pow]
    have h3 : (Real.log (2 + N)) ^ (16 : ℕ) ≤ (Real.log (2 + N)) ^ (20 : ℕ) :=
      pow_le_pow_right₀ hL1 (by norm_num)
    calc (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)
        ≤ (5 * Real.log (2 + N)) ^ (16 : ℕ) := h1
      _ = 5 ^ (16 : ℕ) * (Real.log (2 + N)) ^ (16 : ℕ) := h2
      _ ≤ 5 ^ (16 : ℕ) * (Real.log (2 + N)) ^ (20 : ℕ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hbig : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ)
        * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1))
      ≤ (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))
        * (120 * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)) := by
    rw [hexp]
    have hA0 : (0 : ℝ) ≤ C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ) := by positivity
    have hS1nn : 0 ≤ ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    have hS2nn : 0 ≤ ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 :=
      Finset.sum_nonneg (fun d _ => by positivity)
    have hS2A : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
        ≤ ((nearMassX N : ℕ) : ℝ)
            * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)) := by
      calc (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
          ≤ ((nearMassX N : ℕ) : ℝ)
              * ∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ) := hS2b
        _ ≤ ((nearMassX N : ℕ) : ℝ)
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)) :=
            mul_le_mul_of_nonneg_left hS1b (Nat.cast_nonneg _)
    have hS3A : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ))
        ≤ ((nearMassX N : ℕ) : ℝ) ^ 2
            * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)) := by
      have h1 : (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ))
          ≤ ((nearMassX N : ℕ) : ℝ)
              * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4) := hS3b
      have h2 : ((nearMassX N : ℕ) : ℝ)
            * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
          ≤ ((nearMassX N : ℕ) : ℝ) * (((nearMassX N : ℕ) : ℝ)
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))) :=
        mul_le_mul_of_nonneg_left hS2A (Nat.cast_nonneg _)
      have h3 : ((nearMassX N : ℕ) : ℝ) * (((nearMassX N : ℕ) : ℝ)
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)))
          = ((nearMassX N : ℕ) : ℝ) ^ 2
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)) := by ring
      linarith [h1, h2, h3]
    have hb1_0 : (0 : ℝ) ≤ 4 * nearBoxR N * nearBoxT ϑ N :=
      mul_nonneg (mul_nonneg (by norm_num) (nearBoxR_nonneg N)) (nearBoxT_nonneg ϑ N hϑ0.le)
    have hb2_0 : (0 : ℝ) ≤ 2 * nearBoxR N := mul_nonneg (by norm_num) (nearBoxR_nonneg N)
    have hb3_0 : (0 : ℝ) ≤ 2 * nearBoxT ϑ N :=
      mul_nonneg (by norm_num) (nearBoxT_nonneg ϑ N hϑ0.le)
    have h1 : 4 * nearBoxR N * nearBoxT ϑ N
          * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
        ≤ 4 * nearBoxR N * nearBoxT ϑ N
          * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)) :=
      mul_le_mul_of_nonneg_left hS1b hb1_0
    have h2 : 2 * nearBoxR N * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
        ≤ 2 * nearBoxR N * (((nearMassX N : ℕ) : ℝ)
            * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))) :=
      mul_le_mul_of_nonneg_left hS2A hb2_0
    have h3 : 2 * nearBoxT ϑ N * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
        ≤ 2 * nearBoxT ϑ N * (((nearMassX N : ℕ) : ℝ)
            * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))) :=
      mul_le_mul_of_nonneg_left hS2A hb3_0
    have hc : 4 * nearBoxR N * nearBoxT ϑ N
          + 2 * nearBoxR N * ((nearMassX N : ℕ) : ℝ)
          + 2 * nearBoxT ϑ N * ((nearMassX N : ℕ) : ℝ)
          + ((nearMassX N : ℕ) : ℝ) ^ 2
        ≤ 120 * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1) := by
      nlinarith [hc1, hc2, hc3, hc4, hN0, hϑ0, hsN, hN56, hN23]
    calc 4 * nearBoxR N * nearBoxT ϑ N
            * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 / (d : ℝ))
          + 2 * nearBoxR N * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
          + 2 * nearBoxT ϑ N * (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4)
          + (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ))
        ≤ 4 * nearBoxR N * nearBoxT ϑ N
            * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))
          + 2 * nearBoxR N * (((nearMassX N : ℕ) : ℝ)
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)))
          + 2 * nearBoxT ϑ N * (((nearMassX N : ℕ) : ℝ)
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)))
          + ((nearMassX N : ℕ) : ℝ) ^ 2
              * (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ)) := by
          linarith [h1, h2, h3, hS3A]
      _ = (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))
            * (4 * nearBoxR N * nearBoxT ϑ N + 2 * nearBoxR N * ((nearMassX N : ℕ) : ℝ)
              + 2 * nearBoxT ϑ N * ((nearMassX N : ℕ) : ℝ) + ((nearMassX N : ℕ) : ℝ) ^ 2) := by
          ring
      _ ≤ (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))
            * (120 * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)) :=
          mul_le_mul_of_nonneg_left hc hA0
  calc (∑ d ∈ Finset.Icc 1 (nearMassX N), ((d.divisors.card : ℝ)) ^ 4 * (d : ℝ)
        * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1))
      ≤ (C4 * (Real.log ((nearMassX N : ℕ) : ℝ) + 2) ^ (16 : ℕ))
        * (120 * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)) := hbig
    _ ≤ (C4 * (5 ^ (16 : ℕ) * (Real.log (2 + N)) ^ (20 : ℕ)))
        * (120 * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlogpow hC4.le
    _ ≤ 1000 * C4 * 5 ^ (16 : ℕ)
        * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)
        * (Real.log (2 + N)) ^ (20 : ℕ) := by
        have hAnn : (0 : ℝ) ≤ C4 * (5 ^ (16 : ℕ) * (Real.log (2 + N)) ^ (20 : ℕ)) := by
          positivity
        have hBnn : (0 : ℝ) ≤ ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1 := by
          have h1 : 0 ≤ ϑ * N := mul_nonneg hϑ0.le hN0.le
          linarith [h1, hsN, hN56, hN23]
        nlinarith [hAnn, hBnn]


/-! ## 6. The target -/

/-- **The (5.16) mass bound for the near-axis zone** (`Work.FIRed6Axis.NearMassBound`; unfold it).

Route (the `τ`-route; the docstring of `NearMassBound` in `Submission/Work/FIRed6Axis/Statement.lean`
records it).  For squarefree `n ≥ 1`,
`Work.FIArea6.tau_small_divisor_localization` gives `4^{ω(n)} ≤ 16Σ_{d|n, d³≤n}τ(d)^6`, so
`τ(n) = 2^{ω(n)} ≤ 4Σ_{d|n, d³≤n}τ(d)^3` (`√(Σa²) ≤ Σa` for `a ≥ 0`), and hence, since `n ≤ 2N`,
`Σ_{z∈T}τ(|z|²) ≤ 4Σ_{d ≤ (2N)^{1/3}}τ(d)^3·#{z ∈ T : d | |z|²}`.  The near zone is axis-aligned:
around each of the four axes and each of its two sides it is contained in a rectangle of side lengths
`W₁ ≍ √N` (radial, in `(√N, √(2N)]`) and `W₂ ≍ ϑ√N` (transverse, from `nearArg (4ϑ)`).  If
`d | z.re² + z.im²` then for each fixed `z.re` the residue class of `z.im` mod `d` is one of at most
`M(d) ≤ 2^{ω(d)}·O(1)` classes (`M(d) = max_c #{v : ZMod d // v² = c}`), so
`#{z ∈ rect : d | |z|²} ≤ (W₁/d + 1)·M(d)·(W₂/d + 1)`; the `d`-sums
`Σ_{d≤X}τ(d)^3M(d)/d²`, `Σ_{d≤X}τ(d)^3M(d)/d` are `≪ (log X)^{O(1)}` and
`Σ_{d≤X}τ(d)^3M(d) ≪ X(log X)^{O(1)}` (`τ(d)^3M(d) ≤ 2^{4ω(d)}`, and
`Work.FIArea6.weighted_tau_sum_le` bounds `Σ 2^{7ω(d)}/d`; for the last use `Σ_{d≤X}a_d ≤ XΣ_{d≤X}a_d/d`).
The resulting terms are `ϑN·(log)^C`, `√N(2N)^{1/3}(log)^C = N^{5/6}(log)^C`, `ϑN^{5/6}(log)^C ≤ √N(log)^C`
and `(2N)^{2/3}(log)^C`, all within the stated `(ϑN + √N + N^{5/6} + N^{2/3} + 1)(log(2+N))^{20}`.
An alternative, cheaper route for the *whole* annulus: split `(N,2N]` and apply
`Work.FIArea6b.sector_tau_sum` to each part, but that route loses a factor `ϑ^{-1}` and does *not*
reach the stated shape — use the `τ`-route above. -/
theorem near_mass_bound : Work.FIRed6Axis.NearMassBound := by
  unfold Work.FIRed6Axis.NearMassBound
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FIArea2.sum_tau_pow_div_le 4
  obtain ⟨Car, hCarpos, har⟩ := nm_near_mass_sum_arith C4 hC4pos hC4
  refine ⟨8 * Car, by positivity, ?_⟩
  intro N ϑ T hN hϑ0 hϑ1 hT
  have h1 := nm_near_mass_reduction N ϑ hN hϑ0 hϑ1 T hT
  have h2 := har N ϑ hN hϑ0 hϑ1
  calc (∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 8 * ∑ d ∈ Finset.Icc 1 (nearMassX N),
          (((d.divisors.card : ℕ) : ℝ)) ^ 4 * (d : ℝ)
            * (2 * nearBoxR N / (d : ℝ) + 1) * (2 * nearBoxT ϑ N / (d : ℝ) + 1) := h1
    _ ≤ 8 * (Car * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + N)) ^ (20 : ℕ)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 8 * Car * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)
          * (Real.log (2 + N)) ^ (20 : ℕ) := by ring

end

end Work.FIRed6Axis
