/-
# FI §15: the per-`z₁` lattice count for the *polar box* (5.14)

For a fixed `z₁ ≠ 0` with `(z₁.re, z₁.im) = 1` and any modulus `q ≥ 1`, the number of `z₂` in the
polar box (5.14) with `4q ∣ |Δ(z₁,z₂)|` is `≪ θ²N/q + √N + 1`.

`Δ(z₁,z₂) = Im(z̄₁z₂) = r₁s₂ - r₂s₁` (`FIPlan.Delta`), so the condition is the congruence
`r₁s₂ ≡ r₂s₁ (4q)`.  The set of solutions is a sublattice of `ℤ[i]` of index `4q` (because
`(r₁,s₁) = 1`), and the polar box is contained in a disc of radius `5θ√N`
(`Work.FIArea4.dist_polarBox_le`), i.e. it is a *thin* (diameter `≲ θ√N`) region.  Fibring over
`z₂.re` and counting the `z₂.im`-values of each fibre — one residue class modulo `4q/e`,
`e = (r₁, 4q)` — gives the count

  `# ≤ (2ρ/e + 1)·(2(ρ+1)/(4q/e) + 1) ≤ 8ρ²/(4q) + 8ρ + 8`,   `ρ = 5θ√N`.

The reduction `e ∣ z₂.re` and the fibre congruence `(4q/e) ∣ z₂.im - z₂'.im` are the two places
where `(r₁,s₁) = 1` is used.  With `θ ≤ 1` (`Work.FIArea4.theta_le_one`) this is
`≪ θ²N/q + √N + 1` as claimed.
-/
import Mathlib
import Submission.Work.FIArea4.S15_hard_defs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.S15delta
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Counting a set of integers in a residue class inside a real interval.**  A finite set of
integers lying in an interval of length `2A` whose elements are pairwise congruent modulo `m`
(`m ≥ 1`) has at most `2(A+1)/m + 1` elements. -/
lemma card_le_of_pairwise_dvd_interval {m : ℕ} (hm : 1 ≤ m) {t A : ℝ} (hA : 0 ≤ A)
    (T : Finset ℤ) (hint : ∀ x ∈ T, |(x : ℝ) - t| ≤ A)
    (hcong : ∀ x ∈ T, ∀ y ∈ T, (m : ℤ) ∣ x - y) :
    (T.card : ℝ) ≤ 2 * (A + 1) / (m : ℝ) + 1 := by
  classical
  rcases T.eq_empty_or_nonempty with h | ⟨r₀, hr₀⟩
  · rw [h]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  · set c₀ : ℤ := ⌈t⌉ with hc₀
    set T' : Finset ℤ := T.image (fun x => x - c₀) with hT'
    have hinj : Set.InjOn (fun x : ℤ => x - c₀) (↑T : Set ℤ) := by
      intro x _ y _ hxy
      exact sub_left_inj.mp hxy
    have hcardT : T'.card = T.card := Finset.card_image_of_injOn hinj
    have hc₀1 : |((c₀ : ℤ) : ℝ) - t| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := Int.le_ceil t
        linarith [hc₀]
      · have := Int.ceil_lt_add_one t
        have : ((c₀ : ℤ) : ℝ) = (⌈t⌉ : ℤ) := by rw [hc₀]
        rw [this]
        linarith
    have habs : ∀ y ∈ T', |(y : ℝ)| ≤ A + 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hx1 : |((x : ℤ) : ℝ) - t| ≤ A := hint x hx
      have hsub : (((x - c₀ : ℤ)) : ℝ) = ((x : ℤ) : ℝ) - ((c₀ : ℤ) : ℝ) := by push_cast; ring
      rw [hsub]
      have h2 : ((x : ℤ) : ℝ) - ((c₀ : ℤ) : ℝ)
          = (((x : ℤ) : ℝ) - t) + (t - ((c₀ : ℤ) : ℝ)) := by ring
      rw [h2]
      calc |((x : ℤ) : ℝ) - t + (t - ((c₀ : ℤ) : ℝ))|
          ≤ |((x : ℤ) : ℝ) - t| + |t - ((c₀ : ℤ) : ℝ)| := abs_add_le _ _
        _ = |((x : ℤ) : ℝ) - t| + |((c₀ : ℤ) : ℝ) - t| := by
              rw [abs_sub_comm t ((c₀ : ℤ) : ℝ)]
        _ ≤ A + 1 := by linarith
    have hmod : ∀ y ∈ T', y ≡ (r₀ - c₀) [ZMOD (m : ℤ)] := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [Int.modEq_iff_dvd]
      have h1 : (m : ℤ) ∣ x - r₀ := hcong x hx r₀ hr₀
      have h2 : (r₀ - c₀) - (x - c₀) = -(x - r₀) := by ring
      rw [h2]
      exact Int.dvd_neg.mpr h1
    have key := Commons.NumberTheory.Int.card_le_of_modEq_abs_le (d := m) hm
      (s := T') (r := r₀ - c₀) (A := A + 1) (by linarith) hmod habs
    rw [← hcardT]
    exact key

/-- **Counting multiples of `e` inside a real interval.**  A finite set of integers lying in an
interval of length `2ρ`, all divisible by `e ≥ 1`, has at most `2ρ/e + 1` elements. -/
lemma card_le_of_dvd_mem_interval {e : ℕ} (he : 1 ≤ e) {t ρ : ℝ} (hρ : 0 ≤ ρ) (T : Finset ℤ)
    (hdvd : ∀ x ∈ T, (e : ℤ) ∣ x) (hint : ∀ x ∈ T, t ≤ (x : ℝ) ∧ (x : ℝ) ≤ t + 2 * ρ) :
    (T.card : ℝ) ≤ 2 * (ρ / e) + 1 := by
  classical
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  set T' : Finset ℤ := T.image (fun x => x / (e : ℤ)) with hT'
  have hinj : Set.InjOn (fun x : ℤ => x / (e : ℤ)) (↑T : Set ℤ) := by
    intro x hx y hy hxy
    have h1 : (e : ℤ) * (x / (e : ℤ)) = x := Int.mul_ediv_cancel' (hdvd x hx)
    have h2 : (e : ℤ) * (y / (e : ℤ)) = y := Int.mul_ediv_cancel' (hdvd y hy)
    change x / (e : ℤ) = y / (e : ℤ) at hxy
    rw [← hxy] at h2
    rw [h1] at h2
    exact h2
  have hcard : T'.card = T.card := Finset.card_image_of_injOn hinj
  have hmain : (T'.card : ℝ) ≤ 2 * (ρ / e) + 1 := by
    refine card_int_le_of_mem_interval T' (t := t / (e : ℝ)) (ρ := ρ / (e : ℝ))
      (by positivity) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h1, h2⟩ := hint x hx
    have hxmul : (e : ℤ) * (x / (e : ℤ)) = x := Int.mul_ediv_cancel' (hdvd x hx)
    have hcast : (((x / (e : ℤ)) : ℤ) : ℝ) = (x : ℝ) / (e : ℝ) := by
      have hh : (e : ℝ) * (((x / (e : ℤ)) : ℤ) : ℝ) = (x : ℝ) := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) hxmul
        push_cast at h
        linarith [h]
      rw [eq_div_iff heR.ne', mul_comm]
      exact hh
    rw [hcast]
    constructor
    · have := div_le_div_of_nonneg_right h1 heR.le
      simpa using this
    · have := div_le_div_of_nonneg_right h2 heR.le
      rw [show t / (e : ℝ) + 2 * (ρ / (e : ℝ)) = (t + 2 * ρ) / (e : ℝ) by ring]
      exact this
  rw [← hcard]
  exact hmain

/-- **The lattice count for a congruence `M ∣ a·s - b·r` in a disc.**  If `S` is a finite set of
Gaussian integers lying in the disc of radius `ρ` about `c : ℂ` and every `z ∈ S` satisfies the
congruence `M ∣ a·z.im - b·z.re` with `M ≥ 1` and `(a,b) = 1`, then
`#S ≤ 8ρ²/M + 8ρ + 8`. -/
theorem card_le_of_congr_disc (S : Finset GaussianInt) (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (a b : ℤ) (M : ℕ) (hM : 1 ≤ M) (hcop : Nat.Coprime a.natAbs b.natAbs)
    (hball : ∀ z ∈ S, ‖z.toComplex - c‖ ≤ ρ)
    (hcong : ∀ z ∈ S, (M : ℤ) ∣ a * z.im - b * z.re) :
    (S.card : ℝ) ≤ 8 * ρ ^ 2 / M + 8 * ρ + 8 := by
  classical
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  set e : ℕ := Nat.gcd a.natAbs M with hedef
  have he1 : 1 ≤ e := by
    rw [hedef]; exact Nat.gcd_pos_of_pos_right _ hMpos
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have heA : e ∣ a.natAbs := by rw [hedef]; exact Nat.gcd_dvd_left _ _
  have heM : e ∣ M := by rw [hedef]; exact Nat.gcd_dvd_right _ _
  have heMle : e ≤ M := Nat.le_of_dvd hMpos heM
  set M₁ : ℕ := M / e with hM₁def
  have hMeq : e * M₁ = M := by rw [hM₁def]; exact Nat.mul_div_cancel' heM
  have hM₁pos : 1 ≤ M₁ := by
    rw [hM₁def]
    exact Nat.div_pos heMle (by omega : 0 < e)
  set a₁ : ℤ := a / (e : ℤ) with ha₁def
  have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  have hea : (e : ℤ) ∣ a := by
    have h1 : (e : ℤ) ∣ ((a.natAbs : ℕ) : ℤ) := by exact_mod_cast heA
    by_cases h : 0 ≤ a
    · rwa [Int.natAbs_of_nonneg h] at h1
    · have h2 : a = -(((a.natAbs : ℕ)) : ℤ) := by
        have h3 : (((-a).natAbs : ℕ) : ℤ) = -a := Int.natAbs_of_nonneg (by omega)
        rw [Int.natAbs_neg] at h3
        omega
      rw [h2]
      exact Int.dvd_neg.mpr h1
  have haeq : a = (e : ℤ) * a₁ := by
    rw [ha₁def]
    exact (Int.mul_ediv_cancel' hea).symm
  have hM₁eqZ : (M : ℤ) = (e : ℤ) * (M₁ : ℤ) := by
    rw [← hMeq]; push_cast; ring
  have hcop₁ : IsCoprime a₁ (M₁ : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    have h1 : a₁.natAbs = a.natAbs / e := by
      rw [ha₁def, Int.natAbs_ediv, Int.natAbs_natCast]
      rw [if_pos (by right; right; exact hea)]
      simp
    rw [h1, Int.natAbs_natCast]
    have hgcd : 0 < Nat.gcd a.natAbs M := by rw [← hedef]; omega
    have := Nat.coprime_div_gcd_div_gcd hgcd
    simpa [hedef] using this
  have he_dvd_M : (e : ℤ) ∣ (M : ℤ) := by exact_mod_cast heM
  have hcop_eb : IsCoprime (e : ℤ) b := by
    rw [Int.isCoprime_iff_nat_coprime]
    have h1 : Nat.Coprime e b.natAbs := Nat.Coprime.coprime_dvd_left heA hcop
    simpa using h1
  have hre : ∀ z ∈ S, (e : ℤ) ∣ z.re := by
    intro z hz
    have h1 : (e : ℤ) ∣ a * z.im - b * z.re := dvd_trans he_dvd_M (hcong z hz)
    have h2 : (e : ℤ) ∣ a * z.im := dvd_mul_of_dvd_left hea z.im
    have h3 : (e : ℤ) ∣ b * z.re := by
      have h := dvd_sub h2 h1
      rwa [show a * z.im - (a * z.im - b * z.re) = b * z.re from by ring] at h
    exact hcop_eb.dvd_of_dvd_mul_left h3
  set R : Finset ℤ := S.image (fun z => z.re) with hRdef
  have hmapsto : Set.MapsTo (fun z : GaussianInt => z.re) (↑S : Set GaussianInt) (↑R : Set ℤ) :=
    fun z hz => Finset.mem_image_of_mem _ hz
  have hcardS : S.card = ∑ r ∈ R, (S.filter (fun z => z.re = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmapsto
  have hre_int : ∀ z ∈ S, |((z.re : ℤ) : ℝ) - c.re| ≤ ρ := by
    intro z hz
    calc |((z.re : ℤ) : ℝ) - c.re| = |(z.toComplex - c).re| := by
          rw [ofReal_re_eq_re z, Complex.sub_re]
      _ ≤ ‖z.toComplex - c‖ := Complex.abs_re_le_norm _
      _ ≤ ρ := hball z hz
  have him_int : ∀ z ∈ S, |((z.im : ℤ) : ℝ) - c.im| ≤ ρ := by
    intro z hz
    calc |((z.im : ℤ) : ℝ) - c.im| = |(z.toComplex - c).im| := by
          rw [ofReal_im_eq_im z, Complex.sub_im]
      _ ≤ ‖z.toComplex - c‖ := Complex.abs_im_le_norm _
      _ ≤ ρ := hball z hz
  have hrele : (R.card : ℝ) ≤ 2 * (ρ / e) + 1 := by
    refine card_le_of_dvd_mem_interval (e := e) he1 (t := c.re - ρ) hρ R ?_ ?_
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hre z hz
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 := hre_int z hz
      rw [abs_le] at h1
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hfib : ∀ r ∈ R, ((S.filter (fun z => z.re = r)).card : ℝ)
      ≤ 2 * (ρ + 1) / (M₁ : ℝ) + 1 := by
    intro r hr
    set F : Finset GaussianInt := S.filter (fun z => z.re = r) with hF
    set T : Finset ℤ := F.image (fun z => z.im) with hT
    have hmem : ∀ z ∈ F, z ∈ S ∧ z.re = r := fun z hz => Finset.mem_filter.mp hz
    have hTinj : T.card = F.card := by
      rw [hT]
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      obtain ⟨hxS, hxr⟩ := hmem x hx
      obtain ⟨hyS, hyr⟩ := hmem y hy
      exact Zsqrtd.ext (by rw [hxr, hyr]) hxy
    have hintT : ∀ y ∈ T, |((y : ℤ) : ℝ) - c.im| ≤ ρ := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact him_int z (hmem z hz).1
    have hcongT : ∀ y ∈ T, ∀ y' ∈ T, (M₁ : ℤ) ∣ y - y' := by
      intro y hy y' hy'
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨hzS, hzr⟩ := hmem z hz
      obtain ⟨hwS, hwr⟩ := hmem w hw
      have h1 : (M : ℤ) ∣ a * (z.im - w.im) := by
        have h2 := hcong z hzS
        have h3 := hcong w hwS
        have h4 := dvd_sub h2 h3
        rwa [show a * z.im - b * z.re - (a * w.im - b * w.re) = a * (z.im - w.im) from by
              rw [hzr, hwr]; ring] at h4
      have h5 : ((e : ℤ) * (M₁ : ℤ)) ∣ ((e : ℤ) * a₁) * (z.im - w.im) := by
        rw [← hM₁eqZ, ← haeq]
        exact h1
      have h6 : (M₁ : ℤ) ∣ a₁ * (z.im - w.im) := by
        refine (mul_dvd_mul_iff_left heZ).mp ?_
        rwa [mul_assoc] at h5
      exact hcop₁.symm.dvd_of_dvd_mul_left h6
    have hkey := card_le_of_pairwise_dvd_interval hM₁pos (t := c.im) (A := ρ) hρ T hintT hcongT
    rw [← hTinj]
    exact hkey
  have hfib0 : (0 : ℝ) ≤ 2 * (ρ + 1) / (M₁ : ℝ) + 1 := by
    have h1 : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast (by omega : 0 < M₁)
    have h2 : (0 : ℝ) ≤ 2 * (ρ + 1) / (M₁ : ℝ) := by positivity
    linarith
  have hsum : (S.card : ℝ) ≤ (R.card : ℝ) * (2 * (ρ + 1) / (M₁ : ℝ) + 1) := by
    rw [hcardS, Nat.cast_sum]
    calc ∑ r ∈ R, ((S.filter (fun z => z.re = r)).card : ℝ)
        ≤ ∑ _r ∈ R, (2 * (ρ + 1) / (M₁ : ℝ) + 1) := Finset.sum_le_sum hfib
      _ = (R.card : ℝ) * (2 * (ρ + 1) / (M₁ : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hM₁R : (M₁ : ℝ) = (M : ℝ) / (e : ℝ) := by
    have h : (e : ℝ) * (M₁ : ℝ) = (M : ℝ) := by rw [← hMeq]; push_cast; ring
    rw [eq_div_iff heR.ne', mul_comm]
    exact h
  have he1R : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
  have heMleR : (e : ℝ) ≤ (M : ℝ) := by exact_mod_cast heMle
  have hfin : (2 * (ρ / (e : ℝ)) + 1) * (2 * (ρ + 1) * (e : ℝ) / (M : ℝ) + 1)
      ≤ 8 * ρ ^ 2 / (M : ℝ) + 8 * ρ + 8 := by
    have hX : 2 * (ρ / (e : ℝ)) ≤ 2 * ρ := by
      have h1 : ρ / (e : ℝ) ≤ ρ := by
        rw [div_le_iff₀ heR]
        nlinarith [hρ, he1R, mul_nonneg hρ (by linarith : (0 : ℝ) ≤ (e : ℝ) - 1)]
      linarith
    have hY : 2 * (ρ + 1) * (e : ℝ) / (M : ℝ) ≤ 2 * (ρ + 1) := by
      rw [div_le_iff₀ hMR]
      have hp : (0 : ℝ) ≤ ρ + 1 := by linarith
      have h1 := mul_le_mul_of_nonneg_left heMleR hp
      nlinarith [h1]
    have hXY : (2 * (ρ / (e : ℝ))) * (2 * (ρ + 1) * (e : ℝ) / (M : ℝ))
        = 4 * ρ * (ρ + 1) / (M : ℝ) := by
      field_simp
      try ring
    have hexp : (2 * (ρ / (e : ℝ)) + 1) * (2 * (ρ + 1) * (e : ℝ) / (M : ℝ) + 1)
        = (2 * (ρ / (e : ℝ))) * (2 * (ρ + 1) * (e : ℝ) / (M : ℝ))
          + (2 * (ρ / (e : ℝ)) + 2 * (ρ + 1) * (e : ℝ) / (M : ℝ) + 1) := by ring
    rw [hexp, hXY]
    have hfin2 : 4 * ρ * (ρ + 1) / (M : ℝ) ≤ 4 * ρ ^ 2 / (M : ℝ) + 4 * ρ := by
      rw [div_le_iff₀ hMR, add_mul]
      have h2 : 4 * ρ ^ 2 / (M : ℝ) * (M : ℝ) = 4 * ρ ^ 2 := by field_simp
      rw [h2]
      nlinarith [mul_nonneg hρ (by linarith : (0 : ℝ) ≤ (M : ℝ) - 1)]
    have hr2 : 0 ≤ 4 * ρ ^ 2 / (M : ℝ) := div_nonneg (by positivity) hMR.le
    have hsum2 : 4 * ρ * (ρ + 1) / (M : ℝ)
          + (2 * (ρ / (e : ℝ)) + 2 * (ρ + 1) * (e : ℝ) / (M : ℝ) + 1)
        ≤ (4 * ρ ^ 2 / (M : ℝ) + 4 * ρ) + (2 * ρ + 2 * (ρ + 1) + 1) := by
      linarith [hX, hY, hfin2]
    have hsum3 : (4 * ρ ^ 2 / (M : ℝ) + 4 * ρ) + (2 * ρ + 2 * (ρ + 1) + 1)
        ≤ 8 * ρ ^ 2 / (M : ℝ) + 8 * ρ + 8 := by
      have h84 : 8 * ρ ^ 2 / (M : ℝ) = 2 * (4 * ρ ^ 2 / (M : ℝ)) := by ring
      rw [h84]
      linarith [hr2]
    linarith [hsum2, hsum3]
  calc (S.card : ℝ) ≤ (R.card : ℝ) * (2 * (ρ + 1) / (M₁ : ℝ) + 1) := hsum
    _ ≤ (2 * (ρ / e) + 1) * (2 * (ρ + 1) / (M₁ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hrele hfib0
    _ ≤ 8 * ρ ^ 2 / M + 8 * ρ + 8 := by
        rw [hM₁R]
        have hform : 2 * (ρ + 1) / ((M : ℝ) / (e : ℝ)) = 2 * (ρ + 1) * (e : ℝ) / (M : ℝ) := by
          field_simp
        rw [hform]
        exact hfin

theorem S15_ap_polar_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (q : ℕ) (z1 : GaussianInt),
      1 ≤ q → z1 ≠ 0 → Nat.Coprime z1.re.natAbs z1.im.natAbs →
      ((Work.FIArea4.S15polarBox Pa φ).filter
          (fun z2 => 4 * q ∣ Work.FIPlan.absDelta z1 z2)).card
        ≤ C * ((Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) / (q : ℝ)
                + Real.sqrt Pa.N + 1) := by
  refine ⟨100, by norm_num, ?_⟩
  intro Pa φ q z1 hq hz1 hcop
  set S : Finset GaussianInt :=
    (Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => 4 * q ∣ Work.FIPlan.absDelta z1 z2)
    with hS
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρdef
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hcdef
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hsN0 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hsNsq : Real.sqrt Pa.N ^ 2 = Pa.N := Real.sq_sqrt (by linarith)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]; positivity
  have hball : ∀ z ∈ S, ‖z.toComplex - c‖ ≤ ρ := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := (mem_S15polarBox.mp hz.1).2
    rw [hcdef, hρdef]
    exact dist_polarBox_le Pa φ z hbox
  have hcong : ∀ z ∈ S, ((4 * q : ℕ) : ℤ) ∣ z1.re * z.im - z1.im * z.re := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    have h := (dvd_absDelta_iff z1 z q).mp hz.2
    rwa [show z.re * z1.im = z1.im * z.re from by ring] at h
  have hmain := card_le_of_congr_disc S c ρ hρ0 z1.re z1.im (4 * q) (by omega) hcop hball hcong
  have hrho : 8 * ρ ^ 2 / ((4 * q : ℕ) : ℝ) + 8 * ρ + 8
      = 50 * Pa.θ ^ 2 * Pa.N / (q : ℝ) + 40 * Pa.θ * Real.sqrt Pa.N + 8 := by
    have h4q : (((4 * q : ℕ)) : ℝ) = 4 * (q : ℝ) := by push_cast; ring
    have hρsq : ρ ^ 2 = 25 * Pa.θ ^ 2 * Pa.N := by
      rw [hρdef]
      rw [show (5 * Pa.θ * Real.sqrt Pa.N) ^ 2
          = 25 * Pa.θ ^ 2 * (Real.sqrt Pa.N) ^ 2 by ring, hsNsq]
    rw [hρsq, hρdef, h4q]
    field_simp
    try ring
  have hle : 50 * Pa.θ ^ 2 * Pa.N / (q : ℝ) + 40 * Pa.θ * Real.sqrt Pa.N + 8
      ≤ 100 * ((Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) / (q : ℝ)
                + Real.sqrt Pa.N + 1) := by
    have hA0 : 0 ≤ Pa.θ ^ 2 * Pa.N := by positivity
    have hB0 : 0 ≤ Pa.θ * Real.sqrt Pa.N := by positivity
    have hD0 : 0 ≤ (100 - 40 * Pa.θ) * (Real.sqrt Pa.N * (q : ℝ)) :=
      mul_nonneg (by linarith) (by positivity)
    have hkey : (50 * Pa.θ ^ 2 * Pa.N / (q : ℝ) + 40 * Pa.θ * Real.sqrt Pa.N + 8)
          * (q : ℝ)
        = 50 * Pa.θ ^ 2 * Pa.N + 40 * Pa.θ * Real.sqrt Pa.N * (q : ℝ) + 8 * (q : ℝ) := by
      field_simp
      try ring
    have hkey2 : (100 * ((Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) / (q : ℝ)
            + Real.sqrt Pa.N + 1)) * (q : ℝ)
        = 100 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
            + 100 * Real.sqrt Pa.N * (q : ℝ) + 100 * (q : ℝ) := by
      field_simp
      try ring
    have hmul : (50 * Pa.θ ^ 2 * Pa.N / (q : ℝ) + 40 * Pa.θ * Real.sqrt Pa.N + 8)
          * (q : ℝ)
        ≤ (100 * ((Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) / (q : ℝ)
                + Real.sqrt Pa.N + 1)) * (q : ℝ) := by
      rw [hkey, hkey2]
      nlinarith [hA0, hB0, hD0]
    exact le_of_mul_le_mul_right hmul hq0
  rw [hrho] at hmain
  linarith [hmain, hle]

end

end Work.FIArea4
