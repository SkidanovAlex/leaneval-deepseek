import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaZeroBridge

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- A `1`-separated set of reals contained in `[-L, L]` has at most `2L + 2` elements. -/
private lemma card_separated_abs_le {S : Finset ℝ} {L : ℝ} (hL : 1 ≤ L)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hbd : ∀ x ∈ S, -L ≤ x ∧ x ≤ L) : (S.card : ℝ) ≤ 2 * L + 2 := by
  have hinj : Set.InjOn (fun x : ℝ => ⌊x⌋) (↑S) := by
    intro x hx y hy hxy
    change ⌊x⌋ = ⌊y⌋ at hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : (1 : ℝ) ≤ |x - y| := hsep x hx y hy hne
      rw [abs_of_neg (by linarith)] at h1
      have h2 : ⌊x + 1⌋ ≤ ⌊y⌋ := Int.floor_mono (by linarith)
      rw [Int.floor_add_one] at h2
      omega
    · have h1 : (1 : ℝ) ≤ |x - y| := hsep x hx y hy hne
      rw [abs_of_pos (by linarith)] at h1
      have h2 : ⌊y + 1⌋ ≤ ⌊x⌋ := Int.floor_mono (by linarith)
      rw [Int.floor_add_one] at h2
      omega
  have himg : (Finset.image (fun x : ℝ => ⌊x⌋) S).card = S.card :=
    Finset.card_image_of_injOn hinj
  have hsub : Finset.image (fun x : ℝ => ⌊x⌋) S ⊆ Finset.Icc ⌊-L⌋ ⌊L⌋ := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [Finset.mem_Icc]
    obtain ⟨hb1, hb2⟩ := hbd x hx
    exact ⟨Int.floor_mono hb1, Int.floor_mono hb2⟩
  have hcard : ((Finset.Icc ⌊-L⌋ ⌊L⌋).card : ℝ) ≤ 2 * L + 2 := by
    rw [Int.card_Icc, Int.floor_neg]
    have hpos : (0 : ℤ) ≤ ⌊L⌋ + 1 + ⌈L⌉ := by
      have h1 : (0 : ℤ) ≤ ⌊L⌋ := Int.le_floor.mpr (by push_cast; linarith)
      have h2 : (0 : ℤ) ≤ ⌈L⌉ := Int.ceil_nonneg (by linarith)
      linarith
    have hnat : ((⌊L⌋ + 1 - -⌈L⌉).toNat : ℤ) = ⌊L⌋ + 1 + ⌈L⌉ := by
      rw [show ⌊L⌋ + 1 - -⌈L⌉ = ⌊L⌋ + 1 + ⌈L⌉ by ring]
      exact Int.toNat_of_nonneg hpos
    have hcast : (((⌊L⌋ + 1 - -⌈L⌉).toNat : ℤ) : ℝ) ≤ 2 * L + 2 := by
      rw [hnat]
      have hflL : (⌊L⌋ : ℝ) ≤ L := Int.floor_le L
      have hceL : (⌈L⌉ : ℝ) ≤ L + 1 := by have := Int.ceil_lt_add_one L; linarith
      push_cast
      linarith
    exact_mod_cast hcast
  calc (S.card : ℝ) = ((Finset.image (fun x : ℝ => ⌊x⌋) S).card : ℝ) := by rw [himg]
    _ ≤ ((Finset.Icc ⌊-L⌋ ⌊L⌋).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub)
    _ ≤ 2 * L + 2 := hcard

/-- Elementary lower bound for the last summand of the combined count in the regime `K > T ^ 4`,
where the detector is unavailable. -/
private lemma fallback_arith {A T σ Y : ℝ} {K : ℕ}
    (hA : 6 ≤ A) (hT : 2 ≤ T) (hK4 : T ^ 4 < (K : ℝ)) (hY1 : 1 ≤ Y)
    (hY2 : Y ≤ (A * T) ^ 2) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    A ^ (-(4 : ℝ) / 3) * T ^ ((5 : ℝ) / 3)
      ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) := by
  have hT0 : 0 < T := by linarith
  have hA0 : 0 < A := by linarith
  have hAT0 : 0 < A * T := mul_pos hA0 hT0
  have hY0 : 0 < Y := by linarith
  have hTnn : (0 : ℝ) ≤ T := hT0.le
  have hYnn : (0 : ℝ) ≤ Y := hY0.le
  have hTKnn : (0 : ℝ) ≤ T + (K : ℝ) := add_nonneg hTnn (Nat.cast_nonneg K)
  -- `Y ^ e ≥ (A * T) ^ (-4/3)` for `e = (2 - 4 σ)/3 ∈ [-2/3, 0]`
  have he : (-(2 : ℝ) / 3) ≤ (2 - 4 * σ) / 3 := by linarith
  have hYexp : (A * T) ^ (-(4 : ℝ) / 3) ≤ Y ^ ((2 - 4 * σ) / 3) := by
    have h1 : ((A * T) ^ 2 : ℝ) ^ (-(2 : ℝ) / 3) ≤ Y ^ ((2 - 4 * σ) / 3) :=
      le_trans (Real.rpow_le_rpow_of_nonpos hY0 hY2 (by norm_num))
        (Real.rpow_le_rpow_of_exponent_le hY1 he)
    rwa [show ((A * T) ^ 2 : ℝ) ^ (-(2 : ℝ) / 3) = (A * T) ^ (-(4 : ℝ) / 3) by
        rw [← Real.rpow_natCast (A * T) 2, ← Real.rpow_mul (le_of_lt hAT0)]; norm_num] at h1
  -- `(T + K) ^ (2/3) ≥ T ^ (8/3)`
  have hTKpow : T ^ ((8 : ℝ) / 3) ≤ (T + (K : ℝ)) ^ ((2 : ℝ) / 3) := by
    have hTK : T ^ 4 < T + (K : ℝ) := by linarith
    have h4 : (T ^ 4 : ℝ) ^ ((2 : ℝ) / 3) < (T + (K : ℝ)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_lt_rpow (pow_nonneg hT0.le 4) hTK (by norm_num)
    have h5 : T ^ ((8 : ℝ) / 3) < (T + (K : ℝ)) ^ ((2 : ℝ) / 3) := by
      rwa [show (T ^ 4 : ℝ) ^ ((2 : ℝ) / 3) = T ^ ((8 : ℝ) / 3) by
          rw [← Real.rpow_natCast T 4, ← Real.rpow_mul (le_of_lt hT0)]; norm_num] at h4
    exact le_of_lt h5
  have hstep : T ^ ((1 : ℝ) / 3) * T ^ ((8 : ℝ) / 3)
      ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hTKpow (Real.rpow_nonneg hTnn _)
  have hT53 : T ^ ((5 : ℝ) / 3) = T ^ ((1 : ℝ) / 3) * T ^ ((8 : ℝ) / 3) * T ^ (-(4 : ℝ) / 3) := by
    rw [mul_assoc, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    norm_num
  have hAT43 : (A * T) ^ (-(4 : ℝ) / 3) = A ^ (-(4 : ℝ) / 3) * T ^ (-(4 : ℝ) / 3) :=
    Real.mul_rpow (le_of_lt hA0) (le_of_lt hT0)
  calc A ^ (-(4 : ℝ) / 3) * T ^ ((5 : ℝ) / 3)
      = A ^ (-(4 : ℝ) / 3) * (T ^ ((1 : ℝ) / 3) * T ^ ((8 : ℝ) / 3) * T ^ (-(4 : ℝ) / 3)) := by
        rw [hT53]
    _ = T ^ ((1 : ℝ) / 3) * T ^ ((8 : ℝ) / 3) * (A ^ (-(4 : ℝ) / 3) * T ^ (-(4 : ℝ) / 3)) := by
        ring
    _ = T ^ ((1 : ℝ) / 3) * T ^ ((8 : ℝ) / 3) * (A * T) ^ (-(4 : ℝ) / 3) := by rw [hAT43]
    _ ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * (A * T) ^ (-(4 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg (le_of_lt hAT0) _)
    _ ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) :=
        mul_le_mul_of_nonneg_left hYexp
          (mul_nonneg (Real.rpow_nonneg hTnn _) (Real.rpow_nonneg hTKnn _))

/-- **The combined large-values count of Montgomery's argument for `ζ`** (Montgomery–Vaughan
§28.4.1, both cases, plus the low zeros, at `q = Q = 1`): the single estimate into which the two
counts (`zetaTailCountEta` for the tail alternative, `zetaIntegralCount` for the contour-integral
alternative) and the count of zeros of small height combine.  `A ≥ 6` is the truncation parameter
of the detector `zetaDetector12`.  For every `1`-separated set `R` of zeros of `ζ` in the window
`σ ≤ Re ≤ 1`, `|Im| ≤ T`,

`#R ≤ C T^ε ( (log (AT))² + Y^{2-2σ} + (AT)K^{1-2σ} + T^{1/3}(T+K)^{2/3} Y^{(2-4σ)/3} )`.

The first summand counts the zeros with `|Im| < (log (AT))²` (at most `2(log(AT))²+1` of them, by
`1`-separation); for the others the detector gives one of its two alternatives, and the remaining
two summands are the two counts. -/
theorem zetaCountCombined_of_pieces
    (hdet : ∀ A : ℝ, 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ T ^ 4 →
      1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        (1 / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)‖)
          ∨ (1 / 12 ≤ Y ^ (1 / 2 - ρ.re) *
              ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
                ‖riemannZeta ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                  * ‖MK K ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                  * ‖Complex.Gamma (((1 / 2 : ℝ) - ρ.re : ℝ) + (v : ℝ) * Complex.I)‖))
    (htail : ∀ A : ℝ, 6 ≤ A → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ),
      1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (∀ z ∈ R, (1 : ℝ) / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-z) * Complex.exp (-(n : ℂ) / Y)‖) →
          (R.card : ℝ) ≤ C * T ^ ε * (Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)))
    (hint : ∀ A : ℝ, 6 ≤ A → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ),
      1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (∀ z ∈ R, (1 : ℝ) / 12 ≤ Y ^ (1 / 2 - z.re) *
            ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
              ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                * ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
                * ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) →
          (R.card : ℝ) ≤ C * T ^ ε *
            (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)))
    : ∀ A : ℝ, 6 ≤ A → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ),
      1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T → ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (R.card : ℝ) ≤ C * T ^ ε *
            ((Real.log (A * T)) ^ 2 + Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)
              + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3)
                  * Y ^ ((2 - 4 * σ) / 3)) := by
  intro A hA ε hε
  obtain ⟨Ct, hCtpos, hCtb⟩ := htail A hA ε hε
  obtain ⟨Ci, hCipos, hCib⟩ := hint A hA ε hε
  refine ⟨max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : (0 : ℝ) < Ct + Ci + 4) (le_max_left _ _)
  intro σ T hσ hσ1 hT K Y hK hY1 hY2 R hwin hsep
  set L := (Real.log (A * T)) ^ 2 with hLdef
  have hlog1 : (1 : ℝ) ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le (by nlinarith [hA, hT])]
    have h3 : (3 : ℝ) < A * T := by nlinarith [hA, hT]
    linarith [Real.exp_one_lt_three]
  have hL1 : 1 ≤ L := by rw [hLdef]; nlinarith
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hT1 : (1 : ℝ) < T := by linarith
  have hTeps1 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow (le_of_lt hT1) hε.le
  have hTeps0 : 0 ≤ T ^ ε := le_trans zero_le_one hTeps1
  have hYnn : (0 : ℝ) ≤ Y := by linarith
  have hTnn : (0 : ℝ) ≤ T := by linarith
  have hATnn : (0 : ℝ) ≤ A * T := mul_nonneg (by linarith) hTnn
  have hTKnn : (0 : ℝ) ≤ T + (K : ℝ) := add_nonneg hTnn (Nat.cast_nonneg K)
  have hterm4nn : (0 : ℝ) ≤ T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hTnn _) (Real.rpow_nonneg hTKnn _))
      (Real.rpow_nonneg hYnn _)
  have hs1nn : (0 : ℝ) ≤ Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ) :=
    add_nonneg (Real.rpow_nonneg hYnn _) (mul_nonneg hATnn (Real.rpow_nonneg (Nat.cast_nonneg K) _))
  set g : ℝ := L + Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)
      + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) with hgdef
  have hg0 : 0 ≤ g := by
    rw [hgdef]
    linarith [hL0, hs1nn, hterm4nn]
  have hLg : L ≤ g := by
    rw [hgdef]
    linarith [hs1nn, hterm4nn]
  by_cases hK4 : (K : ℝ) ≤ T ^ 4
  · -- detector branch
    let tailF : ℂ → ℂ := fun z => ∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
        mCoef K n * (n : ℂ) ^ (-z) * Complex.exp (-(n : ℂ) / Y)
    let integF : ℂ → ℝ := fun z => Y ^ (1 / 2 - z.re) *
        ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
          ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
            * ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
            * ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖
    set Rhigh : Finset ℂ := R.filter (fun z => L ≤ |z.im|) with hRhigh
    set Rlow : Finset ℂ := R.filter (fun z => ¬ (L ≤ |z.im|)) with hRlow
    have hRhigh_mem : ∀ z, z ∈ Rhigh ↔ z ∈ R ∧ L ≤ |z.im| := by
      intro z; rw [hRhigh]; exact Finset.mem_filter
    have hRlow_mem : ∀ z, z ∈ Rlow ↔ z ∈ R ∧ ¬ (L ≤ |z.im|) := by
      intro z; rw [hRlow]; exact Finset.mem_filter
    have hRhigh_sub : Rhigh ⊆ R := fun z hz => ((hRhigh_mem z).mp hz).1
    have hRlow_sub : Rlow ⊆ R := fun z hz => ((hRlow_mem z).mp hz).1
    have hcard_eq : R.card = Rhigh.card + Rlow.card := by
      rw [hRhigh, hRlow]
      exact (Finset.card_filter_add_card_filter_not (fun z : ℂ => L ≤ |z.im|) (s := R)).symm
    have hRlowcard : (Rlow.card : ℝ) ≤ 2 * L + 2 := by
      rw [← Finset.card_image_of_injOn (f := fun z : ℂ => z.im) (s := Rlow) ?_]
      · apply card_separated_abs_le hL1
        · intro x hx y hy hxy
          rw [Finset.mem_image] at hx hy
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨z', hz', rfl⟩ := hy
          have hzneq : z ≠ z' := by intro h; exact hxy (by rw [h])
          exact hsep z (hRlow_sub hz) z' (hRlow_sub hz') hzneq
        · intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          have hlt : |z.im| < L := lt_of_not_ge ((hRlow_mem z).mp hz).2
          rw [abs_lt] at hlt
          exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩
      · intro z hz z' hz' him
        by_contra hne
        have h1 : (1 : ℝ) ≤ |z.im - z'.im| := hsep z (hRlow_sub hz) z' (hRlow_sub hz') hne
        rw [show z.im = z'.im from him, sub_self, abs_zero] at h1
        linarith
    have hRhigh_det : ∀ z ∈ Rhigh, (1 / 12 ≤ ‖tailF z‖) ∨ (1 / 12 ≤ integF z) := by
      intro z hz
      obtain ⟨hzR, hzL⟩ := (hRhigh_mem z).mp hz
      obtain ⟨hord, hreσ, hre1, himT⟩ := hwin z hzR
      have hre12 : (1 : ℝ) / 2 ≤ z.re := le_trans hσ hreσ
      have hz0 : riemannZeta z = 0 := (zetaZeroBridge z hre12 hre1).mp hord
      simpa only [tailF, integF] using hdet A hA T hT K Y hK hK4 hY1 hY2 z hz0 hre12 hre1 himT hzL
    set Rtail : Finset ℂ := Rhigh.filter (fun z => (1 : ℝ) / 12 ≤ ‖tailF z‖) with hRtail
    set Rint : Finset ℂ := Rhigh.filter (fun z => ¬ ((1 : ℝ) / 12 ≤ ‖tailF z‖)) with hRint
    have hRtail_mem : ∀ z, z ∈ Rtail ↔ z ∈ Rhigh ∧ (1 : ℝ) / 12 ≤ ‖tailF z‖ := by
      intro z; rw [hRtail]; exact Finset.mem_filter
    have hRint_mem : ∀ z, z ∈ Rint ↔ z ∈ Rhigh ∧ ¬ ((1 : ℝ) / 12 ≤ ‖tailF z‖) := by
      intro z; rw [hRint]; exact Finset.mem_filter
    have hRtail_sub : Rtail ⊆ R := fun z hz => hRhigh_sub ((hRtail_mem z).mp hz).1
    have hRint_sub : Rint ⊆ R := fun z hz => hRhigh_sub ((hRint_mem z).mp hz).1
    have hcard_high : Rhigh.card = Rtail.card + Rint.card := by
      rw [hRtail, hRint]
      exact (Finset.card_filter_add_card_filter_not (fun z : ℂ => (1 : ℝ) / 12 ≤ ‖tailF z‖)
        (s := Rhigh)).symm
    have htail_win : ∀ z ∈ Rtail, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
        σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T := fun z hz => hwin z (hRtail_sub hz)
    have htail_sep : ∀ z ∈ Rtail, ∀ z' ∈ Rtail, z ≠ z' → 1 ≤ |z.im - z'.im| :=
      fun z hz z' hz' hne => hsep z (hRtail_sub hz) z' (hRtail_sub hz') hne
    have htail_hyp : ∀ z ∈ Rtail, (1 : ℝ) / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
          mCoef K n * (n : ℂ) ^ (-z) * Complex.exp (-(n : ℂ) / Y)‖ := by
      intro z hz; simpa only [tailF] using ((hRtail_mem z).mp hz).2
    have hint_win : ∀ z ∈ Rint, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
        σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T := fun z hz => hwin z (hRint_sub hz)
    have hint_sep : ∀ z ∈ Rint, ∀ z' ∈ Rint, z ≠ z' → 1 ≤ |z.im - z'.im| :=
      fun z hz z' hz' hne => hsep z (hRint_sub hz) z' (hRint_sub hz') hne
    have hint_hyp : ∀ z ∈ Rint, (1 : ℝ) / 12 ≤ Y ^ (1 / 2 - z.re) *
        ∫ v in (-(A * Real.log (A * T)))..(A * Real.log (A * T)),
          ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
            * ‖MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖
            * ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖ := by
      intro z hz
      obtain ⟨hzh, hnt⟩ := (hRint_mem z).mp hz
      rcases hRhigh_det z hzh with h | h
      · exact absurd h hnt
      · simpa only [integF] using h
    have htailcard : (Rtail.card : ℝ) ≤ Ct * T ^ ε * (Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)) :=
      hCtb σ T hσ hσ1 hT K Y hK hY1 hY2 Rtail htail_win htail_sep htail_hyp
    have hintcard : (Rint.card : ℝ) ≤ Ci * T ^ ε *
        (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)) :=
      hCib σ T hσ hσ1 hT K Y hK hY1 hY2 Rint hint_win hint_sep hint_hyp
    have hs1 : Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ) ≤ g := by
      rw [hgdef]
      linarith [hterm4nn]
    have hs2 : T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) ≤ g := by
      rw [hgdef]
      linarith [hs1nn]
    have hcard_eq2 : R.card = Rtail.card + Rint.card + Rlow.card := by
      rw [hcard_eq, hcard_high]
    have hCge : Ct + Ci + 4 ≤ max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3)) := le_max_left _ _
    calc (R.card : ℝ)
        = (Rtail.card : ℝ) + (Rint.card : ℝ) + (Rlow.card : ℝ) := by
          rw [hcard_eq2]; push_cast; ring
      _ ≤ Ct * T ^ ε * (Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ))
            + Ci * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3))
            + (2 * L + 2) := by linarith [htailcard, hintcard, hRlowcard]
      _ ≤ (max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3))) * T ^ ε * g := by
          have h1 : Ct * T ^ ε * (Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ))
              ≤ Ct * T ^ ε * g := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hCtpos.le hTeps0)
          have h2 : Ci * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3))
              ≤ Ci * T ^ ε * g := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hCipos.le hTeps0)
          have h3 : 2 * L + 2 ≤ 4 * T ^ ε * g := by
            have ha : 2 * L + 2 ≤ 4 * L := by linarith
            have hb : 4 * L ≤ 4 * T ^ ε * L := by nlinarith [hTeps1, hL0]
            have hc : 4 * T ^ ε * L ≤ 4 * T ^ ε * g := by
              have : (0 : ℝ) ≤ 4 * T ^ ε := mul_nonneg (by norm_num) hTeps0
              exact mul_le_mul_of_nonneg_left hLg this
            linarith
          have hsum : Ct * T ^ ε * g + Ci * T ^ ε * g + 4 * T ^ ε * g
              ≤ (max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3))) * T ^ ε * g := by
            rw [show Ct * T ^ ε * g + Ci * T ^ ε * g + 4 * T ^ ε * g
                = (Ct + Ci + 4) * (T ^ ε * g) by ring]
            calc (Ct + Ci + 4) * (T ^ ε * g)
                ≤ max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3)) * (T ^ ε * g) :=
                  mul_le_mul_of_nonneg_right hCge (mul_nonneg hTeps0 hg0)
              _ = max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3)) * T ^ ε * g := by ring
          linarith
  · -- fallback branch: `K > T ^ 4`
    push_neg at hK4
    have hRcardT : (R.card : ℝ) ≤ 2 * T + 2 := by
      rw [← Finset.card_image_of_injOn (f := fun z : ℂ => z.im) (s := R) ?_]
      · apply card_separated_abs_le (by linarith : (1 : ℝ) ≤ T)
        · intro x hx y hy hxy
          rw [Finset.mem_image] at hx hy
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨z', hz', rfl⟩ := hy
          have hzneq : z ≠ z' := by intro h; exact hxy (by rw [h])
          exact hsep z hz z' hz' hzneq
        · intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          have him : |z.im| ≤ T := (hwin z hz).2.2.2
          rw [abs_le] at him
          exact him
      · intro z hz z' hz' him
        by_contra hne
        have h1 : (1 : ℝ) ≤ |z.im - z'.im| := hsep z hz z' hz' hne
        rw [show z.im = z'.im from him, sub_self, abs_zero] at h1
        linarith
    have hgle : A ^ (-(4 : ℝ) / 3) * T ^ ((5 : ℝ) / 3) ≤ g := by
      rw [hgdef]
      linarith [hs1nn, fallback_arith hA hT hK4 hY1 hY2 hσ hσ1]
    have hC2 : (3 : ℝ) * A ^ ((4 : ℝ) / 3) ≤ max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3)) :=
      le_max_right _ _
    calc (R.card : ℝ) ≤ 2 * T + 2 := hRcardT
      _ ≤ 3 * T := by linarith
      _ ≤ 3 * T ^ ((5 : ℝ) / 3) := by
          have hpow : T ≤ T ^ ((5 : ℝ) / 3) := by
            have h23 : (1 : ℝ) ≤ T ^ ((2 : ℝ) / 3) := Real.one_le_rpow (by linarith) (by norm_num)
            have hsp : T ^ ((5 : ℝ) / 3) = T * T ^ ((2 : ℝ) / 3) := by
              rw [show (5 : ℝ) / 3 = 1 + 2 / 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
            rw [hsp]; nlinarith
          linarith
      _ ≤ (3 * A ^ ((4 : ℝ) / 3)) * T ^ ε * g := by
          have hAg : T ^ ((5 : ℝ) / 3) ≤ A ^ ((4 : ℝ) / 3) * T ^ ε * g := by
            have hApos : (0 : ℝ) ≤ A ^ ((4 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
            have hsplit : A ^ ((4 : ℝ) / 3) * (A ^ (-(4 : ℝ) / 3) * T ^ ((5 : ℝ) / 3))
                = T ^ ((5 : ℝ) / 3) := by
              rw [← mul_assoc, ← Real.rpow_add (by linarith : (0 : ℝ) < A)]
              norm_num
            have hge : g ≤ T ^ ε * g := le_mul_of_one_le_left hg0 hTeps1
            calc T ^ ((5 : ℝ) / 3)
                = A ^ ((4 : ℝ) / 3) * (A ^ (-(4 : ℝ) / 3) * T ^ ((5 : ℝ) / 3)) := hsplit.symm
              _ ≤ A ^ ((4 : ℝ) / 3) * g := mul_le_mul_of_nonneg_left hgle hApos
              _ ≤ A ^ ((4 : ℝ) / 3) * (T ^ ε * g) := mul_le_mul_of_nonneg_left hge hApos
              _ = A ^ ((4 : ℝ) / 3) * T ^ ε * g := by ring
          nlinarith
      _ ≤ (max (Ct + Ci + 4) (3 * A ^ ((4 : ℝ) / 3))) * T ^ ε * g := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hTeps0) hg0


/-- **The combined large-values count of Montgomery's argument for `ζ`** (Montgomery–Vaughan
§28.4.1, both cases, plus the low zeros, at `q = Q = 1`): the single estimate into which the two
counts (`zetaTailCountEta` for the tail alternative, `zetaIntegralCount` for the contour-integral
alternative) and the count of zeros of small height combine.  `A ≥ 6` is the truncation parameter
of the detector `zetaDetector12`.  For every `1`-separated set `R` of zeros of `ζ` in the window
`σ ≤ Re ≤ 1`, `|Im| ≤ T`,

`#R ≤ C T^ε ( (log (AT))² + Y^{2-2σ} + (AT)K^{1-2σ} + T^{1/3}(T+K)^{2/3} Y^{(2-4σ)/3} )`.

The first summand counts the zeros with `|Im| < (log (AT))²` (at most `2(log(AT))²+1` of them, by
`1`-separation); for the others the detector gives one of its two alternatives, and the remaining
two summands are the two counts. -/
theorem zetaCountCombined (A : ℝ) (hA : 6 ≤ A) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (R.card : ℝ) ≤ C * T ^ ε *
            ((Real.log (A * T)) ^ 2 + Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)
              + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3)
                  * Y ^ ((2 - 4 * σ) / 3)) := by
  sorry

end Work.ZeroDensity.Ingham
