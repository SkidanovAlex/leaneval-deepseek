import Mathlib
import Submission.Work.KMTAreas.A7G.annuliUniformSigns
import Submission.Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin
import Submission.Work.Analysis.Variation.rademacher_menshov_bilinear
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7Lpd.supChainSq
import Submission.Port.Aesm

set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7Rescue

open MeasureTheory Finset
open scoped ENNReal BigOperators

/-!
# The block square function of a walk along the Ionescu--Wainger projections

The uniform-in-signs ("Rademacher") hypothesis `hUS` bounds, in `ℓᵖ`, *every* finitely supported
signed sum of consecutive increments `Π_{≤l,≤-(m₀+n+1)} - Π_{≤l,≤-(m₀+n)}` of the Ionescu--Wainger
projections.  The lemma proved in this file, `blockSqFunWalk`, deduces from it the `ℓᵖ` bound of the
**dyadic block square function** along an arbitrary nondecreasing walk `L : ℕ → ℕ`:

`‖ (∑_{m < 2^{n-i}} ‖Π_{≤l,≤-(m₀+L((m+1)2^i))} f - Π_{≤l,≤-(m₀+L(m2^i))} f‖²)^{1/2} ‖_{ℓᵖ} ≤ C ‖f‖_{ℓᵖ}`,

with a constant `C` free of `l`, `m₀`, `L`, `n`, `i`.

The proof has three ingredients, all valid at every exponent `p > 0` (no convexity is used):

* Khintchine's inequality at an arbitrary positive exponent (lower bound), pointwise on `ℤ`;
* the resulting "uniform signs ⟹ square function" linearisation, which is the engine
  `sqSum_lintegral_le_uniformSigns_pos` below;
* the telescoping identity `P b - P a = ∑_{n ∈ [a,b)} (P (n+1) - P n)`, which exhibits the block
  increment over the walk as a sum of consecutive fine increments with a sign that is constant on
  each block — so that `hUS` applies to the block family itself.
-/

/-! ## The two families of increments -/

/-- The height index of the projection: `Π_{≤l,≤-(m₀+t)}`, written as `kmtProj ρ l (idx m₀ t)`. -/
private def idx (m₀ : ℕ) (t : ℕ) : ℤ := -((m₀ : ℤ) + (t : ℤ))

/-- The consecutive increment `Π_{≤l,≤-(m₀+n+1)} g - Π_{≤l,≤-(m₀+n)} g`, as a function of
`x : ℤ`. -/
private noncomputable def iwStep (ρ : ℝ) (l m₀ : ℕ) (g : ℤ → ℂ) (n : ℕ) : ℤ → ℂ :=
  fun x => Work.KMTContract.kmtProj ρ l (idx m₀ (n + 1)) g x
            - Work.KMTContract.kmtProj ρ l (idx m₀ n) g x

/-- The increment of the projections along a monotone walk `L` over the block
`[L (m * D), L ((m + 1) * D))`. -/
private noncomputable def walkStep (ρ : ℝ) (l m₀ : ℕ) (L : ℕ → ℕ) (D : ℕ) (m : ℕ) (g : ℤ → ℂ) : ℤ → ℂ :=
  fun x => Work.KMTContract.kmtProj ρ l (idx m₀ (L ((m + 1) * D))) g x
            - Work.KMTContract.kmtProj ρ l (idx m₀ (L (m * D))) g x

/-- The block `[L (m * D), L ((m + 1) * D))` of the walk `L`. -/
private def walkBlk (L : ℕ → ℕ) (D : ℕ) (m : ℕ) : Finset ℕ :=
  Finset.Ico (L (m * D)) (L ((m + 1) * D))

/-! ## Khintchine's inequality at an arbitrary positive exponent -/

/-- **Khintchine on the `ℓ²`-size of a finite complex vector, in `ℝ≥0∞` form, at every positive
exponent.**  For every `q > 0` there is `c > 0` such that for every `N` and every `v : Fin N → ℂ`

`(∑ i, ‖v i‖ₑ ^ 2) ^ (q/2) ≤ (c^q)^{-1} (2^N)^{-1} ∑ ε, ‖∑ i, ε_i v i‖ₑ ^ q`,

where `ε` runs over the `2^N` sign choices `Fin N → Bool`.  This is
`Work.KMTAreas.A7.khintchine_sqSum_pointwise` with the hypothesis `1 ≤ q` replaced by `0 < q`,
using the Paley--Zygmund lower Khintchine inequality `khintchine_lower_hilbert_small` of
`Work.Analysis.Variation` for `q ≤ 1`. -/
private theorem khintchine_sqSum_pointwise_pos (q : ℝ) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (v : Fin N → ℂ),
      (∑ i : Fin N, ‖v i‖ₑ ^ (2 : ℝ)) ^ (q / 2)
        ≤ (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
            ∑ ε : Fin N → Bool,
              ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * v i‖ₑ ^ q := by
  obtain ⟨c, hc, hKh⟩ : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (v : Fin N → ℂ),
      c * (∑ i : Fin N, ‖v i‖ ^ (2 : ℕ)) ^ ((1 : ℝ) / 2)
        ≤ ((∑ ε : Fin N → Bool,
            ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * v i‖ ^ q) / (2 : ℝ) ^ N)
          ^ ((1 : ℝ) / q) := by
    by_cases hq1 : 1 ≤ q
    · obtain ⟨c, _C, hc, _hC, hKh⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert q hq1
      refine ⟨c, hc, fun N v => ?_⟩
      simpa only [smul_eq_mul] using (hKh (H := ℂ) N v).1
    · obtain ⟨c, hc, hKh⟩ :=
        Work.Analysis.Variation.khintchine_lower_hilbert_small (H := ℂ) hq
          (le_of_lt (lt_of_not_ge hq1))
      refine ⟨c, hc, fun N v => ?_⟩
      simpa only [smul_eq_mul] using hKh N v
  refine ⟨c, hc, ?_⟩
  intro N v
  set B : ℝ := ∑ i : Fin N, ‖v i‖ ^ (2 : ℕ) with hBdef
  set T : ℝ := ∑ e : Fin N → Bool,
      ‖∑ i : Fin N, (if e i then (1 : ℂ) else -1) * v i‖ ^ q with hTdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  have hkh' : c * B ^ ((1 : ℝ) / 2) ≤ (T / (2 : ℝ) ^ N) ^ (1 / q) := by
    rw [hBdef, hTdef]
    exact hKh N v
  have hmain := Work.KMTAreas.Khintchine.ofReal_rpow_le_inv_mul_inv_mul (p := q) (c := c)
    (A := B ^ ((1 : ℝ) / 2)) (S := T) (n := N) hc hq (Real.rpow_nonneg hBnn _) hTnn hkh'
  have hAq : (B ^ ((1 : ℝ) / 2)) ^ q = B ^ (q / 2) := by
    rw [← Real.rpow_mul hBnn]; congr 1; ring
  have hmain' : ENNReal.ofReal (B ^ (q / 2)) ≤
      (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ENNReal.ofReal T := by
    simpa only [hAq] using hmain
  have hLHS : (∑ i : Fin N, ‖v i‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal B := by
    rw [Work.KMTAreas.Khintchine.sum_enorm_rpow v (by norm_num : (0 : ℝ) < 2), hBdef]
    simp
  have hRHS : (∑ e : Fin N → Bool, ‖∑ i : Fin N, (if e i then (1 : ℂ) else -1) * v i‖ₑ ^ q)
      = ENNReal.ofReal T := by
    rw [Work.KMTAreas.Khintchine.sum_enorm_rpow (fun e : Fin N → Bool =>
      ∑ i : Fin N, (if e i then (1 : ℂ) else -1) * v i) hq, hTdef]
  rw [hLHS, hRHS, ENNReal.ofReal_rpow_of_nonneg hBnn (by positivity : (0 : ℝ) ≤ q / 2)]
  exact hmain'

/-! ## Uniform signs imply the square-function bound, at every positive exponent -/

/-- **The uniform sign bound implies the square-function bound, at every exponent `q > 0`.**

Suppose that for every finite set `U` of indices and every choice of signs `ω : ℕ → Bool` the
signed sum `∑_{n ∈ U} ω n · T n f` obeys the `L^q` bound
`∫ ‖∑_{n ∈ U} ω n T n f‖ₑ^q ≤ M^q ∫ ‖f‖ₑ^q`.  Then the square function `(∑ₙ ‖T n f‖²)^{1/2}`
obeys the same `L^q` bound up to a constant depending only on `q`.

This is `Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin` with the hypothesis `1 < q`
weakened to `0 < q` (the proof uses the pointwise Khintchine inequality only through
`khintchine_sqSum_pointwise_pos`, so the convexity restriction was spurious). -/
private theorem sqSum_lintegral_le_uniformSigns_pos (q : ℝ) (hq : 0 < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ))
      (hmeas : ∀ n (f : ℤ → ℂ), AEMeasurable (T n f) MeasureTheory.Measure.count)
      (M : ℝ) (hM : 0 ≤ M)
      (hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
        MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => enorm (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * T n f x) ^ q)
          ≤ ENNReal.ofReal (M ^ q) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => enorm (f x) ^ q))
      (f : ℤ → ℂ),
      MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (∑' n : ℕ, enorm (T n f x) ^ (2 : ℝ)) ^ (q / 2))
        ≤ ENNReal.ofReal (K * M ^ q) * MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => enorm (f x) ^ q) := by
  obtain ⟨c, hc, hkey⟩ := khintchine_sqSum_pointwise_pos q hq
  have hpq : 0 < q / 2 := by linarith
  have hcpos : 0 < c ^ q := Real.rpow_pos_of_pos hc q
  refine ⟨(c ^ q)⁻¹, by positivity, ?_⟩
  intro T hmeas M hM hT f
  -- ## Step 1: the bound for the truncated square function, uniformly in the truncation `N`
  set Q : ENNReal := ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count with hQdef
  have step1 : ∀ N : ℕ,
      ∫⁻ x : ℤ, (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂Measure.count
        ≤ ENNReal.ofReal ((c ^ q)⁻¹ * M ^ q) * Q := by
    intro N
    let B : (Fin N → Bool) → ℤ → ENNReal :=
      fun ε x => ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x‖ₑ ^ q
    have hBmeas : ∀ ε : Fin N → Bool, AEMeasurable (B ε) Measure.count := by
      intro ε
      have h1 : AEMeasurable (fun x : ℤ =>
          ∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x) Measure.count :=
        Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
          AEMeasurable.const_mul (hmeas (i : ℕ) f) (if ε i then (1 : ℂ) else -1)
      have h2 : AEMeasurable (fun x : ℤ =>
          ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x‖ₑ) Measure.count :=
        AEMeasurable.enorm h1
      exact AEMeasurable.pow_const h2 q
    have hpoint : ∀ x : ℤ,
        (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2)
          ≤ (ENNReal.ofReal (c ^ q))⁻¹ *
              ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ∑ ε : Fin N → Bool, B ε x) := by
      intro x
      have h := hkey N (fun i : Fin N => T (i : ℕ) f x)
      rw [show (∑ i : Fin N, ‖T (i : ℕ) f x‖ₑ ^ (2 : ℝ))
            = ∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ) from
          Fin.sum_univ_eq_sum_range (fun n => ‖T n f x‖ₑ ^ (2 : ℝ)) N] at h
      exact h.trans_eq (mul_assoc _ _ _)
    have hbound : ∀ ε : Fin N → Bool, ∫⁻ x : ℤ, B ε x ∂Measure.count
        ≤ ENNReal.ofReal (M ^ q) * Q := by
      intro ε
      have h := hT (Finset.range N) (fun n => if h : n < N then ε ⟨n, h⟩ else false) f
      have hEq : (fun x : ℤ => ‖∑ n ∈ Finset.range N,
            (if (if h : n < N then ε ⟨n, h⟩ else false) then (1 : ℂ) else -1) * T n f x‖ₑ ^ q)
          = B ε := by
        funext x
        have hsum : (∑ n ∈ Finset.range N,
              (if (if h : n < N then ε ⟨n, h⟩ else false) then (1 : ℂ) else -1) * T n f x)
            = ∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x := by
          rw [← Fin.sum_univ_eq_sum_range (fun n =>
            (if (if h : n < N then ε ⟨n, h⟩ else false) then (1 : ℂ) else -1) * T n f x) N]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi : (if h : (i : ℕ) < N then ε ⟨(i : ℕ), h⟩ else false) = ε i := by
            rw [dif_pos i.isLt]
          rw [hi]
        rw [hsum]
      rw [hEq] at h
      rw [hQdef]
      exact h
    have hcard : ((Fintype.card (Fin N → Bool) : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← ENNReal.ofReal_natCast,
        Nat.cast_pow]
      norm_num
    have hsumconst : (∑ ε : Fin N → Bool, (ENNReal.ofReal (M ^ q) * Q))
        = ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ q) * Q) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have hpowpos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
    have hb1 : (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hpowpos))
    have hb2 : ENNReal.ofReal (c ^ q) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)
    have hb3 : (ENNReal.ofReal (c ^ q))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hb2
    have hmul : ENNReal.ofReal ((c ^ q)⁻¹ * M ^ q)
        = ENNReal.ofReal ((c ^ q)⁻¹) * ENNReal.ofReal (M ^ q) :=
      ENNReal.ofReal_mul (p := (c ^ q)⁻¹) (q := M ^ q) (by positivity)
    have h1 : (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
          (ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ q) * Q))
        = ENNReal.ofReal (M ^ q) * Q := by
      calc (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
            (ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ q) * Q))
          = ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ N)) *
              (ENNReal.ofReal (M ^ q) * Q) := (mul_assoc _ _ _).symm
        _ = 1 * (ENNReal.ofReal (M ^ q) * Q) := by
              rw [ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpowpos))
                ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (M ^ q) * Q := one_mul _
    have hY : (ENNReal.ofReal (c ^ q))⁻¹ *
          ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
            (ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ q) * Q)))
        = ENNReal.ofReal ((c ^ q)⁻¹ * M ^ q) * Q := by
      rw [h1]
      calc (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal (M ^ q) * Q)
          = ((ENNReal.ofReal (c ^ q))⁻¹ * ENNReal.ofReal (M ^ q)) * Q :=
              (mul_assoc _ _ _).symm
        _ = (ENNReal.ofReal ((c ^ q)⁻¹) * ENNReal.ofReal (M ^ q)) * Q := by
              rw [ENNReal.ofReal_inv_of_pos hcpos]
        _ = ENNReal.ofReal ((c ^ q)⁻¹ * M ^ q) * Q := by rw [← hmul]
    calc ∫⁻ x : ℤ, (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂Measure.count
        ≤ ∫⁻ x : ℤ, (ENNReal.ofReal (c ^ q))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ∑ ε : Fin N → Bool, B ε x)
            ∂Measure.count := lintegral_mono hpoint
      _ = (ENNReal.ofReal (c ^ q))⁻¹ *
            ∫⁻ x : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * (∑ ε : Fin N → Bool, B ε x)
            ∂Measure.count := by
          exact lintegral_const_mul' _ _ hb3
      _ = (ENNReal.ofReal (c ^ q))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ∫⁻ x : ℤ, ∑ ε : Fin N → Bool, B ε x
              ∂Measure.count) := by
          rw [lintegral_const_mul' _ _ hb1]
      _ = (ENNReal.ofReal (c ^ q))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
              ∑ ε : Fin N → Bool, ∫⁻ x : ℤ, B ε x ∂Measure.count) := by
          rw [lintegral_finsetSum' Finset.univ (fun ε _ => hBmeas ε)]
      _ ≤ (ENNReal.ofReal (c ^ q))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
              ∑ ε : Fin N → Bool, (ENNReal.ofReal (M ^ q) * Q)) :=
          mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun ε _ => hbound ε) _) _
      _ = ENNReal.ofReal ((c ^ q)⁻¹ * M ^ q) * Q := by
          rw [hsumconst]
          exact hY
  -- ## Step 2: monotone convergence as the truncation goes to infinity
  have hmono : ∀ x : ℤ, Monotone (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2)) := by
    intro x N M hNM
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hpq.le
    · exact Finset.range_subset_range.mpr hNM
    · intro i _ _; exact zero_le
  have haemeas : ∀ N : ℕ, AEMeasurable (fun x : ℤ =>
      (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2)) Measure.count := by
    intro N
    have h1 : AEMeasurable (fun x : ℤ =>
        ∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) Measure.count :=
      Finset.aemeasurable_fun_sum (Finset.range N) fun n _ =>
        AEMeasurable.pow_const (AEMeasurable.enorm (hmeas n f)) (2 : ℝ)
    exact AEMeasurable.pow_const h1 (q / 2)
  have hsup : (fun x : ℤ => (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2))
      = fun x : ℤ => ⨆ N : ℕ, (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) := by
    funext x
    rw [ENNReal.tsum_eq_iSup_nat]
    exact Work.KMTAreas.A7.rpow_iSup_ennreal _ hpq
  rw [hsup]
  rw [lintegral_iSup' haemeas (Filter.Eventually.of_forall (fun x => hmono x))]
  exact iSup_le step1

/-! ## The telescoping identity -/

/-- The telescoping sum: `P b - P a = ∑_{n ∈ [a,b)} (P (n+1) - P n)`. -/
private lemma sum_Ico_sub {A : Type*} [AddCommGroup A] (P : ℕ → A) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (P (n + 1) - P n) = P b - P a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih]
      abel

/-! ## The uniform sign bound for the block family -/

/-- **The uniform sign bound for the walk family.**  Under the hypothesis `hUS` (a uniform-in-signs
bound for the consecutive increments), the *block* increments of the projections along a monotone
walk `L` (blocks of length `L ((m+1) D) - L (m D)`) obey the same uniform-in-signs bound, with the
same constant.

Indeed, the blocks `[L (m D), L ((m+1) D))` of the distinct indices `m ∈ U` are pairwise disjoint,
and each block increment telescopes into the consecutive increments inside it, so any signed sum of
block increments *is* a signed sum of consecutive increments (the sign being constant on each
block). -/
private theorem blockUniformSigns (ρ : ℝ) (p : ENNReal) (hptop : p < ⊤) (Cρ : ℝ)
    (hUS : ∀ (l : ℕ) (m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cρ * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (l m₀ : ℕ) (hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)))
    (L : ℕ → ℕ) (hL : Monotone L) {D : ℕ} (hD : 0 < D) :
    ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L ((m + 1) * D) : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L (m * D) : ℕ) : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cρ * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro U ω f
  -- ## (1) the blocks of distinct indices are pairwise disjoint
  have hdisj : (↑U : Set ℕ).PairwiseDisjoint (walkBlk L D) := by
    intro m hm m' hm' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · show Disjoint (walkBlk L D m) (walkBlk L D m')
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [walkBlk, Finset.mem_Ico] at hn1 hn2
      have h1 : (m + 1) * D ≤ m' * D :=
        Nat.mul_le_mul_right D (Nat.succ_le_of_lt hlt)
      exact absurd (lt_of_lt_of_le hn1.2 (hL h1)) (not_lt.mpr hn2.1)
    · show Disjoint (walkBlk L D m) (walkBlk L D m')
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [walkBlk, Finset.mem_Ico] at hn1 hn2
      have h1 : (m' + 1) * D ≤ m * D :=
        Nat.mul_le_mul_right D (Nat.succ_le_of_lt hlt)
      exact absurd (lt_of_lt_of_le hn2.2 (hL h1)) (not_lt.mpr hn1.1)
  -- ## (2) the sign function on the fine index set
  set ω' : ℕ → Bool := fun n =>
    if h : ∃ m ∈ U, n ∈ walkBlk L D m then ω (Classical.choose h) else true with hω'
  have hω'eq : ∀ m ∈ U, ∀ n ∈ walkBlk L D m, ω' n = ω m := by
    intro m hm n hn
    have hex : ∃ m ∈ U, n ∈ walkBlk L D m := ⟨m, hm, hn⟩
    rw [hω']
    show (if h : ∃ m ∈ U, n ∈ walkBlk L D m then ω (Classical.choose h) else true) = ω m
    rw [dif_pos hex]
    congr 1
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj (Classical.choose_spec hex).1 hm hne))
      (Classical.choose_spec hex).2 hn
  -- ## (3) the sum identity, pointwise in `x`
  have hsum : ∀ x : ℤ,
      (∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L ((m + 1) * D) : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L (m * D) : ℕ) : ℤ))) f x))
      = ∑ n ∈ U.biUnion (walkBlk L D), (if ω' n then (1 : ℂ) else -1) *
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x) := by
    intro x
    calc ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L ((m + 1) * D) : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L (m * D) : ℕ) : ℤ))) f x)
        = ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
            ∑ n ∈ walkBlk L D m, (Work.KMTContract.kmtProj ρ l
                (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          congr 1
          simp only [walkBlk]
          exact (sum_Ico_sub (fun t : ℕ =>
            Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (t : ℤ))) f x) (hL (Nat.mul_le_mul_right D
              (Nat.le_succ m)))).symm
      _ = ∑ m ∈ U, ∑ n ∈ walkBlk L D m, (if ω m then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          exact Finset.mul_sum _ _ _
      _ = ∑ m ∈ U, ∑ n ∈ walkBlk L D m, (if ω' n then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x) := by
          refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
          rw [hω'eq m hm n hn]
      _ = ∑ n ∈ U.biUnion (walkBlk L D), (if ω' n then (1 : ℂ) else -1) *
            (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x) :=
          (Finset.sum_biUnion hdisj).symm
  have hfun : (fun x : ℤ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
        (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L ((m + 1) * D) : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L (m * D) : ℕ) : ℤ))) f x))
      = (fun x : ℤ => ∑ n ∈ U.biUnion (walkBlk L D), (if ω' n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x)) :=
    funext hsum
  rw [hfun]
  exact hUS l m₀ hgood (U.biUnion (walkBlk L D)) ω' f

/-! ## The main theorem -/

theorem blockSqFunWalk (ρ : ℝ) (p : ENNReal) (hptop : p < ⊤) (Cρ : ℝ)
    (hUS : ∀ (l : ℕ) (m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cρ * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      ∀ (L : ℕ → ℕ), Monotone L → ∀ (n i : ℕ), i ≤ n → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
          ((∑ m ∈ Finset.range (2 ^ (n - i)),
              ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L ((m + 1) * 2 ^ i) : ℕ) : ℤ))) f x
                - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((L (m * 2 ^ i) : ℕ) : ℤ))) f x‖ ^ 2)
            ^ (1 / 2 : ℝ)))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  by_cases hp0 : p = 0
  · rw [hp0]
    refine ⟨1, one_pos, ?_⟩
    intro l m₀ hgood L hL n i hin f
    simp [MeasureTheory.AEStronglyMeasurable.of_discrete]
  · obtain ⟨K, hKpos, hK⟩ := sqSum_lintegral_le_uniformSigns_pos p.toReal
      (ENNReal.toReal_pos hp0 (ne_of_lt hptop))
    refine ⟨K ^ (1 / p.toReal) * max Cρ 1, ?_, ?_⟩
    · exact mul_pos (Real.rpow_pos_of_pos hKpos _) (lt_of_lt_of_le one_pos (le_max_right _ _))
    intro l m₀ hgood L hL n i hin f
    set q : ℝ := p.toReal with hqdef
    have hqpos : 0 < q := by rw [hqdef]; exact ENNReal.toReal_pos hp0 (ne_of_lt hptop)
    have hM0 : (0 : ℝ) ≤ max Cρ 1 := le_trans zero_le_one (le_max_right Cρ 1)
    -- the `eLpNorm`/`lintegral` dictionary
    have hint : ∀ h : ℤ → ℂ,
        (∫⁻ x : ℤ, ‖h x‖ₑ ^ q ∂Measure.count)
          = (MeasureTheory.eLpNorm h p MeasureTheory.Measure.count) ^ q := by
      intro h
      rw [MeasureTheory.eLpNorm_eq_eLpNorm' (hf := by pw_aesm) (μ := Measure.count) hp0 (ne_of_lt hptop),
        ← hqdef]
      exact MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := Measure.count) hqpos
    -- the block family and its uniform sign bound
    have hblk := blockUniformSigns ρ p hptop Cρ hUS l m₀ hgood L hL (D := 2 ^ i) (by positivity)
    have hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
        ∫⁻ x : ℤ, ‖∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
            walkStep ρ l m₀ L (2 ^ i) m g x‖ₑ ^ q ∂Measure.count
          ≤ ENNReal.ofReal ((max Cρ 1) ^ q) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ q ∂Measure.count := by
      intro U ω g
      have h1 : MeasureTheory.eLpNorm (fun x : ℤ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
            walkStep ρ l m₀ L (2 ^ i) m g x) p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (max Cρ 1) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count :=
        (hblk U ω g).trans
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
      rw [hint (fun x : ℤ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
        walkStep ρ l m₀ L (2 ^ i) m g x), hint g]
      calc (MeasureTheory.eLpNorm (fun x : ℤ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) *
              walkStep ρ l m₀ L (2 ^ i) m g x) p MeasureTheory.Measure.count) ^ q
          ≤ (ENNReal.ofReal (max Cρ 1) *
              MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) ^ q :=
            ENNReal.rpow_le_rpow h1 hqpos.le
        _ = ENNReal.ofReal ((max Cρ 1) ^ q) *
              (MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) ^ q := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
              ENNReal.ofReal_rpow_of_nonneg hM0 hqpos.le]
    -- apply the engine to the block family
    have hKres := hK (walkStep ρ l m₀ L (2 ^ i))
      (fun m g => (measurable_of_countable (walkStep ρ l m₀ L (2 ^ i) m g)).aemeasurable)
      (max Cρ 1) hM0 hT f
    -- the pointwise comparison of the truncated and the full square function
    have hpoint : ∀ x : ℤ,
        ‖ENNReal.ofReal ((∑ m ∈ Finset.range (2 ^ (n - i)),
            ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ ^ 2) ^ (1 / 2 : ℝ))‖ₑ ^ q
          ≤ (∑' m : ℕ, ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) := by
      intro x
      set B : ℝ := ∑ m ∈ Finset.range (2 ^ (n - i)),
        ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ ^ 2 with hBdef
      have hBnn : 0 ≤ B := by rw [hBdef]; positivity
      have hofB : ENNReal.ofReal B
          = ∑ m ∈ Finset.range (2 ^ (n - i)), ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ₑ ^ (2 : ℝ) := by
        rw [hBdef, ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]
        exact (ENNReal.rpow_natCast _ 2).symm
      rw [enorm_eq_self]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hBnn (1 / 2)) hqpos.le]
      rw [← Real.rpow_mul hBnn]
      rw [show (1 / 2 : ℝ) * q = q / 2 by ring]
      rw [← ENNReal.ofReal_rpow_of_nonneg hBnn (by positivity : (0 : ℝ) ≤ q / 2)]
      rw [hofB]
      exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum (Finset.range (2 ^ (n - i))))
        (by positivity)
    -- the assembly
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 (ne_of_lt hptop), ← hqdef]
    have hmain : (∫⁻ x : ℤ, ‖ENNReal.ofReal ((∑ m ∈ Finset.range (2 ^ (n - i)),
            ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ ^ 2) ^ (1 / 2 : ℝ))‖ₑ ^ q ∂Measure.count)
          ^ (1 / q)
        ≤ ENNReal.ofReal (K ^ (1 / q) * max Cρ 1) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      have harith : (K * (max Cρ 1) ^ q) ^ (1 / q) = K ^ (1 / q) * max Cρ 1 := by
        rw [Real.mul_rpow hKpos.le (Real.rpow_nonneg hM0 q),
          ← Real.rpow_mul hM0 q (1 / q), mul_one_div_cancel hqpos.ne', Real.rpow_one]
      calc (∫⁻ x : ℤ, ‖ENNReal.ofReal ((∑ m ∈ Finset.range (2 ^ (n - i)),
              ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ ^ 2) ^ (1 / 2 : ℝ))‖ₑ ^ q ∂Measure.count)
            ^ (1 / q)
          ≤ (∫⁻ x : ℤ, (∑' m : ℕ, ‖walkStep ρ l m₀ L (2 ^ i) m f x‖ₑ ^ (2 : ℝ)) ^ (q / 2)
              ∂Measure.count) ^ (1 / q) :=
            ENNReal.rpow_le_rpow (lintegral_mono hpoint) (by positivity)
        _ ≤ (ENNReal.ofReal (K * (max Cρ 1) ^ q) *
              ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count) ^ (1 / q) :=
            ENNReal.rpow_le_rpow hKres (by positivity)
        _ = ENNReal.ofReal ((K * (max Cρ 1) ^ q) ^ (1 / q)) *
              (∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count) ^ (1 / q) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        _ = ENNReal.ofReal (K ^ (1 / q) * max Cρ 1) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
            rw [harith, MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (μ := Measure.count)
                hp0 (ne_of_lt hptop), ← hqdef]
    exact hmain

end Work.KMTAreas.A7Rescue
