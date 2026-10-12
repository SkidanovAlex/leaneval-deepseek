import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselExcited
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotRankOneG
import Submission.Work.MB.boxSlotSum_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.slotBoxT0AnnComm` — the excited-number row commutes
with the box annihilation

For an orthonormal, measurable, everywhere bounded family `e : Fin m → Sp → ℂ` supported in the
corpus box `boxL ℓ`, a superposition `w` of the modes with `w 0 = 0` (i.e. `η_w` orthogonal to the
condensate mode `e 0`), and a state `Θ` on `Xn (D+1)`,

    `boxSlotSum e (boxT0 m) (boxAnnOf e w D Θ)
        = boxAnnOf e w D (boxSlotSum e (boxT0 m) Θ) − boxAnnOf e w D Θ`,

which is the first-quantised form of the second-quantised relation `[N_ex, a(η_w)] = −a(η_w)`
for `η_w ⊥ e_0`.  Here `boxSlotSum e (boxT0 m) = Σ_{j} (1 − |e_0⟩⟨e_0|)^{(j)}` is the
excited-number operator `N_ex` in slot form, and `boxAnnOf e w D` is the box annihilation of `η_w`.

## Structure of the proof

* `slotJ_apply`-expansions of both sides; the only analytic input is the Fubini swap
  `swap_cons_integral` (the two integrations — over the *updated* coordinate `a` and over the
  *inserted* coordinate `z` — are exchanged), together with the pointwise identities
  `update_cons_succ` / `update_cons_zero` relating `Fin.cons` and `Function.update`.
* the `j = 0` slot of the annihilation is `boxAnnOf e w D Θ` itself, by orthonormality
  (`horth`) and `w 0 = 0`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Elementary `Fin.cons` / `Function.update` algebra -/

/-- `star` on the reals inside `ℂ` is the identity. -/
private lemma star_ofReal_eq (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := Complex.conj_ofReal r

/-- Conjugation preserves the support. -/
private lemma support_star_subset {f : Ω → ℂ} {s : Set Ω} (h : Function.support f ⊆ s) :
    Function.support (fun z => star (f z)) ⊆ s :=
  fun z hz => h (Function.mem_support.mpr (fun hf => hz (by show star (f z) = 0; rw [hf, star_zero])))

/-- The insertion `z ↦ Fin.cons z y` is measurable. -/
private lemma measurable_cons_fixed {d : ℕ} (y : Xn d) :
    Measurable (fun z : Ω => (Fin.cons z y : Xn (d + 1))) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  cases i using Fin.cases with
  | zero =>
      have h : (fun z : Ω => (Fin.cons z y : Xn (d + 1)) 0) = fun z : Ω => z := by
        funext z; rw [Fin.cons_zero]
      rw [h]
      exact measurable_id
  | succ k => simpa only [Fin.cons_succ] using measurable_const

/-- The map `(a,z) ↦ Fin.cons z (Function.update x j a)` is measurable. -/
private lemma measurable_cons_update {d : ℕ} (j : Fin d) (x : Xn d) :
    Measurable (fun p : Ω × Ω => (Fin.cons p.2 (Function.update x j p.1) : Xn (d + 1))) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  cases i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using measurable_snd
  | succ k =>
      have h : (fun p : Ω × Ω =>
            (Fin.cons p.2 (Function.update x j p.1) : Xn (d + 1)) k.succ)
          = fun p : Ω × Ω => Function.update x j p.1 k := by
        funext p; rw [Fin.cons_succ]
      rw [h]
      by_cases hk : k = j
      · have h2 : (fun p : Ω × Ω => Function.update x j p.1 k) = fun p : Ω × Ω => p.1 := by
          funext p; rw [Function.update_apply, if_pos hk]
        rw [h2]; exact measurable_fst
      · have h2 : (fun p : Ω × Ω => Function.update x j p.1 k) = fun _ : Ω × Ω => x k := by
          funext p; rw [Function.update_apply, if_neg hk]
        rw [h2]; exact measurable_const

/-- The map `(z,a) ↦ Fin.cons z (Function.update x j a)` is measurable. -/
private lemma measurable_cons_update' {d : ℕ} (j : Fin d) (x : Xn d) :
    Measurable (fun p : Ω × Ω => (Fin.cons p.1 (Function.update x j p.2) : Xn (d + 1))) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  cases i using Fin.cases with
  | zero => simpa only [Fin.cons_zero] using measurable_fst
  | succ k =>
      have h : (fun p : Ω × Ω =>
            (Fin.cons p.1 (Function.update x j p.2) : Xn (d + 1)) k.succ)
          = fun p : Ω × Ω => Function.update x j p.2 k := by
        funext p; rw [Fin.cons_succ]
      rw [h]
      by_cases hk : k = j
      · have h2 : (fun p : Ω × Ω => Function.update x j p.2 k) = fun p : Ω × Ω => p.2 := by
          funext p; rw [Function.update_apply, if_pos hk]
        rw [h2]; exact measurable_snd
      · have h2 : (fun p : Ω × Ω => Function.update x j p.2 k) = fun _ : Ω × Ω => x k := by
          funext p; rw [Function.update_apply, if_neg hk]
        rw [h2]; exact measurable_const

/-- Overwriting the `0`-slot of `cons z x` by `z'` is `cons z' x`. -/
private lemma update_cons_zero {d : ℕ} (x : Xn d) (z z' : Ω) :
    Function.update (Fin.cons z x : Xn (d + 1)) 0 z' = (Fin.cons z' x : Xn (d + 1)) := by
  funext i
  cases i using Fin.cases with
  | zero => rw [Function.update_apply]; simp
  | succ k => rw [Function.update_apply, if_neg (Fin.succ_ne_zero k)]; simp

/-- Overwriting the `(j+1)`-st slot of `cons z x` by `a` is `cons z (update x j a)`. -/
private lemma update_cons_succ {d : ℕ} (j : Fin d) (x : Xn d) (z a : Ω) :
    Function.update (Fin.cons z x : Xn (d + 1)) (Fin.succ j) a
      = (Fin.cons z (Function.update x j a) : Xn (d + 1)) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      have h1 : (Function.update (Fin.cons z x : Xn (d + 1)) (Fin.succ j) a) 0 = z := by
        rw [Function.update_apply, if_neg (Ne.symm (Fin.succ_ne_zero j)), Fin.cons_zero]
      rw [h1, Fin.cons_zero]
  | succ k =>
      have h1 : (Function.update (Fin.cons z x : Xn (d + 1)) (Fin.succ j) a) (Fin.succ k)
          = if Fin.succ k = Fin.succ j then a else x k := by
        rw [Function.update_apply, Fin.cons_succ]
      have h2 : (Fin.cons z (Function.update x j a) : Xn (d + 1)) (Fin.succ k)
          = if k = j then a else x k := by
        rw [Fin.cons_succ, Function.update_apply]
      rw [h1, h2]
      by_cases hk : k = j
      · rw [if_pos hk, if_pos (by rw [hk])]
      · rw [if_neg hk, if_neg (fun h => hk (Fin.succ_inj.mp h))]

/-! ## 1. Integrability at the weak mode bundle -/

/-- The integrand `star (etaOf e w ·) * f` is integrable whenever `f` is measurable and bounded:
the factor `etaOf e w` is bounded and box-supported, and `boxL ℓ` has finite measure. -/
private lemma integrable_star_etaOf_mul {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {f : Ω → ℂ} (hfm : Measurable f) (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C) :
    Integrable (fun z : Ω => star (etaOf e w z) * f z) := by
  obtain ⟨Bw, hBwnn, hBw⟩ := Work.MB.etaOf_weak_bound hbdd w
  obtain ⟨Cf, hCf⟩ := hfb
  refine Work.MB.integrable_of_bdd_of_support (C := Bw * max Cf 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    (((Complex.continuous_conj.measurable.comp
      (Work.MB.etaOf_weak_measurable hmeas w)).mul hfm)).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, norm_star]
    exact mul_le_mul (hBw z) ((hCf z).trans (le_max_left _ _)) (norm_nonneg _) hBwnn
  · intro z hz
    have hzv : etaOf e w z = 0 :=
      Function.notMem_support.mp (fun h => hz (Work.MB.etaOf_weak_support hsupp w h))
    rw [hzv, star_zero, zero_mul]

/-- The `Fin.cons`-integrand against `etaOf e w` is integrable. -/
private lemma integrable_etaOf_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (y : Xn d) :
    Integrable (fun z : Ω => star (etaOf e w z) * Θ (Fin.cons z y)) :=
  integrable_star_etaOf_mul hmeas hbdd hsupp w (hΘm.comp (measurable_cons_fixed y))
    (by obtain ⟨C, hC⟩ := hΘb; exact ⟨C, fun z => hC (Fin.cons z y)⟩)

/-- The `Fin.cons`-integrand against a single mode is integrable. -/
private lemma integrable_mode_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l : Fin m) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (y : Xn d) :
    Integrable (fun z : Ω => star (e l z) * Θ (Fin.cons z y)) := by
  obtain ⟨Cl, hCl⟩ := hbdd l
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (C := max Cl 0 * max CΘ 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    (((Complex.continuous_conj.measurable.comp (hmeas l)).mul
      (hΘm.comp (measurable_cons_fixed y)))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCl z).trans (le_max_left _ _)) ((hCΘ _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hzl : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    rw [hzl, star_zero, zero_mul]

/-- A product of two modes is integrable at the weak bundle. -/
private lemma integrable_mode_mul_mode {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l l' : Fin m) :
    Integrable (fun z : Ω => star (e l z) * e l' z) := by
  obtain ⟨Cl, hCl⟩ := hbdd l
  obtain ⟨Cl', hCl'⟩ := hbdd l'
  refine Work.MB.integrable_of_bdd_of_support (C := max Cl 0 * max Cl' 0)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    (((Complex.continuous_conj.measurable.comp (hmeas l)).mul (hmeas l'))).aestronglyMeasurable ?_ ?_
  · intro z
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCl z).trans (le_max_left _ _)) ((hCl' z).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro z hz
    have hzl : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
    rw [hzl, star_zero, zero_mul]

/-! ## 2. `boxAnnOf` is linear in the state -/

/-- `boxAnnOf` is additive in the state. -/
private lemma boxAnnOf_sub {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Ψ Φ : Xn (d + 1) → ℂ}
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΦm : Measurable Φ) (hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) :
    boxAnnOf e w d (Ψ - Φ) = boxAnnOf e w d Ψ - boxAnnOf e w d Φ := by
  funext y
  have h1 := integrable_etaOf_cons hmeas hbdd hsupp w hΨm hΨb y
  have h2 := integrable_etaOf_cons hmeas hbdd hsupp w hΦm hΦb y
  have hI : (∫ z : Ω, star (etaOf e w z) * (Ψ (Fin.cons z y) - Φ (Fin.cons z y)))
      = ∫ z : Ω, (star (etaOf e w z) * Ψ (Fin.cons z y)
          - star (etaOf e w z) * Φ (Fin.cons z y)) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      show star (etaOf e w z) * (Ψ (Fin.cons z y) - Φ (Fin.cons z y))
          = star (etaOf e w z) * Ψ (Fin.cons z y) - star (etaOf e w z) * Φ (Fin.cons z y)
      rw [mul_sub]))
  simp only [boxAnnOf, Pi.sub_apply, starRingEnd_apply]
  rw [hI, MeasureTheory.integral_sub h1 h2]
  ring

/-- `boxAnnOf` is additive over a finite sum of states. -/
private lemma boxAnnOf_sum {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {n : ℕ} (Φ : Fin n → Xn (d + 1) → ℂ)
    (hΦm : ∀ k, Measurable (Φ k)) (hΦb : ∀ k, ∃ C : ℝ, ∀ x, ‖Φ k x‖ ≤ C) :
    boxAnnOf e w d (∑ k : Fin n, Φ k) = ∑ k : Fin n, boxAnnOf e w d (Φ k) := by
  funext y
  have hInt : ∀ k : Fin n, Integrable (fun z : Ω => star (etaOf e w z) * Φ k (Fin.cons z y)) :=
    fun k => integrable_etaOf_cons hmeas hbdd hsupp w (hΦm k) (hΦb k) y
  have hI : (∫ z : Ω, star (etaOf e w z) * (∑ k : Fin n, Φ k (Fin.cons z y)))
      = ∫ z : Ω, ∑ k : Fin n, star (etaOf e w z) * Φ k (Fin.cons z y) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      show star (etaOf e w z) * (∑ k : Fin n, Φ k (Fin.cons z y))
          = ∑ k : Fin n, star (etaOf e w z) * Φ k (Fin.cons z y)
      rw [Finset.mul_sum]))
  simp only [boxAnnOf, Finset.sum_apply, starRingEnd_apply]
  rw [hI, MeasureTheory.integral_finsetSum Finset.univ (fun k _ => hInt k), Finset.mul_sum]

/-- Pull a finite sum out of the integral against `star (etaOf e w ·)`. -/
private lemma integral_star_etaOf_mul_sum {m n : ℕ} {e : Fin m → Ω → ℂ}
    (w : Fin m → ℝ) (F : Fin n → Ω → ℂ)
    (hF : ∀ k, Integrable (fun z : Ω => star (etaOf e w z) * F k z)) :
    (∫ z : Ω, star (etaOf e w z) * ∑ k : Fin n, F k z)
      = ∑ k : Fin n, ∫ z : Ω, star (etaOf e w z) * F k z := by
  have hI : (∫ z : Ω, star (etaOf e w z) * ∑ k : Fin n, F k z)
      = ∫ z : Ω, ∑ k : Fin n, star (etaOf e w z) * F k z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by
      show star (etaOf e w z) * (∑ k : Fin n, F k z)
          = ∑ k : Fin n, star (etaOf e w z) * F k z
      rw [Finset.mul_sum]))
  rw [hI]
  exact MeasureTheory.integral_finsetSum Finset.univ (fun k _ => hF k)

/-! ## 3. The Fubini swap -/

/-- The joint kernel `g a · star (etaOf e w z) · Θ (cons z (update x j a))` is product-integrable
(the modes and `g` are bounded and box-supported, and the box has finite measure). -/
private lemma integrable_prod_cons_kernel {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    {g : Ω → ℂ} (hgm : Measurable g) (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hgsupp : Function.support g ⊆ Work.BoseK15.corpusBox.boxL ℓ) (j : Fin d) (x : Xn d) :
    Integrable (fun p : Ω × Ω =>
      g p.1 * (star (etaOf e w p.2) * Θ (Fin.cons p.2 (Function.update x j p.1))))
      (volume.prod volume) := by
  obtain ⟨Cg, hCg⟩ := hgb
  obtain ⟨Bw, hBwnn, hBw⟩ := Work.MB.etaOf_weak_bound hbdd w
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support
    (S := Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
    (C := max Cg 0 * (Bw * max CΘ 0))
    ((Work.BoseK15.corpusBox.boxL_measurableSet ℓ).prod
      (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)) ?_ ?_ ?_ ?_
  · rw [MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_ne_top (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  · exact ((hgm.comp measurable_fst).mul
      (((Complex.continuous_conj.measurable.comp
        ((Work.MB.etaOf_weak_measurable hmeas w).comp measurable_snd)).mul
        (hΘm.comp (measurable_cons_update j x))))).aestronglyMeasurable
  · intro p
    rw [norm_mul]
    refine mul_le_mul ((hCg p.1).trans (le_max_left _ _)) ?_ (norm_nonneg _)
      (le_max_right _ _)
    rw [norm_mul, norm_star]
    exact mul_le_mul (hBw p.2) ((hCΘ _).trans (le_max_left _ _))
      (norm_nonneg _) hBwnn
  · intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with h1 | h2
    · rw [Function.notMem_support.mp (fun h => h1 (hgsupp h)), zero_mul]
    · rw [Function.notMem_support.mp (fun h => h2 (Work.MB.etaOf_weak_support hsupp w h)),
        star_zero, zero_mul, mul_zero]

/-- **The `cons` Fubini swap**: exchanging the integration over the updated coordinate `a` and over
the inserted coordinate `z`. -/
private lemma swap_cons_integral {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    {g : Ω → ℂ} (hgm : Measurable g) (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hgsupp : Function.support g ⊆ Work.BoseK15.corpusBox.boxL ℓ) (j : Fin d) (x : Xn d) :
    (∫ a : Ω, g a * (∫ z : Ω, star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a))))
      = ∫ z : Ω, star (etaOf e w z) *
          (∫ a : Ω, g a * Θ (Fin.cons z (Function.update x j a))) := by
  have hprod := integrable_prod_cons_kernel hmeas hbdd hsupp w hΘm hΘb hgm hgb hgsupp j x
  have hL : (∫ a : Ω, g a * (∫ z : Ω, star (etaOf e w z) *
        Θ (Fin.cons z (Function.update x j a))))
      = ∫ a : Ω, ∫ z : Ω,
          g a * (star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    exact (MeasureTheory.integral_const_mul (g a)
      (fun z : Ω => star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a)))).symm
  have hR : (∫ z : Ω, star (etaOf e w z) *
        (∫ a : Ω, g a * Θ (Fin.cons z (Function.update x j a))))
      = ∫ z : Ω, ∫ a : Ω,
          g a * (star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show star (etaOf e w z) * (∫ a : Ω, g a * Θ (Fin.cons z (Function.update x j a)))
        = ∫ a : Ω, g a * (star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a)))
    rw [show (∫ a : Ω, g a * (star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a))))
        = ∫ a : Ω, star (etaOf e w z) * (g a * Θ (Fin.cons z (Function.update x j a))) from
      integral_congr_ae (Filter.Eventually.of_forall (fun a => by
        show g a * (star (etaOf e w z) * Θ (Fin.cons z (Function.update x j a)))
            = star (etaOf e w z) * (g a * Θ (Fin.cons z (Function.update x j a)))
        ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hL, hR]
  exact MeasureTheory.integral_integral_swap hprod

/-! ## 4. The transposed product integrability -/

/-- The transposed joint kernel `star (etaOf e w z) · (star (e l' a) · Θ (cons z (update x j a)))`
is product-integrable. -/
private lemma integrable_prod_cons_etaOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (l' : Fin m) (j : Fin d) (x : Xn d) :
    Integrable (fun p : Ω × Ω =>
      star (etaOf e w p.1) * (star (e l' p.2) * Θ (Fin.cons p.1 (Function.update x j p.2))))
      (volume.prod volume) := by
  obtain ⟨Cl', hCl'⟩ := hbdd l'
  obtain ⟨Bw, hBwnn, hBw⟩ := Work.MB.etaOf_weak_bound hbdd w
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support
    (S := Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
    (C := Bw * (max Cl' 0 * max CΘ 0))
    ((Work.BoseK15.corpusBox.boxL_measurableSet ℓ).prod
      (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)) ?_ ?_ ?_ ?_
  · rw [MeasureTheory.Measure.prod_prod]
    exact ENNReal.mul_ne_top (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  · have hm1 : Measurable (fun p : Ω × Ω => star (etaOf e w p.1)) :=
      Complex.continuous_conj.measurable.comp
        ((Work.MB.etaOf_weak_measurable hmeas w).comp measurable_fst)
    have hm2 : Measurable (fun p : Ω × Ω => star (e l' p.2)) :=
      Complex.continuous_conj.measurable.comp ((hmeas l').comp measurable_snd)
    have hm3 : Measurable (fun p : Ω × Ω => Θ (Fin.cons p.1 (Function.update x j p.2))) :=
      hΘm.comp (measurable_cons_update' j x)
    exact (hm1.mul (hm2.mul hm3)).aestronglyMeasurable
  · intro p
    rw [norm_mul, norm_mul, norm_star, norm_star]
    refine mul_le_mul (hBw p.1) ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hBwnn
    exact mul_le_mul ((hCl' p.2).trans (le_max_left _ _)) ((hCΘ _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with h1 | h2
    · rw [Function.notMem_support.mp (fun h => h1 (Work.MB.etaOf_weak_support hsupp w h)),
        star_zero, zero_mul]
    · rw [Function.notMem_support.mp (fun h => h2 (hsupp l' h)), star_zero, zero_mul, mul_zero]

/-- `star (etaOf e w ·) · ∫_a star (e l' a) · Θ (cons · (update x j a))` is integrable. -/
private lemma integrable_etaOf_mul_consIntegral {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (l' : Fin m) (j : Fin d) (x : Xn d) :
    Integrable (fun z : Ω => star (etaOf e w z) *
      (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a)))) := by
  have hprod := integrable_prod_cons_etaOf hmeas hbdd hsupp w hΘm hΘb l' j x
  refine (hprod.integral_prod_left).congr (Filter.Eventually.of_forall (fun z => ?_))
  exact MeasureTheory.integral_const_mul (star (etaOf e w z))
    (fun a : Ω => star (e l' a) * Θ (Fin.cons z (Function.update x j a)))

/-! ## 5. The per-mode Fubini identity and the pointwise expansion of a slot -/

/-- **The per-mode Fubini identity**: `∫_a star (e l' a) · (boxAnnOf e w d Θ)(update x j a)` is the
`z`-integral of the swapped kernel. -/
private lemma int_mode_boxAnnOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (l' : Fin m) (j : Fin d) (x : Xn d) :
    (∫ a : Ω, star (e l' a) * boxAnnOf e w d Θ (Function.update x j a))
      = (Real.sqrt ((d : ℝ) + 1) : ℂ) * ∫ z : Ω, star (etaOf e w z) *
          (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))) := by
  obtain ⟨Cl', hCl'⟩ := hbdd l'
  have h1 : (fun a : Ω => star (e l' a) * boxAnnOf e w d Θ (Function.update x j a))
      = fun a : Ω => (Real.sqrt ((d : ℝ) + 1) : ℂ) *
          (star (e l' a) * ∫ z : Ω, star (etaOf e w z) *
            Θ (Fin.cons z (Function.update x j a))) := by
    funext a
    simp only [boxAnnOf, starRingEnd_apply]
    ring
  rw [h1, MeasureTheory.integral_const_mul]
  exact congrArg (fun t => (Real.sqrt ((d : ℝ) + 1) : ℂ) * t)
    (swap_cons_integral hmeas hbdd hsupp w hΘm hΘb
      (Complex.continuous_conj.measurable.comp (hmeas l'))
      ⟨Cl', fun a => by
        simp only [Function.comp_apply, Complex.norm_conj]
        exact hCl' a⟩
      (support_star_subset (hsupp l')) j x)

/-- The value of the `(j+1)`-st slot at `Fin.cons z x`, in the form used by the assembly. -/
private lemma slotJ_cons_succ_apply {m d : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Xn (d + 1) → ℂ} (j : Fin d) (x : Xn d) (z : Ω) :
    slotJ e T (Fin.succ j) Θ (Fin.cons z x)
      = ∑ l : Fin m, ∑ l' : Fin m, ((T (Work.BoseB4.evec m l')) l : ℂ) *
          (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))) := by
  rw [slotJ_apply]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
  have h1 : (Fin.cons z x : Xn (d + 1)) (Fin.succ j) = x j := by simp
  have h2 : (∫ a : Ω, star (e l' a) * Θ (Function.update (Fin.cons z x) (Fin.succ j) a))
      = ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    show star (e l' a) * Θ (Function.update (Fin.cons z x : Xn (d + 1)) (Fin.succ j) a)
        = star (e l' a) * Θ (Fin.cons z (Function.update x j a))
    rw [update_cons_succ]
  rw [h1, h2]

/-! ## 6. The single-slot interchange -/

/-- **The `j`-th slot of the annihilation is the annihilation of the `(j+1)`-st slot.** -/
private lemma slotJ_boxAnnOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (j : Fin d) :
    slotJ e T j (boxAnnOf e w d Θ) = boxAnnOf e w d (slotJ e T (Fin.succ j) Θ) := by
  funext x
  have hbase : ∀ l l' : Fin m, Integrable (fun z : Ω => star (etaOf e w z) *
      (((T (Work.BoseB4.evec m l')) l : ℂ) *
        (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))) := by
    intro l l'
    refine ((integrable_etaOf_mul_consIntegral hmeas hbdd hsupp w hΘm hΘb l' j x).const_mul
      (((T (Work.BoseB4.evec m l')) l : ℂ) * e l (x j))).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      show (((T (Work.BoseB4.evec m l')) l : ℂ) * e l (x j)) *
            (star (etaOf e w z) *
              (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))
          = star (etaOf e w z) *
            (((T (Work.BoseB4.evec m l')) l : ℂ) *
              (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))
      ring)
  have hL : slotJ e T j (boxAnnOf e w d Θ) x
      = ∑ l : Fin m, ∑ l' : Fin m, ((T (Work.BoseB4.evec m l')) l : ℂ) *
          (e l (x j) * ((Real.sqrt ((d : ℝ) + 1) : ℂ) * ∫ z : Ω, star (etaOf e w z) *
            (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))) := by
    rw [slotJ_apply]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
    rw [int_mode_boxAnnOf hmeas hbdd hsupp w hΘm hΘb l' j x]
  have hIntOuter : ∀ l : Fin m, Integrable (fun z : Ω => star (etaOf e w z) *
      ∑ l' : Fin m, (((T (Work.BoseB4.evec m l')) l : ℂ) *
        (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))) := by
    intro l
    refine (integrable_finsetSum Finset.univ (fun l' _ => hbase l l')).congr
      (Filter.Eventually.of_forall (fun z => ?_))
    show (∑ l' : Fin m, star (etaOf e w z) *
          (((T (Work.BoseB4.evec m l')) l : ℂ) *
            (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a)))))
        = star (etaOf e w z) * ∑ l' : Fin m,
            (((T (Work.BoseB4.evec m l')) l : ℂ) *
              (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))
    rw [Finset.mul_sum]
  have hR : boxAnnOf e w d (slotJ e T (Fin.succ j) Θ) x
      = ∑ l : Fin m, ∑ l' : Fin m, ((T (Work.BoseB4.evec m l')) l : ℂ) *
          (e l (x j) * ((Real.sqrt ((d : ℝ) + 1) : ℂ) * ∫ z : Ω, star (etaOf e w z) *
            (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))) := by
    rw [boxAnnOf]
    simp only [starRingEnd_apply]
    rw [show (∫ z : Ω, star (etaOf e w z) * (slotJ e T (Fin.succ j) Θ) (Fin.cons z x))
        = ∫ z : Ω, star (etaOf e w z) * ∑ l : Fin m, ∑ l' : Fin m,
            (((T (Work.BoseB4.evec m l')) l : ℂ) *
              (e l (x j) * ∫ a : Ω, star (e l' a) *
                Θ (Fin.cons z (Function.update x j a)))) from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        show star (etaOf e w z) * (slotJ e T (Fin.succ j) Θ) (Fin.cons z x)
            = star (etaOf e w z) * ∑ l : Fin m, ∑ l' : Fin m,
                (((T (Work.BoseB4.evec m l')) l : ℂ) *
                  (e l (x j) * ∫ a : Ω, star (e l' a) *
                    Θ (Fin.cons z (Function.update x j a))))
        rw [slotJ_cons_succ_apply (e := e) (T := T) (j := j) (x := x) (z := z)]))]
    have hstep1 : (∫ z : Ω, star (etaOf e w z) * ∑ l : Fin m, ∑ l' : Fin m,
          (((T (Work.BoseB4.evec m l')) l : ℂ) *
            (e l (x j) * ∫ a : Ω, star (e l' a) *
              Θ (Fin.cons z (Function.update x j a)))))
        = ∑ l : Fin m, ∫ z : Ω, star (etaOf e w z) * ∑ l' : Fin m,
            (((T (Work.BoseB4.evec m l')) l : ℂ) *
              (e l (x j) * ∫ a : Ω, star (e l' a) *
                Θ (Fin.cons z (Function.update x j a)))) :=
      integral_star_etaOf_mul_sum w _ hIntOuter
    rw [hstep1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hstep2 : (∫ z : Ω, star (etaOf e w z) * ∑ l' : Fin m,
          (((T (Work.BoseB4.evec m l')) l : ℂ) *
            (e l (x j) * ∫ a : Ω, star (e l' a) *
              Θ (Fin.cons z (Function.update x j a)))))
        = ∑ l' : Fin m, ∫ z : Ω, star (etaOf e w z) *
            (((T (Work.BoseB4.evec m l')) l : ℂ) *
              (e l (x j) * ∫ a : Ω, star (e l' a) *
                Θ (Fin.cons z (Function.update x j a)))) :=
      integral_star_etaOf_mul_sum w _ (fun l' => hbase l l')
    rw [hstep2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    have hI : (∫ z : Ω, star (etaOf e w z) * (((T (Work.BoseB4.evec m l')) l : ℂ) *
          (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a)))))
        = ∫ z : Ω, (((T (Work.BoseB4.evec m l')) l : ℂ) * e l (x j)) *
            (star (etaOf e w z) *
              (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a)))) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        show star (etaOf e w z) * (((T (Work.BoseB4.evec m l')) l : ℂ) *
              (e l (x j) * ∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))
            = (((T (Work.BoseB4.evec m l')) l : ℂ) * e l (x j)) *
              (star (etaOf e w z) *
                (∫ a : Ω, star (e l' a) * Θ (Fin.cons z (Function.update x j a))))
        ring))
    rw [hI, MeasureTheory.integral_const_mul]
    ring
  rw [hL, hR]

/-! ## 7. The `j = 0` slot of the excited-number operator -/

/-- **The pairing with `η_w`**: `∫ b, star (η_w b) · e l b = w l`. -/
private lemma integral_star_etaOf_mul_mode {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (w : Fin m → ℝ) (l : Fin m) :
    (∫ b : Ω, star (etaOf e w b) * e l b) = (w l : ℂ) := by
  have hfun : (fun b : Ω => star (etaOf e w b) * e l b)
      = fun b : Ω => ∑ l'', (w l'' : ℂ) * (star (e l'' b) * e l b) := by
    funext b
    simp only [etaOf, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [star_mul', star_ofReal_eq]
    ring
  rw [hfun, MeasureTheory.integral_finsetSum Finset.univ (fun l'' _ =>
      (integrable_mode_mul_mode hmeas hbdd hsupp l'' l).const_mul _)]
  rw [Finset.sum_eq_single l]
  · rw [MeasureTheory.integral_const_mul, horth l l]; simp
  · intro l'' _ hl''
    rw [MeasureTheory.integral_const_mul, horth l'' l, if_neg hl'', mul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- `∫ b, star (η_w b) · Θ (cons b x) = Σ_l w_l ∫ a, star (e l a) · Θ (cons a x)`. -/
private lemma integral_star_etaOf_mul_Theta_cons {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (x : Xn d) :
    (∫ b : Ω, star (etaOf e w b) * Θ (Fin.cons b x))
      = ∑ l : Fin m, (w l : ℂ) * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x)) := by
  have hfun : (fun b : Ω => star (etaOf e w b) * Θ (Fin.cons b x))
      = fun b : Ω => ∑ l, (w l : ℂ) * (star (e l b) * Θ (Fin.cons b x)) := by
    funext b
    simp only [etaOf, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [star_mul', star_ofReal_eq]
    ring
  rw [hfun, MeasureTheory.integral_finsetSum Finset.univ (fun l _ =>
      (integrable_mode_cons hmeas hbdd hsupp l hΘm hΘb x).const_mul _)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- The integrability of the `j = 0` summands. -/
private lemma integrable_star_etaOf_mul_mode_const {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (l : Fin m) (C : ℂ) :
    Integrable (fun b : Ω => star (etaOf e w b) * (e l b * C)) := by
  obtain ⟨Cl, hCl⟩ := hbdd l
  refine integrable_star_etaOf_mul hmeas hbdd hsupp w ((hmeas l).mul measurable_const)
    ⟨max Cl 0 * ‖C‖, fun b => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hCl b).trans (le_max_left _ _)) le_rfl (norm_nonneg _) (le_max_right _ _)

/-- **The `j = 0` slot of the excited-number operator, integrated against `η_w`.** -/
private lemma integral_star_etaOf_mul_slotJ0 {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {w : Fin m → ℝ} (h0 : w 0 = 0) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (x : Xn d) :
    (∫ b : Ω, star (etaOf e w b) * (slotJ e (Work.BoseBoxFock.boxT0 m) 0 Θ) (Fin.cons b x))
      = ∑ l : Fin m, (w l : ℂ) * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x)) := by
  have hfun : (fun b : Ω => star (etaOf e w b) * (slotJ e (Work.BoseBoxFock.boxT0 m) 0 Θ)
        (Fin.cons b x))
      = fun b : Ω => ∑ l ∈ Finset.univ.erase (0 : Fin m),
          star (etaOf e w b) * (e l b * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x))) := by
    funext b
    simp only [slotJ_boxT0, Fin.cons_zero, update_cons_zero]
    rw [Finset.mul_sum]
  rw [hfun, MeasureTheory.integral_finsetSum _ (fun l _ =>
      integrable_star_etaOf_mul_mode_const hmeas hbdd hsupp w l _)]
  have hstep : ∀ l : Fin m,
      (∫ b : Ω, star (etaOf e w b) * (e l b * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x))))
        = (w l : ℂ) * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x)) := by
    intro l
    have hI : (∫ b : Ω, star (etaOf e w b) * (e l b * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x))))
        = ∫ b : Ω, (star (etaOf e w b) * e l b) *
            (∫ a : Ω, star (e l a) * Θ (Fin.cons a x)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun b => by
        show star (etaOf e w b) * (e l b * (∫ a : Ω, star (e l a) * Θ (Fin.cons a x)))
            = (star (etaOf e w b) * e l b) *
              (∫ a : Ω, star (e l a) * Θ (Fin.cons a x))
        ring))
    rw [hI, MeasureTheory.integral_mul_const, integral_star_etaOf_mul_mode hmeas hbdd hsupp horth w l]
  refine (Finset.sum_congr rfl (fun l _ => hstep l)).trans ?_
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin m))]
  rw [h0]
  simp

/-- `boxAnnOf e w d` applied to the `j = 0` slot of the excited-number operator is `boxAnnOf e w d`. -/
private lemma boxAnnOf_slotJ_zero {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {w : Fin m → ℝ} (h0 : w 0 = 0) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    boxAnnOf e w d (slotJ e (Work.BoseBoxFock.boxT0 m) 0 Θ) = boxAnnOf e w d Θ := by
  funext x
  simp only [boxAnnOf, starRingEnd_apply]
  rw [integral_star_etaOf_mul_slotJ0 hmeas hbdd hsupp horth h0 hΘm hΘb x,
    integral_star_etaOf_mul_Theta_cons hmeas hbdd hsupp w hΘm hΘb x]

/-! ## 8. The target -/

theorem slotBoxT0AnnComm {m D : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0)) {w : Fin m → ℝ} (h0 : w 0 = 0) {Θ : Work.BoseDict.Xn (D + 1) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (D + 1) ℓ) : Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) (Work.BoseDict.boxAnnOf e w D Θ) = Work.BoseDict.boxAnnOf e w D (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ) - Work.BoseDict.boxAnnOf e w D Θ := by
  obtain ⟨hSm, ⟨⟨Cb, -, hCbb⟩, -⟩⟩ :=
    (Work.MB.boxSlotSum_bdd hmeas hbdd hsupp (Work.BoseBoxFock.boxT0 m)).2 Θ hΘm hΘb
  have h1 : boxSlotSum e (Work.BoseBoxFock.boxT0 m) (boxAnnOf e w D Θ)
      = ∑ j : Fin D, boxAnnOf e w D (slotJ e (Work.BoseBoxFock.boxT0 m) (Fin.succ j) Θ) := by
    rw [boxSlotSum_eq_sum_slotJ]
    exact Finset.sum_congr rfl (fun j _ =>
      slotJ_boxAnnOf hmeas hbdd hsupp w (Work.BoseBoxFock.boxT0 m) hΘm hΘb j)
  have h2 : (∑ j : Fin D, boxAnnOf e w D (slotJ e (Work.BoseBoxFock.boxT0 m) (Fin.succ j) Θ))
      = boxAnnOf e w D (∑ j : Fin D, slotJ e (Work.BoseBoxFock.boxT0 m) (Fin.succ j) Θ) :=
    (boxAnnOf_sum hmeas hbdd hsupp w
      (fun j : Fin D => slotJ e (Work.BoseBoxFock.boxT0 m) (Fin.succ j) Θ)
      (fun j => measurable_slotJ hmeas (Work.BoseBoxFock.boxT0 m) (Fin.succ j) hΘm)
      (fun j => exists_norm_slotJ_le hmeas hbdd hsupp (Work.BoseBoxFock.boxT0 m) (Fin.succ j)
        hΘm hΘb)).symm
  have h3 : (∑ j : Fin D, slotJ e (Work.BoseBoxFock.boxT0 m) (Fin.succ j) Θ)
      = boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ
        - slotJ e (Work.BoseBoxFock.boxT0 m) 0 Θ := by
    rw [boxSlotSum_eq_sum_slotJ]
    rw [Fin.sum_univ_succ (fun k : Fin (D + 1) => slotJ e (Work.BoseBoxFock.boxT0 m) k Θ)]
    abel
  rw [h1, h2, h3]
  rw [boxAnnOf_sub hmeas hbdd hsupp w hSm ⟨Cb, hCbb⟩
    (measurable_slotJ hmeas (Work.BoseBoxFock.boxT0 m) 0 hΘm)
    (exists_norm_slotJ_le hmeas hbdd hsupp (Work.BoseBoxFock.boxT0 m) 0 hΘm hΘb)]
  rw [boxAnnOf_slotJ_zero hmeas hbdd hsupp horth h0 hΘm hΘb]

end Work.BoseBoxFock.PotCubicLowBandAux
