import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# `Work.EKLRelCross.propor_aux` — the helper lemmas of the EKL (8) argument

Auxiliary material for `Work.EKLRelCross.leafwise_propor` ((U5) of the frozen contract, EKL (8)),
kept in its own module so that other files (in particular the a.e.-packaging lemmas of the
`D_M` argument) can import it without importing the main theorem.

Contents (all self-contained, no dependence on the flowers or on the `A`-covariance):

* `ae_exists_level_frequently` — Poincaré recurrence with a *uniform* level: if the measurable
  sets `D M` cover a conull set and `T` preserves the probability measure, then a.e. `x` has a
  single level `M` whose `D M` is visited infinitely often.
* `map_mul_pow`, `map_conj_mul_pow` — the elementary push-forward algebra of right translations
  and conjugation (quasi-invariance under `u` iterates, and it conjugates).
* `Box1_subset_V`, `entry_le_two`, `Box1_mul_subset_V` — the entrywise estimates placing `Box1 U`
  and its right translates inside the displacement boxes `V R` (so that they lie in the shape
  furnished by the flowers).
* `le_one_of_pow_lt` — the arithmetic step `(∀ k, c ^ k < M) ⇒ c ≤ 1` in `ℝ≥0∞`.
* `mass_translate` — the mass computation of the `D_M` argument: if `ν y` agrees on a shape `S`
  with a multiple of the conjugate of `ν x` and that conjugate is quasi-invariant under right
  translation by `γ = a u^k a⁻¹` with constant `c ^ k`, and if `Box1 U` and `Box1 U γ⁻¹` both lie
  in `S`, then `ν y (Box1 U γ⁻¹) = c ^ k`.
* `measurableSet_Box1`, `eventual_conj_pow_mem_V`, `map_mul_inv_quasi` — small technical lemmas
  used by the final assembly.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

/-! ## A Poincaré-recurrence lemma: one level is visited infinitely often

If `D M` is an increasing-with-`M` (more precisely: a family of measurable sets whose union is
conull) family of measurable subsets of a probability space and `T` is measure preserving, then
for a.e. `x` there is a *single* level `M` such that the orbit of `x` visits `D M` infinitely
often.  (This is the measure-theoretic input of EKL's `D_M` argument: it is *not* the naive
statement "a.e. point visits the union infinitely often", but the stronger one, which is what
allows a uniform bound `M` in the argument.)

The proof uses only Mathlib's Poincaré recurrence for measurable sets
(`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`): the set `A` of points whose orbit
visits each level only finitely often is `T`-invariant; each `A ∩ D M` is null because on it the
orbit returns infinitely often (Poincaré) but, by `A`-invariance and the definition of `A`, only
finitely often.  -/
theorem ae_exists_level_frequently {α : Type*} [MeasurableSpace α] {ι : Type} [Countable ι]
    (μ : Measure α) [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {D : ι → Set α} (hDmeas : ∀ M, MeasurableSet (D M)) (hcover : μ (⋃ M, D M)ᶜ = 0) :
    ∀ᵐ x ∂μ, ∃ M, ∀ N : ℕ, ∃ n ≥ N, T^[n] x ∈ D M := by
  classical
  set A : Set α := {x | ∀ M, ∃ N, ∀ n ≥ N, T^[n] x ∉ D M} with hAdef
  have hAform : A = {x : α | ¬ (∃ M, ∀ N : ℕ, ∃ n ≥ N, T^[n] x ∈ D M)} := by
    rw [hAdef]
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro h ⟨M, hM⟩
      obtain ⟨N, hN⟩ := h M
      obtain ⟨n, hn, hnx⟩ := hM N
      exact hN n hn hnx
    · intro h M
      by_contra hcon
      push_neg at hcon
      exact h ⟨M, hcon⟩
  have hAmeas : MeasurableSet A := by
    have heq : A = Set.iInter (fun M : ι => Set.iUnion (fun N : ℕ =>
        Set.iInter (fun n : ℕ => Set.iInter (fun _ : N ≤ n =>
          (T^[n]) ⁻¹' (D M)ᶜ)))) := by
      rw [hAdef]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_compl_iff]
    rw [heq]
    apply MeasurableSet.iInter
    intro M
    apply MeasurableSet.iUnion
    intro N
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro hn
    exact (hDmeas M).compl.preimage (hT.measurable.iterate n)
  have hAinv : T ⁻¹' A = A := by
    ext x
    simp only [hAdef, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h M
      obtain ⟨N, hN⟩ := h M
      refine ⟨N + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact hN k (by omega)
    · intro h M
      obtain ⟨N, hN⟩ := h M
      refine ⟨N, fun n hn => ?_⟩
      rw [← Function.iterate_succ_apply]
      exact hN (n + 1) (by omega)
  have hlevel : ∀ M, μ (A ∩ D M) = 0 := by
    intro M
    set B : Set α := A ∩ D M with hBdef
    have hBmeas : MeasurableSet B := hAmeas.inter (hDmeas M)
    have hrec : ∀ᵐ x ∂(μ.restrict B), x ∈ B → ∃ᶠ n in atTop, T^[n] x ∈ B :=
      MeasureTheory.ae_restrict_of_ae
        (hT.conservative.ae_mem_imp_frequently_image_mem hBmeas.nullMeasurableSet)
    have hmemB : ∀ᵐ x ∂(μ.restrict B), x ∈ B := by
      rw [MeasureTheory.ae_restrict_iff' hBmeas]
      filter_upwards with x hx
      exact hx
    have hcontr : ∀ᵐ x ∂(μ.restrict B), False := by
      filter_upwards [hrec, hmemB] with x hfreq hxB
      obtain ⟨N, hN⟩ := hxB.1 M
      have hmemA : ∀ n : ℕ, T^[n] x ∈ A := by
        intro n
        induction n with
        | zero => simpa using hxB.1
        | succ k ih =>
          have hk : T^[k] x ∈ T ⁻¹' A := by rw [hAinv]; exact ih
          have hk' : T^[k + 1] x ∈ A := by
            rw [Function.iterate_succ_apply']
            exact hk
          exact hk'
      have hev : ∀ᶠ n in atTop, T^[n] x ∉ B := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn hcon
        exact hN n hn hcon.2
      obtain ⟨n, h1, h2⟩ := ((hfreq hxB).and_eventually hev).exists
      exact h2 h1
    have huniv : (μ.restrict B) Set.univ = 0 := by
      simpa using MeasureTheory.ae_iff.mp hcontr
    rwa [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at huniv
  have hnull : μ A = 0 := by
    have hsub : A ⊆ (⋃ M, D M)ᶜ ∪ ⋃ M, (A ∩ D M) := by
      intro x hx
      by_cases hxD : x ∈ ⋃ M, D M
      · right
        obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hxD
        exact Set.mem_iUnion.mpr ⟨M, hx, hM⟩
      · exact Set.mem_union_left _ hxD
    have h2 : μ (⋃ M, (A ∩ D M)) = 0 := by
      refine le_antisymm ?_ zero_le
      calc μ (⋃ M, (A ∩ D M)) ≤ ∑' M, μ (A ∩ D M) := measure_iUnion_le _
        _ = 0 := by simp [hlevel]
    have h3 : μ ((⋃ M, D M)ᶜ ∪ ⋃ M, (A ∩ D M)) ≤ 0 := by
      have hle := measure_union_le (μ := μ) (⋃ M, D M)ᶜ (⋃ M, (A ∩ D M))
      rw [hcover, h2, add_zero] at hle
      exact hle
    exact measure_mono_null hsub (le_antisymm h3 zero_le)
  rw [MeasureTheory.ae_iff, ← hAform]
  exact hnull


/-! ## Elementary algebra of right translations and conjugation

These are the two elementary facts about push-forwards of measures under right translations that
the `D_M` argument uses: quasi-invariance under `u` iterates, and it conjugates. -/

/-- **Iterating the quasi-invariance.** -/
theorem map_mul_pow {ν : Measure SL3} {u : SL3} {c : ENNReal}
    (h : ν.map (fun g => g * u) = c • ν) : ∀ k : ℕ, ν.map (fun g => g * u ^ k) = c ^ k • ν := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have hcomp : (fun g : SL3 => g * u ^ (n + 1)) =
        (fun g : SL3 => g * u) ∘ (fun g : SL3 => g * u ^ n) := by
      funext g; rw [Function.comp_apply, mul_assoc, pow_succ]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), ih, Measure.map_smul, h,
      smul_smul, ← pow_succ] <;> try fun_prop

/-- **Conjugation of the quasi-invariance.**  If `ν` is quasi-invariant under right translation by
`u` with constant `c`, then the conjugate measure `ν.map (a · a⁻¹)` is quasi-invariant under right
translation by the conjugate `a u^k a⁻¹` with the same constant `c ^ k`.  (Pure functoriality:
right translation by `a u^k a⁻¹` composed with conjugation by `a` is conjugation by `a` composed
with right translation by `u^k`.) -/
theorem map_conj_mul_pow {ν : Measure SL3} {a u : SL3} {c : ENNReal}
    (h : ν.map (fun g => g * u) = c • ν) (k : ℕ) :
    (ν.map (fun g => a * g * a⁻¹)).map (fun g => g * (a * u ^ k * a⁻¹))
      = c ^ k • (ν.map (fun g => a * g * a⁻¹)) := by
  have hp := map_mul_pow h k
  have hcomp : (fun g : SL3 => g * (a * u ^ k * a⁻¹)) ∘ (fun g : SL3 => a * g * a⁻¹)
      = (fun g : SL3 => a * g * a⁻¹) ∘ (fun g : SL3 => g * u ^ k) := by
    funext g
    simp only [Function.comp_apply]
    group
  have step : Measure.map (fun g : SL3 => g * (a * u ^ k * a⁻¹))
        (Measure.map (fun g : SL3 => a * g * a⁻¹) ν)
      = Measure.map ((fun g : SL3 => g * (a * u ^ k * a⁻¹)) ∘
          (fun g : SL3 => a * g * a⁻¹)) ν :=
    Measure.map_map (by fun_prop) (by fun_prop)
  rw [step, hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hp, Measure.map_smul] <;> try fun_prop


/-! ## The normalising box versus the displacement boxes

`Box1 U` is the closed unit box of `U`; it sits in every `V R` with `R > 1`, and multiplying it by
a sufficiently small element keeps it inside `V R`.  These are the two estimates needed to place
both `Box1 U` and the translated `Box1 U * γ` inside the shape supplied by the flowers. -/

/-- `Box1 U ⊆ V R` for `R > 1`. -/
theorem Box1_subset_V {U : Subgroup SL3} {R : ℝ} (hR : 1 < R) : Box1 U ⊆ V R := by
  intro g hg i j
  exact lt_of_le_of_lt (hg.2 i j) hR

/-- Every entry of a matrix in the closed unit box is at most `2`. -/
theorem entry_le_two {g : SL3} (hg : ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
    - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1) (i j : Fin 3) :
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 := by
  have h1 := hg i j
  have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |((g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
    _ ≤ _ + _ := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- Right multiplication of `Box1 U` by an element of `V ((R-1)/8)` stays inside `V R`. -/
theorem Box1_mul_subset_V {U : Subgroup SL3} {R : ℝ} (hR : 1 < R) {γ : SL3}
    (hγ : γ ∈ V ((R - 1) / 8)) : ∀ g ∈ Box1 U, g * γ ∈ V R := by
  intro g hg i j
  have hg2 : ∀ k : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i k| ≤ 2 :=
    fun k => entry_le_two hg.2 i k
  have hγ1 : ∀ k l : Fin 3, |(γ : Matrix (Fin 3) (Fin 3) ℝ) k l
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < (R - 1) / 8 := fun k l => hγ k l
  have hkey : ((g * γ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i k
          * ((γ : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)
        + ((g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
    have h1 : (∑ k : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i k
        * (1 : Matrix (Fin 3) (Fin 3) ℝ) k j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
      rw [← Matrix.mul_apply, Matrix.one_mul]
    have h2 : (∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i k
        * (1 : Matrix (Fin 3) (Fin 3) ℝ) k j) = (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
      rw [← Matrix.mul_apply, Matrix.mul_one]
    have h3 : (∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i k
        * ((γ : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j))
        = (∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i k
            * (γ : Matrix (Fin 3) (Fin 3) ℝ) k j) - (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
      rw [← h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, ← h1, h3]
    ring
  rw [hkey]
  have hb : |∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i k
      * ((γ : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
      ≤ 6 * ((R - 1) / 8) := by
    calc |∑ k : Fin 3, _| ≤ ∑ k : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i k
          * ((γ : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i k|
          * |((γ : Matrix (Fin 3) (Fin 3) ℝ) k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| := by
        simp [abs_mul]
      _ ≤ ∑ _k : Fin 3, 2 * ((R - 1) / 8) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul (hg2 k) (le_of_lt (hγ1 k j)) (abs_nonneg _) (by norm_num)
      _ = 6 * ((R - 1) / 8) := by simp [Finset.sum_const, Fintype.card_fin]; ring
  calc |∑ k : Fin 3, _ + ((g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)| ≤ _ + _ := abs_add_le _ _
    _ ≤ 6 * ((R - 1) / 8) + 1 := add_le_add hb (hg.2 i j)
    _ < R := by nlinarith


/-! ## The two core steps of the `D_M` argument -/

/-- **Step 1 (arithmetic).**  A power `c ^ k` (with `k` arbitrary) bounded by a *fixed* natural
number forces `c ≤ 1`. -/
theorem le_one_of_pow_lt {c : ENNReal} {M : ℕ} (h : ∀ k : ℕ, c ^ k < (M : ENNReal)) : c ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hM : (M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top M
  rcases eq_or_ne c ⊤ with rfl | hne
  · have h1 := h (M + 1)
    simp at h1
  · have hlt : ∀ k : ℕ, c.toReal ^ k < (M : ℝ) := by
      intro k
      have h1 : c ^ k < (M : ENNReal) := h k
      have h2 : c ^ k ≠ ⊤ := ne_top_of_lt h1
      have h3 : (c ^ k).toReal < ((M : ENNReal)).toReal :=
        (ENNReal.toReal_lt_toReal h2 hM).mpr h1
      rwa [ENNReal.toReal_pow, ENNReal.toReal_natCast] at h3
    have hc1 : 1 < c.toReal := by
      have h4 := (ENNReal.toReal_lt_toReal (by simp : (1 : ENNReal) ≠ ⊤) hne).mpr hc
      simpa using h4
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M : ℝ) hc1
    have h5 := hlt k
    linarith

/-- **Step 2 (the mass computation of the `D_M` argument).**  If `ν y` agrees on a shape `S` with
a multiple `c'` of the conjugate `σ = (ν x).map (a · a⁻¹)`, if `σ` is quasi-invariant under right
translation by `γ = a u^k a⁻¹` with constant `c ^ k` (`map_conj_mul_pow` supplies this when
`ν x` is quasi-invariant under `u` with constant `c`), and if both `Box1 U` and its right
translate by `γ⁻¹` lie in `S`, then the mass of that translate at `y` is `c ^ k`. -/
theorem mass_translate {ν : X3 → Measure SL3} {U : Subgroup SL3} {x y : X3} {a u : SL3} {k : ℕ}
    {c c' : ENNReal} {S : Set SL3}
    (hbox₁m : MeasurableSet (Box1 U))
    (hγmeas : MeasurableSet ((fun g : SL3 => g * (a * u ^ k * a⁻¹)⁻¹) '' (Box1 U)))
    (hprop : ∀ C : Set SL3, MeasurableSet C → C ⊆ S →
      ν y C = c' * (ν x).map (fun g => a * g * a⁻¹) C)
    (hbox₁ : Box1 U ⊆ S) (hbox₂ : (fun g : SL3 => g * (a * u ^ k * a⁻¹)⁻¹) '' (Box1 U) ⊆ S)
    (hσ : ((ν x).map (fun g => a * g * a⁻¹)).map (fun g => g * (a * u ^ k * a⁻¹))
      = c ^ k • ((ν x).map (fun g => a * g * a⁻¹)))
    (hnorm : ν y (Box1 U) = 1) :
    ν y ((fun g : SL3 => g * (a * u ^ k * a⁻¹)⁻¹) '' (Box1 U)) = c ^ k := by
  have hpre : (fun g : SL3 => g * (a * u ^ k * a⁻¹)) ⁻¹' (Box1 U)
      = (fun g : SL3 => g * (a * u ^ k * a⁻¹)⁻¹) '' (Box1 U) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hg
      exact ⟨g * (a * u ^ k * a⁻¹), hg, by group⟩
    · rintro ⟨w, hw, rfl⟩
      show w * (a * u ^ k * a⁻¹)⁻¹ * (a * u ^ k * a⁻¹) ∈ Box1 U
      rw [mul_assoc, inv_mul_cancel, mul_one]
      exact hw
  have hmapapp : (((ν x).map (fun g => a * g * a⁻¹)).map
        (fun g => g * (a * u ^ k * a⁻¹))) (Box1 U)
      = ((ν x).map (fun g => a * g * a⁻¹))
          ((fun g : SL3 => g * (a * u ^ k * a⁻¹)⁻¹) '' (Box1 U)) := by
    rw [Measure.map_apply (by fun_prop) hbox₁m]
    exact congrArg _ hpre
  have key : ν y ((fun g : SL3 => g * (a * u ^ k * a⁻¹)⁻¹) '' (Box1 U))
      = c' * (((ν x).map (fun g => a * g * a⁻¹)).map
          (fun g => g * (a * u ^ k * a⁻¹)) (Box1 U)) := by
    rw [hprop _ hγmeas hbox₂, hmapapp]
  have key2 : ν y (Box1 U) = c' * ((ν x).map (fun g => a * g * a⁻¹)) (Box1 U) :=
    hprop _ hbox₁m hbox₁
  have h1 : c' * ((ν x).map (fun g => a * g * a⁻¹)) (Box1 U) = 1 := by
    rw [← key2, hnorm]
  rw [key, hσ, Measure.smul_apply, smul_eq_mul]
  calc c' * (c ^ k * ((ν x).map (fun g => a * g * a⁻¹)) (Box1 U))
      = c ^ k * (c' * ((ν x).map (fun g => a * g * a⁻¹)) (Box1 U)) := by ring
    _ = c ^ k * 1 := by rw [h1]
    _ = c ^ k := mul_one _

/-! ## The target -/




/-! ## Small technical lemmas for the final assembly -/

/-- `Box1 U` is measurable for a closed subgroup `U`. -/
theorem measurableSet_Box1 {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) :
    MeasurableSet (Box1 U) := by
  have hbox : MeasurableSet {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} := by
    rw [show {g : SL3 | ∀ i j : Fin 3,
        |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1}
        = ⋂ i, ⋂ j, {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} by
      ext g; simp]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    have hcont : Continuous (fun g : SL3 => |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|) := by
      have h1 : Continuous (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
      exact (h1.sub continuous_const).abs
    exact measurableSet_Iic.preimage hcont.measurable
  have hEq : Box1 U = (U : Set SL3) ∩ {g : SL3 | ∀ i j : Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} := by
    ext g; simp [Box1]
  rw [hEq]
  exact hU.measurableSet.inter hbox

/-- The conjugate of a power of a matrix: `A * w ^ k * A⁻¹ = (A * w * A⁻¹) ^ k`. -/
theorem conj_pow (A w : SL3) (k : ℕ) : A * w ^ k * A⁻¹ = (A * w * A⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ m ih =>
    have h : A * w ^ (m + 1) * A⁻¹ = (A * w ^ m * A⁻¹) * (A * w * A⁻¹) := by
      rw [pow_succ]; group
    rw [h, ih, pow_succ]

/-- **Smallness of the conjugates of powers.**  If `aDiag t0` contracts `U`, then for every
`w ∈ U` and every `k` the conjugates `aDiag t0 ^ n · w ^ k · (aDiag t0 ^ n)⁻¹` lie in `V ε` for
all large `n`. -/
theorem eventual_conj_pow_mem_V {U : Subgroup SL3} {t0 : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (nhds (1 : SL3))) :
    ∀ w ∈ U, ∀ k : ℕ, ∀ᶠ n in atTop,
      aDiag t0 ^ n * w ^ k * (aDiag t0 ^ n)⁻¹ ∈ V ε := by
  intro w hw k
  have hO : IsOpen {g : SL3 | g ^ k ∈ V ε} :=
    (Work.EKLContract.Lemmas.V_open_one ε hε).1.preimage (continuous_id.pow k)
  have h1 : (1 : SL3) ∈ {g : SL3 | g ^ k ∈ V ε} := by
    simpa using (Work.EKLContract.Lemmas.V_open_one ε hε).2
  filter_upwards [(hcontr w hw).eventually_mem (hO.mem_nhds h1)] with n hn
  rw [conj_pow]
  exact hn

/-- **Inverting the quasi-invariance.**  If `ν` is quasi-invariant under right translation by
`u` with nonzero finite constant `c`, then it is quasi-invariant under right translation by
`u⁻¹` with constant `c⁻¹`. -/
theorem map_mul_inv_quasi {ν : Measure SL3} {u : SL3} {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : ν.map (fun g => g * u) = c • ν) :
    ν.map (fun g => g * u⁻¹) = c⁻¹ • ν := by
  have hcomp : (fun g : SL3 => g * u⁻¹) ∘ (fun g : SL3 => g * u) = id := by
    funext g
    simp [mul_assoc]
  have h2 : (ν.map (fun g : SL3 => g * u)).map (fun g : SL3 => g * u⁻¹)
      = ν.map ((fun g : SL3 => g * u⁻¹) ∘ (fun g : SL3 => g * u)) :=
    Measure.map_map (by fun_prop) (by fun_prop)
  rw [hcomp, Measure.map_id] at h2
  rw [h, Measure.map_smul] at h2 <;> try fun_prop
  calc ν.map (fun g : SL3 => g * u⁻¹)
      = (c⁻¹ * c) • (ν.map (fun g : SL3 => g * u⁻¹)) := by
        rw [ENNReal.inv_mul_cancel hc0 hct, one_smul]
    _ = c⁻¹ • (c • (ν.map (fun g : SL3 => g * u⁻¹))) := by rw [smul_smul]
    _ = c⁻¹ • ν := by rw [h2]

end Work.EKLRelCross
