/-
# C12 (`P_Puig`): AJ Lemma 4.3, the "Puig argument"

This file assembles C12.  The two mathematical inputs of AJ's Lemma 4.3 are

* the existence of the Prüfer rotation number together with its conjugacy formula
  (`P_RotBasics`, part 1/3/4: `prove_RotBasics`), and
* the fact that every spectral point is a point of increase of the integrated density of
  states (`P_IDSSpectrum`, `prove_IDSSpectrum`),

together with two self-contained lemmas proved in `Submission.Work.TMPuig`:

* `resonant_false`: a resonant reducibility datum (a conjugacy of the cocycle to a constant
  rotation whose angle is an integer multiple of the frequency) is impossible; and
* `irrational_int_pair_dense`: for irrational `α` the additive group `ℤ + ℤα` is dense.

Everything is proved below except `prove_Puig` itself, which is instantiated from the
components once they are available.
-/
import Mathlib.Analysis.Real.Cardinality
import Submission.Work.TMPuig.Defs
import Submission.Work.TMPuig.irrational_int_pair_dense
import Submission.Work.TMPuig.rotLift_continuousOn_of_reducible
import Submission.Work.TMPuig.prufer_tendsto_of_reducible
import Submission.Work.TMPuig.dual_l2_solution
import Submission.Work.TMPuig.countable_l2_solutions
import Submission.Work.TMPuig.resonant_false
import Submission.Work.TMContract.Glue

set_option maxHeartbeats 4000000

open Matrix Filter Topology Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace Work.TMComp

open Work.TMContract Work.TMPuig


/-! ## The scaled density statement -/

/-- The scaled form of `Work.TMPuig.irrational_int_pair_dense`: the multiples of `2` of the
group `ℤ + ℤα` are dense. -/
theorem dense_scaled {α : ℝ} (hα : Irrational α) {x y : ℝ} (hxy : x < y) :
    ∃ l j : ℤ, x < 2 * ((l : ℝ) * α + (j : ℝ)) ∧ 2 * ((l : ℝ) * α + (j : ℝ)) < y := by
  obtain ⟨l, j, h1, h2⟩ := irrational_int_pair_dense hα (show x / 2 < y / 2 by linarith)
  exact ⟨l, j, by linarith, by linarith⟩

/-! ## The core of the Puig argument -/

/-- **C12 modulo its design inputs.**

Let `J = (c,d) ⊆ Σ_{λ,α}` and suppose `J ⊆ Λ_{λ,α}` (every energy of `J` is analytically
reducible to a constant rotation).  Then:

* `h5` (C5) gives the conjugacy formula `rotLift = 2 * c_E + 2 * j_E` for the conjugating
  angle `c_E` of `E`, and the continuity of `N = ids`;
* `h6` (C6) makes `N` a point of increase at every point of `J`, so `N` is strictly
  increasing there; hence `N(J)` has non-empty interior, and `hdense` produces an energy at
  which `N` takes a resonant value, so that `c_E ≡ l α  (mod 1)`;
* `hres` then contradicts `J ⊆ Λ`. -/
theorem puig_core (h5 : P_RotBasics) (h6 : P_IDSSpectrum)
    (hres : ∀ {α lam E c : ℝ}, Irrational α → lam ≠ 0 → HasRedDatum α lam E c →
      (∃ l m : ℤ, c - (l : ℝ) * α = (m : ℝ)) → False)
    (hdense : ∀ {α : ℝ}, Irrational α → ∀ {x y : ℝ}, x < y →
      ∃ l j : ℤ, x < 1 + 2 * ((l : ℝ) * α + (j : ℝ)) ∧
        1 + 2 * ((l : ℝ) * α + (j : ℝ)) < y) :
    P_Puig := by
  intro α lam hα hpos hle c d hcd hsub hred
  -- unpack the two component statements (they are large `def`s; do it once)
  have h5' := h5
  simp only [P_RotBasics] at h5'
  obtain ⟨h5a, h5b, h5c, h5d⟩ := h5'
  -- `N = ids α lam` is strictly increasing and continuous on `J`
  have hNsmono : StrictMonoOn (ids α lam) (Ioo c d) :=
    ids_strictMonoOn_Ioo_of_subset h5 h6 hα hsub
  have hNcont : Continuous (fun E : ℝ => ids α lam E) :=
    (h5c lam).comp (continuous_const.prodMk continuous_id)
  -- pick a nondegenerate subinterval `(a,b) ⊆ (c,d)`
  set a : ℝ := (2 * c + d) / 3 with ha
  set b : ℝ := (c + 2 * d) / 3 with hb
  have hca : c < a := by rw [ha]; linarith
  have hab : a < b := by rw [ha, hb]; linarith
  have hbd : b < d := by rw [hb]; linarith
  have hIcc_sub : Icc a b ⊆ amoSpec α lam := fun t ht =>
    hsub ⟨lt_of_lt_of_le hca ht.1, lt_of_le_of_lt ht.2 hbd⟩
  have hIcc_mono : StrictMonoOn (ids α lam) (Icc a b) := by
    intro x hx y hy hxy
    exact ids_lt_of_Icc_subset_amoSpec h5 h6 hα hxy fun t ht =>
      hIcc_sub ⟨le_trans hx.1 ht.1, le_trans ht.2 hy.2⟩
  have himg : (ids α lam) '' Ioo a b = Ioo (ids α lam a) (ids α lam b) :=
    ContinuousOn.image_Ioo_of_strictMonoOn hab.le hNcont.continuousOn hIcc_mono
  have hlt : ids α lam a < ids α lam b :=
    hIcc_mono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  -- a resonant value inside `N '' (a,b)`
  obtain ⟨l, j, hlow, hhigh⟩ := hdense hα hlt
  have hmem : 1 + 2 * ((l : ℝ) * α + (j : ℝ)) ∈ (ids α lam) '' Ioo a b := by
    rw [himg]; exact ⟨hlow, hhigh⟩
  obtain ⟨E, hE, hEval⟩ := hmem
  have hEsub : E ∈ Ioo c d := ⟨lt_trans hca hE.1, lt_trans hE.2 hbd⟩
  -- the reducibility datum at `E`
  have hEred : E ∈ RedSet α lam := hred hEsub
  simp only [RedSet, Set.mem_setOf_eq] at hEred
  obtain ⟨B, cE, hana, hper, hdet, hdeg, hconj⟩ := hEred
  -- the conjugacy formula for the rotation number
  obtain ⟨j₁, hj₁⟩ := h5d α lam E B (fun _ => cE) 0 hdeg hper hdet continuous_const (fun _ => rfl) hconj
  simp only [intervalIntegral.integral_const, sub_zero, mul_zero, one_smul] at hj₁
  -- compare: `N E = 1 - rotLift E = 1 - 2 cE - 2 j₁` and `N E = 1 + 2 (l α + j)`
  have hkey : cE - ((-l : ℤ) : ℝ) * α = ((-(j₁ + j) : ℤ) : ℝ) := by
    have h := hEval
    rw [show ids α lam E = 1 - rotLift α lam E from rfl, hj₁] at h
    push_cast at h ⊢
    linarith [h]
  exact hres hα hpos.ne' ⟨B, hana, hper, hdet, hconj⟩ ⟨-l, -(j₁ + j), hkey⟩


/-! ## The component

`prove_Puig` itself is assembled at the end of the file, on top of `puig_core_own`. -/


/-! ## The core of the Puig argument, self-contained route

Here the inputs of `puig_core` are replaced by the facts about the Prüfer averages that can
be proved directly from the reducibility data:

* `hval`  : the averaged Prüfer angle converges to `2 * cE + 2 * j` (from
  `Submission.Work.TMPuig.prufer_tendsto_of_reducible`);
* `hcont` : continuity of `rotLift` on `J`;
* `hnc`   : `rotLift` takes two different values on `J` (non-constancy, from the dual
  recurrence and the countability of the `ℓ²` eigenvalues);
* `hres`  : no reducibility datum is resonant (`resonant_false`). -/

theorem puig_core_own {α lam c d : ℝ} (hcd : c < d)
    (hred : Ioo c d ⊆ RedSet α lam)
    (hval : ∀ E ∈ RedSet α lam, ∀ (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (cE : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ) → (∀ x, B (x + 1) = B x) →
      (∀ x, (B x).det = 1) → HasDegree B 0 →
      (∀ x, B (x + α) * tmR lam E x = rot cE * B x) →
      ∃ j : ℤ, Tendsto
        (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))
        atTop (𝓝 (2 * cE + 2 * (j : ℝ))))
    (hcont : ContinuousOn (fun E : ℝ => rotLift α lam E) (Ioo c d))
    (hnc : ∃ E₁ ∈ Ioo c d, ∃ E₂ ∈ Ioo c d, rotLift α lam E₁ ≠ rotLift α lam E₂)
    (hres : ∀ {E cE : ℝ}, HasRedDatum α lam E cE →
      (∃ l m : ℤ, cE - (l : ℝ) * α = (m : ℝ)) → False)
    (hdense : ∀ {x y : ℝ}, x < y →
      ∃ l j : ℤ, x < 2 * ((l : ℝ) * α + (j : ℝ)) ∧ 2 * ((l : ℝ) * α + (j : ℝ)) < y) :
    False := by
  obtain ⟨E₁, hE₁, E₂, hE₂, hne⟩ := hnc
  have hne' : E₁ ≠ E₂ := fun h => hne (by rw [h])
  -- a pair `p < q` in `J` with different values
  obtain ⟨p, hp, q, hq, hpq, hpvne⟩ :
      ∃ p ∈ Ioo c d, ∃ q ∈ Ioo c d, p < q ∧ rotLift α lam p ≠ rotLift α lam q := by
    rcases lt_or_gt_of_ne hne' with h | h
    · exact ⟨E₁, hE₁, E₂, hE₂, h, hne⟩
    · exact ⟨E₂, hE₂, E₁, hE₁, h, fun hh => hne hh.symm⟩
  have hcu : ContinuousOn (fun E : ℝ => rotLift α lam E) (Icc p q) :=
    hcont.mono fun t ht => ⟨lt_of_lt_of_le hp.1 ht.1, lt_of_le_of_lt ht.2 hq.2⟩
  -- a resonant value produced by the intermediate value theorem gives a contradiction
  have fin : ∀ (E : ℝ) (l j : ℤ), E ∈ Icc p q →
      rotLift α lam E = 2 * ((l : ℝ) * α + (j : ℝ)) → False := by
    intro E l j hE hEval
    have hEcd : E ∈ Ioo c d := ⟨lt_of_lt_of_le hp.1 hE.1, lt_of_le_of_lt hE.2 hq.2⟩
    have hEredB : E ∈ RedSet α lam := hred hEcd
    have hEred := hEredB
    simp only [RedSet, Set.mem_setOf_eq] at hEred
    obtain ⟨B, cE, hana, hper, hdet, hdeg, hconj⟩ := hEred
    obtain ⟨jE, hjE⟩ := hval E hEredB B cE hana hper hdet hdeg hconj
    have hval_eq : rotLift α lam E = 2 * cE + 2 * (jE : ℝ) :=
      Filter.Tendsto.limUnder_eq hjE
    have hkey : cE - (l : ℝ) * α = ((j - jE : ℤ) : ℝ) := by
      have h2 : 2 * cE + 2 * (jE : ℝ) = 2 * ((l : ℝ) * α + (j : ℝ)) := by
        rw [← hval_eq]; exact hEval
      push_cast
      linarith [h2]
    exact hres (E := E) (cE := cE) ⟨B, hana, hper, hdet, hconj⟩ ⟨l, j - jE, hkey⟩
  rcases lt_or_gt_of_ne hpvne with hpv | hpv
  · obtain ⟨l, j, hlow, hhigh⟩ := hdense hpv
    obtain ⟨E, hE, hEval⟩ := intermediate_value_Icc hpq.le hcu ⟨le_of_lt hlow, le_of_lt hhigh⟩
    exact fin E l j hE hEval
  · obtain ⟨l, j, hlow, hhigh⟩ := hdense hpv
    obtain ⟨E, hE, hEval⟩ := intermediate_value_Icc' hpq.le hcu ⟨le_of_lt hlow, le_of_lt hhigh⟩
    exact fin E l j hE hEval


/-! ## The core of the Puig argument, value form

The same assembly as `puig_core_own`, but with the input about the lifted rotation number
stated as the *value* at a reducibility datum (`rotLift α lam E = 2c + 2j`) rather than as the
convergence of the Cesàro averages: the two are equivalent through `Tendsto.limUnder_eq`, and
both `prufer_tendsto_of_reducible` and `rotLift_of_reducible` supply this form. -/

/-- **C12 modulo its design inputs, value form.** -/
theorem puig_core_value {α lam c d : ℝ} (hcd : c < d)
    (hred : Ioo c d ⊆ RedSet α lam)
    (hval : ∀ E ∈ RedSet α lam, ∀ (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (cE : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ) → (∀ x, B (x + 1) = B x) →
      (∀ x, (B x).det = 1) → HasDegree B 0 →
      (∀ x, B (x + α) * tmR lam E x = rot cE * B x) →
      ∃ j : ℤ, rotLift α lam E = 2 * cE + 2 * (j : ℝ))
    (hcont : ContinuousOn (fun E : ℝ => rotLift α lam E) (Ioo c d))
    (hnc : ∃ E₁ ∈ Ioo c d, ∃ E₂ ∈ Ioo c d, rotLift α lam E₁ ≠ rotLift α lam E₂)
    (hres : ∀ {E cE : ℝ}, HasRedDatum α lam E cE →
      (∃ l m : ℤ, cE - (l : ℝ) * α = (m : ℝ)) → False)
    (hdense : ∀ {x y : ℝ}, x < y →
      ∃ l j : ℤ, x < 2 * ((l : ℝ) * α + (j : ℝ)) ∧ 2 * ((l : ℝ) * α + (j : ℝ)) < y) :
    False := by
  obtain ⟨E₁, hE₁, E₂, hE₂, hne⟩ := hnc
  have hne' : E₁ ≠ E₂ := fun h => hne (by rw [h])
  obtain ⟨p, hp, q, hq, hpq, hpvne⟩ :
      ∃ p ∈ Ioo c d, ∃ q ∈ Ioo c d, p < q ∧ rotLift α lam p ≠ rotLift α lam q := by
    rcases lt_or_gt_of_ne hne' with h | h
    · exact ⟨E₁, hE₁, E₂, hE₂, h, hne⟩
    · exact ⟨E₂, hE₂, E₁, hE₁, h, fun hh => hne hh.symm⟩
  have hcu : ContinuousOn (fun E : ℝ => rotLift α lam E) (Icc p q) :=
    hcont.mono fun t ht => ⟨lt_of_lt_of_le hp.1 ht.1, lt_of_le_of_lt ht.2 hq.2⟩
  have fin : ∀ (E : ℝ) (l j : ℤ), E ∈ Icc p q →
      rotLift α lam E = 2 * ((l : ℝ) * α + (j : ℝ)) → False := by
    intro E l j hE hEval
    have hEcd : E ∈ Ioo c d := ⟨lt_of_lt_of_le hp.1 hE.1, lt_of_le_of_lt hE.2 hq.2⟩
    have hEredB : E ∈ RedSet α lam := hred hEcd
    have hEred := hEredB
    simp only [RedSet, Set.mem_setOf_eq] at hEred
    obtain ⟨B, cE, hana, hper, hdet, hdeg, hconj⟩ := hEred
    obtain ⟨jE, hval_eq⟩ := hval E hEredB B cE hana hper hdet hdeg hconj
    have hkey : cE - (l : ℝ) * α = ((j - jE : ℤ) : ℝ) := by
      have h2 : 2 * cE + 2 * (jE : ℝ) = 2 * ((l : ℝ) * α + (j : ℝ)) := by
        rw [← hval_eq]; exact hEval
      push_cast
      linarith [h2]
    exact hres (E := E) (cE := cE) ⟨B, hana, hper, hdet, hconj⟩ ⟨l, j - jE, hkey⟩
  rcases lt_or_gt_of_ne hpvne with hpv | hpv
  · obtain ⟨l, j, hlow, hhigh⟩ := hdense hpv
    obtain ⟨E, hE, hEval⟩ := intermediate_value_Icc hpq.le hcu ⟨le_of_lt hlow, le_of_lt hhigh⟩
    exact fin E l j hE hEval
  · obtain ⟨l, j, hlow, hhigh⟩ := hdense hpv
    obtain ⟨E, hE, hEval⟩ := intermediate_value_Icc' hpq.le hcu ⟨le_of_lt hlow, le_of_lt hhigh⟩
    exact fin E l j hE hEval

/-! ## Assembly of C12: the reduction to the countable set of `ℓ²` eigenvalues

The remaining input of `puig_core_own` is the non-constancy of `E ↦ rotLift α lam E` on an
interval `(c,d) ⊆ Λ_{λ,α}`.  It is proved here from the *duality* lemmas of
`Submission.Work.TMPuig`:

* `rotLift_of_reducible` (`= prufer_tendsto_of_reducible` + `Tendsto.limUnder_eq`): at a
  reducible energy with conjugating angle `c`, `rotLift = 2c + 2j`;
* `dual_l2_solution`: the same datum produces a nonzero `ℓ²` solution of the dual recurrence
  at phase `c` and parameter `E / λ`;
* `countable_l2_solutions`: for *fixed* phase, the parameters admitting a nonzero `ℓ²`
  solution form a countable set.

Hence every level set of `E ↦ rotLift α lam E` inside `(c,d)` is countable, while `(c,d)`
itself is not; so `rotLift` is non-constant on `(c,d)`. -/

/-- The value form of `prufer_tendsto_of_reducible`: at a reducibility datum with angle `c`,
the lifted rotation number is `2c + 2j` for some `j : ℤ`. -/
theorem rotLift_eq_of_data {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ)
    (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hdeg : HasDegree B 0)
    (hconj : ∀ x, B (x + α) * tmR lam E x = rot c * B x) :
    ∃ j : ℤ, rotLift α lam E = 2 * c + 2 * (j : ℝ) := by
  obtain ⟨j, hj⟩ := prufer_tendsto_of_reducible α lam E c hB hper hdet hdeg hconj
  exact ⟨j, Filter.Tendsto.limUnder_eq hj⟩

/-- **Level sets of the rotation number are countable.**  For `(c,d) ⊆ Λ_{λ,α}` and any `ν`,
the set of `E ∈ (c,d)` with `rotLift α lam E = ν` is countable: any such `E` is reducible
with angle `c_E ≡ ν/2`, hence `E/λ` lies in the countable set of parameters admitting a
nonzero `ℓ²` solution of the dual recurrence at the *fixed* phase `ν/2`. -/
theorem countable_fiber_of_reducible {α lam c d ν : ℝ} (hlam : lam ≠ 0)
    (hred : Ioo c d ⊆ RedSet α lam) :
    (Ioo c d ∩ {E | rotLift α lam E = ν}).Countable := by
  set S : Set ℝ := {Λ : ℝ | ∃ u : ℤ → ℂ, u ≠ 0 ∧ Summable (fun n : ℤ => ‖u n‖ ^ 2) ∧
      ∀ n : ℤ, u (n + 1) + u (n - 1)
        + ((2 / lam) * Real.cos (2 * Real.pi * ((n : ℝ) * α + ν / 2)) - Λ) * u n = 0}
    with hSdef
  have hSc : S.Countable := countable_l2_solutions α lam (ν / 2) hlam
  refine Set.Countable.mono ?_ (Set.Countable.preimage hSc (f := fun E : ℝ => E / lam) ?_)
  · intro E hE
    obtain ⟨hEcd, hEν⟩ := hE
    simp only [Set.mem_setOf_eq] at hEν ⊢
    obtain ⟨B, cE, hana, hper, hdet, hdeg, hconj⟩ := hred hEcd
    obtain ⟨j, hj⟩ := rotLift_eq_of_data hana hper hdet hdeg hconj
    have hcj : cE = ν / 2 - (j : ℝ) := by linarith [hj, hEν]
    obtain ⟨u, hu0, husum, hurec⟩ :=
      dual_l2_solution α lam E cE hlam hana hper hdet hconj
    refine ⟨u, hu0, husum, fun n => ?_⟩
    have hcast : ((E / lam : ℝ) : ℂ) = (E : ℂ) / (lam : ℂ) := by
      push_cast; ring
    rw [hcast]
    have hcos : Real.cos (2 * Real.pi * ((n : ℝ) * α + cE))
        = Real.cos (2 * Real.pi * ((n : ℝ) * α + ν / 2)) := by
      have harg : 2 * Real.pi * ((n : ℝ) * α + cE)
          = 2 * Real.pi * ((n : ℝ) * α + ν / 2) + (-j) * (2 * Real.pi) := by
        rw [hcj]; ring
      rw [harg]
      have := Real.cos_add_int_mul_two_pi (2 * Real.pi * ((n : ℝ) * α + ν / 2)) (-j)
      push_cast at this ⊢
      exact this
    rw [← hcos]
    exact hurec n
  · intro x y hxy
    have hxy' : x / lam = y / lam := hxy
    have h2 : (x / lam) * lam = (y / lam) * lam := by rw [hxy']
    rw [div_mul_cancel₀ x hlam, div_mul_cancel₀ y hlam] at h2
    exact h2

/-- **`rotLift` is not constant on a reducible interval.** -/
theorem rotLift_not_const_of_reducible {α lam c d : ℝ} (hlam : lam ≠ 0) (hcd : c < d)
    (hred : Ioo c d ⊆ RedSet α lam) :
    ¬ ∃ ν : ℝ, ∀ E ∈ Ioo c d, rotLift α lam E = ν := by
  rintro ⟨ν, hν⟩
  have hsub : Ioo c d ⊆ Ioo c d ∩ {E | rotLift α lam E = ν} :=
    fun E hE => ⟨hE, hν E hE⟩
  have hcount : (Ioo c d).Countable :=
    Set.Countable.mono hsub (countable_fiber_of_reducible hlam hred)
  rw [Cardinal.Real.Ioo_countable_iff] at hcount
  linarith

/-- `rotLift` takes two different values on a reducible interval. -/
theorem exists_two_values_of_reducible {α lam c d : ℝ} (hlam : lam ≠ 0) (hcd : c < d)
    (hred : Ioo c d ⊆ RedSet α lam) :
    ∃ E₁ ∈ Ioo c d, ∃ E₂ ∈ Ioo c d, rotLift α lam E₁ ≠ rotLift α lam E₂ := by
  by_contra h
  push_neg at h
  have hmid : (c + d) / 2 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  exact rotLift_not_const_of_reducible hlam hcd hred
    ⟨rotLift α lam ((c + d) / 2), fun E hE => h E hE _ hmid⟩

/-! ## The component (`P_Puig`) -/

/-- **C12** (`P_Puig`): AJ Lemma 4.3.  No interval contained in the spectrum `Σ_{λ,α}` is
contained in the reducibility set `Λ_{λ,α}`. -/
theorem prove_Puig : Work.TMContract.P_Puig := by
  intro α lam hα hpos hle c d hcd hsub hred
  refine puig_core_value hcd hred ?_ ?_ ?_ ?_ (fun {x y} hxy => dense_scaled hα hxy)
  · intro E _ B cE hana hper hdet hdeg hconj
    exact rotLift_eq_of_data hana hper hdet hdeg hconj
  · exact (continuous_rotLift α lam).continuousOn
  · exact exists_two_values_of_reducible hpos.ne' hcd hred
  · intro E cE hd hl
    obtain ⟨B, hana, hper, hdet, hconj⟩ := hd
    obtain ⟨l, m, hm⟩ := hl
    exact resonant_false hα hpos.ne' hana hper hdet hconj l ⟨m, hm⟩

end Work.TMComp
