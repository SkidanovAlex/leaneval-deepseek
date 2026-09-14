import Mathlib
import Submission.Commons.NumberTheory.Height.NumberField.log_abv_form_value_upper
import Submission.Commons.NumberTheory.Height.NumberField.log_abv_form_value_lower
import Submission.Commons.Topology.Box.box_pigeonhole
import Submission.Commons.Analysis.Normed.finite_bounded_int_vectors

namespace Commons.NumberTheory.Height.NumberField

open _root_.NumberField

set_option linter.style.haveILetI false

/-- **Extraction of a common exponent vector for a whole system of forms.**

Let `K` be a number field, `w` an infinite place, `a : σ → σ → K` a system of `|σ|` linear forms
and `X` an infinite set of nonzero integer vectors on which all form values are nonzero and the
sum of the logarithms of the local absolute values of the form values is `< -ε log ‖x‖`.
Then there is a single exponent vector `c : σ → ℝ` with **negative coordinate sum** and an
infinite subset `X' ⊆ X` with `w.val (∑ j, a i j * x j) ≤ ‖x‖ ^ (c i)` for all `x ∈ X'` and all
`i`.

This is the pigeonhole ("approximation domain") step: the normalized exponent vectors
`(log |L_i(x)|_w / log ‖x‖)_i` are bounded (via the upper and lower log-bounds) and their
coordinate sum is `< -ε`; a box of side `1/N` (for `N` large) contains infinitely many of them,
and its north-east corner `c` has `∑ c_i ≤ -ε + |σ|/N < 0` and dominates every exponent vector
in the box. -/
theorem exponent_vector_extraction_uniform {K : Type*} [Field K] [NumberField K]
    {σ : Type*} [Fintype σ] (hσ : 2 ≤ Fintype.card σ) (a : σ → σ → K)
    (w : NumberField.InfinitePlace K) (ε : ℝ) (hε : 0 < ε)
    (X : Set (σ → ℤ)) (hX : X.Infinite)
    (hne : ∀ x ∈ X, x ≠ 0)
    (hnz : ∀ x ∈ X, ∀ i : σ, (∑ j : σ, a i j * (x j : K)) ≠ 0)
    (hsum : ∀ x ∈ X,
      ∑ i : σ, Real.log (w.val (∑ j : σ, a i j * (x j : K))) < -ε * Real.log ‖x‖) :
    ∃ (c : σ → ℝ) (X' : Set (σ → ℤ)), (∑ i : σ, c i < 0) ∧ X' ⊆ X ∧ X'.Infinite ∧
      ∀ x ∈ X', ∀ i : σ, w.val (∑ j : σ, a i j * (x j : K)) ≤ ‖x‖ ^ (c i) := by
  classical
  -- shorthand for the values of the forms
  let Lf : σ → (σ → ℤ) → K := fun i x => ∑ j : σ, a i j * (x j : K)
  -- upper and lower log-bounds, uniform over the coordinates `i`
  have hub : ∀ i : σ, ∃ C : ℝ, 0 < C ∧ ∀ (x : σ → ℤ), x ≠ 0 →
      Real.log (w.val (Lf i x)) ≤ C + C * Real.log ‖x‖ := by
    intro i
    obtain ⟨C, hC0, hC⟩ := log_abv_form_value_upper (a i)
    exact ⟨C, hC0, fun x hx => hC w x hx⟩
  have hlb : ∀ i : σ, ∃ C : ℝ, 0 < C ∧ ∀ (x : σ → ℤ), x ≠ 0 →
      -C - C * Real.log ‖x‖ ≤ Real.log (w.val (Lf i x)) := by
    intro i
    obtain ⟨C, hC0, hC⟩ := log_abv_form_value_lower hσ (a i)
    exact ⟨C, hC0, fun x hx => hC w x hx⟩
  choose Cu hCu using hub
  choose Cl hCl using hlb
  haveI : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  set CU : ℝ := ∑ i : σ, Cu i with hCUdef
  set CL : ℝ := ∑ i : σ, Cl i with hCLdef
  have hCUpos : 0 < CU := by
    rw [hCUdef]; exact Finset.sum_pos (fun i _ => (hCu i).1) Finset.univ_nonempty
  have hCLpos : 0 < CL := by
    rw [hCLdef]; exact Finset.sum_pos (fun i _ => (hCl i).1) Finset.univ_nonempty
  have hCUle : ∀ i : σ, Cu i ≤ CU := fun i => by
    rw [hCUdef]; exact Finset.single_le_sum (fun j _ => (hCu j).1.le) (Finset.mem_univ i)
  have hCLle : ∀ i : σ, Cl i ≤ CL := fun i => by
    rw [hCLdef]; exact Finset.single_le_sum (fun j _ => (hCl j).1.le) (Finset.mem_univ i)
  set B : ℝ := max (2 * CU) (2 * CL) with hBdef
  -- the subset where log ‖x‖ ≥ 1
  set X₀ : Set (σ → ℤ) := X ∩ {x : σ → ℤ | Real.exp 1 ≤ ‖x‖} with hX₀def
  have hX0mem : ∀ x : σ → ℤ, x ∈ X₀ ↔ x ∈ X ∧ Real.exp 1 ≤ ‖x‖ := by
    intro x; rw [hX₀def, Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hX₀inf : X₀.Infinite := by
    by_contra h
    rw [Set.not_infinite] at h
    have hd : (X \ X₀).Finite := by
      refine Set.Finite.subset
        (Commons.Analysis.Normed.finite_bounded_int_vectors (Real.exp 1)) ?_
      intro x hx
      rw [Set.mem_sdiff] at hx
      rw [Set.mem_ofPred_eq]
      by_contra hc
      rw [not_le] at hc
      exact hx.2 ((hX0mem x).mpr ⟨hx.1, hc.le⟩)
    have hXfin : X.Finite := by
      refine Set.Finite.subset (h.union hd) ?_
      intro x hx
      rw [Set.mem_union]
      by_cases hx0 : x ∈ X₀
      · exact Or.inl hx0
      · exact Or.inr ⟨hx, hx0⟩
    exact hX hXfin
  have hlogX : ∀ x ∈ X₀, 1 ≤ Real.log ‖x‖ := by
    intro x hx
    obtain ⟨-, hxe⟩ := (hX0mem x).mp hx
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hlogXpos : ∀ x ∈ X₀, 0 < Real.log ‖x‖ :=
    fun x hx => lt_of_lt_of_le one_pos (hlogX x hx)
  have hxpos_of : ∀ x ∈ X₀, 0 < ‖x‖ := by
    intro x hx
    obtain ⟨-, hxe⟩ := (hX0mem x).mp hx
    exact lt_of_lt_of_le (Real.exp_pos 1) hxe
  -- the normalized exponent vector
  let t : (σ → ℤ) → σ → ℝ := fun x i => Real.log (w.val (Lf i x)) / Real.log ‖x‖
  have hsumS : ∀ x ∈ X₀, ∑ i : σ, t x i < -ε := by
    intro x hx
    obtain ⟨hxX, -⟩ := (hX0mem x).mp hx
    have hxlogpos : 0 < Real.log ‖x‖ := hlogXpos x hx
    have h := hsum x hxX
    have heq : ∑ i : σ, t x i
        = (∑ i : σ, Real.log (w.val (Lf i x))) / Real.log ‖x‖ := by
      rw [Finset.sum_div]
    rw [heq, div_lt_iff₀ hxlogpos]
    linarith
  have ht_ub : ∀ x ∈ X₀, ∀ i : σ, t x i ≤ 2 * CU := by
    intro x hx i
    have hxlogpos : 0 < Real.log ‖x‖ := hlogXpos x hx
    have hxlog1 : 1 ≤ Real.log ‖x‖ := hlogX x hx
    have h := (hCu i).2 x (hne x ((hX0mem x).mp hx).1)
    have hCule : Cu i ≤ CU := hCUle i
    have step : Cu i + Cu i * Real.log ‖x‖ ≤ CU + CU * Real.log ‖x‖ := by
      have := mul_le_mul_of_nonneg_right hCule hxlogpos.le
      linarith
    have step2 : CU + CU * Real.log ‖x‖ ≤ (2 * CU) * Real.log ‖x‖ := by
      nlinarith [hxlog1, hCUpos.le]
    have hmain : Real.log (w.val (Lf i x)) ≤ (2 * CU) * Real.log ‖x‖ :=
      le_trans h (le_trans step step2)
    show Real.log (w.val (Lf i x)) / Real.log ‖x‖ ≤ 2 * CU
    rw [div_le_iff₀ hxlogpos]
    linarith
  have ht_lb : ∀ x ∈ X₀, ∀ i : σ, -(2 * CL) ≤ t x i := by
    intro x hx i
    have hxlogpos : 0 < Real.log ‖x‖ := hlogXpos x hx
    have hxlog1 : 1 ≤ Real.log ‖x‖ := hlogX x hx
    have h := (hCl i).2 x (hne x ((hX0mem x).mp hx).1)
    have hClle : Cl i ≤ CL := hCLle i
    have step : Cl i ≤ Cl i * Real.log ‖x‖ := by
      have := mul_le_mul_of_nonneg_left hxlog1 (hCl i).1.le
      simpa using this
    have step2 : Cl i * Real.log ‖x‖ ≤ CL * Real.log ‖x‖ :=
      mul_le_mul_of_nonneg_right hClle hxlogpos.le
    have hmain : -(2 * CL) * Real.log ‖x‖ ≤ Real.log (w.val (Lf i x)) := by
      nlinarith [h, step, step2]
    show -(2 * CL) ≤ Real.log (w.val (Lf i x)) / Real.log ‖x‖
    rw [le_div_iff₀ hxlogpos]
    linarith
  have ht_abs : ∀ x ∈ X₀, ∀ i : σ, |t x i| ≤ B := by
    intro x hx i
    rw [abs_le]
    constructor
    · have := ht_lb x hx i
      have h2 : 2 * CL ≤ B := by rw [hBdef]; exact le_max_right _ _
      linarith
    · have := ht_ub x hx i
      have h2 : 2 * CU ≤ B := by rw [hBdef]; exact le_max_left _ _
      linarith
  -- main conversion step, used in both pigeonhole branches
  have key : ∀ (c : σ → ℝ) (Y : Set (σ → ℤ)), Y ⊆ X₀ →
      (∀ x ∈ Y, ∀ i : σ, t x i ≤ c i) →
      ∀ x ∈ Y, ∀ i : σ, w.val (Lf i x) ≤ ‖x‖ ^ (c i) := by
    intro c Y hYX0 hc x hxY i
    have hxX0 : x ∈ X₀ := hYX0 hxY
    obtain ⟨hxX, hxe⟩ := (hX0mem x).mp hxX0
    have hxlogpos : 0 < Real.log ‖x‖ := hlogXpos x hxX0
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hwpos : 0 < w.val (Lf i x) := InfinitePlace.pos_iff.mpr (hnz x hxX i)
    have hle : t x i ≤ c i := hc x hxY i
    have h1 : Real.log (w.val (Lf i x)) ≤ c i * Real.log ‖x‖ := by
      have ht : t x i * Real.log ‖x‖ = Real.log (w.val (Lf i x)) := by
        show (Real.log (w.val (Lf i x)) / Real.log ‖x‖) * Real.log ‖x‖ = _
        rw [div_mul_cancel₀ _ hxlogpos.ne']
      have := mul_le_mul_of_nonneg_right hle hxlogpos.le
      rwa [ht] at this
    rw [← Real.log_rpow hxpos (c i)] at h1
    exact (Real.log_le_log_iff hwpos (Real.rpow_pos_of_pos hxpos (c i))).mp h1
  set S : Set (σ → ℝ) := t '' X₀ with hSdef
  by_cases hSinf : S.Infinite
  · -- infinitely many distinct exponent vectors: pigeonhole into a box
    let N : ℕ := ⌊(Fintype.card σ : ℝ) / ε⌋₊ + 1
    have hNpos : 0 < N := by simp [N]
    have hNε : (Fintype.card σ : ℝ) / N < ε := by
      have h1 : (Fintype.card σ : ℝ) / ε < (N : ℝ) := by
        have := Nat.lt_floor_add_one ((Fintype.card σ : ℝ) / ε)
        simpa [N] using this
      have h2 : (Fintype.card σ : ℝ) < (N : ℝ) * ε := by
        rw [div_lt_iff₀ hε] at h1; linarith
      rw [div_lt_iff₀ (by exact_mod_cast hNpos)]
      linarith
    have hbdd : ∀ y ∈ S, ∀ i : σ, |y i| ≤ B := by
      intro y hy i
      rw [hSdef] at hy
      obtain ⟨x, hxX0, rfl⟩ := hy
      exact ht_abs x hxX0 i
    obtain ⟨m, -, hm_inf⟩ := Commons.Topology.Box.box_pigeonhole N hNpos B S hSinf hbdd
    set box : Set (σ → ℝ) :=
      {y : σ → ℝ | ∀ i : σ, (m i : ℝ) / N ≤ y i ∧ y i < ((m i : ℝ) + 1) / N} with hboxdef
    have hm_inf' : (S ∩ box).Infinite := by rw [hboxdef]; exact hm_inf
    have hboxmem : ∀ y : σ → ℝ, y ∈ box ↔
        ∀ i : σ, (m i : ℝ) / N ≤ y i ∧ y i < ((m i : ℝ) + 1) / N := by
      intro y; rw [hboxdef, Set.mem_ofPred_eq]
    set c : σ → ℝ := fun i => ((m i : ℝ) + 1) / N with hcdef
    have hcsum : ∑ i : σ, c i < 0 := by
      obtain ⟨y, hy⟩ := hm_inf'.nonempty
      rw [Set.mem_inter_iff] at hy
      obtain ⟨hyS, hybox⟩ := hy
      have hyb := (hboxmem y).mp hybox
      have h1 : ∑ i : σ, c i ≤ ∑ i : σ, (y i + 1 / N) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hyb i
        have heqc : c i = (m i : ℝ) / N + 1 / N := by
          rw [hcdef]; ring
        rw [heqc]; linarith [hi.1]
      have h2 : ∑ i : σ, (y i + 1 / N)
          = (∑ i : σ, y i) + (Fintype.card σ : ℝ) * (1 / N) := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h3 : (Fintype.card σ : ℝ) * (1 / N) < ε := by
        have : (Fintype.card σ : ℝ) * (1 / N) = (Fintype.card σ : ℝ) / N := by ring
        rw [this]; exact hNε
      rw [hSdef] at hyS
      obtain ⟨x, hxX0, htx⟩ := hyS
      have h4 : ∑ i : σ, y i < -ε := by
        rw [← htx]
        exact hsumS x hxX0
      linarith
    set X' : Set (σ → ℤ) := X₀ ∩ {x : σ → ℤ | t x ∈ box} with hX'def
    have hX'inf : X'.Infinite := by
      have himg : t '' X' = S ∩ box := by
        ext y; constructor
        · rintro ⟨x, hx, rfl⟩
          rw [hX'def] at hx
          rw [Set.mem_inter_iff] at hx
          exact ⟨by rw [hSdef]; exact Set.mem_image_of_mem t hx.1, hx.2⟩
        · rintro ⟨hyS, hybox⟩
          rw [hSdef] at hyS
          obtain ⟨x, hxX0, rfl⟩ := hyS
          exact ⟨x, by
            rw [hX'def, Set.mem_inter_iff]
            exact ⟨hxX0, hybox⟩, rfl⟩
      by_contra hfin
      rw [Set.not_infinite] at hfin
      have : (S ∩ box).Finite := by rw [← himg]; exact Set.Finite.image t hfin
      exact hm_inf' this
    refine ⟨c, X', hcsum, ?_, hX'inf, ?_⟩
    · intro x hx
      rw [hX'def] at hx
      rw [Set.mem_inter_iff] at hx
      exact ((hX0mem x).mp hx.1).1
    · intro x hx i
      apply key c X' ?_ ?_ x hx i
      · intro z hz
        rw [hX'def] at hz
        rw [Set.mem_inter_iff] at hz
        exact hz.1
      · intro z hz j
        rw [hX'def, Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
        have hzb := (hboxmem (t z)).mp hz.2
        rw [hcdef]
        exact le_of_lt (hzb j).2
  · -- only finitely many distinct exponent vectors: one fibre is infinite
    have hSfin : S.Finite := Set.not_infinite.mp hSinf
    letI : Fintype ↥S := hSfin.fintype
    let A : ↥S → Set (σ → ℤ) := fun y => {x : σ → ℤ | x ∈ X₀ ∧ t x = y.1}
    have hcover : X₀ ⊆ ⋃ y : ↥S, A y := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨⟨t x, ?_⟩, hx, rfl⟩
      rw [hSdef]; exact Set.mem_image_of_mem t hx
    obtain ⟨y, hy⟩ := Commons.Set.Infinite.infinite_of_finite_cover hX₀inf A hcover
    have hyX0 : ∀ x ∈ X₀ ∩ A y, x ∈ X₀ := by
      intro x hx; rw [Set.mem_inter_iff] at hx; exact hx.1
    have hyc : ∑ i : σ, (y.1 : σ → ℝ) i < -ε := by
      obtain ⟨x, hx⟩ := hy.nonempty
      rw [Set.mem_inter_iff] at hx
      obtain ⟨hxX0, hxA⟩ := hx
      rw [Set.mem_ofPred_eq] at hxA
      rw [← hxA.2]
      exact hsumS x hxX0
    refine ⟨y.1, X₀ ∩ A y, by linarith [hyc, hε], ?_, hy, ?_⟩
    · intro x hx
      exact ((hX0mem x).mp (hyX0 x hx)).1
    · intro x hx i
      apply key y.1 (X₀ ∩ A y) hyX0 ?_ x hx i
      intro z hz j
      rw [Set.mem_inter_iff] at hz
      obtain ⟨-, hzA⟩ := hz
      rw [Set.mem_ofPred_eq] at hzA
      rw [hzA.2]

end Commons.NumberTheory.Height.NumberField
