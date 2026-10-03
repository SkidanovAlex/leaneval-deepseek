import Mathlib

/-!
# The level-set bound for a real polynomial

For a real polynomial `P` of degree `n = P.natDegree ≥ 1` there is a constant `C > 0` with

  `volume {t : ℝ | |P.eval t| ≤ ε} ≤ C * ε ^ ((n : ℝ)⁻¹)`   for every `ε > 0`.

This is the elementary "sublevel set of a polynomial grows like `ε ^ (1/n)`" estimate which
underlies Weyl-type / circle-method arguments (it is used, e.g., to bound the measure of the set
of `θ` on which a polynomial phase is small).

**Proof.**  Factor `P` over `ℂ`.  With `Q = P.map (algebraMap ℝ ℂ)` one has, at any real `x`,

  `|P.eval x| = ‖Q.eval x‖ = |P.leadingCoeff| * ∏_{z ∈ Q.roots} ‖x - z‖`

and since `‖x - z‖ ≥ |x - z.re|`, putting `ρ = (ε / |P.leadingCoeff|) ^ (1/n)` we get

  `{t | |P.eval t| ≤ ε} ⊆ ⋃_{z ∈ Q.roots} [z.re - ρ, z.re + ρ]`,

because if every `|t - z.re| > ρ` then `∏ ‖t - z‖ ≥ ∏ |t - z.re| > ρ ^ n = ε / |P.leadingCoeff|`
(strict comparison of the multiset products, using `ρ > 0`), hence `|P.eval t| > ε`.
Finally `Q.roots.card = P.natDegree` and the union is bounded by `card · 2ρ`, giving the constant
`C = 2 n |P.leadingCoeff| ^ (-(1/n))`.
-/

namespace Work.A3

open MeasureTheory

/-- The norm of a product of complex numbers is the product of the norms. -/
private lemma norm_multiset_prod_complex {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun a => ‖f a‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [Multiset.map_cons, Multiset.prod_cons, ih]

theorem real_poly_levelSet_volume_le (P : Polynomial ℝ) (hd : 1 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      MeasureTheory.volume {t : ℝ | |P.eval t| ≤ ε}
        ≤ ENNReal.ofReal (C * ε ^ ((P.natDegree : ℝ)⁻¹)) := by
  classical
  have hP : P ≠ 0 := by rintro rfl; simp at hd
  have ha : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have han : 0 < |P.leadingCoeff| := abs_pos.mpr ha
  have hn0 : 0 < P.natDegree := by omega
  have hnne : P.natDegree ≠ 0 := by omega
  set C : ℝ := 2 * (P.natDegree : ℝ) * |P.leadingCoeff| ^ (-((P.natDegree : ℝ)⁻¹)) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 0 < |P.leadingCoeff| ^ (-((P.natDegree : ℝ)⁻¹)) := Real.rpow_pos_of_pos han _
    have h2 : (0:ℝ) < (P.natDegree : ℝ) := by exact_mod_cast hn0
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro ε hε
  set ρ : ℝ := (ε / |P.leadingCoeff|) ^ ((P.natDegree : ℝ)⁻¹) with hρdef
  have hεa : 0 < ε / |P.leadingCoeff| := div_pos hε han
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hεa _
  have hρpow : ρ ^ P.natDegree = ε / |P.leadingCoeff| :=
    Real.rpow_inv_natCast_pow (le_of_lt hεa) hnne
  set Q : Polynomial ℂ := P.map (algebraMap ℝ ℂ) with hQdef
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hcard : Q.roots.card = P.natDegree := by
    rw [← hsplit.natDegree_eq_card_roots, hQdef]
    exact Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective P
  have hne : Q.roots ≠ 0 := by
    intro h; rw [h] at hcard; simp at hcard; omega
  have hkey : ∀ x : ℝ,
      |P.eval x| = |P.leadingCoeff| * (Q.roots.map (fun z => ‖(x:ℂ) - z‖)).prod := by
    intro x
    have h1 : Q.eval (x:ℂ) = Q.leadingCoeff * (Q.roots.map (fun z => (x:ℂ) - z)).prod :=
      hsplit.eval_eq_prod_roots (x:ℂ)
    have h2 : Q.eval (x:ℂ) = ((P.eval x : ℝ) : ℂ) := by
      rw [hQdef, Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
    have h3 : ‖Q.eval (x:ℂ)‖ = |P.eval x| := by
      rw [h2, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
    have h4 : ‖(Q.roots.map (fun z => (x:ℂ) - z)).prod‖
        = (Q.roots.map (fun z => ‖(x:ℂ) - z‖)).prod :=
      norm_multiset_prod_complex _ _
    have h5 : ‖Q.leadingCoeff‖ = |P.leadingCoeff| := by
      have h5a : Q.leadingCoeff = ((P.leadingCoeff : ℝ) : ℂ) := by
        rw [hQdef, Polynomial.leadingCoeff_map_of_injective Complex.ofReal_injective]
        rfl
      rw [h5a, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
    rw [← h3, h1, norm_mul, h4, h5]
  have hsubset : {t : ℝ | |P.eval t| ≤ ε} ⊆
      ⋃ z ∈ Q.roots.toFinset, Set.Icc (z.re - ρ) (z.re + ρ) := by
    intro t ht
    by_contra hnot
    have hgt : ∀ z ∈ Q.roots, ρ < ‖(t:ℂ) - z‖ := by
      intro z hz
      have hz' : z ∈ Q.roots.toFinset := Multiset.mem_toFinset.mpr hz
      have hmem : t ∉ Set.Icc (z.re - ρ) (z.re + ρ) :=
        fun hc => hnot (Set.mem_iUnion₂.mpr ⟨z, hz', hc⟩)
      have hlt : ρ < |t - z.re| := by
        have h' : ¬ |t - z.re| ≤ ρ := fun h =>
          hmem (Set.mem_Icc.mpr ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩)
        exact not_le.mp h'
      calc ρ < |t - z.re| := hlt
        _ ≤ ‖(t:ℂ) - z‖ := by simpa using Complex.abs_re_le_norm ((t:ℂ) - z)
    have hprod : ρ ^ Q.roots.card < (Q.roots.map (fun z => ‖(t:ℂ) - z‖)).prod := by
      have h1 : (Q.roots.map (fun _ : ℂ => ρ)).prod = ρ ^ Q.roots.card := by
        rw [Multiset.map_const', Multiset.prod_replicate]
      rw [← h1]
      exact Multiset.prod_map_lt_prod_map hne (fun _ : ℂ => ρ) (fun z => ‖(t:ℂ) - z‖)
        (fun _ _ => hρpos) (fun z hz => hgt z hz)
    have hE : ε < |P.eval t| := by
      have h2 : |P.leadingCoeff| * ρ ^ Q.roots.card
          < |P.leadingCoeff| * (Q.roots.map (fun z => ‖(t:ℂ) - z‖)).prod :=
        mul_lt_mul_of_pos_left hprod han
      rw [← hkey t] at h2
      have h3 : |P.leadingCoeff| * ρ ^ Q.roots.card = ε := by
        rw [hcard, hρpow, mul_comm, div_mul_cancel₀ _ (ne_of_gt han)]
      linarith
    exact absurd ht (not_le.mpr hE)
  have hcardle : Q.roots.toFinset.card ≤ P.natDegree :=
    le_trans (Multiset.toFinset_card_le Q.roots) (le_of_eq hcard)
  calc MeasureTheory.volume {t : ℝ | |P.eval t| ≤ ε}
      ≤ MeasureTheory.volume (⋃ z ∈ Q.roots.toFinset, Set.Icc (z.re - ρ) (z.re + ρ)) :=
        measure_mono hsubset
    _ ≤ ∑ z ∈ Q.roots.toFinset, MeasureTheory.volume (Set.Icc (z.re - ρ) (z.re + ρ)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ z ∈ Q.roots.toFinset, ENNReal.ofReal (2 * ρ) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Real.volume_Icc]
        ring_nf
    _ = ENNReal.ofReal ((Q.roots.toFinset.card : ℝ) * (2 * ρ)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (s := Q.roots.toFinset) (f := fun _ => 2 * ρ)
          (fun z hz => by positivity)]
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((P.natDegree : ℝ) * (2 * ρ)) := by
        apply ENNReal.ofReal_le_ofReal
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcardle
    _ = ENNReal.ofReal (C * ε ^ ((P.natDegree : ℝ)⁻¹)) := by
        congr 1
        rw [hCdef, hρdef, Real.div_rpow (le_of_lt hε) (le_of_lt han),
          Real.rpow_neg (le_of_lt han), div_eq_mul_inv]
        ring

end Work.A3
