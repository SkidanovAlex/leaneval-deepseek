import Mathlib
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Commons.Analysis.Intervals.exists_distant_of_finset

namespace Work.LinnikAreas.Zeta1Aux

/-- Elementary arithmetic: a real `x` whose absolute value lies outside `[T, T+3]` is at
distance at least `1` from every `T' ∈ [T+1, T+2]`, in either direction. -/
private theorem far_dist_arith {T T' x : ℝ} (hT : 1 ≤ T) (hlo : T + 1 ≤ T') (hhi : T' ≤ T + 2)
    (hx : |x| < T ∨ T + 3 < |x|) : 1 ≤ |x - T'| ∧ 1 ≤ |x + T'| := by
  rcases hx with h | h
  · obtain ⟨h1, h2⟩ := abs_lt.mp h
    constructor
    · rw [abs_of_nonpos (by linarith : x - T' ≤ 0)]
      linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ x + T')]
      linarith
  · rcases lt_abs.mp h with h3 | h4
    · constructor
      · rw [abs_of_nonneg (by linarith : 0 ≤ x - T')]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ x + T')]
        linarith
    · constructor
      · rw [abs_of_nonpos (by linarith : x - T' ≤ 0)]
        linarith
      · rw [abs_of_nonpos (by linarith : x + T' ≤ 0)]
        linarith

/-- **The combinatorial step.**  Given a finite set `S ⊂ ℝ` of "forbidden heights"
(closed under `x ↦ -x` for the zero heights in the window `T ≤ |Im| ≤ T+3`) of small
cardinality, there is `T' ∈ [T+1, T+2]` at distance at least `δ` from every zero height
of `ζ₁`, in both directions. -/
private theorem goodHeight_of_window_finset_aux
    {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {S : Finset ℝ}
    (hcard : 2 * δ * (S.card : ℝ) ≤ T + 2 - (T + 1))
    (hS : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → T ≤ |ρ.im| → |ρ.im| ≤ T + 3 →
      ρ.im ∈ S ∧ -ρ.im ∈ S) :
    ∃ T' : ℝ, T + 1 ≤ T' ∧ T' ≤ T + 2 ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - T'|) ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im + T'|) := by
  obtain ⟨T', hlo, hhi, hfar⟩ :=
    Commons.Analysis.Intervals.exists_distant_of_finset (S := S) (t := δ) (a := T + 1)
      (b := T + 2) hδ hcard
  have hfar_out : ∀ x : ℝ, |x| < T ∨ T + 3 < |x| → 1 ≤ |x - T'| ∧ 1 ≤ |x + T'| :=
    fun x hx => far_dist_arith hT hlo hhi hx
  refine ⟨T', hlo, hhi, ?_, ?_⟩
  · intro ρ hρ
    by_cases hwin : T ≤ |ρ.im| ∧ |ρ.im| ≤ T + 3
    · obtain ⟨h1, _⟩ := hS ρ hρ hwin.1 hwin.2
      calc δ ≤ |T' - ρ.im| := hfar ρ.im h1
        _ = |ρ.im - T'| := abs_sub_comm _ _
    · have hx : |ρ.im| < T ∨ T + 3 < |ρ.im| := by
        rcases lt_or_ge |ρ.im| T with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge (fun hc => hwin ⟨h, hc⟩))
      exact le_trans hδ1 (hfar_out ρ.im hx).1
  · intro ρ hρ
    by_cases hwin : T ≤ |ρ.im| ∧ |ρ.im| ≤ T + 3
    · obtain ⟨_, h2⟩ := hS ρ hρ hwin.1 hwin.2
      calc δ ≤ |T' - (-ρ.im)| := hfar (-ρ.im) h2
        _ = |ρ.im + T'| := by rw [show T' - (-ρ.im) = ρ.im + T' by ring]
    · have hx : |ρ.im| < T ∨ T + 3 < |ρ.im| := by
        rcases lt_or_ge |ρ.im| T with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge (fun hc => hwin ⟨h, hc⟩))
      exact le_trans hδ1 (hfar_out ρ.im hx).2

/-- Elementary logarithmic comparison: for `T ≥ 1`,
`log (T + 9/2) ≤ 2 log (T + 4)` and `log (T + 4) ≥ 1`. -/
private theorem goodHeight_log_arith_aux {T : ℝ} (hT : 1 ≤ T) :
    Real.log (T + 9 / 2) ≤ 2 * Real.log (T + 4) ∧ (1 : ℝ) ≤ Real.log (T + 4) := by
  have h4 : (0 : ℝ) < T + 4 := by linarith
  have h92 : (0 : ℝ) < T + 9 / 2 := by linarith
  constructor
  · have hsq : T + 9 / 2 ≤ (T + 4) ^ 2 := by nlinarith
    calc Real.log (T + 9 / 2) ≤ Real.log ((T + 4) ^ 2) := Real.log_le_log h92 hsq
      _ = 2 * Real.log (T + 4) := Real.log_pow (T + 4) 2
  · rw [Real.le_log_iff_exp_le h4]
    have h3 := Real.exp_one_lt_three
    linarith

/-- A finite-support function with non-negative integral values is dominated in cardinality
by its (finite) sum. -/
private lemma card_supp_le_finsum {G : ℂ → ℝ} (hGnn : ∀ u, 0 ≤ G u)
    (hGint : ∀ u, ∃ m : ℤ, G u = (m : ℝ)) (hfin : (Function.support G).Finite) :
    ((hfin.toFinset).card : ℝ) ≤ ∑ᶠ u : ℂ, G u := by
  have hsum_eq : (∑ᶠ u : ℂ, G u) = ∑ u ∈ hfin.toFinset, G u := by
    refine finsum_eq_sum_of_support_subset G ?_
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hx
  rw [hsum_eq]
  calc ((hfin.toFinset).card : ℝ) = ∑ _u ∈ hfin.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ hfin.toFinset, G u := by
        refine Finset.sum_le_sum ?_
        intro u hu
        have hGne : G u ≠ 0 := by
          have hmem : u ∈ hfin.toFinset := hu
          rw [Set.Finite.mem_toFinset] at hmem
          simpa [Function.mem_support] using hmem
        obtain ⟨m, hm⟩ := hGint u
        have hm0 : (0 : ℤ) ≤ m := by
          have : (0 : ℝ) ≤ (m : ℝ) := by rw [← hm]; exact hGnn u
          exact_mod_cast this
        have hmne : m ≠ 0 := by
          intro h0
          exact hGne (by rw [hm, h0]; norm_num)
        have hm1 : (1 : ℤ) ≤ m := by omega
        rw [hm]
        exact_mod_cast hm1

/-- A zero of `ζ₁` inside a closed ball is in the support of the divisor. -/
private lemma zeta1_div_ne_zero {R : ℝ} {ρ : ℂ}
    (hρU : ρ ∈ Metric.closedBall (0 : ℂ) R) (hρ : riemannZeta₁ ρ = 0) :
    (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) R)) ρ ≠ 0 :=
  Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero differentiable_riemannZeta₁
    (fun h0 => by
      have h1 : riemannZeta₁ 1 = (0 : ℂ) := by simpa using congrFun h0 1
      rw [riemannZeta₁_one] at h1
      exact one_ne_zero h1) hρU hρ

/-- The divisor coefficient of `ζ₁` at a zero inside the ball is a non-zero real. -/
private lemma zeta1_div_cast_ne_zero {R : ℝ} {ρ : ℂ}
    (hρU : ρ ∈ Metric.closedBall (0 : ℂ) R) (hρ : riemannZeta₁ ρ = 0) :
    (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) R)) ρ : ℤ) : ℝ) ≠ 0 :=
  fun h0 => zeta1_div_ne_zero hρU hρ (by exact_mod_cast h0)

/-- The divisor coefficient of the entire function `ζ₁`, cast to `ℝ`, is non-negative. -/
private lemma zeta1_div_cast_nonneg (R : ℝ) (u : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) R) u : ℤ) : ℝ) := by
  have han : AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have h := MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := riemannZeta₁)
    (U := Metric.closedBall (0 : ℂ) R) han
  exact_mod_cast (h u)

/-- The divisor coefficients of `ζ₁` (cast to `ℝ`) have finite support on a closed ball. -/
private lemma zeta1_div_finsupport (R : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ =>
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) R) u : ℤ) : ℝ)) := by
  have hfinZ : (Function.support
      (fun u : ℂ =>
        (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) R) u : ℤ))).Finite := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall (0 : ℂ) R))
  refine hfinZ.subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  exact fun hz => hu (by exact_mod_cast hz)

/-- **The zero heights in the window `T ≤ |Im| ≤ T + 3` lie in a small finite set.**

Take `t = T + 3/2`.  The two sums in `hcount` (at `t` and at `-t`) count, with multiplicity,
the zeros with `Im ∈ [T, T+3]` and those with `Im ∈ [-T-3, -T]`; the union `Z` of the
supports of the corresponding summands has at most `2 * C₀ * log (T + 9/2)` elements, and
the set `S := Im(Z) ∪ (-Im)(Z)` has at most twice as many.  Every zero `ρ` with
`|ρ.im| ∈ [T, T+3]` satisfies `|ρ.im ∓ t| ≤ 3` and lies in the divisor ball, so `ρ ∈ Z`. -/
private theorem zeta1_window_finset_count_tmp
    (hstrip : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    {C₀ : ℝ} (hC₀pos : 0 < C₀)
    (hcount : ∀ t : ℝ, 1 ≤ |t| →
      (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) ≤ C₀ * Real.log (|t| + 3))
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ S : Finset ℝ, (S.card : ℝ) ≤ 4 * C₀ * Real.log (T + 9 / 2) ∧
      ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → T ≤ |ρ.im| → |ρ.im| ≤ T + 3 →
        ρ.im ∈ S ∧ -ρ.im ∈ S := by
  classical
  set t : ℝ := T + 3 / 2 with htdef
  have htpos : 0 < t := by rw [htdef]; linarith
  have htabs : |t| = t := abs_of_pos htpos
  have ht1 : 1 ≤ |t| := by rw [htabs, htdef]; linarith
  have htn1 : 1 ≤ |-t| := by rw [abs_neg]; exact ht1
  set F : ℂ → ℝ := (fun u =>
    (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ))
    with hFdef
  set Gp : ℂ → ℝ := (fun u => F u * (if |u.im - t| ≤ 3 then (1 : ℝ) else 0)) with hGpdef
  set Gm : ℂ → ℝ := (fun u => F u * (if |u.im + t| ≤ 3 then (1 : ℝ) else 0)) with hGmdef
  have hFnn : ∀ u : ℂ, (0 : ℝ) ≤ F u := by
    intro u
    rw [hFdef]
    exact zeta1_div_cast_nonneg (|t| + 6) u
  have hsumP : (∑ᶠ u : ℂ, Gp u) ≤ C₀ * Real.log (|t| + 3) := by
    have h := hcount t ht1
    rw [hGpdef, hFdef]
    exact h
  have hsumM : (∑ᶠ u : ℂ, Gm u) ≤ C₀ * Real.log (|t| + 3) := by
    have h := hcount (-t) htn1
    rw [abs_neg] at h
    simp only [sub_neg_eq_add] at h
    rw [hGmdef, hFdef]
    exact h
  have hfinP : (Function.support Gp).Finite := by
    rw [hGpdef, hFdef]
    exact Function.HasFiniteSupport.mul_left (zeta1_div_finsupport (|t| + 6))
      (fun u : ℂ => if |u.im - t| ≤ 3 then (1 : ℝ) else 0)
  have hfinM : (Function.support Gm).Finite := by
    rw [hGmdef, hFdef]
    exact Function.HasFiniteSupport.mul_left (zeta1_div_finsupport (|t| + 6))
      (fun u : ℂ => if |u.im + t| ≤ 3 then (1 : ℝ) else 0)
  have hGpnn : ∀ u : ℂ, (0 : ℝ) ≤ Gp u := by
    intro u
    have h1 : (0 : ℝ) ≤ (if |u.im - t| ≤ 3 then (1 : ℝ) else 0) := by split <;> norm_num
    rw [hGpdef]
    simpa using mul_nonneg (hFnn u) h1
  have hGmnn : ∀ u : ℂ, (0 : ℝ) ≤ Gm u := by
    intro u
    have h1 : (0 : ℝ) ≤ (if |u.im + t| ≤ 3 then (1 : ℝ) else 0) := by split <;> norm_num
    rw [hGmdef]
    simpa using mul_nonneg (hFnn u) h1
  have hGpint : ∀ u : ℂ, ∃ m : ℤ, Gp u = (m : ℝ) := by
    intro u
    by_cases hc : |u.im - t| ≤ 3
    · exact ⟨MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6)) u,
        by rw [hGpdef, hFdef]; simp [hc]⟩
    · exact ⟨0, by rw [hGpdef, hFdef]; simp [hc]⟩
  have hGmint : ∀ u : ℂ, ∃ m : ℤ, Gm u = (m : ℝ) := by
    intro u
    by_cases hc : |u.im + t| ≤ 3
    · exact ⟨MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6)) u,
        by rw [hGmdef, hFdef]; simp [hc]⟩
    · exact ⟨0, by rw [hGmdef, hFdef]; simp [hc]⟩
  have hPcard : ((hfinP.toFinset).card : ℝ) ≤ ∑ᶠ u : ℂ, Gp u :=
    card_supp_le_finsum hGpnn hGpint hfinP
  have hMcard : ((hfinM.toFinset).card : ℝ) ≤ ∑ᶠ u : ℂ, Gm u :=
    card_supp_le_finsum hGmnn hGmint hfinM
  have hFne : ∀ u : ℂ, u ∈ Metric.closedBall (0 : ℂ) (|t| + 6) → riemannZeta₁ u = 0 → F u ≠ 0 := by
    intro u hu hz
    rw [hFdef]
    exact zeta1_div_cast_ne_zero hu hz
  let Z : Finset ℂ := hfinP.toFinset ∪ hfinM.toFinset
  have hZdef : Z = hfinP.toFinset ∪ hfinM.toFinset := rfl
  let S : Finset ℝ := Z.image (fun u : ℂ => u.im) ∪ Z.image (fun u : ℂ => -u.im)
  have hSdef : S = Z.image (fun u : ℂ => u.im) ∪ Z.image (fun u : ℂ => -u.im) := rfl
  refine ⟨S, ?_, ?_⟩
  · have hZcard : (Z.card : ℝ) ≤ 2 * (C₀ * Real.log (|t| + 3)) := by
      rw [hZdef]
      have h1 : (hfinP.toFinset ∪ hfinM.toFinset).card ≤
          hfinP.toFinset.card + hfinM.toFinset.card := Finset.card_union_le _ _
      have h1' : ((hfinP.toFinset ∪ hfinM.toFinset).card : ℝ) ≤
          (hfinP.toFinset.card : ℝ) + (hfinM.toFinset.card : ℝ) := by exact_mod_cast h1
      linarith
    have hScard_nat : (Z.image (fun u : ℂ => u.im) ∪ Z.image (fun u : ℂ => -u.im)).card ≤
        2 * Z.card := by
      have h1 := Finset.card_union_le (Z.image (fun u : ℂ => u.im)) (Z.image (fun u : ℂ => -u.im))
      have h2 := Finset.card_image_le (s := Z) (f := fun u : ℂ => u.im)
      have h3 := Finset.card_image_le (s := Z) (f := fun u : ℂ => -u.im)
      omega
    have htlog : |t| + 3 = T + 9 / 2 := by rw [htabs, htdef]; ring
    rw [hSdef]
    calc ((Z.image (fun u : ℂ => u.im) ∪ Z.image (fun u : ℂ => -u.im)).card : ℝ)
        ≤ ((2 * Z.card : ℕ) : ℝ) := by exact_mod_cast hScard_nat
      _ = 2 * (Z.card : ℝ) := by push_cast; ring
      _ ≤ 2 * (2 * (C₀ * Real.log (|t| + 3))) := by linarith
      _ = 4 * C₀ * Real.log (T + 9 / 2) := by rw [htlog]; ring
  · intro ρ hρ h1 h2
    have him : ρ.im ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h1
      linarith
    obtain ⟨hre0, hre1⟩ := hstrip ρ hρ him
    have hball : ρ ∈ Metric.closedBall (0 : ℂ) (|t| + 6) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hre : |ρ.re| ≤ 1 := by rw [abs_of_pos hre0]; exact le_of_lt hre1
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ ≤ 1 + (T + 3) := by linarith
        _ ≤ |t| + 6 := by rw [htabs, htdef]; linarith
    have hwin : |ρ.im - t| ≤ 3 ∨ |ρ.im + t| ≤ 3 := by
      rcases lt_or_ge 0 ρ.im with hpos | hneg
      · left
        rw [abs_of_nonneg (le_of_lt hpos)] at h1 h2
        rw [htdef, abs_le]
        constructor <;> linarith
      · right
        rw [abs_of_nonpos hneg] at h1 h2
        rw [htdef, abs_le]
        constructor <;> linarith
    have hmemZ : ρ ∈ Z := by
      rw [hZdef, Finset.mem_union]
      rcases hwin with hw | hw
      · left
        rw [Set.Finite.mem_toFinset, Function.mem_support]
        have hEq : Gp ρ = F ρ := by simp only [hGpdef, if_pos hw, mul_one]
        rw [hEq]
        exact hFne ρ hball hρ
      · right
        rw [Set.Finite.mem_toFinset, Function.mem_support]
        have hEq : Gm ρ = F ρ := by simp only [hGmdef, if_pos hw, mul_one]
        rw [hEq]
        exact hFne ρ hball hρ
    constructor
    · rw [hSdef]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨ρ, hmemZ, rfl⟩))
    · rw [hSdef]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨ρ, hmemZ, rfl⟩))

/-- **A good height for `ζ₁`.**

There is `c > 0` such that for every `T ≥ 1` one can choose `T' ∈ [T+1, T+2]` whose directed
distances to every zero height of `riemannZeta₁` (both `T'` and `-T'`) are at least
`c / log (T' + 3)`.

Route (as in `Commons.NumberTheory.DirichletCharacter.goodHeight_separated`, but for `ζ₁`):
put `t₀ = T + 3/2` and let `Z` be the (finite) union of the supports of the two sums appearing
in `hcount` at `t = t₀` and `t = -t₀`; every zero `ρ` with `|ρ.im| ∈ [T, T+3]` lies in `Z`:
its imaginary part is non-zero, so by `hstrip` `Re ρ ∈ (0,1)` and hence `‖ρ‖ ≤ t₀ + 4 ≤ t₀ + 6`,
while `|ρ.im ∓ t₀| ≤ 3`.  Set `S := Z.image im ∪ Z.image (-im)`, so
`S.card ≤ 2 * Z.card ≤ 4 * C₀ * log (t₀ + 3)`, and apply
`Commons.Analysis.Intervals.exists_distant_of_finset` on `[T+1, T+2]` with
`δ = c / log (T + 4)`, `c := min (1 / (16 * C₀)) (1 / 2)`, so that
`2 * δ * S.card ≤ 1`.  A zero `ρ` with `|ρ.im| ∈ [T, T+3]` has `ρ.im ∈ S` and `-ρ.im ∈ S`,
giving both inequalities; a zero with `|ρ.im| < T` or `|ρ.im| > T+3` is at distance at least
`1 ≥ δ ≥ c / log (T' + 3)` from both `T'` and `-T'` by the elementary arithmetic of
`T' ∈ [T+1, T+2]` (note `δ ≤ 1` because `c ≤ 1 ≤ log (T + 4)`). -/
theorem zeta1_goodHeight_pointwise
    (hstrip : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    (hcount : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) ≤ C₀ * Real.log (|t| + 3)) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T → ∃ T' : ℝ, T + 1 ≤ T' ∧ T' ≤ T + 2 ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → c / Real.log (T' + 3) ≤ |ρ.im - T'|) ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → c / Real.log (T' + 3) ≤ |ρ.im + T'|) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀count⟩ := hcount
  set cf : ℝ := min (1 / (16 * C₀)) (1 / 2) with hcfdef
  have hcfpos : 0 < cf := by rw [hcfdef]; exact lt_min (by positivity) (by norm_num)
  have hcfle : cf ≤ 1 / (16 * C₀) := by rw [hcfdef]; exact min_le_left _ _
  have hcfle2 : cf ≤ 1 / 2 := by rw [hcfdef]; exact min_le_right _ _
  have hcfle1 : cf ≤ 1 := by linarith
  refine ⟨cf, hcfpos, ?_⟩
  intro T hT
  obtain ⟨S, hScard, hS⟩ := zeta1_window_finset_count_tmp hstrip hC₀pos hC₀count hT
  obtain ⟨harith1, harith2⟩ := goodHeight_log_arith_aux hT
  have hlogpos : 0 < Real.log (T + 4) := by linarith
  set δ : ℝ := cf / Real.log (T + 4) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hcfpos hlogpos
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    have h := div_le_div_of_nonneg_left (le_of_lt hcfpos) (by norm_num : (0:ℝ) < 1) harith2
    rw [div_one] at h
    linarith
  have hcard : 2 * δ * (S.card : ℝ) ≤ T + 2 - (T + 1) := by
    rw [show T + 2 - (T + 1) = (1 : ℝ) by ring]
    have hnonneg1 : (0 : ℝ) ≤ 2 * (cf / Real.log (T + 4)) := by
      have h0 : (0 : ℝ) ≤ cf / Real.log (T + 4) := div_nonneg (le_of_lt hcfpos) (le_of_lt hlogpos)
      linarith
    have hnonneg2 : (0 : ℝ) ≤ 8 * C₀ * cf := by nlinarith [hC₀pos, hcfpos]
    have hratio : Real.log (T + 9 / 2) / Real.log (T + 4) ≤ 2 := by
      rw [div_le_iff₀ hlogpos]
      linarith
    have hCcf : C₀ * cf ≤ 1 / 16 := by
      have h := mul_le_mul_of_nonneg_left hcfle (le_of_lt hC₀pos)
      have h2 : C₀ * (1 / (16 * C₀)) = 1 / 16 := by field_simp
      linarith [h, h2.ge, h2.le]
    calc 2 * δ * (S.card : ℝ)
        = 2 * (cf / Real.log (T + 4)) * (S.card : ℝ) := by rw [hδdef]
      _ ≤ 2 * (cf / Real.log (T + 4)) * (4 * C₀ * Real.log (T + 9 / 2)) :=
            mul_le_mul_of_nonneg_left hScard hnonneg1
      _ = 8 * C₀ * cf * (Real.log (T + 9 / 2) / Real.log (T + 4)) := by
            rw [div_eq_mul_inv]; ring
      _ ≤ 8 * C₀ * cf * 2 := mul_le_mul_of_nonneg_left hratio hnonneg2
      _ = 16 * (C₀ * cf) := by ring
      _ ≤ 16 * (1 / 16) := by linarith
      _ = 1 := by norm_num
  obtain ⟨T', hlo, hhi, hfar1, hfar2⟩ :=
    goodHeight_of_window_finset_aux hT hδpos hδ1 hcard hS
  have hcmp : cf / Real.log (T' + 3) ≤ δ := by
    rw [hδdef]
    have hle : T + 4 ≤ T' + 3 := by linarith
    exact div_le_div_of_nonneg_left (le_of_lt hcfpos) hlogpos
      (Real.log_le_log (by linarith : (0:ℝ) < T + 4) hle)
  exact ⟨T', hlo, hhi, fun ρ hρ => le_trans hcmp (hfar1 ρ hρ),
    fun ρ hρ => le_trans hcmp (hfar2 ρ hρ)⟩

end Work.LinnikAreas.Zeta1Aux
