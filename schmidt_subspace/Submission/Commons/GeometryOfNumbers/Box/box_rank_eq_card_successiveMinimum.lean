import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.Basic
import Submission.Commons.GeometryOfNumbers.Box.finite_int_points_box
import Submission.Commons.GeometryOfNumbers.Box.eq_card_sInf_of_monotone

namespace Commons.GeometryOfNumbers.Box

/-!
# The rank of the approximation domain is the number of successive minima below the scale

`L : Fin N → Fin N → ℂ` is an invertible system of `N` linear forms in `N` variables, `Q ≥ 1`
and `c : Fin N → ℝ`.  The box at scale `t ≥ 0` is

  `box L c Q t := {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}`

with `ℚ`-rank `rankBox t := finrank ℚ (span ℚ (image of box L c Q t in ℚ^N))`, and the box
successive minima are

  `lamBox j := sInf {t : ℝ | 0 ≤ t ∧ (j+1) ≤ rankBox t}`.

Then for every scale `t`, the rank of the box at that scale is exactly the number of successive
minima which are at most `t`:

  `rankBox t = #{j : lamBox j ≤ t}`.

This is the standard dictionary between the two definitions of successive minima ("rank jumps"
and "minimal scaling admitting `j` independent points"), and it is what identifies the
approximation domain `V(Q) = span(box L c Q 1)` with the span of the first
`rankBox 1` realising vectors.  The proof is by monotonicity in `t`: `rankBox` is monotone and
takes integer values, and `lamBox j` is the threshold at which the rank first reaches `j+1`
(note `j ≤ rankBox t ↔ lamBox (j-1) ≤ t` for `j ≥ 1`, with the `sInf` formulation, using that
`rankBox` is right-monotone and that the sets `{t | 0 ≤ t ∧ j+1 ≤ rankBox t}` are
upward closed).
-/
open scoped BigOperators

/-- The approximation box at scale `t`. -/
private noncomputable def bSet {N : ℕ} (L : Fin N → Fin N → ℂ) (Q : ℝ) (c : Fin N → ℝ)
    (t : ℝ) : Set (Fin N → ℤ) :=
  {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}

/-- The image of the box in `ℚ^N`. -/
private noncomputable def iSet {N : ℕ} (L : Fin N → Fin N → ℂ) (Q : ℝ) (c : Fin N → ℝ)
    (t : ℝ) : Set (Fin N → ℚ) :=
  Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ)) (bSet L Q c t)

/-- The `ℚ`-rank of the approximation box at scale `t`. -/
private noncomputable def rBox {N : ℕ} (L : Fin N → Fin N → ℂ) (Q : ℝ) (c : Fin N → ℝ)
    (t : ℝ) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (iSet L Q c t))

/-- The box is monotone in the scale. -/
private lemma bSet_mono {N : ℕ} (L : Fin N → Fin N → ℂ) (Q : ℝ) (hQ : 1 ≤ Q) (c : Fin N → ℝ)
    {t t' : ℝ} (htt : t ≤ t') : bSet L Q c t ⊆ bSet L Q c t' := by
  intro y hy i
  have hQc : 0 ≤ Q ^ (c i) := Real.rpow_nonneg (le_trans zero_le_one hQ) _
  calc ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i) := hy i
    _ ≤ t' * Q ^ (c i) := mul_le_mul_of_nonneg_right htt hQc

/-- The rank of the box is monotone in the scale. -/
private lemma rBox_mono {N : ℕ} (L : Fin N → Fin N → ℂ) (Q : ℝ) (hQ : 1 ≤ Q) (c : Fin N → ℝ)
    {t t' : ℝ} (htt : t ≤ t') : rBox L Q c t ≤ rBox L Q c t' := by
  unfold rBox iSet
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, bSet_mono L Q hQ c htt hy, rfl⟩

/-- The rank of the box is at most `N`. -/
private lemma rBox_le {N : ℕ} (L : Fin N → Fin N → ℂ) (Q : ℝ) (c : Fin N → ℝ) (t : ℝ) :
    rBox L Q c t ≤ N := by
  unfold rBox
  calc Module.finrank ℚ (Submodule.span ℚ (iSet L Q c t))
      ≤ Module.finrank ℚ (⊤ : Submodule ℚ (Fin N → ℚ)) := Submodule.finrank_mono le_top
    _ = N := by rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private lemma bSet_single_cast (N : ℕ) (m : Fin N) :
    (fun k => ((Pi.single m (1:ℤ) : Fin N → ℤ) k : ℚ)) = (Pi.single m (1:ℚ) : Fin N → ℚ) := by
  funext k
  by_cases hk : k = m
  · subst hk; rw [Pi.single_eq_same, Pi.single_eq_same]; norm_num
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk]; norm_num

private lemma bSet_sum_single (N : ℕ) (L : Fin N → Fin N → ℂ) (i m : Fin N) :
    (∑ k, L i k * ((Pi.single m (1:ℤ) : Fin N → ℤ) k : ℂ)) = L i m := by
  rw [Finset.sum_eq_single m]
  · rw [Pi.single_eq_same]; norm_num
  · intro b _ hbm
    rw [Pi.single_eq_of_ne hbm]
    simp
  · intro hm; exact absurd (Finset.mem_univ m) hm

/-- For large enough scale the box attains full rank `N`. -/
private lemma rBox_top {N : ℕ} (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (Q : ℝ) (hQ : 1 ≤ Q)
    (c : Fin N → ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ rBox L Q c t = N := by
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
  set T : ℝ := max 0 (∑ p : Fin N × Fin N, ‖L p.1 p.2‖ * Q ^ (-(c p.1))) with hT
  have hT0 : 0 ≤ T := le_max_left _ _
  refine ⟨T, hT0, ?_⟩
  have hstep : ∀ m : Fin N, (Pi.single m (1:ℤ) : Fin N → ℤ) ∈ bSet L Q c T := by
    intro m i
    show ‖∑ k, L i k * ((Pi.single m (1:ℤ) : Fin N → ℤ) k : ℂ)‖ ≤ T * Q ^ (c i)
    rw [bSet_sum_single]
    have hle : ‖L i m‖ * Q ^ (-(c i)) ≤ T := by
      have h1 : ‖L i m‖ * Q ^ (-(c i)) ≤
          ∑ p : Fin N × Fin N, ‖L p.1 p.2‖ * Q ^ (-(c p.1)) := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun p : Fin N × Fin N => ‖L p.1 p.2‖ * Q ^ (-(c p.1))) ?_
          (Finset.mem_univ (i, m))
        intro p _
        exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hQpos.le _)
      exact le_trans h1 (le_max_right _ _)
    have hrw : Q ^ (-(c i)) * Q ^ (c i) = 1 := by
      rw [← Real.rpow_add hQpos]; simp
    calc ‖L i m‖ = ‖L i m‖ * (Q ^ (-(c i)) * Q ^ (c i)) := by rw [hrw, mul_one]
      _ = (‖L i m‖ * Q ^ (-(c i))) * Q ^ (c i) := by ring
      _ ≤ T * Q ^ (c i) := mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hQpos.le _)
  have hspan : (⊤ : Submodule ℚ (Fin N → ℚ)) ≤ Submodule.span ℚ (iSet L Q c T) := by
    rw [← (Pi.basisFun ℚ (Fin N)).span_eq]
    apply Submodule.span_mono
    rintro x ⟨m, rfl⟩
    refine ⟨(Pi.single m (1:ℤ) : Fin N → ℤ), hstep m, ?_⟩
    dsimp only
    rw [bSet_single_cast, Pi.basisFun_apply]
  unfold rBox
  have hle : Module.finrank ℚ (Submodule.span ℚ (iSet L Q c T)) ≤ N := by
    calc Module.finrank ℚ (Submodule.span ℚ (iSet L Q c T))
        ≤ Module.finrank ℚ (⊤ : Submodule ℚ (Fin N → ℚ)) := Submodule.finrank_mono le_top
      _ = N := by rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hge : N ≤ Module.finrank ℚ (Submodule.span ℚ (iSet L Q c T)) := by
    have := Submodule.finrank_mono hspan
    rwa [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  omega

/-- The scale at which the point `y` enters the box: `y ∈ box t ↔ tau y ≤ t`. -/
private noncomputable def tau {N : ℕ} (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (Q : ℝ)
    (c : Fin N → ℝ) (y : Fin N → ℤ) : ℝ :=
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  Finset.univ.sup' Finset.univ_nonempty (fun i => ‖∑ k, L i k * (y k : ℂ)‖ / Q ^ (c i))

private lemma mem_bSet_iff_tau {N : ℕ} (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (Q : ℝ) (hQ : 1 ≤ Q)
    (c : Fin N → ℝ) (y : Fin N → ℤ) (s : ℝ) :
    y ∈ bSet L Q c s ↔ tau hN L Q c y ≤ s := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hunf : tau hN L Q c y =
      Finset.univ.sup' Finset.univ_nonempty (fun i => ‖∑ k, L i k * (y k : ℂ)‖ / Q ^ (c i)) := by
    rw [tau]
  rw [bSet, Set.mem_setOf_eq, hunf, Finset.sup'_le_iff]
  constructor
  · intro h i _
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hQpos _)).mpr (h i)
  · intro h i
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hQpos _)).mp (h i (Finset.mem_univ i))

/-- Right-constancy of the rank: locally to the right of any scale the rank is constant. -/
private lemma rBox_stab {N : ℕ} (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (Q : ℝ) (hQ : 1 ≤ Q)
    (c : Fin N → ℝ)
    (hfin : ∀ (M : Fin N → ℝ),
      {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ M i}.Finite) :
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ t' ∈ Set.Icc t (t + ε), rBox L Q c t' = rBox L Q c t := by
  classical
  intro t
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hYfin : (bSet L Q c (t+1)).Finite := hfin (fun i => (t+1) * Q ^ (c i))
  let Y : Finset (Fin N → ℤ) := hYfin.toFinset
  have hYmem : ∀ y, y ∈ Y ↔ y ∈ bSet L Q c (t+1) := fun y => hYfin.mem_toFinset
  let V : Finset ℝ := Y.image (tau hN L Q c)
  let W : Finset ℝ := V.filter (fun s => t < s)
  let ε : ℝ := if h : W.Nonempty then min ((W.min' h - t)/2) (1/2) else 1/2
  have hεpos : 0 < ε := by
    dsimp only [ε]
    split_ifs with h
    · have hmin : t < W.min' h := (Finset.mem_filter.mp (Finset.min'_mem W h)).2
      exact lt_min (by linarith) (by norm_num)
    · norm_num
  have hεle : ε ≤ 1/2 := by
    dsimp only [ε]; split_ifs with h
    · exact min_le_right _ _
    · rfl
  have hεW : ∀ s ∈ W, t + ε < s := by
    intro s hs
    have hWne : W.Nonempty := ⟨s, hs⟩
    have hεeq : ε = min ((W.min' hWne - t)/2) (1/2) := by
      dsimp only [ε]; rw [dif_pos hWne]
    have hmt : t < W.min' hWne := (Finset.mem_filter.mp (Finset.min'_mem W hWne)).2
    have hms : W.min' hWne ≤ s := Finset.min'_le W s hs
    have h1 : min ((W.min' hWne - t)/2) (1/2) ≤ (W.min' hWne - t)/2 := min_le_left _ _
    rw [hεeq]; linarith
  refine ⟨ε, hεpos, ?_⟩
  intro t' ht'
  rw [Set.mem_Icc] at ht'
  obtain ⟨ht1, ht2⟩ := ht'
  have ht'le : t' ≤ t + 1 := by linarith [hεle]
  have hkey : ∀ y : Fin N → ℤ, (tau hN L Q c y ≤ t' ↔ tau hN L Q c y ≤ t) := by
    intro y
    refine ⟨fun hy => ?_, fun hy => le_trans hy ht1⟩
    by_contra hcon
    push Not at hcon
    have hyY : y ∈ Y := by
      rw [hYmem, mem_bSet_iff_tau hN L Q hQ c y (t+1)]
      linarith
    have hmemW : tau hN L Q c y ∈ W := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨y, hyY, rfl⟩, hcon⟩
    have hge := hεW (tau hN L Q c y) hmemW
    linarith
  have hset' : bSet L Q c t' = bSet L Q c t := by
    ext y
    rw [mem_bSet_iff_tau hN L Q hQ c y t', mem_bSet_iff_tau hN L Q hQ c y t]
    exact hkey y
  unfold rBox iSet
  rw [hset']

theorem box_rank_eq_card_successiveMinimum
    {N : ℕ} (hN : 1 ≤ N) (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (Q : ℝ) (hQ : 1 ≤ Q) (c : Fin N → ℝ) :
    ∀ (lam : Fin N → ℝ),
      (∀ j : Fin N, lam j = sInf {t : ℝ | 0 ≤ t ∧ (j.val + 1) ≤ Module.finrank ℚ
        (Submodule.span ℚ (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
          {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))}) →
      ∀ t : ℝ, 0 ≤ t →
        Module.finrank ℚ (Submodule.span ℚ (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
          {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))
          = ((Finset.univ : Finset (Fin N)).filter (fun j => lam j ≤ t)).card := by
  intro lam hlam t ht
  have hstab := rBox_stab hN L Q hQ c (fun M => finite_int_points_box L hdet M)
  have hmono : Monotone (fun t : ℝ => rBox L Q c t) := fun a b hab => rBox_mono L Q hQ c hab
  obtain ⟨T, hT0, hTN⟩ := rBox_top hN L Q hQ c
  exact eq_card_sInf_of_monotone (fun t : ℝ => rBox L Q c t) hmono hstab
    (fun t => rBox_le L Q c t) ⟨T, hT0, hTN⟩ lam (fun j => hlam j) t ht

end Commons.GeometryOfNumbers.Box