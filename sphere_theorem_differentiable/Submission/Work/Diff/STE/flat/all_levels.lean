
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.energy_apriori
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.ENormSq_seriesFun_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

/-- A coefficient family supported in a box decays faster than every polynomial weight. -/
lemma rapid_of_box {n N : ℕ} (f : (Fin n → ℤ) → ℂ)
    (hf : ∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → f k' = 0) (M : ℕ) :
    Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖f k‖) := by
  refine summable_of_ne_finset_zero (s := Work.Diff.STE.Flat.box n N) ?_
  intro k hk
  simp [hf k hk]

/-- The matrix energy at level `j` is nonnegative. -/
lemma ENormSqM_nonneg' {n : ℕ} (k : ℕ) (u : Work.Diff.STE.Flat.Torus n) :
    0 ≤ Work.Diff.STE.Flat.ENormSqM k u := by
  rw [show Work.Diff.STE.Flat.ENormSqM k u
      = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
          ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l (fun y => u y i j) x‖ ^ 2
        from rfl]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => sq_nonneg _))))

/-- **Lower levels are controlled by the level `s` energy.**  For a coefficient family supported in
the box `box n N`, the full energy of any level `j ≤ s` is bounded by a constant (depending only on
`j`, `s`, `n`) times the full energy of level `s`.  The proof compares the physical energies with
the weighted coefficient norms `CSq` (`ENormSq_seriesFun_le`, `CSq_le_ENormSq_seriesFun`) and uses
that `CSq` is monotone in the level because `wt k ≥ 1`. -/
lemma level_mono {n : ℕ} {j s : ℕ} (hjs : j ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM c)
        ≤ C * Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) := by
  obtain ⟨Cj, hCjnn, hCj⟩ := Work.Diff.STE.ENormSq_seriesFun_le (ι := Fin n) j
  obtain ⟨Cs, hCsnn, hCs⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨Cj * Cs + 1, by positivity, ?_⟩
  intro N c hc
  have hpt : ∀ (i k : Fin n),
      Work.Diff.STE.ENormSq j (Work.Diff.STE.seriesFun (fun m => c m i k))
        ≤ Cj * Cs * (Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun (fun m => c m i k))
            + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun m => c m i k))) := by
    intro i k
    have hd : ∀ M : ℕ, Summable (fun m : Fin n → ℤ =>
        (Work.Diff.STE.wt m) ^ M * ‖c m i k‖) :=
      fun M => rapid_of_box (N := N) (fun m => c m i k) (fun m hm => by simp [hc m hm]) M
    have h1 := hCj (fun m => c m i k) hd
    have h2 := hCs (fun m => c m i k) hd
    have h3 : Work.Diff.STE.CSq j (fun m => c m i k)
        ≤ Work.Diff.STE.CSq s (fun m => c m i k) := by
      refine Summable.tsum_le_tsum (fun m => ?_)
        (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hd j)
        (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hd s)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (Work.Diff.STE.wt_one_le m) hjs) (sq_nonneg _)
    calc Work.Diff.STE.ENormSq j (Work.Diff.STE.seriesFun (fun m => c m i k))
        ≤ Cj * Work.Diff.STE.CSq j (fun m => c m i k) := h1
      _ ≤ Cj * Work.Diff.STE.CSq s (fun m => c m i k) := mul_le_mul_of_nonneg_left h3 hCjnn
      _ ≤ Cj * (Cs * (Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun (fun m => c m i k))
            + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun m => c m i k)))) :=
            mul_le_mul_of_nonneg_left h2 hCjnn
      _ = Cj * Cs * (Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun (fun m => c m i k))
            + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun m => c m i k))) := by ring
  have hsum : Work.Diff.STE.Flat.ENormSqM j (Work.Diff.STE.Flat.seriesFunM c)
      ≤ Cj * Cs * (Work.Diff.STE.Flat.ENormSqM s (Work.Diff.STE.Flat.seriesFunM c)
          + Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c)) := by
    rw [Work.Diff.STE.Flat.ENormSqM]
    calc ∑ i, ∑ k, Work.Diff.STE.ENormSq j
            (fun x => Work.Diff.STE.Flat.seriesFunM c x i k)
        = ∑ i, ∑ k, Work.Diff.STE.ENormSq j
            (Work.Diff.STE.seriesFun (fun m => c m i k)) := by
          simp only [Work.Diff.STE.Flat.seriesFunM_apply]
      _ ≤ ∑ i, ∑ k, Cj * Cs * (Work.Diff.STE.ENormSq s
              (Work.Diff.STE.seriesFun (fun m => c m i k))
            + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun m => c m i k))) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hpt i k))
      _ = Cj * Cs * (∑ i, ∑ k, Work.Diff.STE.ENormSq s
              (Work.Diff.STE.seriesFun (fun m => c m i k))
            + ∑ i, ∑ k, Work.Diff.STE.ENormSq 0
              (Work.Diff.STE.seriesFun (fun m => c m i k))) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = Cj * Cs * (Work.Diff.STE.Flat.ENormSqM s (Work.Diff.STE.Flat.seriesFunM c)
            + Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c)) := by
          rw [Work.Diff.STE.Flat.ENormSqM, Work.Diff.STE.Flat.ENormSqM]
          simp only [Work.Diff.STE.Flat.seriesFunM_apply]
  have hE0le : Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c)
      ≤ Work.Diff.STE.Flat.ENormSqM s (Work.Diff.STE.Flat.seriesFunM c)
        + Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c) := by
    linarith [ENormSqM_nonneg' s (Work.Diff.STE.Flat.seriesFunM c)]
  show Work.Diff.STE.Flat.ENormSqM j (Work.Diff.STE.Flat.seriesFunM c)
      + Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c)
      ≤ (Cj * Cs + 1) * (Work.Diff.STE.Flat.ENormSqM s (Work.Diff.STE.Flat.seriesFunM c)
        + Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c))
  nlinarith [hsum, hE0le]

theorem all_levels {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (s₀ : ℕ) (hs₀ : Fintype.card (Fin n) + 5 ≤ s₀)
    (lam : ℝ) (hlam : 0 < lam)
    (hstep : ∀ s : ℕ, s₀ ≤ s → ∀ Bs : ℝ, 0 ≤ Bs → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ)
        (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ Bs ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          DifferentiableAt ℝ
            (fun σ => Work.Diff.STE.Flat.ENormSqFull (s + 1)
              (Work.Diff.STE.Flat.seriesFunM (c σ))) t ∧
          deriv (fun σ => Work.Diff.STE.Flat.ENormSqFull (s + 1)
              (Work.Diff.STE.Flat.seriesFunM (c σ))) t
            ≤ C * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
                (Work.Diff.STE.Flat.seriesFunM (c t))))
    (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∀ Tc : ℝ, 0 < Tc → ∃ Blim : (ℕ → ℝ) → ℕ → ℝ,
      (∀ E0 : ℕ → ℝ, (∀ j, 0 ≤ E0 j) → ∀ j, 0 ≤ Blim E0 j) ∧
      ∀ (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull s₀ (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B₀ ^ 2) →
        ∀ E0 : ℕ → ℝ, (∀ j, 0 ≤ E0 j) →
        (∀ j, Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c 0)) ≤ E0 j) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ j : ℕ,
          Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ Blim E0 j := by
  intro Tc hTc
  let stepC : ℕ → ℝ → ℝ := fun m Bprev =>
    Classical.choose (hstep (s₀ + m) (Nat.le_add_right s₀ m) (Real.sqrt Bprev)
      (Real.sqrt_nonneg Bprev))
  let B : (ℕ → ℝ) → ℕ → ℝ := fun E0 m =>
    Nat.rec (Classical.choose (level_mono (n := n) (s := s₀) (le_refl s₀)) * B₀ ^ 2)
      (fun m prev => max 0 ((E0 (s₀ + m + 1) + 1) * Real.exp (stepC m prev * Tc) - 1)) m
  let Blim : (ℕ → ℝ) → ℕ → ℝ := fun E0 j =>
    if h : j ≤ s₀ then Classical.choose (level_mono (n := n) (s := s₀) h) * B₀ ^ 2
    else B E0 (j - s₀)
  have hBnn : ∀ (E0 : ℕ → ℝ) (m : ℕ), 0 ≤ B E0 m := by
    intro E0 m
    induction m with
    | zero =>
        show (0 : ℝ) ≤ Classical.choose (level_mono (n := n) (s := s₀) (le_refl s₀)) * B₀ ^ 2
        exact mul_nonneg (Classical.choose_spec (level_mono (n := n) (s := s₀) (le_refl s₀))).1
          (sq_nonneg B₀)
    | succ m ih =>
        show (0 : ℝ) ≤ max 0 ((E0 (s₀ + m + 1) + 1)
          * Real.exp (stepC m (B E0 m) * Tc) - 1)
        exact le_max_left _ _
  have hBlim_le : ∀ (E0 : ℕ → ℝ) (j : ℕ) (h : j ≤ s₀),
      Blim E0 j = Classical.choose (level_mono (n := n) (s := s₀) h) * B₀ ^ 2 := by
    intro E0 j h
    simp only [Blim]
    exact dite_eq_left h
  have hBlim_gt : ∀ (E0 : ℕ → ℝ) (j : ℕ), ¬ (j ≤ s₀) → Blim E0 j = B E0 (j - s₀) := by
    intro E0 j h
    simp only [Blim]
    exact dite_eq_right h
  refine ⟨Blim, ?_, ?_⟩
  · intro E0 hE0 j
    by_cases h : j ≤ s₀
    · rw [hBlim_le E0 j h]
      exact mul_nonneg (Classical.choose_spec (level_mono (n := n) (s := s₀) h)).1 (sq_nonneg B₀)
    · rw [hBlim_gt E0 j h]
      exact hBnn E0 (j - s₀)
  · intro N c hderiv hsupp hell hlev E0 hE0nn hinit t ht j
    by_cases hj : j ≤ s₀
    · rw [hBlim_le E0 j hj]
      have hbase := Classical.choose_spec (level_mono (n := n) (s := s₀) hj)
      have hbound := hbase.2 N (c t) (hsupp t)
      calc Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c t))
          ≤ Classical.choose (level_mono (n := n) (s := s₀) hj)
              * Work.Diff.STE.Flat.ENormSqFull s₀ (Work.Diff.STE.Flat.seriesFunM (c t)) := hbound
        _ ≤ Classical.choose (level_mono (n := n) (s := s₀) hj) * B₀ ^ 2 :=
              mul_le_mul_of_nonneg_left (hlev t ht) hbase.1
    · rw [hBlim_gt E0 j hj]
      have hkey : ∀ m (t' : ℝ), t' ∈ Set.Ico (0 : ℝ) Tc →
          Work.Diff.STE.Flat.ENormSqFull (s₀ + m) (Work.Diff.STE.Flat.seriesFunM (c t'))
            ≤ B E0 m := by
        intro m
        induction m with
        | zero =>
            intro t' ht'
            rw [show B E0 0
                = Classical.choose (level_mono (n := n) (s := s₀) (le_refl s₀)) * B₀ ^ 2 from rfl]
            have hbase := Classical.choose_spec (level_mono (n := n) (s := s₀) (le_refl s₀))
            calc Work.Diff.STE.Flat.ENormSqFull s₀ (Work.Diff.STE.Flat.seriesFunM (c t'))
                ≤ Classical.choose (level_mono (n := n) (s := s₀) (le_refl s₀))
                    * Work.Diff.STE.Flat.ENormSqFull s₀
                        (Work.Diff.STE.Flat.seriesFunM (c t')) := hbase.2 N (c t') (hsupp t')
              _ ≤ Classical.choose (level_mono (n := n) (s := s₀) (le_refl s₀)) * B₀ ^ 2 :=
                    mul_le_mul_of_nonneg_left (hlev t' ht') hbase.1
        | succ m ih =>
            intro t' ht'
            have hspec := Classical.choose_spec
              (hstep (s₀ + m) (Nat.le_add_right s₀ m) (Real.sqrt (B E0 m))
                (Real.sqrt_nonneg (B E0 m)))
            have hlev' : ∀ t'' ∈ Set.Ico (0 : ℝ) Tc,
                Work.Diff.STE.Flat.ENormSqFull (s₀ + m)
                    (Work.Diff.STE.Flat.seriesFunM (c t''))
                  ≤ (Real.sqrt (B E0 m)) ^ 2 := by
              intro t'' ht''
              rw [Real.sq_sqrt (hBnn E0 m)]
              exact ih t'' ht''
            have hCbound := hspec.2 Tc hTc N c hderiv hsupp hell hlev'
            have hgr : ∀ τ ∈ Set.Ico (0 : ℝ) Tc,
                Work.Diff.STE.Flat.ENormSqFull ((s₀ + m) + 1)
                    (Work.Diff.STE.Flat.seriesFunM (c τ))
                  ≤ (E0 (s₀ + m + 1) + 1) * Real.exp (stepC m (B E0 m) * τ) - 1 :=
              gronwall_Ico (C := stepC m (B E0 m)) (B := E0 (s₀ + m + 1)) hspec.1
                (fun τ hτ => (hCbound τ hτ).1.hasDerivAt)
                (fun τ hτ => (hCbound τ hτ).2)
                (hinit (s₀ + m + 1))
            have htle : t' ≤ Tc := le_of_lt ht'.2
            have hexp : Real.exp (stepC m (B E0 m) * t')
                ≤ Real.exp (stepC m (B E0 m) * Tc) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htle hspec.1)
            have hE1 : (0 : ℝ) ≤ E0 (s₀ + m + 1) + 1 := by linarith [hE0nn (s₀ + m + 1)]
            have hb1 : (E0 (s₀ + m + 1) + 1) * Real.exp (stepC m (B E0 m) * t') - 1
                ≤ (E0 (s₀ + m + 1) + 1) * Real.exp (stepC m (B E0 m) * Tc) - 1 := by
              linarith [mul_le_mul_of_nonneg_left hexp hE1]
            rw [show B E0 (m + 1)
                = max 0 ((E0 (s₀ + m + 1) + 1)
                    * Real.exp (stepC m (B E0 m) * Tc) - 1) from rfl]
            exact le_trans (hgr t' ht') (le_trans hb1 (le_max_right _ _))
      have hlast := hkey (j - s₀) t ht
      rwa [Nat.add_sub_of_le (le_of_lt (not_le.mp hj))] at hlast

end

end Work.Diff.STE.flat
