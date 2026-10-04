import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.honestTower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ricTowerBound_fixed_of_stage`

Staging lemma for `Work.Diff.EXT.ConnCov.ricTowerBound_fixed`: from

* `hHonest` — the uniform `(1 + √)`-shaped bound on the *honest* towers
  `htower (lcOf (G 0)) (baseRic (G t)) m` (`m ≤ k`), with the same constant `R` at every level, and
* `hExp` — the *shift (span) identity* expressing the shifted tower
  `tower (lcOf (G 0)) (baseRic (G t)) m` as the alternating sum of honest towers evaluated on
  strictly monotone selections `f : Fin j ↪o Fin m` of the direction slots,

we deduce the `(1 + Σ_{j<m} B j)`-shaped bound on the shifted tower
`tower (lcOf (G 0)) (baseRic (G t)) m` for all `m ≤ k` on `[T/2, T)`.

The mathematical content is purely finite combinatorics:

* the absolute value of the alternating sum `Σ_j (-1)^{m+j}(m-j)! Σ_f …` is bounded by the sum of
  the absolute values;
* on each selection `f` the product `∏_{l<j}(1+√⟪v_{f l},v_{f l}⟫)` is dominated by the full product
  `∏_{i<m}(1+√⟪vᵢ,vᵢ⟫)` (the *selection product estimate*);
* the remaining factor `(m-j)! · #{f : Fin j ↪o Fin m}` is bounded by
  `(k+1)! · (k+1)^{k+1}`, and there are `m+1 ≤ k+1` levels.

The same argument (for the *moving* connection and a homogeneous honest bound) is carried out in
`Submission/Work/Diff/EXT/ConnCov/RicTower_moving_bound_of_inputs.lean`.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.EXT.ConnCov.RicTr

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Elementary pieces -/

/-- `valOp` is the evaluation of an operator on the `Classical.epsilon`-chosen smooth extensions:
definitional. -/
theorem valOp_eq_apply {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k) (x : M)
    (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    Work.Diff.EXT.ATower.valOp τ x v a b c
      = τ (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x b) (Submission.Diff.smoothExt x c) x := rfl

/-- `oneAddSqrtProd` unfolded: definitional. -/
theorem oneAddSqrtProd_eq_prod (g : Submission.Diff.SMet I M) (x : M) {m : ℕ}
    (v : Fin m → TangentSpace I x) :
    Work.Diff.EXT.ConnCov.oneAddSqrtProd g x v
      = Finset.univ.prod (fun i : Fin m => (1 + Real.sqrt (g.inner x (v i) (v i)))) := rfl

/-- **The selection product estimate.**  The product of the factors `1 + √⟪·,·⟫` over the range of an
injective selection `f : Fin j → Fin m` is dominated by the product over all of `Fin m`. -/
theorem prod_selection_le_oneAdd (g : Submission.Diff.SMet I M) (x : M) {m j : ℕ}
    (v : Fin m → TangentSpace I x) (f : Fin j → Fin m) (hf : Function.Injective f) :
    (Finset.univ.prod (fun l : Fin j => (1 + Real.sqrt (g.inner x (v (f l)) (v (f l))))))
      ≤ Work.Diff.EXT.ConnCov.oneAddSqrtProd g x v := by
  rw [oneAddSqrtProd_eq_prod]
  rw [← Finset.prod_image (s := Finset.univ) (g := f)
        (f := fun i : Fin m => 1 + Real.sqrt (g.inner x (v i) (v i)))
        (fun a _ b _ h => hf h)]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _ => add_nonneg zero_le_one (Real.sqrt_nonneg _))
    (fun i _ _ => le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- **The combinatorial factor of one summand of the shift identity**: the factorial coefficient
times the number of strictly monotone selections `Fin j → Fin m` is bounded by
`(k+1)! · (k+1)^{k+1}` whenever `j ≤ m ≤ k`. -/
theorem factorial_mul_card_strictMono_le {m k j : ℕ} (hm : m ≤ k) (hj : j ≤ m) :
    ((m - j).factorial : ℝ) * ((Fintype.card {f : Fin j → Fin m // StrictMono f} : ℕ) : ℝ)
      ≤ ((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1)) := by
  have hfac : ((m - j).factorial : ℝ) ≤ ((k + 1).factorial : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (by omega : m - j ≤ k + 1))
  have h1 : Fintype.card {f : Fin j → Fin m // StrictMono f} ≤ Fintype.card (Fin j → Fin m) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have h2 : Fintype.card (Fin j → Fin m) = m ^ j := by simp
  have h3 : m ^ j ≤ (k + 1) ^ j := Nat.pow_le_pow_left (by omega) j
  have h4 : (k + 1) ^ j ≤ (k + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcard : ((Fintype.card {f : Fin j → Fin m // StrictMono f} : ℕ) : ℝ)
      ≤ (((k + 1 : ℕ) : ℝ) ^ (k + 1)) := by
    rw [h2] at h1
    have hnat : Fintype.card {f : Fin j → Fin m // StrictMono f} ≤ (k + 1) ^ (k + 1) :=
      le_trans h1 (le_trans h3 h4)
    rw [← Nat.cast_pow]
    exact Nat.cast_le.mpr hnat
  exact mul_le_mul hfac hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The combinatorial core.**  If every term of the shift identity is bounded by `R · P · Q`
homogeneously, then the shifted tower (the alternating sum) is bounded by
`(k+1) · (k+1)! · (k+1)^{k+1} · R · P · Q`. -/
theorem sel_sum_abs_bound (m k : ℕ) (hm : m ≤ k) (R P Q : ℝ) (hR0 : 0 ≤ R)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (S : (j : ℕ) → (Fin j → Fin m) → ℝ)
    (hS : ∀ (j : ℕ), j ≤ m → ∀ f : {f : Fin j → Fin m // StrictMono f},
      |S j f.val| ≤ R * (P * Q)) :
    |∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
        ∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val|
      ≤ ((k : ℝ) + 1) * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * R
          * (P * Q) := by
  have hRPQ : 0 ≤ R * (P * Q) := mul_nonneg hR0 (mul_nonneg hP0 hQ0)
  have hAB : (0 : ℝ) ≤ ((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1)) :=
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  calc |∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val|
      ≤ ∑ j ∈ Finset.range (m + 1), |((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (m + 1),
          (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * (R * (P * Q)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hTj : |∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val|
            ≤ (Fintype.card {f : Fin j → Fin m // StrictMono f} : ℝ) * (R * (P * Q)) := by
          calc |∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val|
              ≤ ∑ f : {f : Fin j → Fin m // StrictMono f}, |S j f.val| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _f : {f : Fin j → Fin m // StrictMono f}, R * (P * Q) :=
                Finset.sum_le_sum (fun f _ => hS j hjle f)
            _ = (Fintype.card {f : Fin j → Fin m // StrictMono f} : ℝ) * (R * (P * Q)) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc |((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
                ∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val|
            = ((m - j).factorial : ℝ) *
                |∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val| := by
              rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                abs_of_nonneg (Nat.cast_nonneg ((m - j).factorial))]
          _ ≤ ((m - j).factorial : ℝ) *
                ((Fintype.card {f : Fin j → Fin m // StrictMono f} : ℝ) * (R * (P * Q))) :=
              mul_le_mul_of_nonneg_left hTj (Nat.cast_nonneg _)
          _ = ((m - j).factorial : ℝ) * (Fintype.card {f : Fin j → Fin m // StrictMono f} : ℝ)
                * (R * (P * Q)) := by ring
          _ ≤ (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * (R * (P * Q)) :=
              mul_le_mul_of_nonneg_right (factorial_mul_card_strictMono_le hm hjle) hRPQ
    _ = ((m : ℝ) + 1) *
          ((((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * (R * (P * Q))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ ((k : ℝ) + 1) * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * R
          * (P * Q) := by
        have hle : ((m : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
          have h : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hm
          linarith
        have hC0 : 0 ≤ (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * (R * (P * Q)) :=
          mul_nonneg hAB hRPQ
        calc ((m : ℝ) + 1) *
              ((((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * (R * (P * Q)))
            ≤ ((k : ℝ) + 1) *
              ((((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * (R * (P * Q))) :=
              mul_le_mul_of_nonneg_right hle hC0
          _ = ((k : ℝ) + 1) * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * R
                * (P * Q) := by ring

end Helpers

/-! ## The target -/

theorem ricTowerBound_fixed_of_stage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j))
    (R : ℝ) (hR0 : 0 ≤ R)
    (hHonest : ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k →
      Work.Diff.EXT.ConnCov.ValBoundNoC G t m
        (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic (G t)) m) R)
    (hExp : ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k →
      ∀ (v : Fin m → Work.Diff.EXT.ATower.TF (I := I) (M := M))
        (A B Cc : Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M),
        Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic (G t)) m v A B Cc x
          = ∑ j ∈ Finset.range (m + 1),
              ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
                ∑ f : {f : Fin j → Fin m // StrictMono f},
                  Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G 0))
                    (Work.Diff.EXT.ConnCov.baseRic (G t)) j (fun l : Fin j => v (f.val l)) A B Cc x) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k → ∀ x : M,
      ∀ (v : Fin m → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x v a b c|
          ≤ Ck * (1 + Finset.sum (Finset.range m) B)
              * Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
  classical
  let Ck : ℝ := ((k : ℝ) + 1) * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * R
  have hCk : Ck = ((k : ℝ) + 1) * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * R :=
    rfl
  have hCk0 : 0 ≤ Ck := by
    rw [hCk]
    exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (by positivity)))
      hR0
  refine ⟨Ck, hCk0, ?_⟩
  intro t ht m hm x v a b c
  let P : ℝ := Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
  let Q : ℝ := Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
  have hP : P = Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v := rfl
  have hQ : Q = Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := rfl
  have hP0 : 0 ≤ P := by
    rw [hP, oneAddSqrtProd_eq_prod]
    exact Finset.prod_nonneg (fun i _ => by
      have := Real.sqrt_nonneg ((G t).inner x (v i) (v i))
      linarith)
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let S : (j : ℕ) → (Fin j → Fin m) → ℝ := fun j e =>
    Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G 0))
      (Work.Diff.EXT.ConnCov.baseRic (G t)) j
      (fun l : Fin j => Submission.Diff.smoothExt x (v (e l)))
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
      (Submission.Diff.smoothExt x c) x
  have hS : ∀ (j : ℕ), j ≤ m → ∀ f : {f : Fin j → Fin m // StrictMono f},
      |S j f.val| ≤ R * (P * Q) := by
    intro j hjle f
    have hjk : j ≤ k := le_trans hjle hm
    have hb := hHonest t ht j hjk x (fun l : Fin j => v (f.val l)) a b c
    have hb' : |S j f.val| ≤ R * (Finset.univ.prod (fun l : Fin j =>
          (1 + Real.sqrt ((G t).inner x (v (f.val l)) (v (f.val l))))))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := hb
    have hprod : (Finset.univ.prod (fun l : Fin j =>
          (1 + Real.sqrt ((G t).inner x (v (f.val l)) (v (f.val l)))))) ≤ P := by
      rw [hP]
      exact prod_selection_le_oneAdd (G t) x v f.val (StrictMono.injective f.property)
    have hbr : R * (Finset.univ.prod (fun l : Fin j =>
          (1 + Real.sqrt ((G t).inner x (v (f.val l)) (v (f.val l))))))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) ≤ R * (P * Q) := by
      rw [hQ]
      calc R * (Finset.univ.prod (fun l : Fin j =>
              (1 + Real.sqrt ((G t).inner x (v (f.val l)) (v (f.val l))))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          = R * ((Finset.univ.prod (fun l : Fin j =>
              (1 + Real.sqrt ((G t).inner x (v (f.val l)) (v (f.val l))))))
            * (Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))) := by ring
        _ ≤ R * (P * (Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))) := by
            apply mul_le_mul_of_nonneg_left _ hR0
            exact mul_le_mul_of_nonneg_right hprod
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    exact le_trans hb' hbr
  have hval : Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x v a b c
      = ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val := by
    have h1 : Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x v a b c
        = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic (G t)) m (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x := rfl
    rw [h1]
    exact hExp t ht m hm (fun i => Submission.Diff.smoothExt x (v i))
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
      (Submission.Diff.smoothExt x c) x
  have hsum : (0 : ℝ) ≤ Finset.sum (Finset.range m) B := Finset.sum_nonneg (fun j _ => hB j)
  have h1le : (1 : ℝ) ≤ 1 + Finset.sum (Finset.range m) B := le_add_of_nonneg_right hsum
  have hPQ : (0 : ℝ) ≤ P * Q := mul_nonneg hP0 hQ0
  calc |Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x v a b c|
      = |∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)) *
          ∑ f : {f : Fin j → Fin m // StrictMono f}, S j f.val| := by rw [hval]
    _ ≤ ((k : ℝ) + 1) * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) ^ (k + 1))) * R
          * (P * Q) := sel_sum_abs_bound m k hm R P Q hR0 hP0 hQ0 S hS
    _ = Ck * (P * Q) := by rw [hCk]
    _ ≤ Ck * ((1 + Finset.sum (Finset.range m) B) * (P * Q)) := by
        apply mul_le_mul_of_nonneg_left _ hCk0
        have := mul_le_mul_of_nonneg_right h1le hPQ
        rwa [one_mul] at this
    _ = Ck * (1 + Finset.sum (Finset.range m) B)
          * Work.Diff.EXT.ConnCov.oneAddSqrtProd (G t) x v
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
        rw [hP, hQ]; ring

end Work.Diff.EXT.ConnCov.RicTr
