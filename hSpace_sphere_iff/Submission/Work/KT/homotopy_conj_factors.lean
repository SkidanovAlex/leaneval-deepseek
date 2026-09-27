import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.conj_setup

/-!
# `Work.KT.homotopy_conj_factors` — factorising a homotopy of idempotents into small steps

Let `X` be a compact Hausdorff space and `Q` an idempotent `k × k` matrix over
`C(X × [0,1], ℂ)`.  A homotopy of idempotents can be cut into finitely many steps that are so
small that on each step the elementary algebraic identity

`(1 + (2p - 1)(q - p)) * q = p * (1 + (2p - 1)(q - p))`   (`Work.KT.idem_step`)

applies; chaining the corresponding factors gives matrices `W i` over `C(X, ℂ)`, each entrywise
bounded by `1/(2(k+1))`, whose product intertwines the two end points of the homotopy.

The file is self-contained apart from `Work.KT.Defs` (`sliceAt`) and `Work.KT.conj_setup`
(`idem_step`, `seg`).
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## Slicing -/

/-- Evaluating a slice at a point is evaluation of the original function. -/
lemma sliceAt_apply_pair {X : Type} [TopologicalSpace X] (t : unitInterval)
    (g : C(X × unitInterval, ℂ)) (x : X) : sliceAt t g x = g (x, t) := rfl

/-- The slices of an idempotent matrix are idempotent. -/
lemma sliceAt_idem {k : ℕ} {X : Type} [TopologicalSpace X]
    {Q : Matrix (Fin k) (Fin k) C(X × unitInterval, ℂ)} (hQ : Q * Q = Q) (t : unitInterval) :
    (Q.map (fun f => sliceAt t f)) * (Q.map (fun f => sliceAt t f)) =
      Q.map (fun f => sliceAt t f) := by
  have h := congrArg (fun (M : Matrix (Fin k) (Fin k) C(X × unitInterval, ℂ)) =>
    M.map (fun f => sliceAt t f)) hQ
  rwa [Matrix.map_mul] at h

/-! ## Entrywise estimates -/

/-- If the entries of `A` are bounded by `M`, the entries of `2 * A - 1` are bounded by
`2 * M + 1`. -/
lemma entry_norm_two_mul_sub_one {k : ℕ} {X : Type} [TopologicalSpace X]
    {A : Matrix (Fin k) (Fin k) C(X, ℂ)} {M : ℝ}
    (hA : ∀ (a b : Fin k) (x : X), ‖A a b x‖ ≤ M) :
    ∀ (a b : Fin k) (x : X),
      ‖(((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * A - 1) a b) x‖ ≤ 2 * M + 1 := by
  intro a b x
  have h2 : (((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * A) a b) x = 2 * (A a b x) := by
    rw [two_mul, two_mul]
    simp [Matrix.add_apply, ContinuousMap.add_apply]
  have hA2 : ‖(((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * A) a b) x‖ ≤ 2 * M := by
    rw [h2, norm_mul]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    exact mul_le_mul_of_nonneg_left (hA a b x) (by norm_num)
  have hone : ‖((1 : Matrix (Fin k) (Fin k) C(X, ℂ)) a b) x‖ ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  calc ‖(((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * A - 1) a b) x‖
      = ‖(((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * A) a b) x -
          ((1 : Matrix (Fin k) (Fin k) C(X, ℂ)) a b) x‖ := by
        rw [Matrix.sub_apply, ContinuousMap.sub_apply]
    _ ≤ ‖(((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * A) a b) x‖ +
          ‖((1 : Matrix (Fin k) (Fin k) C(X, ℂ)) a b) x‖ := norm_sub_le _ _
    _ ≤ 2 * M + 1 := add_le_add hA2 hone

/-- The entries of a product of matrices over `C(X, ℂ)` are bounded by `k` times the product of
the entrywise bounds. -/
lemma entry_norm_mul_le {k : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    {A B : Matrix (Fin k) (Fin k) C(X, ℂ)} {MA MB : ℝ}
    (hA : ∀ (a b : Fin k) (x : X), ‖A a b x‖ ≤ MA) (hA0 : 0 ≤ MA)
    (hB : ∀ (a b : Fin k) (x : X), ‖B a b x‖ ≤ MB) (hB0 : 0 ≤ MB) :
    ∀ (a b : Fin k) (x : X), ‖(A * B) a b x‖ ≤ (k : ℝ) * (MA * MB) := by
  intro a b x
  calc ‖(A * B) a b x‖ ≤ ‖(A * B) a b‖ := ContinuousMap.norm_coe_le_norm _ x
    _ = ‖∑ c, A a c * B c b‖ := by rw [Matrix.mul_apply]
    _ ≤ ∑ c, ‖A a c * B c b‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin k, MA * MB := Finset.sum_le_sum fun c _ => by
        calc ‖A a c * B c b‖ ≤ ‖A a c‖ * ‖B c b‖ := norm_mul_le _ _
          _ ≤ MA * MB :=
              mul_le_mul ((ContinuousMap.norm_le (f := A a c) hA0).mpr (fun x => hA a c x))
                ((ContinuousMap.norm_le (f := B c b) hB0).mpr (fun x => hB c b x))
                (norm_nonneg _) hA0
    _ = (k : ℝ) * (MA * MB) := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The numerical estimate behind the entrywise bound: with
`ε = 1 / (k (2M+2) 2(k+1))` one has `k (2M+1) ε ≤ 1/(2(k+1))`. -/
lemma homotopy_conj_key_bound (k : ℕ) {M : ℝ} (hk : 0 < k) (hM : 0 ≤ M) :
    (k : ℝ) * ((2 * M + 1) * (1 / ((k : ℝ) * (2 * M + 2) * (2 * ((k : ℝ) + 1))))) ≤
      1 / (2 * ((k : ℝ) + 1)) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h3 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * (2 * M + 2) * (2 * ((k : ℝ) + 1)) := by positivity
  rw [show (k : ℝ) * ((2 * M + 1) * (1 / ((k : ℝ) * (2 * M + 2) * (2 * ((k : ℝ) + 1))))) =
      (k : ℝ) * (2 * M + 1) / ((k : ℝ) * (2 * M + 2) * (2 * ((k : ℝ) + 1))) by
    rw [mul_one_div, mul_div_assoc]]
  rw [div_le_div_iff₀ hden h3]
  nlinarith [hk'.le, hM]

/-! ## Chaining the elementary steps -/

/-- **Chaining the elementary steps.**  Let `P : ℕ → A` be a sequence of idempotents in a ring and
set `u i = 1 + (2 P i - 1) * (P (i+1) - P i)` (which satisfies `u i * P (i+1) = P i * u i`, see
`Work.KT.idem_step`).  Then the product of the first `N` factors carries `P N` on the right to
`P 0` on the left. -/
theorem homotopy_conj_chain_prod {A : Type*} [Ring A] (N : ℕ) (P : ℕ → A) (u : ℕ → A)
    (hu : ∀ i, u i = (1 : A) + (2 * P i - 1) * (P (i + 1) - P i))
    (hidem : ∀ j, P j * P j = P j) :
    (List.ofFn (fun i : Fin N => u (i : ℕ))).prod * P N =
      P 0 * (List.ofFn (fun i : Fin N => u (i : ℕ))).prod := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.prod_concat]
    have ih' : (List.ofFn (fun i : Fin n =>
        u ((Fin.castSucc i : Fin (n + 1)) : ℕ))).prod * P n =
        P 0 * (List.ofFn (fun i : Fin n =>
          u ((Fin.castSucc i : Fin (n + 1)) : ℕ))).prod := ih
    have hlast : u (((Fin.last n : Fin (n + 1)) : ℕ)) =
        (1 : A) + (2 * P n - 1) * (P (n + 1) - P n) := hu n
    rw [hlast, mul_assoc, idem_step (hidem n) (hidem (n + 1)), ← mul_assoc, ih', mul_assoc]

/-! ## Uniformly small steps of a continuous function on `X × [0,1]` -/

/-- **Uniform small steps for a continuous function on `X × [0,1]`.**  Let `X` be compact and
`f : C(X × [0,1], ℂ)` continuous, and let `seg N j` be the `j`-th point of the equal partition of
`[0,1]` into `N` pieces (clamped, see `Work.KT.seg`).  Then for every `ε > 0` there is `N ≥ 1`
such that every refinement `N' ≥ N` has consecutive slices within `ε`, uniformly in `x`. -/
theorem exists_seg_partition {X : Type} [TopologicalSpace X] [CompactSpace X]
    (f : C(X × unitInterval, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (N' : ℕ), N ≤ N' → ∀ (i : Fin N') (x : X),
      ‖f (x, seg N' ((i : ℕ) + 1)) - f (x, seg N' (i : ℕ))‖ ≤ ε := by
  -- Curry `f` into a continuous path of functions on the compact space `X`; the norm topology on
  -- `C(X, ℂ)` then turns Heine–Cantor into a statement uniform in `x`.
  let σ : C(unitInterval × X, X × unitInterval) := ⟨fun p => (p.2, p.1), by fun_prop⟩
  let g : C(unitInterval, C(X, ℂ)) := ContinuousMap.curry (f.comp σ)
  have hgval : ∀ (t : unitInterval) (x : X), g t x = f (x, t) := fun t x => rfl
  have huc : UniformContinuous g :=
    CompactSpace.uniformContinuous_of_continuous g.continuous
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuous_iff.mp huc) ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro N' hN' i x
  have hN'pos : 0 < N' := by omega
  have h1 : 1 / (N' : ℝ) < δ := by
    refine lt_of_le_of_lt ?_ hn
    exact one_div_le_one_div_of_le (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast hN')
  have hdist : dist (seg N' ((i : ℕ) + 1)) (seg N' (i : ℕ)) < δ :=
    lt_of_le_of_lt (dist_seg_le N' hN'pos (i : ℕ)) h1
  have hclose : dist (g (seg N' ((i : ℕ) + 1))) (g (seg N' (i : ℕ))) < ε := hδ' hdist
  have key : ‖g (seg N' ((i : ℕ) + 1)) x - g (seg N' (i : ℕ)) x‖ ≤
      ‖g (seg N' ((i : ℕ) + 1)) - g (seg N' (i : ℕ))‖ := by
    rw [← ContinuousMap.sub_apply]
    exact ContinuousMap.norm_coe_le_norm _ x
  calc ‖f (x, seg N' ((i : ℕ) + 1)) - f (x, seg N' (i : ℕ))‖
      = ‖g (seg N' ((i : ℕ) + 1)) x - g (seg N' (i : ℕ)) x‖ := by rw [hgval, hgval]
    _ ≤ ‖g (seg N' ((i : ℕ) + 1)) - g (seg N' (i : ℕ))‖ := key
    _ = dist (g (seg N' ((i : ℕ) + 1))) (g (seg N' (i : ℕ))) := by rw [dist_eq_norm]
    _ ≤ ε := le_of_lt hclose

/-! ## The main statement -/

/-- **Partition of a homotopy of idempotents into small steps.**  Let `X` be a compact Hausdorff
space and `Q` an idempotent `k × k` matrix over `C(X × [0,1], ℂ)`.  Then there are finitely many
matrices `W i` over `C(X,ℂ)`, each with all entries pointwise bounded by `1/(2(k+1))`, such that the
product of the elementary conjugating factors `1 + W i` carries the time-`1` value of `Q` to the
time-`0` value: with `Q_s` the specialisation of `Q` at time `s`,
`(∏ i, (1 + W i)) * Q₁ = Q₀ * (∏ i, (1 + W i))`.  Each factor is `1 + (2 q - 1)(q' - q)` for
consecutive values `q`, `q'` of the homotopy. -/
theorem homotopy_conj_factors {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k : ℕ) (Q : Matrix (Fin k) (Fin k) C(X × unitInterval, ℂ)) (hQ : Q * Q = Q) :
    ∃ (K : ℕ) (W : Fin K → Matrix (Fin k) (Fin k) C(X, ℂ)),
      (∀ (i : Fin K) (a b : Fin k) (x : X), ‖W i a b x‖ ≤ 1 / (2 * ((k : ℝ) + 1))) ∧
      (List.ofFn (fun i => 1 + W i)).prod * Q.map (fun f => sliceAt 1 f) =
        Q.map (fun f => sliceAt 0 f) * (List.ofFn (fun i => 1 + W i)).prod := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- `k = 0`: there are no entries, and `0 × 0` matrices are subsingletons.
    subst hk
    refine ⟨0, (fun i => i.elim0), ?_, ?_⟩
    · intro i; exact i.elim0
    · simp only [List.ofFn_zero, List.prod_nil, one_mul, mul_one]
      funext i
      exact i.elim0
  · -- A uniform bound `M` on the entries of `Q`.
    set M : ℝ := ∑ p : Fin k × Fin k, ‖Q p.1 p.2‖ with hM
    have hMnn : 0 ≤ M := Finset.sum_nonneg fun p _ => norm_nonneg _
    have hMb : ∀ (a b : Fin k), ‖Q a b‖ ≤ M := fun a b =>
      Finset.single_le_sum (f := fun p : Fin k × Fin k => ‖Q p.1 p.2‖) (a := (a, b))
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (a, b))
    have hMe : ∀ (a b : Fin k) (y : X × unitInterval), ‖Q a b y‖ ≤ M := fun a b y =>
      (ContinuousMap.norm_coe_le_norm (Q a b) y).trans (hMb a b)
    -- The step size, small enough for the entrywise estimate.
    set ε : ℝ := 1 / ((k : ℝ) * (2 * M + 2) * (2 * ((k : ℝ) + 1))) with hε
    have hεpos : 0 < ε := by rw [hε]; positivity
    -- A common number of steps for all entries.
    choose Nf hNf using fun p : Fin k × Fin k => exists_seg_partition (Q p.1 p.2) hεpos
    set N : ℕ := Finset.univ.sup Nf with hN
    have hNpos : 0 < N := by
      have h1 : 0 < Nf (⟨0, hk⟩, ⟨0, hk⟩) := (hNf (⟨0, hk⟩, ⟨0, hk⟩)).1
      have h2 : Nf (⟨0, hk⟩, ⟨0, hk⟩) ≤ N := by
        rw [hN]; exact Finset.le_sup (Finset.mem_univ _)
      omega
    have hNne : N ≠ 0 := by omega
    have hNbound : ∀ (a b : Fin k) (i : Fin N) (x : X),
        ‖Q a b (x, seg N ((i : ℕ) + 1)) - Q a b (x, seg N (i : ℕ))‖ ≤ ε := by
      intro a b i x
      have hle : Nf (a, b) ≤ N := by rw [hN]; exact Finset.le_sup (Finset.mem_univ _)
      exact (hNf (a, b)).2 N hle i x
    -- The successive slices of `Q`, and the elementary factors.
    set P : ℕ → Matrix (Fin k) (Fin k) C(X, ℂ) :=
      fun j => Q.map (fun f => sliceAt (seg N j) f) with hP
    have hidemP : ∀ j, P j * P j = P j := fun j => by rw [hP]; exact sliceAt_idem hQ (seg N j)
    set W : Fin N → Matrix (Fin k) (Fin k) C(X, ℂ) :=
      fun i => ((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * P (i : ℕ) - 1) *
        (P ((i : ℕ) + 1) - P (i : ℕ)) with hW
    refine ⟨N, W, ?_, ?_⟩
    · -- Entrywise bound on the factors.
      intro i a b x
      have hAP : ∀ (a c : Fin k) (x : X), ‖P (i : ℕ) a c x‖ ≤ M := by
        intro a c x
        rw [hP]
        simp only [Matrix.map_apply, sliceAt_apply_pair]
        exact hMe a c (x, seg N (i : ℕ))
      have hA : ∀ (a c : Fin k) (x : X),
          ‖(((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * P (i : ℕ) - 1) a c) x‖ ≤ 2 * M + 1 :=
        fun a c x => entry_norm_two_mul_sub_one hAP a c x
      have hB : ∀ (c b : Fin k) (x : X),
          ‖(P ((i : ℕ) + 1) - P (i : ℕ)) c b x‖ ≤ ε := by
        intro c b x
        have hsub : (P ((i : ℕ) + 1) - P (i : ℕ)) c b x =
            Q c b (x, seg N ((i : ℕ) + 1)) - Q c b (x, seg N (i : ℕ)) := by
          simp only [hP, Matrix.sub_apply, ContinuousMap.sub_apply, Matrix.map_apply,
            sliceAt_apply_pair]
        rw [hsub]
        exact hNbound c b i x
      have h := entry_norm_mul_le (A := ((2 : Matrix (Fin k) (Fin k) C(X, ℂ)) * P (i : ℕ) - 1))
        (B := P ((i : ℕ) + 1) - P (i : ℕ)) (MA := 2 * M + 1) (MB := ε)
        hA (by positivity) hB hεpos.le a b x
      rw [hW]
      refine h.trans ?_
      have hkey : (k : ℝ) * ((2 * M + 1) * ε) ≤ 1 / (2 * ((k : ℝ) + 1)) := by
        rw [hε]; exact homotopy_conj_key_bound k hk hMnn
      exact hkey
    · -- Chaining the factors.
      have hchain := homotopy_conj_chain_prod N P
        (fun i => (1 : Matrix (Fin k) (Fin k) C(X, ℂ)) +
          (2 * P i - 1) * (P (i + 1) - P i)) (fun i => rfl) hidemP
      simpa [hP, hW, seg_last N hNne, seg_zero N] using hchain

end

end Work.KT
