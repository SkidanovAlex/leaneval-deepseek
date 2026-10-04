import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVDeltaTower
import Submission.Work.Diff.EXT.ConnCov.RicFlip.towerEqLoweringDeltaTowerM
import Submission.Work.Diff.EXT.ATower.fixedDeltaAtomBndV
import Submission.Work.Diff.EXT.ATower.bndV_metric_le
import Submission.Work.Diff.EXT.ConnCov.RicTr.deltaTower_bound_of_hA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The affine bound for the flipped `δ`-atom

`Work.Diff.EXT.ConnCov.DT.TB G t c D` is the bound of the fixed-connection `δ`-tower
`V_c = ∇^{G 0,c}(∇^{G t} − ∇^{G 0})` of the connection difference, measured in the *moving*
metric `G t`, on arbitrary smooth fields.  The `δ`-tower chapter of `ConnCov/RicTr/DT`
proves it from the bounds of the towers of `aOf = g_t ⊙ δ` at the levels `≤ c`
(`Work.Diff.EXT.ConnCov.DT.exists_TB`).

The present module is the **affine** version needed on the critical path of
`Work.Diff.EXT.conn_diff_cov_bounds`: on the top level `k` only the *pointwise* hypothesis
`ValBound G t k (tower (lcOf (G 0)) (aOf G t) k) ρ` is available (a different `ρ` for each `t`,
coming from the preceding step of the Grönwall induction), and the conclusion must be affine in
`ρ` with a constant that does not depend on it.

The proof is a transcription of the expansion bound of the `δ`-tower chapter
(`Work.Diff.EXT.ConnCov.DT.wterm_bound_of_expansion`) in which

* the level-`k` bound `B k` is replaced by the *given* `ρ` (the leading term of the bound),
* the level-`m n ≤ k − 1` bounds of the metric factors are taken from `hA` (the very hypothesis
  of the target: the expansion term of level `k` pairs the metric tower `∇^{G 0, m n + 1}g_t` —
  which is the symmetrised `aOf`-tower at level `m n`, bounded by `hA` — with the `δ`-tower at
  level `j n`, bounded by the lower-level constants),
* and the interval-uniform constants are replaced by the pointwise ones.

Finally the `G t`-bound is transported to the initial metric by `ATower.bndV_metric_le`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ATower

/-! ## (1) The lower-level `δ`-tower bounds

From the bounds of the towers of `aOf` at the levels `< k` the `δ`-tower chapter produces
constants `Dlow` with the `TB`-bounds at all levels `< k`; this is
`Work.Diff.EXT.ConnCov.DT.exists_TB` applied at level `k - 1`. -/

lemma exists_TB_low
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (Bb : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bb j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) j) (Bb j)) :
    ∃ Dlow : ℕ → ℝ, (∀ j, 0 ≤ Dlow j) ∧
      ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
        Work.Diff.EXT.ConnCov.DT.TB G t j (Dlow j) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨fun _ => 0, fun _ => le_rfl, fun j hj => absurd hj (by omega)⟩
  · obtain ⟨D, hD0, hDB⟩ := Work.Diff.EXT.ConnCov.DT.exists_TB (I := I) (M := M) hLC G T hT
      (k - 1) Bb hB (fun j hj t ht => hA j (by omega) t ht)
    refine ⟨fun c => max (D c) 0, fun c => le_max_right _ _, ?_⟩
    intro j hj t ht
    have hj' : j ≤ k - 1 := by omega
    have hmax : max (D j) 0 = D j := max_eq_left (hD0 j hj')
    change Work.Diff.EXT.ConnCov.DT.TB G t j (max (D j) 0)
    rw [hmax]
    exact hDB j hj' t ht

/-! ## (2) The affine bound of the lowering `Wterm`

This is the transcription of `Work.Diff.EXT.ConnCov.DT.wterm_bound_of_expansion` described in the
module docstring.  The constant is `ρ + Σ_n 2 * B (m n) * Dlow (j n)`: the leading term carries
the *given* level-`k` bound `ρ`, and the expansion terms carry the level-`m n` bound `B (m n)`
(available from `hA`, because `m n + 1 + j n = k` forces `m n < k`). -/

theorem wterm_bound_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (T : ℝ)
    (k : ℕ) (Bb : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bb j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) j) (Bb j))
    {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ValBound G t k (tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k) ρ)
    (Dc : Work.Diff.EXT.ConnCov.DT.CombData k)
    (hDcx : ∀ (G' : ℝ → Submission.Diff.SMet I M) (t' : ℝ),
      Work.Diff.EXT.ConnCov.DT.OpEqSel
        (tower (Submission.Diff.lcOf (G' 0)) (fun _ => aOf G' t') k)
        (fun v A B C y => Work.Diff.EXT.ConnCov.DT.Wterm G' t' k v A B C y
          + Work.Diff.EXT.ConnCov.DT.CombTerm Dc G' t' v A B C y))
    (Dlow : ℕ → ℝ) (hDlow0 : ∀ j, j < k → 0 ≤ Dlow j)
    (hDlow : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.DT.TB G t j (Dlow j)) :
    ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M),
      (∀ p, SmE I M (v p)) → SmE I M A → SmE I M B → SmE I M C →
      |Work.Diff.EXT.ConnCov.DT.Wterm G t k v A B C x|
        ≤ (ρ + ∑ n : Dc.ι, 2 * Bb (Dc.m n) * Dlow (Dc.j n))
          * ((Finset.univ.prod (fun p : Fin k =>
                (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
              * Real.sqrt ((G t).inner x (A x) (A x))
              * Real.sqrt ((G t).inner x (B x) (B x))
              * Real.sqrt ((G t).inner x (C x) (C x))) := by
  intro v A B C x hv hA' hB' hC'
  have hm0 : ∀ p : Fin k, 0 ≤ Real.sqrt ((G t).inner x (v p x) (v p x)) :=
    fun p => Real.sqrt_nonneg _
  have hsA : 0 ≤ Real.sqrt ((G t).inner x (A x) (A x)) := Real.sqrt_nonneg _
  have hsB : 0 ≤ Real.sqrt ((G t).inner x (B x) (B x)) := Real.sqrt_nonneg _
  have hsC : 0 ≤ Real.sqrt ((G t).inner x (C x) (C x)) := Real.sqrt_nonneg _
  -- the Leibniz expansion at level `k`
  have hex := hDcx G t v A B C x hv hA' hB' hC'
  have hW : Work.Diff.EXT.ConnCov.DT.Wterm G t k v A B C x
      = tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x
        - ∑ n : Dc.ι,
            Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
              (Dc.F n) (Dc.G' n) v A B C x := by
    have h : tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x
        = Work.Diff.EXT.ConnCov.DT.Wterm G t k v A B C x
          + ∑ n : Dc.ι,
              Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
                (Dc.F n) (Dc.G' n) v A B C x := hex
    linarith
  -- the leading term: the bound `ρ` at level `k`
  have htow : |tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x|
      ≤ ρ * ((Finset.univ.prod (fun p : Fin k =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
          * Real.sqrt ((G t).inner x (A x) (A x))
          * Real.sqrt ((G t).inner x (B x) (B x))
          * Real.sqrt ((G t).inner x (C x) (C x))) := by
    have h := Work.Diff.EXT.ConnCov.DT.aOfTower_val_bound hLC G t k ρ hρ x v A B C hv hA' hB' hC'
    have hprod : (Finset.univ.prod (fun p : Fin k =>
          Real.sqrt ((G t).inner x (v p x) (v p x))))
        ≤ Finset.univ.prod (fun p : Fin k =>
          (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))) :=
      Finset.prod_le_prod₀ (fun p _ => hm0 p) (fun p _ => by linarith [hm0 p])
    have step : ρ * (Finset.univ.prod (fun p : Fin k =>
            Real.sqrt ((G t).inner x (v p x) (v p x))))
        ≤ ρ * (Finset.univ.prod (fun p : Fin k =>
            (1 + Real.sqrt ((G t).inner x (v p x) (v p x))))) :=
      mul_le_mul_of_nonneg_left hprod hρ0
    have h1 := mul_le_mul_of_nonneg_right step hsA
    have h2 := mul_le_mul_of_nonneg_right h1 hsB
    exact le_trans h (le_trans (mul_le_mul_of_nonneg_right h2 hsC) (le_of_eq (by ring)))
  -- the expansion terms
  have hterm : ∀ n : Dc.ι,
      |Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
          (Dc.F n) (Dc.G' n) v A B C x|
        ≤ (2 * Bb (Dc.m n) * Dlow (Dc.j n)) * ((Finset.univ.prod (fun p : Fin k =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x))) := by
    intro n
    have hj : Dc.j n < k := by have := Dc.hmj n; omega
    have hmk : Dc.m n < k := by have := Dc.hmj n; omega
    exact Work.Diff.EXT.ConnCov.DT.selTerm_val_bound (I := I) (M := M) hLC G t x (Dc.hmj n)
      (by omega) (Dc.F n)
      (Dc.G' n) (Dc.hfinj n) (Dc.hginj n) (Dc.hdisj n)
      (Work.Diff.EXT.ConnCov.DT.range_union_eq_univ (Dc.hmj n) (Dc.F n) (Dc.G' n) (Dc.hfinj n)
        (Dc.hginj n) (Dc.hdisj n))
      (2 * Bb (Dc.m n)) (Dlow (Dc.j n)) (by linarith [hB (Dc.m n)]) (hDlow0 (Dc.j n) hj)
      (fun d Y Z hd hY hZ =>
        Work.Diff.EXT.ConnCov.DT.gtTower_val_bound (I := I) (M := M) hLC G t x (Dc.m n)
          (Bb (Dc.m n))
          (hB (Dc.m n)) ((Work.Diff.EXT.ConnCov.DT.aOfTower_val_bound hLC G t (Dc.m n)
            (Bb (Dc.m n)) (hA (Dc.m n) hmk t ht)) x) d Y Z hd hY hZ)
      (fun d Y X hd hY hX => (hDlow (Dc.j n) hj t ht) d Y X x hd hY hX)
      v A B C hv hA' hB' hC'
  -- the sum of the expansion terms
  have hsum : |∑ n : Dc.ι,
        Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
          (Dc.F n) (Dc.G' n) v A B C x|
      ≤ (∑ n : Dc.ι, 2 * Bb (Dc.m n) * Dlow (Dc.j n))
        * ((Finset.univ.prod (fun p : Fin k =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => hterm n)) ?_
    exact le_of_eq (Finset.sum_mul ..).symm
  -- assembly
  calc |Work.Diff.EXT.ConnCov.DT.Wterm G t k v A B C x|
      = |tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x
          - ∑ n : Dc.ι,
              Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
                (Dc.F n) (Dc.G' n) v A B C x| := by
        rw [hW]
    _ ≤ |tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x|
          + |∑ n : Dc.ι,
              Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
                (Dc.F n) (Dc.G' n) v A B C x| := by
        rw [sub_eq_add_neg]
        calc |tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x
              + -(∑ n : Dc.ι,
                  Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
                    (Dc.F n) (Dc.G' n) v A B C x)|
            ≤ |tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k v A B C x|
              + |-(∑ n : Dc.ι,
                  Work.Diff.EXT.ConnCov.DT.selTerm G t k (Dc.m n + 1) (Dc.j n)
                    (Dc.F n) (Dc.G' n) v A B C x)| :=
              abs_add_le _ _
          _ = _ := by rw [abs_neg]
    _ ≤ ρ * ((Finset.univ.prod (fun p : Fin k =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x)))
          + (∑ n : Dc.ι, 2 * Bb (Dc.m n) * Dlow (Dc.j n))
            * ((Finset.univ.prod (fun p : Fin k =>
                  (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
                * Real.sqrt ((G t).inner x (A x) (A x))
                * Real.sqrt ((G t).inner x (B x) (B x))
                * Real.sqrt ((G t).inner x (C x) (C x))) := add_le_add htow hsum
    _ = (ρ + ∑ n : Dc.ι, 2 * Bb (Dc.m n) * Dlow (Dc.j n))
          * ((Finset.univ.prod (fun p : Fin k =>
                (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
              * Real.sqrt ((G t).inner x (A x) (A x))
              * Real.sqrt ((G t).inner x (B x) (B x))
              * Real.sqrt ((G t).inner x (C x) (C x))) := by
        ring

/-! ## (3) The affine `TB`-bound

From the affine bound of the lowering `Wterm` at level `k` (the metric is an isometry for its own
pairing) follows the affine bound of the `δ`-tower itself. -/

theorem TB_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (T : ℝ)
    (k : ℕ) (Bb : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bb j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) j) (Bb j))
    {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ValBound G t k (tower (Submission.Diff.lcOf (G 0)) (fun _ => aOf G t) k) ρ)
    (Dc : Work.Diff.EXT.ConnCov.DT.CombData k)
    (hDcx : ∀ (G' : ℝ → Submission.Diff.SMet I M) (t' : ℝ),
      Work.Diff.EXT.ConnCov.DT.OpEqSel
        (tower (Submission.Diff.lcOf (G' 0)) (fun _ => aOf G' t') k)
        (fun v A B C y => Work.Diff.EXT.ConnCov.DT.Wterm G' t' k v A B C y
          + Work.Diff.EXT.ConnCov.DT.CombTerm Dc G' t' v A B C y))
    (Dlow : ℕ → ℝ) (hDlow0 : ∀ j, j < k → 0 ≤ Dlow j)
    (hDlow : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.DT.TB G t j (Dlow j)) :
    Work.Diff.EXT.ConnCov.DT.TB G t k (ρ + ∑ n : Dc.ι, 2 * Bb (Dc.m n) * Dlow (Dc.j n)) := by
  have h0 : 0 ≤ ρ + ∑ n : Dc.ι, 2 * Bb (Dc.m n) * Dlow (Dc.j n) := by
    refine add_nonneg hρ0 (Finset.sum_nonneg (fun n _ => ?_))
    have hj : Dc.j n < k := by have := Dc.hmj n; omega
    exact mul_nonneg (mul_nonneg (by norm_num) (hB (Dc.m n))) (hDlow0 (Dc.j n) hj)
  refine Work.Diff.EXT.ConnCov.DT.TB_of_wterm_bound (I := I) (M := M) G t h0 ?_
  intro v A B C x hv hA' hB' hC'
  exact wterm_bound_affine (I := I) (M := M) hLC G T k Bb hB hA ht hρ0 hρ Dc hDcx Dlow hDlow0
    hDlow v A B C x hv hA' hB' hC'

/-! ## (4) From the moving-metric bound to the `AMB.BndV` shape

`Work.Diff.EXT.ConnCov.AMB.BndV G t Θ C` is the bound of the value of `Θ` in the `G t`-norm with
the `(1 + √·)`-factors on all slots; `DT.TB` differs from it by the use of `√(Y,Y)`, `√(X,X)` for
the two section slots (and by the sign of `Θ`, which does not matter). -/

lemma bndV_of_TB_flip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    {t : ℝ} {c : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (h : Work.Diff.EXT.ConnCov.DT.TB G t c D) :
    Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) G t
      (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
        (fun s : ℝ => G (t - s)) t c) D := by
  intro v X Z hv hX hZ x
  have hbridge : Work.Diff.EXT.ConnCov.DTB.deltaTower G t c
      = Work.Diff.EXT.ConnCov.DT.deltaTower G t c :=
    Work.Diff.EXT.ConnCov.RicTr.DTB_deltaTower_eq_DT (I := I) (M := M) G t c
  have hflip := deltaTowerM_flip (I := I) (M := M) hLC G t
    (Ĝ := fun s : ℝ => G (t - s)) (by simp) (by simp) c v X Z hv hX hZ
  have hval : (G t).inner x
        (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
          (fun s : ℝ => G (t - s)) t c v X Z x)
        (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
          (fun s : ℝ => G (t - s)) t c v X Z x)
      = (G t).inner x (Work.Diff.EXT.ConnCov.DT.deltaTower G t c v X Z x)
        (Work.Diff.EXT.ConnCov.DT.deltaTower G t c v X Z x) := by
    rw [hflip, hbridge]
    simp
  rw [hval]
  have hb := h v X Z x hv hX hZ
  -- the `√`-factors of the two section slots are dominated by the `(1 + √)`-factors
  set P : ℝ := ∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))) with hP
  set sX : ℝ := Real.sqrt ((G t).inner x (X x) (X x)) with hsX
  set sZ : ℝ := Real.sqrt ((G t).inner x (Z x) (Z x)) with hsZ
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.prod_nonneg (fun i _ => by
      have := Real.sqrt_nonneg ((G t).inner x (v i x) (v i x)); linarith)
  have hsX0 : 0 ≤ sX := by rw [hsX]; exact Real.sqrt_nonneg _
  have hsZ0 : 0 ≤ sZ := by rw [hsZ]; exact Real.sqrt_nonneg _
  have hDP : 0 ≤ D * P := mul_nonneg hD hP0
  have e1 : D * P * sX * sZ ≤ D * P * (1 + sX) * sZ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hDP) hsZ0
  have e2 : D * P * (1 + sX) * sZ ≤ D * P * (1 + sX) * (1 + sZ) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hDP (by linarith))
  exact le_trans hb (le_trans e1 e2)

/-- The metric comparison factor of `bndV_metric_le` on `[T/2, T)` at the level `c`. -/
lemma expFactor_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {C₀ T : ℝ} (hT : 0 < T) (hC₀ : 0 ≤ C₀) (c : ℕ) :
    0 ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2) ^ c
        * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2)
        * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2)
        * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2) := by
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
  have h1 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) := by
    have := mul_nonneg hn0 hC₀; linarith
  have h2 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2 := by
    have := mul_nonneg h1 hT.le; linarith
  have h3 : 0 ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2) := Real.exp_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg h3 c) h3) h3) h3

theorem deltaAtomAffineBndV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * t) * (G t).inner x u u)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ (W : ℕ → ℝ) (A Cu : ℝ), (∀ c, 0 ≤ W c) ∧ 0 ≤ A ∧ 0 ≤ Cu ∧
      (∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
        Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
            (fun s : ℝ => G (t - s)) t c) (W c)) ∧
      (∀ t ∈ Set.Ico (T / 2) T, ∀ ρ : ℝ, 0 ≤ ρ →
        Work.Diff.EXT.ATower.ValBound G t k
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) k) ρ →
        Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
            (fun s : ℝ => G (t - s)) t k) (A + Cu * ρ)) := by
  -- the metric comparison factor on `[T/2, T)`
  set e : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2) with he
  have he1 : 1 ≤ e := by
    rw [he]
    apply Real.one_le_exp
    have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
    have h1 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) := by
      have := mul_nonneg hn0 hC₀; linarith
    have h2 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) * T := mul_nonneg h1 hT.le
    linarith
  have he0 : 0 ≤ e := le_trans zero_le_one he1
  -- the lower-level `δ`-tower bounds
  obtain ⟨Dlow, hDlow0, hDlowB⟩ :=
    exists_TB_low (I := I) (M := M) hLC G T hT k B hB hA
  -- the Leibniz-expansion data at level `k`
  obtain ⟨Dc, hDcx⟩ := Work.Diff.EXT.ConnCov.DT.exists_combData (I := I) (M := M) hLC k
  -- the affine constant of the top level
  set Ssum : ℝ := ∑ n : Dc.ι, 2 * B (Dc.m n) * Dlow (Dc.j n) with hSsum
  have hSsum0 : 0 ≤ Ssum := by
    rw [hSsum]
    refine Finset.sum_nonneg (fun n _ => ?_)
    have hj : Dc.j n < k := by have := Dc.hmj n; omega
    exact mul_nonneg (mul_nonneg (by norm_num) (hB (Dc.m n))) (hDlow0 (Dc.j n))
  have hLa0 : 0 ≤ e ^ k * e * e * e :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg he0 k) he0) he0) he0
  refine ⟨fun c => Dlow c * e ^ c * e * e * e, Ssum * (e ^ k * e * e * e), e ^ k * e * e * e,
    ?_, mul_nonneg hSsum0 hLa0, hLa0, ?_, ?_⟩
  · -- nonnegativity of `W`
    intro c
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hDlow0 c) (pow_nonneg he0 c)) he0)
      he0) he0
  · -- the levels `< k`
    intro c hc t ht
    have hc0 : 0 ≤ Dlow c := hDlow0 c
    have hb := bndV_of_TB_flip (I := I) (M := M) hLC G (t := t) (c := c) (D := Dlow c) hc0
      (hDlowB c hc t ht)
    have h2 := bndV_metric_le (I := I) (M := M) (G := G) (C₀ := C₀) (T := T) hT hC₀ hmet ht
      (Θ := Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
        (fun s : ℝ => G (t - s)) t c) (C := Dlow c) hc0 hb
    simpa only [he] using h2
  · -- the top level: affine in `ρ`
    intro t ht ρ hρ0 hρ
    have hTB := TB_affine (I := I) (M := M) hLC G T k B hB hA ht hρ0 hρ Dc hDcx Dlow
      (fun j _ => hDlow0 j) hDlowB
    have hS0 : 0 ≤ ρ + Ssum := by rw [hSsum]; exact add_nonneg hρ0 hSsum0
    have hb := bndV_of_TB_flip (I := I) (M := M) hLC G (t := t) (c := k)
      (D := ρ + Ssum) hS0 hTB
    have h2 := bndV_metric_le (I := I) (M := M) (G := G) (C₀ := C₀) (T := T) hT hC₀ hmet ht
      (Θ := Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
        (fun s : ℝ => G (t - s)) t k) (C := ρ + Ssum) hS0 hb
    have hgoal : Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
        (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
          (fun s : ℝ => G (t - s)) t k)
        (Ssum * (e ^ k * e * e * e) + (e ^ k * e * e * e) * ρ) := by
      convert h2 using 2
      rw [he]
      ring
    exact hgoal

end Work.Diff.EXT.ATower
