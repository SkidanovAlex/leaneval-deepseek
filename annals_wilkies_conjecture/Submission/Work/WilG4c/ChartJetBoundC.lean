/-
  WilG4c — the per-cell engine's chart-jet bound, with genuine smoothness hypotheses.

  `cellChart χ M W ψ l z` is the chart of the `(n+1)`-cube built from a base parametrisation `χ`,
  an `n`-cube chart `ψ` and the midpoint/half-width functions `M`, `W`:

  * coordinates `j < n` are `χ l (ψ l (Fin.init z)) j`;
  * the last coordinate is `M l (ψ l (Fin.init z)) + (z_last - 1/2) (2 W l (ψ l (Fin.init z)) - 1/2)`.

  The theorem bounds the jet norm `Σ_{1 ≤ k ≤ r} ‖D^k chart(z)‖/k!` on the open cube by a
  constant `S₀` depending only on `n`, uniformly in `r`, `χ`, `ψ`, `M`, `W`, `l` and `z`,
  under the hypotheses that the composites `u ↦ χ l (ψ l u) j`, `u ↦ M l (ψ l u)`,
  `u ↦ W l (ψ l u)` are `C^r` on the `n`-cube with all iterated derivatives of norm `≤ 1`.

  The structure of the proof:

  * the norm of the jet of a map into `Fin (n+1) → ℝ` is at most the sum of the norms of the
    coordinate jets (`NormIteratedFDerivPiSum`);
  * each interior coordinate is `χ_j ∘ Fin.init`, and composing with the linear projection
    `Fin.init` cannot increase the jet (`NormIteratedFDerivCompLinearGeneral`, `‖Fin.init‖ ≤ 1`);
  * the last coordinate is `M ∘ Fin.init` plus the product of the affine function
    `z ↦ z_last - 1/2` (all of whose iterated derivatives have norm `≤ 1` on the cube:
    `NormIteratedFDerivCoordSubHalf`) with `2 (W ∘ Fin.init) - 1/2`
    (all of whose iterated derivatives have norm `≤ 5/2`: `NormIteratedFDerivTwoMulSubHalf`);
    Leibniz plus `Σ_i C(k,i) = 2^k` gives the bound `1 + (5/2) 2^k` for the `k`-th derivative;
  * summing against `1/k!` and using `Σ_k x^k/k! ≤ exp x` yields
    `S₀ = (n+1) (exp 1 + (5/2) exp 2) + 1`.
-/
import Mathlib
import Submission.Work.WilG4c.EngineDefs
import Submission.Work.WilG4c.cellChart_contDiffOn
import Submission.Work.WilG2.Tnorm
import Submission.Work.WilG4c.NormIteratedFDerivPiSum
import Submission.Work.WilG4c.NormIteratedFDerivCompLinearGeneral
import Submission.Work.WilG4c.NormIteratedFDerivCoordSubHalf
import Submission.Work.WilG4c.NormIteratedFDerivTwoMulSubHalf

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ### the map `Fin.init` as a continuous linear map -/

/-- `Fin.init` (forget the last coordinate of a tuple) as a continuous linear map. -/
noncomputable def initL (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n =>
    (ContinuousLinearMap.proj i.castSucc : (Fin (n + 1) → ℝ) →L[ℝ] ℝ))

theorem initL_apply (n : ℕ) (x : Fin (n + 1) → ℝ) : initL n x = Fin.init x := by
  ext i
  simp [initL, Fin.init_def]

/-- The operator norm of `Fin.init` is at most `1`. -/
theorem norm_initL_le (n : ℕ) : ‖initL n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  rw [initL_apply, Fin.init_def]
  exact norm_le_pi_norm x i.castSucc

/-- `Fin.init` maps the open `(n+1)`-cube into the open `n`-cube. -/
theorem initL_mem (n : ℕ) {x : Fin (n + 1) → ℝ} (hx : x ∈ openCube (n + 1)) :
    initL n x ∈ openCube n := by
  intro i
  have h : (initL n x) i = x i.castSucc := by rw [initL_apply, Fin.init_def]
  rw [h]
  exact hx i.castSucc

/-! ### the chart-jet bound -/

theorem ChartJetBoundC (p n : ℕ) : ∃ S₀ : ℝ, 1 ≤ S₀ ∧ ∀ (r : ℕ)
    (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (l : Fin p → ℝ),
    (∀ j : Fin n, ContDiffOn ℝ r (fun u : Fin n → ℝ => χ l (ψ l u) j)
      (WilkiesDesign.openCube n)) →
    (ContDiffOn ℝ r (fun u : Fin n → ℝ => M l (ψ l u)) (WilkiesDesign.openCube n)) →
    (ContDiffOn ℝ r (fun u : Fin n → ℝ => W l (ψ l u)) (WilkiesDesign.openCube n)) →
    (∀ j : Fin n, ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => χ l (ψ l u) j) t‖ ≤ 1) →
    (∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => M l (ψ l u)) t‖ ≤ 1) →
    (∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => W l (ψ l u)) t‖ ≤ 1) →
    ∀ z ∈ WilkiesDesign.openCube (n + 1),
      ∑ k ∈ Finset.Ico 1 (r + 1),
        ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ =>
          Work.WilG4c.cellChart χ M W ψ l y) z‖ / (k.factorial : ℝ) ≤ S₀ := by
  refine ⟨((n : ℝ) + 1) * (Real.exp 1 + 5 / 2 * Real.exp 2) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ ((n : ℝ) + 1) * (Real.exp 1 + 5 / 2 * Real.exp 2) := by positivity
    linarith
  · intro r χ ψ M W l hχ hM hW hχb hMb hWb z hz
    set K : ℝ := Real.exp 1 + 5 / 2 * Real.exp 2 with hKdef
    set chart : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
      fun y => cellChart χ M W ψ l y with hchartdef
    have hchart : ContDiffOn ℝ r chart (openCube (n + 1)) := by
      rw [hchartdef]
      exact cellChart_contDiffOn χ ψ M W l hχ hM hW
    -- Step 1: bound the whole jet by the sum of the coordinate jets.
    have hstep1 : ∑ k ∈ Finset.Ico 1 (r + 1),
          ‖iteratedFDeriv ℝ k chart z‖ / (k.factorial : ℝ)
        ≤ ∑ j : Fin (n + 1), ∑ k ∈ Finset.Ico 1 (r + 1),
          ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖
            / (k.factorial : ℝ) := by
      calc ∑ k ∈ Finset.Ico 1 (r + 1), ‖iteratedFDeriv ℝ k chart z‖ / (k.factorial : ℝ)
          ≤ ∑ k ∈ Finset.Ico 1 (r + 1),
              ∑ j : Fin (n + 1),
                ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖
                  / (k.factorial : ℝ) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have hkr : k ≤ r := by
              have := (Finset.mem_Ico.mp hk).2; omega
            have hck : ContDiffAt ℝ k chart z :=
              (hchart.of_le (by exact_mod_cast hkr)).contDiffAt
                ((Work.WilkG4c.openCube_isOpen (n + 1)).mem_nhds hz)
            have h := NormIteratedFDerivPiSum (f := chart) (x := z) hck
            calc ‖iteratedFDeriv ℝ k chart z‖ / (k.factorial : ℝ)
                ≤ (∑ j : Fin (n + 1),
                    ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖)
                    / (k.factorial : ℝ) :=
                  div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
              _ = ∑ j : Fin (n + 1),
                    ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖
                      / (k.factorial : ℝ) := Finset.sum_div _ _ _
        _ = ∑ j : Fin (n + 1), ∑ k ∈ Finset.Ico 1 (r + 1),
                ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖
                  / (k.factorial : ℝ) := Finset.sum_comm
    -- Step 2: each coordinate jet-sum is at most `K`.
    have hcoord : ∀ j : Fin (n + 1), ∑ k ∈ Finset.Ico 1 (r + 1),
        ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖
          / (k.factorial : ℝ) ≤ K := by
      intro j
      by_cases hj : (j : ℕ) = n
      · -- the last coordinate
        have hjlast : j = Fin.last n := Fin.ext (by rw [Fin.val_last]; exact hj)
        rw [hjlast]
        have hlast : ∀ y : Fin (n + 1) → ℝ, chart y (Fin.last n) =
            M l (ψ l (Fin.init y)) + (y (Fin.last n) - 1 / 2) *
              (2 * W l (ψ l (Fin.init y)) - 1 / 2) := by
          intro y
          rw [hchartdef]
          simp only [cellChart]
          rw [dite_eq_left (Fin.val_last n)]
        have hfun : (fun y : Fin (n + 1) → ℝ => chart y (Fin.last n)) =
            fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y)) + (y (Fin.last n) - 1 / 2) *
              (2 * W l (ψ l (initL n y)) - 1 / 2) := by
          funext y
          rw [hlast y, initL_apply]
        rw [hfun]
        have hBc : ContDiffOn ℝ r (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y)))
            (openCube (n + 1)) :=
          (hM.comp_continuousLinearMap (initL n)).mono (fun y hy => initL_mem n hy)
        have hCc : ContDiffOn ℝ r (fun y : Fin (n + 1) → ℝ => W l (ψ l (initL n y)))
            (openCube (n + 1)) :=
          (hW.comp_continuousLinearMap (initL n)).mono (fun y hy => initL_mem n hy)
        have hopen1 : IsOpen (openCube (n + 1)) := Work.WilkG4c.openCube_isOpen (n + 1)
        have hopenn : IsOpen (openCube n) := Work.WilkG4c.openCube_isOpen n
        have hBcAt : ContDiffAt ℝ r (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y))) z :=
          hBc.contDiffAt (hopen1.mem_nhds hz)
        have hCcAt : ContDiffAt ℝ r (fun y : Fin (n + 1) → ℝ => W l (ψ l (initL n y))) z :=
          hCc.contDiffAt (hopen1.mem_nhds hz)
        have hhAt : ContDiffAt ℝ r
            (fun y : Fin (n + 1) → ℝ => 2 * W l (ψ l (initL n y)) - 1 / 2) z :=
          ((contDiffAt_const (c := (2 : ℝ))).mul hCcAt).sub contDiffAt_const
        have haAt : ContDiffAt ℝ r (fun y : Fin (n + 1) → ℝ => y (Fin.last n) - 1 / 2) z :=
          (contDiffAt_apply ℝ ℝ (Fin.last n) z).sub contDiffAt_const
        -- jet bound for the inner half-width factor
        have hWjet : ∀ m, m ≤ r →
            ‖iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => W l (ψ l (initL n y))) z‖ ≤ 1 := by
          intro m hm
          have hAt : ContDiffAt ℝ m (fun u : Fin n → ℝ => W l (ψ l u)) (initL n z) :=
            (hW.of_le (by exact_mod_cast hm)).contDiffAt
              (hopenn.mem_nhds (initL_mem n hz))
          have h := NormIteratedFDerivCompLinearGeneral (initL n)
            (fun u : Fin n → ℝ => W l (ψ l u)) z m hAt
          calc ‖iteratedFDeriv ℝ m (fun y : Fin (n + 1) → ℝ => W l (ψ l (initL n y))) z‖
              ≤ ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ => W l (ψ l u)) (initL n z)‖
                  * ‖initL n‖ ^ m := h
            _ ≤ 1 * 1 := mul_le_mul (hWb m hm (initL n z) (initL_mem n hz))
                  (pow_le_one₀ (norm_nonneg _) (norm_initL_le n)) (by positivity) (by norm_num)
            _ = 1 := one_mul 1
        have hhjet : ∀ m, m ≤ r →
            ‖iteratedFDeriv ℝ m
              (fun y : Fin (n + 1) → ℝ => 2 * W l (ψ l (initL n y)) - 1 / 2) z‖ ≤ 5 / 2 :=
          NormIteratedFDerivTwoMulSubHalf r
            (fun y : Fin (n + 1) → ℝ => W l (ψ l (initL n y))) z hCcAt hWjet
        have hterm : ∀ k ∈ Finset.Ico 1 (r + 1),
            ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y)) +
              (y (Fin.last n) - 1 / 2) * (2 * W l (ψ l (initL n y)) - 1 / 2)) z‖
              / (k.factorial : ℝ) ≤ (1 + 5 / 2 * 2 ^ k) / (k.factorial : ℝ) := by
          intro k hk
          have hkr : k ≤ r := by
            have := (Finset.mem_Ico.mp hk).2; omega
          have hBk : ContDiffAt ℝ k (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y))) z :=
            hBcAt.of_le (by exact_mod_cast hkr)
          have hhk : ContDiffAt ℝ k
              (fun y : Fin (n + 1) → ℝ => 2 * W l (ψ l (initL n y)) - 1 / 2) z :=
            hhAt.of_le (by exact_mod_cast hkr)
          have hak : ContDiffAt ℝ k (fun y : Fin (n + 1) → ℝ => y (Fin.last n) - 1 / 2) z :=
            haAt.of_le (by exact_mod_cast hkr)
          have habk : ContDiffAt ℝ k
              (fun y : Fin (n + 1) → ℝ => (y (Fin.last n) - 1 / 2) *
                (2 * W l (ψ l (initL n y)) - 1 / 2)) z := hak.mul hhk
          have hsplit : iteratedFDeriv ℝ k
                (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y)) +
                  (y (Fin.last n) - 1 / 2) * (2 * W l (ψ l (initL n y)) - 1 / 2)) z
              = iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y))) z
                + iteratedFDeriv ℝ k
                  (fun y : Fin (n + 1) → ℝ => (y (Fin.last n) - 1 / 2) *
                    (2 * W l (ψ l (initL n y)) - 1 / 2)) z :=
            iteratedFDeriv_add_apply hBk habk
          have hPB : ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y))) z‖
              ≤ 1 := by
            have hAt : ContDiffAt ℝ k (fun u : Fin n → ℝ => M l (ψ l u)) (initL n z) :=
              (hM.of_le (by exact_mod_cast hkr)).contDiffAt
                (hopenn.mem_nhds (initL_mem n hz))
            have h := NormIteratedFDerivCompLinearGeneral (initL n)
              (fun u : Fin n → ℝ => M l (ψ l u)) z k hAt
            calc ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y))) z‖
                ≤ ‖iteratedFDeriv ℝ k (fun u : Fin n → ℝ => M l (ψ l u)) (initL n z)‖
                    * ‖initL n‖ ^ k := h
              _ ≤ 1 * 1 := mul_le_mul (hMb k hkr (initL n z) (initL_mem n hz))
                    (pow_le_one₀ (norm_nonneg _) (norm_initL_le n)) (by positivity) (by norm_num)
              _ = 1 := one_mul 1
          have hmul : ‖iteratedFDeriv ℝ k
                (fun y : Fin (n + 1) → ℝ => (y (Fin.last n) - 1 / 2) *
                  (2 * W l (ψ l (initL n y)) - 1 / 2)) z‖ ≤ 5 / 2 * 2 ^ k := by
            have hm := WilkiesDesign.CG.norm_iteratedFDeriv_mul_le_at r k hkr
              (fun y : Fin (n + 1) → ℝ => y (Fin.last n) - 1 / 2)
              (fun y : Fin (n + 1) → ℝ => 2 * W l (ψ l (initL n y)) - 1 / 2) z haAt hhAt
            have hch : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
              rw [← Nat.cast_sum, Nat.sum_range_choose]
              simp only [Nat.cast_pow, Nat.cast_ofNat]
            calc ‖iteratedFDeriv ℝ k
                    (fun y : Fin (n + 1) → ℝ => (y (Fin.last n) - 1 / 2) *
                      (2 * W l (ψ l (initL n y)) - 1 / 2)) z‖
                ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
                    ‖iteratedFDeriv ℝ i (fun y : Fin (n + 1) → ℝ => y (Fin.last n) - 1 / 2) z‖ *
                    ‖iteratedFDeriv ℝ (k - i)
                      (fun y : Fin (n + 1) → ℝ => 2 * W l (ψ l (initL n y)) - 1 / 2) z‖ := hm
              _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * 1 * (5 / 2) := by
                refine Finset.sum_le_sum (fun i hi => ?_)
                have h1 : ‖iteratedFDeriv ℝ i
                    (fun y : Fin (n + 1) → ℝ => y (Fin.last n) - 1 / 2) z‖ ≤ 1 :=
                  NormIteratedFDerivCoordSubHalf (Fin.last n) z hz i
                have h2 : ‖iteratedFDeriv ℝ (k - i)
                    (fun y : Fin (n + 1) → ℝ => 2 * W l (ψ l (initL n y)) - 1 / 2) z‖ ≤ 5 / 2 :=
                  hhjet (k - i) (by omega)
                have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
                exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
                  (by positivity)
              _ = 5 / 2 * 2 ^ k := by
                calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * 1 * (5 / 2)
                    = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (5 / 2) := by
                      rw [Finset.sum_mul]
                      refine Finset.sum_congr rfl (fun i _ => by ring)
                  _ = (2 : ℝ) ^ k * (5 / 2) := by rw [hch]
                  _ = 5 / 2 * 2 ^ k := by ring
          have hmain : ‖iteratedFDeriv ℝ k
                (fun y : Fin (n + 1) → ℝ => M l (ψ l (initL n y)) +
                  (y (Fin.last n) - 1 / 2) * (2 * W l (ψ l (initL n y)) - 1 / 2)) z‖
              ≤ 1 + 5 / 2 * 2 ^ k := by
            rw [hsplit]
            exact (norm_add_le _ _).trans (add_le_add hPB hmul)
          exact div_le_div_of_nonneg_right hmain (Nat.cast_nonneg _)
        have hsub : Finset.Ico 1 (r + 1) ⊆ Finset.range (r + 1) :=
          fun k hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        refine le_trans (Finset.sum_le_sum hterm) ?_
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => by positivity)) ?_
        calc ∑ k ∈ Finset.range (r + 1), (1 + 5 / 2 * 2 ^ k) / (k.factorial : ℝ)
            = ∑ k ∈ Finset.range (r + 1),
                (1 / (k.factorial : ℝ) + (5 / 2) * (2 ^ k / (k.factorial : ℝ))) := by
              refine Finset.sum_congr rfl (fun k _ => by ring)
          _ = (∑ k ∈ Finset.range (r + 1), 1 / (k.factorial : ℝ)) +
                (5 / 2) * ∑ k ∈ Finset.range (r + 1), 2 ^ k / (k.factorial : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ Real.exp 1 + 5 / 2 * Real.exp 2 := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num))
              · simpa using Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) zero_le_one (r + 1)
              · exact Real.sum_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num) (r + 1)
          _ = K := hKdef.symm
      · -- an interior coordinate
        have hjlt : (j : ℕ) < n := by
          have h := j.isLt; omega
        have hnotlast : ∀ y : Fin (n + 1) → ℝ, chart y j =
            χ l (ψ l (Fin.init y)) ⟨(j : ℕ), hjlt⟩ := by
          intro y
          rw [hchartdef]
          simp only [cellChart]
          rw [dite_eq_right hj]
        have hfun : (fun y : Fin (n + 1) → ℝ => chart y j) =
            fun y : Fin (n + 1) → ℝ =>
              (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩) (initL n y) := by
          funext y
          rw [hnotlast y, initL_apply]
        rw [hfun]
        have hopenn : IsOpen (openCube n) := Work.WilkG4c.openCube_isOpen n
        have hjAt : ContDiffAt ℝ r (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩)
            (initL n z) :=
          (hχ ⟨(j : ℕ), hjlt⟩).contDiffAt (hopenn.mem_nhds (initL_mem n hz))
        have hterm : ∀ k ∈ Finset.Ico 1 (r + 1),
            ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ =>
              (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩) (initL n y)) z‖
              / (k.factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
          intro k hk
          have hkr : k ≤ r := by
            have := (Finset.mem_Ico.mp hk).2; omega
          have hAt : ContDiffAt ℝ k (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩)
              (initL n z) := hjAt.of_le (by exact_mod_cast hkr)
          have h := NormIteratedFDerivCompLinearGeneral (initL n)
            (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩) z k hAt
          have hb : ‖iteratedFDeriv ℝ k (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩)
              (initL n z)‖ ≤ 1 :=
            hχb ⟨(j : ℕ), hjlt⟩ k hkr (initL n z) (initL_mem n hz)
          have hbound : ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ =>
              (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩) (initL n y)) z‖ ≤ 1 := by
            calc ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ =>
                    (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩) (initL n y)) z‖
                ≤ ‖iteratedFDeriv ℝ k (fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩)
                    (initL n z)‖ * ‖initL n‖ ^ k := h
              _ ≤ 1 * 1 := mul_le_mul hb (pow_le_one₀ (norm_nonneg _) (norm_initL_le n))
                    (by positivity) (by norm_num)
              _ = 1 := one_mul 1
          exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg _)
        have hsub : Finset.Ico 1 (r + 1) ⊆ Finset.range (r + 1) :=
          fun k hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        refine le_trans (Finset.sum_le_sum hterm) ?_
        calc ∑ k ∈ Finset.Ico 1 (r + 1), 1 / (k.factorial : ℝ)
            ≤ ∑ k ∈ Finset.range (r + 1), 1 / (k.factorial : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
          _ ≤ Real.exp 1 := by
              simpa using Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) zero_le_one (r + 1)
          _ ≤ K := by
              rw [hKdef]
              exact le_add_of_nonneg_right (by positivity)
    -- Step 3: assemble
    calc ∑ k ∈ Finset.Ico 1 (r + 1), ‖iteratedFDeriv ℝ k chart z‖ / (k.factorial : ℝ)
        ≤ ∑ j : Fin (n + 1), ∑ k ∈ Finset.Ico 1 (r + 1),
            ‖iteratedFDeriv ℝ k (fun y : Fin (n + 1) → ℝ => chart y j) z‖
              / (k.factorial : ℝ) := hstep1
      _ ≤ ∑ _j : Fin (n + 1), K := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = ((n : ℝ) + 1) * K := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_add, Nat.cast_one]
      _ ≤ ((n : ℝ) + 1) * K + 1 := le_add_of_nonneg_right zero_le_one

end Work.WilG4c
