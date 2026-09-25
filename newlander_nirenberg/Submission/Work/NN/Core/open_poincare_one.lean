import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.dbar_interior_oneshot
import Submission.Work.NN.Core.dbar_solver_open_ratio

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

/-! ## Interpolating multi-radii

Between two multi-radii `ρ'` and `ρo` (with `ρ' j < ρo j` and `ρo j ≤ ρ j` for all `j`) we
interpolate a chain of polydiscs, used to iterate the one-step interior Schauder estimate
`Work.CR.Flat.Cauchy.dbar_interior_oneshot` from the outer polydisc `ρo` down to `ρ'`. -/

/-- The `i`-th interpolated multi-radius between `ρ'` and `ρo` (with `k+2` steps). -/
noncomputable def chainRad {n : ℕ} (k : ℕ) (ρ' ρo : Fin n → ℝ) (i : ℕ) : Fin n → ℝ :=
  fun j => ρ' j + (i : ℝ) * ((ρo j - ρ' j) / ((k : ℝ) + 2))

variable {n : ℕ}

lemma chainRad_apply {k : ℕ} {ρ' ρo : Fin n → ℝ} {i : ℕ} {j : Fin n} :
    chainRad k ρ' ρo i j = ρ' j + (i : ℝ) * ((ρo j - ρ' j) / ((k : ℝ) + 2)) := rfl

@[simp] lemma chainRad_zero (k : ℕ) (ρ' ρo : Fin n → ℝ) : chainRad k ρ' ρo 0 = ρ' := by
  funext j
  simp [chainRad]

lemma chainRad_succ {k : ℕ} {ρ' ρo : Fin n → ℝ} (i : ℕ) (j : Fin n) :
    chainRad k ρ' ρo (i + 1) j = chainRad k ρ' ρo i j + (ρo j - ρ' j) / ((k : ℝ) + 2) := by
  simp only [chainRad_apply]
  push_cast
  ring

lemma chainRad_top {k : ℕ} {ρ' ρo : Fin n → ℝ} : chainRad k ρ' ρo (k + 2) = ρo := by
  funext j
  have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  simp only [chainRad_apply, hcast]
  field_simp
  ring

lemma chainRad_pos {k : ℕ} {ρ' ρo : Fin n → ℝ} (hρ' : ∀ j, 0 < ρ' j)
    (hρ'ρo : ∀ j, ρ' j ≤ ρo j) (i : ℕ) (j : Fin n) : 0 < chainRad k ρ' ρo i j := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have ht : 0 ≤ (ρo j - ρ' j) / ((k : ℝ) + 2) := div_nonneg (by linarith [hρ'ρo j]) hk.le
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hnn : 0 ≤ (i : ℝ) * ((ρo j - ρ' j) / ((k : ℝ) + 2)) := mul_nonneg hi ht
  simp only [chainRad_apply]
  linarith [hρ' j, hnn]

lemma chainRad_lt_of_lt {k : ℕ} {ρ' ρo : Fin n → ℝ} (hlt : ∀ j, ρ' j < ρo j) {i i' : ℕ}
    (h : i < i') (j : Fin n) : chainRad k ρ' ρo i j < chainRad k ρ' ρo i' j := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have ht : 0 < (ρo j - ρ' j) / ((k : ℝ) + 2) := div_pos (by linarith [hlt j]) hk
  have hcast : (i : ℝ) < (i' : ℝ) := by exact_mod_cast h
  have hmul := mul_lt_mul_of_pos_right hcast ht
  simp only [chainRad_apply]
  linarith

lemma chainRad_mono {k : ℕ} {ρ' ρo : Fin n → ℝ} (hlt : ∀ j, ρ' j < ρo j) {i i' : ℕ}
    (h : i ≤ i') (j : Fin n) : chainRad k ρ' ρo i j ≤ chainRad k ρ' ρo i' j := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [h']
  · exact le_of_lt (chainRad_lt_of_lt hlt h' j)

lemma chainRad_le {k : ℕ} {ρ' ρo ρ : Fin n → ℝ} (hρ'ρo : ∀ j, ρ' j ≤ ρo j)
    (hle : ∀ j, ρo j ≤ ρ j) {i : ℕ} (h : i ≤ k + 2) (j : Fin n) :
    chainRad k ρ' ρo i j ≤ ρ j := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have ht : 0 ≤ (ρo j - ρ' j) / ((k : ℝ) + 2) := div_nonneg (by linarith [hρ'ρo j]) hk.le
  have hcast : (i : ℝ) ≤ ((k : ℝ) + 2) := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this ⊢
    linarith
  have hmul : (i : ℝ) * ((ρo j - ρ' j) / ((k : ℝ) + 2))
      ≤ ((k : ℝ) + 2) * ((ρo j - ρ' j) / ((k : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right hcast ht
  have hcancel : ((k : ℝ) + 2) * ((ρo j - ρ' j) / ((k : ℝ) + 2)) = ρo j - ρ' j := by
    field_simp
  simp only [chainRad_apply]
  linarith [hle j, hcancel, hmul]

/-! ## The interior Schauder iterate with an arbitrary ratio -/

/-- **The interior Schauder estimate with a gain of one derivative, at an arbitrary ratio.**

Let `ρ' < ρo ≤ ρ` (componentwise), let `u` be a `C^{k+1}` solution of the flat `∂̄`-equation
`∂̄_j u = f_j` on the polydisc `polydisc 0 ρo`, with `f` closed and `C^{k+1}`.  Then
`‖u‖_{C^{k+1,α}(polydisc 0 ρ')}` is controlled by the `C^{k,α}` norms of the data on the larger
polydisc `polydisc 0 ρ` together with the single `C^{0,α}` norm of `u` on `polydisc 0 ρo`.

This is `Work.CR.Flat.Cauchy.dbar_interior_oneshot` iterated along the chain of polydiscs
interpolating between `ρ'` and `ρo`; the ratios are arbitrary. -/
theorem holderNorm_succ_le_of_dbar {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) {ρ ρ' ρo : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j)
    (hlt : ∀ j, ρ' j < ρo j) (hle : ∀ j, ρo j ≤ ρ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Cn n → ℂ) (f : Fin n → Cn n → ℂ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) → IsClosedForm f →
      (∀ j z, z ∈ polydisc 0 ρo → dbarCoord j u z = f j z) →
      holderNorm (k + 1) α u (polydisc 0 ρ')
        ≤ ENNReal.ofReal C * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
            + holderNorm 0 α u (polydisc 0 ρo)) := by
  classical
  -- The chain of estimates, indexed from the outer polydisc inwards: for every `i ≤ k+1` there
  -- is a constant `D i` with
  -- `‖u‖_{C^{i,α}(polydisc (chainRad (k+2-i)))} ≤ D i · (S + ‖u‖_{C^{0,α}(polydisc ρo)})`.
  have key : ∀ i ≤ k + 1, ∃ D : ℝ, 0 < D ∧ ∀ (u : Cn n → ℂ) (f : Fin n → Cn n → ℂ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) → IsClosedForm f →
      (∀ j z, z ∈ polydisc 0 ρo → dbarCoord j u z = f j z) →
      holderNorm i α u (polydisc 0 (chainRad k ρ' ρo (k + 2 - i)))
        ≤ ENNReal.ofReal D * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
            + holderNorm 0 α u (polydisc 0 ρo)) := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨1, one_pos, ?_⟩
      intro u f hu hf hcl heq
      have h0 : chainRad k ρ' ρo (k + 2 - 0) = ρo := by
        rw [Nat.sub_zero, chainRad_top]
      rw [h0]
      calc holderNorm 0 α u (polydisc 0 ρo)
          = ENNReal.ofReal (1 : ℝ) * (0 + holderNorm 0 α u (polydisc 0 ρo)) := by simp
        _ ≤ ENNReal.ofReal (1 : ℝ)
              * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                  + holderNorm 0 α u (polydisc 0 ρo)) := by
              refine mul_le_mul' le_rfl ?_
              exact add_le_add (zero_le : (0 : ℝ≥0∞) ≤ ∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                le_rfl
    | succ i ih =>
      have hik1 : i + 1 ≤ k + 1 := hi
      obtain ⟨D, hDpos, hD⟩ := ih (by omega)
      -- one step of the interior estimate, from `chainRad (k+2-i)` to `chainRad (k+1-i)`
      have hidx : k + 2 - (i + 1) = k + 1 - i := by omega
      obtain ⟨Ci, hCipos, hCi⟩ :=
        Work.CR.Flat.Cauchy.dbar_interior_oneshot (n := n) hn (c := 0)
          (ρi := chainRad k ρ' ρo (k + 2 - (i + 1))) (ρo := chainRad k ρ' ρo (k + 2 - i))
          (fun j => by
            rw [hidx]
            exact chainRad_lt_of_lt hlt (by omega) j)
          (fun j => chainRad_pos hρ' (fun j => (hlt j).le) (k + 2 - i) j) hα hα1 i
      refine ⟨Ci * (1 + D) + D + 1, by positivity, ?_⟩
      intro u f hu hf hcl heq
      set S : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (polydisc 0 ρ) with hS
      set U : ℝ≥0∞ := holderNorm 0 α u (polydisc 0 ρo) with hU
      have heq' : ∀ j (z : Cn n), z ∈ polydisc 0 (chainRad k ρ' ρo (k + 2 - i)) →
          dbarCoord j u z = f j z := by
        intro j z hz
        refine heq j z (fun l => ?_)
        have h1 : chainRad k ρ' ρo (k + 2 - i) l ≤ ρo l := by
          have h2 := chainRad_mono (k := k) (ρ' := ρ') (ρo := ρo) hlt
            (show k + 2 - i ≤ k + 2 by omega) l
          rwa [chainRad_top] at h2
        exact lt_of_lt_of_le (hz l) h1
      have hu' : ContDiff ℝ (i + 1) u := hu.of_le (by exact_mod_cast hik1)
      have hf' : ∀ j, ContDiff ℝ (i + 1) (f j) := fun j => (hf j).of_le (by exact_mod_cast hik1)
      have hstep := hCi u f hu' hf' hcl heq'
      have hDapp := hD u f hu hf hcl heq
      have hdata : (∑ j, holderNorm i α (f j) (polydisc 0 (chainRad k ρ' ρo (k + 2 - i))))
          ≤ S := by
        rw [hS]
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (holderNorm_mono_k (by omega : i ≤ k) α (f j) _) ?_
        refine holderNorm_mono_set (isOpen_polydisc 0 ρ)
          (isOpen_polydisc 0 (chainRad k ρ' ρo (k + 2 - i))) (fun z hz l => ?_) k α (f j)
        exact lt_of_lt_of_le (hz l)
          (chainRad_le (fun j => (hlt j).le) hle (show k + 2 - i ≤ k + 2 by omega) l)
      have hspos : S + U = ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
          + holderNorm 0 α u (polydisc 0 ρo)) := by rw [hS, hU]
      calc holderNorm (i + 1) α u (polydisc 0 (chainRad k ρ' ρo (k + 2 - (i + 1))))
          ≤ ENNReal.ofReal Ci
              * ((∑ j, holderNorm i α (f j) (polydisc 0 (chainRad k ρ' ρo (k + 2 - i))))
                  + holderNorm i α u (polydisc 0 (chainRad k ρ' ρo (k + 2 - i)))) := hstep
        _ ≤ ENNReal.ofReal Ci * (S + ENNReal.ofReal D * (S + U)) := by
              refine mul_le_mul' le_rfl (add_le_add hdata ?_)
              simpa only [hS, hU] using hDapp
        _ ≤ ENNReal.ofReal (Ci * (1 + D) + D + 1) * (S + U) := by
              have h1 : S + ENNReal.ofReal D * (S + U) ≤ ENNReal.ofReal (1 + D) * (S + U) := by
                have h2 : S ≤ S + U := le_add_right le_rfl
                calc S + ENNReal.ofReal D * (S + U)
                    ≤ (S + U) + ENNReal.ofReal D * (S + U) := add_le_add h2 le_rfl
                  _ = (1 + ENNReal.ofReal D) * (S + U) := by rw [add_mul, one_mul]
                  _ = ENNReal.ofReal (1 + D) * (S + U) := by
                        rw [ENNReal.ofReal_add (by norm_num) hDpos.le, ENNReal.ofReal_one]
              calc ENNReal.ofReal Ci * (S + ENNReal.ofReal D * (S + U))
                  ≤ ENNReal.ofReal Ci * (ENNReal.ofReal (1 + D) * (S + U)) :=
                    mul_le_mul' le_rfl h1
                _ = (ENNReal.ofReal Ci * ENNReal.ofReal (1 + D)) * (S + U) := by rw [mul_assoc]
                _ = ENNReal.ofReal (Ci * (1 + D)) * (S + U) := by
                      rw [ENNReal.ofReal_mul hCipos.le]
                _ ≤ ENNReal.ofReal (Ci * (1 + D) + D + 1) * (S + U) := by
                      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
                      linarith [hDpos]
        _ = ENNReal.ofReal (Ci * (1 + D) + D + 1)
              * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ)) + holderNorm 0 α u (polydisc 0 ρo)) := by
              rw [hspos]
  obtain ⟨C, hCpos, hC⟩ := key (k + 1) le_rfl
  refine ⟨C, hCpos, ?_⟩
  intro u f hu hf hcl heq
  have hfinal := hC u f hu hf hcl heq
  rw [show k + 2 - (k + 1) = 1 by omega] at hfinal
  exact le_trans
    (holderNorm_mono_set (isOpen_polydisc 0 (chainRad k ρ' ρo 1)) (isOpen_polydisc 0 ρ')
      (fun z hz l => by
        have h1 : chainRad k ρ' ρo 0 l ≤ chainRad k ρ' ρo 1 l := chainRad_mono hlt (by omega) l
        rw [chainRad_zero] at h1
        exact lt_of_lt_of_le (by simpa using hz l) h1)
      (k + 1) α u)
    hfinal

/-! ## Assembly: from the core to the target -/

/-- The intermediate multi-radius halfway between `ρ'` and `ρ`. -/
noncomputable def midRad {n : ℕ} (ρ ρ' : Fin n → ℝ) : Fin n → ℝ := fun j => (ρ j + ρ' j) / 2

lemma midRad_apply {n : ℕ} (ρ ρ' : Fin n → ℝ) (j : Fin n) :
    midRad ρ ρ' j = (ρ j + ρ' j) / 2 := rfl

lemma midRad_gt {n : ℕ} {ρ ρ' : Fin n → ℝ} (hlt : ∀ j, ρ' j < ρ j) :
    ∀ j, ρ' j < midRad ρ ρ' j := by
  intro j
  simp only [midRad]
  linarith [hlt j]

lemma midRad_lt {n : ℕ} {ρ ρ' : Fin n → ℝ} (hlt : ∀ j, ρ' j < ρ j) :
    ∀ j, midRad ρ ρ' j < ρ j := by
  intro j
  simp only [midRad]
  linarith [hlt j]

lemma midRad_pos {n : ℕ} {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) :
    ∀ j, 0 < midRad ρ ρ' j := by
  intro j
  simp only [midRad]
  linarith [hρ j, hρ' j]

/-- **Assembly.**  The analytic core at an intermediate polydisc `midRad ρ ρ'` (the statement of
`Work.NN.Core.dbar_solver_open_ratio`, whose proof is the hard analytic input) implies the target
statement: the equation on `polydisc 0 ρ'`, the `C^{k+1,α}` estimates with the data measured on
`polydisc 0 ρ`, and smoothness of the solution for data smooth on `polydisc 0 ρ`.

The higher-order estimates are obtained from the core's single `C^{1,α}`-level estimate by the
interior Schauder iterate `holderNorm_succ_le_of_dbar`. -/
theorem open_poincare_one_of_core {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j)
    (core : ∃ (T : (Fin n → Cn n → ℂ) →ₗ[ℝ] (Cn n → ℂ)) (C : ℝ),
      0 < C ∧
      (∀ f, (∀ j, ContDiff ℝ 1 (f j)) → IsClosedForm f →
        ∀ j (z : Cn n), z ∈ polydisc 0 (midRad ρ ρ') → dbarCoord j (T f) z = f j z) ∧
      (∀ f, (∀ j, ContDiff ℝ 1 (f j)) → IsClosedForm f →
        holderNorm 1 α (T f) (polydisc 0 (midRad ρ ρ'))
          ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)) ∧
      (∀ (k : ℕ) (f : Fin n → Cn n → ℂ), (∀ j, ContDiff ℝ (k + 1) (f j)) → IsClosedForm f →
        ContDiff ℝ (k + 1) (T f)) ∧
      (∀ f, (∀ j, ContDiffOn ℝ ∞ (f j) (polydisc 0 ρ)) → IsClosedForm f →
        ContDiffOn ℝ ∞ (T f) (polydisc 0 (midRad ρ ρ')))) :
    ∃ (T1 : (Fin n → Cn n → ℂ) →ₗ[ℝ] (Cn n → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ f, (∀ j, ContDiff ℝ 1 (f j)) → IsClosedForm f → ∀ j (z : Cn n),
        z ∈ polydisc 0 ρ' → dbarCoord j (T1 f) z = f j z) ∧
      (∀ (k : ℕ) (f : Fin n → Cn n → ℂ), (∀ j, ContDiff ℝ (k + 1) (f j)) →
        IsClosedForm f →
        holderNorm (k + 1) α (T1 f) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)) ∧
      (∀ (f : Fin n → Cn n → ℂ), (∀ j, ContDiffOn ℝ ∞ (f j) (polydisc 0 ρ)) →
        IsClosedForm f →
        ContDiffOn ℝ ∞ (T1 f) (polydisc 0 ρ')) := by
  classical
  obtain ⟨T, C0, hC0pos, heqC, hestC, hsmC, hsmInf⟩ := core
  have hmidlt : ∀ j, ρ' j < midRad ρ ρ' j := midRad_gt hlt
  have hmidle : ∀ j, midRad ρ ρ' j ≤ ρ j := fun j => (midRad_lt hlt j).le
  choose Cf hCfpos hCfest using fun k =>
    holderNorm_succ_le_of_dbar (n := n) hn hα hα1 k hρ hρ' hmidlt hmidle
  refine ⟨T, fun k => Cf k * (1 + C0) + 1, ?_, ?_, ?_, ?_⟩
  · intro k
    have h1 := hCfpos k
    have h2 := hC0pos
    have h3 : (0 : ℝ) < 1 + C0 := by linarith
    nlinarith [mul_pos h1 h3]
  · -- the equation, transported from `midRad` down to `ρ'`
    intro f hf hcl j z hz
    exact heqC f hf hcl j z (fun l => lt_of_lt_of_le (hz l) (hmidlt l).le)
  · -- the estimates
    intro k f hf hcl
    have hf1 : ∀ j, ContDiff ℝ 1 (f j) := fun j =>
      (hf j).of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
    have hsm : ContDiff ℝ (k + 1) (T f) := hsmC k f hf hcl
    have heq : ∀ j (z : Cn n), z ∈ polydisc 0 (midRad ρ ρ') →
        dbarCoord j (T f) z = f j z := heqC f hf1 hcl
    have hclimb := hCfest k (T f) f hsm hf hcl heq
    have hC0b : holderNorm 0 α (T f) (polydisc 0 (midRad ρ ρ'))
        ≤ ENNReal.ofReal C0 * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) :=
      le_trans (holderNorm_mono_k (Nat.zero_le 1) α (T f) _) (hestC f hf1 hcl)
    have hS0 : (∑ j, holderNorm 0 α (f j) (polydisc 0 ρ))
        ≤ ∑ j, holderNorm k α (f j) (polydisc 0 ρ) :=
      Finset.sum_le_sum fun j _ => holderNorm_mono_k (Nat.zero_le k) α (f j) _
    calc holderNorm (k + 1) α (T f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (Cf k)
            * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                + holderNorm 0 α (T f) (polydisc 0 (midRad ρ ρ'))) := hclimb
      _ ≤ ENNReal.ofReal (Cf k)
            * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                + ENNReal.ofReal C0 * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)) :=
            mul_le_mul' le_rfl (add_le_add le_rfl hC0b)
      _ ≤ ENNReal.ofReal (Cf k)
            * ((∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                + ENNReal.ofReal C0 * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)) :=
            mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl hS0))
      _ = ENNReal.ofReal (Cf k * (1 + C0)) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
            have h1 : (∑ j, holderNorm k α (f j) (polydisc 0 ρ))
                + ENNReal.ofReal C0 * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)
                = (1 + ENNReal.ofReal C0) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
              rw [add_mul, one_mul]
            have h2 : ENNReal.ofReal (Cf k) * (1 + ENNReal.ofReal C0)
                = ENNReal.ofReal (Cf k * (1 + C0)) := by
              rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (hC0pos).le,
                ← ENNReal.ofReal_mul (hCfpos k).le]
            rw [h1, ← mul_assoc, h2]
      _ ≤ ENNReal.ofReal (Cf k * (1 + C0) + 1) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            linarith [hCfpos k, hC0pos]
  · -- smoothness
    intro f hf hcl
    exact (hsmInf f hf hcl).mono (polydisc_mono (fun j => (hmidlt j).le))

theorem open_poincare_one {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T1 : (Fin n → Cn n → ℂ) →ₗ[ℝ] (Cn n → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ f, (∀ j, ContDiff ℝ 1 (f j)) → IsClosedForm f → ∀ j (z : Cn n),
        z ∈ polydisc 0 ρ' → dbarCoord j (T1 f) z = f j z) ∧
      (∀ (k : ℕ) (f : Fin n → Cn n → ℂ), (∀ j, ContDiff ℝ (k + 1) (f j)) →
        IsClosedForm f →
        holderNorm (k + 1) α (T1 f) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)) ∧
      (∀ (f : Fin n → Cn n → ℂ), (∀ j, ContDiffOn ℝ ∞ (f j) (polydisc 0 ρ)) →
        IsClosedForm f →
        ContDiffOn ℝ ∞ (T1 f) (polydisc 0 ρ')) :=
  open_poincare_one_of_core hn hα hα1 hρ hρ' hlt
    (Work.NN.Core.dbar_solver_open_ratio hn hα hα1 hρ (midRad_pos hρ hρ') (midRad_lt hlt))

end Work.NN.Core
