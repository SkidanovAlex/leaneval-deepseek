/-
Copyright: work module for the Elgindi finite-time singularity project.

# The reverse multiplier bound for `HkIntegrand`, uniformly at a fixed `z`

`Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zrev_at_z` is the *reverse* of
`HkIntegrand_zmul_uniform`: for a multiplier `φ` depending only on `z` and **nonzero at a
fixed point `z > 0`**, we can bound the `ℋⁿ`-integrand of `f` by a constant times the
`ℋⁿ`-integrand of `φ · f` — with a constant that depends on `α`, `n`, `φ` and `z`, but is
*uniform in `θ` and in `f`*:

`HkIntegrand α n f z θ ≤ C · HkIntegrand α n (fun z θ => φ z * f z θ) z θ`.

At a fixed `z`, `f ↦ φ z · f` is an invertible *triangular* linear map on the jet of `f` at
`z`: the Leibniz rule for the derivation `D_z = z ∂_z` gives, with `c b = (D_z^b φ)(z)` and
`c 0 = φ z ≠ 0`,

`D_z^i (φ·f)(z,θ) = ∑_{b≤i} binom(i,b) · c b · D_z^{i-b} f(z,θ)`,

and the `b = 0` term is `c 0 · D_z^i f(z,θ)`, so `D_z^i f(z,θ)` can be solved for recursively
in terms of `D_z^k (φ·f)(z,θ)`, `k ≤ i`, with coefficients depending only on `z` and `φ`.
The same triangular system governs `D_z^j D_θ^i f(z,θ)` for each *fixed* angular order `i ≥ 1`
(because `D_θ` commutes with multiplication by a `z`-only factor), so every slot of the
integrand is controlled.  The linear-algebraic content is isolated in the pure-arithmetic
`Work.FTS.CoercivityFix.E2Bound.SlotMul.zrev_seq_bound`; here we only have to instantiate the
two Leibniz identities and add up.

Note that no decay of `φ` at `0` or `∞` and no lower bound on `|φ|` off `z` are used: only
`φ z ≠ 0` at the single point under consideration.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.CoercivityFix.E2Bound.mixed_zmul
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.zrev_seq_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas -/

/-- A function of `z` alone, `C^∞` on `(-1,∞)`, is `SmoothQuad` as a function of `(z,θ)`. -/
private lemma smoothQuad_zonly_slot {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => a z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => a z))
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
  have h : Function.uncurry (fun z _ : ℝ => a z) = fun p : ℝ × ℝ => a p.1 := rfl
  rw [h]
  exact ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- The Leibniz expansion of `D_z^i (φ·f)` for a `z`-only multiplier `φ`, in the shape used
below: `D_z^i (φ f) = ∑_{b ≤ i} binom(i,b) · (Zop^b φ) · D_z^{i-b} f`, where
`Zop = z ∂_z` is the operator acting on functions of `z` alone. -/
private lemma DzIter_zmul_expand (i : ℕ) (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hzI : z ∈ Work.Spaces.Iz)
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)))
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi (-1))) :
    Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ
      = ∑ b ∈ Finset.range (i + 1),
          (i.choose b : ℝ) * (Work.Spaces.Zop^[b] φ z) * (Work.Spaces.DzIter (i - b) f z θ) := by
  have h := Work.FTS.LocData.DzIter_mul_smoothQuad i (fun z' (_ : ℝ) => φ z') f hzI hφ hf
  rw [show (fun z θ => φ z * f z θ) = (fun z θ => (fun z' (_ : ℝ) => φ z') z θ * f z θ)
    from rfl]
  rw [h]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hZ : Work.Spaces.DzIter b (fun z' (_ : ℝ) => φ z') z θ = Work.Spaces.Zop^[b] φ z := by
    simpa using congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z' (_ : ℝ) => φ z') θ) z
  rw [hZ]
  ring

/-- The mixed Leibniz expansion: `D_z^j D_θ^i (φ·f) = ∑_{b ≤ j} binom(j,b) · (Zop^b φ) ·
D_z^{j-b} D_θ^i f` for a `z`-only multiplier `φ`.  This is `mixed_zmul` reshaped. -/
private lemma mixed_zmul_expand (j i : ℕ) (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz1 : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hφquad : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => φ z))
    (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1),
          (j.choose b : ℝ) * (Work.Spaces.Zop^[b] φ z) * (Work.Spaces.mixed (j - b) i f z θ) := by
  have h := Work.FTS.CoercivityFix.E2Bound.mixed_zmul j i φ f hz1 hθ hφquad hf
  rw [h]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-! ## The requested lemma -/

theorem HkIntegrand_zrev_at_z (α : ℝ) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1))) :
    ∀ z ∈ Set.Ioi (0 : ℝ), φ z ≠ 0 → ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad f →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.Spaces.HkIntegrand α n f z θ
            ≤ C * Work.Spaces.HkIntegrand α n (fun z θ => φ z * f z θ) z θ := by
  intro z hz hφz
  have hzpos : (0 : ℝ) < z := hz
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hzpos)
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hφquad : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => φ z) := smoothQuad_zonly_slot hφ
  have hc0 : (fun b : ℕ => Work.Spaces.Zop^[b] φ z) 0 ≠ 0 := by simpa using hφz
  obtain ⟨D, hDpos, hD⟩ :=
    zrev_seq_bound n
      (fun b : ℕ => Work.Spaces.Zop^[b] φ z) hc0
  refine ⟨2 * ((n : ℝ) + 1) ^ 3 * D + 1, ?_, ?_⟩
  · have hq : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 := by positivity
    have h2 : (0 : ℝ) < 2 * ((n : ℝ) + 1) ^ 3 * D := mul_pos (mul_pos (by norm_num) hq) hDpos
    linarith
  · intro f hf θ hθ
    have hfslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' : ℝ => f z' θ)
        (Set.Ioi (-1)) := hf.curry_z hθ
    set ρ : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hρ
    set Wθ : ℝ := Work.Spaces.Wt α z θ with hWθ
    set H : ℝ := Work.Spaces.HkIntegrand α n (fun z θ => φ z * f z θ) z θ with hH
    have hHnn : (0 : ℝ) ≤ H := by
      rw [hH]; exact Work.Spaces.HkIntegrand_nonneg α n (fun z θ => φ z * f z θ) z θ
    have hq1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- the two Leibniz identities, at the level of sequences
    have hzid : ∀ i ≤ n,
        Work.Spaces.DzIter i (fun z θ => φ z * f z θ) z θ
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) * (Work.Spaces.Zop^[b] φ z)
              * (Work.Spaces.DzIter (i - b) f z θ) :=
      fun i _ => DzIter_zmul_expand i φ f z θ hzI hφ hfslice
    have hmixid : ∀ i j, j ≤ n →
        Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (Work.Spaces.Zop^[b] φ z)
              * (Work.Spaces.mixed (j - b) i f z θ) :=
      fun i j _ => mixed_zmul_expand j i φ f z θ hz1 hθ hφquad hf
    -- the two triangular reconstructions
    have hzseq : ∀ j ≤ n, (Work.Spaces.DzIter j f z θ) ^ 2
        ≤ D * ∑ k ∈ Finset.range (j + 1),
            (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ) ^ 2 :=
      fun j hj => hD (fun k => Work.Spaces.DzIter k f z θ)
        (fun k => Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ)
        (fun i hi => hzid i hi) j hj
    have hmixseq : ∀ i, 1 ≤ i → ∀ j ≤ n, (Work.Spaces.mixed j i f z θ) ^ 2
        ≤ D * ∑ k ∈ Finset.range (j + 1),
            (Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ) ^ 2 :=
      fun i _ j hj => hD (fun k => Work.Spaces.mixed k i f z θ)
        (fun k => Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ)
        (fun l hl => hmixid i l hl) j hj
    -- a single term of the pure `D_z` sum
    have hzterm : ∀ k ≤ n,
        (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ * ρ) ^ 2 ≤ H := by
      intro k hk
      rw [hH, hρ]
      exact Work.Spaces.sq_le_HkIntegrand_z α n (fun z θ => φ z * f z θ) z θ k hk
    -- a single term of the mixed sum
    have hmixterm : ∀ i j, 1 ≤ i → i + j ≤ n →
        (Work.Spaces.mixed j i (fun z θ => φ z * f z θ) z θ * Wθ) ^ 2 ≤ H := by
      intro i j hi1 hij
      rw [hH, hWθ]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α n (fun z θ => φ z * f z θ) z θ i j hi1 hij
    -- per-slot bounds, all with the same constant `D * (n+1) * H`
    have hzslot : ∀ i ≤ n, (Work.Spaces.DzIter i f z θ * ρ) ^ 2
        ≤ D * ((n : ℝ) + 1) * H := by
      intro i hi
      have hs := hzseq i hi
      have hstep : (∑ k ∈ Finset.range (i + 1),
            (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ) ^ 2) * ρ ^ 2
          = ∑ k ∈ Finset.range (i + 1),
              (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ * ρ) ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      calc (Work.Spaces.DzIter i f z θ * ρ) ^ 2
          = (Work.Spaces.DzIter i f z θ) ^ 2 * ρ ^ 2 := by ring
        _ ≤ (D * ∑ k ∈ Finset.range (i + 1),
              (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ) ^ 2) * ρ ^ 2 :=
            mul_le_mul_of_nonneg_right hs (sq_nonneg ρ)
        _ = D * ((∑ k ∈ Finset.range (i + 1),
              (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ) ^ 2) * ρ ^ 2) := by ring
        _ = D * ∑ k ∈ Finset.range (i + 1),
              (Work.Spaces.DzIter k (fun z θ => φ z * f z θ) z θ * ρ) ^ 2 := by rw [hstep]
        _ ≤ D * ∑ _k ∈ Finset.range (i + 1), H := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
            exact Finset.sum_le_sum (fun k hk =>
              hzterm k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hi))
        _ = D * ((i : ℝ) + 1) * H := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ D * ((n : ℝ) + 1) * H := by
            apply mul_le_mul_of_nonneg_right _ hHnn
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
            have : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi
            linarith
    have hmixslot : ∀ i ≤ n, ∀ j ≤ n,
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0)
          ≤ D * ((n : ℝ) + 1) * H := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [ite_eq_left hc]
        obtain ⟨hi1, hij⟩ := hc
        have hs := hmixseq i hi1 j hj
        have hstep : (∑ k ∈ Finset.range (j + 1),
              (Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ) ^ 2) * Wθ ^ 2
            = ∑ k ∈ Finset.range (j + 1),
                (Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ * Wθ) ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        calc (Work.Spaces.mixed j i f z θ * Wθ) ^ 2
            = (Work.Spaces.mixed j i f z θ) ^ 2 * Wθ ^ 2 := by ring
          _ ≤ (D * ∑ k ∈ Finset.range (j + 1),
                (Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ) ^ 2) * Wθ ^ 2 :=
              mul_le_mul_of_nonneg_right hs (sq_nonneg Wθ)
          _ = D * ((∑ k ∈ Finset.range (j + 1),
                (Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ) ^ 2) * Wθ ^ 2) := by ring
          _ = D * ∑ k ∈ Finset.range (j + 1),
                (Work.Spaces.mixed k i (fun z θ => φ z * f z θ) z θ * Wθ) ^ 2 := by rw [hstep]
          _ ≤ D * ∑ _k ∈ Finset.range (j + 1), H := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
              exact Finset.sum_le_sum (fun k hk =>
                hmixterm i k hi1 (le_trans (Nat.add_le_add_left
                  (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) i) hij))
          _ = D * ((j : ℝ) + 1) * H := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
          _ ≤ D * ((n : ℝ) + 1) * H := by
              apply mul_le_mul_of_nonneg_right _ hHnn
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hDpos)
              have : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj
              linarith
      · rw [ite_eq_right hc]
        exact mul_nonneg (mul_nonneg (le_of_lt hDpos) (le_of_lt hq1)) hHnn
    -- summing the two halves
    have hzle : (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
        ≤ ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H) := by
      calc (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
          ≤ ∑ _i ∈ Finset.range (n + 1), (D * ((n : ℝ) + 1) * H) :=
            Finset.sum_le_sum (fun i hi =>
              hzslot i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        _ = ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hmle : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0))
        ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H)) := by
      have hinner : ∀ i ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0))
            ≤ ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H) := by
        intro i hi
        calc (∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0))
            ≤ ∑ _j ∈ Finset.range (n + 1), (D * ((n : ℝ) + 1) * H) :=
              Finset.sum_le_sum (fun j hj => hmixslot i
                (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) j
                (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
          _ = ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (n + 1),
              ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H) := Finset.sum_le_sum hinner
        _ = ((n : ℝ) + 1) * (((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    -- arithmetic with the constant
    have hB : (0 : ℝ) ≤ D * ((n : ℝ) + 1) * H :=
      mul_nonneg (mul_nonneg (le_of_lt hDpos) (le_of_lt hq1)) hHnn
    have hmain : (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
        + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0))
        ≤ (2 * ((n : ℝ) + 1) ^ 3 * D + 1) * H := by
      have hstep1 : ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H)
          + ((n : ℝ) + 1) * (((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H))
          = (((n : ℝ) + 1) + ((n : ℝ) + 1) ^ 2) * (D * ((n : ℝ) + 1) * H) := by ring
      have hstep2 : ((n : ℝ) + 1) + ((n : ℝ) + 1) ^ 2 ≤ 2 * ((n : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) + 1), hq1]
      have hstep3 : 2 * ((n : ℝ) + 1) ^ 2 * (D * ((n : ℝ) + 1) * H)
          = 2 * ((n : ℝ) + 1) ^ 3 * D * H := by ring
      calc (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
            + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
                (if 1 ≤ i ∧ i + j ≤ n
                  then (Work.Spaces.mixed j i f z θ * Wθ) ^ 2 else 0))
          ≤ ((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H)
              + ((n : ℝ) + 1) * (((n : ℝ) + 1) * (D * ((n : ℝ) + 1) * H)) :=
            add_le_add hzle hmle
        _ = (((n : ℝ) + 1) + ((n : ℝ) + 1) ^ 2) * (D * ((n : ℝ) + 1) * H) := hstep1
        _ ≤ (2 * ((n : ℝ) + 1) ^ 2) * (D * ((n : ℝ) + 1) * H) :=
            mul_le_mul_of_nonneg_right hstep2 hB
        _ = 2 * ((n : ℝ) + 1) ^ 3 * D * H := hstep3
        _ ≤ (2 * ((n : ℝ) + 1) ^ 3 * D + 1) * H := by
            nlinarith [hHnn]
    conv_lhs => rw [Work.Spaces.HkIntegrand]
    rw [← hρ, ← hWθ]
    exact hmain

end Work.FTS.CoercivityFix.E2Bound.SlotMul
