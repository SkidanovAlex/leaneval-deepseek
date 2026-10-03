import Mathlib
import Submission.Work.KMTAreas.A7.lacDilTriVarDefs
import Submission.Work.Analysis.Hilbert.lattice_walk_var_lp
import Submission.Port.Aesm

/-
# The `ℓ^p` bound for the reversed-chain variation of the shifted lattice averages

`Work.KMTAreas.A7.latVarSupR r L τ h` is the supremum, over all strictly increasing chains
`u : ℕ → ℕ` and all lengths `J`, of the `ℓ^r`-chain sums of the *reversed* dyadic lattice
conditional expectations `k ↦ latticeExpR (L - k) τ h` (reversed, because those σ-algebras shrink
with `k`, so the reversed family is a genuine conditional-expectation martingale).

The already proved martingale Lépingle inequality `Work.Analysis.Hilbert.latticeWalk_var_le`
bounds the `ℒ^p` norm of exactly the same chain sums, read as an `ℝ`-valued supremum.  The only
gap between the two formulations is bookkeeping: an `ℝ≥0∞`-valued supremum of `ofReal`s versus the
real-valued supremum (`iSup_ofReal_le_ofReal_iSup`), and the identification of `‖w‖ₑ` for the two
codomains.  For the `ℝ≥0∞`-supremum of `ofReal`s to be comparable with the `ofReal` of the real
supremum one needs the chain sums to be *bounded above* at a fixed point `x`; this is
`exists_bound_latChainSum` below and uses that at the fixed point `x` only the finitely many values
`latticeExpR k τ h x`, `k ≤ L`, can occur (the chain `j ↦ L - u j` is weakly decreasing and
`≤ L`).
-/

namespace Work.KMTAreas.A7

open MeasureTheory Finset Filter
open scoped ENNReal BigOperators

noncomputable section

/-- The `s`-chain sum of the shifted dyadic lattice expectations along a (weakly increasing) scale
chain `u`, truncated at the dyadic horizon `L`.  This is the real-valued integrand whose
`ℝ≥0∞`-supremum is `latVarSupR`. -/
def latChainSum (s : ℝ) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ) (u : ℕ → ℕ) (J : ℕ) (x : ℤ) : ℝ :=
  (∑ j ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
        - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s) ^ (1 / s)

lemma latChainSum_nonneg (s : ℝ) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ) (u : ℕ → ℕ) (J : ℕ) (x : ℤ) :
    0 ≤ latChainSum s L τ h u J x := by
  rw [latChainSum]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) s) (1 / s)

/-- Telescoping of the successive differences of a real sequence. -/
lemma sum_range_sub_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Uniform bound for the chain sums at a fixed point.**

At a fixed point `x` the reversed lattice indices `j ↦ L - u j` stay in `{0, …, L}` and are weakly
decreasing; hence every term of the chain sum vanishes unless the index *strictly* decreases, and
the sum of the decreases telescopes to at most `L`.  With `M = ∑_{k ≤ L} |latticeExpR k τ h x|`
this gives the bound `(L · (2M)^s)^{1/s}`. -/
lemma exists_bound_latChainSum (s : ℝ) (hs : 0 < s) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ) (x : ℤ) :
    ∃ B : ℝ, ∀ (u : ℕ → ℕ), (∀ j, u j ≤ u (j + 1)) → ∀ J : ℕ, latChainSum s L τ h u J x ≤ B := by
  set M : ℝ := ∑ k ∈ Finset.range (L + 1), |Work.Analysis.Hilbert.latticeExpR k τ h x| with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hE : ∀ k, k ≤ L → |Work.Analysis.Hilbert.latticeExpR k τ h x| ≤ M := by
    intro k hk
    rw [hM]
    exact Finset.single_le_sum (f := fun i => |Work.Analysis.Hilbert.latticeExpR i τ h x|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  refine ⟨((L : ℝ) * (2 * M) ^ s) ^ (1 / s), fun u hu J => ?_⟩
  have h2M0 : 0 ≤ (2 * M) ^ s := Real.rpow_nonneg (by linarith) s
  have hterm : ∀ j ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
          - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s
        ≤ (((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ)) * (2 * M) ^ s := by
    intro j _
    have hb_le : L - u (j + 1) ≤ L - u j := Nat.sub_le_sub_left (hu j) L
    have ha : |Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ≤ M :=
      hE _ (Nat.sub_le L _)
    have hb : |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x| ≤ M :=
      hE _ (Nat.sub_le L _)
    have h2 : |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
        - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ≤ 2 * M := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;>
        linarith [ha, hb, le_abs_self (Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x),
          le_abs_self (Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x),
          neg_abs_le (Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x),
          neg_abs_le (Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x)]
    have h3 : |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
        - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s ≤ (2 * M) ^ s :=
      Real.rpow_le_rpow (abs_nonneg _) h2 hs.le
    have hcast : ((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ)
        = ((L - u j - (L - u (j + 1)) : ℕ) : ℝ) := (Nat.cast_sub hb_le).symm
    rcases Nat.eq_zero_or_pos (L - u j - (L - u (j + 1))) with h0 | hpos
    · have hEq : L - u (j + 1) = L - u j := by omega
      have hzero : |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
          - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s = 0 := by
        rw [hEq, sub_self, abs_zero, Real.zero_rpow (ne_of_gt hs)]
      have hright : (((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ)) * (2 * M) ^ s = 0 := by
        rw [hcast, h0, Nat.cast_zero, zero_mul]
      exact le_of_eq (by rw [hzero, hright])
    · have h4 : (1 : ℝ) ≤ ((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ) := by
        rw [hcast]
        have h5 : ((1 : ℕ) : ℝ) ≤ ((L - u j - (L - u (j + 1)) : ℕ) : ℝ) :=
          Nat.cast_le.mpr (show (1 : ℕ) ≤ L - u j - (L - u (j + 1)) from hpos)
        simpa using h5
      calc |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
            - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s
          ≤ (2 * M) ^ s := h3
        _ = 1 * (2 * M) ^ s := (one_mul _).symm
        _ ≤ (((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ)) * (2 * M) ^ s :=
            mul_le_mul_of_nonneg_right h4 h2M0
  have htel : (∑ j ∈ Finset.range J,
      (((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ))) ≤ ((L : ℕ) : ℝ) := by
    rw [sum_range_sub_real]
    have h0 : (((L - u 0 : ℕ) : ℝ)) ≤ ((L : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.sub_le L (u 0))
    have hJ : (0 : ℝ) ≤ ((L - u J : ℕ) : ℝ) := by positivity
    linarith
  have hsum : (∑ j ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
        - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s)
      ≤ ((L : ℕ) : ℝ) * (2 * M) ^ s := by
    calc (∑ j ∈ Finset.range J,
          |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
            - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s)
        ≤ ∑ j ∈ Finset.range J,
            (((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ)) * (2 * M) ^ s :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range J,
            (((L - u j : ℕ) : ℝ) - ((L - u (j + 1) : ℕ) : ℝ))) * (2 * M) ^ s := by
          rw [Finset.sum_mul]
      _ ≤ ((L : ℕ) : ℝ) * (2 * M) ^ s := mul_le_mul_of_nonneg_right htel h2M0
  calc latChainSum s L τ h u J x
      = (∑ j ∈ Finset.range J,
          |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
            - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ s) ^ (1 / s) := rfl
    _ ≤ (((L : ℕ) : ℝ) * (2 * M) ^ s) ^ (1 / s) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) s)
          hsum (div_pos one_pos hs).le

/-- `latVarSupR` is the `ℝ≥0∞`-supremum of the `ofReal`s of the chain sums `latChainSum`. -/
lemma latVarSupR_eq_iSup_latChainSum (r : NNReal) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ) (x : ℤ) :
    latVarSupR r L τ h x = ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      ENNReal.ofReal (latChainSum (r : ℝ) L τ h u.1 J x) := rfl

theorem eLpNorm_latVarSupR_le (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℤ → ℝ),
      MeasureTheory.MemLp h (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) →
      MeasureTheory.Integrable h (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) →
      ∀ (L : ℕ) (τ : ℤ),
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.latVarSupR r L τ h) (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨C, hCpos, hwalk⟩ :=
    Work.Analysis.Hilbert.latticeWalk_var_le (p := p) (r := (r : ℝ)) hp (by exact_mod_cast hr)
  refine ⟨C, hCpos, fun h hmem hint L τ => ?_⟩
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have h2 : (0 : NNReal) < r := lt_trans (by norm_num) hr
    exact_mod_cast h2
  have hpt : ∀ x : ℤ, latVarSupR r L τ h x
      ≤ ENNReal.ofReal (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
          latChainSum (r : ℝ) L τ h u.1 J x) := by
    intro x
    obtain ⟨B, hB⟩ := exists_bound_latChainSum (r : ℝ) hr0 L τ h x
    have hb_inner : ∀ u : {u : ℕ → ℕ // StrictMono u},
        BddAbove (Set.range (fun J : ℕ => latChainSum (r : ℝ) L τ h u.1 J x)) :=
      fun u => ⟨B, fun y hy => by
        obtain ⟨J, rfl⟩ := hy
        exact hB u.1 (fun j => u.2.monotone (Nat.le_succ j)) J⟩
    have hb_outer : BddAbove (Set.range (fun u : {u : ℕ → ℕ // StrictMono u} =>
        ⨆ (J : ℕ), latChainSum (r : ℝ) L τ h u.1 J x)) :=
      ⟨B, fun y hy => by
        obtain ⟨u, rfl⟩ := hy
        exact ciSup_le (fun J => hB u.1 (fun j => u.2.monotone (Nat.le_succ j)) J)⟩
    rw [latVarSupR_eq_iSup_latChainSum]
    refine le_trans (iSup_mono (fun u =>
      Work.Analysis.Hilbert.iSup_ofReal_le_ofReal_iSup
        (fun J : ℕ => latChainSum (r : ℝ) L τ h u.1 J x) (hb_inner u))) ?_
    exact Work.Analysis.Hilbert.iSup_ofReal_le_ofReal_iSup
      (fun u : {u : ℕ → ℕ // StrictMono u} => ⨆ (J : ℕ), latChainSum (r : ℝ) L τ h u.1 J x)
      hb_outer
  have hnn : ∀ x : ℤ, 0 ≤ (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      latChainSum (r : ℝ) L τ h u.1 J x) := fun x =>
    Real.iSup_nonneg fun u => Real.iSup_nonneg fun J =>
      latChainSum_nonneg (r : ℝ) L τ h u.1 J x
  calc MeasureTheory.eLpNorm (latVarSupR r L τ h) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal (⨆ (u : {u : ℕ → ℕ // StrictMono u})
            (J : ℕ), latChainSum (r : ℝ) L τ h u.1 J x))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
          simp only [enorm_eq_self]
          exact hpt x)
    _ = MeasureTheory.eLpNorm (fun x : ℤ => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
            latChainSum (r : ℝ) L τ h u.1 J x)
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
        MeasureTheory.eLpNorm_ofReal _ (Eventually.of_forall hnn)
    _ ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := hwalk L τ h hint hmem

end

end Work.KMTAreas.A7
