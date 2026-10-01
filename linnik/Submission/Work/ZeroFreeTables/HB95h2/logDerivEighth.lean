/-
# `HB95h2/logDerivEighth` — HB Lemma 3.1 at `φ = 1/4` (the `1/8` constant)

The statement is the analytic input of the `k = 1` term of the `P₃` method of
Heath-Brown §8/§9, with the constant `1/8` special to **real** characters
(`χ ^ 2 = 1`): for every `e > 0` there are `L₀` and a window radius `δ ∈ (0,1)`
such that every primitive non-principal real character `χ` of modulus `N` with
`L ≥ L₀` and `log N ≤ L` satisfies

`Work.ZeroFreeTables.LogDerivHyp χ δ L (1/8 + e)`.

This is the `HB95h2`-world copy of `Work.ZeroFreeTables.Table4.logDerivHyp_eighth`
(the `P3` world) and of the rect-world duplicates
`Work.ZeroFreeTables.Table4Rect.HB83LogDerivEighth` /
`Work.ZeroFreeTables.lam0w.RectW.LogDerivEighth`; it is proved here on the import
surface of the `HB95h2` engine so that `HB95SigmaEngine` can consume it.

* the analytic engine is `Work.LinnikAreas.l31free.lemma3_1_free_gen_real` — HB
  Lemma 3.1 with a free logarithmic scale `L` and the hypothesis `χ ^ 2 = 1`
  inserted at the two places where the character bound is used;
* the region of `LogDerivHyp` is `1 + 1/(L log L) ≤ Re s ≤ 1 + log L / L`,
  `|Im s| ≤ L`, which sits inside the engine's `|Im s| ≤ 10 L` because
  `0 ≤ log N ≤ L`;
* the `hbound` slot of the engine at `φ = 1/4` is filled by `hbound_quarter_real`
  below — HB Lemma 2.5 for real characters, deduced from the cube-free-moduli
  Burgess character-sum bound (HB Lemma 2.1) and the `φ = 1/4` partial-summation
  chain `LFunction_bound_quarter_of_bounded_order`.

The cube-free input is obtained from the Heath-Brown `2r`-th moment bounds for
cube-free moduli (`Work.LinnikAreas.moment_cubefree_all_r`) fed into the Burgess
core argument (`Work.LinnikAreas.charSum_of_moment_all_k`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.LinnikAreas.charSum_of_moment_all_k
import Submission.Work.LinnikAreas.moment_cubefree_all_r
import Submission.Work.NumberTheory.DirichletCharacter.quarterBurgess

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 1000000

namespace Work.ZeroFreeTables.HB95h2

/-- A non-principal character of modulus `N` forces `3 ≤ N` (for `N ≤ 2` the unit
group is trivial, hence every character is principal). -/
private lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  obtain ⟨a, hne⟩ := hχne
  have hs : Subsingleton (ZMod N)ˣ := by interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

/-- **HB Lemma 2.1, cube-free case, every `k ≥ 2`.**  A single constant works
uniformly over all cube-free moduli and all primitive non-principal characters: the
`2r`-th moment bounds of Heath-Brown for cube-free moduli
(`moment_cubefree_all_r`) fed into the Burgess core argument
(`charSum_of_moment_all_k`). -/
private theorem cubefree_charSum (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) :=
  Work.LinnikAreas.charSum_of_moment_all_k
    (fun r hr ε' hε' => Work.LinnikAreas.moment_cubefree_all_r r hr ε' hε') hε k hk

/-- **HB Lemma 2.5 with `φ = 1/4`, for real characters.**  From the cube-free
Burgess character-sum input and the `φ = 1/4` partial-summation chain of HB §2 for
characters of bounded order one gets, for every non-principal real character `χ` of
modulus `N`,

`‖L(σ + it, χ)‖ ≤ Cb (1+|t|) N^{(1/4)(1-σ)(1+1/k)+ε'}`.

This is the `hbound` slot of HB Lemma 3.1 at `φ = 1/4`. -/
private theorem hbound_quarter_real (k : ℕ) (hk : 3 ≤ k) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
          σ ≤ 1 + Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Cb * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by
  obtain ⟨CB, hCB, hB0⟩ := cubefree_charSum (ε' / 4) (by positivity) k (by omega)
  have hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε' / 4)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    intro u _ ψ hp hψ hcf N H hN hH hHu
    exact hB0 hcf ψ hp hψ hN hH hHu
  obtain ⟨C, hC, hbound⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_bound_quarter_of_bounded_order
      hε' k hk 2 (by norm_num) hCB hB
  refine ⟨C, hC, ?_⟩
  intro N _inst χ hχ hsq σ t hσlo hσhi
  -- `χ ^ 2 = 1` (with `χ ≠ 1`) gives `orderOf χ = 2 ≤ M = 2`
  have hord : orderOf χ ≤ 2 := by
    have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    exact Nat.le_of_dvd (by norm_num) hdvd
  exact hbound χ hχ hord σ t hσlo hσhi

/-- **HB Lemma 3.1 at `φ = 1/4`** (constant `c = 1/8 + e`), in the `LogDerivHyp`
form: for a primitive real character and large scale `L ≥ log N`,

`-Re (L'/L)(s) + Σ_{near} Re(1/(s-ρ)) ≤ (1/8 + e)·L`. -/
theorem logDerivEighth {e : ℝ} (he : 0 < e) :
    ∃ L₀ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hsq : χ ^ 2 = 1) {L : ℝ},
      L₀ ≤ L → Real.log (N : ℝ) ≤ L →
        Work.ZeroFreeTables.LogDerivHyp χ δ L (1 / 8 + e) := by
  -- HB Lemma 3.1 at `φ = 1/4` with `hbound` = HB Lemma 2.5 for real characters
  have hbound : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
          σ ≤ 1 + Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Cb * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => hbound_quarter_real k hk hε'
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := (1 : ℝ) / 4) (by norm_num)
      (ε := e) he hbound
  refine ⟨L₀, δ, hδ0, hδ1, ?_⟩
  intro N _inst χ hχ hprim hsq L hL hlogN
  have hN3 : 3 ≤ N := three_le_of_char_ne_one χ hχ
  have hlogNnn : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLnn : 0 ≤ L := le_trans hlogNnn hlogN
  intro s hs1 hs2 hs3
  -- the engine is stated for `|Im s| ≤ 10 L`, which contains `|Im s| ≤ L`
  have key := hmain hN3 χ hχ hprim hsq hL hlogN s hs1 hs2 (le_trans hs3 (by linarith))
  have hc : (1 : ℝ) / 4 / 2 + e = 1 / 8 + e := by norm_num
  rw [hc] at key
  simpa only [LogDerivHyp, InvNearSum, pdiv] using key

end Work.ZeroFreeTables.HB95h2
