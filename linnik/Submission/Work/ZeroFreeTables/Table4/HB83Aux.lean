/-
# ZeroFreeTables/Table4/HB83Aux — the analytic inputs of HB Lemma 8.3, cycle-free copy

This is a *copy* of the content of `Table4/HB83_base.lean` in the sub-namespace
`Work.ZeroFreeTables.Table4.HB83aux`, with the import of `Table4.HB83` removed: it provides

* `HB83aux.hb85` — the pointwise inequality HB (8.5) at `σ, σ+iγ⁰, σ+2iγ⁰`;
* `HB83aux.logDerivHyp_eighth` — HB Lemma 3.1 at `φ = 1/4` (i.e. `c = 1/8 + e`) for a
  primitive real character;

to `Table4/HB83.lean` itself, which needs them in the proof of `HB83` but cannot import
`HB83_base` (that file imports `Table4.HB83`).
-/
/-
# ZeroFreeTables/Table4/HB83_base — analytic inputs of HB Lemma 8.3

`Work.ZeroFreeTables.HBLemma8_3`: for a **real** character `χ₁` (`χ₁² = 1`, `χ₁ ≠ 1`)
with a real minimal zero `ρ₁` and a further, **non-real** zero `ρ₀` of the working
region, if the side condition (8.6) `(a+λ₀)⁻³ + (a+λ₁)⁻³ ≥ a⁻³` holds then, for
`q ≥ q(a,K,ε)`,

`(K² + 1/2)(P₃((a+λ₁)/a) − P₃(1)) − 2K P₃((a+λ₁)/(a+λ₀)) + (K+1)²(a+λ₁)(1/8 + ε) ≥ 0`.

Route (verbatim HB §8.2, with the constant `1/8 = φ(χ₁)/2`, `φ = 1/4`, from HB Lemma 2.5):
the pointwise inequality (8.5) is the `γ₀ = 0` shadow of HB (9.1)
(`P9.HbCombinationL_nonneg`); the near/far split of the `P₃`-weighted explicit formula
(`P9.pointEngine_prim`) bounds each of the six `Σ(s,χ)` values; the principal-character
terms give `p(α/((s−1)L))`; and the comparison identities `A83_nonneg`, `B83_nonneg` of
`Table4.HB83` dispose of the `A`/`B` bracket.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.CompletedDerivPF
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.pointEngine_prim
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.NumberTheory.DirichletCharacter.quarterBurgess
import Submission.Work.LinnikAreas.charSum_of_moment_all_k
import Submission.Work.LinnikAreas.moment_cubefree_all_r

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Table4.HB83aux

open Work.ZeroFreeTables

/-! ## Small facts about characters -/

lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
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

/-- A real character has order dividing `2`. -/
lemma orderOf_le_two_of_sq_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hsq : χ ^ 2 = 1) : orderOf χ ≤ 2 :=
  Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hsq)

/-! ## The cube-free Burgess character-sum bound -/

/-- **HB Lemma 2.1, cube-free case, every `k`.**  A single constant works uniformly over all
cube-free moduli and all primitive non-principal characters: the `2r`-th moment bounds of
Heath-Brown for cube-free moduli (`moment_cubefree_all_r`) fed into the Burgess core argument
(`charSum_of_moment_all_k`). -/
theorem cubefree_charSum (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) :=
  Work.LinnikAreas.charSum_of_moment_all_k
    (fun r hr ε' hε' => Work.LinnikAreas.moment_cubefree_all_r r hr ε' hε') hε k hk

/-! ## HB Lemma 2.5 with `φ = 1/4` for real characters -/

/-- **HB Lemma 2.5, small-order case, for real characters.**  From the cube-free Burgess
character-sum input (`burgess_charSum_cubefree`) and the `φ = 1/4` partial-summation chain
of HB §2 (`LFunction_bound_quarter_of_bounded_order`) one gets, for every real
non-principal character of modulus `N`,

`‖L(σ + it, χ)‖ ≤ Cb (1+|t|) N^{(1/4)(1-σ)(1+1/k)+ε'}`.

This is the `hbound` slot of HB Lemma 3.1 at `φ = 1/4`. -/
theorem hbound_quarter_real (k : ℕ) (hk : 3 ≤ k) {ε' : ℝ} (hε' : 0 < ε') :
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
    have h := hB0 hcf ψ hp hψ hN hH hHu
    convert h using 2 <;> push_cast <;> ring
  obtain ⟨C, hC, hbound⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_bound_quarter_of_bounded_order
      hε' k hk 2 (by norm_num) hCB hB
  refine ⟨C, hC, ?_⟩
  intro N _ χ hχ hsq σ t h1 h2
  exact hbound χ hχ (orderOf_le_two_of_sq_one χ hsq) σ t h1 h2

/-! ## HB Lemma 3.1 with `φ = 1/4` (constant `c = 1/8 + e`) -/

/-- **HB Lemma 3.1 at `φ = 1/4`**, in the `LogDerivHyp` form: for a primitive real
character and large scale `L ≥ log N`,

`-Re (L'/L)(s) + Σ_{near} Re(1/(s-ρ)) ≤ (1/8 + e)·L`.

This is the only analytic input of the `k = 1` term of the `P₃` method with the constant
`1/8` specific to real characters (`orderOf χ = 2 ≤ L`). -/
theorem logDerivHyp_eighth {e : ℝ} (he : 0 < e) :
    ∃ L₀ : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
        (hprim : χ.IsPrimitive) (hsq : χ ^ 2 = 1) {L : ℝ},
        L₀ ≤ L → Real.log (N : ℝ) ≤ L → LogDerivHyp χ δ L (1 / 8 + e) := by
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
  intro N _ χ hχ hprim hsq L hL hlogN
  have hN3 : 3 ≤ N := three_le_of_char_ne_one χ hχ
  have hlogNnn : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLnn : 0 ≤ L := le_trans hlogNnn hlogN
  intro s hs1 hs2 hs3
  have key := hmain hN3 χ hχ hprim hsq hL hlogN s hs1 hs2
    (le_trans hs3 (by linarith))
  have hc : (1 : ℝ) / 4 / 2 + e = 1 / 8 + e := by norm_num
  rw [hc] at key
  exact key

/-! ## HB (8.5): the pointwise inequality at `σ`, `σ+iγ⁰`, `σ+2iγ⁰` -/

/-- **HB (8.5)** for a real character.  With `γ₀ = 0`, `γ₁ = γ`, the eight-term combination
`HbCombinationL` collapses (using `χ² = 1`) to the six terms of HB (8.5). -/
theorem hb85 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {K σ γ a lam₁ : ℝ} (hK : 0 ≤ K) (hσ : 1 < σ) (ha : 0 < a) (hlam : 0 ≤ lam₁) :
    0 ≤ (K ^ 2 + 1 / 2) *
          (SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
            + SigmaP3L q (Real.log q) χ (σ : ℂ) a lam₁)
        + 2 * K *
          (SigmaP3L q (Real.log q) 1 ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁
            + SigmaP3L q (Real.log q) χ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁)
        + (1 / 2) *
          (SigmaP3L q (Real.log q) 1 ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) a lam₁
            + SigmaP3L q (Real.log q) χ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) a lam₁) := by
  have h3 : χ ^ 3 = χ := by rw [pow_succ, hsq, one_mul]
  have h := P9.HbCombinationL_nonneg χ K σ 0 γ a lam₁ hK hσ ha hlam
  rw [HbCombinationL, hsq, h3] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_one] at h ⊢
  linarith

end Work.ZeroFreeTables.Table4.HB83aux
