/-
# FTS/GalBasis — the Galerkin basis of the corrected N6 interface (Elgindi / annals)

This directory (`Submission/Work/FTS/GalBasis/`, namespace `Work.FTS.GalBasis`) is the area
of design §3 of `Submission/Work/FTS/FTS_ELL_GALERKIN.md`: the **existence of a Galerkin
basis**

  `exists_galBasis (hIP : UnifIP IP α₂ cc clo Cup Ccs) :
      ∀ α ∈ Ioc 0 α₂, ∃ φ : ℕ → Fn,
        GalBasis α IP φ ∧ DenseSpan α IP φ ∧ DenseSpanO α IP φ ∧ CcBasis φ`

i.e. a sequence `φ` of test functions which is

* `IP α`-orthonormal (`GalBasis.orth`) with every finite combination in the regular class
  `GalClass α` (`GalBasis.cls`);
* dense in the `ℋ⁴`-norm in the regular class `{f : RegQ α 4, L₁₂ f 0 = 0}`
  (`Work.FTS.Galerkin.DenseSpan`);
* dense in the `ℋ⁴`-norm in the honest open class `{f : HQo α 4, BdryTraces α 4,
  L₁₂ f 0 = 0}` (`DenseSpanO`, the form consumed by Open2/Open3);
* each element `C^∞` with support in a box `[a,b] × [δ, π/2-δ]` (`CcBasis`).

## The shape of the construction (why these definitions)

Write `Fn = ℝ → ℝ → ℝ` for a profile of the self-similar variables (curried `f z θ`), and
recall the weighted `ℋ^k` norm `Spaces.HkNorm α k` (the paper's `ℋ^k`, `dz dθ` — not
`rdrdθ`), the zero-mode functional `Construction.L12`, and the classes `RegQ`, `HQo`,
`GalClass`, `CoerAdm`, `UnifIP`, `GalBasis` of `Vocab.lean`/`VocabO.lean`.

1. **The test functions.** `Ccφ f` (this file): `f` is `C^∞` on all of `ℝ²` (`ContDiff ℝ
   (⊤ : ℕ∞)`, the *honest* `C^∞` order — **not** the analytic order `⊤ : ℕ∞ω`) and is
   supported *strictly inside* a box `[a,b] × [δ, π/2-δ]` with `0 < a < b`, `0 < δ < π/2`.
   Support away from the boundary of the quadrant is what makes every membership in this
   chapter (`HkMem`, `BdryTraces`, `DecayAll`, `SmoothQuad`, …) immediate: both weights
   `w(z) = (1+z)²/z²` and `sin(2θ)^{-γ}` are bounded on a neighbourhood of the support.
   `Coreφ f := Ccφ f ∧ L₁₂ f 0 = 0` is the class the basis elements live in.

2. **The countable family.**  A *single* explicit sequence `famE : ℕ → Fn` is fixed:
   `famE (code7 p q n m₁ m₂ m₃ m₄)` is the monomial `z^p θ^q` times the product of four
   smooth steps — two in `z` (at the rationals `m_i/(n+1)`) and two in `θ` — so it is
   `C^∞` with support in the rational box
   `[m₁/(n+1), m₂/(n+1)] × [m₃/(n+1), m₄/(n+1)]`.
   The steps are built from Mathlib's `Real.smoothTransition`; the key point is that the
   *scale invariant* derivatives `D_z = z∂_z`, `D_θ = sin(2θ)∂_θ` of a step of mesh `h` are
   bounded **uniformly in `h`** — which is what makes cutoffs harmless in the `ℋ⁴`-norm.

3. **The `L₁₂`-adjustment.**  `GalBasis.cls` requires every finite combination `galFun φ c`
   to have `L₁₂(·)(0) = 0`; `L₁₂` being additive, that forces `L₁₂ (φ k) 0 = 0` for each
   basis element.  So the family is adjusted *once and for all*:
   `testFam k := famE k - (L₁₂ (famE k) 0 / c₀) • Gfar`, where `c₀ := L₁₂ Gfar 0 ≠ 0` and
   `Gfar` is one designated family element.  `testFam` is still `C^∞`, still compactly
   supported, and now `L₁₂ (testFam k) 0 = 0`.

4. **Gram–Schmidt.**  See `GramSchmidt.lean`: the orthonormalisation of `testFam` in `IP`
   (positivity from `UnifIP.lo` on `CoerAdm`, every element of the span being a finite
   combination of test functions) preserves the algebraic span, hence the density.

5. **Density.**  Two density statements are proved: the cutoff approximation of an honest
   class element by a `Ccφ` function (`Cutoff.lean`), and the approximation of a `Ccφ`
   function by a combination of the family in the `C^4`-norm (`Approx.lean`, the
   strip-Taylor argument).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.GalerkinFix.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## The test-function class -/

/-- `f` is supported in the box `[a,b] × [δ, π/2-δ]` (it vanishes off the closed box). -/
def SuppIn (f : Fn) (a b δ : ℝ) : Prop :=
  ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0

/-- `f` is supported in the rectangle `[a,b] × [c,d]` (the two-dimensional form, used by the
approximation lemmas, whose boxes need not be symmetric about `θ = π/4`). -/
def SuppBox (f : Fn) (a b c d : ℝ) : Prop :=
  ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → f z θ = 0

theorem suppIn_iff_suppBox (f : Fn) (a b δ : ℝ) :
    SuppIn f a b δ ↔ SuppBox f a b δ (π / 2 - δ) := Iff.rfl

theorem SuppIn.mono {f : Fn} {a b a' b' δ δ' : ℝ} (h : SuppIn f a b δ)
    (ha : a' ≤ a) (hb : b ≤ b') (hδ : δ' ≤ δ) (hδ' : π / 2 - δ ≤ π / 2 - δ') :
    SuppIn f a' b' δ' := by
  intro z θ hz
  refine h z θ ?_
  rcases hz with hz | hz
  · exact Or.inl fun hc => hz ⟨le_trans ha hc.1, le_trans hc.2 hb⟩
  · exact Or.inr fun hc => hz ⟨le_trans hδ hc.1, le_trans hc.2 hδ'⟩

/-- The compactly supported smooth class: `g` is `C^m` on the open box `(a,b) × (δ, π/2-δ)`
and supported in a strictly smaller box.  This is the class produced by the cutoffs of
`Cutoff.lean` and consumed by the approximation lemma of `Approx.lean`. -/
def CcOn (m : ℕ) (g : Fn) : Prop :=
  ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧
    ContDiffOn ℝ m (Function.uncurry g) (Set.Ioo a b ×ˢ Set.Ioo δ (π / 2 - δ)) ∧
    ∃ a' b' δ' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ δ < δ' ∧ δ' < π / 2 - δ' ∧
      SuppIn g a' b' δ'

theorem CcOn.contDiffOn {m : ℕ} {g : Fn} (h : CcOn m g) :
    ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧
      ContDiffOn ℝ m (Function.uncurry g) (Set.Ioo a b ×ˢ Set.Ioo δ (π / 2 - δ)) := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, hd, -⟩ := h
  exact ⟨a, b, δ, ha, hab, hδ, hδ2, hd⟩

theorem CcOn.supp {m : ℕ} {g : Fn} (h : CcOn m g) :
    ∃ a' b' δ' : ℝ, 0 < a' ∧ a' < b' ∧ 0 < δ' ∧ δ' < π / 2 ∧ SuppIn g a' b' δ' := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, -, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h
  exact ⟨a', b', δ', lt_trans ha haa, hab', lt_trans hδ hδδ,
    by linarith [hδ, hδδ, hδδ2], hs⟩

/-- **The test functions of the Galerkin basis**: globally `C^∞` (order `(⊤ : ℕ∞)`, the honest
`C^∞` order, *not* the analytic order `⊤ : ℕ∞ω`) and supported strictly inside a box
`[a,b] × [δ, π/2-δ]` with `0 < a < b`, `0 < δ < π/2`. -/
def Ccφ (f : Fn) : Prop :=
  ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) ∧
    ∃ a' b' δ' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ δ < δ' ∧ δ' < π / 2 - δ' ∧
      SuppIn f a' b' δ'

theorem Ccφ.contDiff {f : Fn} (h : Ccφ f) : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f) := by
  obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := h; exact hd

theorem Ccφ.supp {f : Fn} (h : Ccφ f) :
    ∃ a b δ : ℝ, 0 < a ∧ a < b ∧ 0 < δ ∧ δ < π / 2 ∧ SuppIn f a b δ := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, -, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h
  exact ⟨a', b', δ', lt_trans ha haa, hab', lt_trans hδ hδδ,
    by linarith [hδ, hδδ, hδδ2], hs⟩

/-- Every `Ccφ` function is in the compactly supported smooth class at every order. -/
theorem Ccφ.ccOn {f : Fn} (h : Ccφ f) (m : ℕ) : CcOn m f := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, hd, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h
  exact ⟨a, b, δ, ha, hab, hδ, hδ2,
    (hd.contDiffOn).of_le (WithTop.coe_le_coe.mpr le_top), a', b', δ', haa, hab', hbb, hδδ, hδδ2,
    hs⟩

/-- **The basis condition of the design** (`CcBasis` of `FTS_ELL_GALERKIN_STMTS`): every
element is `C^∞` and is supported in a box `[a,b] × [δ,π/2-δ]`. -/
def CcBasis (φ : ℕ → Fn) : Prop :=
  ∀ k : ℕ, ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ δ : ℝ, 0 < δ ∧
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (φ k)) ∧
    ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → φ k z θ = 0

theorem CcBasis.of_Ccφ {φ : ℕ → Fn} (h : ∀ k, Ccφ (φ k)) : CcBasis φ := by
  intro k
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, hd, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h k
  refine ⟨a', b', lt_trans ha haa, hab', δ', lt_trans hδ hδδ, hd, ?_⟩
  intro z θ hz
  exact hs z θ hz

/-- The test functions with vanishing `L₁₂`-zero-mode: the class in which the basis elements
(and hence all their finite combinations) live. -/
def Coreφ (f : Fn) : Prop := Ccφ f ∧ Work.Construction.L12 f 0 = 0

theorem Coreφ.cc {f : Fn} (h : Coreφ f) : Ccφ f := h.1
theorem Coreφ.l12 {f : Fn} (h : Coreφ f) : Work.Construction.L12 f 0 = 0 := h.2

/-! ## The explicit countable family of test functions

The family is indexed by seven natural numbers, decoded from a single one by `Nat.pair`.
Each element is a monomial `z^p θ^q` times the product of four smooth *steps* — two in `z`
and two in `θ` — of common mesh `1/(n+1)`; the support is the rational box
`[m₁/(n+1), m₂/(n+1)] × [m₃/(n+1), m₄/(n+1)]`. -/

/-- The smooth *step* of mesh `1/(n+1)` starting at `m/(n+1)`: `0` for `t ≤ m/(n+1)`,
`1` for `t ≥ (m+1)/(n+1)`. -/
def stp (n m : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (((n : ℝ) + 1) * t - (m : ℝ))

/-- The reversed smooth *step*: `1` for `t ≤ (m-1)/(n+1)`, `0` for `t ≥ m/(n+1)`. -/
def ustp (n m : ℕ) (t : ℝ) : ℝ := Real.smoothTransition ((m : ℝ) - ((n : ℝ) + 1) * t)

theorem stp_eq_zero {n m : ℕ} {t : ℝ} (h : ((n : ℝ) + 1) * t ≤ (m : ℝ)) : stp n m t = 0 := by
  rw [stp]; exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem stp_eq_one {n m : ℕ} {t : ℝ} (h : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) * t) :
    stp n m t = 1 := by
  rw [stp]; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem ustp_eq_one {n m : ℕ} {t : ℝ} (h : ((n : ℝ) + 1) * t ≤ (m : ℝ) - 1) : ustp n m t = 1 := by
  rw [ustp]; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem ustp_eq_zero {n m : ℕ} {t : ℝ} (h : (m : ℝ) ≤ ((n : ℝ) + 1) * t) : ustp n m t = 0 := by
  rw [ustp]; exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem stp_nonneg (n m : ℕ) (t : ℝ) : 0 ≤ stp n m t := Real.smoothTransition.nonneg _
theorem stp_le_one (n m : ℕ) (t : ℝ) : stp n m t ≤ 1 := Real.smoothTransition.le_one _
theorem ustp_nonneg (n m : ℕ) (t : ℝ) : 0 ≤ ustp n m t := Real.smoothTransition.nonneg _
theorem ustp_le_one (n m : ℕ) (t : ℝ) : ustp n m t ≤ 1 := Real.smoothTransition.le_one _

/-- The `z`-factor of a family element. -/
def famZ (n m₁ m₂ : ℕ) : ℝ → ℝ := fun z => stp n m₁ z * ustp n m₂ z

/-- The `θ`-factor of a family element. -/
def famTh (n m₃ m₄ : ℕ) : ℝ → ℝ := fun θ => stp n m₃ θ * ustp n m₄ θ

/-- The raw family element: a monomial times a product of four steps. -/
def famRaw (p q n m₁ m₂ m₃ m₄ : ℕ) : Fn :=
  fun z θ => z ^ p * θ ^ q * (famZ n m₁ m₂ z * famTh n m₃ m₄ θ)

theorem famRaw_apply (p q n m₁ m₂ m₃ m₄ : ℕ) (z θ : ℝ) :
    famRaw p q n m₁ m₂ m₃ m₄ z θ
      = z ^ p * θ ^ q * (stp n m₁ z * ustp n m₂ z * (stp n m₃ θ * ustp n m₄ θ)) := rfl

theorem famRaw_eq_mul (p q n m₁ m₂ m₃ m₄ : ℕ) (z θ : ℝ) :
    famRaw p q n m₁ m₂ m₃ m₄ z θ = z ^ p * θ ^ q * (famZ n m₁ m₂ z * famTh n m₃ m₄ θ) := rfl

theorem famRaw_nonneg (p q n m₁ m₂ m₃ m₄ : ℕ) {z θ : ℝ} (hz : 0 ≤ z) (hθ : 0 ≤ θ) :
    0 ≤ famRaw p q n m₁ m₂ m₃ m₄ z θ := by
  have h1 : 0 ≤ z ^ p := pow_nonneg hz p
  have h2 : 0 ≤ θ ^ q := pow_nonneg hθ q
  have h3 : 0 ≤ famZ n m₁ m₂ z := mul_nonneg (stp_nonneg _ _ _) (ustp_nonneg _ _ _)
  have h4 : 0 ≤ famTh n m₃ m₄ θ := mul_nonneg (stp_nonneg _ _ _) (ustp_nonneg _ _ _)
  simp only [famRaw, famZ, famTh]
  exact mul_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4)

/-- The support bound for the `z`-factor: it vanishes off `(m₁/(n+1), m₂/(n+1))`. -/
theorem famZ_eq_zero {n m₁ m₂ : ℕ} {z : ℝ}
    (h : ((n : ℝ) + 1) * z ≤ (m₁ : ℝ) ∨ (m₂ : ℝ) ≤ ((n : ℝ) + 1) * z) : famZ n m₁ m₂ z = 0 := by
  rcases h with h | h
  · rw [famZ, stp_eq_zero h, zero_mul]
  · rw [famZ, ustp_eq_zero h, mul_zero]

/-- The plateau of the `z`-factor: it is `1` on `[(m₁+1)/(n+1), (m₂-1)/(n+1)]`. -/
theorem famZ_eq_one {n m₁ m₂ : ℕ} {z : ℝ} (h₁ : ((m₁ : ℝ) + 1) ≤ ((n : ℝ) + 1) * z)
    (h₂ : ((n : ℝ) + 1) * z ≤ (m₂ : ℝ) - 1) : famZ n m₁ m₂ z = 1 := by
  rw [famZ, stp_eq_one h₁, ustp_eq_one h₂, one_mul]

/-- The support bound for the `θ`-factor. -/
theorem famTh_eq_zero {n m₃ m₄ : ℕ} {θ : ℝ}
    (h : ((n : ℝ) + 1) * θ ≤ (m₃ : ℝ) ∨ (m₄ : ℝ) ≤ ((n : ℝ) + 1) * θ) :
    famTh n m₃ m₄ θ = 0 := by
  rcases h with h | h
  · rw [famTh, stp_eq_zero h, zero_mul]
  · rw [famTh, ustp_eq_zero h, mul_zero]

/-- The plateau of the `θ`-factor. -/
theorem famTh_eq_one {n m₃ m₄ : ℕ} {θ : ℝ} (h₁ : ((m₃ : ℝ) + 1) ≤ ((n : ℝ) + 1) * θ)
    (h₂ : ((n : ℝ) + 1) * θ ≤ (m₄ : ℝ) - 1) : famTh n m₃ m₄ θ = 1 := by
  rw [famTh, stp_eq_one h₁, ustp_eq_one h₂, one_mul]

theorem famRaw_eq_zero {p q n m₁ m₂ m₃ m₄ : ℕ} {z θ : ℝ}
    (h : ((n : ℝ) + 1) * z ≤ (m₁ : ℝ) ∨ (m₂ : ℝ) ≤ ((n : ℝ) + 1) * z
      ∨ ((n : ℝ) + 1) * θ ≤ (m₃ : ℝ) ∨ (m₄ : ℝ) ≤ ((n : ℝ) + 1) * θ) :
    famRaw p q n m₁ m₂ m₃ m₄ z θ = 0 := by
  rw [famRaw_eq_mul]
  rcases h with h | h | h | h
  · rw [famZ_eq_zero (n := n) (Or.inl h), zero_mul, mul_zero]
  · rw [famZ_eq_zero (n := n) (Or.inr h), zero_mul, mul_zero]
  · rw [famTh_eq_zero (n := n) (Or.inl h), mul_zero, mul_zero]
  · rw [famTh_eq_zero (n := n) (Or.inr h), mul_zero, mul_zero]

/-- The `C^∞`-ness of a family element. -/
theorem contDiff_famRaw (p q n m₁ m₂ m₃ m₄ : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (famRaw p q n m₁ m₂ m₃ m₄)) := by
  unfold famRaw famZ famTh stp ustp Function.uncurry
  fun_prop

/-- The decoding of the index of a family element. -/
def un7 (k : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let t₁ := Nat.unpair k
  let t₂ := Nat.unpair t₁.2
  let t₃ := Nat.unpair t₂.2
  let t₄ := Nat.unpair t₃.2
  let t₅ := Nat.unpair t₄.2
  let t₆ := Nat.unpair t₅.2
  (t₁.1, t₂.1, t₃.1, t₄.1, t₅.1, t₆.1, t₆.2)

/-- The encoding of a seven-tuple of naturals. -/
def code7 (p q n m₁ m₂ m₃ m₄ : ℕ) : ℕ :=
  Nat.pair p (Nat.pair q (Nat.pair n (Nat.pair m₁ (Nat.pair m₂ (Nat.pair m₃ m₄)))))

theorem un7_code7 (p q n m₁ m₂ m₃ m₄ : ℕ) :
    un7 (code7 p q n m₁ m₂ m₃ m₄) = (p, q, n, m₁, m₂, m₃, m₄) := by
  simp only [un7, code7, Nat.unpair_pair]

/-- **The countable family** of test functions, as an explicit sequence. -/
def famE (k : ℕ) : Fn :=
  famRaw (un7 k).1 (un7 k).2.1 (un7 k).2.2.1 (un7 k).2.2.2.1 (un7 k).2.2.2.2.1
    (un7 k).2.2.2.2.2.1 (un7 k).2.2.2.2.2.2

theorem famE_code (p q n m₁ m₂ m₃ m₄ : ℕ) :
    famE (code7 p q n m₁ m₂ m₃ m₄) = famRaw p q n m₁ m₂ m₃ m₄ := by
  rw [famE, un7_code7]

/-- The set of values of `famE`. -/
def famSet : Set Fn := Set.range famE

theorem contDiff_famE (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (famE k)) := by
  rw [famE]
  exact contDiff_famRaw _ _ _ _ _ _ _

/-- **The designated far bump** `Gfar`: the family element with `p = q = 0` and `n = 3` on the
box `[40/4, 80/4] × [1/4, 5/4] = [10,20] × [0.25,1.25]` (inside the quadrant, and with `z`-box
disjoint from the boxes `[1/3,2/3]` used in the independence argument of `GramSchmidt.lean`).
It is used to adjust the zero mode `L₁₂(·)(0)`. -/
def Gfar : Fn := famRaw 0 0 3 40 80 1 5

/-- The zero mode of the far bump, `c₀ = L₁₂(Gfar)(0)`.  It is positive (`c0_pos`), which is
what makes the adjustment `testFam` well behaved. -/
def c0 : ℝ := Work.Construction.L12 Gfar 0

/-- **The `L₁₂`-adjusted family**: a family element minus its zero mode times the fixed far
bump.  Every element has `L₁₂(·)(0) = 0`, is `C^∞` and is supported in the same box as the
family element (`testFam_cc`, `testFam_l12`). -/
def testFam (k : ℕ) : Fn :=
  fun z θ => famE k z θ - (Work.Construction.L12 (famE k) 0 / c0) * Gfar z θ

theorem testFam_code (p q n m₁ m₂ m₃ m₄ : ℕ) :
    testFam (code7 p q n m₁ m₂ m₃ m₄)
      = fun z θ => famRaw p q n m₁ m₂ m₃ m₄ z θ
          - (Work.Construction.L12 (famRaw p q n m₁ m₂ m₃ m₄) 0 / c0) * Gfar z θ := by
  unfold testFam
  rw [famE_code]

/-- The set of values of `testFam`. -/
def testSet : Set Fn := Set.range testFam

/-- The parameter condition under which a family element is a genuine test function: its box
`[m₁/(n+1), m₂/(n+1)] × [m₃/(n+1), m₄/(n+1)]` is nondegenerate and lies inside the quadrant
`[0,∞) × [0,π/2]`. -/
def GoodTup (p q n m₁ m₂ m₃ m₄ : ℕ) : Prop :=
  0 < m₁ ∧ m₁ < m₂ ∧ 0 < m₃ ∧ m₃ < m₄ ∧ ((m₃ : ℝ) + m₄) ≤ ((n : ℝ) + 1) * (π / 2)

theorem goodTup_code {p q n m₁ m₂ m₃ m₄ : ℕ} (h : GoodTup p q n m₁ m₂ m₃ m₄) :
    GoodTup p q n m₁ m₂ m₃ m₄ := h

/-- **The index predicate of the guarded family**: `k` decodes to a parameter tuple whose box
`[m₁/(n+1), m₂/(n+1)] × [m₃/(n+1), m₄/(n+1)]` is nondegenerate and lies strictly inside the
quadrant `(0,∞) × (0,π/2)`.  This is the exact condition under which the family element is a
test function (`famE_cc_of_goodIdx`); it is *implied* by `GoodTup`, which is the slightly
stronger symmetric box condition used by `famE_basic`. -/
def GoodIdx (k : ℕ) : Prop :=
  0 < (un7 k).2.2.2.1 ∧ (un7 k).2.2.2.1 < (un7 k).2.2.2.2.1 ∧ 0 < (un7 k).2.2.2.2.2.1 ∧
    (un7 k).2.2.2.2.2.1 < (un7 k).2.2.2.2.2.2 ∧
    ((un7 k).2.2.2.2.2.2 : ℝ) < (((un7 k).2.2.1 : ℝ) + 1) * (π / 2)

/-- The weak (asymmetric) box condition implied by `GoodTup`. -/
theorem goodTup_weak {p q n m₁ m₂ m₃ m₄ : ℕ} (h : GoodTup p q n m₁ m₂ m₃ m₄) :
    0 < m₁ ∧ m₁ < m₂ ∧ 0 < m₃ ∧ m₃ < m₄ ∧ (m₄ : ℝ) < ((n : ℝ) + 1) * (π / 2) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  have h₃R : (0 : ℝ) < (m₃ : ℝ) := by exact_mod_cast h₃
  linarith

theorem goodTup_goodIdx {p q n m₁ m₂ m₃ m₄ : ℕ} (h : GoodTup p q n m₁ m₂ m₃ m₄) :
    GoodIdx (code7 p q n m₁ m₂ m₃ m₄) := by
  rw [GoodIdx, un7_code7]
  exact goodTup_weak h

/-- **The guarded family**: `testFam k` when the index decodes to a good parameter tuple, and
the zero function otherwise.  It is `Coreφ`-valued (`famGood_core`), it contains all the
`testFam` elements that the density argument produces, and the junk indices only add the zero
function, which Gram–Schmidt discards — this is why the final basis is indexed by `ℕ` with no
side conditions. -/
def famGood (k : ℕ) : Fn := by
  classical
  exact if GoodIdx k then testFam k else 0

theorem famGood_code {p q n m₁ m₂ m₃ m₄ : ℕ} (h : GoodTup p q n m₁ m₂ m₃ m₄) :
    famGood (code7 p q n m₁ m₂ m₃ m₄) = testFam (code7 p q n m₁ m₂ m₃ m₄) := by
  classical
  rw [famGood, if_pos (goodTup_goodIdx h)]

/-- The guarded family at a good index is the `L₁₂`-adjusted family element. -/
theorem famGood_eq_testFam {k : ℕ} (h : GoodIdx k) : famGood k = testFam k := by
  classical
  rw [famGood, if_pos h]

/-- The guarded family at a bad index is the zero function. -/
theorem famGood_eq_zero {k : ℕ} (h : ¬ GoodIdx k) : famGood k = 0 := by
  classical
  rw [famGood, if_neg h]

/-! ## The density statements of the design -/

/-- **`DenseSpanO`** (`FTS_ELL_GALERKIN_STMTS`): the span of `φ` is dense in the `ℋ⁴`-norm in
the honest open class `{f : HQo α 4, BdryTraces α 4, L₁₂ f 0 = 0}`.  This is the form consumed
by Open3 (`weakDetermines'_of`).  (`HQo` is `VocabO.HQo`: interior `C^∞` plus `HkMem`.) -/
def DenseSpanO (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.BdryTraces α 4 f →
    Work.Construction.L12 f 0 = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Work.Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

/-- The `ℋ⁴`-density of the span of a sequence in an abstract class `K`, in the shape used by
the assembly: every element of `K` is the `ℋ⁴`-limit of finite combinations. -/
def DenseIn (α : ℝ) (K : Fn → Prop) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, K f → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Work.Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

theorem DenseIn.mono {α : ℝ} {K K' : Fn → Prop} {φ : ℕ → Fn} (h : DenseIn α K φ)
    (hKK' : ∀ f, K' f → K f) : DenseIn α K' φ :=
  fun f hf => h f (hKK' f hf)

end Work.FTS.GalBasis
