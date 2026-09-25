import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_eq_norm_ftLp

/-!
# The canonical fractions and the Ionescu–Wainger projection of KMSZ §6

Source: Kosz–Mirek–Słomian–Zhang, *Remarks on the Ionescu–Wainger multiplier theorem*,
arXiv:2606.12663, §2.4 and §6.1: the **canonical fractions**

`R_{≤ N} := { a/q : q ∈ [1,N], gcd (a,q) = 1 }`

(as points of the circle `𝕋 = ℝ/ℤ`), the smoothing `η_{≤ m}(ξ) = η (2^{-m} ξ)` of a bump
`η` with `1_{[-1/4,1/4]} ≤ η ≤ 1_{(-1/2,1/2)}`, and the **dyadic Ionescu–Wainger projections**

`Π_{≤ l, ≤ m} := T_ℤ [J_1 | η_{≤ m} K_{Σ_{≤ l}}]`,

the `ℓ²(ℤ)`-multiplier whose symbol is the multifrequency extension (KMSZ (2.2))
`Σ_{σ ∈ R_{≤ 2^l}} η_{≤ m} (ξ - σ)`.  In the vocabulary of this development that symbol is exactly
`arcSymbol η_{≤ m} (canonicalFinset (2^l))`, so `Π_{≤ l, ≤ m} f = opArc η_{≤ m} h (canonicalFinset (2^l)) f hf`.

This file provides

* `canonicalFinset N` — the canonical fractions with denominator `≤ N`, as a `Finset` of the circle,
  with its membership description;
* `canonicalFinset_separation` — **distinct canonical fractions with denominators `≤ N` are
  `N^{-2}`-separated** (KMSZ: "if `m ≤ -2l - 2`, then the arcs `[θ - 2^m, θ + 2^m]` that comprise
  `M_{≤ l, ≤ m}` are pairwise disjoint");
* the elementary properties of `Π_{≤ l, ≤ m}` for a bump `φ` of scale `2^{m-1}`:
  the pointwise symbol bound (`norm_arcSymbol_canonical_le_one`, giving the `ℓ²`-contraction
  `opArc_canonical_l2_contract` — KMSZ §6.1(v)) and the frequency support
  (`hasFreqSupport_opArc_canonical` — KMSZ §6.1(ii));
* `IWProjectionBound` — KMSZ **(6.11)**, the `ℓᵖ(ℤ)` bound `‖Π_{≤ l, ≤ m} f‖_{ℓᵖ} ≲_p 2^{C_p γ l}
  ‖f‖_{ℓᵖ}` for `m ≤ -6 max{p, p/(p-1)} (l+1)`, stated as a named hypothesis: it is the *only*
  analytic input of the minor-arc half (KMSZ §6.2) of the assembly, and it is "a consequence of
  Theorem 1.9" (the Ionescu–Wainger multiplier theorem), i.e. of the `IonescuWainger` chapter of
  this development.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ## The canonical fractions -/

/-- **The canonical fractions with denominator `≤ N`** (KMSZ (2.1)), as a `Finset` of the circle:
the points `a/q` with `1 ≤ q ≤ N`, `0 ≤ a < q` and `gcd (a,q) = 1`. -/
def canonicalFinset (N : ℕ) : Finset Work.BourgainPlan.IonescuWainger.Circle :=
  (Finset.Icc 1 N).biUnion (fun q =>
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun (a : ℕ) => arcPt q (a : ℤ)))

/-- Membership in the set of canonical fractions. -/
theorem mem_canonicalFinset {N : ℕ} {β : Work.BourgainPlan.IonescuWainger.Circle} :
    β ∈ canonicalFinset N ↔
      ∃ q ∈ Finset.Icc 1 N, ∃ a ∈ Finset.range q,
        Nat.Coprime a q ∧ arcPt q (a : ℤ) = β := by
  classical
  rw [canonicalFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hβ⟩
    rw [Finset.mem_image] at hβ
    obtain ⟨a, ha, rfl⟩ := hβ
    rw [Finset.mem_filter] at ha
    exact ⟨q, hq, a, ha.1, ha.2, rfl⟩
  · rintro ⟨q, hq, a, ha, hcop, rfl⟩
    exact ⟨q, hq, Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hcop⟩, rfl⟩⟩

/-- **Distinct canonical fractions with denominators `≤ N` are `1/N²`-separated.**  This is the
disjointness of the arcs `M_{≤ l, ≤ m}` for `m ≤ -2l-2` (KMSZ §6.1): with `N = 2^l`, the arcs of
radius `2^m ≤ 2^{-2l-1}` around distinct points of `canonicalFinset (2^l)` do not meet. -/
theorem canonicalFinset_separation {N : ℕ} (hN : 1 ≤ N) {β β' : Work.BourgainPlan.IonescuWainger.Circle}
    (hβ : β ∈ canonicalFinset N) (hβ' : β' ∈ canonicalFinset N) (hne : β ≠ β') :
    1 / (N : ℝ) ^ 2 ≤ ‖β - β'‖ := by
  classical
  obtain ⟨q, hq, a, ha, hcop, rfl⟩ := mem_canonicalFinset.mp hβ
  obtain ⟨q', hq', a', ha', hcop', rfl⟩ := mem_canonicalFinset.mp hβ'
  rw [Finset.mem_Icc] at hq hq'
  obtain ⟨hq1, hqN⟩ := hq
  obtain ⟨hq1', hqN'⟩ := hq'
  have hqz : q ≠ 0 := by omega
  have hq'z : q' ≠ 0 := by omega
  have hQ1 : 1 ≤ q * q' := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hqz hq'z)
  have hsub : arcPt q (a : ℤ) - arcPt q' (a' : ℤ)
      = arcPt (q * q') ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)) :=
    arcPt_sub_denom hqz hq'z (a : ℤ) (a' : ℤ)
  have hne0 : arcPt (q * q') ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)) ≠ 0 := by
    intro h0
    refine hne ?_
    have hz : arcPt q (a : ℤ) - arcPt q' (a' : ℤ) = 0 := by rw [hsub, h0]
    exact sub_eq_zero.mp hz
  have h1 : 1 / ((q * q' : ℕ) : ℝ) ≤ ‖arcPt q (a : ℤ) - arcPt q' (a' : ℤ)‖ := by
    rw [hsub]
    exact norm_arcPt_ge hQ1 hne0
  have hqq : ((q * q' : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h1' : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqN
    have h2' : (q' : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqN'
    have h0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    calc ((q * q' : ℕ) : ℝ) = (q : ℝ) * (q' : ℝ) := by push_cast; ring
      _ ≤ (N : ℝ) * (N : ℝ) := mul_le_mul h1' h2' (by positivity) h0
      _ = (N : ℝ) ^ 2 := by ring
  have hpos : (0 : ℝ) < ((q * q' : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc 1 / (N : ℝ) ^ 2 ≤ 1 / ((q * q' : ℕ) : ℝ) := by
        apply one_div_le_one_div_of_le hpos hqq
    _ ≤ ‖arcPt q (a : ℤ) - arcPt q' (a' : ℤ)‖ := h1

/-! ## The pointwise symbol bound and the `ℓ²` contraction -/

/-- **The pointwise bound on the Ionescu–Wainger symbol**: if `φ` is supported in the ball of
radius `ε`, is bounded by `1`, and `2ε < 2^{-2l}`, then the multifrequency extension
`Σ_{σ ∈ R_{≤ 2^l}} φ (· - σ)` is bounded by `1` pointwise — because the arcs around distinct
canonical fractions with denominator `≤ 2^l` do not overlap. -/
theorem norm_arcSymbol_canonical_le_one {l : ℕ} {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ} {ε : ℝ}
    (hφbd : ∀ ξ, ‖φ ξ‖ ≤ 1) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    (hε : 2 * ε < 1 / (((2 ^ l : ℕ) : ℝ)) ^ 2)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    ‖arcSymbol φ (canonicalFinset (2 ^ l)) ξ‖ ≤ 1 :=
  norm_arcSymbol_le hφbd hφsupp
    (fun β hβ β' hβ' hne =>
      canonicalFinset_separation (N := 2 ^ l) Nat.one_le_two_pow hβ hβ' hne)
    hε ξ

/-- **The `ℓ²` contraction** (KMSZ §6.1(v)): under the hypotheses of
`norm_arcSymbol_canonical_le_one`, the Ionescu–Wainger projection `Π_{≤ l, ≤ m}` (with the bump
`φ` of scale `ε`) is a contraction of `ℓ²(ℤ)`, by Plancherel and the pointwise symbol bound. -/
theorem opArc_canonical_l2_contract {l : ℕ} {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {ε : ℝ}
    (hφbd : ∀ ξ, ‖φ ξ‖ ≤ 1) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    (hε : 2 * ε < 1 / (((2 ^ l : ℕ) : ℝ)) ^ 2) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∑' n : ℤ, ‖opArc φ hφ (canonicalFinset (2 ^ l)) f hf n‖ ^ 2 ≤ ∑' n : ℤ, ‖f n‖ ^ 2 := by
  classical
  set E : Finset Work.BourgainPlan.IonescuWainger.Circle := canonicalFinset (2 ^ l) with hE
  set Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) := arcSymbolLp φ hφ E with hΦ
  have hg : Memℓp (opMul Φ f hf) 2 := opMul_memℓp Φ f hf
  have hcoe : (Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbol φ E :=
    arcSymbolLp_coeFn φ hφ E
  -- the a.e. bound on the symbol
  have hbd : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)), ‖(Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ≤ 1 := by
    filter_upwards [hcoe] with ξ hξ
    rw [hξ]
    exact norm_arcSymbol_canonical_le_one hφbd hφsupp hε ξ
  -- the a.e. pointwise comparison of the multiplied function with `g`
  have hle : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) ξ‖
        ≤ ‖(ftLp f hf : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ := by
    filter_upwards [hbd, Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Φ (ftLp f hf)] with ξ hb hsm
    have hsm' : ((Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
          Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
        = (Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
          * (ftLp f hf : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ := by
      rw [hsm]; rfl
    rw [hsm', norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hb
  have hmono : eLpNorm (⇑(Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) 2
        (AddCircle.haarAddCircle (T := 1))
      ≤ eLpNorm (⇑(ftLp f hf) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) 2 (AddCircle.haarAddCircle (T := 1)) :=
    eLpNorm_mono_ae (Lp.aestronglyMeasurable _) hle
  have hfin : eLpNorm (⇑(ftLp f hf) : Work.BourgainPlan.IonescuWainger.Circle → ℂ) 2
      (AddCircle.haarAddCircle (T := 1)) ≠ ⊤ :=
    (Lp.eLpNorm_lt_top (ftLp f hf)).ne
  have hnorm : ‖(Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖
      ≤ ‖ftLp f hf‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact ENNReal.toReal_mono hfin hmono
  have hsq : ‖(Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ ^ 2
      ≤ ‖ftLp f hf‖ ^ 2 := by
    have h0 : 0 ≤ ‖(Φ • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 hnorm 2
  have hft : ftLp (opMul Φ f hf) hg = Φ • ftLp f hf := ftLp_opMul Φ f hf
  calc ∑' n : ℤ, ‖opArc φ hφ E f hf n‖ ^ 2
      = ∑' n : ℤ, ‖opMul Φ f hf n‖ ^ 2 := by rw [opArc, hΦ]
    _ = ‖ftLp (opMul Φ f hf) hg‖ ^ 2 := tsum_norm_sq_eq_norm_ftLp hg
    _ = ‖Φ • ftLp f hf‖ ^ 2 := by rw [hft]
    _ ≤ ‖ftLp f hf‖ ^ 2 := hsq
    _ = ∑' n : ℤ, ‖f n‖ ^ 2 := (tsum_norm_sq_eq_norm_ftLp hf).symm

/-! ## The frequency support of the projection -/

/-- **The frequency support of `Π_{≤ l, ≤ m}f`** (KMSZ §6.1(ii)): it is contained in the union of
the arcs `σ + [-ε, ε]`, `σ ∈ R_{≤ 2^l}`, i.e. in `M_{≤ l, ≤ m}` when `ε ≤ 2^m`. -/
theorem hasFreqSupport_opArc_canonical {l : ℕ} {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {ε : ℝ}
    (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    HasFreqSupport (opArc φ hφ (canonicalFinset (2 ^ l)) f hf)
      (opMul_memℓp (arcSymbolLp φ hφ (canonicalFinset (2 ^ l))) f hf)
      {ξ | ∃ β ∈ canonicalFinset (2 ^ l),
        ξ - β ∈ {η : Work.BourgainPlan.IonescuWainger.Circle | ‖η‖ ≤ ε}} := by
  refine hasFreqSupport_opArc φ hφ (canonicalFinset (2 ^ l)) f hf ?_
  intro ξ hξ
  exact hφsupp ξ (by simpa using hξ)


/-- **A unique-bump value computation**: if at one point of `E` the bump equals `1`, if `φ` vanishes
off the ball of radius `ε'`, and if the points of `E` are `2ε'`-separated, then the whole symbol
equals `1` at `ξ` (all the other bumps vanish there). -/
lemma arcSymbol_eq_one_of_unique {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    {E : Finset Work.BourgainPlan.IonescuWainger.Circle} {ε' : ℝ}
    (hφsupp : ∀ ξ, ε' < ‖ξ‖ → φ ξ = 0)
    (hsep : ∀ β ∈ E, ∀ β' ∈ E, β ≠ β' → 2 * ε' < ‖β - β'‖)
    {β₀ : Work.BourgainPlan.IonescuWainger.Circle} (hβ₀ : β₀ ∈ E)
    {ξ : Work.BourgainPlan.IonescuWainger.Circle} (hφ₀ : φ (ξ - β₀) = 1) :
    arcSymbol φ E ξ = 1 := by
  classical
  have hb0 : ‖ξ - β₀‖ ≤ ε' := le_of_not_gt fun h => by rw [hφsupp _ h] at hφ₀; exact one_ne_zero hφ₀.symm
  have hsingle : ∀ β ∈ E, φ (ξ - β) = if β = β₀ then (1 : ℂ) else 0 := by
    intro β hβ
    by_cases h : β = β₀
    · simp [h, hφ₀]
    · rw [if_neg h]
      by_contra hne
      have hb : ‖ξ - β‖ ≤ ε' := le_of_not_gt fun hlt => hne (hφsupp _ hlt)
      have hsub : β - β₀ = (ξ - β₀) - (ξ - β) := by abel
      have h2 : ‖β - β₀‖ ≤ 2 * ε' := by
        rw [hsub]
        linarith [norm_sub_le (ξ - β₀) (ξ - β)]
      linarith [hsep β hβ β₀ hβ₀ h]
  rw [arcSymbol_apply, Finset.sum_congr rfl hsingle, Finset.sum_ite_eq' E β₀ (fun _ => (1 : ℂ))]
  simp [hβ₀]

/-- **The projection symbol equals `1` on the inner arcs** (KMSZ §6.1(iv)): if `φ` is a bump that
equals `1` on the ball of radius `ε`, vanishes off the ball of radius `ε' ≥ ε`, and the canonical
fractions with denominator `≤ 2^l` are `2ε'`-separated (which holds as soon as `2ε' < 2^{-2l}`),
then `arcSymbol φ (canonicalFinset (2^l))` equals `1` on the union of the inner arcs of radius `ε`.
This is what makes `1 - σ` vanish there, i.e. what allows the minor-arc step (6.15) to use the Weyl
bound off the arcs. -/
theorem arcSymbol_canonical_eq_one {l : ℕ} {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    {ε ε' : ℝ} (hεε' : ε ≤ ε') (hφone : ∀ ξ, ‖ξ‖ ≤ ε → φ ξ = 1)
    (hφsupp : ∀ ξ, ε' < ‖ξ‖ → φ ξ = 0)
    (hε' : 2 * ε' < 1 / (((2 ^ l : ℕ) : ℝ)) ^ 2)
    {ξ : Work.BourgainPlan.IonescuWainger.Circle}
    (hξ : ∃ β ∈ canonicalFinset (2 ^ l), ‖ξ - β‖ ≤ ε) :
    arcSymbol φ (canonicalFinset (2 ^ l)) ξ = 1 := by
  obtain ⟨β₀, hβ₀, hβ₀ξ⟩ := hξ
  refine arcSymbol_eq_one_of_unique hφsupp (fun β hβ β' hβ' hne => ?_) hβ₀
    (hφone _ hβ₀ξ)
  exact canonicalFinset_separation (N := 2 ^ l) Nat.one_le_two_pow hβ hβ' hne
    |> fun h => lt_of_lt_of_le hε' h

/-! ## The analytic input: KMSZ (6.11) -/

/-- **KMSZ (6.11)**: the `ℓᵖ(ℤ)` bound for the dyadic Ionescu–Wainger projections,
`‖Π_{≤ l, ≤ m} f‖_{ℓᵖ} ≤ D · 2^{C_p γ l} ‖f‖_{ℓᵖ}` for `m ≤ -6 max{p, p/(p-1)} (l+1)`, uniform in
the bump `φ` of scale `2^{m-1}` (a smooth even bump `η` with `1_{[-1/4,1/4]} ≤ η ≤ 1_{(-1/2,1/2)}` and
`η_{≤ m}(ξ) = η (2^{-m} ξ)`; only the support and size of `φ` are used).

This is the single analytic input of the minor-arc half of KMSZ §6.2 (and, through §5, of the
Rademacher–Menshov chain of this development).  It is *"a consequence of Theorem 1.9"*, the
Ionescu–Wainger multiplier theorem of the `IonescuWainger` chapter of this development.

**The shape of the two constants matters, and this is the faithful reading of the source.**  The
source states (6.11) as `‖Π_{≤ l, ≤ m} f‖_{ℓᵖ} ≲_{p,γ} 2^{C_p γ l} ‖f‖_{ℓ^p}`, i.e.

* the *exponent coefficient* is `C_p γ` with `C_p` depending on `p` **only** — in particular it does
  *not* depend on `γ`; and
* the constant `D = D(p,γ)` hidden in `≲_{p,γ}` does depend on `γ`.

Both points are necessary for the assembly, and dropping the constant is *not* harmless:

* at `l = 0` the projection is the multiplier by the single bump `φ` itself (`canonicalFinset 1 =
  {0}`), i.e. the `ℓᵖ(ℤ)`-multiplier whose symbol is the sequence `(φ(-j))_{j ∈ ℤ}`; its norm is
  the `M_p(𝕋)`-multiplier norm of `φ`, which for `p ≠ 2` is *not* bounded by `sup |φ|` (a smooth
  step-like bump of height `1` has multiplier norm `> 1`, approaching the Riesz/Hilbert constant;
  by de Leeuw transference plus Young it is `≲ ‖φ̂‖_{ℓ¹}`, which is `> 1` for a bump whose profile
  has sign-changing Fourier transform).  Hence a constant `D > 1` is needed already at `l = 0`;
* if instead one absorbs `D` into the exponent — writing the bound as `2^{C'γ(l+1)}` — then the
  *smallest admissible* `C'` satisfies `C'γ ≥ log₂ D(0) > 0`, so `C'γ` is bounded below by a positive
  `γ`-independent constant; the loss in `N` is then `N^{C'γα}` with `α = l / log₂ N`, and the
  interpolation step (6.16) of §6.2 — which needs the *exponent* `C_p γ α (1-θ)` of the loss to be
  smaller than the gain `ν δ θ` for a small *free* `γ` — no longer works.  With the constant kept
  separate, `γ` is free in the exponent and the gain is obtained.

So the quantification below is `∃ C (before γ), ∀ γ, ∃ D`, which is exactly the source's
statement. -/
def IWProjectionBound : Prop :=
  ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → ∃ D : ℝ, 0 < D ∧
    ∀ l : ℕ, ∀ m : ℤ, (m : ℝ) ≤ -(6 * max p (p / (p - 1)) * ((l : ℝ) + 1)) →
    ∀ (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))),
      (∀ ξ, ‖φ ξ‖ ≤ 1) → (∀ ξ, (2 : ℝ) ^ (m - 1) < ‖ξ‖ → φ ξ = 0) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset (2 ^ l)) f hf n‖ₑ ^ p ∂Measure.count
          ≤ ENNReal.ofReal ((D * 2 ^ (C * γ * (l : ℝ))) ^ p)
              * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count

end

end Work.BourgainPlan.Maximal
