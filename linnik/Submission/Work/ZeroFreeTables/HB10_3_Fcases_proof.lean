/-
# `HB10_3_Fcases_proof`

The `F`-method cases of Heath-Brown (1992), §10 (his Lemmas 10.1 and 10.2), in the form of
`Engine.HB10_3_Fcases`:

> three conjugate pairs, `(χ₁,ρ₁)` realising the minimum of `λ = (1-Re)·log q` over all
> non-principal zeros of height `≤ 10`, and `(χ₂,ρ₂)`, `(χ₃,ρ₃)` two further pairs at distance
> at most one conjugate pair each, which are **not** in the `P₃` configuration (all three
> characters real, `χ₁χ₂χ₃ = χ₀`, `ρ₁` real), satisfy `max (λ(ρ₂)) (λ(ρ₃)) ≥ 6/7 - ε`.

The proof is the case analysis of HB §10, every branch being a *proved* engine of the
workspace at rectangle height `L = 1` (where `IsRectMin 1` is the wide minimality
`IsMin1WideAt 10` and `IsZAt 1` is the working region `IsZ`):

* `ρ₁` complex (`ρ₁.im ≠ 0`): HB Lemmas 10.1 **and** 10.2 at once — the engine
  `OffAxis/HB10_3EngineNear` produces (10.6) for *every* configuration of the three pairs, so
  no product condition on the characters is needed;
* `ρ₁` real, no signed triple product `χ₁^{±1}χ₂^{±1}χ₃^{±1}` principal: HB Lemma 10.1 — the
  engine `OffAxis/Rect10_3RealF1Clean`'s `hb106RealC` gives (10.6) (it never uses its
  off-axis sibling's hypothesis `1 < |Im ρ₁|`);
* `ρ₁` real, `χ₁` complex, `χ₁χ₂χ₃ = χ₀` (the reduction to this normal form is by conjugating
  one of the pairs, `(χ,ρ) ↦ (χ⁻¹,ρ̄)`, which preserves `IsRectMin`, `IsZAt`, all the `λ`'s and
  the distinctness hypotheses): HB Lemma 10.2 with `ρ₁ ∈ ℝ` — the engine
  `OffAxis/Rect10_3RealF2Complex`'s `rect103Engine` (copied as `rect103EngineNoMin`: its two
  "successive minimum" hypotheses on `ρ₂`, `ρ₃` occur only in the statement, never in the
  proof, and the present statement cannot supply them);
* `ρ₁` real, `χ₁` real, `χ₂,χ₃` complex, `χ₁χ₂χ₃ = χ₀`: HB §10 case 3, the `β₂`-centred
  argument (10.12) — the engine `OffAxis/Rect10_3OneReal`'s `rect103OneRealH` (copied as
  `rect103OneRealNoMin`, for the same reason);
* `ρ₁` real, `χ₁,χ₂,χ₃` real, `χ₁χ₂χ₃ = χ₀`: this is exactly the `P₃` case
  (`HBLemma10_3_engine`), which the statement excludes.  (If all three characters are real and
  *some* signed triple product is principal, then `χ₁χ₂χ₃ = χ₀`: multiplying e.g.
  `χ₁χ₂ = χ₃` by `χ₃` gives `χ₁χ₂χ₃ = χ₃² = χ₀`.)

Each branch finishes with the §10 numerical endgame for HB Lemma 7.2's test function at
`λ = 6/7` (`endgame103` below, assembled from the proved `rect10_3_endgame_clean`,
`MomentStep103` and `tf72f_refute_quant_clean`), whose margin `83/9000` is what turns (10.6)
into `λ₃ ≥ 6/7 - ε` with the fixed slack `ε' = min (ε/10⁶) 10⁻⁶`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.OffAxis.Rect10_3H_F1
import Submission.Work.ZeroFreeTables.OffAxis.Rect10_3EngineH
import Submission.Work.ZeroFreeTables.OffAxis.tf72Fc_ten_eight
import Submission.Work.OffAxis.HB10_3EngineNear
import Submission.Work.OffAxis.Rect10_3RealF1Clean
import Submission.Work.OffAxis.Rect10_3RealF2Complex
import Submission.Work.OffAxis.Rect10_3OneReal
import Submission.Work.OffAxis.Rect10_3EndgameClean
import Submission.Work.OffAxis.MomentStep103
import Submission.Work.OffAxis.Rect10_3Sub2Numeric
import Submission.Work.OffAxis.TF72FarBound
import Submission.Work.ZeroFreeTables.Fcases.EngineRealChiC
import Submission.Work.ZeroFreeTables.Fcases.EngineOneReal

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Elementary transports -/

/-- **`IsMin1WideAt 10` is `IsRectMin 1`.**  The wide minimality clause is literally the
minimality clause of `IsRectMin` at height `1` (`10 * 1 = 10`), and the two region predicates
are the same three clauses. -/
lemma isRectMin_one_of_isMin1WideAt {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁) : Work.ZeroFreeTables.IsRectMin 1 χ₁ ρ₁ := by
  refine ⟨h.1.1, ?_⟩
  intro χ u hu
  exact h.2 χ u hu.1 hu.2.1 (by simpa using hu.2.2)

/-- `(a b c)² = 1` with `c² = 1` forces `a² = 1 ↔ b² = 1` (in a commutative group). -/
lemma sq_eq_one_iff_of_mul {G : Type*} [CommGroup G] {a b c : G} (hc : c ^ 2 = 1)
    (h : c * a * b = 1) : a ^ 2 = 1 ↔ b ^ 2 = 1 := by
  have hsq : (c * a * b) ^ 2 = c ^ 2 * (a ^ 2 * b ^ 2) := by
    calc (c * a * b) ^ 2 = (c * a) ^ 2 * b ^ 2 := by rw [mul_pow]
      _ = c ^ 2 * a ^ 2 * b ^ 2 := by rw [mul_pow]
      _ = c ^ 2 * (a ^ 2 * b ^ 2) := by rw [mul_assoc]
  have h2 : a ^ 2 * b ^ 2 = 1 := by
    have h3 : (c * a * b) ^ 2 = 1 := by rw [h, one_pow]
    rw [hsq, hc, one_mul] at h3
    exact h3
  constructor
  · intro ha
    rw [ha, one_mul] at h2
    exact h2
  · intro hb
    rw [hb, mul_one] at h2
    exact h2

/-- `(a⁻¹)² = 1` implies `a² = 1`. -/
lemma sq_eq_one_of_inv_sq {G : Type*} [Group G] {a : G} (h : a⁻¹ ^ 2 = 1) : a ^ 2 = 1 := by
  rw [inv_pow] at h
  exact inv_eq_one.mp h

/-- `a⁻¹ = b⁻¹` implies `a = b`. -/
lemma eq_of_inv_eq_inv {G : Type*} [Group G] {a b : G} (h : a⁻¹ = b⁻¹) : a = b := by
  have h' := congrArg (fun z : G => z⁻¹) h
  simpa using h'

/-- `a⁻¹ = b` implies `a = b⁻¹`. -/
lemma eq_inv_of_inv_eq {G : Type*} [Group G] {a b : G} (h : a⁻¹ = b) : a = b⁻¹ := by
  rw [← h, inv_inv]

/-! ## The numerical endgame: from (10.6) to `λ₃ ≥ 6/7 - ε`

HB (10.6) for the test function of Lemma 7.2 at `λ = 6/7` (with the fixed slack
`ε' = min (ε/10⁶) 10⁻⁶`, whose `s = 8ε'f(0)` satisfies `s ≤ ε/10⁴` and `s < 83/9000`), the
ordering `0 ≤ λ₁ ≤ λ₂ ≤ λ₃ ≤ 6/7` and the moment step `MomentStep103`, together with the
quantitative falsity of (10.7) for `λ₁ ≤ 792/1000` (`tf72f_refute_quant_clean`, with the
margin `83/9000`), give `λ₃ ≥ 6/7 - ε`. -/
lemma endgame103 (ε : ℝ) (hε : 0 < ε) {l₁ l₂ l₃ : ℝ}
    (h01 : 0 ≤ l₁) (h12 : l₁ ≤ l₂) (h23 : l₂ ≤ l₃) (h36 : l₃ ≤ 6/7)
    (h106 : 0 ≤ (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F (-l₁)
      - (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F 0
      - (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F (l₂ - l₁)
      - (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).F (l₃ - l₁)
      + (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)).f 0
        * (7/6 + 8 * min (ε/1000000) (1/1000000))) :
    6/7 - ε ≤ l₃ := by
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)
    with hTdef
  have hTx₀ : T.x₀ = 7/3 := by
    rw [hTdef]
    show (2:ℝ) / ((6:ℝ)/7) = 7/3
    norm_num
  have hTf : T.f = Work.ZeroFreeTables.tf72f ((6:ℝ)/7) := rfl
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTf]
    show Work.ZeroFreeTables.tf72f ((6:ℝ)/7) 0 = 32/35
    rw [Work.ZeroFreeTables.tf72f_at_zero ((6:ℝ)/7) (by norm_num)]
    norm_num
  have hTF0 : T.F 0 = 8/9 := by
    show (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) ((0:ℝ) : ℂ)).re = 8/9
    rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
    exact Work.ZeroFreeTables.tf72Fc_zero_re ((6:ℝ)/7) (by norm_num)
  have hTF6 : T.F (-((6:ℝ)/7)) = 8/5 := by
    show (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) (((-((6:ℝ)/7) : ℝ)) : ℂ)).re = 8/5
    exact Work.ZeroFreeTables.tf72Fc_neglam_re ((6:ℝ)/7) (by norm_num)
  have hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-((6:ℝ)/7)) := by
    rw [hTf0, hTF0, hTF6]
    norm_num
  set ε' : ℝ := min (ε/1000000) (1/1000000) with hε'def
  have hε' : 0 < ε' := by
    rw [hε'def]
    exact lt_min (by linarith) (by norm_num)
  have hε'1 : ε' ≤ ε/1000000 := by rw [hε'def]; exact min_le_left _ _
  have hε'2 : ε' ≤ 1/1000000 := by rw [hε'def]; exact min_le_right _ _
  set s : ℝ := 8 * ε' * T.f 0 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hse : s ≤ ε/10000 := by
    rw [hsdef, hTf0]
    nlinarith [hε'1, hε]
  have hs83 : s < 83/9000 := by
    rw [hsdef, hTf0]
    nlinarith [hε'2]
  have hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
    intro l hl0 hl67 hl
    have e1 : T.F (-(6/7)) = ∫ t in (0:ℝ)..(7/3),
        Real.exp ((6/7:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.OffAxis.TestFn_F_neg_eq_integral', hTx₀, hTf]
    have e2 : T.F (-l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (l * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.OffAxis.TestFn_F_neg_eq_integral', hTx₀, hTf]
    have e3 : T.F 0 = ∫ t in (0:ℝ)..(7/3), Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.TestFn_F_eq_integral, hTx₀, hTf]
      apply intervalIntegral.integral_congr
      intro t _
      simp
    have e4 : T.F (6/7 - l) = ∫ t in (0:ℝ)..(7/3),
        Real.exp (-((6/7 - l) * t)) * Work.ZeroFreeTables.tf72f (6/7) t := by
      rw [Work.ZeroFreeTables.TestFn_F_eq_integral, hTx₀, hTf]
    rw [e1, e2, e3, e4] at hl
    exact Work.OffAxis.MomentStep103 ε s hε hs0 hse l hl0 hl67 hl
  have href : ∀ l : ℝ, 0 ≤ l → l ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l) ≥ 2 * (T.F 0 - T.F (6/7 - l)) + 83/9000 :=
    fun l h0 h1 => Work.OffAxis.tf72f_refute_quant_clean T hTx₀ hTf hTF0 hTF6 l h0 h1
  have h106' : T.F (-l₁) - T.F 0 - T.F (l₂ - l₁) - T.F (l₃ - l₁)
      + T.f 0 * (7/6 + 8 * ε') ≥ 0 := h106
  exact Work.OffAxis.rect10_3_endgame_clean T ε' ε s l₁ l₂ l₃ hε hTx₀ hTf hTF0 hTF6 hL75
    hs0 hse (le_of_eq rfl) hs83 hmom href h106' h01 (le_trans h12 h23) h23 h36

/-! ## The branch `ρ₁.im ≠ 0`: HB Lemmas 10.1 and 10.2 together -/

/-- **The `F`-method cases with `ρ₁` complex.**  The engine `OffAxis/HB10_3EngineNear`
(HB §10, Lemmas 10.1 and 10.2, on the hypothesis `μ₁ ≠ 0`) gives (10.6) for every
configuration of the three pairs, so no product condition is needed. -/
lemma Fcases_complexRho (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin 1 χ₁ ρ₁ → ρ₁.im ≠ 0 →
      Work.ZeroFreeTables.IsZAt 1 χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt 1 χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      lamOf q ρ₂ ≤ lamOf q ρ₃ → lamOf q ρ₃ ≤ 6/7 - ε →
      6/7 - ε ≤ lamOf q ρ₃ := by
  have hε' : 0 < min (ε/1000000) (1/1000000) := lt_min (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := Work.OffAxis.HB10_3EngineNear
    (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)) (min (ε/1000000) (1/1000000))
    hε' 1 le_rfl
  refine ⟨q₀, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)
    with hTdef
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTdef]
    show Work.ZeroFreeTables.tf72f ((6:ℝ)/7) 0 = 32/35
    rw [Work.ZeroFreeTables.tf72f_at_zero ((6:ℝ)/7) (by norm_num)]
    norm_num
  have hTFc : T.Fc = Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) := rfl
  have hnum1 : ∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
      (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * (T.Fc ((μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a μ ha0 ha6 hμ
    have h := Work.ZeroFreeTables.OffAxis.tf72Fc_ten_eight.1 a μ ha0 ha6 hμ
    rw [hTFc, hTf0]
    linarith
  have hnum2 : ∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
      (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a μ ha0 ha6 hμ
    have h := Work.ZeroFreeTables.OffAxis.tf72Fc_ten_eight.2 a μ ha0 ha6 hμ
    rw [hTFc, hTf0]
    linarith
  have hl1nn : 0 ≤ lamOf q ρ₁ := Work.OffAxis.lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, by linarith [hZ2.2.2]⟩
  have h106 := hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 (by linarith) hnum1 hnum2
  exact endgame103 ε hε hl1nn hl12 hlam23 (by linarith) h106

/-! ## The branch `ρ₁.im = 0` with no principal signed triple product: HB Lemma 10.1 -/

/-- **HB Lemma 10.1** (no signed triple product `χ₁^{±1}χ₂^{±1}χ₃^{±1}` is principal) at
height `1`, with no minimality hypothesis on `ρ₂`, `ρ₃`. -/
lemma Fcases_noPrincipal (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin 1 χ₁ ρ₁ →
      Work.ZeroFreeTables.IsZAt 1 χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt 1 χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      lamOf q ρ₂ ≤ lamOf q ρ₃ → lamOf q ρ₃ ≤ 6/7 - ε →
      χ₁ * χ₂ * χ₃ ≠ 1 → χ₁ * χ₂ ≠ χ₃ → χ₁ * χ₃ ≠ χ₂ → χ₂ * χ₃ ≠ χ₁ →
      6/7 - ε ≤ lamOf q ρ₃ := by
  have hε' : 0 < min (ε/1000000) (1/1000000) := lt_min (by linarith) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := Work.ZeroFreeTables.OffAxis.hb106RealC
    (Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)) (min (ε/1000000) (1/1000000))
    hε' 1 le_rfl
  refine ⟨q₀, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3
    hp1 hp2 hp3 hp4
  have hl1nn : 0 ≤ lamOf q ρ₁ := Work.OffAxis.lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, by linarith [hZ2.2.2]⟩
  have h106 := hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 (by linarith) hp1 hp2 hp3 hp4
  exact endgame103 ε hε hl1nn hl12 hlam23 (by linarith) h106

/-! ## The branch `ρ₁.im = 0`, `χ₁² ≠ 1`, `χ₁χ₂χ₃ = χ₀`: HB Lemma 10.2 -/

/-- **HB Lemma 10.2** with `ρ₁` real and `χ₁` complex: (10.6) from the engine
`rect103EngineNoMin` (the principal product `χ₀ = χ₁χ₂χ₃` paid for by the companion pair
`χ₂χ₃ = χ₁⁻¹` at the real zero `ρ₁`), plus the endgame. -/
lemma Fcases_realChiComplex (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin 1 χ₁ ρ₁ → ρ₁.im = 0 → χ₁ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.IsZAt 1 χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt 1 χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      lamOf q ρ₂ ≤ lamOf q ρ₃ → lamOf q ρ₃ ≤ 6/7 - ε →
      χ₁ * χ₂ * χ₃ = 1 →
      6/7 - ε ≤ lamOf q ρ₃ := by
  have hε' : 0 < min (ε/1000000) (1/1000000) := lt_min (by linarith) (by norm_num)
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)
    with hTdef
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTdef]
    show Work.ZeroFreeTables.tf72f ((6:ℝ)/7) 0 = 32/35
    rw [Work.ZeroFreeTables.tf72f_at_zero ((6:ℝ)/7) (by norm_num)]
    norm_num
  have hTFc : T.Fc = Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) := rfl
  have hA : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re
        - 2 * (T.Fc ((m : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a m ha0 ha6
    have h := Work.OffAxis.TF72Num103a a m ha0 ha6
    rw [hTFc, hTf0]
    linarith
  have hB : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a m ha0 ha6 hm
    have h := Work.OffAxis.TF72Num103b a m ha0 ha6 hm
    rw [hTFc, hTf0]
    have h2 := (abs_le.mp h).2
    linarith
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hP : ∃ qP : ℕ, ∀ q : ℕ, qP ≤ q → ∀ [NeZero q] (s : ℂ),
      |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
      |s.im| ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
        ≤ Real.log (q : ℝ) *
            (∫ t in (0:ℝ)..T.x₀,
              Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                * ((T.f t : ℝ) : ℂ)).re
          + T.f 0 * min (ε/1000000) (1/1000000) * Real.log (q : ℝ) := by
    obtain ⟨q₀, hq₀⟩ := Work.OffAxis.principalShiftMain_aux T.x₀ B T.x₀_pos hB0
      T.f_cont T.f_supp T.f_diff hBnd (min (ε/1000000) (1/1000000)) hε' T.f0_pos
    exact ⟨q₀, fun q hq _ s hs1 hs2 => hq₀ hq s hs1 hs2⟩
  obtain ⟨q₀, hq₀⟩ := Work.OffAxis.rect103EngineNoMin T (min (ε/1000000) (1/1000000))
    hε' hP hA hB 1 le_rfl
  refine ⟨q₀, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hsq hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 hlam3 hprod
  have hl1nn : 0 ≤ lamOf q ρ₁ := Work.OffAxis.lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, by linarith [hZ2.2.2]⟩
  have h106 := hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hsq hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 (by linarith) hprod
  exact endgame103 ε hε hl1nn hl12 hlam23 (by linarith) h106

/-! ## The branch `ρ₁, χ₁` real and `χ₂, χ₃` complex: HB §10 case 3, (10.12) -/

/-- **HB §10 case 3**, exactly one real character: (10.6) from the engine
`rect103OneRealNoMin` (which uses `φ = 1/4` for the real character `χ₁` and the condition
(10.12) in place of (10.8)), plus the endgame. -/
lemma Fcases_realOneReal (ε : ℝ) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin 1 χ₁ ρ₁ → ρ₁.im = 0 → χ₁ ^ 2 = 1 →
      χ₂ ^ 2 ≠ 1 → χ₃ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.IsZAt 1 χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt 1 χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      lamOf q ρ₂ ≤ lamOf q ρ₃ → lamOf q ρ₃ ≤ 6/7 - ε →
      χ₁ * χ₂ * χ₃ = 1 →
      6/7 - ε ≤ lamOf q ρ₃ := by
  have hε' : 0 < min (ε/1000000) (1/1000000) := lt_min (by linarith) (by norm_num)
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T ((6:ℝ)/7) (by norm_num)
    with hTdef
  have hTf0 : T.f 0 = 32/35 := by
    rw [hTdef]
    show Work.ZeroFreeTables.tf72f ((6:ℝ)/7) 0 = 32/35
    rw [Work.ZeroFreeTables.tf72f_at_zero ((6:ℝ)/7) (by norm_num)]
    norm_num
  have hTFc : T.Fc = Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) := rfl
  have hTF6 : T.F (-((6:ℝ)/7)) = 8/5 := by
    rw [hTdef]
    show (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) (((-((6:ℝ)/7) : ℝ)) : ℂ)).re = 8/5
    exact Work.ZeroFreeTables.tf72Fc_neglam_re ((6:ℝ)/7) (by norm_num)
  have hsub : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 9/7 ≤ |m| →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re - (T.Fc ((m : ℂ) * Complex.I)).re
        ≤ 7 * T.f 0 / 24 := by
    intro a m ha0 ha6 hm
    have h := Work.OffAxis.Rect10_3Sub2Numeric a m ha0 ha6 hm
    rw [hTFc, hTf0]
    linarith
  have hlow : ∀ t m : ℝ, 0 ≤ t → t ≤ 6/7 → |m| ≤ 9/7 →
      3 * T.f 0 / 8 ≤ (T.Fc ((t : ℂ) + (m : ℂ) * Complex.I)).re := by
    intro t m ht0 ht6 hm
    have h := Work.OffAxis.rect103ReLowNumeric t m ht0 ht6 hm
    rw [hTFc, hTf0]
    linarith
  have hB : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 / 6 := by
    intro a m ha0 ha6 hm
    have h := Work.OffAxis.TF72FarBound a m ha0 ha6 hm
    rw [hTFc, hTf0]
    linarith
  have hF20 : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → |m| ≤ 9/7 →
      (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 * (7/4) := by
    intro a m ha0 ha6 hm
    have h1 := Work.OffAxis.abs_Fc_re_le T (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)
    have h2 : (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I).re = -a := by simp
    rw [h2] at h1
    have h3 : T.F (-a) ≤ T.F (-((6:ℝ)/7)) :=
      Work.ZeroFreeTables.TestFn_F_antitone T (by linarith)
    rw [hTF6] at h3
    have h4 : T.f 0 * (7/4) = 8/5 := by rw [hTf0]; norm_num
    rw [h4]
    linarith [abs_le.mp h1 |>.2, h3]
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hP : ∃ qP : ℕ, ∀ q : ℕ, qP ≤ q → ∀ [NeZero q] (s : ℂ),
      |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
      |s.im| ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
        ≤ Real.log (q : ℝ) *
            (∫ t in (0:ℝ)..T.x₀,
              Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                * ((T.f t : ℝ) : ℂ)).re
          + T.f 0 * min (ε/1000000) (1/1000000) * Real.log (q : ℝ) := by
    obtain ⟨q₀, hq₀⟩ := Work.OffAxis.principalShiftMain_aux T.x₀ B T.x₀_pos hB0
      T.f_cont T.f_supp T.f_diff hBnd (min (ε/1000000) (1/1000000)) hε' T.f0_pos
    exact ⟨q₀, fun q hq _ s hs1 hs2 => hq₀ hq s hs1 hs2⟩
  obtain ⟨q₀, hq₀⟩ := Work.OffAxis.rect103OneRealNoMin T (min (ε/1000000) (1/1000000)) hε'
    hP hsub hlow hB hF20 1 le_rfl
  refine ⟨q₀, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him h1sq h2sq h3sq hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 hlam3 hprod
  have hl1nn : 0 ≤ lamOf q ρ₁ := Work.OffAxis.lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, by linarith [hZ2.2.2]⟩
  have h106 := hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him h1sq h2sq h3sq hprod hZ2 hZ3
    h21 h2i h31 h3i h32 h3ii hlam23 (by linarith)
  exact endgame103 ε hε hl1nn hl12 hlam23 (by linarith) h106

/-! ## The target -/

theorem HB10_3_Fcases_proof : Work.ZeroFreeTables.HB10_3_Fcases := by
  intro ε hε
  by_cases hbig : (6:ℝ)/7 ≤ ε
  · refine ⟨0, ?_⟩
    intro q _hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ _hmin hZ2 _h21 _h2i _hZ3 _h31 _h3i _h32 _h3ii _hdeg
    have h2nn : 0 ≤ lamOf q ρ₂ := Work.OffAxis.lamOf_nonneg_of_zeroMult hZ2.2.1
    have hle : (6:ℝ)/7 - ε ≤ 0 := by linarith
    exact le_trans hle (le_trans h2nn (le_max_left _ _))
  push Not at hbig
  obtain ⟨q1, h1⟩ := Fcases_complexRho ε hε
  obtain ⟨q2, h2⟩ := Fcases_realChiComplex ε hε
  obtain ⟨q3, h3⟩ := Fcases_realOneReal ε hε
  obtain ⟨q4, h4⟩ := Fcases_noPrincipal ε hε
  refine ⟨max (max q1 q2) (max q3 q4), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hmin hZ2 h21 h2i hZ3 h31 h3i h32 h3ii hdeg
  have hq1 : q1 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : q3 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hq4 : q4 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hR : Work.ZeroFreeTables.IsRectMin 1 χ₁ ρ₁ := isRectMin_one_of_isMin1WideAt hmin
  have hZ2' : Work.ZeroFreeTables.IsZAt 1 χ₂ ρ₂ := hZ2
  have hZ3' : Work.ZeroFreeTables.IsZAt 1 χ₃ ρ₃ := hZ3
  by_contra hcon
  push Not at hcon
  have h2lt : lamOf q ρ₂ < 6/7 - ε := lt_of_le_of_lt (le_max_left _ _) hcon
  have h3lt : lamOf q ρ₃ < 6/7 - ε := lt_of_le_of_lt (le_max_right _ _) hcon
  have h2le : lamOf q ρ₂ ≤ 6/7 - ε := le_of_lt h2lt
  have h3le : lamOf q ρ₃ ≤ 6/7 - ε := le_of_lt h3lt
  -- the local workhorse: an ordered pair `(ψ,υ) ≤ (ψ',υ')` of working-region zeros, both
  -- distinct from the pair `{χ₁^{±1}}`, cannot sit below `6/7 - ε`
  have step : ∀ (ψ ψ' : DirichletCharacter ℂ q) (υ υ' : ℂ),
      Work.LinnikContract.IsZ ψ υ → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      Work.LinnikContract.IsZ ψ' υ' → ψ' ≠ χ₁ → ψ' ≠ χ₁⁻¹ → ψ' ≠ ψ → ψ' ≠ ψ⁻¹ →
      lamOf q υ ≤ lamOf q υ' → lamOf q υ' ≤ 6/7 - ε →
      ¬ (χ₁ ^ 2 = 1 ∧ ψ ^ 2 = 1 ∧ ψ' ^ 2 = 1 ∧ χ₁ * ψ * ψ' = 1 ∧ ρ₁.im = 0) →
      6/7 - ε ≤ lamOf q υ' := by
    intro ψ ψ' υ υ' hZψ hψ1 hψi hZψ' hψ'1 hψ'i hψ'ψ hψ'ψi hlam hlam' hdeg'
    have hZψa : Work.ZeroFreeTables.IsZAt 1 ψ υ := hZψ
    have hZψ'a : Work.ZeroFreeTables.IsZAt 1 ψ' υ' := hZψ'
    have hl1ψ : lamOf q ρ₁ ≤ lamOf q υ :=
      hmin.2 ψ υ hZψ.1 hZψ.2.1 (by linarith [hZψ.2.2])
    by_cases him : ρ₁.im = 0
    · -- `ρ₁` real
      -- the normal form `χa ψa ψb = χ₀`: the second pair real or complex
      have prod1 : ∀ (χa ψa ψb : DirichletCharacter ℂ q) (υa υb : ℂ),
          Work.ZeroFreeTables.IsRectMin 1 χa ρ₁ →
          Work.ZeroFreeTables.IsZAt 1 ψa υa → ψa ≠ χa → ψa ≠ χa⁻¹ →
          Work.ZeroFreeTables.IsZAt 1 ψb υb → ψb ≠ χa → ψb ≠ χa⁻¹ →
          ψb ≠ ψa → ψb ≠ ψa⁻¹ →
          lamOf q υa ≤ lamOf q υb → lamOf q υb ≤ 6/7 - ε →
          χa * ψa * ψb = 1 →
          ¬ (χa ^ 2 = 1 ∧ ψa ^ 2 = 1 ∧ ψb ^ 2 = 1) →
          6/7 - ε ≤ lamOf q υb := by
        intro χa ψa ψb υa υb hRa hZa hna1 hnai hZb hnb1 hnbi hnbna hnbni hlamab hlamab'
          hproda hndeg
        have hlab : lamOf q ρ₁ ≤ lamOf q υa :=
          hRa.2 ψa υa ⟨hZa.1, hZa.2.1, by linarith [hZa.2.2]⟩
        by_cases hsq : χa ^ 2 = 1
        · have hψane : ψa ^ 2 ≠ 1 := fun h =>
            hndeg ⟨hsq, h, (sq_eq_one_iff_of_mul hsq hproda).mp h⟩
          have hψbne : ψb ^ 2 ≠ 1 := fun h =>
            hndeg ⟨hsq, (sq_eq_one_iff_of_mul hsq hproda).mpr h, h⟩
          exact h3 q hq3 χa ψa ψb ρ₁ υa υb hRa him hsq hψane hψbne hZa hZb
            hna1 hnai hnb1 hnbi hnbna hnbni hlamab hlamab' hproda
        · exact h2 q hq2 χa ψa ψb ρ₁ υa υb hRa him hsq hZa hZb
            hna1 hnai hnb1 hnbi hnbna hnbni hlamab hlamab' hproda
      by_cases hcase : χ₁ * ψ * ψ' = 1 ∨ χ₁ * ψ = ψ' ∨ χ₁ * ψ' = ψ ∨ ψ * ψ' = χ₁
      · rcases hcase with h0 | h0 | h0 | h0
        · -- `χ₁ψψ' = 1`
          exact prod1 χ₁ ψ ψ' υ υ' hR hZψa hψ1 hψi hZψ'a hψ'1 hψ'i hψ'ψ hψ'ψi
            hlam hlam' h0 (fun h => hdeg' ⟨h.1, h.2.1, h.2.2, h0, him⟩)
        · -- `χ₁ψ = ψ'`: conjugate the third pair
          have hprod' : χ₁ * ψ * ψ'⁻¹ = 1 := by rw [h0, mul_inv_cancel]
          have hndeg : ¬ (χ₁ ^ 2 = 1 ∧ ψ ^ 2 = 1 ∧ (ψ'⁻¹) ^ 2 = 1) := by
            rintro ⟨h1, h2, h3⟩
            have h3' : ψ' ^ 2 = 1 := sq_eq_one_of_inv_sq h3
            have h4 : χ₁ * ψ * ψ' = 1 := by rw [h0, ← pow_two, h3']
            exact hdeg' ⟨h1, h2, h3', h4, him⟩
          have hres := prod1 χ₁ ψ ψ'⁻¹ υ (starRingEnd ℂ υ') hR hZψa hψ1 hψi
            (Work.OffAxis.IsZAt_inv_conj hZψ'a)
            (fun h => hψ'i (eq_inv_of_inv_eq h))
            (fun h => hψ'1 (eq_of_inv_eq_inv h))
            (fun h => hψ'ψi (eq_inv_of_inv_eq h))
            (fun h => hψ'ψ (eq_of_inv_eq_inv h))
            (by rw [Work.OffAxis.lamOf_star]; exact hlam)
            (by rw [Work.OffAxis.lamOf_star]; exact hlam') hprod' hndeg
          rwa [Work.OffAxis.lamOf_star] at hres
        · -- `χ₁ψ' = ψ`: conjugate the second pair
          have hprod' : χ₁ * ψ⁻¹ * ψ' = 1 := by
            have hk : χ₁ * ψ' * ψ⁻¹ = 1 := by rw [h0, mul_inv_cancel]
            rwa [show χ₁ * ψ' * ψ⁻¹ = χ₁ * ψ⁻¹ * ψ' by ac_rfl] at hk
          have hndeg : ¬ (χ₁ ^ 2 = 1 ∧ (ψ⁻¹) ^ 2 = 1 ∧ ψ' ^ 2 = 1) := by
            rintro ⟨h1, h2, h3⟩
            have h2' : ψ ^ 2 = 1 := sq_eq_one_of_inv_sq h2
            have h4 : χ₁ * ψ * ψ' = 1 := by
              have hk : χ₁ * ψ' = ψ := mul_inv_eq_one.mp (by
                rw [show χ₁ * ψ' * ψ⁻¹ = χ₁ * ψ⁻¹ * ψ' by ac_rfl]; exact hprod')
              rw [show χ₁ * ψ * ψ' = (χ₁ * ψ') * ψ by ac_rfl, hk, ← pow_two, h2']
            exact hdeg' ⟨h1, h2', h3, h4, him⟩
          exact prod1 χ₁ ψ⁻¹ ψ' (starRingEnd ℂ υ) υ' hR
            (Work.OffAxis.IsZAt_inv_conj hZψa)
            (fun h => hψi (eq_inv_of_inv_eq h))
            (fun h => hψ1 (eq_of_inv_eq_inv h))
            hZψ'a hψ'1 hψ'i hψ'ψi (fun h => hψ'ψ (by rwa [inv_inv] at h))
            (by rw [Work.OffAxis.lamOf_star]; exact hlam) hlam' hprod' hndeg
        · -- `ψψ' = χ₁`: conjugate the first pair
          have hRinv : Work.ZeroFreeTables.IsRectMin 1 χ₁⁻¹ ρ₁ :=
            Work.OffAxis.IsRectMin_inv hR him
          have hprod' : χ₁⁻¹ * ψ * ψ' = 1 := by rw [mul_assoc, h0, inv_mul_cancel]
          have hndeg : ¬ ((χ₁⁻¹) ^ 2 = 1 ∧ ψ ^ 2 = 1 ∧ ψ' ^ 2 = 1) := by
            rintro ⟨h1, h2, h3⟩
            have h1' : χ₁ ^ 2 = 1 := sq_eq_one_of_inv_sq h1
            have h4 : χ₁ * ψ * ψ' = 1 := by rw [mul_assoc, h0, ← pow_two, h1']
            exact hdeg' ⟨h1', h2, h3, h4, him⟩
          exact prod1 χ₁⁻¹ ψ ψ' υ υ' hRinv hZψa hψi (fun h => hψ1 (by rwa [inv_inv] at h))
            hZψ'a hψ'i (fun h => hψ'1 (by rwa [inv_inv] at h)) hψ'ψ hψ'ψi
            hlam hlam' hprod' hndeg
      · push Not at hcase
        -- no principal signed triple product: HB Lemma 10.1
        exact h4 q hq4 χ₁ ψ ψ' ρ₁ υ υ' hR hZψa hZψ'a hψ1 hψi hψ'1 hψ'i hψ'ψ hψ'ψi
          hlam (by linarith) hcase.1 hcase.2.1 hcase.2.2.1 hcase.2.2.2
    · -- `ρ₁` complex: HB Lemmas 10.1 and 10.2 together
      exact h1 q hq1 χ₁ ψ ψ' ρ₁ υ υ' hR him hZψa hZψ'a hψ1 hψi hψ'1 hψ'i hψ'ψ hψ'ψi
        hlam hlam'
  by_cases hord : lamOf q ρ₂ ≤ lamOf q ρ₃
  · have h := step χ₂ χ₃ ρ₂ ρ₃ hZ2 h21 h2i hZ3 h31 h3i h32 h3ii hord h3le hdeg
    linarith [h, h3lt]
  · push Not at hord
    have hdegSwap :
        ¬ (χ₁ ^ 2 = 1 ∧ χ₃ ^ 2 = 1 ∧ χ₂ ^ 2 = 1 ∧ χ₁ * χ₃ * χ₂ = 1 ∧ ρ₁.im = 0) :=
      fun h => hdeg ⟨h.1, h.2.2.1, h.2.1,
        by rw [show χ₁ * χ₂ * χ₃ = χ₁ * χ₃ * χ₂ by ac_rfl]; exact h.2.2.2.1, h.2.2.2.2⟩
    have h := step χ₃ χ₂ ρ₃ ρ₂ hZ3 h31 h3i hZ2 h21 h2i (fun hh => h32 hh.symm)
      (fun hh => h3ii (by rw [hh, inv_inv])) (le_of_lt hord) h2le hdegSwap
    linarith [h, h2lt]

end Work.ZeroFreeTables
