import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs
import Submission.Work.LinnikAreas.BGTZ.E.detJ_le

/-!
# The detector "shifted-line" bound `detJ_le_target`

This is L7a of `BGTZ/E/NOTES_E.md`: the arithmetic consequence of the contour bound
`E.detJ_le` (`‖detJ‖ ≤ KJ·A²q^{2θ}E²(1+|ρ.im|)^{2θ}·R(1+log R)^9·N^{1/2-ρ.re}`) in which the
two size hypotheses

* `R ≤ 2·CR·sieveX A q β₁`  and
* `max 1 ((KJ·CR)²)·detNE A q β₁ T R ≤ N`

are absorbed into the constant, giving `‖detJ‖ ≤ 2(1-β₁)N^{1-ρ.re}`.  This is the shape the
detector interface `DetectorPropE` consumes (`E.DetectorE_of_detJ`).

The only point that is not pure plumbing is that `R : ℕ` has *no* explicit lower bound in the
statement: it comes from `IsSieveWeight R θw`, which forces `R ≥ 1` (`θw 1 = 1` while any
`d > R` gets weight `0`).  With `R ≥ 1` the arithmetic `detJTargetArith` goes through.
-/

namespace Work.LinnikAreas.BGTZ.E

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- `IsSieveWeight R θw` forces `R ≥ 1`: the second structural condition applied at `d = 1`
(`1` is squarefree, so the disjunction reduces to `R < 1`) gives `θw 1 = 0`, contradicting
`θw 1 = 1`. -/
private lemma one_le_of_isSieveWeight {R : ℕ} {θw : ℕ → ℝ}
    (h : Work.LinnikAreas.BGTZ.IsSieveWeight R θw) : 1 ≤ R := by
  by_contra hcon
  have hlt : R < 1 := by omega
  have h0 : θw 1 = 0 := h.2.1 1 (Or.inr hlt)
  have h1 : θw 1 = 1 := h.1
  rw [h0] at h1
  norm_num at h1

/-- **Pure-arithmetic core of the shifted-line estimate.**

Given the two size hypotheses `R ≤ 2·CR·A²q^{2θ}E²δ^{-2}` and
`(KJ·CR)²·A⁸q^{8θ}E⁸T^{4θ}δ^{-6}(1+log R)^18 ≤ N`, and the truncation `1+|γ| ≤ T`, the bound
`KJ·A²q^{2θ}E²(1+|γ|)^{2θ}·R(1+log R)^9 ≤ 2δ√N` holds.  (The proof is the squaring trick: the
right side is `2δ·√N = √(4δ²N)` and the hypotheses give exactly `(KJ·CR)²·D ≤ N` with
`(KJ·A²q^{2θ}E²(1+|γ|)^{2θ}R(1+log R)^9)² ≤ 4δ²·(KJ·CR)²·D`.) -/
theorem detJTargetArith {KJ CR A q E T R N δ γ θ : ℝ}
    (hKJ : 0 < KJ) (hCR : 1 ≤ CR) (hA : 1 ≤ A) (hq : 1 ≤ q) (hE : 1 ≤ E)
    (hδ : 0 < δ) (hθ : 0 < θ) (hN : 1 ≤ N) (hR1 : 1 ≤ R) (hγT : 1 + |γ| ≤ T)
    (hRle : R ≤ 2 * CR * (A ^ 2 * q ^ (2 * θ) * E ^ 2 * δ ^ (-2 : ℝ)))
    (hNge : (KJ * CR) ^ 2
              * (A ^ 8 * q ^ (8 * θ) * E ^ 8 * T ^ (4 * θ) * δ ^ (-6 : ℝ)
                  * (1 + Real.log R) ^ 18) ≤ N) :
    KJ * A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * (R * (1 + Real.log R) ^ 9)
      ≤ 2 * δ * Real.sqrt N := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : (0 : ℝ) < T := by linarith [abs_nonneg γ]
  have hlogR9 : (0 : ℝ) ≤ (1 + Real.log R) ^ 9 := by
    have : (0 : ℝ) ≤ 1 + Real.log R := by linarith [Real.log_nonneg hR1]
    positivity
  have h2θ : (0 : ℝ) ≤ 2 * θ := by linarith
  have hγT' : (1 + |γ|) ^ (2 * θ) ≤ T ^ (2 * θ) :=
    Real.rpow_le_rpow (by positivity) hγT h2θ
  have hδδ : δ * δ ^ (-3 : ℝ) = δ ^ (-2 : ℝ) := by
    have h : δ ^ (1 : ℝ) * δ ^ (-3 : ℝ) = δ ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hδ]; norm_num
    rwa [Real.rpow_one] at h
  have hqq : q ^ (2 * θ) * q ^ (2 * θ) = q ^ (4 * θ) := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  have hXB : A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * R
      ≤ 2 * CR * (A ^ 4 * q ^ (4 * θ) * E ^ 4 * T ^ (2 * θ) * δ ^ (-2 : ℝ)) := by
    have h1 : A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * R
        ≤ A ^ 2 * q ^ (2 * θ) * E ^ 2 * T ^ (2 * θ) * R := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hγT' (by positivity)
    have h2 : A ^ 2 * q ^ (2 * θ) * E ^ 2 * T ^ (2 * θ) * R
        ≤ A ^ 2 * q ^ (2 * θ) * E ^ 2 * T ^ (2 * θ)
            * (2 * CR * (A ^ 2 * q ^ (2 * θ) * E ^ 2 * δ ^ (-2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hRle (by positivity)
    have h3 : A ^ 2 * q ^ (2 * θ) * E ^ 2 * T ^ (2 * θ)
          * (2 * CR * (A ^ 2 * q ^ (2 * θ) * E ^ 2 * δ ^ (-2 : ℝ)))
        = 2 * CR * (A ^ 4 * q ^ (4 * θ) * E ^ 4 * T ^ (2 * θ) * δ ^ (-2 : ℝ)) := by
      rw [← hqq]; ring
    exact h1.trans (h2.trans (le_of_eq h3))
  set Z : ℝ := A ^ 4 * q ^ (4 * θ) * E ^ 4 * T ^ (2 * θ) * δ ^ (-3 : ℝ) * (1 + Real.log R) ^ 9
    with hZ
  set D : ℝ := A ^ 8 * q ^ (8 * θ) * E ^ 8 * T ^ (4 * θ) * δ ^ (-6 : ℝ) * (1 + Real.log R) ^ 18
    with hD
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg hq0.le _)) (by positivity)) (Real.rpow_nonneg hT0.le _))
      (Real.rpow_nonneg hδ.le _)) hlogR9
  have hZsq : Z ^ 2 = D := by
    rw [hZ, hD]
    simp only [mul_pow]
    rw [show (q ^ (4 * θ)) ^ 2 = q ^ (8 * θ) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; ring,
        show (T ^ (2 * θ)) ^ 2 = T ^ (4 * θ) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; congr 1; ring,
        show (δ ^ (-3 : ℝ)) ^ 2 = δ ^ (-6 : ℝ) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; ring]
    ring
  have hXZ : KJ * A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * (R * (1 + Real.log R) ^ 9)
      ≤ 2 * δ * KJ * CR * Z := by
    rw [hZ]
    calc KJ * A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * (R * (1 + Real.log R) ^ 9)
        = KJ * (A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * R)
            * (1 + Real.log R) ^ 9 := by
          ring
      _ ≤ KJ * (2 * CR * (A ^ 4 * q ^ (4 * θ) * E ^ 4 * T ^ (2 * θ) * δ ^ (-2 : ℝ)))
            * (1 + Real.log R) ^ 9 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXB hKJ.le) hlogR9
      _ = 2 * δ * KJ * CR
            * (A ^ 4 * q ^ (4 * θ) * E ^ 4 * T ^ (2 * θ) * δ ^ (-3 : ℝ)
                * (1 + Real.log R) ^ 9) := by
          rw [← hδδ]; ring
  have hKZ : KJ * CR * Z ≤ Real.sqrt N := by
    rw [Real.le_sqrt (mul_nonneg (mul_nonneg hKJ.le (by linarith)) hZ0) (by linarith)]
    rw [show (KJ * CR * Z) ^ 2 = (KJ * CR) ^ 2 * D from by rw [mul_pow, hZsq]]
    exact hNge
  calc KJ * A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * (R * (1 + Real.log R) ^ 9)
      ≤ 2 * δ * KJ * CR * Z := hXZ
    _ = 2 * δ * (KJ * CR * Z) := by ring
    _ ≤ 2 * δ * Real.sqrt N := mul_le_mul_of_nonneg_left hKZ (by linarith)

theorem detJ_le_target :
    ∃ KJ : ℝ, 0 < KJ ∧ ∀ (CR : ℝ), 1 ≤ CR → ∀ (q : ℕ) [NeZero q], 400000 < q →
      ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 →
      ∀ {A : ℝ}, 1 ≤ A → Work.LinnikAreas.BGTZ.HypA A Work.LinnikAreas.BGTZ.thA →
      ∀ {R : ℕ} {θw : ℕ → ℝ}, Work.LinnikAreas.BGTZ.IsSieveWeight R θw →
      (R : ℝ) ≤ 2 * CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ →
      ∀ (T : ℝ) {ρ : ℂ}, 3 / 4 ≤ ρ.re → ρ.re < 1 → 1 + |ρ.im| ≤ T →
      ∀ (N : ℕ), 1 ≤ N →
        max 1 ((KJ * CR) ^ 2) * Work.LinnikAreas.BGTZ.detNE A q β₁ T R ≤ (N : ℝ) →
        ‖Work.LinnikAreas.BGTZ.detJ χ₁ χ R θw N ρ‖ ≤ 2 * (1 - β₁) * (N : ℝ) ^ (1 - ρ.re) := by
  obtain ⟨KJ, hKJpos, hDetJ⟩ := detJ_le
  refine ⟨KJ, hKJpos, ?_⟩
  intro CR hCR q _ hq χ₁ χ hχ₁ hχ₁ne β₁ hβ₁lt A hA1 hA R θw hθw hRhi T ρ hρre34 hρlt hρimT
    N hN1 hNsize
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    have := one_le_of_isSieveWeight hθw
    exact_mod_cast this
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hδpos : 0 < 1 - β₁ := by linarith
  set E : ℝ := Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) with hEdef
  have hE1 : (1 : ℝ) ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
  have hEq : E ^ 2 = Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by
    rw [hEdef, ← Real.exp_nat_mul]
    norm_num
  have hEq8 : E ^ 8 = Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by
    rw [hEdef, ← Real.exp_nat_mul]
    norm_num
  have hRle : (R : ℝ) ≤ 2 * CR * (A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA) * E ^ 2
      * (1 - β₁) ^ (-2 : ℝ)) := by
    rw [Work.LinnikAreas.BGTZ.sieveX] at hRhi
    calc (R : ℝ) ≤ 2 * CR * (A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)) := hRhi
      _ = 2 * CR * (A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA) * E ^ 2
            * (1 - β₁) ^ (-2 : ℝ)) := by rw [← hEq]
  have hNge : (KJ * CR) ^ 2 * (A ^ 8 * (q : ℝ) ^ (8 * Work.LinnikAreas.BGTZ.thA) * E ^ 8
      * T ^ (4 * Work.LinnikAreas.BGTZ.thA) * (1 - β₁) ^ (-6 : ℝ)
      * (1 + Real.log (R : ℝ)) ^ 18) ≤ (N : ℝ) := by
    rw [Work.LinnikAreas.BGTZ.detNE] at hNsize
    rw [← hEq8] at hNsize
    refine le_trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((KJ * CR) ^ 2)) ?_) hNsize
    have h1 : (0 : ℝ) ≤ A ^ 8 := by positivity
    have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (8 * Work.LinnikAreas.BGTZ.thA) :=
      Real.rpow_nonneg (by positivity) _
    have h3 : (0 : ℝ) ≤ E ^ 8 := by rw [hEdef]; positivity
    have h4 : (0 : ℝ) ≤ T ^ (4 * Work.LinnikAreas.BGTZ.thA) :=
      Real.rpow_nonneg (by linarith [abs_nonneg ρ.im]) _
    have h5 : (0 : ℝ) ≤ (1 - β₁) ^ (-6 : ℝ) := Real.rpow_nonneg (by linarith) _
    have h6 : (0 : ℝ) ≤ (1 + Real.log (R : ℝ)) ^ 18 :=
      pow_nonneg (by linarith [Real.log_nonneg hR1]) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5) h6
  have harith := detJTargetArith (KJ := KJ) (CR := CR) (A := A) (q := (q : ℝ)) (E := E) (T := T)
    (R := (R : ℝ)) (N := (N : ℝ)) (δ := 1 - β₁) (γ := ρ.im) (θ := Work.LinnikAreas.BGTZ.thA)
    hKJpos hCR hA1 hq1 hE1 hδpos (by norm_num [Work.LinnikAreas.BGTZ.thA]) hN1R hR1 hρimT hRle hNge
  have harith' : KJ * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
        * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
        * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
        * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9)
      ≤ 2 * (1 - β₁) * Real.sqrt (N : ℝ) := by
    rw [← hEq]
    exact harith
  have hdetJ := hDetJ q hq χ₁ χ hχ₁ hχ₁ne hA1 hA hθw hρre34 hρlt (N := N) hN1
  have hsplit : Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 2 - ρ.re) = (N : ℝ) ^ (1 - ρ.re) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0 : ℝ) < (N : ℝ))]
    congr 1
    ring
  calc ‖Work.LinnikAreas.BGTZ.detJ χ₁ χ R θw N ρ‖
      ≤ KJ * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1 / 2 - ρ.re) := hdetJ
    _ ≤ (2 * (1 - β₁) * Real.sqrt (N : ℝ)) * (N : ℝ) ^ (1 / 2 - ρ.re) :=
        mul_le_mul_of_nonneg_right harith' (Real.rpow_nonneg (by positivity) _)
    _ = 2 * (1 - β₁) * (N : ℝ) ^ (1 - ρ.re) := by rw [mul_assoc, hsplit]

end Work.LinnikAreas.BGTZ.E
