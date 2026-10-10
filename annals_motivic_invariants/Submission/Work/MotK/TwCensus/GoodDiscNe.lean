import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TwCensus.GoodDiscDefs
import Submission.Work.MotK.TwCensus.GoodDiscCert
import Submission.Work.MotK.TwCensus.GoodDiscFactor
import Submission.Work.MotK.TwCensus.GoodDiscAlphaPow
import Submission.Work.MotK.TwCensus.GoodDiscLinIndep
import Submission.Work.MotK.TwCensus.GoodDiscZeta
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwCensus.GoodDiscNe`

`D.Good` forces `D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10 ≠ 0`.

Write `r = b/a`, so the discriminant is `a¹⁰(1 - 11r⁵ - r¹⁰)`.  If it vanished, the Klein quintic
`C_{a,b} = V(p₀,…,p₄)` would degenerate into five lines, the product of whose five defining
hyperplanes is the form `gdForm` of `GoodDiscDefs`; the certificate `GoodDiscCert` (`25 · gdForm`
lies in the ideal `(p₀,…,p₄)`) evaluated in the function field of `D.E` — extended so as to contain
a primitive fifth root `ζ` — gives `∏ⱼ (κ₀ + ζʲκ₃ + (α/5)ζ³ʲκ₄) = 0`, so one factor vanishes: a
non-trivial linear relation between the Klein coordinates, contradicting `D.Good.spans` together
with the linear independence of `1, x, y, x², xy`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.MotK.TwCensus

open WeierstrassCurve WeierstrassCurve.Affine

variable {A : Type*} [Field A]

/-- The Pfaffians in the coordinates `(a,b)` are `a²` times the normalised ones `(1, b/a)`. -/
theorem kleinP_scale (a b : A) (ha : a ≠ 0) (x : Fin 5 → A) (k : Fin 5) :
    Work.MotK.kleinP a b x k = a ^ 2 * Work.MotK.kleinP 1 (b / a) x k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero, Work.MotK.kleinP_one, Work.MotK.kleinP_two,
      Work.MotK.kleinP_three, Work.MotK.kleinP_four, Work.MotK.kleinP_zero',
      Work.MotK.kleinP_one', Work.MotK.kleinP_two', Work.MotK.kleinP_three',
      Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    field_simp <;> ring

/-- `gdForm25` is `25` times `gdForm`. -/
theorem gdForm25_eq_gdForm (r : A) (x : Fin 5 → A) (h25 : (25 : A) ≠ 0) :
    gdForm25 r x = 25 * gdForm r x := by
  simp only [gdForm25, gdForm]
  field_simp
  first | refl_ring1 | ring

/-- The certificate with general Klein parameters `(a,b)`. -/
theorem gdCertSumGen_eq (a b : A) (ha : a ≠ 0) (x : Fin 5 → A)
    (hr : (b / a) ^ 10 + 11 * (b / a) ^ 5 - 1 = 0) :
    25 * gdCertSumGen a b x = a ^ 2 * gdForm25 (b / a) x := by
  have h := GoodDiscCert (A := A) (b / a) hr x
  have h' : gdCertSumGen a b x = a ^ 2 * gdCertSum (b / a) x := by
    simp only [gdCertSumGen, gdCertSum, kleinP_scale a b ha x]
    first | refl_ring1 | ring
  rw [h', mul_left_comm, h]

/-- The degenerate quintic `gdForm r` is the product of the five linear forms. -/
theorem gdForm_eq_prod (h5 : (5 : A) ≠ 0) (r : A) (ζ : A) (hζ : IsPrimitiveRoot ζ 5)
    (hα : gdAlpha r ^ 5 = -3125 * r ^ 5) (x : Fin 5 → A) :
    gdForm r x
      = ∏ j : Fin 5, (x 0 + ζ ^ (j : ℕ) * x 3 + (gdAlpha r / 5) * ζ ^ (3 * (j : ℕ)) * x 4) := by
  have h25 : (25 : A) ≠ 0 := by
    have h : (25 : A) = 5 * 5 := by norm_num
    rw [h]; exact mul_ne_zero h5 h5
  have h3125 : (3125 : A) ≠ 0 := by
    have h : (3125 : A) = 5 ^ 5 := by norm_num
    rw [h]; exact pow_ne_zero 5 h5
  have hfac := GoodDiscFactor (gdAlpha r / 5) ζ hζ x
  rw [hfac]
  have h1 : (5 : A) * (gdAlpha r / 5) = gdAlpha r := by field_simp
  have h2 : (5 : A) * (gdAlpha r / 5) ^ 3 = gdAlpha r ^ 3 / 25 := by field_simp; ring
  have h3 : (gdAlpha r / 5) ^ 5 = -r ^ 5 := by
    rw [div_pow, hα, show (5 : A) ^ 5 = 3125 by norm_num]
    field_simp
  simp only [gdForm]
  rw [h1, h2, h3]
  first | refl_ring1 | ring

/-- **Auxiliary step.**  Over any extension field containing a primitive fifth root of unity,
`Good` forces the discriminant to be non-zero. -/
theorem goodDisc_extension (K : Type) [Field K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (L : Type) [Field L] [Algebra K L]
    (hζ : ∃ ζ : L, IsPrimitiveRoot ζ 5) :
    D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10 ≠ 0 := by
  intro hΔ
  have ha : D.a ≠ 0 := fun h => hD.ab_ne (by rw [h, zero_mul])
  have hb : D.b ≠ 0 := fun h => hD.ab_ne (by rw [h, mul_zero])
  have h5K : (5 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5
    · exact (CharP.ringChar_ne_one (R := K)) h1
    · exact hk h5
  have h5L : (5 : L) ≠ 0 := by
    intro h
    have hn : (algebraMap K L) (5 : K) = (5 : L) := map_ofNat _ 5
    have h0 : (algebraMap K L) (0 : K) = (0 : L) := map_zero _
    exact h5K ((algebraMap K L).injective (by rw [hn, h, h0]))
  let F := WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)
  letI hSemi : Semiring F := (inferInstance : Field F).toSemifield.toSemiring
  letI hOne : One F := hSemi.toOne
  letI hZero : Zero F := hSemi.toMulZeroClass.toZero
  have h5F : (5 : F) ≠ 0 := by
    intro h
    have hn : (algebraMap L F) (5 : L) = (5 : F) := map_ofNat _ 5
    have h0 : (algebraMap L F) (0 : L) = (0 : F) := map_zero _
    exact h5L ((algebraMap L F).injective (by rw [hn, h, h0]))
  let κ : Fin 5 → F := Work.MotV.kleinCoord D L
  let b : Fin 5 → F := Work.MotV.kleinBas D L
  -- linear independence of the basis `1, x, y, x², xy`
  have hli : LinearIndependent L b := by
    have h := GoodDiscLinIndep (A := L) (D.E.baseChange L)
    simpa only [b, Work.MotV.kleinBas] using h
  have hcb : ∀ i : Fin 5, κ i = ∑ m, (algebraMap K L (D.coord i m)) • b m := by
    intro i
    have h := Work.MotV.kleinCoord_eq_sum D L i
    simp only [κ, b, Algebra.smul_def] at h ⊢
    exact h
  obtain ⟨e, he⟩ := hD.spans
  have hbc : ∀ m : Fin 5, b m = ∑ i, (algebraMap K L (e m i)) • κ i := by
    intro m
    have h := he L m
    simp only [b, κ, Algebra.smul_def] at h ⊢
    exact h
  have hspan : Submodule.span L (Set.range κ) = Submodule.span L (Set.range b) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hcb i]
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      rw [hbc m]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hκli : LinearIndependent L κ := by
    rw [linearIndependent_iff_card_eq_finrank_span] at hli ⊢
    have hfr : Set.finrank L (Set.range κ) = Set.finrank L (Set.range b) := by
      simp only [Set.finrank]
      rw [hspan]
    rw [hfr]
    exact hli
  -- the parameters `r = b/a`
  let aL : L := algebraMap K L D.a
  let bL : L := algebraMap K L D.b
  let rL : L := bL / aL
  have h0KL : (algebraMap K L) (0 : K) = (0 : L) := map_zero _
  have haL : aL ≠ 0 := by
    intro h
    simp only [aL] at h
    exact ha ((algebraMap K L).injective (by rw [h, h0KL]))
  have hbL : bL ≠ 0 := by
    intro h
    simp only [bL] at h
    exact hb ((algebraMap K L).injective (by rw [h, h0KL]))
  have hrL : rL ^ 10 + 11 * rL ^ 5 - 1 = 0 := by
    have h := congrArg (algebraMap K L) hΔ
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero, aL, bL] at h
    have hmul : aL ^ 10 * (rL ^ 10 + 11 * rL ^ 5 - 1) = 0 := by
      simp only [rL]
      field_simp
      ring_nf
      linear_combination (norm := first | refl_ring1 | ring1) -h
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 10 haL)
  -- push everything into the function field
  let aF : F := algebraMap K F D.a
  let bF : F := algebraMap K F D.b
  have h0LF : (algebraMap L F) (0 : L) = (0 : F) := map_zero _
  have haF : aF ≠ 0 := by
    rw [show aF = algebraMap L F aL from (IsScalarTower.algebraMap_apply K L F D.a)]
    intro h
    exact haL ((algebraMap L F).injective (by rw [h, h0LF]))
  have hbFdiv : bF / aF = algebraMap L F rL := by
    simp only [bF, aF, rL, aL, bL, IsScalarTower.algebraMap_apply K L F D.b,
      IsScalarTower.algebraMap_apply K L F D.a, map_div₀]
  have hrF : (bF / aF) ^ 10 + 11 * (bF / aF) ^ 5 - 1 = 0 := by
    rw [hbFdiv]
    have h := congrArg (algebraMap L F) hrL
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] at h
    exact h
  -- the certificate evaluated at the Klein coordinates
  have hk : ∀ k : Fin 5, Work.MotK.kleinP aF bF κ k = 0 := by
    intro k
    have h := hD.klein_eq L k
    simpa only [aF, bF, κ] using h
  have hzsum : gdCertSumGen aF bF κ = 0 := by
    simp only [gdCertSumGen, hk, mul_zero, zero_mul, add_zero]
  have hcert := gdCertSumGen_eq aF bF haF κ hrF
  rw [hzsum, mul_zero] at hcert
  have hform25 : gdForm25 (bF / aF) κ = 0 :=
    (mul_eq_zero.mp hcert.symm).resolve_left (pow_ne_zero 2 haF)
  have h25F : (25 : F) ≠ 0 := by
    have h : (25 : F) = 5 * 5 := by norm_num
    rw [h]; exact mul_ne_zero h5F h5F
  have hgF : gdForm (bF / aF) κ = 0 := by
    have h := gdForm25_eq_gdForm (bF / aF) κ h25F
    rw [h] at hform25
    exact (mul_eq_zero.mp hform25).resolve_left h25F
  -- the factorisation into five linear forms
  obtain ⟨ζL, hζL⟩ := hζ
  let ζF : F := algebraMap L F ζL
  have hζF : IsPrimitiveRoot ζF 5 := hζL.map_of_injective (algebraMap L F).injective
  let BL : L := gdAlpha rL / 5
  have hB_eq : algebraMap L F BL = gdAlpha (bF / aF) / 5 := by
    have key : (algebraMap L F : L →+* F) (gdAlpha rL / 5)
        = gdAlpha ((algebraMap L F) rL) / 5 := by
      simp only [gdAlpha, map_div₀, map_neg, map_add, map_mul, map_pow, map_ofNat]
    simp only [BL]
    rw [hbFdiv]
    exact key
  have hα5 : gdAlpha (bF / aF) ^ 5 = -3125 * (bF / aF) ^ 5 := GoodDiscAlphaPow (bF / aF) hrF
  have hprod : (∏ j : Fin 5,
      (κ 0 + ζF ^ (j : ℕ) * κ 3 + algebraMap L F BL * ζF ^ (3 * (j : ℕ)) * κ 4)) = 0 := by
    rw [hB_eq]
    rw [← gdForm_eq_prod h5F (bF / aF) ζF hζF hα5 κ]
    exact hgF
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp (by simpa using hprod)
  -- the resulting non-trivial linear relation
  set μ : Fin 5 → L := ![1, 0, 0, ζL ^ (j : ℕ), BL * ζL ^ (3 * (j : ℕ))] with hμ
  have hμsum : ∑ i : Fin 5, μ i • κ i = 0 := by
    have hexp : (∑ i : Fin 5, μ i • κ i)
        = μ 0 • κ 0 + (μ 1 • κ 1 + (μ 2 • κ 2 + (μ 3 • κ 3 + μ 4 • κ 4))) := by
      simp [Fin.sum_univ_succ]
    rw [hexp]
    have hm0 : μ 0 = 1 := rfl
    have hm1 : μ 1 = 0 := rfl
    have hm2 : μ 2 = 0 := rfl
    have hm3 : μ 3 = ζL ^ (j : ℕ) := rfl
    have hm4 : μ 4 = BL * ζL ^ (3 * (j : ℕ)) := rfl
    rw [hm0, hm1, hm2, hm3, hm4]
    simpa only [one_smul, zero_smul, zero_add, add_zero, add_assoc, Algebra.smul_def,
      map_pow, map_mul, map_one, map_zero, one_mul, zero_mul, ζF] using hj
  have hμne : μ ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    rw [hμ] at h0
    simp at h0
  exact hμne (funext fun i => (Fintype.linearIndependent_iff.mp hκli μ hμsum i))

/-- **The discriminant of a `Good` Klein datum does not vanish.** -/
theorem GoodDiscNe (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) :
    D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10 ≠ 0 :=
  goodDisc_extension K hk D hD (AlgebraicClosure K) (GoodDiscZeta K hk)

end Work.MotK.TwCensus
