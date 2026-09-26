import Mathlib

/-!
# Trigonometric sums with integer frequencies

A `TrigFun E` is a *canonical* finite trigonometric sum with integer frequencies,
`t ↦ Σ_k (cos (k t)) • c_k + (sin (k t)) • d_k` (`k : ℤ`, coefficients in an `ℝ`-module `E`).
The coefficients are stored as finitely supported functions `ℤ →₀ E`, so that the operations
below (addition, differentiation, and the *primitive*, i.e. the termwise antiderivative with the
constant part moved into the frequency-`0` coefficient) are defined on the coefficients and hence
compute.  This is the model in which a `C¹` periodic curve is `C¹`-approximated by an analytic
periodic curve (`Work.Drive.exists_analytic_periodic_close`).

Main items:
* `TrigFun.toFun` — evaluation;
* `TrigFun.add`, `TrigFun.constTrig`, `TrigFun.smulVec`, `TrigFun.mulComplex`, `TrigFun.reTrig`;
* `TrigFun.prim` — the primitive, with `TrigFun.prim_toFun_zero` and `TrigFun.hasDerivAt_prim_toFun`
  (in `Submission.Work.Drive.trigFunCalculus`);
* `TrigFun.contDiff_toFun`, `TrigFun.periodic_toFun` (analyticity and periodicity of `toFun`).
-/

namespace Work.Drive

open scoped Real

noncomputable section

/-- A finite trigonometric sum with integer frequencies, in coefficient form:
`toFun P t = Σ_k cos (k t) • P.c k + sin (k t) • P.d k`. -/
@[ext]
structure TrigFun (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  c : ℤ →₀ E
  d : ℤ →₀ E

namespace TrigFun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of a trigonometric sum. -/
noncomputable def toFun (P : TrigFun E) (t : ℝ) : E :=
  P.c.sum (fun k v => Real.cos ((k : ℝ) * t) • v) +
    P.d.sum (fun k v => Real.sin ((k : ℝ) * t) • v)

instance : Zero (TrigFun E) := ⟨⟨0, 0⟩⟩
instance : Add (TrigFun E) := ⟨fun P Q => ⟨P.c + Q.c, P.d + Q.d⟩⟩
instance : Neg (TrigFun E) := ⟨fun P => ⟨-P.c, -P.d⟩⟩
instance : Sub (TrigFun E) := ⟨fun P Q => ⟨P.c - Q.c, P.d - Q.d⟩⟩
instance : SMul ℝ (TrigFun E) := ⟨fun a P => ⟨a • P.c, a • P.d⟩⟩

@[simp] lemma c_zero : (0 : TrigFun E).c = 0 := rfl
@[simp] lemma d_zero : (0 : TrigFun E).d = 0 := rfl
@[simp] lemma c_add (P Q : TrigFun E) : (P + Q).c = P.c + Q.c := rfl
@[simp] lemma d_add (P Q : TrigFun E) : (P + Q).d = P.d + Q.d := rfl
@[simp] lemma c_neg (P : TrigFun E) : (-P).c = -P.c := rfl
@[simp] lemma d_neg (P : TrigFun E) : (-P).d = -P.d := rfl
@[simp] lemma c_sub (P Q : TrigFun E) : (P - Q).c = P.c - Q.c := rfl
@[simp] lemma d_sub (P Q : TrigFun E) : (P - Q).d = P.d - Q.d := rfl
@[simp] lemma c_smul (a : ℝ) (P : TrigFun E) : (a • P).c = a • P.c := rfl
@[simp] lemma d_smul (a : ℝ) (P : TrigFun E) : (a • P).d = a • P.d := rfl

lemma toFun_zero (t : ℝ) : (0 : TrigFun E).toFun t = 0 := by
  simp [toFun]

lemma toFun_add (P Q : TrigFun E) (t : ℝ) :
    (P + Q).toFun t = P.toFun t + Q.toFun t := by
  have h1 := Finsupp.sum_add_index (f := P.c) (g := Q.c)
    (h := fun k v => Real.cos ((k : ℝ) * t) • v)
    (by intro k hk; simp) (by intro k hk b₁ b₂; simp [smul_add])
  have h2 := Finsupp.sum_add_index (f := P.d) (g := Q.d)
    (h := fun k v => Real.sin ((k : ℝ) * t) • v)
    (by intro k hk; simp) (by intro k hk b₁ b₂; simp [smul_add])
  simp only [toFun, c_add, d_add]
  rw [h1, h2]
  abel

lemma toFun_neg (P : TrigFun E) (t : ℝ) : (-P).toFun t = -P.toFun t := by
  have h1 := Finsupp.sum_neg_index (g := P.c)
    (h := fun k v => Real.cos ((k : ℝ) * t) • v) (by intro k; simp)
  have h2 := Finsupp.sum_neg_index (g := P.d)
    (h := fun k v => Real.sin ((k : ℝ) * t) • v) (by intro k; simp)
  simp only [toFun, c_neg, d_neg]
  rw [h1, h2]
  simp only [smul_neg, Finsupp.sum, Finset.sum_neg_distrib]
  abel

lemma toFun_sub (P Q : TrigFun E) (t : ℝ) :
    (P - Q).toFun t = P.toFun t - Q.toFun t := by
  have h : (P - Q) = P + (-Q) := by ext a <;> exact sub_eq_add_neg _ _
  rw [h, toFun_add, toFun_neg]
  abel

/-- The trigonometric sum with the single nonvanishing coefficient `v` at frequency `0`. -/
def constTrig (v : E) : TrigFun E := ⟨Finsupp.single 0 v, 0⟩

@[simp] lemma c_constTrig (v : E) : (constTrig v).c = Finsupp.single 0 v := rfl
@[simp] lemma d_constTrig (v : E) : (constTrig v).d = 0 := rfl

lemma toFun_constTrig (v : E) (t : ℝ) : (constTrig v).toFun t = v := by
  rw [toFun]
  simp [constTrig]

/-- The real trigonometric sum `t ↦ cos (k t)`. -/
def cosFun (k : ℤ) : TrigFun ℝ := ⟨Finsupp.single k 1, 0⟩

/-- The real trigonometric sum `t ↦ sin (k t)`. -/
def sinFun (k : ℤ) : TrigFun ℝ := ⟨0, Finsupp.single k 1⟩

lemma toFun_cosFun (k : ℤ) (t : ℝ) : (cosFun k).toFun t = Real.cos ((k : ℝ) * t) := by
  rw [toFun]
  simp [cosFun]

lemma toFun_sinFun (k : ℤ) (t : ℝ) : (sinFun k).toFun t = Real.sin ((k : ℝ) * t) := by
  rw [toFun]
  simp [sinFun]

/-- The complex exponential `t ↦ exp (i k t)` (`k : ℤ`) as a trigonometric sum. -/
def expFun (k : ℤ) : TrigFun ℂ :=
  ⟨Finsupp.single k 1, Finsupp.single k Complex.I⟩

lemma toFun_expFun (k : ℤ) (t : ℝ) :
    (expFun k).toFun t = Complex.exp (((k : ℝ) * t) * Complex.I) := by
  rw [toFun]
  simp [expFun, Complex.exp_mul_I]

/-- Multiply a real trigonometric sum into a vector: `t ↦ (a.toFun t) • v`. -/
def smulVec (a : TrigFun ℝ) (v : E) : TrigFun E :=
  ⟨a.c.mapRange (fun r => r • v) (by simp), a.d.mapRange (fun r => r • v) (by simp)⟩

lemma toFun_smulVec (a : TrigFun ℝ) (v : E) (t : ℝ) :
    (smulVec a v).toFun t = (a.toFun t) • v := by
  have h1 := Finsupp.sum_mapRange_index (f := fun r : ℝ => r • v) (hf := by simp)
    (g := a.c) (h := fun k r => Real.cos ((k : ℝ) * t) • r) (by intro k; simp)
  have h2 := Finsupp.sum_mapRange_index (f := fun r : ℝ => r • v) (hf := by simp)
    (g := a.d) (h := fun k r => Real.sin ((k : ℝ) * t) • r) (by intro k; simp)
  simp only [toFun, smulVec]
  rw [h1, h2]
  simp only [Finsupp.sum, Finset.sum_smul, add_smul, smul_assoc]

/-- Multiplication of a complex trigonometric sum by a complex constant. -/
def mulComplex (P : TrigFun ℂ) (c : ℂ) : TrigFun ℂ :=
  ⟨P.c.mapRange (fun z => c * z) (by simp), P.d.mapRange (fun z => c * z) (by simp)⟩

lemma toFun_mulComplex (P : TrigFun ℂ) (c : ℂ) (t : ℝ) :
    (mulComplex P c).toFun t = c * P.toFun t := by
  have h1 := Finsupp.sum_mapRange_index (f := fun z : ℂ => c * z) (hf := by simp)
    (g := P.c) (h := fun k z => Real.cos ((k : ℝ) * t) • z) (by intro k; simp)
  have h2 := Finsupp.sum_mapRange_index (f := fun z : ℂ => c * z) (hf := by simp)
    (g := P.d) (h := fun k z => Real.sin ((k : ℝ) * t) • z) (by intro k; simp)
  simp only [toFun, mulComplex]
  rw [h1, h2]
  simp only [Finsupp.sum, Complex.real_smul, mul_add]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring

/-- The real part of a complex trigonometric sum. -/
def reTrig (P : TrigFun ℂ) : TrigFun ℝ :=
  ⟨P.c.mapRange Complex.re (by simp), P.d.mapRange Complex.re (by simp)⟩

lemma toFun_reTrig (P : TrigFun ℂ) (t : ℝ) : (reTrig P).toFun t = (P.toFun t).re := by
  have h1 := Finsupp.sum_mapRange_index (f := fun z : ℂ => z.re) (hf := by simp)
    (g := P.c) (h := fun k z => Real.cos ((k : ℝ) * t) • z) (by intro k; simp)
  have h2 := Finsupp.sum_mapRange_index (f := fun z : ℂ => z.re) (hf := by simp)
    (g := P.d) (h := fun k z => Real.sin ((k : ℝ) * t) • z) (by intro k; simp)
  simp only [toFun, reTrig]
  rw [h1, h2]
  simp only [Finsupp.sum, Complex.add_re, Complex.re_sum, Complex.smul_re, smul_eq_mul]

/-- The primitive of a trigonometric sum, normalised to vanish at `0`.
The frequency-`0` term of `P` (the constant term `P.c 0`) is *dropped*: the primitive is
normalised so that its derivative is `P.toFun` exactly when `P.c 0 = 0`
(`TrigFun.hasDerivAt_prim_toFun`), and the constant of integration created by the `sin` terms is
absorbed into the frequency-`0` coefficient of the derivative-free sum, so that
`(prim P).toFun 0 = 0` always (`TrigFun.prim_toFun_zero`). -/
noncomputable def prim (P : TrigFun E) : TrigFun E where
  c := Finsupp.onFinset (insert 0 (P.c.support ∪ P.d.support))
    (fun k => if k = 0 then P.d.sum (fun j v => ((j : ℝ))⁻¹ • v)
      else -(((k : ℝ))⁻¹ • P.d k))
    (by
      intro k hk
      by_contra hks
      have hk0 : k ≠ 0 := fun h => hks (Finset.mem_insert.mpr (Or.inl h))
      have hkd : P.d k = 0 := by
        by_contra h
        exact hks (Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finsupp.mem_support_iff.mpr h)))))
      exact hk (by simp [hk0, hkd]))
  d := Finsupp.onFinset (insert 0 (P.c.support ∪ P.d.support))
    (fun k => if k = 0 then 0 else ((k : ℝ))⁻¹ • P.c k)
    (by
      intro k hk
      by_contra hks
      have hk0 : k ≠ 0 := fun h => hks (Finset.mem_insert.mpr (Or.inl h))
      have hkc : P.c k = 0 := by
        by_contra h
        exact hks (Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr h)))))
      exact hk (by simp [hk0, hkc]))

end TrigFun

end

end Work.Drive
