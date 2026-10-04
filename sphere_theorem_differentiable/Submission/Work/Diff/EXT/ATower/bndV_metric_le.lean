import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Changing the metric in a `BndV` bound

`Work.Diff.EXT.ConnCov.AMB.BndV` bounds the value of a vector-valued tensor `Θ` (in `G t`-norm) by
`C` times a product of `(1 + √⟨·,·⟩)`-factors, again in the `G t`-metric.

This file transfers such a bound from the metric `G t` to the *background* metric `G 0` under the
hypothesis that `G s` and `G 0` are comparable with factor `exp (2 * (dim E * C₀) * s)` on
`[0, T)`.  Since the bound is stated with *square roots*, the factor that appears is the square root
of the comparison factor, i.e. `exp ((dim E * C₀) * s)`; on `[T/2, T)` this is at most
`exp (2 * (dim E * C₀) * T / 2)`, and it is needed once for `Θ` and once for each of the `c + 2`
slots, which is exactly the constant of the statement.

The mathematics is elementary; the content of the file is the bookkeeping of the `√`-inequalities.
-/

set_option linter.unusedSectionVars false

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- From a comparison `g'.inner x u u ≤ K * g.inner x u u` of the quadratic forms with `K ≥ 0`,
the square roots compare as `√⟨u,u⟩_{g'} ≤ √K · √⟨u,u⟩_{g}`. -/
private theorem sqrt_inner_le_of_inner_le_bml {g g' : Submission.Diff.SMet I M} {x : M} {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ u : TangentSpace I x, g'.inner x u u ≤ K * g.inner x u u)
    (u : TangentSpace I x) :
    Real.sqrt (g'.inner x u u) ≤ Real.sqrt K * Real.sqrt (g.inner x u u) := by
  rw [← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt (h u)

/-- `1 + a ≤ K * (1 + b)` from `a ≤ K * b` and `1 ≤ K`. -/
private theorem one_add_sqrt_le_of_sqrt_le_bml {a b K : ℝ} (hK : 1 ≤ K) (h : a ≤ K * b) :
    1 + a ≤ K * (1 + b) := by
  calc 1 + a ≤ 1 + K * b := by linarith
    _ ≤ K + K * b := by linarith
    _ = K * (1 + b) := by ring

theorem bndV_metric_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {G : ℝ → Submission.Diff.SMet I M} {C₀ T : ℝ} (hT : 0 < T) (hC₀ : 0 ≤ C₀)
    (hmet : ∀ s ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G s).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * s) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * s) * (G s).inner x u u)
    {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T)
    {c : ℕ} (Θ : (Fin c → (Π y : M, TangentSpace I y)) → (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y))
    {C : ℝ} (hC : 0 ≤ C)
    (h : Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) G t Θ C) :
    Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t Θ
      (C * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2) ^ c
        * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2)
        * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2)
        * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2)) := by
  intro v X Z hv hX hZ x
  -- `t ∈ [0, T)` and the elementary bounds on the exponents
  have ht0 : t ∈ Set.Ico (0 : ℝ) T := ⟨by linarith [hT, ht.1], ht.2⟩
  have htng : 0 ≤ t := by linarith [hT, ht.1]
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
  have hnC : 0 ≤ (Module.finrank ℝ E : ℝ) * C₀ := mul_nonneg hn0 hC₀
  have hnCt : 0 ≤ ((Module.finrank ℝ E : ℝ) * C₀) * t := mul_nonneg hnC htng
  have hnexpT : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2 := by
    have h1 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) := by linarith
    have h2 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C₀) * T := mul_nonneg h1 hT.le
    linarith
  -- the comparison factor at time `T`
  set e : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2) with he
  have he1 : 1 ≤ e := by rw [he]; exact Real.one_le_exp hnexpT
  have he0 : 0 ≤ e := le_trans zero_le_one he1
  -- the comparison factor at time `t` (with its square root)
  have hE1_one : 1 ≤ Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t) :=
    Real.one_le_exp hnCt
  have hsqrtEt : Real.sqrt (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * t))
      = Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t) := by
    rw [← Real.exp_half]
    congr 1
    ring
  have hE1_le_e : Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t) ≤ e := by
    rw [he, Real.exp_le_exp]
    have hkey : ((Module.finrank ℝ E : ℝ) * C₀) * t ≤ ((Module.finrank ℝ E : ℝ) * C₀) * T :=
      mul_le_mul_of_nonneg_left ht.2.le hnC
    calc ((Module.finrank ℝ E : ℝ) * C₀) * t ≤ ((Module.finrank ℝ E : ℝ) * C₀) * T := hkey
      _ = 2 * ((Module.finrank ℝ E : ℝ) * C₀) * T / 2 := by ring
  -- the two-sided comparison of the quadratic forms at time `t`
  have hGt_le : ∀ u : TangentSpace I x,
      (G t).inner x u u
        ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * t) * (G 0).inner x u u :=
    fun u => (hmet t ht0 x u).1
  have hG0_le : ∀ u : TangentSpace I x,
      (G 0).inner x u u
        ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C₀) * t) * (G t).inner x u u :=
    fun u => (hmet t ht0 x u).2
  -- the square-root comparisons
  have hcmp_t : ∀ u : TangentSpace I x,
      Real.sqrt ((G t).inner x u u)
        ≤ Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t) * Real.sqrt ((G 0).inner x u u) := by
    intro u
    simpa only [hsqrtEt] using
      sqrt_inner_le_of_inner_le_bml (Real.exp_nonneg _) hGt_le u
  -- the `(1 + √·)` comparison with the *global* constant `e`
  have hf_t : ∀ u : TangentSpace I x,
      1 + Real.sqrt ((G t).inner x u u) ≤ e * (1 + Real.sqrt ((G 0).inner x u u)) := by
    intro u
    have h1 := one_add_sqrt_le_of_sqrt_le_bml hE1_one (hcmp_t u)
    calc 1 + Real.sqrt ((G t).inner x u u)
        ≤ Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t)
            * (1 + Real.sqrt ((G 0).inner x u u)) := h1
      _ ≤ e * (1 + Real.sqrt ((G 0).inner x u u)) :=
          mul_le_mul_of_nonneg_right hE1_le_e (by positivity)
  -- the abbreviations for the two products of factors
  let QΘ : ℝ := Real.sqrt ((G t).inner x (Θ v X Z x) (Θ v X Z x))
  let Qv : ℝ := ∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x)))
  let QX : ℝ := 1 + Real.sqrt ((G t).inner x (X x) (X x))
  let QZ : ℝ := 1 + Real.sqrt ((G t).inner x (Z x) (Z x))
  let Pv : ℝ := ∏ i : Fin c, (1 + Real.sqrt ((G 0).inner x (v i x) (v i x)))
  let PX : ℝ := 1 + Real.sqrt ((G 0).inner x (X x) (X x))
  let PZ : ℝ := 1 + Real.sqrt ((G 0).inner x (Z x) (Z x))
  -- the hypothesis, in the abbreviations
  have hval : QΘ ≤ C * Qv * QX * QZ := h v X Z hv hX hZ x
  have hQv0 : 0 ≤ Qv := by positivity
  have hQX0 : 0 ≤ QX := by positivity
  have hQZ0 : 0 ≤ QZ := by positivity
  have hPv0 : 0 ≤ Pv := by positivity
  have hPX0 : 0 ≤ PX := by positivity
  have hPZ0 : 0 ≤ PZ := by positivity
  -- the comparison of the two products of factors
  have hQv : Qv ≤ e ^ c * Pv := by
    have h1 := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i : Fin c => 1 + Real.sqrt ((G t).inner x (v i x) (v i x)))
      (g := fun i : Fin c => e * (1 + Real.sqrt ((G 0).inner x (v i x) (v i x))))
      (fun i _ => by positivity) (fun i _ => hf_t (v i x))
    have h2 : (∏ i : Fin c, e * (1 + Real.sqrt ((G 0).inner x (v i x) (v i x))))
        = e ^ c * ∏ i : Fin c, (1 + Real.sqrt ((G 0).inner x (v i x) (v i x))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rwa [h2] at h1
  have hQX : QX ≤ e * PX := by
    calc QX = 1 + Real.sqrt ((G t).inner x (X x) (X x)) := rfl
      _ ≤ e * (1 + Real.sqrt ((G 0).inner x (X x) (X x))) := hf_t (X x)
      _ = e * PX := rfl
  have hQZ : QZ ≤ e * PZ := by
    calc QZ = 1 + Real.sqrt ((G t).inner x (Z x) (Z x)) := rfl
      _ ≤ e * (1 + Real.sqrt ((G 0).inner x (Z x) (Z x))) := hf_t (Z x)
      _ = e * PZ := rfl
  -- the `Θ`-factor: the `G 0`-norm bounded by the `G t`-norm
  have hΘ : Real.sqrt ((G 0).inner x (Θ v X Z x) (Θ v X Z x)) ≤ e * QΘ := by
    have h1 : Real.sqrt ((G 0).inner x (Θ v X Z x) (Θ v X Z x))
        ≤ Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t)
          * Real.sqrt ((G t).inner x (Θ v X Z x) (Θ v X Z x)) := by
      simpa only [hsqrtEt] using
        sqrt_inner_le_of_inner_le_bml (Real.exp_nonneg _) hG0_le (Θ v X Z x)
    calc Real.sqrt ((G 0).inner x (Θ v X Z x) (Θ v X Z x))
        ≤ Real.exp (((Module.finrank ℝ E : ℝ) * C₀) * t)
            * Real.sqrt ((G t).inner x (Θ v X Z x) (Θ v X Z x)) := h1
      _ ≤ e * QΘ := mul_le_mul_of_nonneg_right hE1_le_e (Real.sqrt_nonneg _)
  -- the middle step
  have hmid : C * Qv * QX * QZ ≤ C * (e ^ c * Pv) * (e * PX) * (e * PZ) := by
    have h1 : C * Qv ≤ C * (e ^ c * Pv) := mul_le_mul_of_nonneg_left hQv hC
    have h2 : (C * Qv) * QX ≤ (C * (e ^ c * Pv)) * (e * PX) :=
      mul_le_mul h1 hQX hQX0 (mul_nonneg hC (mul_nonneg (pow_nonneg he0 c) hPv0))
    have h3 : ((C * Qv) * QX) * QZ ≤ ((C * (e ^ c * Pv)) * (e * PX)) * (e * PZ) :=
      mul_le_mul h2 hQZ hQZ0
        (mul_nonneg (mul_nonneg hC (mul_nonneg (pow_nonneg he0 c) hPv0))
          (mul_nonneg he0 hPX0))
    exact h3
  have key : Real.sqrt ((G 0).inner x (Θ v X Z x) (Θ v X Z x))
      ≤ C * e ^ c * e * e * e * Pv * PX * PZ := by
    calc Real.sqrt ((G 0).inner x (Θ v X Z x) (Θ v X Z x))
        ≤ e * QΘ := hΘ
      _ ≤ e * (C * Qv * QX * QZ) := mul_le_mul_of_nonneg_left hval he0
      _ ≤ e * (C * (e ^ c * Pv) * (e * PX) * (e * PZ)) := mul_le_mul_of_nonneg_left hmid he0
      _ = C * e ^ c * e * e * e * Pv * PX * PZ := by ring
  exact key

end Work.Diff.EXT.ATower
