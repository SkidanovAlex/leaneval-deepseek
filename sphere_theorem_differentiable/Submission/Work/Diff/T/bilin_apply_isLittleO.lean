import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Asymptotics
open scoped Topology

namespace Work.Diff.T

/-- Little-o transfer for a moving vector against a family of bilinear forms: if `Δ = o(t - t₀)`
(near `t₀`) and, for every `w`, `t ↦ B t w z` is continuous at `t₀`, then
`t ↦ B t (Δ t) z` is `o(t - t₀)`. Proof sketch: expand `Δ t = ∑ i, (b.repr (Δ t)) i • b i`; each
coordinate functional `v ↦ b.repr v i` is linear on the finite-dimensional space `V`, hence
continuous (indeed `LinearMap.toContinuousLinearMap`), so `t ↦ b.repr (Δ t) i` is `o(t - t₀)` via
`ContinuousLinearMap.isBigO_comp` and `IsBigO.trans_isLittleO`; each `t ↦ B t (b i) z` is
continuous at `t₀`, hence eventually bounded (`IsBigO` with the constant function `1`), and
`IsLittleO.mul_isBigO` plus `IsLittleO.sum` concludes. -/
theorem bilin_apply_isLittleO
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {t₀ : ℝ} {Δ : ℝ → V} {z : V}
    (hΔ : Asymptotics.IsLittleO (nhds t₀) Δ (fun t ↦ t - t₀))
    (hB : ∀ w : V, ContinuousAt (fun t ↦ B t w z) t₀) :
    Asymptotics.IsLittleO (nhds t₀) (fun t ↦ B t (Δ t) z) (fun t ↦ t - t₀) := by
  classical
  -- `V` is finite-dimensional, being spanned by the finite basis `b`.
  have hfin : FiniteDimensional ℝ V := Module.Finite.of_basis b
  -- Each coordinate functional is linear on the finite-dimensional space `V`, hence continuous.
  have hcoord : ∀ i : ι, IsLittleO (𝓝 t₀) (fun t => b.repr (Δ t) i) (fun t => t - t₀) := by
    intro i
    have h := (((b.coord i).toContinuousLinearMap).isBigO_comp Δ (𝓝 t₀)).trans_isLittleO hΔ
    simpa [Module.Basis.coord_apply] using h
  -- Each `t ↦ B t (b i) z` is continuous at `t₀`, hence eventually bounded.
  have hbdd : ∀ i : ι, IsBigO (𝓝 t₀) (fun t => B t (b i) z) (fun _ : ℝ => (1 : ℝ)) := by
    intro i
    refine (isBigO_one_iff (F := ℝ)).mpr ?_
    have h := ((continuous_abs.tendsto _).comp (hB (b i))).isBoundedUnder_le
    simpa [Real.norm_eq_abs, Function.comp_def] using h
  -- Hence each summand is `o(t - t₀)`.
  have hterm : ∀ i : ι,
      IsLittleO (𝓝 t₀) (fun t => b.repr (Δ t) i * (B t (b i) z)) (fun t => t - t₀) := by
    intro i
    have h := (hcoord i).mul_isBigO (hbdd i)
    simpa [mul_one] using h
  -- A finite sum of little-o functions is little-o.
  have hsum :
      IsLittleO (𝓝 t₀) (fun t => ∑ i, b.repr (Δ t) i * (B t (b i) z)) (fun t => t - t₀) := by
    have h := IsLittleO.sum (s := Finset.univ)
      (A := fun i t => b.repr (Δ t) i * (B t (b i) z)) (fun i _ => hterm i)
    have heq : (∑ i, (fun t => b.repr (Δ t) i * (B t (b i) z))) =
        fun t => ∑ i, b.repr (Δ t) i * (B t (b i) z) := by
      funext t
      simp [Finset.sum_apply]
    rwa [heq] at h
  -- `B t (Δ t) z` is (literally) the sum of its coordinate pieces.
  have hfun : (fun t => B t (Δ t) z) = fun t => ∑ i, b.repr (Δ t) i * (B t (b i) z) := by
    funext t
    conv_lhs => rw [← b.sum_repr (Δ t)]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  rw [hfun]
  exact hsum

end Work.Diff.T
