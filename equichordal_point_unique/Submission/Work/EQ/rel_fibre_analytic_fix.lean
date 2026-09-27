import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.exists_analyticAt_sq_eq
import Submission.Work.EQ.par_unit_solutions
import Submission.Work.EQ.eqRelC_smul_inv_subO1

/-!
# The two analytic branches of the equichordal relation over an analytic family

For an analytic family `Q : ℂ → ℂ²` of second arguments of the (complexified) equichordal
relation `EqRelC a · ·`, with `Q u₀ - O₁` non-isotropic (`(Q u₀)₁ + a/2)² + (Q u₀)₂² ≠ 0`),
there are locally exactly two analytic families `P₁, P₂` with `EqRelC a (Pᵢ u) (Q u)`, and they
are distinct at `u₀`.  This is the "regular fibre" fact used downstream (`H0_invParam_ge`,
`H0_path_limit`): the fibre of the relation over a regular value has two analytic local branches.

Writing `Z u = subO1 a (Q u) = ((Q u)₁ + a/2, (Q u)₂)`, a local analytic square root `ρ` of
`bsq ∘ Z = (·)₁² + (·)₂²` (which exists near `u₀` because that function does not vanish there,
`exists_analyticAt_sq_eq`) linearises the fibre: the two branches are
`ρ⁻¹ • Z - Q` and `-(ρ⁻¹ • Z) - Q`.  Both are analytic, both satisfy the relation
(`eqRelC_smul_inv_subO1`) and any solution equals one of them (`par_unit_solutions`).

Note the local re-branching matters: `invBranch a s ∘ Q` is *not* analytic in general, since the
principal square root of `bsq (subO1 a (Q u))` is discontinuous when the value crosses the
negative real axis.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

theorem rel_fibre_analytic_fix {a : ℝ} {Q : ℂ → ℂ × ℂ} {u₀ : ℂ}
    (hQ : AnalyticAt ℂ Q u₀)
    (hne : ((Q u₀).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (Q u₀).2 ^ 2 ≠ 0) :
    ∃ P₁ P₂ : ℂ → ℂ × ℂ, AnalyticAt ℂ P₁ u₀ ∧ AnalyticAt ℂ P₂ u₀ ∧ P₁ u₀ ≠ P₂ u₀ ∧
      Filter.Eventually (fun u => EqRelC a (P₁ u) (Q u) ∧ EqRelC a (P₂ u) (Q u)) (nhds u₀) ∧
      Filter.Eventually (fun u => ∀ P : ℂ × ℂ, EqRelC a P (Q u) → P = P₁ u ∨ P = P₂ u)
        (nhds u₀) := by
  -- `w u = bsq (subO1 a (Q u))` is the (nonvanishing) radicand of the fibre.
  set w : ℂ → ℂ := fun u => ((Q u).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (Q u).2 ^ 2 with hw_eq
  have hw0 : w u₀ ≠ 0 := by rw [hw_eq]; exact hne
  have hw : AnalyticAt ℂ w u₀ := by
    rw [hw_eq]
    have h1 : AnalyticAt ℂ (fun u => (Q u).1) u₀ :=
      (analyticAt_fst (𝕜 := ℂ) (p := Q u₀)).comp hQ
    have h2 : AnalyticAt ℂ (fun u => (Q u).2) u₀ :=
      (analyticAt_snd (𝕜 := ℂ) (p := Q u₀)).comp hQ
    exact ((h1.add analyticAt_const).pow 2).add (h2.pow 2)
  -- A local analytic square root `ρ` of `w`, nonvanishing at `u₀`.
  obtain ⟨ρ, hρan, hρne0, hρsq⟩ := exists_analyticAt_sq_eq hw hw0
  have hbsq_eq : ∀ u, bsq (subO1 a (Q u)) = w u := by
    intro u; rw [hw_eq]; simp [subO1, bsq]
  have hsub : AnalyticAt ℂ (fun u => subO1 a (Q u)) u₀ := by
    have h1 : AnalyticAt ℂ (fun u => (Q u).1) u₀ :=
      (analyticAt_fst (𝕜 := ℂ) (p := Q u₀)).comp hQ
    have h2 : AnalyticAt ℂ (fun u => (Q u).2) u₀ :=
      (analyticAt_snd (𝕜 := ℂ) (p := Q u₀)).comp hQ
    have hEq : (fun u => subO1 a (Q u)) =
        (fun u => ((Q u).1 + ((a / 2 : ℝ) : ℂ), (Q u).2)) := by
      funext u; rfl
    rw [hEq]
    exact (h1.add analyticAt_const).prod h2
  have hρne_ev : ∀ᶠ u in nhds u₀, ρ u ≠ 0 := hρan.continuousAt.eventually_ne hρne0
  -- The two branches.
  set P₁ : ℂ → ℂ × ℂ := fun u => (ρ u)⁻¹ • subO1 a (Q u) - Q u with hP₁
  set P₂ : ℂ → ℂ × ℂ := fun u => -((ρ u)⁻¹ • subO1 a (Q u)) - Q u with hP₂
  have hZne : subO1 a (Q u₀) ≠ 0 := by
    intro hZ
    exact hw0 (by rw [← hbsq_eq u₀, hZ]; simp [bsq])
  refine ⟨P₁, P₂, ?h1, ?h2, ?h3, ?h4, ?h5⟩
  · -- analyticity of `P₁`
    rw [hP₁]
    exact ((hρan.inv hρne0).smul hsub).sub hQ
  · -- analyticity of `P₂`
    rw [hP₂]
    exact (((hρan.inv hρne0).smul hsub).neg).sub hQ
  · -- distinctness at `u₀`
    intro hEq
    have hdiff : P₁ u₀ - P₂ u₀ = (2 * (ρ u₀)⁻¹) • subO1 a (Q u₀) := by
      rw [hP₁, hP₂]; ext <;> simp [smul_eq_mul] <;> ring
    have hcne : (2 * (ρ u₀)⁻¹) ≠ 0 := by simp [hρne0]
    have hz : (2 * (ρ u₀)⁻¹) • subO1 a (Q u₀) = 0 := by rw [← hdiff, hEq, sub_self]
    exact hZne ((smul_eq_zero.mp hz).resolve_left hcne)
  · -- both branches satisfy the relation
    filter_upwards [hρne_ev] with u hru
    have hρ : (ρ u) ^ 2 = bsq (subO1 a (Q u)) := (hρsq u).trans (hbsq_eq u).symm
    have := eqRelC_smul_inv_subO1 (a := a) (Q := Q u) (ρ := ρ u) hru hρ
    simpa only [hP₁, hP₂] using this
  · -- and any solution is one of them
    filter_upwards [hρne_ev] with u hru P hP
    have hρ : (ρ u) ^ 2 = bsq (subO1 a (Q u)) := (hρsq u).trans (hbsq_eq u).symm
    have hX : bsq (P + Q u) = 1 := ((eqRelC_iff_reverse P (Q u)).mp hP).1
    have hpar : par (P + Q u) (subO1 a (Q u)) := ((eqRelC_iff_reverse P (Q u)).mp hP).2
    rcases par_unit_solutions (Z := subO1 a (Q u)) (X := P + Q u) (ρ := ρ u) hru hρ hX hpar
      with h | h
    · left
      have : P = (ρ u)⁻¹ • subO1 a (Q u) - Q u := (eq_sub_iff_add_eq).mpr h
      simpa only [hP₁] using this
    · right
      have h' : P + Q u = -((ρ u)⁻¹ • subO1 a (Q u)) := by rw [h, neg_smul]
      have : P = -((ρ u)⁻¹ • subO1 a (Q u)) - Q u := (eq_sub_iff_add_eq).mpr h'
      simpa only [hP₂] using this

end Work.EQ
