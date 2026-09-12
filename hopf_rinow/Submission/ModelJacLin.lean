import Submission.Model
import Submission.ModelCore
import Submission.ModelJacobi
import Submission.ModelVarConv
import Mathlib

/-!
# Linearized solutions are unique and linear in the initial variation

Task: prove the two final theorems `linearized_unique` and `linearized_linear` (replace the
placeholder proofs).

## Setting

`V := odeField g` on `E × E`.  Along a fixed geodesic trajectory `z : ℝ → E × E`
(`HasDerivAt z (V (z t)) t` on `Ioo (-ε) ε`), consider the linearized equation

    J' t = (fderiv ℝ V (z t)) (J t)        (t ∈ Ioo (-ε) ε).

By `Submission.Model.linearized_exists`, for every initial `w` there is a solution `J` with
`J 0 = w`.

## Theorems

1. **Uniqueness**: two solutions of the linearized equation with the same value at `0` agree on
   the common interval.

2. **Linearity**: writing `J_w` for the (unique) solution with `J_w 0 = w`, the map
   `w ↦ J_w t` is linear for each fixed `t`; i.e. if `J₁`, `J₂` solve with initial data `w₁`,
   `w₂`, then `J₁ + J₂` solves with initial data `w₁ + w₂`, and `s • J₁` solves with initial
   data `s • w₁`.

## Proof route

* For (2) use the definitional linearity of the linearized ODE: if `J` solves with data `w`
  then `s • J` satisfies `(s•J)' = fderiv V (z t)(s•J s)` (linearity of the fderiv application)
  with `(s•J) 0 = s•w`; and the sum of two solutions is a solution.  Then (1) makes the map
  well-defined and linear.
* For (1) use uniqueness of ODE solutions with Lipschitz right-hand side.  The map
  `(t, X) ↦ (fderiv ℝ V (z t)) X` is linear in `X`, hence `LipschitzOnWith K` in `X` on any
  set, with `K := sup {‖fderiv ℝ V (z t)‖ | t ∈ Icc a b}` finite on a compact subinterval
  (use `isCompact_Icc` + continuity of `t ↦ ‖fderiv ℝ V (z t)‖` + `ContinuousOn.isBounded`,
  or simply pick a local Lipschitz constant from `ContDiffAt.exists_lipschitzOnWith` near the
  compact trajectory image).  Then invoke Mathlib's ODE uniqueness theorem, e.g.
  `ODE_solution_unique_of_mem_Icc_right` / `_left` from
  `Mathlib/Analysis/ODE/ExistUnique.lean`, or the Gronwall-based
  `dist_le_of_trajectories_ODE` in `Mathlib/Analysis/ODE/Gronwall.lean`.  Work on a compact
  interval `Icc (-T') T'` inside `Ioo (-ε) ε` (shrinking as needed) and then extend to the
  whole open interval by the standard open-closed argument (equality set is open and closed in
  the connected interval), or simply conclude equality on the symmetric interval produced by the
  existence theorem and state the results on that interval.

## Concrete statements to prove (keep the signatures)

    theorem linearized_unique (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
        {c vel : ℝ → E}
        (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
        (hv : ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
        {J₁ J₂ : ℝ → E × E} {w : E × E}
        (hJ₁ : J₁ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t)
        (hJ₂ : J₂ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt J₂ ((fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t) :
        ∀ t ∈ Ioo (-ε) ε, J₁ t = J₂ t

    theorem linearized_linear (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
        {c vel : ℝ → E}
        (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
        (hv : ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
        {J₁ J₂ : ℝ → E × E} {w₁ w₂ : E × E} (s : ℝ)
        (hJ₁ : J₁ 0 = w₁ ∧ ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t)
        (hJ₂ : J₂ 0 = w₂ ∧ ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt J₂ ((fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t) :
        (∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (fun u => J₁ u + J₂ u)
            ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t + J₂ t)) t) ∧
        (∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (fun u => s • J₁ u)
            ((fderiv ℝ (odeField g)) (c t, vel t) (s • J₁ t)) t) ∧
        (J₁ + J₂) 0 = w₁ + w₂ ∧ (fun u => s • J₁ u) 0 = s • w₁

Do NOT change the statements.  You may add helper lemmas.  No placeholders or axioms may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology NNReal
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


/-- The map `x ↦ fderiv ℝ (odeField g) x` is continuous (the geodesic field is `C¹`). -/
lemma fderiv_odeField_continuous (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) :
    Continuous (fderiv ℝ (odeField g)) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact (odeField_contDiffAt g hg hinv p.1 p.2).continuousAt_fderiv (by norm_num)

/-- Solutions of the linearized (Jacobi) equation with the same initial value agree. -/
theorem linearized_unique (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
    {c vel : ℝ → E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    {J₁ J₂ : ℝ → E × E} {w : E × E}
    (hJ₁ : J₁ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t)
    (hJ₂ : J₂ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J₂ ((fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t) :
    ∀ t ∈ Ioo (-ε) ε, J₁ t = J₂ t := by
  let z : ℝ → E × E := fun t => (c t, vel t)
  let L : ℝ → (E × E) →L[ℝ] (E × E) := fun t => fderiv ℝ (odeField g) (z t)
  let v : ℝ → (E × E) → (E × E) := fun t X => L t X
  have hz (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt z (odeField g (z t)) t := by
    dsimp [z]
    exact ((hc t ht).prodMk (hv t ht)).congr_deriv (by simp [odeField])
  have hLcontAt (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : ContinuousAt L t := by
    have hcomp : ContinuousAt (fun s : ℝ => fderiv ℝ (odeField g) (z s)) t :=
      (fderiv_odeField_continuous g hg hinv).continuousAt.comp (hz t ht).continuousAt
    simpa [L] using hcomp
  have hloc (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (-ε) ε) (heq : J₁ t₀ = J₂ t₀) : J₁ =ᶠ[𝓝 t₀] J₂ := by
    rcases Metric.continuousAt_iff.mp (hLcontAt t₀ ht₀) (1 : ℝ) zero_lt_one with ⟨δ, hδpos, hδ⟩
    let M : ℝ := ‖L t₀‖ + 1
    have hMpos : 0 ≤ M := by positivity
    let K : ℝ≥0 := ⟨M, hMpos⟩
    have hnorm (t : ℝ) (ht : dist t t₀ < δ) : ‖L t‖ ≤ M := by
      dsimp [M]
      have hlt : ‖L t - L t₀‖ < 1 := by
        simpa [dist_eq_norm] using hδ ht
      have hsub : ‖L t‖ ≤ ‖L t - L t₀‖ + ‖L t₀‖ := by
        calc
          ‖L t‖ = ‖(L t - L t₀) + L t₀‖ := by abel_nf
          _ ≤ ‖L t - L t₀‖ + ‖L t₀‖ := norm_add_le _ _
      linarith
    have hKle (t : ℝ) (ht : dist t t₀ < δ) : ‖L t‖₊ ≤ K := by
      dsimp [K]
      exact hnorm t ht
    have hve : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (univ : Set (E × E)) := by
      filter_upwards [ball_mem_nhds t₀ hδpos] with t ht
      have hKle' : ‖L t‖₊ ≤ K := hKle t (mem_ball.mp ht)
      have hlip : LipschitzWith K (fun X : E × E => L t X) := by
        simpa using (L t).lipschitz.weaken hKle'
      simpa [v] using hlip
    have hder₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt J₁ (v t (J₁ t)) t := by
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
      simpa [v, L, z] using (hJ₁.2 t ht)
    have hder₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt J₂ (v t (J₂ t)) t := by
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
      simpa [v, L, z] using (hJ₂.2 t ht)
    have hmem₁ : ∀ᶠ t in 𝓝 t₀, J₁ t ∈ (univ : Set (E × E)) := by
      filter_upwards with t
      trivial
    have hmem₂ : ∀ᶠ t in 𝓝 t₀, J₂ t ∈ (univ : Set (E × E)) := by
      filter_upwards with t
      trivial
    exact ODE_solution_unique_of_eventually (v := v) (s := fun _ : ℝ => (univ : Set (E × E)))
      (K := K) hve (hder₁.and hmem₁) (hder₂.and hmem₂) heq
  have hJ0 : J₁ 0 = J₂ 0 := by
    rw [hJ₁.1, hJ₂.1]
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  set u : Set ℝ := {t | J₁ t = J₂ t} ∩ Ioo (-ε) ε
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have ht₁ag : J₁ t₁ = J₂ t₁ := ht₁.1
    have ht₁I : t₁ ∈ Ioo (-ε) ε := ht₁.2
    have heq_t₁ : J₁ =ᶠ[𝓝 t₁] J₂ := hloc t₁ ht₁I ht₁ag
    apply (heq_t₁.and (Ioo_mem_nhds ht₁I.1 ht₁I.2)).mono
    intro t ht
    exact ⟨ht.1, ht.2⟩
  have hu_nonempty : (Ioo (-ε) ε ∩ u).Nonempty := by
    refine ⟨0, h0mem, ?_⟩
    exact ⟨hJ0, h0mem⟩
  have hu_closed : closure u ∩ Ioo (-ε) ε ⊆ u := by
    intro t ht
    have htI : t ∈ Ioo (-ε) ε := ht.2
    have htAg : J₁ t = J₂ t := by
      by_contra hne
      rcases t2_separation hne with ⟨U, V, hUo, hVo, hxU, hxV, hUV⟩
      have hpre1 : J₁ ⁻¹' U ∈ 𝓝 t :=
        (hJ₁.2 t htI).continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)
      have hpre2 : J₂ ⁻¹' V ∈ 𝓝 t :=
        (hJ₂.2 t htI).continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV)
      let W : Set ℝ := J₁ ⁻¹' U ∩ J₂ ⁻¹' V
      have hW : W ∈ 𝓝 t := Filter.inter_mem hpre1 hpre2
      have hUVempty : U ∩ V = ∅ := by
        simpa [Set.disjoint_iff] using hUV
      have hWu : W ∩ u = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        have hsW : s ∈ W := hs.1
        have hsu : s ∈ u := hs.2
        have hmemU : J₁ s ∈ U := hsW.1
        have hmemV : J₂ s ∈ V := hsW.2
        have hEq : J₁ s = J₂ s := hsu.1
        have hmemV' : J₁ s ∈ V := by simpa [hEq] using hmemV
        have hx : J₁ s ∈ U ∩ V := ⟨hmemU, hmemV'⟩
        rw [hUVempty] at hx
        simp at hx
      rcases (_root_.mem_nhds_iff.mp hW) with ⟨O, hOW, hOo, htO⟩
      have hclO : (O ∩ u).Nonempty := (_root_.mem_closure_iff.mp ht.1) O hOo htO
      have hOempty : O ∩ u = ∅ := by
        have hsubW : O ∩ u ⊆ W ∩ u := inter_subset_inter_left u hOW
        rw [hWu] at hsubW
        exact subset_empty_iff.mp hsubW
      rw [hOempty] at hclO
      exact not_nonempty_empty hclO
    exact ⟨htAg, htI⟩
  have hsub : Ioo (-ε) ε ⊆ u := by
    exact isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo (-ε) ε) (u := u)
      hu_open hu_nonempty hu_closed
  intro t' ht'
  exact (hsub ht').1

/-- The linearized equation is linear in the initial variation (sums and scalar multiples of
solutions are solutions). -/
theorem linearized_linear (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
    {c vel : ℝ → E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    {J₁ J₂ : ℝ → E × E} {w₁ w₂ : E × E} (s : ℝ)
    (hJ₁ : J₁ 0 = w₁ ∧ ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t)
    (hJ₂ : J₂ 0 = w₂ ∧ ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J₂ ((fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t) :
    (∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun u => J₁ u + J₂ u)
        ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t + J₂ t)) t) ∧
    (∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun u => s • J₁ u)
        ((fderiv ℝ (odeField g)) (c t, vel t) (s • J₁ t)) t) ∧
    (J₁ + J₂) 0 = w₁ + w₂ ∧ (fun u => s • J₁ u) 0 = s • w₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have hd1 : HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t := hJ₁.2 t ht
    have hd2 : HasDerivAt J₂ ((fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t := hJ₂.2 t ht
    have hdadd : HasDerivAt (fun u => J₁ u + J₂ u)
        ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t) +
          (fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t := hd1.add hd2
    refine hdadd.congr_deriv ?_
    let A : (E × E) →L[ℝ] (E × E) := fderiv ℝ (odeField g) (c t, vel t)
    change A (J₁ t) + A (J₂ t) = A (J₁ t + J₂ t)
    exact (map_add A (J₁ t) (J₂ t)).symm
  · intro t ht
    have hd1 : HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t := hJ₁.2 t ht
    have hds : HasDerivAt (fun u => s • J₁ u) (s • ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t))) t :=
      hd1.const_smul s
    refine hds.congr_deriv ?_
    let A : (E × E) →L[ℝ] (E × E) := fderiv ℝ (odeField g) (c t, vel t)
    change s • A (J₁ t) = A (s • J₁ t)
    exact (map_smul A s (J₁ t)).symm
  · simp [Pi.add_apply, hJ₁.1, hJ₂.1]
  · simp [hJ₁.1]
end

end Submission.Model
