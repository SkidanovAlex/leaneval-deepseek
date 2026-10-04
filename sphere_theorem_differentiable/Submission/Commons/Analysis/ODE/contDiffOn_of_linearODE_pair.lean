import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Submission.Commons.Analysis.ODE.contDiffOn_of_hasDerivAt_of_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open scoped ContDiff
open Set Filter

/-- **Smoothness of solutions of a linear first-order ODE system.**

If `A` and `B` are `C^∞` on `Icc a b` and `(y, z)` solves the linear system
`y' = z - A(t) y`, `z' = -A(t) z - B(t) y` on `Icc a b` (with `y`, `z` continuous), then `y` and `z`
are `C^∞` on `Icc a b`.

This is the specialization to a linear system of
`Commons.Analysis.ODE.contDiffOn_of_hasDerivAt_of_contDiffOn` (the non-autonomous bootstrap), applied
to the pair `t ↦ (y t, z t)`: the vector field `G t (p₁, p₂) = (p₂ - A t p₁, -(A t p₂) - B t p₁)` is
`C^∞` in `(t, p)` because it is linear in `p` and `A`, `B` are `C^∞` in `t`. -/
theorem contDiffOn_of_linearODE_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A B : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a < b)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Icc a b))
    (hB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B (Set.Icc a b))
    {y z : ℝ → E}
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (z t - A t (y t)) t)
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (-(A t (z t)) - B t (y t)) t)
    (hyc : ContinuousOn y (Set.Icc a b)) (hzc : ContinuousOn z (Set.Icc a b)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y (Set.Icc a b) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z (Set.Icc a b) := by
  -- The state space is `E × E`, and we package `(y, z)` as a single curve.
  let G : ℝ → E × E → E × E := fun t p => (p.2 - A t p.1, -(A t p.2) - B t p.1)
  let w : ℝ → E × E := fun t => (y t, z t)
  set U : Set (ℝ × (E × E)) := Set.Icc a b ×ˢ (Set.univ : Set (E × E)) with hU
  have hUmem : ∀ t ∈ Set.uIcc a b, (t, w t) ∈ U := by
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    exact ⟨ht, trivial⟩
  have hw_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt w (G t (w t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    exact (hy t ht).prodMk (hz t ht)
  have hw_cont : ContinuousOn w (Set.uIcc a b) := by
    have h1 : ContinuousOn y (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab.le]
    have h2 : ContinuousOn z (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab.le]
    exact h1.prodMk h2
  -- `G` is smooth on `Icc a b ×ˢ univ`, being linear in the state and smooth in `t`.
  have hG_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (E × E) => G q.1 q.2) U := by
    have hmaps : MapsTo (fun q : ℝ × (E × E) => q.1) U (Set.Icc a b) :=
      fun q hq => hq.1
    have hAq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => A q.1) U := by
      have h := hA.comp contDiffOn_fst hmaps
      simpa only [Function.comp_def] using h
    have hBq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => B q.1) U := by
      have h := hB.comp contDiffOn_fst hmaps
      simpa only [Function.comp_def] using h
    have hq1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => q.2.1) U :=
      contDiffOn_snd.fst
    have hq2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => q.2.2) U :=
      contDiffOn_snd.snd
    have hA1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => A q.1 q.2.1) U :=
      hAq.clm_apply hq1
    have hA2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => A q.1 q.2.2) U :=
      hAq.clm_apply hq2
    have hB1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (E × E) => B q.1 q.2.1) U :=
      hBq.clm_apply hq1
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (E × E) => q.2.2 - A q.1 q.2.1) U := hq2.sub hA1
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (E × E) => -(A q.1 q.2.2) - B q.1 q.2.1) U := hA2.neg.sub hB1
    exact h1.prodMk h2
  -- Bootstrap: `w` is `C^n` for every `n`, hence `C^∞`.
  have hw_smooth : ∀ n : ℕ, ContDiffOn ℝ n w (Set.uIcc a b) := by
    intro n
    have hGn : ContDiffOn ℝ n (fun q : ℝ × (E × E) => G q.1 q.2) U :=
      (contDiffOn_infty.mp hG_smooth) n
    exact contDiffOn_of_hasDerivAt_of_contDiffOn hGn hUmem hw_deriv hw_cont
  have hwy : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => (w t).1) (Set.Icc a b) := by
    rw [contDiffOn_infty]
    intro n
    have h := (hw_smooth n).fst
    rwa [Set.uIcc_of_le hab.le] at h
  have hwz : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => (w t).2) (Set.Icc a b) := by
    rw [contDiffOn_infty]
    intro n
    have h := (hw_smooth n).snd
    rwa [Set.uIcc_of_le hab.le] at h
  exact ⟨hwy.congr (fun t _ => rfl), hwz.congr (fun t _ => rfl)⟩

end Commons.Analysis.ODE