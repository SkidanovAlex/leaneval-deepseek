import Mathlib
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.chartLev_contDiffOn
import Submission.Work.RPB.B5.collarChart_flat
import Submission.Work.RPB.B5.lagPt_negSqrt2_decomp
import Submission.Work.RPB.B5.lagData_per
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff
import Submission.Work.RPB.B5.jet_vanish
import Submission.Work.RPB.B5.lagData_tShift

/-!
# B5: smoothness of the assembled Lagrangian family at the junction `x = -√2`

The assembled family `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` is the collar
`collarPt Γc Ac τ (sig x) t` for `x ≤ -√2` and the chord chart `W τ t (rho τ x t)` for
`-√2 ≤ x`.  Near `x = -√2` the level `sig x = x²/2 - 1` is small and `rho` agrees with the
level inverse `ρh (sig ·)` on a two-sided neighbourhood (`LagData.hrhonearδ`), so

`ℓ τ (x,t) = W τ t (ρh τ t (sig x)) + (if sig x ≤ 0 then 0 else D τ t (sig x))`

where `D τ t σ = collarPt Γc Ac τ σ t - W τ t (ρh τ t σ)` is the *seam defect*: the chart
branch is `W τ t (ρh τ t (sig x))`, and on the collar side one adds back the difference between
the collar and the chart.  The collar's and the chart's `σ`-profiles have the same one-sided
jets of every order `≤ 8` at `σ = 0` (`LagData.σjet`, used here through
`Work.RPB.B5.collarChart_flat`), so `D` is flat at `σ = 0` and the truncation is `C⁸`.

The mathematical content is therefore a *flat truncation* statement
(`Work.RPB.B5.truncFlatAux` below), proved here from the general jet-vanishing theorem
`Work.RPB.B5.jet_vanish` of the team's library.

## Layout

* `iteratedDerivWithin_Ioi_eq_iteratedDeriv` : the one-sided derivative of a function smooth at
  `0` is the two-sided one.
* `iteratedFDerivWithin_fderivWithin_eq_zero` : currying of the jet vanishing.
* `truncFlatAux` : the flat truncation theorem (induction on the order).
* `lagData_smooth_at_negSqrt2` : the junction statement.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology
open Filter

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

universe u

/-! ## One-sided versus two-sided derivatives -/

/-- For a function of one real variable which is `C^n` at `0`, the one-sided iterated derivative
within `(0,∞)` at `0` is the ordinary iterated derivative. -/
theorem iteratedDerivWithin_Ioi_eq_iteratedDeriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) {f : ℝ → F} (hf : ContDiffAt ℝ n f 0) :
    iteratedDerivWithin n f (Set.Ioi (0 : ℝ)) 0 = iteratedDeriv n f 0 := by
  have h1 : Set.Ici (0 : ℝ) = insert 0 (Set.Ioi (0 : ℝ)) := Set.Ioi_insert.symm
  have h2 : iteratedDerivWithin n f (Set.Ioi (0 : ℝ)) 0
      = iteratedDerivWithin n f (Set.Ici (0 : ℝ)) 0 := by
    simp only [iteratedDerivWithin, h1, iteratedFDerivWithin_insert]
  rw [h2]
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hf (by simp)

/-! ## Flat truncation on a slab

The truncation `z ↦ if z.2 ≤ 0 then 0 else G z` of a function `G` which is `C^k` on `A × [0,∞)`
and whose one-sided `σ`-jets at the seam vanish is `C^k` on `A × ℝ`.  This is a self-contained
proof (by induction on `k`) of the statement whose hard input — the vanishing of the iterated
Fréchet derivatives of `G` at the seam — is supplied by `Work.RPB.B5.jet_vanish`. -/

/-- The iterated Fréchet derivative within `A × [0,∞)` of the within-derivative of `G` vanishes
at the seam whenever the next iterated Fréchet derivative of `G` does (currying of multilinear
maps). -/
theorem iteratedFDerivWithin_fderivWithin_eq_zero {P E : Type u} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set P} {k : ℕ} {G : P × ℝ → E} {p : P}
    (hUD : UniqueDiffOn ℝ (A ×ˢ Set.Ici (0 : ℝ)))
    (hx : (p, (0 : ℝ)) ∈ A ×ˢ Set.Ici (0 : ℝ))
    (h : iteratedFDerivWithin ℝ (k + 1) G (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) = 0) :
    iteratedFDerivWithin ℝ k (fun y => fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) y)
      (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) = 0 := by
  refine ContinuousMultilinearMap.ext (fun u => ?_)
  refine ContinuousLinearMap.ext (fun w => ?_)
  have hcur := iteratedFDerivWithin_succ_apply_right (𝕜 := ℝ)
    (s := A ×ˢ Set.Ici (0 : ℝ)) (x := (p, 0)) (f := G) hUD hx (n := k) (Fin.snoc u w)
  rw [Fin.init_snoc, Fin.snoc_last] at hcur
  rw [h] at hcur
  exact hcur.symm

/-- **Flat truncation.**  If `G : P × ℝ → E` is `C^k` on `A × [0,∞)` and all its iterated
Fréchet derivatives of order `≤ k` vanish along the seam `A × {0}`, then its truncation at the
seam is `C^k` on `A × ℝ`. -/
theorem truncFlatAux : ∀ (k : ℕ) {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Set P), UniqueDiffOn ℝ A →
    (∀ p ∈ A, p ∈ closure (interior A)) → (G : P × ℝ → E) →
    ContDiffOn ℝ k G (A ×ˢ Set.Ici (0 : ℝ)) →
    (∀ m ≤ k, ∀ p ∈ A,
      iteratedFDerivWithin ℝ m G (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) = 0) →
    ContDiffOn ℝ k (fun z : P × ℝ => if z.2 ≤ 0 then 0 else G z) (A ×ˢ Set.univ) := by
  intro k
  induction k with
  | zero =>
    intro P E _ _ _ _ A hA hAcl G hG hjet
    rw [show ((0 : ℕ) : WithTop ℕ∞) = (0 : WithTop ℕ∞) from rfl, contDiffOn_zero]
    intro z hz
    rw [ContinuousWithinAt]
    rcases z with ⟨p, σ⟩
    rcases lt_trichotomy σ 0 with hlt | heq | hgt
    · -- left half space: the truncated function vanishes near the point
      have hmem : {w : P × ℝ | w.2 < 0} ∈ 𝓝[A ×ˢ Set.univ] (p, σ) :=
        nhdsWithin_le_nhds (Filter.mem_of_superset
          ((isOpen_lt continuous_snd continuous_const).mem_nhds hlt) (fun w hw => hw))
      have hev : (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
          =ᶠ[𝓝[A ×ˢ Set.univ] (p, σ)] (fun _ => 0) := by
        filter_upwards [hmem] with w hw
        exact ite_eq_left (le_of_lt hw)
      exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hev
        (ite_eq_left (le_of_lt hlt))
    · -- the seam: `G w → G (p,0) = 0` from the right and `0` from the left
      subst heq
      have hp : p ∈ A := hz.1
      have hGz : G (p, 0) = 0 := by
        have h := congrArg (fun (L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => P × ℝ) E) =>
          L Fin.elim0) (hjet 0 (Nat.zero_le 0) p hp)
        simpa only [iteratedFDerivWithin_zero_apply, ContinuousMultilinearMap.zero_apply] using h
      have hcl : ContinuousWithinAt G (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) :=
        hG.continuousOn.continuousWithinAt ⟨hp, Set.mem_Ici.mpr (le_refl (0:ℝ))⟩
      -- split the domain into the two half spaces
      have hleft : Filter.Tendsto (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
          (𝓝[(A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0}] (p, 0)) (𝓝 (0 : E)) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (ite_eq_left hw.2).symm
      have hright : Filter.Tendsto (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
          (𝓝[(A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2}] (p, 0)) (𝓝 (0 : E)) := by
        have h1 : Filter.Tendsto G (𝓝[(A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2}] (p, 0))
            (𝓝 (0 : E)) := by
          have hset : (A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2}
              = (A ×ˢ Set.Ici (0:ℝ)) ∩ {w : P × ℝ | 0 < w.2} := by
            ext w
            constructor
            · rintro ⟨hw1, hw2⟩
              exact ⟨Set.mem_prod.mpr ⟨(Set.mem_prod.mp hw1).1, Set.mem_Ici.mpr (le_of_lt hw2)⟩,
                hw2⟩
            · rintro ⟨hw1, hw2⟩
              exact ⟨Set.mem_prod.mpr ⟨(Set.mem_prod.mp hw1).1, Set.mem_univ _⟩, hw2⟩
          have h2 : Filter.Tendsto G (𝓝[A ×ˢ Set.Ici (0:ℝ)] (p, 0)) (𝓝 (G (p, 0))) := hcl
          rw [hGz] at h2
          rw [hset]
          exact h2.mono_left (nhdsWithin_mono _ Set.inter_subset_left)
        refine Filter.Tendsto.congr' ?_ h1
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (ite_eq_right (not_le.mpr (show (0:ℝ) < w.2 from hw.2))).symm
      have hcov : {w : P × ℝ | w.2 ≤ 0} ∪ {w : P × ℝ | 0 < w.2} = Set.univ := by
        ext w
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ]
        exact ⟨fun _ => trivial, fun _ => (lt_or_ge (0:ℝ) w.2).elim Or.inr Or.inl⟩
      have hunion : (A ×ˢ Set.univ : Set (P × ℝ))
          = ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0})
            ∪ ((A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2}) := by
        rw [← Set.inter_union_distrib_left, hcov, Set.inter_univ]
      have hsup := hleft.sup hright
      rw [← nhdsWithin_union, ← hunion] at hsup
      have hval : (if (p, (0:ℝ)).2 ≤ 0 then (0 : E) else G (p, 0)) = 0 := ite_eq_left le_rfl
      rw [hval]
      exact hsup
    · -- right half space: the truncated function agrees with `G` near the point
      have hmem : {w : P × ℝ | 0 < w.2} ∈ 𝓝[A ×ˢ Set.univ] (p, σ) :=
        nhdsWithin_le_nhds (Filter.mem_of_superset
          ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt) (fun w hw => hw))
      have hev : (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
          =ᶠ[𝓝[A ×ˢ Set.univ] (p, σ)] G := by
        filter_upwards [hmem] with w hw
        exact ite_eq_right (not_le.mpr hw)
      have hset : (A ×ˢ Set.univ : Set (P × ℝ)) =ᶠ[𝓝 (p, σ)] (A ×ˢ Set.Ici (0:ℝ)) := by
        filter_upwards [Filter.mem_of_superset
          ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt) (fun w hw => hw)] with w hw
        refine propext ⟨?_, ?_⟩
        · intro h
          exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).1, Set.mem_Ici.mpr (le_of_lt hw)⟩
        · intro h
          exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).1, Set.mem_univ _⟩
      have hGc : ContinuousWithinAt G (A ×ˢ Set.univ) (p, σ) :=
        ContinuousWithinAt.congr_set
          (hG.continuousOn.continuousWithinAt ⟨hz.1, le_of_lt hgt⟩) hset.symm
      exact ContinuousWithinAt.congr_of_eventuallyEq hGc hev (ite_eq_right (not_le.mpr hgt))
  | succ k ih =>
    intro P E _ _ _ _ A hA hAcl G hG hjet
    have hUD : UniqueDiffOn ℝ (A ×ˢ Set.Ici (0 : ℝ)) := hA.prod (uniqueDiffOn_Ici 0)
    have hGdiff : DifferentiableOn ℝ G (A ×ˢ Set.Ici (0 : ℝ)) := hG.differentiableOn (by simp)
    -- ### Step 1: the truncated function is differentiable on the slab
    have hdiff : DifferentiableOn ℝ (fun z : P × ℝ => if z.2 ≤ 0 then 0 else G z)
        (A ×ˢ Set.univ) := by
      intro z hz
      rcases z with ⟨p, σ⟩
      rcases lt_trichotomy σ 0 with hlt | heq | hgt
      · have hmem : {w : P × ℝ | w.2 < 0} ∈ 𝓝[A ×ˢ Set.univ] (p, σ) :=
          nhdsWithin_le_nhds (Filter.mem_of_superset
            ((isOpen_lt continuous_snd continuous_const).mem_nhds hlt) (fun w hw => hw))
        have hev : (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
            =ᶠ[𝓝[A ×ˢ Set.univ] (p, σ)] (fun _ => 0) := by
          filter_upwards [hmem] with w hw
          exact ite_eq_left (le_of_lt hw)
        exact DifferentiableWithinAt.congr_of_eventuallyEq (differentiableWithinAt_const 0) hev
          (ite_eq_left (le_of_lt hlt))
      · -- the seam: the derivative vanishes
        subst heq
        have hp : p ∈ A := hz.1
        have hz1 : (p, (0:ℝ)) ∈ A ×ˢ Set.Ici (0 : ℝ) := ⟨hp, Set.mem_Ici.mpr (le_refl (0:ℝ))⟩
        have hUDat : UniqueDiffWithinAt ℝ (A ×ˢ Set.Ici (0 : ℝ)) (p, (0:ℝ)) :=
          UniqueDiffWithinAt.prod (𝕜 := ℝ) (x := p) (y := (0:ℝ)) (hA p hp)
            (uniqueDiffWithinAt_Ici (0:ℝ))
        have hjet1 : iteratedFDerivWithin ℝ 1 G (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) = 0 :=
          hjet 1 (by simp) p hp
        have hGfd0 : HasFDerivWithinAt G (0 : (P × ℝ) →L[ℝ] E) (A ×ˢ Set.Ici (0 : ℝ))
            (p, (0:ℝ)) := by
          have hd := (hGdiff (p, (0:ℝ)) hz1).hasFDerivWithinAt
          have h0 : fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) (p, (0:ℝ)) = 0 := by
            refine ContinuousLinearMap.ext (fun v => ?_)
            have h := iteratedFDerivWithin_one_apply (𝕜 := ℝ) (s := A ×ˢ Set.Ici (0 : ℝ))
              (f := G) (x := (p, (0:ℝ))) hUDat (fun _ => v)
            simpa only [hjet1, ContinuousMultilinearMap.zero_apply] using h.symm
          rwa [h0] at hd
        have hGz : G (p, 0) = 0 := by
          have h := congrArg (fun (L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => P × ℝ) E) =>
            L Fin.elim0) (hjet 0 (Nat.zero_le (k+1)) p hp)
          simpa only [iteratedFDerivWithin_zero_apply, ContinuousMultilinearMap.zero_apply] using h
        have hpos : HasFDerivWithinAt (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w) 0
            ((A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2}) (p, 0) :=
          (hGfd0.mono (fun w hw => ⟨hw.1.1, le_of_lt (show (0:ℝ) < w.2 from hw.2)⟩)).congr
            (fun w hw => ite_eq_right (not_le.mpr (show (0:ℝ) < w.2 from hw.2)))
            (by rw [hGz]; simp)
        have hneg : HasFDerivWithinAt (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w) 0
            ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0}) (p, 0) :=
          (hasFDerivWithinAt_const (𝕜 := ℝ) (E := P × ℝ) (F := E) (0 : E) (p, (0:ℝ))
            ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0})).congr
            (fun w hw => ite_eq_left hw.2)
            (by simp)
        have hcov : {w : P × ℝ | 0 < w.2} ∪ {w : P × ℝ | w.2 ≤ 0} = Set.univ := by
          ext w
          simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ]
          exact ⟨fun _ => trivial, fun _ => (lt_or_ge (0:ℝ) w.2).elim Or.inl Or.inr⟩
        have hunion : ((A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2})
            ∪ ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0}) = A ×ˢ Set.univ := by
          rw [← Set.inter_union_distrib_left, hcov, Set.inter_univ]
        have hboth := hpos.union hneg
        rw [hunion] at hboth
        exact hboth.differentiableWithinAt
      · have hmem : {w : P × ℝ | 0 < w.2} ∈ 𝓝[A ×ˢ Set.univ] (p, σ) :=
          nhdsWithin_le_nhds (Filter.mem_of_superset
            ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt) (fun w hw => hw))
        have hev : (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
            =ᶠ[𝓝[A ×ˢ Set.univ] (p, σ)] G := by
          filter_upwards [hmem] with w hw
          exact ite_eq_right (not_le.mpr hw)
        have hset : (A ×ˢ Set.univ : Set (P × ℝ)) =ᶠ[𝓝 (p, σ)] (A ×ˢ Set.Ici (0:ℝ)) := by
          filter_upwards [Filter.mem_of_superset
            ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt) (fun w hw => hw)] with w hw
          refine propext ⟨?_, ?_⟩
          · intro h
            exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).1, Set.mem_Ici.mpr (le_of_lt hw)⟩
          · intro h
            exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).1, Set.mem_univ _⟩
        have hgd : DifferentiableWithinAt ℝ G (A ×ˢ Set.univ) (p, σ) :=
          (differentiableWithinAt_congr_set hset).mpr
            (hGdiff (p, σ) ⟨hz.1, le_of_lt hgt⟩)
        exact DifferentiableWithinAt.congr_of_eventuallyEq hgd hev
          (ite_eq_right (not_le.mpr hgt))
    -- ### Step 2: the within-derivative is the truncation of `fderivWithin ℝ G`
    have hderiv : ∀ z ∈ A ×ˢ Set.univ,
        fderivWithin ℝ (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
            (A ×ˢ Set.univ) z
          = (if z.2 ≤ 0 then 0 else fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) z) := by
      intro z hz
      rcases z with ⟨p, σ⟩
      rcases lt_trichotomy σ 0 with hlt | heq | hgt
      · have hmem : {w : P × ℝ | w.2 < 0} ∈ 𝓝[A ×ˢ Set.univ] (p, σ) :=
          nhdsWithin_le_nhds (Filter.mem_of_superset
            ((isOpen_lt continuous_snd continuous_const).mem_nhds hlt) (fun w hw => hw))
        have hev : (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
            =ᶠ[𝓝[A ×ˢ Set.univ] (p, σ)] (fun _ => 0) := by
          filter_upwards [hmem] with w hw
          exact ite_eq_left (le_of_lt hw)
        rw [hev.fderivWithin_eq (ite_eq_left (le_of_lt hlt)), ite_eq_left (le_of_lt hlt)]
        exact (hasFDerivWithinAt_const (0 : E) (p, σ) (A ×ˢ Set.univ)).fderivWithin
          (UniqueDiffWithinAt.prod (hA p hz.1) uniqueDiffWithinAt_univ)
      · subst heq
        have hp : p ∈ A := hz.1
        have hUDat : UniqueDiffWithinAt ℝ (A ×ˢ (Set.univ : Set ℝ)) (p, 0) :=
          UniqueDiffWithinAt.prod (𝕜 := ℝ) (x := p) (y := (0:ℝ)) (hA p hp)
            (uniqueDiffWithinAt_univ : UniqueDiffWithinAt ℝ (Set.univ : Set ℝ) 0)
        have hz1 : (p, (0:ℝ)) ∈ A ×ˢ Set.Ici (0 : ℝ) := ⟨hp, Set.mem_Ici.mpr (le_refl (0:ℝ))⟩
        have hjet1 : iteratedFDerivWithin ℝ 1 G (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) = 0 :=
          hjet 1 (by simp) p hp
        have hGfd0 : HasFDerivWithinAt G (0 : (P × ℝ) →L[ℝ] E) (A ×ˢ Set.Ici (0 : ℝ))
            (p, (0:ℝ)) := by
          have hd := (hGdiff (p, (0:ℝ)) hz1).hasFDerivWithinAt
          have h0 : fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) (p, (0:ℝ)) = 0 := by
            refine ContinuousLinearMap.ext (fun v => ?_)
            have h := iteratedFDerivWithin_one_apply (𝕜 := ℝ) (s := A ×ˢ Set.Ici (0 : ℝ))
              (f := G) (x := (p, (0:ℝ)))
              (UniqueDiffWithinAt.prod (𝕜 := ℝ) (x := p) (y := (0:ℝ)) (hA p hp)
                (uniqueDiffWithinAt_Ici (0:ℝ))) (fun _ => v)
            simpa only [hjet1, ContinuousMultilinearMap.zero_apply] using h.symm
          rwa [h0] at hd
        have hGz : G (p, 0) = 0 := by
          have h := congrArg (fun (L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => P × ℝ) E) =>
            L Fin.elim0) (hjet 0 (Nat.zero_le (k+1)) p hp)
          simpa only [iteratedFDerivWithin_zero_apply, ContinuousMultilinearMap.zero_apply] using h
        have hpos : HasFDerivWithinAt (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w) 0
            ((A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2}) (p, 0) :=
          (hGfd0.mono (fun w hw => ⟨hw.1.1, le_of_lt (show (0:ℝ) < w.2 from hw.2)⟩)).congr
            (fun w hw => ite_eq_right (not_le.mpr (show (0:ℝ) < w.2 from hw.2)))
            (by rw [hGz]; simp)
        have hneg : HasFDerivWithinAt (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w) 0
            ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0}) (p, 0) :=
          (hasFDerivWithinAt_const (𝕜 := ℝ) (E := P × ℝ) (F := E) (0 : E) (p, (0:ℝ))
            ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0})).congr
            (fun w hw => ite_eq_left hw.2)
            (by simp)
        have hcov : {w : P × ℝ | 0 < w.2} ∪ {w : P × ℝ | w.2 ≤ 0} = Set.univ := by
          ext w
          simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ]
          exact ⟨fun _ => trivial, fun _ => (lt_or_ge (0:ℝ) w.2).elim Or.inl Or.inr⟩
        have hunion : ((A ×ˢ Set.univ) ∩ {w : P × ℝ | 0 < w.2})
            ∪ ((A ×ˢ Set.univ) ∩ {w : P × ℝ | w.2 ≤ 0}) = A ×ˢ Set.univ := by
          rw [← Set.inter_union_distrib_left, hcov, Set.inter_univ]
        have hboth := hpos.union hneg
        rw [hunion] at hboth
        rw [hboth.fderivWithin hUDat, ite_eq_left (le_refl (0:ℝ))]
      · have hmem : {w : P × ℝ | 0 < w.2} ∈ 𝓝[A ×ˢ Set.univ] (p, σ) :=
          nhdsWithin_le_nhds (Filter.mem_of_superset
            ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt) (fun w hw => hw))
        have hev : (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
            =ᶠ[𝓝[A ×ˢ Set.univ] (p, σ)] G := by
          filter_upwards [hmem] with w hw
          exact ite_eq_right (not_le.mpr hw)
        have hset : (A ×ˢ Set.univ : Set (P × ℝ)) =ᶠ[𝓝 (p, σ)] (A ×ˢ Set.Ici (0:ℝ)) := by
          filter_upwards [Filter.mem_of_superset
            ((isOpen_lt continuous_const continuous_snd).mem_nhds hgt) (fun w hw => hw)] with w hw
          refine propext ⟨?_, ?_⟩
          · intro h
            exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).1, Set.mem_Ici.mpr (le_of_lt hw)⟩
          · intro h
            exact Set.mem_prod.mpr ⟨(Set.mem_prod.mp h).1, Set.mem_univ _⟩
        rw [hev.fderivWithin_eq (ite_eq_right (not_le.mpr hgt)), ite_eq_right (not_le.mpr hgt),
          fderivWithin_congr_set hset]
    -- ### Step 3: apply the induction hypothesis to the derivative family
    have hG' : ContDiffOn ℝ k (fun y => fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) y)
        (A ×ˢ Set.Ici (0 : ℝ)) :=
      hG.fderivWithin hUD (by simp)
    have hjet' : ∀ m ≤ k, ∀ p ∈ A,
        iteratedFDerivWithin ℝ m (fun y => fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) y)
          (A ×ˢ Set.Ici (0 : ℝ)) (p, 0) = 0 := by
      intro m hm p hp
      exact iteratedFDerivWithin_fderivWithin_eq_zero hUD ⟨hp, Set.mem_Ici.mpr (le_refl (0:ℝ))⟩
        (hjet (m + 1) (by omega) p hp)
    have hih := ih A hA hAcl (fun y => fderivWithin ℝ G (A ×ˢ Set.Ici (0 : ℝ)) y) hG' hjet'
    have hder : ContDiffOn ℝ k
        (fun y => fderivWithin ℝ (fun w : P × ℝ => if w.2 ≤ 0 then (0 : E) else G w)
          (A ×ˢ Set.univ) y) (A ×ˢ Set.univ) :=
      hih.congr (fun y hy => hderiv y hy)
    have hmain := contDiffOn_succ_of_fderivWithin (𝕜 := ℝ) (n := (k : WithTop ℕ∞)) hdiff
      (fun hcon => by simp at hcon) hder
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 := by simp
    rw [hcast]
    exact hmain

theorem lagData_smooth_at_negSqrt2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) (t₀ : ℝ) :
    ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (-Real.sqrt 2, t₀)) := by
  classical
  -- ## Step 1: shift `t₀` into `[1, ∞)`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℝ) ≤ t₀ + 2 * Real.pi * (N : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_ge ((1 - t₀) / (2 * Real.pi))
    refine ⟨n, ?_⟩
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_right hn (le_of_lt hπ)
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h
    linarith
  set t₁ : ℝ := t₀ + 2 * Real.pi * (N : ℝ) with ht₁def
  have ht₁ : (1 : ℝ) ≤ t₁ := hN
  have ht₁pos : 0 < t₁ := by linarith
  suffices hmain : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (-Real.sqrt 2, t₁)) by
    have h := hmain
    rw [ht₁def] at h
    exact lagData_tShift CI a ha D τ₀ hτ₀ t₀ N h
  -- ## Step 2: the truncation data
  obtain ⟨δ, hδpos, hδle, hdec⟩ := lagPt_negSqrt2_decomp CI a ha D
  set η : ℝ := D.κ / 8 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith [D.hκ]
  have hηκ : 3 * η < D.κ := by rw [hηdef]; linarith [D.hκ]
  have hsig0 : Work.RPB.B5.sig (-Real.sqrt 2) = 0 := by
    simp only [Work.RPB.B5.sig, neg_sq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hex : ∃ e : ℝ, 0 < e ∧ ∀ x : ℝ, |x + Real.sqrt 2| < e →
      |Work.RPB.B5.sig x| < η ∧ |x + Real.sqrt 2| < δ := by
    have hcont : ContinuousAt Work.RPB.B5.sig (-Real.sqrt 2) := by
      have hd : ContDiff ℝ 8 (fun x : ℝ => x ^ 2 / 2 - 1) := by fun_prop
      have hcd : ContDiffAt ℝ 8 Work.RPB.B5.sig (-Real.sqrt 2) := by
        change ContDiffAt ℝ 8 (fun x : ℝ => x ^ 2 / 2 - 1) (-Real.sqrt 2)
        exact hd.contDiffAt
      exact hcd.continuousAt
    have hpre : Work.RPB.B5.sig ⁻¹' Set.Ioo (-η) η ∈ 𝓝 (-Real.sqrt 2) :=
      hcont.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by rw [hsig0]; exact ⟨by linarith, hηpos⟩))
    obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min r δ, lt_min hrpos hδpos, ?_⟩
    intro x hx
    have hxr : |x + Real.sqrt 2| < r := lt_of_lt_of_le hx (min_le_left _ _)
    have hxδ : |x + Real.sqrt 2| < δ := lt_of_lt_of_le hx (min_le_right _ _)
    have hd : dist x (-Real.sqrt 2) < r := by
      rw [Real.dist_eq, sub_neg_eq_add]
      exact hxr
    have hmem := Set.mem_Ioo.mp (hr hd)
    exact ⟨abs_lt.mpr ⟨hmem.1, hmem.2⟩, hxδ⟩
  obtain ⟨e, hepos, he⟩ := hex
  -- ## Step 3: the slab `A` in the `(τ,t)`-plane, and the cut-off `ψ`
  set A : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ) with hAdef
  have hAud : UniqueDiffOn ℝ A := by
    rw [hAdef]
    exact (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)).prod (uniqueDiffOn_Ioi 0)
  have hAcl : ∀ p ∈ A, p ∈ closure (interior A) := by
    intro p hp
    rw [hAdef] at hp ⊢
    have hp2 : (0 : ℝ) < p.2 := hp.2
    rw [interior_prod_eq, interior_Icc, interior_Ioi, closure_prod_eq,
      closure_Ioo (by norm_num : (0:ℝ) ≠ 1), closure_Ioi, Set.mem_prod]
    exact ⟨hp.1, show (0 : ℝ) ≤ p.2 from le_of_lt hp2⟩
  set ψ : ℝ → ℝ := fun σ => Real.smoothTransition (2 + σ / η) *
    Real.smoothTransition (2 - σ / η) with hψdef
  have hψsm : ContDiff ℝ 8 ψ := by rw [hψdef]; fun_prop
  have hψone : ∀ σ : ℝ, |σ| ≤ η → ψ σ = 1 := by
    intro σ hσ
    rw [hψdef]
    have h1 : (1 : ℝ) ≤ 2 + σ / η := by
      have h : -1 ≤ σ / η := by
        rw [le_div_iff₀ hηpos]
        linarith [(abs_le.mp hσ).1]
      linarith
    have h2 : (1 : ℝ) ≤ 2 - σ / η := by
      have h : σ / η ≤ 1 := by
        rw [div_le_iff₀ hηpos]
        linarith [(abs_le.mp hσ).2]
      linarith
    show Real.smoothTransition (2 + σ / η) * Real.smoothTransition (2 - σ / η) = 1
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]
  have hψzero : ∀ σ : ℝ, 2 * η ≤ σ → ψ σ = 0 := by
    intro σ hσ
    rw [hψdef]
    have h : 2 - σ / η ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hηpos]
      linarith
    show Real.smoothTransition (2 + σ / η) * Real.smoothTransition (2 - σ / η) = 0
    rw [Real.smoothTransition.zero_of_nonpos h, mul_zero]
  -- ## Step 4: the seam defect and its cut-off
  set DD : ℝ → ℝ → ℝ → Work.RPV.PS := fun τ t σ =>
    collarPt D.Γc D.Ac τ σ t - D.W τ t (D.ρh τ t σ) with hDDdef
  set hh : (ℝ × ℝ) × ℝ → Work.RPV.PS := fun p => ψ p.2 • DD p.1.1 p.1.2 p.2 with hhhdef
  have hΓ : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => D.Γc p.1.1 p.2 p.1.2)
      (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ) := by
    have hφ : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ) :=
      (by fun_prop : ContDiff ℝ 8 (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))).contDiffOn
    have hmap : Set.MapsTo (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ)
        ((Set.Icc 0 1 : Set ℝ) ×ˢ Set.univ ×ˢ Set.Ici 0) := by
      intro p hp
      exact ⟨hp.1.1, Set.mem_univ _, hp.1.2⟩
    have := D.hΓsm.comp hφ hmap
    simpa only [Function.comp_def] using this
  have hAc : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => D.Ac p.1.1 p.2 p.1.2)
      (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ) := by
    have hφ : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ) :=
      (by fun_prop : ContDiff ℝ 8 (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))).contDiffOn
    have hmap : Set.MapsTo (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ)
        ((Set.Icc 0 1 : Set ℝ) ×ˢ Set.univ ×ˢ Set.Ici 0) := by
      intro p hp
      exact ⟨hp.1.1, Set.mem_univ _, hp.1.2⟩
    have := D.hAsm.comp hφ hmap
    simpa only [Function.comp_def] using this
  have hcollar : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ =>
      collarPt D.Γc D.Ac p.1.1 p.2 p.1.2) (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ) := by
    have hpair : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ =>
        (D.Γc p.1.1 p.2 p.1.2, (p.2, D.Ac p.1.1 p.2 p.1.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.Ici 0) ×ˢ Set.univ) :=
      hΓ.prodMk ((contDiff_snd.contDiffOn).prodMk hAc)
    have := chartJets_levelPt_contDiff.comp_contDiffOn hpair
    simpa only [Function.comp_def, collarPt] using this
  have hchart : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ =>
      D.W p.1.1 p.1.2 (D.ρh p.1.1 p.1.2 p.2))
      (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.univ) ×ˢ Set.Ioo (-D.κ) D.κ) := by
    have hφ : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.1.2, p.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.univ) ×ˢ Set.Ioo (-D.κ) D.κ) :=
      (by fun_prop : ContDiff ℝ 8 (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.1.2, p.2)))).contDiffOn
    have hmap : Set.MapsTo (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.1.2, p.2)))
        (((Set.Icc 0 1 : Set ℝ) ×ˢ Set.univ) ×ˢ Set.Ioo (-D.κ) D.κ)
        ((Set.Icc 0 1 : Set ℝ) ×ˢ Set.univ ×ˢ Set.Ioo (-D.κ) D.κ) := by
      intro p hp
      exact ⟨hp.1.1, Set.mem_univ _, hp.2⟩
    have := (chartLev_W_rho_contDiffOn CI a ha D).comp hφ hmap
    simpa only [Function.comp_def] using this
  have hDD : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => DD p.1.1 p.1.2 p.2)
      ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) := by
    have h1 : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ =>
        collarPt D.Γc D.Ac p.1.1 p.2 p.1.2)
        ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) :=
      hcollar.mono (fun p hp => ⟨⟨hp.1.1,
        show (0 : ℝ) ≤ p.1.2 from le_of_lt (show (0:ℝ) < p.1.2 from hp.1.2)⟩, Set.mem_univ _⟩)
    have h2 : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ =>
        D.W p.1.1 p.1.2 (D.ρh p.1.1 p.1.2 p.2))
        ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) :=
      hchart.mono (fun p hp => ⟨⟨hp.1.1, Set.mem_univ _⟩, hp.2⟩)
    have := h1.sub h2
    simpa only [hDDdef] using this
  -- `hh` is `C⁸` on the half space `σ ≥ 0`
  have hh_sm : ContDiffOn ℝ 8 hh ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ici 0) := by
    intro p hp
    obtain ⟨hpA, hpσ⟩ := hp
    have hpσ' : (0 : ℝ) ≤ p.2 := hpσ
    rcases lt_or_ge (2 * η) p.2 with hbig | hsmall
    · -- `ψ` vanishes near `p`
      have hmem : {w : (ℝ × ℝ) × ℝ | 2 * η < w.2} ∈
          𝓝[((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ici 0)] p :=
        nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_snd).mem_nhds hbig)
      have hev : hh =ᶠ[𝓝[((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ici 0)] p]
          (fun _ => (0 : Work.RPV.PS)) := by
        filter_upwards [hmem] with w hw
        simp only [hhhdef]
        rw [hψzero w.2 (le_of_lt hw), zero_smul]
      refine (contDiffWithinAt_const (c := (0 : Work.RPV.PS))).congr_of_eventuallyEq hev ?_
      simp only [hhhdef]
      rw [hψzero p.2 (le_of_lt hbig), zero_smul]
    · -- the point lies where both profiles are smooth
      have hlow : -D.κ < p.2 := by linarith [D.hκ, hpσ']
      have hhigh : p.2 < D.κ := by linarith [hηpos, hηκ, hsmall]
      have hpT : p ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ :=
        ⟨hpA, hlow, hhigh⟩
      have hopen : {w : (ℝ × ℝ) × ℝ | w.2 < D.κ} ∈ 𝓝 p :=
        (isOpen_lt continuous_snd continuous_const).mem_nhds hhigh
      have hmem : ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) ∈
          𝓝[((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ici 0)] p := by
        refine Filter.mem_of_superset
          (Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hopen)) ?_
        rintro w ⟨hw1, hw2⟩
        have hw0 : (0 : ℝ) ≤ w.2 := hw1.2
        exact ⟨hw1.1, ⟨by linarith [D.hκ, hw0], hw2⟩⟩
      have hT : ContDiffOn ℝ 8 hh ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) := by
        have h1 : ContDiffOn ℝ 8 (fun w : (ℝ × ℝ) × ℝ => ψ w.2)
            ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) :=
          hψsm.comp_contDiffOn contDiff_snd.contDiffOn
        have h2 : ContDiffOn ℝ 8 (fun p : (ℝ × ℝ) × ℝ => ψ p.2 • DD p.1.1 p.1.2 p.2)
            ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) :=
          (h1.smul hDD).congr (fun q _ => by
            show ψ q.2 • DD q.1.1 q.1.2 q.2
              = ((fun w : (ℝ × ℝ) × ℝ => ψ w.2) • fun q : (ℝ × ℝ) × ℝ => DD q.1.1 q.1.2 q.2) q
            rw [Pi.smul_apply'])
        simpa only [hhhdef] using h2
      exact (contDiffWithinAt_inter' hmem).mp
        ((hT.mono Set.inter_subset_right).contDiffWithinAt ⟨⟨hpA, hpσ⟩, hpT⟩)
  -- the one-sided `σ`-jets of `hh` vanish at the seam
  have hh_flat : ∀ p ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0), ∀ j : ℕ, j ≤ 8 →
      iteratedDerivWithin j (fun σ : ℝ => hh (p, σ)) (Set.Ioi 0) 0 = 0 := by
    intro p hp j hj
    have hpt : (p, (0:ℝ)) ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ :=
      ⟨hp, ⟨by linarith [D.hκ], by linarith [D.hκ]⟩⟩
    have hDD_at : ContDiffAt ℝ 8 (fun σ : ℝ => DD p.1 p.2 σ) 0 := by
      have hin : ContDiffWithinAt ℝ 8 (fun σ : ℝ => (p, σ)) (Set.Ioo (-D.κ) D.κ) 0 :=
        (by fun_prop : ContDiff ℝ 8 (fun σ : ℝ => (p, σ))).contDiffWithinAt
      have hmap : Set.MapsTo (fun σ : ℝ => (p, σ)) (Set.Ioo (-D.κ) D.κ)
          ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ioo (-D.κ) D.κ) :=
        fun σ hσ => ⟨hp, hσ⟩
      exact ((hDD.contDiffWithinAt hpt).comp 0 hin hmap).contDiffAt
        (isOpen_Ioo.mem_nhds ⟨by linarith [D.hκ], by linarith [D.hκ]⟩)
    have hhh_at : ContDiffAt ℝ 8 (fun σ : ℝ => hh (p, σ)) 0 := by
      have h2 := hψsm.contDiffAt.smul hDD_at
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun σ => ?_))
      show ψ σ • DD p.1 p.2 σ = ((ψ : ℝ → ℝ) • fun σ : ℝ => DD p.1 p.2 σ) σ
      rw [Pi.smul_apply']
    rw [iteratedDerivWithin_Ioi_eq_iteratedDeriv j (hhh_at.of_le (by exact_mod_cast hj))]
    have hev : (fun σ : ℝ => hh (p, σ)) =ᶠ[𝓝 0] (fun σ : ℝ => DD p.1 p.2 σ) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) hηpos] with σ hσ
      have hσ' : |σ| < η := by
        have h2 := hσ
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h2
        exact h2
      show ψ σ • DD p.1 p.2 σ = DD p.1 p.2 σ
      rw [hψone σ (le_of_lt hσ'), one_smul]
    rw [Filter.EventuallyEq.iteratedDeriv_eq j hev]
    rw [← iteratedDerivWithin_Ioi_eq_iteratedDeriv j (hDD_at.of_le (by exact_mod_cast hj))]
    exact collarChart_flat CI a ha D p.1 hp.1 p.2 j hj
  -- the jet vanishing at the seam, from `jet_vanish`
  have hjet_hh : ∀ m ≤ 8, ∀ p ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0),
      iteratedFDerivWithin ℝ m hh ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.Ici 0) (p, 0) = 0 :=
    jet_vanish (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) hAud hAcl 8 hh hh_sm
      (fun p hp => by
        have h := hh_flat p hp 0 (Nat.zero_le 8)
        simpa only [iteratedDerivWithin_zero] using h)
      hh_flat
  -- ## Step 5: the two summands of `ℓ` near the junction
  have hσsm : ContDiff ℝ 8 Work.RPB.B5.sig := by
    change ContDiff ℝ 8 (fun x : ℝ => x ^ 2 / 2 - 1)
    fun_prop
  set S : Set (ℝ × (ℝ × ℝ)) := Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ with hSdef
  set G : Set (ℝ × (ℝ × ℝ)) :=
    {z : ℝ × (ℝ × ℝ) | 0 < z.2.2 ∧ |z.2.1 + Real.sqrt 2| < e} with hGdef
  have hGmem : G ∈ 𝓝[S] (τ₀, (-Real.sqrt 2, t₁)) := by
    have hopen : IsOpen G := by
      rw [hGdef]
      exact (isOpen_lt continuous_const continuous_snd.snd).inter
        (isOpen_Iio.preimage (continuous_abs.comp (continuous_snd.fst.add continuous_const)))
    refine nhdsWithin_le_nhds (hopen.mem_nhds ?_)
    have hmem0 : |(-Real.sqrt 2) + Real.sqrt 2| < e := by
      rw [neg_add_cancel, abs_zero]; exact hepos
    exact ⟨ht₁pos, hmem0⟩
  -- the chart branch
  have hchartPart : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => D.W z.1 z.2.2 (D.ρh z.1 z.2.2 (Work.RPB.B5.sig z.2.1)))
      (S ∩ G) (τ₀, (-Real.sqrt 2, t₁)) := by
    have h1 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.1) := contDiff_fst
    have h2 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.2.2) := contDiff_snd.snd
    have h3 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.sig z.2.1) :=
      hσsm.comp contDiff_snd.fst
    have hinner : ContDiffWithinAt ℝ 8
        (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, Work.RPB.B5.sig z.2.1))) (S ∩ G)
        (τ₀, (-Real.sqrt 2, t₁)) :=
      (h1.prodMk (h2.prodMk h3)).contDiffWithinAt
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, Work.RPB.B5.sig z.2.1)))
        (S ∩ G) (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.κ) D.κ) := by
      rintro ⟨τ, x, t⟩ ⟨⟨hτ, -, -⟩, ht, hx⟩
      obtain ⟨hsig, -⟩ := he x hx
      have hsig' := abs_lt.mp hsig
      exact ⟨hτ, Set.mem_univ _, ⟨by linarith [D.hκ, hηκ, hsig'.1],
        by linarith [hηκ, hsig'.2]⟩⟩
    have hout : ContDiffWithinAt ℝ 8
        (fun q : ℝ × (ℝ × ℝ) => D.W q.1 q.2.1 (D.ρh q.1 q.2.1 q.2.2))
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.κ) D.κ)
        (τ₀, (t₁, Work.RPB.B5.sig (-Real.sqrt 2))) :=
      (chartLev_W_rho_contDiffOn CI a ha D).contDiffWithinAt
        ⟨hτ₀, Set.mem_univ _, by rw [hsig0]; exact ⟨by linarith [D.hκ], by linarith [D.hκ]⟩⟩
    have hc := ContDiffWithinAt.comp (τ₀, (-Real.sqrt 2, t₁)) hout hinner hmap
    simpa only [Function.comp_def] using hc
  -- the truncated seam defect
  have htruncPart : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => if Work.RPB.B5.sig z.2.1 ≤ 0 then 0
        else hh ((z.1, z.2.2), Work.RPB.B5.sig z.2.1)) (S ∩ G) (τ₀, (-Real.sqrt 2, t₁)) := by
    have hout : ContDiffWithinAt ℝ 8 (fun q : (ℝ × ℝ) × ℝ => if q.2 ≤ 0 then 0 else hh q)
        ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.univ) ((τ₀, t₁), Work.RPB.B5.sig (-Real.sqrt 2)) := by
      have hmemA : ((τ₀, t₁) : ℝ × ℝ) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi (0:ℝ) :=
        ⟨hτ₀, Set.mem_Ioi.mpr ht₁pos⟩
      have h2 := (truncFlatAux 8 (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) hAud hAcl hh hh_sm hjet_hh).contDiffWithinAt
        (x := ((τ₀, t₁), (0:ℝ))) ⟨hmemA, Set.mem_univ _⟩
      convert h2 using 1
      simp [hsig0]
    have h1 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.1) := contDiff_fst
    have h2 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.2.2) := contDiff_snd.snd
    have h3 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.sig z.2.1) :=
      hσsm.comp contDiff_snd.fst
    have hinner : ContDiffWithinAt ℝ 8
        (fun z : ℝ × (ℝ × ℝ) => ((z.1, z.2.2), Work.RPB.B5.sig z.2.1)) (S ∩ G)
        (τ₀, (-Real.sqrt 2, t₁)) :=
      ((h1.prodMk h2).prodMk h3).contDiffWithinAt
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => ((z.1, z.2.2), Work.RPB.B5.sig z.2.1))
        (S ∩ G) ((Set.Icc (0:ℝ) 1 ×ˢ Set.Ioi 0) ×ˢ Set.univ) := by
      rintro ⟨τ, x, t⟩ ⟨⟨hτ, -, -⟩, ht, -⟩
      exact ⟨⟨hτ, ht⟩, Set.mem_univ _⟩
    have hc := ContDiffWithinAt.comp (τ₀, (-Real.sqrt 2, t₁)) hout hinner hmap
    simpa only [Function.comp_def] using hc
  -- ## Step 6: glue and identify
  refine (contDiffWithinAt_inter' hGmem).mp ?_
  refine ((hchartPart.add htruncPart).congr_of_eventuallyEq ?_ ?_)
  · -- eventual equality with `lagPt`
    filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨⟨hτ, -, -⟩, ht, hx⟩ := hz
    obtain ⟨hsig, hxδ⟩ := he z.2.1 hx
    have hψ1 : ψ (Work.RPB.B5.sig z.2.1) = 1 := hψone _ (le_of_lt hsig)
    rw [hdec z.1 hτ z.2.2 z.2.1 hxδ]
    show (if Work.RPB.B5.sig z.2.1 ≤ 0 then D.W z.1 z.2.2 (D.ρh z.1 z.2.2 (Work.RPB.B5.sig z.2.1))
        else collarPt D.Γc D.Ac z.1 (Work.RPB.B5.sig z.2.1) z.2.2)
      = D.W z.1 z.2.2 (D.ρh z.1 z.2.2 (Work.RPB.B5.sig z.2.1))
        + (if Work.RPB.B5.sig z.2.1 ≤ 0 then 0 else hh ((z.1, z.2.2), Work.RPB.B5.sig z.2.1))
    by_cases hσ : Work.RPB.B5.sig z.2.1 ≤ 0
    · rw [ite_eq_left hσ, ite_eq_left hσ, add_zero]
    · rw [ite_eq_right hσ, ite_eq_right hσ]
      show collarPt D.Γc D.Ac z.1 (Work.RPB.B5.sig z.2.1) z.2.2
        = D.W z.1 z.2.2 (D.ρh z.1 z.2.2 (Work.RPB.B5.sig z.2.1))
          + ψ (Work.RPB.B5.sig z.2.1) • DD z.1 z.2.2 (Work.RPB.B5.sig z.2.1)
      rw [hψ1, one_smul, hDDdef]
      show collarPt D.Γc D.Ac z.1 (Work.RPB.B5.sig z.2.1) z.2.2
        = D.W z.1 z.2.2 (D.ρh z.1 z.2.2 (Work.RPB.B5.sig z.2.1))
          + (collarPt D.Γc D.Ac z.1 (Work.RPB.B5.sig z.2.1) z.2.2
            - D.W z.1 z.2.2 (D.ρh z.1 z.2.2 (Work.RPB.B5.sig z.2.1)))
      abel
  · -- the value at the base point
    obtain ⟨-, hxδ⟩ := he (-Real.sqrt 2) (by rw [neg_add_cancel, abs_zero]; exact hepos)
    have hψ1 : ψ (Work.RPB.B5.sig (-Real.sqrt 2)) = 1 := by
      refine hψone _ ?_
      rw [hsig0]; simpa using le_of_lt hηpos
    rw [hdec τ₀ hτ₀ t₁ (-Real.sqrt 2) hxδ]
    show (if Work.RPB.B5.sig (-Real.sqrt 2) ≤ 0
        then D.W τ₀ t₁ (D.ρh τ₀ t₁ (Work.RPB.B5.sig (-Real.sqrt 2)))
        else collarPt D.Γc D.Ac τ₀ (Work.RPB.B5.sig (-Real.sqrt 2)) t₁)
      = D.W τ₀ t₁ (D.ρh τ₀ t₁ (Work.RPB.B5.sig (-Real.sqrt 2)))
        + (if Work.RPB.B5.sig (-Real.sqrt 2) ≤ 0 then 0
          else hh ((τ₀, t₁), Work.RPB.B5.sig (-Real.sqrt 2)))
    by_cases hσ : Work.RPB.B5.sig (-Real.sqrt 2) ≤ 0
    · rw [ite_eq_left hσ, ite_eq_left hσ, add_zero]
    · rw [ite_eq_right hσ, ite_eq_right hσ]
      show collarPt D.Γc D.Ac τ₀ (Work.RPB.B5.sig (-Real.sqrt 2)) t₁
        = D.W τ₀ t₁ (D.ρh τ₀ t₁ (Work.RPB.B5.sig (-Real.sqrt 2)))
          + ψ (Work.RPB.B5.sig (-Real.sqrt 2)) • DD τ₀ t₁ (Work.RPB.B5.sig (-Real.sqrt 2))
      rw [hψ1, one_smul, hDDdef]
      show collarPt D.Γc D.Ac τ₀ (Work.RPB.B5.sig (-Real.sqrt 2)) t₁
        = D.W τ₀ t₁ (D.ρh τ₀ t₁ (Work.RPB.B5.sig (-Real.sqrt 2)))
          + (collarPt D.Γc D.Ac τ₀ (Work.RPB.B5.sig (-Real.sqrt 2)) t₁
            - D.W τ₀ t₁ (D.ρh τ₀ t₁ (Work.RPB.B5.sig (-Real.sqrt 2))))
      abel

end Work.RPB.B5
