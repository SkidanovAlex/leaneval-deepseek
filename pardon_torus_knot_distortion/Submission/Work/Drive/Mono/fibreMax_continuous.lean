import Mathlib
import Submission.Work.Drive.Mono.tiltedShadowDefs

/-!
# Continuity of the fibre height `fibreMax` of the box over its shadow

For the closed box `X = closure (PBox s c σ) ⊆ ℝ³` and three linear functionals
`p, q, ζ : ℝ³ →L[ℝ] ℝ` with `ker p ∩ ker q ∩ ker ζ = {0}`, the maximal height of `ζ` over the
fibre of `X` over a point `w = (p y, q y)` of the shadow of `X` depends continuously on `w`.

## Route

Write `X = {y | ∀ i, |y (σ i) - c (σ i)| ≤ boxSide i * s}` (the closed box, `closure_PBox_eq`).
Since `(p,q,ζ) : ℝ³ → ℝ³` is injective and `ℝ³` is finite dimensional, it is a linear isomorphism
`e`; put `v := e⁻¹ (0,0,1)` (so `p v = q v = 0`, `ζ v = 1`) and `g w := e⁻¹ (w.1, w.2, 0)` (so
`p (g w) = w.1`, `q (g w) = w.2`).

Every point `y ∈ X` over `w` has the form `y = g w + t v` with `t = ζ (y - g w)`, and the box
conditions on the parameter `t` are, for each `i` with `V i := v (σ i) ≠ 0`, the inequality
`|(g w)(σ i) - c(σ i) + t V i| ≤ boxSide i * s`, which bounds `t` above by the *affine* function
`Bi i w := (sign (V i) * boxSide i * s - ((g w)(σ i) - c(σ i))) / V i` of `w`
(and gives no condition when `V i = 0`).  Hence

`fibreMax ζ p q X w = ζ (g w) + min_{i : V i ≠ 0} Bi i w`   for `w` in the shadow of `X`,

a minimum of finitely many continuous functions of `w`; this is the identity `key`, and continuity
follows with `Continuous.finset_inf'_apply`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The closed box with the side lengths of `PBox s c σ`. -/
theorem closure_PBox_eq {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ)
      = {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
  have hcl : IsClosed {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} := by
    rw [show {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s}
        = ⋂ i, {y : R3 | |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} by ext y; simp]
    apply isClosed_iInter
    intro i
    have h : {y : R3 | |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s}
        = (fun y : R3 => y (σ i) - c (σ i)) ⁻¹'
            Set.Icc (-(Submission.boxSide i * s)) (Submission.boxSide i * s) := by
      ext y; simp [abs_le]
    rw [h]
    exact isClosed_Icc.preimage
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).sub continuous_const)
  have hsub : closure (Submission.PBox s c σ)
      ⊆ {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} :=
    closure_minimal (fun y hy i => le_of_lt (hy i)) hcl
  refine Subset.antisymm hsub ?_
  intro y hy
  have hmem : ∀ t : ℝ, 0 < t → t < 1 → c + t • (y - c) ∈ Submission.PBox s c σ := by
    intro t ht0 ht1 i
    have hcoord : (c + t • (y - c)) (σ i) - c (σ i) = t * (y (σ i) - c (σ i)) := by simp
    rw [hcoord, abs_mul, abs_of_pos ht0]
    have hB : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
    have hA : |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := hy i
    nlinarith [abs_nonneg (y (σ i) - c (σ i))]
  have hcont : Continuous (fun t : ℝ => c + t • (y - c)) := by fun_prop
  have htend : Filter.Tendsto (fun t : ℝ => c + t • (y - c))
      (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds y) := by
    have h : Filter.Tendsto (fun t : ℝ => c + t • (y - c)) (nhds 1) (nhds y) := by
      have h' := (hcont.continuousAt (x := 1)).tendsto
      have hy1 : c + (1:ℝ) • (y - c) = y := by simp
      rwa [hy1] at h'
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto (f := fun t : ℝ => c + t • (y - c))
    (b := nhdsWithin (1:ℝ) (Set.Iio 1)) htend ?_
  have hIoi : Set.Ioi (0:ℝ) ∈ nhdsWithin (1:ℝ) (Set.Iio 1) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hIoi] with t ht1 ht0
  exact hmem t ht0 ht1


/-- **The maximal height of the box over its shadow is continuous.** -/
theorem fibreMax_continuous {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3))
    {p q ζ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    (hker : ∀ y : LeanEval.KnotTheory.PardonDistortion.R3,
      p y = 0 → q y = 0 → ζ y = 0 → y = 0) :
    ContinuousOn (Work.Drive.Mono.fibreMax ζ p q (closure (Submission.PBox s c σ)))
      {w : ℝ × ℝ | ∃ y ∈ closure (Submission.PBox s c σ), p y = w.1 ∧ q y = w.2} := by
  classical
  have hbox : closure (Submission.PBox s c σ)
      = {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s} :=
    closure_PBox_eq hs c σ
  have hXbox : ∀ y : R3, y ∈ closure (Submission.PBox s c σ) ↔
      ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro y; rw [hbox]; rfl
  have hXcpt : IsCompact (closure (Submission.PBox s c σ)) := by
    have hsub : closure (Submission.PBox s c σ) ⊆ Metric.closedBall c ((5/2) * s) :=
      closure_minimal
        (Subset.trans (Submission.PBox_subset_ball s (le_of_lt hs) c σ) Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall
    exact (Metric.isCompact_iff_isClosed_bounded).mpr
      ⟨isClosed_closure, Metric.isBounded_closedBall.subset hsub⟩
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  let Fco : R3 →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi (fun i : Fin 3 => ![p, q, ζ] i)
  have hFco : ∀ y : R3, Fco y = ![p y, q y, ζ y] := by
    intro y; funext i; fin_cases i <;> simp [Fco]
  let Phi : R3 →L[ℝ] R3 := (E.symm : (Fin 3 → ℝ) →L[ℝ] R3).comp Fco
  have hPhi : ∀ y : R3, E (Phi y) = ![p y, q y, ζ y] := by intro y; simp [Phi, hFco]
  have hinj : Function.Injective Phi := by
    intro y y' h
    have h2 : ![p y, q y, ζ y] = ![p y', q y', ζ y'] := by rw [← hPhi y, ← hPhi y', h]
    have hp : p y = p y' := by have := congrFun h2 0; simpa using this
    have hq : q y = q y' := by have := congrFun h2 1; simpa using this
    have hz : ζ y = ζ y' := by have := congrFun h2 2; simpa using this
    have hzero : y - y' = 0 := by
      refine hker (y - y') ?_ ?_ ?_ <;> simp [map_sub, hp, hq, hz]
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective Phi := (LinearMap.injective_iff_surjective).mp hinj
  let e : R3 ≃L[ℝ] R3 := ContinuousLinearEquiv.ofBijective Phi
    (by rw [LinearMap.ker_eq_bot]; exact hinj) (by rw [LinearMap.range_eq_top]; exact hsurj)
  have hee : ∀ y : R3, e y = Phi y :=
    fun y => congrFun (ContinuousLinearEquiv.coeFn_ofBijective Phi _ _) y
  have hEe : ∀ y : R3, E (e y) = ![p y, q y, ζ y] := by intro y; rw [hee y]; exact hPhi y
  let v : R3 := e.symm (E.symm ![0, 0, 1])
  have hvE : E (e v) = ![0, 0, 1] := by simp [v]
  have hEev : ![p v, q v, ζ v] = ![0, 0, 1] := by rw [← hEe v, hvE]
  have hpv : p v = 0 := by have := congrFun hEev 0; simpa using this
  have hqv : q v = 0 := by have := congrFun hEev 1; simpa using this
  have hzv : ζ v = 1 := by have := congrFun hEev 2; simpa using this
  have hker2 : ∀ y : R3, p y = 0 → q y = 0 → y = ζ y • v := by
    intro y hp hq
    have hzero : y - ζ y • v = 0 := by
      refine hker (y - ζ y • v) ?_ ?_ ?_ <;> simp [map_sub, map_smul, hp, hq, hpv, hqv, hzv]
    exact sub_eq_zero.mp hzero
  let J : ℝ × ℝ →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi (fun i : Fin 3 =>
      ![ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ, 0] i)
  have hJ : ∀ w : ℝ × ℝ, J w = ![w.1, w.2, 0] := by
    intro w; funext i; fin_cases i <;> simp [J]
  let gfun : ℝ × ℝ →L[ℝ] R3 :=
    (e.symm : R3 →L[ℝ] R3).comp ((E.symm : (Fin 3 → ℝ) →L[ℝ] R3).comp J)
  have hge : ∀ w : ℝ × ℝ, e (gfun w) = E.symm (J w) := by intro w; simp [gfun]
  have hgE : ∀ w : ℝ × ℝ, E (e (gfun w)) = ![w.1, w.2, 0] := by
    intro w; rw [hge w]; simp [hJ]
  have hgp : ∀ w : ℝ × ℝ, p (gfun w) = w.1 := by
    intro w
    have h := hEe (gfun w)
    rw [hgE w] at h
    have := congrFun h 0
    simpa using this.symm
  have hgq : ∀ w : ℝ × ℝ, q (gfun w) = w.2 := by
    intro w
    have h := hEe (gfun w)
    rw [hgE w] at h
    have := congrFun h 1
    simpa using this.symm
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hzv; norm_num at hzv
  obtain ⟨i0, hi0⟩ : ∃ i : Fin 3, v (σ i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hvne
    apply E.injective
    funext j
    show E v j = 0
    rw [show E v j = v j from rfl]
    simpa using hcon (σ.symm j)
  let Sf : Finset (Fin 3) := Finset.univ.filter (fun i => v (σ i) ≠ 0)
  have hSne : Sf.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩
  have hSfmem : ∀ i : Fin 3, i ∈ Sf ↔ v (σ i) ≠ 0 := by intro i; simp [Sf]
  let hh : Fin 3 → ℝ := fun i => Submission.boxSide i * s
  let si : Fin 3 → ℝ := fun i => if 0 < v (σ i) then 1 else -1
  let Bi : Fin 3 → ℝ × ℝ → ℝ := fun i w =>
    (si i * hh i - ((gfun w) (σ i) - c (σ i))) / (v (σ i))
  have Bi_eq : ∀ (i : Fin 3) (w : ℝ × ℝ), Bi i w =
      (si i * hh i - ((gfun w) (σ i) - c (σ i))) / (v (σ i)) := fun i w => rfl
  have si_eq : ∀ i : Fin 3, si i = if 0 < v (σ i) then (1:ℝ) else -1 := fun i => rfl
  let tstar : ℝ × ℝ → ℝ := fun w => Sf.inf' hSne (fun i => Bi i w)
  have tstar_eq : ∀ w : ℝ × ℝ, tstar w = Sf.inf' hSne (fun i => Bi i w) := fun w => rfl
  let F : ℝ × ℝ → ℝ := fun w => ζ (gfun w) + tstar w
  have F_eq : ∀ w : ℝ × ℝ, F w = ζ (gfun w) + tstar w := fun w => rfl
  have hBcont : ∀ i : Fin 3, Continuous (Bi i) := by
    intro i
    have h1 : Continuous (fun w : ℝ × ℝ => (gfun w) (σ i)) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ i)).comp gfun.continuous
    show Continuous (fun w : ℝ × ℝ =>
      (si i * hh i - ((gfun w) (σ i) - c (σ i))) / (v (σ i)))
    exact ((continuous_const.sub (h1.sub continuous_const)).div_const _)
  have hFcont : Continuous F := by
    have hinf : Continuous (fun w : ℝ × ℝ => Sf.inf' hSne (fun i => Bi i w)) :=
      Continuous.finset_inf'_apply hSne (fun i _ => hBcont i)
    show Continuous (fun w : ℝ × ℝ => ζ (gfun w) + Sf.inf' hSne (fun i => Bi i w))
    exact (ζ.comp gfun).continuous.add hinf
  have key : ∀ w ∈ {w : ℝ × ℝ | ∃ y ∈ closure (Submission.PBox s c σ), p y = w.1 ∧ q y = w.2},
      fibreMax ζ p q (closure (Submission.PBox s c σ)) w = F w := by
    intro w hw
    obtain ⟨y0, hy0X, hy0p, hy0q⟩ := hw
    have h1 : p (y0 - gfun w) = 0 := by rw [map_sub, hy0p, hgp w, sub_self]
    have h2 : q (y0 - gfun w) = 0 := by rw [map_sub, hy0q, hgq w, sub_self]
    have hdecomp : y0 = gfun w + ζ (y0 - gfun w) • v := by
      have h3 := hker2 (y0 - gfun w) h1 h2
      rw [← h3]; abel
    have ht0mem : ∀ i : Fin 3,
        |(gfun w) (σ i) + ζ (y0 - gfun w) * (v (σ i)) - c (σ i)| ≤ hh i := by
      intro i
      have hXi := (hXbox y0).mp hy0X i
      have hcoord : y0 (σ i) - c (σ i) =
          (gfun w) (σ i) + ζ (y0 - gfun w) * (v (σ i)) - c (σ i) := by
        have h4 : y0 (σ i) = (gfun w) (σ i) + ζ (y0 - gfun w) * (v (σ i)) := by
          conv_lhs => rw [hdecomp]
          simp
        rw [h4]
      rwa [hcoord] at hXi
    have htstar := tstar_eq w
    have htle : ∀ (i : Fin 3), i ∈ Sf → ∀ t : ℝ,
        |(gfun w) (σ i) + t * (v (σ i)) - c (σ i)| ≤ hh i → t ≤ Bi i w := by
      intro i hi t hmem
      have hVi : v (σ i) ≠ 0 := (hSfmem i).mp hi
      rw [Bi_eq]
      rcases lt_or_gt_of_ne hVi with hneg | hpos
      · have hsi : si i = -1 := by rw [si_eq i]; exact if_neg (not_lt.mpr (le_of_lt hneg))
        rw [hsi, neg_one_mul, le_div_iff_of_neg hneg]
        have := (abs_le.mp hmem).1
        linarith
      · have hsi : si i = 1 := by rw [si_eq i]; exact if_pos hpos
        rw [hsi, one_mul, le_div_iff₀ hpos]
        have := (abs_le.mp hmem).2
        linarith
    have ht0le : ζ (y0 - gfun w) ≤ tstar w := by
      rw [htstar]
      refine Finset.le_inf' hSne (fun i => Bi i w) ?_
      intro i hi
      exact htle i hi _ (ht0mem i)
    have hystarX : gfun w + tstar w • v ∈ closure (Submission.PBox s c σ) := by
      rw [hXbox]
      intro i
      have hcoord : (gfun w + tstar w • v) (σ i) - c (σ i) =
          (gfun w) (σ i) + tstar w * (v (σ i)) - c (σ i) := by
        have h4 : (gfun w + tstar w • v) (σ i) = (gfun w) (σ i) + tstar w * (v (σ i)) := by
          simp
        rw [h4]
      rw [hcoord]
      by_cases hi : i ∈ Sf
      · have hVi : v (σ i) ≠ 0 := (hSfmem i).mp hi
        have hleB : tstar w ≤ Bi i w := by
          rw [htstar]; exact Finset.inf'_le (fun j => Bi j w) hi
        have hupper0 := (abs_le.mp (ht0mem i)).2
        have hlower0 := (abs_le.mp (ht0mem i)).1
        rw [abs_le]
        constructor
        · rcases lt_or_gt_of_ne hVi with hneg | hpos
          · have hsi : si i = -1 := by rw [si_eq i]; exact if_neg (not_lt.mpr (le_of_lt hneg))
            rw [Bi_eq, hsi, neg_one_mul] at hleB
            have := (le_div_iff_of_neg hneg).mp hleB
            linarith
          · have : ζ (y0 - gfun w) * (v (σ i)) ≤ tstar w * (v (σ i)) := by nlinarith
            linarith
        · rcases lt_or_gt_of_ne hVi with hneg | hpos
          · have : tstar w * (v (σ i)) ≤ ζ (y0 - gfun w) * (v (σ i)) := by nlinarith
            linarith
          · have hsi : si i = 1 := by rw [si_eq i]; exact if_pos hpos
            rw [Bi_eq, hsi, one_mul] at hleB
            have := (le_div_iff₀ hpos).mp hleB
            linarith
      · have hVi0 : v (σ i) = 0 := by
          by_contra hc; exact hi ((hSfmem i).mpr hc)
        have hmem0 := ht0mem i
        rw [hVi0, mul_zero, add_zero] at hmem0
        rw [hVi0, mul_zero, add_zero]
        exact hmem0
    have hystarp : p (gfun w + tstar w • v) = w.1 := by
      simp [map_add, map_smul, hgp w, hpv]
    have hystarq : q (gfun w + tstar w • v) = w.2 := by
      simp [map_add, map_smul, hgq w, hqv]
    have hystarz : ζ (gfun w + tstar w • v) = F w := by
      rw [F_eq]
      simp [map_add, map_smul, hzv]
    have hbdd : BddAbove (ζ '' {y ∈ closure (Submission.PBox s c σ) | p y = w.1 ∧ q y = w.2}) :=
      (hXcpt.image ζ.continuous).bddAbove.mono (Set.image_mono (fun y hy => hy.1))
    have hle : fibreMax ζ p q (closure (Submission.PBox s c σ)) w ≤ F w := by
      rw [fibreMax]
      refine csSup_le ⟨ζ y0, y0, ⟨hy0X, hy0p, hy0q⟩, rfl⟩ ?_
      rintro z ⟨y, ⟨hyX, hyp, hyq⟩, rfl⟩
      have h1' : p (y - gfun w) = 0 := by rw [map_sub, hyp, hgp w, sub_self]
      have h2' : q (y - gfun w) = 0 := by rw [map_sub, hyq, hgq w, sub_self]
      have hdec : y = gfun w + ζ (y - gfun w) • v := by
        have h3 := hker2 (y - gfun w) h1' h2'
        rw [← h3]; abel
      have hmem : ∀ i : Fin 3,
          |(gfun w) (σ i) + ζ (y - gfun w) * (v (σ i)) - c (σ i)| ≤ hh i := by
        intro i
        have hXi := (hXbox y).mp hyX i
        have hcoord : y (σ i) - c (σ i) =
            (gfun w) (σ i) + ζ (y - gfun w) * (v (σ i)) - c (σ i) := by
          have h4 : y (σ i) = (gfun w) (σ i) + ζ (y - gfun w) * (v (σ i)) := by
            conv_lhs => rw [hdec]
            simp
          rw [h4]
        rwa [hcoord] at hXi
      have hleT : ζ (y - gfun w) ≤ tstar w := by
        rw [htstar]
        refine Finset.le_inf' hSne (fun i => Bi i w) ?_
        intro i hi
        exact htle i hi _ (hmem i)
      have hzy : ζ y = ζ (gfun w) + ζ (y - gfun w) := by
        conv_lhs => rw [hdec]
        simp [map_add, map_smul, hzv]
      have hFw : F w = ζ (gfun w) + tstar w := F_eq w
      rw [hzy, hFw]
      linarith
    have hge : F w ≤ fibreMax ζ p q (closure (Submission.PBox s c σ)) w := by
      rw [fibreMax]
      refine le_csSup hbdd ⟨gfun w + tstar w • v, ⟨hystarX, hystarp, hystarq⟩, hystarz⟩
    exact le_antisymm hle hge
  exact hFcont.continuousOn.congr key

end

end Work.Drive.Mono
