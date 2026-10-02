import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeMap
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.PlaneCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

variable {k m : ℕ}

/-! ## `probeCy` kills the fixed complement, `probeUx` reads it -/

theorem probeCy_tailVec (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (l : Fin (k - 2)) :
    probeCy k m hk hm (probeTailVec k m hk l) = 0 := by
  rw [probeCy_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [probeTailVec,
    single_coord_ne (a := probeTailIdx k m hk l) (b := probeAmbIdx k m hk hm i)
      (probeAmbIdx_ne_probeTailIdx k m hk hm i l), zero_smul]

theorem probeCy_tailComb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (t : Amb (k - 2)) :
    probeCy k m hk hm (probeTailComb k m hk t) = 0 := by
  rw [probeTailComb_apply, map_sum]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  rw [map_smul, probeCy_tailVec, smul_zero]

/-! ## The orthogonal projection onto `probeEmb`'s range plus the complement -/

/-- The projection onto the coordinates covered by `probeEmb` and by the fixed complement frame. -/
noncomputable def probeProj (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Amb (k + m) →L[ℝ] Amb (k + m) :=
  (probeEmb k m hk hm).comp (probeCy k m hk hm)
    + (probeTailComb k m hk).comp (probeUx k m hk)

theorem probeProj_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (w : Amb (k + m)) :
    probeProj k m hk hm w = probeEmb k m hk hm (probeCy k m hk hm w)
      + probeTailComb k m hk (probeUx k m hk w) := by
  simp only [probeProj, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]

theorem probeProj_probeEmb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (y : Amb 6) :
    probeProj k m hk hm (probeEmb k m hk hm y) = probeEmb k m hk hm y := by
  simp only [probeProj_apply, probeCy_probeEmb, probeUx_probeEmb, map_zero, add_zero]

theorem probeProj_tailComb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (t : Amb (k - 2)) :
    probeProj k m hk hm (probeTailComb k m hk t) = probeTailComb k m hk t := by
  simp only [probeProj_apply, probeCy_tailComb, probeUx_tailComb, map_zero, zero_add]

theorem probeProj_eq_self (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) {w : Amb (k + m)}
    (hw : w ∈ Submodule.span ℝ (Set.range (probeEmb k m hk hm)
      ∪ Set.range (probeTailComb k m hk))) :
    probeProj k m hk hm w = w := by
  refine Submodule.span_induction (p := fun z _ => probeProj k m hk hm z = z) ?_ ?_ ?_ ?_ hw
  · rintro - (⟨y, rfl⟩ | ⟨t, rfl⟩)
    · exact probeProj_probeEmb k m hk hm y
    · exact probeProj_tailComb k m hk hm t
  · simp
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro c a _ ha
    rw [map_smul, ha]

/-! ## The plane of `probeSigma x` and the frame -/

/-- The `SO(k)`-action on frames preserves the span. -/
theorem span_soActFun_subset (k m : ℕ) (A : SOk k) (f : Fin k → Amb (k + m)) :
    Submodule.span ℝ (Set.range (soActFun A.1 f)) ≤ Submodule.span ℝ (Set.range f) := by
  refine Submodule.span_le.mpr ?_
  rintro - ⟨j, rfl⟩
  rw [soActFun]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩))

/-- The `SO(k)`-action on frames preserves the span. -/
theorem span_soActFun (k m : ℕ) (A : SOk k) (f : Fin k → Amb (k + m)) :
    Submodule.span ℝ (Set.range (soActFun A.1 f)) = Submodule.span ℝ (Set.range f) := by
  have hAA : ∀ i l : Fin k, (∑ j : Fin k, A.1 i j * A.1 l j) = if i = l then 1 else 0 := by
    intro i l
    have h := congrFun (congrFun A.2.mul_transpose_self i) l
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  have hback : ∀ i : Fin k, f i = ∑ j : Fin k, A.1 i j • soActFun A.1 f j := by
    intro i
    have h1 : (∑ j : Fin k, A.1 i j • soActFun A.1 f j)
        = ∑ j : Fin k, ∑ l : Fin k, (A.1 i j * A.1 l j) • f l := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [soActFun, Finset.smul_sum]
      exact Finset.sum_congr rfl (fun l _ => by rw [mul_smul])
    have h2 : (∑ j : Fin k, ∑ l : Fin k, (A.1 i j * A.1 l j) • f l)
        = ∑ l : Fin k, (∑ j : Fin k, A.1 i j * A.1 l j) • f l := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun l _ => (Finset.sum_smul).symm)
    have h3 : (∑ l : Fin k, (∑ j : Fin k, A.1 i j * A.1 l j) • f l) = f i := by
      rw [Finset.sum_eq_single i]
      · rw [hAA i i, if_pos rfl, one_smul]
      · intro l _ hl
        rw [hAA i l, if_neg (fun hc => hl hc.symm), zero_smul]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1, h2, h3]
  refine le_antisymm (span_soActFun_subset k m A f) ?_
  have hcomp : soActFun A.transpose.1 (soActFun A.1 f) = f := by
    funext i
    rw [show soActFun A.transpose.1 (soActFun A.1 f) i
        = ∑ j : Fin k, A.1 i j • soActFun A.1 f j from by
      rw [soActFun]
      exact Finset.sum_congr rfl (fun j _ => by
        show A.1.transpose j i • soActFun A.1 f j = A.1 i j • soActFun A.1 f j
        rw [Matrix.transpose_apply])]
    exact (hback i).symm
  have hsub := span_soActFun_subset k m A.transpose (soActFun A.1 f)
  rwa [hcomp] at hsub

/-- **The plane of `probeSigma x` is spanned by the explicit probe frame** (for `x` in the chart
`i`). -/
theorem memPlane_span_frame (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) {w : Amb (k + m)}
    (hw : memPlane (probeSigma k m hk hm x) w) :
    w ∈ Submodule.span ℝ (Set.range (probeFrameRep k m hk hm (Work.Gen.uVec i x))) := by
  obtain ⟨f, hf, hwspan⟩ := hw
  have hmk := probeSigma_apply_uVec k m hk hm i x hx
  have hEq : (Quotient.mk'' f : OG k m) = Quotient.mk''
      (probeStiefelRep k m hk hm (Work.Gen.uVec i x) (Work.Gen.uVec_ne_zero i x)) := by
    rw [hf, hmk]
    rfl
  obtain ⟨A, hA⟩ := Quotient.exact hEq
  have hspan_eq : Submodule.span ℝ (Set.range (probeFrameRep k m hk hm (Work.Gen.uVec i x)))
      = Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
    have h1 : probeFrameRep k m hk hm (Work.Gen.uVec i x) = soActFun A.1 f.1 :=
      congrArg Subtype.val hA
    rw [h1, span_soActFun k m A]
  rw [hspan_eq]
  exact hwspan

/-- Every vector of the probe frame lies in the span of the images of `probeEmb` and of the fixed
complement frame. -/
theorem probeFrameRep_mem_bigSpan (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) :
    ∀ w ∈ Set.range (probeFrameRep k m hk hm v),
      w ∈ Submodule.span ℝ (Set.range (probeEmb k m hk hm) ∪ Set.range (probeTailComb k m hk)) := by
  rintro - ⟨j, rfl⟩
  obtain ⟨p, rfl⟩ := (probeSplit k hk).surjective j
  rcases p with a | l
  · rw [probeFrameRep_inl]
    fin_cases a
    · show probePairVec k m hk hm v 0 ∈ _
      rw [probePairVec_zero]
      exact Submodule.subset_span (Or.inl ⟨cxE (cxUnit v), rfl⟩)
    · show probePairVec k m hk hm v 1 ∈ _
      rw [show probePairVec k m hk hm v 1
          = -(probeEmb k m hk hm (cxE (Complex.I • cxUnit v))) from
        probePairVec_one k m hk hm v]
      exact Submodule.neg_mem _ (Submodule.subset_span
        (Or.inl ⟨cxE (Complex.I • cxUnit v), rfl⟩))
  · rw [probeFrameRep_inr, probeTailVec_eq_tailComb]
    exact Submodule.subset_span (Or.inr ⟨EuclideanSpace.single (𝕜 := ℝ) l 1, rfl⟩)

theorem memPlane_bigSpan (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) {w : Amb (k + m)}
    (hw : memPlane (probeSigma k m hk hm x) w) :
    w ∈ Submodule.span ℝ (Set.range (probeEmb k m hk hm) ∪ Set.range (probeTailComb k m hk)) :=
  (Submodule.span_le.mpr (probeFrameRep_mem_bigSpan k m hk hm (Work.Gen.uVec i x)))
    (memPlane_span_frame k m hk hm i x hx hw)

/-- **A vector of the plane of `probeSigma x` is the sum of its `probeEmb`-part and its
complement-part.** -/
theorem probePlaneDecomp (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) (w : Amb (k + m))
    (hw : memPlane (probeSigma k m hk hm x) w) :
    w = probeEmb k m hk hm (probeCy k m hk hm w)
        + probeTailComb k m hk (probeUx k m hk w) :=
  (probeProj_eq_self k m hk hm (memPlane_bigSpan k m hk hm i x hx hw)).symm.trans
    (probeProj_apply k m hk hm w)

/-! ## The line of the probe plane -/

theorem span_re_add_smul_le (u : E3) (r : ℝ) :
    Submodule.span ℝ {r • u, r • (Complex.I • u)}
      ≤ (Submodule.span ℂ {r • u}).restrictScalars ℝ := by
  refine Submodule.span_le.mpr ?_
  rintro z (rfl | rfl)
  · exact Submodule.subset_span rfl
  · rw [smul_comm]
    exact Submodule.smul_mem _ Complex.I (Submodule.subset_span rfl)

theorem real_smul_eq_coe_smul (r : ℝ) (z : E3) : r • z = ((r : ℂ)) • z := by
  simpa using (IsScalarTower.smul_assoc r (1 : ℂ) z).symm

theorem cxE_symm_mem_span_iff (u : E3) {y : Amb 6} :
    y ∈ Submodule.span ℝ {cxE u, cxE (Complex.I • u)}
      → cxE.symm y ∈ Submodule.span ℝ {u, Complex.I • u} := by
  intro hy
  let g : Amb 6 →ₗ[ℝ] E3 := cxE.symm
  have hgu : g (cxE u) = u := by simp [g]
  have hgI : g (cxE (Complex.I • u)) = Complex.I • u := by simp [g]
  have h1 : cxE.symm y ∈ Submodule.map g (Submodule.span ℝ {cxE u, cxE (Complex.I • u)}) :=
    Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  rw [Submodule.map_span] at h1
  have hset : g '' ({cxE u, cxE (Complex.I • u)} : Set (Amb 6)) = {u, Complex.I • u} := by
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with hw | hw
      · left
        rw [← hwz, hw, hgu]
      · right
        rw [← hwz, hw, hgI]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨cxE u, by simp, by rw [hz, hgu]⟩
      · exact ⟨cxE (Complex.I • u), by simp, by rw [hz, hgI]⟩
  rwa [hset] at h1

theorem probeCy_mem_span_line (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    {w : Amb (k + m)}
    (hw : w ∈ Submodule.span ℝ (Set.range (probeFrameRep k m hk hm v))) :
    probeCy k m hk hm w ∈ Submodule.span ℝ {cxE (cxUnit v), cxE (Complex.I • cxUnit v)} := by
  refine Submodule.span_induction
    (p := fun z _ => probeCy k m hk hm z
      ∈ Submodule.span ℝ {cxE (cxUnit v), cxE (Complex.I • cxUnit v)})
    (fun u hu => ?_) (by simp) (fun a b _ _ ha hb => ?_) (fun c a _ ha => ?_) hw
  · obtain ⟨j, rfl⟩ := hu
    obtain ⟨p, rfl⟩ := (probeSplit k hk).surjective j
    rcases p with a | l
    · rw [probeFrameRep_inl]
      fin_cases a
      · show probeCy k m hk hm (probePairVec k m hk hm v 0) ∈ _
        rw [probePairVec_zero, probeCy_probeEmb]
        exact Submodule.subset_span (Or.inl rfl)
      · show probeCy k m hk hm (probePairVec k m hk hm v 1) ∈ _
        rw [show probePairVec k m hk hm v 1
            = -(probeEmb k m hk hm (cxE (Complex.I • cxUnit v))) from
          probePairVec_one k m hk hm v, map_neg, probeCy_probeEmb]
        exact Submodule.neg_mem _ (Submodule.subset_span (Or.inr rfl))
    · rw [probeFrameRep_inr, probeCy_tailVec]
      exact Submodule.zero_mem _
  · rw [map_add]
    exact Submodule.add_mem _ ha hb
  · have hc : probeCy k m hk hm (c • a) = c • probeCy k m hk hm a := map_smul _ c a
    rw [hc]
    exact Submodule.smul_mem _ _ ha

/-- **The `probeEmb`-part of a vector of the plane of `probeSigma x` lies in the complex line of the
point `x`.** -/
theorem probePlaneLine (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) (w : Amb (k + m))
    (hw : memPlane (probeSigma k m hk hm x) w) :
    cxE.symm (probeCy k m hk hm w)
      ∈ Submodule.span ℂ {cxOf (Work.Gen.uVec i x)} := by
  have hv : Work.Gen.uVec i x ≠ 0 := Work.Gen.uVec_ne_zero i x
  have hcy := probeCy_mem_span_line k m hk hm (Work.Gen.uVec i x) hv
    (memPlane_span_frame k m hk hm i x hx hw)
  have hsym := cxE_symm_mem_span_iff (cxUnit (Work.Gen.uVec i x)) hcy
  have hle : Submodule.span ℝ {cxUnit (Work.Gen.uVec i x),
        Complex.I • cxUnit (Work.Gen.uVec i x)}
      ≤ (Submodule.span ℂ {cxOf (Work.Gen.uVec i x)}).restrictScalars ℝ := by
    refine Submodule.span_le.mpr ?_
    rintro z (rfl | rfl)
    · show cxUnit (Work.Gen.uVec i x) ∈ Submodule.span ℂ {cxOf (Work.Gen.uVec i x)}
      rw [cxUnit, real_smul_eq_coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · show Complex.I • cxUnit (Work.Gen.uVec i x) ∈ Submodule.span ℂ {cxOf (Work.Gen.uVec i x)}
      rw [cxUnit, smul_comm, real_smul_eq_coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
  exact hle hsym

/-! ## The inverse of the chart evaluation -/

theorem toECoordAt_evalChartO (S : ChartIdx k m) (P : OG k m) (hPS : P ∈ baseSet S) (v : Amb k) :
    toECoordAt S P (evalChartO S ⟨P, hPS⟩ v) = v := by
  obtain ⟨f, hfmk⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = P := Quotient.exists_rep _
  have hfc : f ∈ Work.ThomBordism.Grassmann.chartSet S :=
    (mem_baseSet_iff S f).mp (hfmk ▸ hPS)
  have hspec := evalChart_spec S ⟨P, hPS⟩ f hfc hfmk.symm (matLin (orientMat S P) v)
  rw [evalChartO, hspec, toECoordAt,
    show WithLp.toLp 2 (coordProj S (WithLp.ofLp (coordEval S f (matLin (orientMat S P) v))))
        = WithLp.toLp 2 (WithLp.ofLp (matLin (orientMat S P) v)) from by
      rw [coordProj_coordEval S f (matLin (orientMat S P) v) hfc],
    WithLp.toLp_ofLp]
  exact orientMat_involutive S P hPS v

end

end Work.ThomBordism.Grassmann
