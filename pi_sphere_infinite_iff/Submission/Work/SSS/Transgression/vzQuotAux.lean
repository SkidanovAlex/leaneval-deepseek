import Mathlib
import Submission.Work.SSS.FibreColDefs

/-!
# Chain-level naturality for a saturated filtration, and the kernel of `projQ`

Auxiliary lemmas for the transgression into the left column of the Serre spectral sequence
(`Work.SSS.Transgression.vzQuotSurj`).

* `Cincl_dFs`, `Finc_dFs`, `Cincl_Finc`, `dFs_dFs` : the filtration terms form a diagram of chain
  complexes, so the comparison maps `Finc ξ s' s h n` and the inclusions `Cincl ξ s n` commute with
  the differentials, and consecutive differentials compose to zero.
* `projQ_succ_eq_zero_iff` : the kernel of the projection `(F_s)_{n} → (grF ξ s)_n` is the image of
  `F_{s-1} → F_s` (exactness of `F_{s-1} → F_s → F_s/F_{s-1}` in degree `n`).
* `dC_dC` : two consecutive differentials of `C` compose to zero, in the form used with `Zof`.
-/

set_option autoImplicit false

attribute [-instance] AddCommGroup.toIntModule

namespace Work.SSS.Transgression

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-! ## Naturality of the comparison maps -/

/-- The inclusion `F_s ⊆ C` commutes with the differentials. -/
theorem Cincl_dFs (ξ : Filtration C) (s a b : ℕ) :
    (Cincl ξ s b).comp (dFs ξ s a b) = (dC C a b).comp (Cincl ξ s a) := by
  have h := HomologicalComplex.Hom.comm (ξ.incl s) a b
  have h' := congrArg ModuleCat.Hom.hom h
  simpa only [Cincl, dFs, dC, ModuleCat.hom_comp] using h'.symm

/-- The inclusion `F_s ⊆ C` commutes with the differentials, on elements. -/
theorem Cincl_dFs_apply (ξ : Filtration C) (s a b : ℕ) (y : (ξ.F.obj s).X a) :
    Cincl ξ s b (dFs ξ s a b y) = dC C a b (Cincl ξ s a y) :=
  congrFun (congrArg DFunLike.coe (Cincl_dFs ξ s a b)) y

/-- The comparison map `F_{s'} → F_s` commutes with the differentials. -/
theorem Finc_dFs (ξ : Filtration C) {s' s : ℕ} (h : s' ≤ s) (a b : ℕ) :
    (Finc ξ s' s h b).comp (dFs ξ s' a b) = (dFs ξ s a b).comp (Finc ξ s' s h a) := by
  have hh := HomologicalComplex.Hom.comm (ξ.F.map (homOfLE h)) a b
  have h'' := congrArg ModuleCat.Hom.hom hh
  simpa only [Finc, dFs, ModuleCat.hom_comp] using h''.symm

/-- The comparison map `F_{s'} → F_s` commutes with the differentials, on elements. -/
theorem Finc_dFs_apply (ξ : Filtration C) {s' s : ℕ} (h : s' ≤ s) (a b : ℕ)
    (y : (ξ.F.obj s').X a) :
    Finc ξ s' s h b (dFs ξ s' a b y) = dFs ξ s a b (Finc ξ s' s h a y) :=
  congrFun (congrArg DFunLike.coe (Finc_dFs ξ h a b)) y

/-- The composite `F_{s'} → F_s → C` is the inclusion of `F_{s'}`. -/
theorem Cincl_Finc (ξ : Filtration C) {s' s : ℕ} (h : s' ≤ s) (b : ℕ) :
    (Cincl ξ s b).comp (Finc ξ s' s h b) = Cincl ξ s' b := by
  have hh := congrArg (fun (g : ξ.F.obj s' ⟶ C) => ModuleCat.Hom.hom (g.f b)) (ξ.compat h)
  simpa only [Cincl, Finc, HomologicalComplex.comp_f, ModuleCat.hom_comp] using hh

/-- The composite `F_{s'} → F_s → C` is the inclusion of `F_{s'}`, on elements. -/
theorem Cincl_Finc_apply (ξ : Filtration C) {s' s : ℕ} (h : s' ≤ s) (b : ℕ)
    (y : (ξ.F.obj s').X b) :
    Cincl ξ s b (Finc ξ s' s h b y) = Cincl ξ s' b y :=
  congrFun (congrArg DFunLike.coe (Cincl_Finc ξ h b)) y

/-- Two consecutive differentials of a filtration term compose to zero. -/
theorem dFs_dFs (ξ : Filtration C) (s a b c : ℕ) :
    (dFs ξ s b c).comp (dFs ξ s a b) = 0 := by
  have h := HomologicalComplex.d_comp_d (ξ.F.obj s) a b c
  have h' := congrArg ModuleCat.Hom.hom h
  simpa only [dFs, ModuleCat.hom_comp, ModuleCat.hom_zero] using h'

/-- Two consecutive differentials of a filtration term compose to zero, on elements. -/
theorem dFs_dFs_apply (ξ : Filtration C) (s a b c : ℕ) (y : (ξ.F.obj s).X a) :
    dFs ξ s b c (dFs ξ s a b y) = 0 :=
  congrFun (congrArg DFunLike.coe (dFs_dFs ξ s a b c)) y

/-- Two consecutive differentials of the ambient complex `C` compose to zero, in the form in which
it is used with `Zof` (the composite `d ∘ d` is zero in degrees `t+1 → t → t-1`). -/
theorem dC_dC (t : ℕ) (u : C.X (t + 1)) : dC C t (t - 1) (dC C (t + 1) t u) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d C (t + 1) t (t - 1))
  exact congrFun (congrArg DFunLike.coe h) u

/-! ## The kernel of the projection onto the graded piece -/

/-- The projection `projQ ξ (k+1) n` onto the graded piece `grF ξ (k+1)` has kernel the image of
the inclusion `F_k → F_{k+1}`: the proof of exactness of `F_k → F_{k+1} → F_{k+1}/F_k` in
degree `n`. -/
theorem projQ_succ_eq_zero_iff (ξ : Filtration C) (k n : ℕ) (x : (ξ.F.obj (k+1)).X n) :
    projQ ξ (k + 1) n x = 0 ↔ ∃ y : (ξ.F.obj k).X n, ((incF ξ.F k).f n).hom y = x := by
  have hS : (ShortComplex.mk (incF ξ.F k) (cokernel.π (incF ξ.F k))
      (cokernel.condition (incF ξ.F k))).Exact := ShortComplex.exact_cokernel _
  have h2 := hS.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h2
  simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map] at h2
  have h3 : LinearMap.ker ((cokernel.π (incF ξ.F k)).f n).hom =
      LinearMap.range ((incF ξ.F k).f n).hom := h2.symm
  show ((cokernel.π (incF ξ.F k)).f n).hom x = 0 ↔ ∃ y, ((incF ξ.F k).f n).hom y = x
  rw [← LinearMap.mem_range, ← h3, LinearMap.mem_ker]

end

end Work.SSS.Transgression
