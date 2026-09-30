import Mathlib
import Submission.Work.Pi6.MSS.evSaux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Injectivity half of `evS_bij`: the kernel of `evZ` lies in the denominator

`evZ : Z_1^{s,n} ⟶ Hom_𝕜(H_n(gr_s), 𝕜)` evaluates a `1`-cocycle of the Serre cochain filtration on
the cycles of the s-th graded piece of the Serre chain filtration.  Here we prove that a
`1`-cocycle which evaluates to zero on homology lies in `F^{s+1} + d(F^s) = pDen`, i.e. that `evZ`
kills nothing more than the denominator of `E_1^s`.

The argument: `Ψ : gr_s^n → 𝕜`, `z ↦ x(incl (grSecX z))`, is a functional on the graded piece which
kills cycles (by hypothesis) and boundaries (since `x` is a cocycle); hence it factors through the
differential, `Ψ = q' ∘ d`.  Lift `q'` to `x' ∈ F^s C^{n-1}` (`evTheta_surj`), so that
`x - d x'` still kills the chosen cycle representatives; by `mem_F_succ_of_kills_sec` it lies in
`F^{s+1}`, and `d x' ∈ F^s ∩ d(F^s) = B_1^s`, which is exactly the assertion.

The auxiliary lemmas `inclL_d_pred(_apply)`, `cochainFun_dPrev` and `dPrev_mem_F` handle the
`ℕ`-truncation of the differentials in degree `0`.
-/

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

lemma dPrev_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) :
    (Wc 𝕜 p).dPrev 0 = 0 := by
  rw [CohFilt.dPrev, show (0:ℕ) - 1 = 0 from rfl]
  exact congrArg ModuleCat.Hom.hom
    (HomologicalComplex.shape (Wc 𝕜 p).C 0 0 (by simp [ComplexShape.up]))

/-- The `dPrev` of a cochain of `F^s` lies in `F^s` in the next degree. -/
lemma dPrev_mem_F (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (y : (Wc 𝕜 p).C.X (n-1)) (hy : y ∈ (Wc 𝕜 p).F s (n-1)) :
    ((Wc 𝕜 p).dPrev n) y ∈ (Wc 𝕜 p).F s n := by
  cases n with
  | zero =>
    rw [dPrev_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | succ k =>
    show ((Wc 𝕜 p).d k) y ∈ (Wc 𝕜 p).F s (k+1)
    exact (Wc 𝕜 p).F_leib s k y hy

/-- The evaluation of `dPrev` in terms of the chain differential. -/
lemma cochainFun_dPrev (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ)
    (x : (Wc 𝕜 p).C.X (n-1)) (v : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n) :
    (cochainFun 𝕜 p n (((Wc 𝕜 p).dPrev n) x)) v =
      (cochainFun 𝕜 p (n-1) x)
        (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d n (n-1)).hom v) := by
  cases n with
  | zero =>
    have hbmap2 : ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d 0 0) = 0 :=
      HomologicalComplex.shape (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)) 0 0
        (by simp [ComplexShape.down])
    have hzero : ((Wc 𝕜 p).dPrev 0) x = 0 := by
      rw [dPrev_zero, LinearMap.zero_apply]
    have hzero2 : (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d 0 0).hom v) = 0 := by
      rw [hbmap2, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hzero, hzero2, map_zero]
    exact LinearMap.zero_apply v
  | succ k =>
    exact (Wc_d_apply_applied 𝕜 p k x v).symm

/-- The projection `grPi` is a chain map. -/
lemma grPi_d (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) (v : (Cc 𝕜 p (s+1)).X n) :
    grPi 𝕜 p s (n-1) (((Cc 𝕜 p (s+1)).d n (n-1)).hom v) =
      ((Kg 𝕜 p s).d n (n-1)).hom (grPi 𝕜 p s n v) := by
  have h := congrArg (fun (g : (Cc 𝕜 p (s+1)).X n ⟶ (Kg 𝕜 p s).X (n-1)) => g.hom v)
    ((Kgπ 𝕜 p s).comm n (n-1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- The kernel of the projection is the image of the inclusion of the previous step. -/
lemma grPi_ker_eq (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    LinearMap.ker (grPi 𝕜 p s n) = LinearMap.range (grIncl 𝕜 p s n).hom := by
  refine le_antisymm ?_ ?_
  · rw [grPi_ker]
    exact ker_Kgπ_le_grIncl 𝕜 p s n
  · rintro x ⟨b, rfl⟩
    exact grPi_grIncl 𝕜 p s n b

/-- The chosen section is a chain map up to the chains of the previous step. -/
lemma grSecX_d_mem (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) (z : (Kg 𝕜 p s).X n) :
    grSecX 𝕜 p s (n-1) (((Kg 𝕜 p s).d n (n-1)).hom z) -
      ((Cc 𝕜 p (s+1)).d n (n-1)).hom (grSecX 𝕜 p s n z) ∈
        LinearMap.range (grIncl 𝕜 p s (n-1)).hom := by
  rw [← grPi_ker_eq]
  rw [LinearMap.mem_ker, map_sub]
  have h1 : grPi 𝕜 p s (n-1)
      (grSecX 𝕜 p s (n-1) (((Kg 𝕜 p s).d n (n-1)).hom z)) =
      ((Kg 𝕜 p s).d n (n-1)).hom z := grPi_grSecX 𝕜 p s (n-1) _
  have h2 : grPi 𝕜 p s (n-1)
      (((Cc 𝕜 p (s+1)).d n (n-1)).hom (grSecX 𝕜 p s n z)) =
      ((Kg 𝕜 p s).d n (n-1)).hom z := by
    rw [grPi_d, grPi_grSecX]
  rw [h1, h2, sub_self]



/-- The inclusion `inclL` is a chain map, with the differential indexed uniformly by `n`
(the statement for `n = 0` being trivial). -/
lemma inclL_d_pred (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) :
    (inclL 𝕜 p k).f n ≫ (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d n (n-1) =
      (Cc 𝕜 p k).d n (n-1) ≫ (inclL 𝕜 p k).f (n-1) := by
  cases n with
  | zero =>
    have h1 : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d 0 (0-1) = 0 :=
      HomologicalComplex.shape (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)) 0 0
        (by simp [ComplexShape.down])
    have h2 : (Cc 𝕜 p k).d 0 (0-1) = 0 :=
      HomologicalComplex.shape (Cc 𝕜 p k) 0 0 (by simp [ComplexShape.up])
    rw [h1, h2]
    simp
  | succ m =>
    exact inclL_d 𝕜 p k m

lemma inclL_d_pred_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ)
    (v : (Cc 𝕜 p k).X n) :
    ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d n (n-1)).hom
        (((inclL 𝕜 p k).f n).hom v) =
      ((inclL 𝕜 p k).f (n-1)).hom (((Cc 𝕜 p k).d n (n-1)).hom v) := by
  have h := congrArg (fun (g : (Cc 𝕜 p k).X n ⟶
      (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (n-1)) => g.hom v)
    (inclL_d_pred 𝕜 p k n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at h
  exact h

/-- The kernel of `evZ` is contained in the denominator of the first page. -/
theorem evZkerle_proof (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n) :
    LinearMap.ker (evZ 𝕜 p s n hann) ≤
      (pDen 𝕜 (Wc 𝕜 p) 1 s n).comap (pZ 𝕜 (Wc 𝕜 p) 1 s n).subtype := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_comap, mem_pDen_one]
  obtain ⟨hxF, _hxd⟩ := (mem_pZ_one (Wc 𝕜 p) s n x.1).mp x.2
  set Φ : ↥((Kg 𝕜 p s).X n) →ₗ[𝕜] 𝕜 :=
    (cochainFun 𝕜 p n x.1).comp (((inclL 𝕜 p (s+1)).f n).hom.comp (grSecX 𝕜 p s n))
    with hΦdef
  have hΦz : ∀ z : ↥((Kg 𝕜 p s).X n),
      Φ z = (cochainFun 𝕜 p n x.1) (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) := by
    intro z
    rw [hΦdef, LinearMap.comp_apply, LinearMap.comp_apply]
  have hΦkill : LinearMap.ker ((Kg 𝕜 p s).d n (n-1)).hom ≤ LinearMap.ker Φ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have h1 := LinearMap.congr_fun hx ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) n).mkQ ⟨z, hz⟩)
    rw [evZ_apply, LinearMap.zero_apply] at h1
    exact (hΦz z).trans h1
  obtain ⟨q', hq'⟩ := exists_comp_of_ker_le ((Kg 𝕜 p s).d n (n-1)).hom Φ hΦkill
  obtain ⟨x', hx'⟩ := evTheta_surj 𝕜 p s (n-1) hann q'
  have hx'q : ∀ z : ↥((Kg 𝕜 p s).X (n-1)),
      (cochainFun 𝕜 p (n-1) x'.1)
        (((inclL 𝕜 p (s+1)).f (n-1)).hom (grSecX 𝕜 p s (n-1) z)) = q' z := by
    intro z
    have h := LinearMap.congr_fun hx' z
    rwa [evTheta_apply] at h
  have hq'z : ∀ z : ↥((Kg 𝕜 p s).X n), q' (((Kg 𝕜 p s).d n (n-1)).hom z) = Φ z := by
    intro z
    have h := LinearMap.congr_fun hq' z
    rwa [LinearMap.comp_apply] at h
  set y : (Wc 𝕜 p).C.X n := x.1 - ((Wc 𝕜 p).dPrev n) x'.1 with hydef
  have hyF : y ∈ (Wc 𝕜 p).F s n := by
    rw [hydef]
    exact Submodule.sub_mem _ hxF (dPrev_mem_F 𝕜 p s n x'.1 x'.2)
  have hykill : ∀ z : (Kg 𝕜 p s).X n,
      (cochainFun 𝕜 p n y) (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) = 0 := by
    intro z
    obtain ⟨b, hb⟩ := grSecX_d_mem 𝕜 p s n z
    have hsplit : ((Cc 𝕜 p (s+1)).d n (n-1)).hom (grSecX 𝕜 p s n z) =
        grSecX 𝕜 p s (n-1) (((Kg 𝕜 p s).d n (n-1)).hom z) -
          (grIncl 𝕜 p s (n-1)).hom b := by
      rw [hb]
      abel
    change (cochainFun 𝕜 p n (x.1 - ((Wc 𝕜 p).dPrev n) x'.1))
        (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) = 0
    change ((cochainFun 𝕜 p n x.1) -
        (cochainFun 𝕜 p n (((Wc 𝕜 p).dPrev n) x'.1)))
        (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) = 0
    rw [LinearMap.sub_apply, ← hΦz z, cochainFun_dPrev, inclL_d_pred_apply 𝕜 p (s+1) n
      (grSecX 𝕜 p s n z), hsplit, map_sub, map_sub, hx'q,
      kills_grIncl 𝕜 p s (n-1) hann x'.1 x'.2 b, sub_zero, hq'z z, sub_self]
  have hyF1 : y ∈ (Wc 𝕜 p).F (s+1) n :=
    mem_F_succ_of_kills_sec 𝕜 p s n hann y hyF hykill
  refine ⟨y, hyF1, ((Wc 𝕜 p).dPrev n) x'.1, ?_, ?_⟩
  · rw [pB_one_eq]
    exact Submodule.mem_map.mpr ⟨x'.1, x'.2, rfl⟩
  · rw [hydef]
    abel

end

end Work.Pi6.MSS
