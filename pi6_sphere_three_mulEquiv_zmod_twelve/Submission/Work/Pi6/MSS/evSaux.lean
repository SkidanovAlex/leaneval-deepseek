import Mathlib
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.coFiltAnn
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Auxiliary lemmas for `Work.Pi6.MSS.evS_bij`

The evaluation map `evS : E_1^{s,n}(p;𝕜) ⟶ Hom_𝕜(H_n(gr_s C_*(E)),𝕜)` of
`Submission/Work/Pi6/MSS/E1Map.lean` is an isomorphism over a field.  This file collects the
ingredients that are shared between the injectivity and the surjectivity halves of the proof:

* `exists_comp_of_injective`, `exists_comp_of_ker_le` — the two elementary extensions of
  functionals over a field;
* `inclL_f_injective`, `exists_cochain_extend` — every functional on the chains of `A_k` extends to
  a cochain of `E`;
* `grPi` — the projection `C_*(A_{s+1}) ⟶ gr_s`, with its domain type spelled as the chains of
  `A_{s+1}` so that composition with the section `grSecX` is transparent;
* `exists_eq_sec_add` — every chain of `A_{s+1}` is the sum of the chosen representative of its
  class in `gr_s` and a chain in `A_s`;
* `mem_F_iff` — membership in the Serre filtration step `F^s`, in terms of killing the chains of
  `A_s`;
* `mem_F_succ_of_kills_sec` — a cochain of `F^s` which kills the chosen cycle representatives of
  `gr_s` lies in `F^{s+1}`;
* `evTheta` (with `evTheta_apply`) and `evTheta_surj` — the restriction map
  `F^s C^n ⟶ Hom_𝕜(gr_s^n, 𝕜)` is surjective;
* `mem_pZ_one`, `mem_pDen_one` — the standard descriptions of `Z_1^s` and of the denominator of
  `E_1^s`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Two elementary extensions of functionals over a field -/

/-- A functional on `M` extends to `N` along an injective linear map. -/
lemma exists_comp_of_injective {𝕜 : Type} [Field 𝕜] {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (f : M →ₗ[𝕜] N) (hf : Function.Injective f) (r : M →ₗ[𝕜] 𝕜) :
    ∃ g : N →ₗ[𝕜] 𝕜, g.comp f = r := by
  let e : M ≃ₗ[𝕜] ↥(LinearMap.range f) := LinearEquiv.ofInjective f hf
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := LinearMap.range f) (r.comp e.symm.toLinearMap)
  refine ⟨g, ?_⟩
  have hfe : (LinearMap.range f).subtype.comp e.toLinearMap = f := by
    ext x
    show (e x).1 = f x
    exact LinearEquiv.ofInjective_apply f x
  have h2 : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
    exact LinearEquiv.symm_apply_apply e x
  rw [← hfe, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, h2, LinearMap.comp_id]

/-- A functional killing the kernel of `f` factors through `f`. -/
lemma exists_comp_of_ker_le {𝕜 : Type} [Field 𝕜] {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (f : M →ₗ[𝕜] N) (φ : M →ₗ[𝕜] 𝕜)
    (h : LinearMap.ker f ≤ LinearMap.ker φ) :
    ∃ ψ : N →ₗ[𝕜] 𝕜, ψ.comp f = φ := by
  obtain ⟨g, hg⟩ := exists_comp_of_injective (LinearMap.range f).subtype
    (fun x y hxy => Subtype.ext hxy)
    (((LinearMap.ker f).liftQ φ h).comp (LinearMap.quotKerEquivRange f).symm.toLinearMap)
  refine ⟨g, ?_⟩
  ext x
  have h1 := LinearMap.congr_fun hg ⟨f x, LinearMap.mem_range_self f x⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  rw [LinearMap.comp_apply, h1]
  show ((LinearMap.ker f).liftQ φ h)
    ((LinearMap.quotKerEquivRange f).symm ⟨f x, LinearMap.mem_range_self f x⟩) = φ x
  rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-! ## Extending a functional on the chains of `A_k` to a cochain of `E` -/

lemma inclL_f_mono (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) :
    Mono ((inclL 𝕜 p k).f n) := by
  rw [show inclL 𝕜 p k = Work.SSSR.sChainMap 𝕜 (Work.StemsB.serreSubcomplex (sF p) k).ι from rfl]
  rw [Work.SSSR.sChainMap_f 𝕜 _ n]
  exact Work.SSSR.mono_sigma_map'_of_injective 𝕜 _
    (Work.SSSR.injective_app_of_mono _ inferInstance n)

/-- The inclusion of the chains of `A_k` into the chains of `E` is injective in every degree. -/
lemma inclL_f_injective (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) :
    Function.Injective (((inclL 𝕜 p k).f n).hom) :=
  (ModuleCat.mono_iff_injective _).mp (inclL_f_mono 𝕜 p k n)

/-- Every functional on the chains of `A_k` extends to a cochain of `E`. -/
lemma exists_cochain_extend (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ)
    (r : (Cc 𝕜 p k).X n →ₗ[𝕜] 𝕜) :
    ∃ x : (Wc 𝕜 p).C.X n,
      (cochainFun 𝕜 p n x).comp ((inclL 𝕜 p k).f n).hom = r :=
  exists_comp_of_injective (((inclL 𝕜 p k).f n).hom) (inclL_f_injective 𝕜 p k n) r

/-! ## The projection onto the graded piece, with its domain spelled as `C_*(A_{s+1})` -/

/-- The projection `gr_s = C_*(A_{s+1})/C_*(A_s)`, with its domain type written as the chains of
`A_{s+1}` (the two types are definitionally equal). -/
def grPi (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    (Cc 𝕜 p (s+1)).X n →ₗ[𝕜] (Kg 𝕜 p s).X n :=
  ((Kgπ 𝕜 p s).f n).hom

lemma grPi_ker (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    LinearMap.ker (grPi 𝕜 p s n) = (ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f n)).ker := rfl

/-- The chosen section `grSecX` is a section of the projection. -/
lemma grPi_grSecX (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) (z : (Kg 𝕜 p s).X n) :
    grPi 𝕜 p s n (grSecX 𝕜 p s n z) = z :=
  Kgπ_grSecX_apply 𝕜 p s n z

/-- The inclusion `A_0 ⟶ A_1` of the `0`-th step of the Serre filtration is zero. -/
lemma grIncl_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ) : grIncl 𝕜 p 0 n = 0 := rfl

/-- The `A_s`-chains are killed by the projection onto `gr_s`. -/
lemma grPi_grIncl (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) (b : (Cc 𝕜 p s).X n) :
    grPi 𝕜 p s n ((grIncl 𝕜 p s n).hom b) = 0 := by
  match s with
  | 0 =>
    show grPi 𝕜 p 0 n ((grIncl 𝕜 p 0 n).hom b) = 0
    rw [grIncl_zero, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  | (k+1) =>
    have h := congrArg (fun (g : ((Work.SSSR.serF 𝕜 (sF p)).obj k) ⟶ (Kg 𝕜 p (k+1))) =>
        (g.f n).hom b) (Work.SSSR.incF_comp_grFι (R := 𝕜) (sF p) k)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply] at h
    exact h

/-- **Decomposition of a chain of `A_{s+1}`**: it is the sum of the chosen representative of its
class in `gr_s` and a chain of `A_s`. -/
lemma exists_eq_sec_add (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (a : (Cc 𝕜 p (s+1)).X n) :
    ∃ b : (Cc 𝕜 p s).X n,
      a = grSecX 𝕜 p s n (grPi 𝕜 p s n a) + (grIncl 𝕜 p s n).hom b := by
  have hker : a - grSecX 𝕜 p s n (grPi 𝕜 p s n a) ∈ LinearMap.ker (grPi 𝕜 p s n) := by
    rw [LinearMap.mem_ker, map_sub, grPi_grSecX, sub_self]
  rw [grPi_ker] at hker
  obtain ⟨b, hb⟩ := ker_Kgπ_le_grIncl 𝕜 p s n hker
  exact ⟨b, by rw [hb]; abel⟩

/-! ## Membership in the filtration, in terms of killing the chains of `A_s` -/

/-- Membership in the Serre filtration `F^s` is equivalent to killing the chains of `A_s`. -/
lemma mem_F_iff (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (y : (Wc 𝕜 p).C.X n) :
    y ∈ (Wc 𝕜 p).F s n ↔ ∀ z : (Cc 𝕜 p s).X n,
      (cochainFun 𝕜 p n y) (((inclL 𝕜 p s).f n).hom z) = 0 := by
  change y ∈ coFilt 𝕜 (sF p) s n ↔ _
  rw [hann s n]
  rfl

/-- A cochain of `F^s` kills the image of the chains of `A_s` inside `A_{s+1}`. -/
lemma kills_grIncl (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (y : (Wc 𝕜 p).C.X n) (hy : y ∈ (Wc 𝕜 p).F s n) (b : (Cc 𝕜 p s).X n) :
    (cochainFun 𝕜 p n y) (((inclL 𝕜 p (s+1)).f n).hom ((grIncl 𝕜 p s n).hom b)) = 0 := by
  match s with
  | 0 =>
    show (cochainFun 𝕜 p n y) (((inclL 𝕜 p 1).f n).hom ((grIncl 𝕜 p 0 n).hom b)) = 0
    rw [grIncl_zero, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, map_zero]
  | (k+1) =>
    change (cochainFun 𝕜 p n y) (((inclL 𝕜 p (k+2)).f n).hom
      (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom b)) = 0
    rw [inclL_comp_apply 𝕜 p k n b]
    exact ((mem_F_iff 𝕜 p (k+1) n hann y).mp hy) b

/-- **The key injectivity step**: a cochain of `F^s` killing the chosen cycle representatives of
`gr_s` lies in `F^{s+1}`. -/
lemma mem_F_succ_of_kills_sec (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n)
    (y : (Wc 𝕜 p).C.X n) (hy : y ∈ (Wc 𝕜 p).F s n)
    (hsec : ∀ z : (Kg 𝕜 p s).X n,
      (cochainFun 𝕜 p n y) (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) = 0) :
    y ∈ (Wc 𝕜 p).F (s+1) n := by
  rw [mem_F_iff 𝕜 p (s+1) n hann]
  intro a
  obtain ⟨b, hb⟩ := exists_eq_sec_add 𝕜 p s n a
  rw [hb, map_add, map_add, hsec (grPi 𝕜 p s n a), zero_add]
  exact kills_grIncl 𝕜 p s n hann y hy b

/-! ## The restriction map `F^s ⟶ Hom(gr_s^n, 𝕜)` -/

/-- The restriction of a cochain of `F^s` to the graded piece `gr_s`, along the chosen section. -/
def evTheta (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ) :
    ↥((Wc 𝕜 p).F s n) →ₗ[𝕜] ((Kg 𝕜 p s).X n →ₗ[𝕜] 𝕜) where
  toFun x := (cochainFun 𝕜 p n x.1).comp
    (((inclL 𝕜 p (s+1)).f n).hom.comp (grSecX 𝕜 p s n))
  map_add' x y := by
    ext z
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add]
    rfl
  map_smul' a x := by
    ext z
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rfl

lemma evTheta_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (x : ↥((Wc 𝕜 p).F s n)) (z : (Kg 𝕜 p s).X n) :
    evTheta 𝕜 p s n x z = (cochainFun 𝕜 p n x.1)
      (((inclL 𝕜 p (s+1)).f n).hom (grSecX 𝕜 p s n z)) := rfl

/-- **Every functional on the graded piece comes from a cochain of `F^s`.** -/
lemma evTheta_surj (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s n : ℕ)
    (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n) :
    Function.Surjective (evTheta 𝕜 p s n) := by
  intro q
  let r : (Cc 𝕜 p (s+1)).X n →ₗ[𝕜] 𝕜 := q.comp (grPi 𝕜 p s n)
  obtain ⟨x, hx⟩ := exists_cochain_extend 𝕜 p (s+1) n r
  have hxF : x ∈ (Wc 𝕜 p).F s n := by
    cases s with
    | zero =>
      rw [(Wc 𝕜 p).F_zero]
      exact Submodule.mem_top
    | succ k =>
      rw [mem_F_iff 𝕜 p (k+1) n hann]
      intro b
      rw [← inclL_comp_apply 𝕜 p k n b]
      have h1 := LinearMap.congr_fun hx
        (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom b)
      simp only [LinearMap.comp_apply] at h1
      rw [h1]
      show (q.comp (grPi 𝕜 p (k+1) n))
        (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom b) = 0
      rw [LinearMap.comp_apply]
      rw [show grPi 𝕜 p (k+1) n
            (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n).hom b) = 0 from
        grPi_grIncl 𝕜 p (k+1) n b]
      exact map_zero q
  refine ⟨⟨x, hxF⟩, ?_⟩
  ext z
  rw [evTheta_apply]
  have h1 := LinearMap.congr_fun hx (grSecX 𝕜 p s n z)
  simp only [LinearMap.comp_apply] at h1
  rw [h1]
  show (q.comp (grPi 𝕜 p s n)) (grSecX 𝕜 p s n z) = q z
  rw [LinearMap.comp_apply, grPi_grSecX]

/-! ## The pieces of the first page -/

/-- `Z_1^s` as a set of cochains: `F^s C^n` whose coboundary lies in `F^{s+1} C^{n+1}`. -/
lemma mem_pZ_one {𝕜 : Type} [CommRing 𝕜] (W : CohFilt 𝕜) (s n : ℕ) (x : W.C.X n) :
    x ∈ pZ 𝕜 W 1 s n ↔ x ∈ W.F s n ∧ W.d n x ∈ W.F (s+1) (n+1) := by
  rw [pZ, Submodule.mem_inf, Submodule.mem_comap]

/-- The denominator of `E_1^s`: `Z_0^{s+1} + B_1^s = F^{s+1} + (F^s ∩ d(F^s))`. -/
lemma mem_pDen_one {𝕜 : Type} [CommRing 𝕜] (W : CohFilt 𝕜) (s n : ℕ) (x : W.C.X n) :
    x ∈ pDen 𝕜 W 1 s n ↔
      ∃ a ∈ W.F (s+1) n, ∃ b ∈ pB 𝕜 W 1 s n, a + b = x := by
  rw [pDen_one_eq, pB_one_eq, Submodule.mem_sup]

end

end Work.Pi6.MSS
