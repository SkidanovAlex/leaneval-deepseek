import Mathlib
import Submission.Work.SSS.ExpTensLES
import Submission.Work.SSS.expTensHomologyZero
import Submission.Work.Pi6.EMM2.freeFlatPresentation
import Submission.Work.Pi6.EMM2.degreeZeroRetraction
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Coefficient change does not create homology

This file proves `Work.Pi6.EMM2.coeffVanishing`: if a chain complex `K` of free `ℤ`-modules has
`H_j(K) = 0` for `1 ≤ j ≤ n` and `H_0(K)` is free, then `H_n(K ⊗ M) = 0` for *every* coefficient
module `M`.  (This is the universal coefficient theorem
`H_n(K ⊗ M) ≅ H_n(K) ⊗ M ⊕ Tor_1(H_{n-1}(K), M)` read as a vanishing statement; `H_0(K)` free
is needed only for `n = 1`, where the relevant `Tor` term is `Tor_1(H_0(K), M)`.)

The mathematical content is split into three independent mechanisms:

* `Work.Pi6.EMM2.isZero_homology_of_rTensor_injective` — the **flat-case computation**.  If
  `H_n(K) = 0` and the inclusion of the boundaries `B_{n-1} = im d_n ⊆ K_{n-1}` stays injective
  after tensoring with `M`, then `H_n(K ⊗ M) = 0`.  The point is that `- ⊗ M` is right exact, so
  `ker (d_n ⊗ M) = Z_n ⊗ M` and `im (d_{n+1} ⊗ M) = B_n ⊗ M` (as submodules of `K_n ⊗ M`), and
  `Z_n = B_n` because `H_n(K) = 0`.
* `Work.Pi6.EMM2.isZero_expTens_homology_of_flat` — the special case where `M` is flat.
* `Work.Pi6.EMM2.isZero_expTens_homology_ge_two` — for `n ≥ 2` an arbitrary coefficient module is
  handled by a free presentation `0 → P → Q → M → 0` with `P` torsion free (hence flat) and the
  long exact homology sequence of `0 → K ⊗ P → K ⊗ Q → K ⊗ M → 0`, whose outer terms vanish by the
  flat case.  For `n = 1` the corresponding term `H_0(K ⊗ P)` need not vanish and the argument is
  replaced by `Work.Pi6.EMM2.isZero_expTens_homology_one`, where the hypothesis that `H_0(K)` is
  free makes `B_0 ⊆ K_0` a direct summand and hence keeps `B_0 ⊗ M → K_0 ⊗ M` injective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

attribute [local instance 5000] Submodule.module
attribute [-instance] AddCommGroup.toIntModule

namespace Work.Pi6.EMM2

noncomputable section

/-- If `A --f--> B --g--> C` is exact in `ModuleCat ℤ` and `A` and `C` are zero, then `B` is
zero. -/
theorem isZero_of_exact_of_isZero {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f.hom g.hom) (hA : IsZero A) (hC : IsZero C) : IsZero B := by
  have hf : f.hom = 0 := by
    haveI : Subsingleton ↥A := (ModuleCat.isZero_iff_subsingleton).mp hA
    ext x
    rw [show x = 0 from Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have hg : g.hom = 0 := by
    haveI : Subsingleton ↥C := (ModuleCat.isZero_iff_subsingleton).mp hC
    ext x
    exact Subsingleton.elim _ _
  have hbot : (⊥ : Submodule ℤ ↥B) = ⊤ := by
    have h1 := LinearMap.exact_iff.mp h
    rw [hf, hg, LinearMap.range_zero, LinearMap.ker_zero] at h1
    exact h1.symm
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  have hle : (⊤ : Submodule ℤ ↥B) ≤ ⊥ := by rw [← hbot]
  have h2 : ∀ x : ↥B, x = 0 := fun x => by
    simpa using (hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ ↥B)))
  rw [h2 a, h2 b]

/-- **Right exactness of `- ⊗ M` computes `H_n(K ⊗ M)` when the boundaries stay injective.**

Let `K` be a chain complex of `ℤ`-modules with `H_n(K) = 0` (`n ≥ 1`) and let `M` be a coefficient
module such that the inclusion of the boundaries `B_{n-1} = d_n(K_n) ⊆ K_{n-1}` remains injective
after tensoring with `M` (this is what holds when `M` is flat, and for `n = 1` when `B_0 ⊆ K_0` is
a direct summand).  Then `H_n(K ⊗ M) = 0`.

The proof identifies, using only the right exactness of `- ⊗ M`
(`TensorProduct.rTensor_exact`), the two submodules

`ker (d_n ⊗ M) = Z_n ⊗ M`  and  `im (d_{n+1} ⊗ M) = B_n ⊗ M`

of `K_n ⊗ M`: the first from `0 → Z_n → K_n → B_{n-1} → 0` and the injectivity hypothesis, the
second from `K_{n+1} → B_n → K_n`.  Since `H_n(K) = 0` gives `Z_n = B_n`, the two agree. -/
theorem isZero_homology_of_rTensor_injective (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (hn : 1 ≤ n) (M : ModuleCat ℤ) (hvan : IsZero (K.homology n))
    (hinj : Function.Injective
      (LinearMap.rTensor ↥M (LinearMap.range (K.d n (n - 1)).hom).subtype)) :
    IsZero ((Work.SSS.expTens K M).homology n) := by
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 := ComplexShape.prev_eq' _ rfl
  have hnext : (ComplexShape.down ℕ).next n = n - 1 :=
    ComplexShape.next_eq' _ (show n - 1 + 1 = n from by omega)
  -- the two differentials of `K` and of `K ⊗ M` that meet in degree `n`
  have hf : ((Work.SSS.expTens K M).sc' (n+1) n (n-1)).f = K.d (n+1) n ▷ M := by
    rw [show ((Work.SSS.expTens K M).sc' (n+1) n (n-1)).f
        = (Work.SSS.expTens K M).d (n+1) n from rfl]
    exact Work.SSS.expTens_d K M n
  have hg : ((Work.SSS.expTens K M).sc' (n+1) n (n-1)).g = K.d n (n-1) ▷ M := by
    rw [show ((Work.SSS.expTens K M).sc' (n+1) n (n-1)).g
        = (Work.SSS.expTens K M).d n (n-1) from rfl]
    have h : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    rw [h]
    exact Work.SSS.expTens_d K M (n - 1)
  set f : ↥(K.X n) →ₗ[ℤ] ↥(K.X (n-1)) := (K.d n (n-1)).hom with hfdef
  set g : ↥(K.X (n+1)) →ₗ[ℤ] ↥(K.X n) := (K.d (n+1) n).hom with hgdef
  -- `H_n(K) = 0` says that the `n`-cycles are the `n`-boundaries
  have hker_range : LinearMap.ker f = LinearMap.range g := by
    have h1 : (K.sc' (n+1) n (n-1)).Exact :=
      (HomologicalComplex.exactAt_iff' K (n+1) n (n-1) hprev hnext).mp
        ((HomologicalComplex.exactAt_iff_isZero_homology K n).mpr hvan)
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h1
    rw [LinearMap.exact_iff] at h1
    simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
      HomologicalComplex.shortComplexFunctor'_obj_g] at h1
    exact h1
  -- the identification `range (g ⊗ M) = ker (f ⊗ M)`
  have hmain : Function.Exact (LinearMap.rTensor ↥M g) (LinearMap.rTensor ↥M f) := by
    rw [LinearMap.exact_iff]
    let f' := f.codRestrict (LinearMap.range f) (fun x => ⟨x, rfl⟩)
    let g' := g.codRestrict (LinearMap.range g) (fun x => ⟨x, rfl⟩)
    have hsurjf' : Function.Surjective f' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    have hsurjg' : Function.Surjective g' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    have hfg_eq : f = (LinearMap.range f).subtype.comp f' :=
      (LinearMap.subtype_comp_codRestrict f (LinearMap.range f) (fun x => ⟨x, rfl⟩)).symm
    have hgg_eq : g = (LinearMap.range g).subtype.comp g' :=
      (LinearMap.subtype_comp_codRestrict g (LinearMap.range g) (fun x => ⟨x, rfl⟩)).symm
    have hexact : Function.Exact (LinearMap.rTensor ↥M (LinearMap.ker f).subtype)
        (LinearMap.rTensor ↥M f') :=
      rTensor_exact ↥M (LinearMap.exact_iff.mpr (by
        rw [LinearMap.ker_codRestrict, Submodule.range_subtype])) hsurjf'
    have e1 : LinearMap.range (LinearMap.rTensor ↥M g)
        = LinearMap.range (LinearMap.rTensor ↥M (LinearMap.range g).subtype) := by
      conv_lhs => rw [hgg_eq, LinearMap.rTensor_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr (LinearMap.rTensor_surjective ↥M hsurjg'),
        Submodule.map_top]
    have e2 : LinearMap.range (LinearMap.rTensor ↥M (LinearMap.range g).subtype)
        = LinearMap.range (LinearMap.rTensor ↥M (LinearMap.ker f).subtype) := by
      rw [hker_range]
    have e3 : LinearMap.range (LinearMap.rTensor ↥M (LinearMap.ker f).subtype)
        = LinearMap.ker (LinearMap.rTensor ↥M f') := (LinearMap.exact_iff.mp hexact).symm
    have hf_eq : LinearMap.rTensor ↥M f
        = (LinearMap.rTensor ↥M (LinearMap.range f).subtype).comp
            (LinearMap.rTensor ↥M f') := by
      conv_lhs => rw [hfg_eq, LinearMap.rTensor_comp]
    have e4 : LinearMap.ker (LinearMap.rTensor ↥M f')
        = LinearMap.ker (LinearMap.rTensor ↥M f) := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_ker, hf_eq, LinearMap.comp_apply]
      constructor
      · intro hx
        rw [hx, map_zero]
      · intro hx
        apply hinj
        rw [map_zero]
        exact hx
    rw [e1, e2, e3, e4]
  have hExat : (Work.SSS.expTens K M).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n+1) n (n-1) hprev hnext,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, hf, hg]
    exact hmain
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp hExat

/-- The **flat case**: for flat coefficients, vanishing of `H_n(K)` implies vanishing of
`H_n(K ⊗ M)` provided the boundaries `B_{n-1} ⊆ K_{n-1}` stay injective after tensoring, which
flatness of `M` provides. -/
theorem isZero_homology_of_flat (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (M : ModuleCat ℤ) [Module.Flat ℤ ↥M] (hvan : IsZero (K.homology n)) :
    IsZero ((Work.SSS.expTens K M).homology n) :=
  isZero_homology_of_rTensor_injective K n hn M hvan
    (Module.Flat.rTensor_preserves_injective_linearMap
      (f := (LinearMap.range (K.d n (n - 1)).hom).subtype) Subtype.val_injective)

/-- **The case `n = 1` with arbitrary coefficients.**  Here `H_0(K)` free makes `B_0 ⊆ K_0` a
direct summand (via a retraction `ρ`), so that `B_0 ⊗ M → K_0 ⊗ M` is injective and
`Work.Pi6.EMM2.isZero_homology_of_rTensor_injective` applies. -/
theorem isZero_expTens_homology_one (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ)
    (hvan : IsZero (K.homology 1))
    (hretr : ∃ ρ : ↥(K.X 0) →ₗ[ℤ] ↥(LinearMap.range (K.d 1 0).hom),
      ρ ∘ₗ (LinearMap.range (K.d 1 0).hom).subtype = LinearMap.id) :
    IsZero ((Work.SSS.expTens K M).homology 1) := by
  obtain ⟨ρ, hρ⟩ := hretr
  refine isZero_homology_of_rTensor_injective K 1 le_rfl M hvan ?_
  have hcomp : (LinearMap.rTensor ↥M ρ).comp
      (LinearMap.rTensor ↥M (LinearMap.range (K.d 1 0).hom).subtype) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hρ, LinearMap.rTensor_id]
  refine Function.LeftInverse.injective (g := LinearMap.rTensor ↥M ρ) fun x => ?_
  have h := LinearMap.congr_fun hcomp x
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  exact h

/-- **The case `n ≥ 2` with arbitrary coefficients**, given a free presentation
`0 → P → Q → M → 0` of the coefficients with `P` flat.  The long exact homology sequence of
`0 → K ⊗ P → K ⊗ Q → K ⊗ M → 0` has vanishing terms `H_n(K ⊗ Q)` (flat case, `H_n(K) = 0`) and
`H_{n-1}(K ⊗ P)` (flat case, `H_{n-1}(K) = 0` because `n ≥ 2`), whence `H_n(K ⊗ M) = 0`. -/
theorem isZero_expTens_homology_ge_two
    (hpres : ∀ M : ModuleCat.{0,0} ℤ, ∃ S : ShortComplex (ModuleCat ℤ),
      S.X₃ = M ∧ S.ShortExact ∧ Module.Free ℤ ↥(S.X₂) ∧ Module.Flat ℤ ↥(S.X₁))
    (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 2 ≤ n)
    (hfree : ∀ i : ℕ, Module.Free ℤ ↥(K.X i))
    (hvan : ∀ j : ℕ, 1 ≤ j → j ≤ n → IsZero (K.homology j)) (M : ModuleCat.{0,0} ℤ) :
    IsZero ((Work.SSS.expTens K M).homology n) := by
  obtain ⟨S, hS3, hS, hQfree, hPflat⟩ := hpres M
  haveI : Module.Flat ℤ ↥(S.X₁) := hPflat
  haveI : Module.Flat ℤ ↥(S.X₂) := Module.Flat.of_free
  have hK : ∀ i, Module.Flat ℤ ↥(K.X i) := fun i => by
    haveI := hfree i
    exact Module.Flat.of_free
  rw [← hS3]
  have hSE : (Work.SSS.expTensShort K S).ShortExact :=
    Work.SSS.expTensShort_shortExact S hS hK
  have h2 : IsZero ((Work.SSS.expTensShort K S).X₂.homology n) :=
    isZero_homology_of_flat K n (by omega) S.X₂ (hvan n (by omega) le_rfl)
  have h1 : IsZero ((Work.SSS.expTensShort K S).X₁.homology (n - 1)) :=
    isZero_homology_of_flat K (n - 1) (by omega) S.X₁
      (hvan (n - 1) (by omega) (by omega))
  have hij : (ComplexShape.down ℕ).Rel n (n - 1) := by
    show n - 1 + 1 = n
    omega
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hSE.homology_exact₃ n (n - 1) hij)
  exact isZero_of_exact_of_isZero _ _ hex h2 h1

/-- **Coefficient change does not create homology in a range of vanishing integral homology.**
Let `K` be a chain complex of free `ℤ`-modules whose homology vanishes in degrees `1 ≤ j ≤ n`
(`n ≥ 1`) and whose `H_0(K)` is free.  Then for *every* coefficient module `M` the homology of the
coefficient extension `Work.SSS.expTens K M` also vanishes in degree `n`.

(Mathematically this is the universal coefficient theorem
`H_n(K ⊗ M) ≅ H_n(K) ⊗ M ⊕ Tor_1(H_{n-1}(K), M)`; `H_0(K)` free is used only for `n = 1`, where the
relevant Tor term is `Tor_1(H_0(K), M)`.) -/
theorem coeffVanishing (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hfree : ∀ i : ℕ, Module.Free ℤ ↥(K.X i))
    (h0 : Module.Free ℤ ↥(K.homology 0))
    (hvan : ∀ j : ℕ, 1 ≤ j → j ≤ n → CategoryTheory.Limits.IsZero (K.homology j))
    (M : ModuleCat ℤ) :
    CategoryTheory.Limits.IsZero ((Work.SSS.expTens K M).homology n) := by
  rcases lt_or_ge 1 n with hn2 | hn1
  · exact isZero_expTens_homology_ge_two (fun M => freeFlatPresentation M) K n (by omega) hfree
      hvan M
  · have hn_eq : n = 1 := le_antisymm hn1 hn
    subst hn_eq
    exact isZero_expTens_homology_one K M (hvan 1 le_rfl le_rfl) (degreeZeroRetraction K h0)

end

end Work.Pi6.EMM2
