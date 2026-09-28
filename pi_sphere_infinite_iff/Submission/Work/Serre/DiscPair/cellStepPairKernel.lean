import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.CsrSharp.cellStepSharpIso
import Submission.Work.Serre.CsrSharp.Cell.perCellSharp
import Submission.Work.Serre.CsrSharp.Sigma.sigmaSharp
import Submission.Work.Serre.CsrSharp.Union
import Submission.Work.Serre.cellStepSharp
import Submission.Work.ThreeConnected.Excision.isZero_homology_zero_of_cokernel_pi_eq_zero
import Submission.Work.Cohomology.epsilonNaturality

/-!
# The kernel of the cell-step pair map

For `Z = attachCells n Y ι f` (cells of dimension `n+2`), `Y' = range (attachIncl n Y ι f)` and a
Serre fibration `q : E ⟶ Z`, the map of pairs `(E, q⁻¹Y') → (Z, Y')` is surjective on rational
homology in every degree `k ≥ n+2`, and its kernel is the direct sum, over the attached cells, of
the *reduced* homology of the fibre over the centre of the cell:

  `ker (H_k(E, q⁻¹Y') → H_k(Z, Y')) ≅ ⨁ᵢ H_{k-(n+2)}(F_{cᵢ}, bᵢ)`.

The proof follows the chain of the sharp rational cell step
(`Submission/Work/Serre/CsrSharp/cellStepSharpIso.lean`): the pair map is the composite of the two
compressions onto the complement of the cell centres, of the two excision isomorphisms onto the
union of the open half-balls and of the disjoint-union comparison, the middle map being the
coproduct of the per-cell comparisons.  Since homology commutes with coproducts
(`Work.Serre.sigmaHomologyMap`) and coproducts of kernels are kernels
(`Work.Serre.isIso_sigmaKernelMap`), the kernel of the pair map is the direct sum of the kernels of
the per-cell maps; those are computed from *existence* results only: the per-cell map is surjective
in every degree (a section over the contractible open half-ball) and its source is the shifted
homology of the fibre (`Work.Serre.CsrSharp.Cell.sourceIso`), while its target vanishes away from
degree `n+2` (`Work.Serre.CsrSharp.Cell.targetGroups`).  In the top degree `k = n+2` the kernel is
a hyperplane of the source, and any two hyperplanes of a `ℚ`-vector space are isomorphic.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000


/-! ## 1. Linear algebra over `ℚ` -/

/-- **Any two hyperplanes of a `ℚ`-vector space are isomorphic.** -/
theorem nonempty_ker_iso_of_surjective_rat {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f g : V →ₗ[ℚ] ℚ) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nonempty (LinearMap.ker f ≃ₗ[ℚ] LinearMap.ker g) := by
  by_cases hI : ∃ v : V, g v = 1 ∧ f v ≠ 0
  · obtain ⟨v, hv1, hv2⟩ := hI
    have hmem : ∀ x ∈ LinearMap.ker f,
        ((LinearMap.id : V →ₗ[ℚ] V) - g.smulRight v) x ∈ LinearMap.ker g := by
      intro x _
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, hv1, smul_eq_mul, mul_one]
      ring
    let Φ : LinearMap.ker f →ₗ[ℚ] LinearMap.ker g :=
      LinearMap.restrict ((LinearMap.id : V →ₗ[ℚ] V) - g.smulRight v) hmem
    have hΦ : ∀ x : LinearMap.ker f, ((Φ x : LinearMap.ker g) : V) = (x : V) - (g (x : V)) • v :=
      fun x => rfl
    have hinj : Function.Injective Φ := by
      intro x y hxy
      have h2 : (x : V) - (g (x : V)) • v = (y : V) - (g (y : V)) • v := by
        have h := congrArg (fun w : LinearMap.ker g => (w : V)) hxy
        rw [hΦ x, hΦ y] at h
        exact h
      have hxv : f (x : V) = 0 := x.2
      have hyv : f (y : V) = 0 := y.2
      have h3 : f ((x : V) - (g (x : V)) • v) = f ((y : V) - (g (y : V)) • v) := congrArg f h2
      have h4 : -((g (x:V)) * f v) = -((g (y:V)) * f v) := by
        simpa [map_sub, map_smul, smul_eq_mul, hxv, hyv] using h3
      have h5 : g (x : V) = g (y : V) := mul_right_cancel₀ hv2 (neg_inj.mp h4)
      have h6 : (x : V) = (y : V) := by
        have h7 : (x : V) - (g (x : V)) • v = (y : V) - (g (x : V)) • v := by
          rw [← h5] at h2; exact h2
        exact sub_left_inj.mp h7
      exact Subtype.ext h6
    have hsurj : Function.Surjective Φ := by
      intro y
      have hgy : g (y : V) = 0 := y.2
      refine ⟨⟨(y : V) + (-(f (y : V)) / (f v)) • v, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]
        simp only [map_add, map_smul, smul_eq_mul, hgy, zero_add]
        field_simp
        ring
      · apply Subtype.ext
        show ((y : V) + (-(f (y : V)) / (f v)) • v)
            - (g ((y : V) + (-(f (y : V)) / (f v)) • v)) • v = (y : V)
        have hgt : g ((y : V) + (-(f (y : V)) / (f v)) • v) = -(f (y : V)) / (f v) := by
          simp only [map_add, map_smul, smul_eq_mul, hgy, zero_add, hv1, mul_one]
        rw [hgt, add_sub_cancel_right]
    exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩
  · push_neg at hI
    have hII : ∃ u : V, f u = 1 ∧ g u ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨w, hw⟩ := hg 1
      obtain ⟨u, hu⟩ := hf 1
      have h1 : f (w + u) = 0 := hI (w + u) (by rw [map_add, hw, h u hu, add_zero])
      rw [map_add, hI w hw, hu, zero_add] at h1
      exact one_ne_zero h1
    obtain ⟨u, hu1, hu2⟩ := hII
    have hmem : ∀ x ∈ LinearMap.ker g,
        ((LinearMap.id : V →ₗ[ℚ] V) - f.smulRight u) x ∈ LinearMap.ker f := by
      intro x _
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, hu1, smul_eq_mul, mul_one]
      ring
    let Ψ : LinearMap.ker g →ₗ[ℚ] LinearMap.ker f :=
      LinearMap.restrict ((LinearMap.id : V →ₗ[ℚ] V) - f.smulRight u) hmem
    have hΨ : ∀ x : LinearMap.ker g, ((Ψ x : LinearMap.ker f) : V) = (x : V) - (f (x : V)) • u :=
      fun x => rfl
    have hinj : Function.Injective Ψ := by
      intro x y hxy
      have h2 : (x : V) - (f (x : V)) • u = (y : V) - (f (y : V)) • u := by
        have h := congrArg (fun w : LinearMap.ker f => (w : V)) hxy
        rw [hΨ x, hΨ y] at h
        exact h
      have hxg : g (x : V) = 0 := x.2
      have hyg : g (y : V) = 0 := y.2
      have h3 : g ((x : V) - (f (x : V)) • u) = g ((y : V) - (f (y : V)) • u) := congrArg g h2
      have h4 : -((f (x:V)) * g u) = -((f (y:V)) * g u) := by
        simpa [map_sub, map_smul, smul_eq_mul, hxg, hyg] using h3
      have h5 : f (x : V) = f (y : V) := mul_right_cancel₀ hu2 (neg_inj.mp h4)
      have h6 : (x : V) = (y : V) := by
        have h7 : (x : V) - (f (x : V)) • u = (y : V) - (f (x : V)) • u := by
          rw [← h5] at h2; exact h2
        exact sub_left_inj.mp h7
      exact Subtype.ext h6
    have hsurj : Function.Surjective Ψ := by
      intro y
      have hy : f (y : V) = 0 := y.2
      refine ⟨⟨(y : V) + (-(g (y : V)) / (g u)) • u, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]
        simp only [map_add, map_smul, smul_eq_mul, hy, zero_add]
        field_simp
        ring
      · apply Subtype.ext
        show ((y : V) + (-(g (y : V)) / (g u)) • u)
            - (f ((y : V) + (-(g (y : V)) / (g u)) • u)) • u = (y : V)
        have hft : f ((y : V) + (-(g (y : V)) / (g u)) • u) = -(g (y : V)) / (g u) := by
          simp only [map_add, map_smul, smul_eq_mul, hy, zero_add, hu1, mul_one]
        rw [hft, add_sub_cancel_right]
    exact ⟨(LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩

/-- **A quotient by the image of a split injection is a kernel.**  If `g ∘ f = id` then
`B / im f ≅ ker g`. -/
theorem nonempty_coker_iso_ker {A B : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] A)
    (h : ∀ a, g (f a) = a) :
    Nonempty ((B ⧸ LinearMap.range f) ≃ₗ[ℚ] LinearMap.ker g) := by
  let L : B →ₗ[ℚ] B := LinearMap.id - f.comp g
  have hL : ∀ b, L b = b - f (g b) := fun b => rfl
  have hker : L.ker = LinearMap.range f := by
    ext b
    rw [LinearMap.mem_ker, hL b, sub_eq_zero]
    constructor
    · intro hb; exact ⟨g b, hb.symm⟩
    · rintro ⟨a, rfl⟩; rw [h a]
  have hrange : L.range = LinearMap.ker g := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      rw [LinearMap.mem_ker, hL a, map_sub, h (g a), sub_self]
    · intro hb
      refine ⟨b, ?_⟩
      rw [hL b, LinearMap.mem_ker.mp hb, map_zero, sub_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hker).symm.trans ((LinearMap.quotKerEquivRange L).trans
    (LinearEquiv.ofEq _ _ hrange))⟩

/-- **The cokernel of a map with epimorphic image description.**  If `g` is surjective with
`ker g = range f` then `B / im f ≅ C`. -/
theorem nonempty_coker_iso_of_epi_ker {A B C : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [AddCommGroup C] [Module ℚ C]
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] C) (hg : Function.Surjective g)
    (hker : LinearMap.ker g = LinearMap.range f) :
    Nonempty ((B ⧸ LinearMap.range f) ≃ₗ[ℚ] C) := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := le_of_eq hker.symm
  let g' : (B ⧸ LinearMap.range f) →ₗ[ℚ] C := Submodule.liftQ (LinearMap.range f) g hle
  have hg' : ∀ b : B, g' (Submodule.mkQ (LinearMap.range f) b) = g b := by
    intro b
    exact Submodule.liftQ_apply (LinearMap.range f) (f := g) (h := hle) b
  have hinj : Function.Injective g' := by
    intro x y hxy
    obtain ⟨x₀, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y₀, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [hg' x₀, hg' y₀] at hxy
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    rw [← hker, LinearMap.mem_ker, map_sub, hxy, sub_self]
  have hsurj : Function.Surjective g' := by
    intro c
    obtain ⟨b, hb⟩ := hg c
    exact ⟨Submodule.mkQ _ b, by rw [hg' b, hb]⟩
  exact ⟨LinearEquiv.ofBijective g' ⟨hinj, hsurj⟩⟩


/-! ## 2. Transport of kernels and surjectivity in `ModuleCat ℚ` -/

/-- Kernels are invariant under a commutative square whose vertical maps are isomorphisms. -/
theorem nonempty_kernel_iso_of_sq {A B A' B' : ModuleCat ℚ} (f : A ⟶ B) (f' : A' ⟶ B')
    (e₁ : A ≅ A') (e₂ : B ≅ B') (hsq : f ≫ e₂.hom = e₁.hom ≫ f') :
    Nonempty (kernel f ≅ kernel f') := ⟨kernel.mapIso f f' e₁ e₂ hsq⟩

/-- Surjectivity is invariant under a commutative square whose vertical maps are
isomorphisms. -/
theorem surjective_of_sq_iff {A B A' B' : ModuleCat ℚ} (f : A ⟶ B) (f' : A' ⟶ B')
    (e₁ : A ≅ A') (e₂ : B ≅ B') (hsq : f ≫ e₂.hom = e₁.hom ≫ f') :
    Function.Surjective f.hom ↔ Function.Surjective f'.hom := by
  have hcomp : f' = e₁.inv ≫ f ≫ e₂.hom := by
    calc f' = 𝟙 _ ≫ f' := (Category.id_comp _).symm
      _ = (e₁.inv ≫ e₁.hom) ≫ f' := by rw [Iso.inv_hom_id]
      _ = e₁.inv ≫ (e₁.hom ≫ f') := Category.assoc _ _ _
      _ = e₁.inv ≫ (f ≫ e₂.hom) := by rw [← hsq]
      _ = e₁.inv ≫ f ≫ e₂.hom := (Category.assoc _ _ _).symm
  constructor
  · intro hf
    rw [hcomp, ModuleCat.hom_comp, ModuleCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso e₂.hom).surjective.comp
      (hf.comp (ConcreteCategory.bijective_of_isIso e₁.inv).surjective)
  · intro hf'
    have hcomp2 : f = e₁.hom ≫ f' ≫ e₂.inv := by
      calc f = 𝟙 A ≫ f ≫ 𝟙 B := by simp
        _ = (e₁.hom ≫ e₁.inv) ≫ f ≫ (e₂.hom ≫ e₂.inv) := by
              rw [Iso.hom_inv_id, Iso.hom_inv_id]
        _ = e₁.hom ≫ (e₁.inv ≫ f ≫ e₂.hom) ≫ e₂.inv := by simp only [Category.assoc]
        _ = e₁.hom ≫ f' ≫ e₂.inv := by rw [← hcomp]
    rw [hcomp2, ModuleCat.hom_comp, ModuleCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso e₂.inv).surjective.comp
      (hf'.comp (ConcreteCategory.bijective_of_isIso e₁.hom).surjective)

/-- Kernels are insensitive to composing the map with an isomorphism on the target. -/
theorem nonempty_kernel_iso_comp_iso_right {A B B' : ModuleCat ℚ} (f : A ⟶ B) (e : B ≅ B') :
    Nonempty (kernel (f ≫ e.hom) ≅ kernel f) :=
  ⟨kernel.mapIso (f ≫ e.hom) f (Iso.refl A) e.symm (by simp)⟩

/-- Kernels are insensitive to composing the map with an isomorphism on the source. -/
theorem nonempty_kernel_iso_comp_iso_left {A A' B : ModuleCat ℚ} (e : A ≅ A') (f : A' ⟶ B) :
    Nonempty (kernel (e.hom ≫ f) ≅ kernel f) :=
  ⟨kernel.mapIso (e.hom ≫ f) f e (Iso.refl B) (by simp)⟩

/-- The kernel of the zero map into a module is the source. -/
theorem nonempty_kernel_iso_zero (M N : ModuleCat ℚ) :
    Nonempty (kernel (0 : M ⟶ N) ≅ M) := by
  refine ⟨Iso.mk (kernel.ι (0 : M ⟶ N)) (kernel.lift (0 : M ⟶ N) (𝟙 M) (by simp)) ?_ ?_⟩
  · apply (cancel_mono (kernel.ι (0 : M ⟶ N))).mp
    rw [Category.assoc, kernel.lift_ι, Category.comp_id, Category.id_comp]
  · simp

/-- **Kernels commute with coproducts** (via `Work.Serre.isIso_sigmaKernelMap`). -/
theorem nonempty_kernel_iso_coprod {ι : Type} {A B : ι → ModuleCat ℚ}
    (f : ∀ i, A i ⟶ B i) :
    Nonempty (kernel (Limits.Sigma.map f) ≅ ∐ fun i => kernel (f i)) := by
  haveI : IsIso (Work.Serre.sigmaKernelMap f) := Work.Serre.isIso_sigmaKernelMap f
  exact ⟨(asIso (Work.Serre.sigmaKernelMap f)).symm⟩

/-- The coproduct of a family of `ℚ`-modules is the direct sum. -/
theorem nonempty_coprod_iso_directSum {ι : Type} [DecidableEq ι] (M : ι → ModuleCat ℚ) :
    Nonempty ((∐ M) ≅ ModuleCat.of ℚ (DirectSum ι (fun i => ↥(M i)))) :=
  ⟨ModuleCat.coprodIsoDirectSum M⟩

/-! ## 3. `H₀` and the cokernel projection -/

/-- Epimorphy of the map on `H₀` induced by a degreewise surjective chain map, over `ℚ`. -/
theorem epi_homologyMap_of_cycles_rat {C D : ChainComplex (ModuleCat ℚ) ℕ} (φ : C ⟶ D) (n : ℕ)
    (h : ∀ (z : D.X n), (D.d n (n - 1)) z = 0 →
          ∃ (c : C.X n) (b : D.X (n + 1)),
            (C.d n (n - 1)) c = 0 ∧ (φ.f n) c = z + (D.d (n + 1) n) b) :
    CategoryTheory.Epi (HomologicalComplex.homologyMap φ n) := by
  have hnext : (ComplexShape.down ℕ).next n = n - 1 := by
    cases n with | zero => simp | succ n => simp
  have key : Epi (HomologicalComplex.cyclesMap φ n ≫ D.homologyπ n) := by
    rw [ModuleCat.epi_iff_surjective]
    intro w
    have hsurj := (ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance
    obtain ⟨zz, hzz⟩ := hsurj w
    have hz : D.d n (n - 1) (D.iCycles n zz) = 0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
      simp
    obtain ⟨c0, b, hc0, hphi⟩ := h (D.iCycles n zz) hz
    have hs : (C.sc n).g c0 = 0 := by
      show C.d n ((ComplexShape.down ℕ).next n) c0 = 0
      rw [hnext]; exact hc0
    have hker : c0 ∈ LinearMap.ker (C.sc n).g.hom := hs
    let x : (C.sc n).moduleCatLeftHomologyData.K := ⟨c0, hker⟩
    let cc : C.cycles n := (C.sc n).moduleCatCyclesIso.inv x
    have hcc_i : C.iCycles n cc = c0 := by
      show (C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv x) = c0
      rw [← ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
      rfl
    refine ⟨cc, ?_⟩
    show D.homologyπ n (HomologicalComplex.cyclesMap φ n cc) = w
    have hL : D.iCycles n (HomologicalComplex.cyclesMap φ n cc) = φ.f n c0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, hcc_i]
    have hR : D.iCycles n (zz + D.toCycles (n + 1) n b) = φ.f n c0 := by
      rw [map_add, ← ModuleCat.comp_apply (f := D.toCycles (n + 1) n) (g := D.iCycles n),
        HomologicalComplex.toCycles_i, hphi]
    have hkey : HomologicalComplex.cyclesMap φ n cc = zz + D.toCycles (n + 1) n b :=
      (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance (hL.trans hR.symm)
    rw [hkey, map_add, hzz]
    have hzero : D.homologyπ n (D.toCycles (n + 1) n b) = 0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
      simp
    rw [hzero, add_zero]
  have key2 : Epi (C.homologyπ n ≫ HomologicalComplex.homologyMap φ n) := by
    rw [HomologicalComplex.homologyπ_naturality]
    exact key
  exact epi_of_epi (C.homologyπ n) (HomologicalComplex.homologyMap φ n)

/-- The map on `H₀` induced by the projection to the cokernel of a chain map is an epimorphism. -/
theorem epi_cokernel_pi_zero_rat {C D : ChainComplex (ModuleCat ℚ) ℕ} (f : C ⟶ D) :
    Epi (HomologicalComplex.homologyMap (cokernel.π f) 0) := by
  refine epi_homologyMap_of_cycles_rat (cokernel.π f) 0 (fun z _hz => ?_)
  have hsurj : Function.Surjective ⇑(ConcreteCategory.hom ((cokernel.π f).f 0)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨c, hc⟩ := hsurj z
  exact ⟨c, 0, by simp, by rw [hc]; simp⟩

/-! ## 4. Absolute homology versus the homology relative to a point -/

/-- `H_m(X;ℚ) ≅ H_m(X,{x₀};ℚ)` for `m ≥ 1`. -/
theorem nonempty_abs_iso_rel_singleton (X : Type) [TopologicalSpace X] (x₀ : X) (m : ℕ)
    (hm : 1 ≤ m) :
    Nonempty ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology m ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of X) ({x₀} : Set X)).homology m) := by
  haveI : Nonempty ↥({x₀} : Set X) := ⟨⟨x₀, rfl⟩⟩
  haveI : Subsingleton ↥({x₀} : Set X) := ⟨fun a b => Subtype.ext (by rw [a.2, b.2])⟩
  haveI : ContractibleSpace ↥({x₀} : Set X) := inferInstance
  haveI : PathConnectedSpace ↥({x₀} : Set X) := inferInstance
  have hz : ∀ j, 0 < j →
      IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of ↥({x₀} : Set X))).homology j) :=
    fun j hj => Work.Serre.RatAcyclic.isZero_ratH (X := ↥({x₀} : Set X))
      (Work.Serre.ratAcyclic_of_contractible ↥({x₀} : Set X)) hj
  have hIncl : HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X)) 0
      ≫ TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
      = TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ) :=
    Work.Cohomology.SSet_homologyMap_homology₀ε
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of X) ({x₀} : Set X)))
      (ModuleCat.of ℚ ℚ)
  have hmonoIncl : Mono (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X)) 0) := by
    haveI hmonoA : Mono ((TopCat.of ↥({x₀} : Set X)).singularHomology₀ε (ModuleCat.of ℚ ℚ)) :=
      inferInstance
    haveI : Mono (HomologicalComplex.homologyMap
        (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X)) 0
        ≫ (TopCat.of X).singularHomology₀ε (ModuleCat.of ℚ ℚ)) := hIncl.symm ▸ hmonoA
    exact mono_of_mono _ (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ))
  have hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X))) m) := by
    have hf : HomologicalComplex.homologyMap
        (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X)) m = 0 :=
      (hz m hm).eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp
      (Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of X) ({x₀} : Set X) m)
  have hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X))) m) := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rcases j with _ | j
    · have hδ : Work.StemsB.relChainsRδ ℚ (TopCat.of X) ({x₀} : Set X) 0 = 0 := by
        have hEx := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of X) ({x₀} : Set X) 0
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
        have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X)) 0)).ker = ⊥ := by
          rw [LinearMap.ker_eq_bot]
          exact (ModuleCat.mono_iff_injective _).mp hmonoIncl
        rw [hker] at hEx
        exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
      exact (ShortComplex.exact_iff_epi _ hδ).mp
        (Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of X) ({x₀} : Set X) 0)
    · have hδ : Work.StemsB.relChainsRδ ℚ (TopCat.of X) ({x₀} : Set X) (j + 1) = 0 :=
        (hz (j + 1) (by omega)).eq_of_tgt _ 0
      exact (ShortComplex.exact_iff_epi _ hδ).mp
        (Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of X) ({x₀} : Set X) (j + 1))
  haveI hIso : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X))) m) :=
    isIso_of_mono_of_epi _
  exact ⟨asIso (HomologicalComplex.homologyMap
    (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X))) m)⟩



/-- **The augmentation of a space with a point is surjective**, over `ℚ`: the augmentation of the
point is an isomorphism and the augmentation is natural. -/
theorem surjective_augmentation_of_point (X : Type) [TopologicalSpace X] (x₀ : X) :
    Function.Surjective (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)).hom := by
  classical
  haveI hne : Nonempty ↥({x₀} : Set X) := ⟨⟨x₀, rfl⟩⟩
  haveI hsub : Subsingleton ↥({x₀} : Set X) := ⟨fun a c => Subtype.ext (by rw [a.2, c.2])⟩
  haveI hpc : PathConnectedSpace ↥({x₀} : Set X) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
      (ModuleCat.of ℚ ℚ)) := inferInstance
  have hnat : HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
        ({x₀} : Set X)) 0 ≫ TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
      = TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ) :=
    Work.Cohomology.SSet_homologyMap_homology₀ε
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of X) ({x₀} : Set X)))
      (ModuleCat.of ℚ ℚ)
  intro z
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (TopCat.singularHomology₀ε
    (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ))).2 z
  refine ⟨(HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
    ({x₀} : Set X)) 0).hom a, ?_⟩
  change (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
      ({x₀} : Set X)) 0
      ≫ TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)).hom a = z
  have ha' : (ModuleCat.Hom.hom (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
      (ModuleCat.of ℚ ℚ))) a = z := ha
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat) a).trans ha'

/-- **Two surjections onto `ℚ` with isomorphic sources have isomorphic kernels.** -/
theorem nonempty_kernel_iso_of_surj_rat {V W : ModuleCat ℚ} (f : V ⟶ ModuleCat.of ℚ ℚ)
    (π : W ⟶ ModuleCat.of ℚ ℚ) (hf : Function.Surjective f.hom)
    (hπ : Function.Surjective π.hom) (e : V ≅ W) :
    Nonempty (kernel f ≅ kernel π) := by
  have h2 : Function.Surjective (e.inv ≫ f).hom :=
    hf.comp (ConcreteCategory.bijective_of_isIso e.inv).2
  have hk1 : Nonempty (kernel f ≅ kernel (e.inv ≫ f)) :=
    ⟨kernel.mapIso f _ e (Iso.refl _) (by simp)⟩
  have hhyper := nonempty_ker_iso_of_surjective_rat (e.inv ≫ f).hom (π.hom) h2 hπ
  exact ⟨hk1.some ≪≫ (ModuleCat.kernelIsoKer _).trans
    (hhyper.some.toModuleIso.trans (ModuleCat.kernelIsoKer _).symm)⟩

/-- **The homology of a space relative to a point is the kernel of the augmentation.**  By the
naturality of the degree-`0` augmentation, the composite `H₀({x₀}) → H₀(X) → ℤ` is an isomorphism,
so `H₀(X,{x₀})`, the cokernel of the first map, is the kernel of the augmentation. -/
theorem rel_point_iso_coker_ker (X : Type) [TopologicalSpace X] (x₀ : X) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of X) ({x₀} : Set X)).homology 0 ≅
      kernel (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ))) := by
  classical
  haveI hne : Nonempty ↥({x₀} : Set X) := ⟨⟨x₀, rfl⟩⟩
  haveI hsub : Subsingleton ↥({x₀} : Set X) := ⟨fun a c => Subtype.ext (by rw [a.2, c.2])⟩
  haveI hpc : PathConnectedSpace ↥({x₀} : Set X) := inferInstance
  haveI hεAiso : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
      (ModuleCat.of ℚ ℚ)) := inferInstance
  have hnat : HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
        ({x₀} : Set X)) 0
      ≫ TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
      = TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ) :=
    Work.Cohomology.SSet_homologyMap_homology₀ε
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl (TopCat.of X) ({x₀} : Set X)))
      (ModuleCat.of ℚ ℚ)
  -- (A) the relative `H₀` is the cokernel of the map induced by the inclusion of the point
  have hcoker : Nonempty (cokernel (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ
        (TopCat.of X) ({x₀} : Set X)) 0) ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of X) ({x₀} : Set X)).homology 0) := by
    have hπepi : Epi (HomologicalComplex.homologyMap (cokernel.π (Work.StemsB.relChainsRIncl ℚ
        (TopCat.of X) ({x₀} : Set X))) 0) := epi_cokernel_pi_zero_rat _
    have hkerπ : LinearMap.ker (HomologicalComplex.homologyMap (cokernel.π
        (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) ({x₀} : Set X))) 0).hom
        = LinearMap.range (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ
          (TopCat.of X) ({x₀} : Set X)) 0).hom :=
      (ShortComplex.Exact.moduleCat_range_eq_ker (Work.StemsB.relChainsR_exact₂ ℚ
        (TopCat.of X) ({x₀} : Set X) 0)).symm
    exact ⟨(ModuleCat.cokernelIsoRangeQuotient _).trans
      (nonempty_coker_iso_of_epi_ker _ _
        ((ModuleCat.epi_iff_surjective _).mp hπepi) hkerπ).some.toModuleIso⟩
  -- (B) that cokernel is the kernel of the augmentation
  have hker : Nonempty (cokernel (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ
        (TopCat.of X) ({x₀} : Set X)) 0) ≅
      kernel (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ))) := by
    have hpt : ∀ a, ((TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
        ≫ inv (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
          (ModuleCat.of ℚ ℚ))).hom)
        ((HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
          ({x₀} : Set X)) 0).hom a) = a := by
      intro a
      have h1 : (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)).hom
          ((HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
            ({x₀} : Set X)) 0).hom a)
          = (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ)).hom a := by
        change (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
          ({x₀} : Set X)) 0
          ≫ TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)).hom a
          = (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ)).hom a
        exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat) a
      have h2 : (inv (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
            (ModuleCat.of ℚ ℚ))).hom
          ((TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
            (ModuleCat.of ℚ ℚ)).hom a) = a := by
        change ((TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ))
          ≫ inv (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
            (ModuleCat.of ℚ ℚ))).hom a = a
        rw [IsIso.hom_inv_id (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
          (ModuleCat.of ℚ ℚ)), ModuleCat.hom_id]
        rfl
      change (inv (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X))
        (ModuleCat.of ℚ ℚ))).hom
        ((TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)).hom
          ((HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
            ({x₀} : Set X)) 0).hom a)) = a
      rw [h1, h2]
    exact ⟨((ModuleCat.cokernelIsoRangeQuotient _).trans
      ((nonempty_coker_iso_ker _ _ hpt).some.toModuleIso.trans
        (ModuleCat.kernelIsoKer _).symm)).trans
      (kernel.mapIso (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
        ≫ inv (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ)))
        (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)) (Iso.refl _)
        (asIso (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ)))
        (by
          show (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
              ≫ inv (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ)))
              ≫ (TopCat.singularHomology₀ε (TopCat.of ↥({x₀} : Set X)) (ModuleCat.of ℚ ℚ))
            = TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℚ ℚ)
          rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]))⟩
  exact ⟨hcoker.some.symm ≪≫ hker.some⟩

/-! ## 5. The per-cell comparison and its kernel -/

/-- The fibre of `q` over the centre of the `i`-th attached cell. -/
abbrev csrFibre (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) : Type :=
  Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)

/-- **The kernel of the per-cell comparison in the top degree** is the reduced `H₀` of the fibre.

The per-cell map is surjective (a section over the contractible open half-ball), its source in
degree `n+2` is `H₀` of the fibre (`sourceIso`) and its target is `ℚ` (`targetGroups`); the kernel
is therefore a hyperplane of `H₀(F)`.  On the other hand `H₀(F,{b})` is the quotient of `H₀(F)` by
the image of `H₀({b})` (the pair sequence) which, by the naturality of the augmentation, is a
complement of the kernel of the augmentation.  Two hyperplanes of a `ℚ`-vector space are
isomorphic. -/
theorem perCellKernel_top (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (b : ∀ i : ι, csrFibre n Y ι f q i) (i : ι) :
    Nonempty (kernel (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) (n+2)) ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of (csrFibre n Y ι f q i))
        ({b i} : Set (csrFibre n Y ι f q i))).homology 0) := by
  classical
  -- (1) the per-cell map is surjective in degree `n+2`
  obtain ⟨s, hs⟩ := Work.Serre.Csr.csrOpenBallSection' n Y ι f q hq i ⟨b i⟩
  have hsurj := Work.Serre.CsrSharp.Cell.perCellMap_surjective n Y ι f q i s hs (n+2)
  -- (2) the source is the shifted `H₀` of the fibre and the target is `ℚ`
  obtain ⟨eSraw⟩ := Work.Serre.CsrSharp.Cell.sourceIso n Y ι f q hq i 0
  have hVW : (Work.Serre.CsrSharp.Cell.src n Y ι f q i).homology (n+2) ≅
      (Work.Cohomology.singularChains ℚ (TopCat.of (csrFibre n Y ι f q i))).homology 0 :=
    (eqToIso (congrArg (fun j => (Work.Serre.CsrSharp.Cell.src n Y ι f q i).homology j)
      (Nat.zero_add (n+2)))).symm ≪≫ eSraw
  obtain ⟨eT⟩ := (Work.Serre.CsrSharp.Cell.targetGroups n Y ι f i).2
  -- (3) the per-cell map composed with the target isomorphism
  let g : (Work.Serre.CsrSharp.Cell.src n Y ι f q i).homology (n+2) ⟶ ModuleCat.of ℚ ℚ :=
    HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) (n+2) ≫ eT.hom
  have hgsurj : Function.Surjective g.hom := by
    change Function.Surjective (eT.hom.hom
      ∘ (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i)
        (n+2)).hom)
    exact (ConcreteCategory.bijective_of_isIso eT.hom).2.comp hsurj
  have hker1 : Nonempty (kernel (HomologicalComplex.homologyMap
      (Work.Serre.CsrSharp.perCellMap n Y ι f q i) (n+2)) ≅ kernel g) :=
    (nonempty_kernel_iso_comp_iso_right
      (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) (n+2))
      eT).map Iso.symm
  have hker2 : Nonempty (kernel g ≅ kernel (hVW.inv ≫ g)) :=
    (nonempty_kernel_iso_comp_iso_left hVW.symm g).map Iso.symm
  -- (4) the augmentation of the fibre is surjective: it is the augmentation of the point
  -- composed with the inclusion
  haveI hne : Nonempty ↥({b i} : Set (csrFibre n Y ι f q i)) := ⟨⟨b i, rfl⟩⟩
  haveI hsub : Subsingleton ↥({b i} : Set (csrFibre n Y ι f q i)) :=
    ⟨fun a c => Subtype.ext (by rw [a.2, c.2])⟩
  haveI hpc : PathConnectedSpace ↥({b i} : Set (csrFibre n Y ι f q i)) := inferInstance
  haveI hεAiso : IsIso (TopCat.singularHomology₀ε
      (TopCat.of ↥({b i} : Set (csrFibre n Y ι f q i))) (ModuleCat.of ℚ ℚ)) := inferInstance
  -- (5) the kernel of the per-cell map is the kernel of the augmentation of the fibre
  have hker3 : Nonempty (kernel g ≅ kernel (TopCat.singularHomology₀ε
      (TopCat.of (csrFibre n Y ι f q i)) (ModuleCat.of ℚ ℚ))) :=
    nonempty_kernel_iso_of_surj_rat g _ hgsurj
      (surjective_augmentation_of_point (csrFibre n Y ι f q i) (b i)) hVW
  -- (6) the relative `H₀` of the fibre at the point is the kernel of the augmentation
  exact ⟨hker1.some ≪≫ hker3.some
    ≪≫ (rel_point_iso_coker_ker (csrFibre n Y ι f q i) (b i)).some.symm⟩

/-- **The kernel of the per-cell comparison in degrees `> n+2`**: the target vanishes there, so the
kernel is the source, which is the homology of the fibre shifted by `n+2`, that is, up to the
identification of the homology relative to a point with the absolute homology, `H_{k-(n+2)}(F)`
identified with `H_{k-(n+2)}(F,{b})`. -/
theorem perCellKernel_high (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (b : ∀ i : ι, csrFibre n Y ι f q i) (i : ι) (k : ℕ) (hk : n + 2 < k) :
    Nonempty (kernel (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k) ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of (csrFibre n Y ι f q i))
        ({b i} : Set (csrFibre n Y ι f q i))).homology (k - (n+2))) := by
  have hz : IsZero ((Work.Serre.CsrSharp.Cell.tgt n Y ι f i).homology k) :=
    (Work.Serre.CsrSharp.Cell.targetGroups n Y ι f i).1 k (by omega)
  have hzero : HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k = 0 :=
    hz.eq_of_tgt _ 0
  have h1 : Nonempty (kernel (HomologicalComplex.homologyMap
      (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k) ≅
      (Work.Serre.CsrSharp.Cell.src n Y ι f q i).homology k) := by
    rw [hzero]
    exact nonempty_kernel_iso_zero _ _
  have h2 : Nonempty ((Work.Serre.CsrSharp.Cell.src n Y ι f q i).homology k ≅
      (Work.Cohomology.singularChains ℚ (TopCat.of (csrFibre n Y ι f q i))).homology
        (k - (n+2))) := by
    obtain ⟨eS⟩ := Work.Serre.CsrSharp.Cell.sourceIso n Y ι f q hq i (k - (n+2))
    exact ⟨(eqToIso (congrArg (fun j => (Work.Serre.CsrSharp.Cell.src n Y ι f q i).homology j)
      (Nat.sub_add_cancel (by omega : n + 2 ≤ k)))).symm ≪≫ eS⟩
  have h3 := nonempty_abs_iso_rel_singleton (csrFibre n Y ι f q i) (b i) (k - (n+2)) (by omega)
  exact ⟨h1.some ≪≫ h2.some ≪≫ h3.some⟩

/-- **The kernel of the per-cell comparison** in every degree `k ≥ n+2`. -/
theorem perCellKernel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (b : ∀ i : ι, csrFibre n Y ι f q i) (i : ι) (k : ℕ) (hk : n + 2 ≤ k) :
    Nonempty (kernel (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k) ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of (csrFibre n Y ι f q i))
        ({b i} : Set (csrFibre n Y ι f q i))).homology (k - (n+2))) := by
  rcases eq_or_lt_of_le hk with h | h
  · subst h
    rw [Nat.sub_self]
    exact perCellKernel_top n Y ι f q hq b i
  · exact perCellKernel_high n Y ι f q hq b i k h


/-! ## 6. The cell-step sandwich -/

/-- **Kernel transfer along a square in the "other" orientation.** -/
theorem nonempty_kernel_iso_of_sq' {A B A' B' : ModuleCat ℚ} (f : A ⟶ B) (f' : A' ⟶ B')
    (e₁ : A' ≅ A) (e₂ : B' ≅ B) (hsq : e₁.hom ≫ f = f' ≫ e₂.hom) :
    Nonempty (kernel f ≅ kernel f') := by
  have h : f ≫ e₂.symm.hom = e₁.symm.hom ≫ f' := by
    have h1 : f = e₁.inv ≫ (e₁.hom ≫ f) := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have h3 : f' = (f' ≫ e₂.hom) ≫ e₂.inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h4 : f ≫ e₂.inv = e₁.inv ≫ f' := by
      calc f ≫ e₂.inv = (e₁.inv ≫ (e₁.hom ≫ f)) ≫ e₂.inv := by
            conv_lhs => rw [h1]
        _ = e₁.inv ≫ ((e₁.hom ≫ f) ≫ e₂.inv) := Category.assoc _ _ _
        _ = e₁.inv ≫ ((f' ≫ e₂.hom) ≫ e₂.inv) := by rw [hsq]
        _ = e₁.inv ≫ f' := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact h4
  exact ⟨kernel.mapIso f f' e₁.symm e₂.symm h⟩

/-- **Surjectivity transfer along a square in the "other" orientation.** -/
theorem surjective_of_sq_iff' {A B A' B' : ModuleCat ℚ} (f : A ⟶ B) (f' : A' ⟶ B')
    (e₁ : A' ≅ A) (e₂ : B' ≅ B) (hsq : e₁.hom ≫ f = f' ≫ e₂.hom) :
    Function.Surjective f.hom ↔ Function.Surjective f'.hom := by
  have h : f ≫ e₂.symm.hom = e₁.symm.hom ≫ f' := by
    have h1 : f = e₁.inv ≫ (e₁.hom ≫ f) := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have h3 : f' = (f' ≫ e₂.hom) ≫ e₂.inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h4 : f ≫ e₂.inv = e₁.inv ≫ f' := by
      calc f ≫ e₂.inv = (e₁.inv ≫ (e₁.hom ≫ f)) ≫ e₂.inv := by
            conv_lhs => rw [h1]
        _ = e₁.inv ≫ ((e₁.hom ≫ f) ≫ e₂.inv) := Category.assoc _ _ _
        _ = e₁.inv ≫ ((f' ≫ e₂.hom) ≫ e₂.inv) := by rw [hsq]
        _ = e₁.inv ≫ f' := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact h4
  exact surjective_of_sq_iff f f' e₁.symm e₂.symm h

/-- **The middle comparison over the union of the open half-balls is the coproduct of the per-cell
comparisons.** -/
theorem midU_sigma (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (k : ℕ) :
    Nonempty (kernel (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.midUMap n Y ι f q) k) ≅
      ∐ fun i => kernel (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k)) ∧
    ((∀ i, Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k).hom) →
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.midUMap n Y ι f q) k).hom) := by
  classical
  obtain ⟨hopen, -, -, -, hcentre, -, hdisjO, -, -, -, -, -⟩ := Work.Serre.csrGeom n Y ι f
  -- the model spaces over the pieces
  let X : ι → Type := fun i => ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)
  let W : ι → Type := fun i => ↥(Work.Serre.csrOpenBall n Y ι f i)
  let A : ∀ i, Set (X i) := fun i =>
    {u : X i | (u : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}
  let Bm : ∀ i, Set (W i) := fun i =>
    {v : W i | (v : Work.RatHurewicz.attachCells n Y ι f) ∈
      Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}}
  let AU : Set ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) :=
    {x | (x : E) ∈ q ⁻¹' (Work.Serre.csrV n Y ι f)}
  let BU : Set ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i) :=
    {x | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ Work.Serre.csrV n Y ι f}
  let gs : ∀ i, C(X i, W i) := fun i => Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)
  let qU : C(↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)), ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i)) :=
    Work.Serre.csrRestrict q (⋃ i, Work.Serre.csrOpenBall n Y ι f i)
  let ΦW : ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i) ≃ₜ (Σ i, W i) :=
    Work.Serre.CsrSharp.Tools.sigmaPiecesHomeo (fun i => Work.Serre.csrOpenBall n Y ι f i) hopen hdisjO
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩) (fun z hz => Set.mem_iUnion.mp hz)
  let ΦX : ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) ≃ₜ (Σ i, X i) :=
    Work.Serre.CsrSharp.Tools.sigmaPiecesHomeo (fun i => q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)
      (fun i => (hopen i).preimage q.continuous)
      (fun i j hij => (hdisjO i j hij).preimage (⇑q))
      (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
      (fun z hz => Set.mem_iUnion.mp (Set.preimage_iUnion ▸ hz))
  let cW : C(↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i), Σ i, W i) := ⟨fun x => ΦW x, ΦW.continuous_toFun⟩
  let cWi : C(Σ i, W i, ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i)) :=
    ⟨fun x => ΦW.symm x, ΦW.continuous_invFun⟩
  let cX : C(↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)), Σ i, X i) :=
    ⟨fun x => ΦX x, ΦX.continuous_toFun⟩
  let cXi : C(Σ i, X i, ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i))) :=
    ⟨fun x => ΦX.symm x, ΦX.continuous_invFun⟩
  have hvalW : ∀ x : Σ i, W i, (cWi x).1 = x.2.1 := fun x => rfl
  have hvalX : ∀ x : Σ i, X i, (cXi x).1 = x.2.1 := fun x => rfl
  -- the comparisons of the pairs
  have hΦW : Set.MapsTo cW BU {x : Σ i, W i | x.2 ∈ Bm x.1} := by
    intro x hx
    refine ⟨(cW x).2.2, fun hc => ?_⟩
    rw [show ((cW x).2 : Work.RatHurewicz.attachCells n Y ι f) = x.1 from rfl] at hc
    exact hx ⟨(cW x).1, hc.symm⟩
  have hΦWi : Set.MapsTo cWi {x : Σ i, W i | x.2 ∈ Bm x.1} BU := by
    intro x hx hc
    obtain ⟨j, hj⟩ := hc
    rcases eq_or_ne j x.1 with h | h
    · exact hx.2 ((hvalW x).symm.trans ((h ▸ hj).symm))
    · exact (Set.disjoint_left.mp (hdisjO x.1 j (Ne.symm h)) hx.1) (hj ▸ hcentre j)
  have hΦX : Set.MapsTo cX AU {x : Σ i, X i | x.2 ∈ A x.1} := by
    intro x hx
    refine ⟨(cX x).2.2, fun hc => ?_⟩
    rw [show q ((cX x).2 : E) = q x.1 from rfl] at hc
    exact hx ⟨(cX x).1, hc.symm⟩
  have hΦXi : Set.MapsTo cXi {x : Σ i, X i | x.2 ∈ A x.1} AU := by
    intro x hx hc
    obtain ⟨j, hj⟩ := hc
    rcases eq_or_ne j x.1 with h | h
    · exact hx.2 ((congrArg (fun w => q w) (hvalX x)).symm.trans ((h ▸ hj).symm))
    · exact (Set.disjoint_left.mp (hdisjO x.1 j (Ne.symm h)) hx.1) (hj ▸ hcentre j)
  have hqU : Set.MapsTo qU AU BU := by intro x hx; exact hx
  have hgS : Set.MapsTo (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
      C(Σ i, X i, Σ i, W i)) {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, W i | x.2 ∈ Bm x.1} := by
    intro x hx
    exact hx
  -- the comparison maps and the middle map
  let PX : Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i))) AU ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} :=
    Work.Serre.relChainsRPairMap AU {x : Σ i, X i | x.2 ∈ A x.1} cX hΦX
  let PXi : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i))) AU :=
    Work.Serre.relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} AU cXi hΦXi
  let PY : Work.StemsB.relChainsR ℚ (TopCat.of ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i)) BU ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1} :=
    Work.Serre.relChainsRPairMap BU {x : Σ i, W i | x.2 ∈ Bm x.1} cW hΦW
  let PYi : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i)) BU :=
    Work.Serre.relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} BU cWi hΦWi
  let M := Work.Serre.CsrSharp.midUMap n Y ι f q
  let σMap : Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1} :=
    Work.Serre.relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
      ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ (by intro x hx; exact hx)

  -- the two transport maps are isomorphisms
  have hidX : Set.MapsTo (ContinuousMap.id ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i))) AU AU :=
    fun x hx => hx
  have hidXi : Set.MapsTo (ContinuousMap.id (Σ i, X i)) {x : Σ i, X i | x.2 ∈ A x.1}
      {x : Σ i, X i | x.2 ∈ A x.1} := fun x hx => hx
  have hidW : Set.MapsTo (ContinuousMap.id ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i)) BU BU :=
    fun x hx => hx
  have hidWi : Set.MapsTo (ContinuousMap.id (Σ i, W i)) {x : Σ i, W i | x.2 ∈ Bm x.1}
      {x : Σ i, W i | x.2 ∈ Bm x.1} := fun x hx => hx
  have hcompX : cXi.comp cX
      = ContinuousMap.id ↥(q ⁻¹' (⋃ i, Work.Serre.csrOpenBall n Y ι f i)) := by
    apply ContinuousMap.ext
    intro z
    show ΦX.symm (ΦX z) = z
    exact ΦX.symm_apply_apply z
  have hcompXi : cX.comp cXi = ContinuousMap.id (Σ i, X i) := by
    apply ContinuousMap.ext
    intro z
    show ΦX (ΦX.symm z) = z
    exact ΦX.apply_symm_apply z
  have hcompW : cWi.comp cW = ContinuousMap.id ↥(⋃ i, Work.Serre.csrOpenBall n Y ι f i) := by
    apply ContinuousMap.ext
    intro z
    show ΦW.symm (ΦW z) = z
    exact ΦW.symm_apply_apply z
  have hcompWi : cW.comp cWi = ContinuousMap.id (Σ i, W i) := by
    apply ContinuousMap.ext
    intro z
    show ΦW (ΦW.symm z) = z
    exact ΦW.apply_symm_apply z
  have hPX : PX ≫ PXi = 𝟙 _ := by
    have h1 : PX ≫ PXi
        = Work.Serre.relChainsRPairMap AU AU (cXi.comp cX) (fun x hx => hΦXi (hΦX hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cX cXi hΦX hΦXi (hg'' := fun x hx => hΦXi (hΦX hx))
    have h2 : Work.Serre.relChainsRPairMap AU AU (cXi.comp cX) (fun x hx => hΦXi (hΦX hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompX (fun x hx => hΦXi (hΦX hx)) hidX).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' AU hidX)
    exact h1.trans h2
  have hPXi : PXi ≫ PX = 𝟙 _ := by
    have h1 : PXi ≫ PX
        = Work.Serre.relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, X i | x.2 ∈ A x.1}
            (cX.comp cXi) (fun x hx => hΦX (hΦXi hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cXi cX hΦXi hΦX (hg'' := fun x hx => hΦX (hΦXi hx))
    have h2 : Work.Serre.relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, X i | x.2 ∈ A x.1}
        (cX.comp cXi) (fun x hx => hΦX (hΦXi hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompXi (fun x hx => hΦX (hΦXi hx)) hidXi).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' _ hidXi)
    exact h1.trans h2
  have hPY : PY ≫ PYi = 𝟙 _ := by
    have h1 : PY ≫ PYi
        = Work.Serre.relChainsRPairMap BU BU (cWi.comp cW) (fun x hx => hΦWi (hΦW hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cW cWi hΦW hΦWi (hg'' := fun x hx => hΦWi (hΦW hx))
    have h2 : Work.Serre.relChainsRPairMap BU BU (cWi.comp cW) (fun x hx => hΦWi (hΦW hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompW (fun x hx => hΦWi (hΦW hx)) hidW).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' BU hidW)
    exact h1.trans h2
  have hPYi : PYi ≫ PY = 𝟙 _ := by
    have h1 : PYi ≫ PY
        = Work.Serre.relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
            (cW.comp cWi) (fun x hx => hΦW (hΦWi hx)) :=
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp cWi cW hΦWi hΦW (hg'' := fun x hx => hΦW (hΦWi hx))
    have h2 : Work.Serre.relChainsRPairMap {x : Σ i, W i | x.2 ∈ Bm x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
        (cW.comp cWi) (fun x hx => hΦW (hΦWi hx)) = 𝟙 _ :=
      (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hcompWi (fun x hx => hΦW (hΦWi hx)) hidWi).trans
        (Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' _ hidWi)
    exact h1.trans h2
  -- the square: the two ways round commute
  have hcommCM : (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ :
      C(Σ i, X i, Σ i, W i)).comp cX = cW.comp qU := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hcomm : PX ≫ σMap = M ≫ PY :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp_congr cX
      (⟨Sigma.map id (fun i => gs i), by fun_prop⟩ : C(Σ i, X i, Σ i, W i))
      hΦX hgS qU cW hqU hΦW hcommCM

  -- the two transport chain maps are isomorphisms
  haveI hPXiso : IsIso PX := IsIso.mk ⟨PXi, hPX, hPXi⟩
  haveI hPYiso : IsIso PY := IsIso.mk ⟨PYi, hPY, hPYi⟩
  haveI hPXk : IsIso (HomologicalComplex.homologyMap PX k) :=
    (HomologicalComplex.homologyMapIso (asIso PX) k).isIso_hom
  haveI hPYk : IsIso (HomologicalComplex.homologyMap PY k) :=
    (HomologicalComplex.homologyMapIso (asIso PY) k).isIso_hom
  -- the square at the level of homology
  have hcommH : HomologicalComplex.homologyMap PX k ≫ HomologicalComplex.homologyMap σMap k
      = HomologicalComplex.homologyMap M k ≫ HomologicalComplex.homologyMap PY k := by
    rw [← HomologicalComplex.homologyMap_comp, hcomm, HomologicalComplex.homologyMap_comp]
  -- the disjoint-union square
  let hgA : ∀ i, Set.MapsTo (gs i) (A i) (Bm i) := fun i => by intro x hx; exact hx
  obtain ⟨eX, eY, hsq⟩ := Work.Serre.relChainsCoproductSquareRat (X := X) (Y := W) A Bm gs hgA
  have hsqσ : Work.Serre.relChainsRPairMap {x : Σ i, X i | x.2 ∈ A x.1}
      {x : Σ i, W i | x.2 ∈ Bm x.1} ⟨Sigma.map id (fun i => gs i), by fun_prop⟩
      (by rintro ⟨i, x⟩ hx; exact hgA i hx) = σMap :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr rfl _ _
  have hsq' : HomologicalComplex.homologyMap eX.hom k
        ≫ HomologicalComplex.homologyMap (Limits.Sigma.map
            (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i))) k
      = HomologicalComplex.homologyMap σMap k ≫ HomologicalComplex.homologyMap eY.hom k := by
    calc HomologicalComplex.homologyMap eX.hom k
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i))) k
        = HomologicalComplex.homologyMap (eX.hom ≫ Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i))) k :=
          (HomologicalComplex.homologyMap_comp eX.hom _ k).symm
      _ = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
              ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ (by rintro ⟨i, x⟩ hx; exact hgA i hx)
              ≫ eY.hom) k := by rw [hsq]
      _ = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : Σ i, X i | x.2 ∈ A x.1} {x : Σ i, W i | x.2 ∈ Bm x.1}
              ⟨Sigma.map id (fun i => gs i), by fun_prop⟩ (by rintro ⟨i, x⟩ hx; exact hgA i hx)) k
          ≫ HomologicalComplex.homologyMap eY.hom k :=
          HomologicalComplex.homologyMap_comp _ eY.hom k
      _ = HomologicalComplex.homologyMap σMap k ≫ HomologicalComplex.homologyMap eY.hom k := by
          rw [hsqσ]
  haveI heXk : IsIso (HomologicalComplex.homologyMap eX.hom k) :=
    (HomologicalComplex.homologyMapIso eX k).isIso_hom
  haveI heYk : IsIso (HomologicalComplex.homologyMap eY.hom k) :=
    (HomologicalComplex.homologyMapIso eY k).isIso_hom
  -- the naturality of the coproduct of homologies
  have hnat := Work.Serre.homologyMap_sigma_natural
    (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k
  haveI hs1 : IsIso (Work.Serre.sigmaHomologyMap (fun i => Work.StemsB.relChainsR ℚ
      (TopCat.of (X i)) (A i)) k) := Work.Serre.isIso_sigmaHomologyMap _ k
  haveI hs2 : IsIso (Work.Serre.sigmaHomologyMap (fun i => Work.StemsB.relChainsR ℚ
      (TopCat.of (W i)) (Bm i)) k) := Work.Serre.isIso_sigmaHomologyMap _ k
  -- (A) the kernel
  have hker1 : Nonempty (kernel (HomologicalComplex.homologyMap σMap k) ≅
      kernel (HomologicalComplex.homologyMap (Limits.Sigma.map
        (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i))) k)) :=
    ⟨kernel.mapIso _ _ (asIso (HomologicalComplex.homologyMap eX.hom k))
      (asIso (HomologicalComplex.homologyMap eY.hom k)) hsq'.symm⟩
  have hker2 : Nonempty (kernel (HomologicalComplex.homologyMap (Limits.Sigma.map
        (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i))) k) ≅
      kernel (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k))) :=
    (nonempty_kernel_iso_of_sq' _ _ (asIso (Work.Serre.sigmaHomologyMap (fun i =>
        Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A i)) k))
      (asIso (Work.Serre.sigmaHomologyMap (fun i => Work.StemsB.relChainsR ℚ
        (TopCat.of (W i)) (Bm i)) k)) hnat.symm)
  have hker3 : Nonempty (kernel (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k)) ≅
      ∐ fun i => kernel (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k)) :=
    nonempty_kernel_iso_coprod _
  -- transport from `σMap` to the middle map over the union
  have hkerM : Nonempty (kernel (HomologicalComplex.homologyMap M k) ≅
      kernel (HomologicalComplex.homologyMap σMap k)) :=
    ⟨kernel.mapIso _ _ (asIso (HomologicalComplex.homologyMap PX k))
      (asIso (HomologicalComplex.homologyMap PY k)) hcommH.symm⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hkerM.some ≪≫ hker1.some ≪≫ hker2.some ≪≫ hker3.some⟩
  · intro hpc
    haveI hEpi : ∀ i, Epi (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k) :=
      fun i => (ModuleCat.epi_iff_surjective _).mpr (hpc i)
    haveI hEpiS : Epi (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k)) :=
      Limits.Sigma.map_epi _
    have h3 : Function.Surjective (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i)) k)).hom :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    have h2 : Function.Surjective (HomologicalComplex.homologyMap (Limits.Sigma.map
          (fun i => Work.Serre.relChainsRPairMap (A i) (Bm i) (gs i) (hgA i))) k).hom :=
      (surjective_of_sq_iff' _ _ (asIso (Work.Serre.sigmaHomologyMap (fun i =>
          Work.StemsB.relChainsR ℚ (TopCat.of (X i)) (A i)) k))
        (asIso (Work.Serre.sigmaHomologyMap (fun i => Work.StemsB.relChainsR ℚ
          (TopCat.of (W i)) (Bm i)) k)) hnat.symm).mpr h3
    have h1 : Function.Surjective (HomologicalComplex.homologyMap σMap k).hom :=
      (surjective_of_sq_iff _ _ (asIso (HomologicalComplex.homologyMap eX.hom k))
        (asIso (HomologicalComplex.homologyMap eY.hom k)) hsq'.symm).mpr h2
    exact (surjective_of_sq_iff _ _ (asIso (HomologicalComplex.homologyMap PX k))
      (asIso (HomologicalComplex.homologyMap PY k)) hcommH.symm).mpr h1


/-- **The cell-step pair map is the composite of the two compressions and the two excisions with
the middle comparison over the union of the open half-balls.** -/
theorem cellStep_midU (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (k : ℕ) :
    (Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.midUMap n Y ι f q) k).hom) ∧
    Nonempty (kernel (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) k) ≅
      kernel (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.midUMap n Y ι f q) k)) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hVopen, hcover, -⟩ := Work.Serre.csrGeom n Y ι f
  let Y' : Set (Work.RatHurewicz.attachCells n Y ι f) :=
    Set.range (Work.RatHurewicz.attachIncl n Y ι f)
  let U₀ : Set (Work.RatHurewicz.attachCells n Y ι f) := ⋃ i, Work.Serre.csrOpenBall n Y ι f i
  let V : Set (Work.RatHurewicz.attachCells n Y ι f) := Work.Serre.csrV n Y ι f
  have hUopen : IsOpen U₀ := by
    rw [show U₀ = ⋃ i, Work.Serre.csrOpenBall n Y ι f i from rfl]
    exact isOpen_iUnion fun i => (Work.Serre.csrGeom n Y ι f).1 i
  have hY'V : Y' ⊆ V := by
    rintro z ⟨y, rfl⟩ ⟨i, hi⟩
    refine Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (f := f) i ?_
    change Work.Serre.csrCentre n Y ι f i ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
    exact hi ▸ ⟨y, rfl⟩
  have hcomp := fun m => Work.Serre.csrCompress n Y ι f q hq m
  have hVzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥V) {x : ↥V | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ Y'}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m (hcomp m).1
  have hBzero : ∀ m : ℕ, CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
      (TopCat.of ↥(q ⁻¹' V)) {x : ↥(q ⁻¹' V) | (x : E) ∈ q ⁻¹' Y'}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m (hcomp m).2
  have hr1 : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
        (fun x hx => Set.preimage_mono hY'V hx)) m) :=
    fun m => Work.Serre.csrRelIso (q ⁻¹' Y') (q ⁻¹' V) (Set.preimage_mono hY'V) hBzero m
  have hr3 : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap Y' V (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f))
        (fun x hx => hY'V hx)) m) :=
    fun m => Work.Serre.csrRelIso Y' V hY'V hVzero m
  have hsq1 : Work.Serre.cellStepMap n ι f q
        ≫ (Work.Serre.relChainsRPairMap Y' V
            (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx))
      = (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E)
          (fun x hx => Set.preimage_mono hY'V hx))
        ≫ (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx)) := by
    rw [Work.Serre.CsrSharp.cellStepMap_eq_pairMap n Y ι f q]
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp_congr q
      (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun _ hx => hx)
      (fun x hx => hY'V hx) (ContinuousMap.id E) q
      (fun x hx => Set.preimage_mono hY'V hx) (fun _ hx => hx) (by ext x; rfl)
  have hcovE : q ⁻¹' U₀ ∪ q ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, show U₀ ∪ V = Set.univ from hcover, Set.preimage_univ]
  have hexcE : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) m) :=
    fun m => Work.Serre.csrExcisionRat (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)
      (hUopen.preimage q.continuous) (hVopen.preimage q.continuous) hcovE m
  have hexcZ : ∀ m : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of (Work.RatHurewicz.attachCells n Y ι f))
        U₀ V) m) :=
    fun m => Work.Serre.csrExcisionRat (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V
      hUopen hVopen hcover m
  have hmapTot : Work.Cohomology.subtypeIncl (TopCat.of E) (q ⁻¹' U₀) ≫ TopCat.ofHom q
      = TopCat.ofHom (Work.Serre.csrRestrict q U₀)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hsq2 :
      (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V))
        ≫ (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q (fun _ hx => hx))
      = (Work.Serre.relChainsRPairMap
          {x : ↥(q ⁻¹' U₀) | (x : E) ∈ q ⁻¹' V}
          {x : ↥U₀ | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ V}
          (Work.Serre.csrRestrict q U₀) (fun _ hx => hx))
        ≫ (Work.Serre.relChainsRInclPairMap
            (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) := by
    unfold Work.Serre.relChainsRInclPairMap Work.Serre.relChainsRPairMap
    rw [Work.Serre.csrRelMapOf_comp, Work.Serre.csrRelMapOf_comp]
    refine Work.Serre.CsrSharp.Tools.csrRelMapOf_congr ?_ ?_ ?_ ?_
    · exact hmapTot
    · apply TopCat.hom_ext
      ext x
      rfl
    · apply TopCat.hom_ext
      ext x
      rfl
    · apply TopCat.hom_ext
      ext x
      rfl
  -- the homology-level squares
  have hsq1H : HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) k
        ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap Y' V
            (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx)) k
      = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' Y') (q ⁻¹' V)
            (ContinuousMap.id E) (fun x hx => Set.preimage_mono hY'V hx)) k
        ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q
            (fun _ hx => hx)) k := by
    rw [← HomologicalComplex.homologyMap_comp, hsq1, HomologicalComplex.homologyMap_comp]
  have hsq2H : HomologicalComplex.homologyMap (Work.Serre.relChainsRInclPairMap (TopCat.of E)
          (q ⁻¹' U₀) (q ⁻¹' V)) k
        ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q
            (fun _ hx => hx)) k
      = HomologicalComplex.homologyMap (Work.Serre.CsrSharp.midUMap n Y ι f q) k
        ≫ HomologicalComplex.homologyMap (Work.Serre.relChainsRInclPairMap
            (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) k := by
    rw [← HomologicalComplex.homologyMap_comp, hsq2, HomologicalComplex.homologyMap_comp]
    rfl
  haveI hr1k : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' Y')
      (q ⁻¹' V) (ContinuousMap.id E) (fun x hx => Set.preimage_mono hY'V hx)) k) := hr1 k
  haveI hr3k : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap Y' V
      (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx)) k) := hr3 k
  haveI hexcEk : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRInclPairMap
      (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) k) := hexcE k
  haveI hexcZk : IsIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRInclPairMap
      (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) k) := hexcZ k
  -- transfer `cellStepMap ↔ midV`
  have hA : (Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.cellStepMap n ι f q) k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
        (q ⁻¹' V) V q (fun _ hx => hx)) k).hom) :=
    surjective_of_sq_iff _ _ (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
        (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E) (fun x hx => Set.preimage_mono hY'V hx)) k))
      (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap Y' V
        (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx)) k)) hsq1H
  have hB : Nonempty (kernel (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) k) ≅
      kernel (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (q ⁻¹' V) V q
        (fun _ hx => hx)) k)) :=
    ⟨kernel.mapIso _ _ (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
        (q ⁻¹' Y') (q ⁻¹' V) (ContinuousMap.id E) (fun x hx => Set.preimage_mono hY'V hx)) k))
      (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap Y' V
        (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) (fun x hx => hY'V hx)) k)) hsq1H⟩
  -- transfer `midV ↔ midU`
  have hC : (Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
        (q ⁻¹' V) V q (fun _ hx => hx)) k).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.midUMap n Y ι f q) k).hom) :=
    surjective_of_sq_iff' _ _ (asIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) k))
      (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRInclPairMap
        (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) k)) hsq2H
  have hD : Nonempty (kernel (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
        (q ⁻¹' V) V q (fun _ hx => hx)) k) ≅
      kernel (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.midUMap n Y ι f q) k)) :=
    nonempty_kernel_iso_of_sq' _ _ (asIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRInclPairMap (TopCat.of E) (q ⁻¹' U₀) (q ⁻¹' V)) k))
      (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRInclPairMap
        (TopCat.of (Work.RatHurewicz.attachCells n Y ι f)) U₀ V) k)) hsq2H
  exact ⟨hA.trans hC, ⟨hB.some ≪≫ hD.some⟩⟩


/-! ## 7. The kernel of the pair map of the cell step -/

theorem cellStepPairKernel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hne : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))
    (b : ∀ i : ι, Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i))
    (k : ℕ) (hk : n + 2 ≤ k) :
    Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl n Y ι f))
          (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) q (fun _ hx => hx)) k).hom ∧
      Nonempty ((CategoryTheory.Limits.kernel (HomologicalComplex.homologyMap
          (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl n Y ι f))
            (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) q (fun _ hx => hx)) k))
        ≅ ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.StemsB.relChainsR ℚ
            (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))
            {b i}).homology (k - (n+2)))))) := by
  classical
  rw [← Work.Serre.CsrSharp.cellStepMap_eq_pairMap n Y ι f q]
  -- the per-cell surjectivity and the per-cell kernels
  have hsurj_i : ∀ i, Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k).hom := by
    intro i
    obtain ⟨s, hs⟩ := Work.Serre.Csr.csrOpenBallSection' n Y ι f q hq i ⟨b i⟩
    exact Work.Serre.CsrSharp.Cell.perCellMap_surjective n Y ι f q i s hs k
  have hker_i : ∀ i, Nonempty (kernel (HomologicalComplex.homologyMap
      (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k) ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of (csrFibre n Y ι f q i))
        ({b i} : Set (csrFibre n Y ι f q i))).homology (k - (n+2))) :=
    fun i => perCellKernel n Y ι f q hq b i k hk
  -- the sandwich
  obtain ⟨hstepSurj, hstepKer⟩ := cellStep_midU n Y ι f q hq k
  obtain ⟨hmidKer, hmidSurj⟩ := midU_sigma n Y ι f q k
  -- the coproduct of the per-cell kernels
  have h1 : Nonempty (kernel (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) k) ≅
      ∐ fun i => kernel (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k)) :=
    ⟨hstepKer.some ≪≫ hmidKer.some⟩
  have h2 : Nonempty ((∐ fun i => kernel (HomologicalComplex.homologyMap
        (Work.Serre.CsrSharp.perCellMap n Y ι f q i) k)) ≅
      ∐ fun i => (Work.StemsB.relChainsR ℚ (TopCat.of (csrFibre n Y ι f q i))
        ({b i} : Set (csrFibre n Y ι f q i))).homology (k - (n+2))) :=
    ⟨Sigma.mapIso fun i => (hker_i i).some⟩
  have h3 : Nonempty ((∐ fun i => (Work.StemsB.relChainsR ℚ (TopCat.of (csrFibre n Y ι f q i))
        ({b i} : Set (csrFibre n Y ι f q i))).homology (k - (n+2))) ≅
      ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.StemsB.relChainsR ℚ
        (TopCat.of (csrFibre n Y ι f q i)) ({b i} : Set (csrFibre n Y ι f q i))).homology
          (k - (n+2)))))) :=
    nonempty_coprod_iso_directSum _
  exact ⟨hstepSurj.mpr (hmidSurj hsurj_i), ⟨h1.some ≪≫ h2.some ≪≫ h3.some⟩⟩

end

end Work.Serre.DiscPair
