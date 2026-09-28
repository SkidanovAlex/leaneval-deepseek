import Mathlib
import Submission.Work.SSS.serreE2Defs
import Submission.Work.SSS.ExpTens
import Submission.Work.SSS.ExpTensLES
import Submission.Work.SSS.expTensHomologyZero
import Submission.Work.SSS.exists_shortExact_free
import Submission.Work.StemsB.sphRatHomology

/-!
# Finiteness of singular homology with finitely generated coefficients

This file proves `Work.SSS.singularCoeffFG`: for a topological space `B` and a finitely generated
`ℤ`-module `M`, the singular homology `H_s(B;M)` is finitely generated as soon as `H_s(B;ℤ)` and
`H_{s-1}(B;ℤ)` are.  This is the universal coefficient theorem

`H_s(B;M) ≅ H_s(B;ℤ) ⊗ M ⊕ Tor(H_{s-1}(B;ℤ), M)`

read in the Serre class of finitely generated abelian groups: `H_s(B;M)` is the homology of the
coefficient extension of the integral singular chain complex `C_*(B)` by `M`.

The proof is a self-contained development of the universal coefficient theorem in finiteness form,
`Work.SSS.expTensFG`, together with the identification of the singular chains with coefficients in
`M` with the coefficient extension `expTens C_*(B;ℤ) M`:

* `Work.SSS.sChains_free` — the integral singular chains of a simplicial set are degreewise free;
* `Work.SSS.tensorRightMapHomIsoExpTens` — the naive coefficient extension `expTens K M` is the
  image of `K` under the additive functor `- ⊗ M`;
* `Work.SSS.chainCoeffExpIso` — the singular chains with coefficients in `M` of a simplicial set
  are the coefficient extension of its integral chains (from
  `Work.StemsB.SphRat.chainComplexBaseChange`: a functor preserving coproducts commutes with the
  simplicial chain complex, plus the unitor `ℤ ⊗ M ≅ M`);
* `Work.SSS.expTensFreeFG` — universal coefficients for **free** coefficients of finite rank,
  `H_m(K ⊗ ℤ^r) ≅ H_m(K) ⊗ ℤ^r`, by induction on the rank through the long exact sequence of
  `0 → ℤ^r → ℤ^{r+1} → ℤ → 0` (`Work.SSS.freeSES`), the case `r = 0` being the case of a
  coefficient module all of whose terms are subsingleton;
* `Work.SSS.expTensFG` — the general case: a free presentation `0 → P → Q → M → 0` of `M` gives,
  after tensoring with the flat complex `K`, a long exact sequence
  `H_n(K⊗P) → H_n(K⊗Q) → H_n(K⊗M) → H_{n-1}(K⊗P)` in which the outer terms are finitely generated
  by the free case and `H_n(K⊗M)` is an extension of two finitely generated modules.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped CategoryTheory MonoidalCategory

namespace Work.SSS

noncomputable section

/-! ## 1. The singular chains with coefficients in `M` -/

/-- **The singular chains of a simplicial set with `ℤ` coefficients are degreewise free**, being
the coproduct of one copy of `ℤ` for each simplex.  (This is
`Work.Cohomology.singularChains_free` for a topological space, restated for a simplicial set and
proved directly from the coproduct description to keep the import footprint small.) -/
theorem sChains_free (X : SSet) (n : ℕ) :
    Module.Free ℤ ((X.chainComplex (ModuleCat.of ℤ ℤ)).X n) := by
  have h : ((X.chainComplex (ModuleCat.of ℤ ℤ)).X n) =
      (∐ fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) => (ModuleCat.of ℤ ℤ)) := rfl
  rw [h]
  have e : (∐ fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) => (ModuleCat.of ℤ ℤ)) ≅
      ModuleCat.of ℤ (X.obj (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :=
    (IsColimit.coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (X.obj (Opposite.op (SimplexCategory.mk n))))
      (colimit.isColimit _)).symm
  exact Module.Free.of_equiv (Iso.toLinearEquiv e).symm

/-- **The naive coefficient extension is the image of a complex under `- ⊗ M`.**  The complex
`expTens K M` (with `(expTens K M).X n = K.X n ⊗ M` and differential `K.d (n+1) n ▷ M`) is the
image of `K` under the additive functor `tensorRight M`. -/
def tensorRightMapHomIsoExpTens (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    ((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ expTens K M := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) (fun i j hij => ?_)
  obtain rfl : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
  simp only [Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d, Iso.refl_hom]
  rfl

/-- **The singular chain complex with coefficients in `M` is the coefficient extension of the
integral singular chain complex of a simplicial set.**  Both sides are the coproduct, in degree `n`,
of one copy of `M` for each `n`-simplex, with the alternating sum of the face maps as differential;
the identification is `Work.StemsB.SphRat.chainComplexBaseChange` (the functor `- ⊗ M` preserves
coproducts, so it commutes with the simplicial chain complex) followed by the unitor `ℤ ⊗ M ≅ M`. -/
def chainCoeffExpIso (X : SSet.{0}) (M : ModuleCat ℤ) :
    X.chainComplex M ≅ expTens (X.chainComplex (ModuleCat.of ℤ ℤ)) M :=
  (Work.StemsB.SphRat.chainComplexBaseChange (tensorRight M) X (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso X
        (show (tensorRight M).obj (ModuleCat.of ℤ ℤ) ≅ M from λ_ M)).symm ≪≫
    tensorRightMapHomIsoExpTens (X.chainComplex (ModuleCat.of ℤ ℤ)) M

/-! ## 2. Elementary finiteness lemmas -/

/-- A subsingleton `ℤ`-module is finitely generated. -/
theorem fg_of_subsingleton {X : ModuleCat ℤ} (h : Subsingleton ↥X) : Module.Finite ℤ X :=
  Module.Finite.of_surjective (0 : ℤ →ₗ[ℤ] ↥X) (fun _ => ⟨0, Subsingleton.elim _ _⟩)

/-- Finite generation of `ℤ`-modules is invariant under isomorphism. -/
theorem moduleCatFiniteOfIso {X Y : ModuleCat ℤ} (e : X ≅ Y) [Module.Finite ℤ X] :
    Module.Finite ℤ Y :=
  Module.Finite.equiv (Iso.toLinearEquiv e)

/-- The homology of a complex of `ℤ`-modules all of whose terms are subsingleton modules is
finitely generated. -/
theorem fg_homology_of_subsingleton_terms (L : ChainComplex (ModuleCat ℤ) ℕ)
    (h : ∀ n, Subsingleton ↥(L.X n)) (m : ℕ) : Module.Finite ℤ (L.homology m) := by
  have hinj : Function.Injective (ModuleCat.Hom.hom (L.iCycles m)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (L.homologyπ m)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hcyc : Subsingleton ↥(L.cycles m) := ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  refine fg_of_subsingleton ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  exact congrArg _ (Subsingleton.elim a' b')

/-- The tensor product of a module with a subsingleton module is subsingleton. -/
theorem subsingleton_tensor_right {M N : ModuleCat ℤ} (h : Subsingleton ↥N) :
    Subsingleton ↥(M ⊗ N) := by
  have hzero : ∀ x : ↥(M ⊗ N), x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-! ## 3. Universal coefficients for free coefficients of finite rank -/

/-- A finitely generated free `ℤ`-module is `ℤ^r` for some `r`. -/
theorem exists_iso_fin_int (Q : ModuleCat ℤ) [Module.Free ℤ Q] [Module.Finite ℤ Q] :
    ∃ r : ℕ, Nonempty (Q ≅ ModuleCat.of ℤ (Fin r → ℤ)) := by
  refine ⟨Module.finrank ℤ ↥Q, ⟨LinearEquiv.toModuleIso ?_⟩⟩
  exact (Module.finBasis ℤ ↥Q).repr.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (Module.finrank ℤ ↥Q)))

/-- The inclusion `ℤ^r → ℤ^{r+1}` (in the first coordinate coordinates: `v ↦ (0, v)`). -/
def fmap (r : ℕ) : (Fin r → ℤ) →ₗ[ℤ] (Fin (r + 1) → ℤ) :=
  LinearMap.pi (Fin.cases 0 (fun j => LinearMap.proj j))

/-- The projection `ℤ^{r+1} → ℤ` onto the zeroth coordinate. -/
def gmap (r : ℕ) : (Fin (r + 1) → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj 0

lemma fmap_injective (r : ℕ) : Function.Injective (fmap r) := by
  intro v w h
  funext j
  have h2 := congrFun h (Fin.succ j)
  simpa [fmap, LinearMap.pi_apply] using h2

lemma gmap_surjective (r : ℕ) : Function.Surjective (gmap r) := by
  intro z
  exact ⟨Pi.single 0 z, by simp [gmap, LinearMap.proj_apply]⟩

lemma fmap_gmap_exact (r : ℕ) : Function.Exact (fmap r) (gmap r) := by
  rw [LinearMap.exact_iff]
  ext w
  constructor
  · intro hw
    rw [LinearMap.mem_ker] at hw
    have hw0 : w 0 = 0 := by simpa [gmap, LinearMap.proj_apply] using hw
    rw [LinearMap.mem_range]
    refine ⟨fun j => w (Fin.succ j), ?_⟩
    funext i
    refine Fin.cases ?_ ?_ i
    · simpa [fmap, LinearMap.pi_apply] using hw0.symm
    · intro j
      simp [fmap, LinearMap.pi_apply]
  · rintro ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    simp [gmap, fmap]

/-- **The free short exact sequence `0 → ℤ^r → ℤ^{r+1} → ℤ → 0`.** -/
def freeSES (r : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom (fmap r)) (ModuleCat.ofHom (gmap r)) (by
    ext v
    simp [fmap, gmap])

theorem freeSES_shortExact (r : ℕ) : (freeSES r).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (LinearMap.exact_iff.mp (fmap_gmap_exact r)).symm
  · exact (ModuleCat.mono_iff_injective _).mpr (fmap_injective r)
  · exact (ModuleCat.epi_iff_surjective _).mpr (gmap_surjective r)

/-- **Universal coefficients for free coefficients `ℤ^r`**: if the terms of `K` are flat and
`H_m(K)` is finitely generated, then `H_m(K ⊗ ℤ^r)` is finitely generated.  The long exact sequence
of `0 → ℤ^r → ℤ^{r+1} → ℤ → 0`, tensored with `K`, gives the induction step; the base case `r = 0`
is the case of a complex whose terms are tensor products with a subsingleton module. -/
theorem expTensFinFG (K : ChainComplex (ModuleCat ℤ) ℕ) (hK : ∀ n, Module.Flat ℤ (K.X n))
    (m : ℕ) (hm : Module.Finite ℤ (K.homology m)) (r : ℕ) :
    Module.Finite ℤ ((expTens K (ModuleCat.of ℤ (Fin r → ℤ))).homology m) := by
  induction r with
  | zero =>
      refine fg_homology_of_subsingleton_terms _ (fun n => ?_) m
      rw [expTens_X]
      exact subsingleton_tensor_right (M := K.X n) inferInstance
  | succ r ih =>
      haveI hS : (freeSES r).ShortExact := freeSES_shortExact r
      have h1 : Module.Finite ℤ ((expTensShort K (freeSES r)).X₁.homology m) := ih
      have h3 : Module.Finite ℤ ((expTensShort K (freeSES r)).X₃.homology m) := by
        haveI : Module.Finite ℤ
            ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).obj K) := hm
        exact moduleCatFiniteOfIso
          (((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso
            (expTensUnitIso K)).symm)
      exact finite_homology_middle (K := K) (freeSES r) hS hK m h1 h3

/-- **Universal coefficients for free coefficients of finite rank**: if the terms of `K` are flat
and `H_m(K)` is finitely generated, then so is `H_m(K ⊗ Q)` for every finitely generated free
`ℤ`-module `Q`. -/
theorem expTensFreeFG (K : ChainComplex (ModuleCat ℤ) ℕ) (hK : ∀ n, Module.Flat ℤ (K.X n))
    (m : ℕ) (hm : Module.Finite ℤ (K.homology m)) (Q : ModuleCat ℤ) [Module.Free ℤ Q]
    [Module.Finite ℤ Q] : Module.Finite ℤ ((expTens K Q).homology m) := by
  obtain ⟨r, ⟨e⟩⟩ := exists_iso_fin_int Q
  haveI : Module.Finite ℤ
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).obj
        (expTens K (ModuleCat.of ℤ (Fin r → ℤ)))) := expTensFinFG K hK m hm r
  exact moduleCatFiniteOfIso
    (((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso (expTensIso e K)).symm)

/-! ## 4. Universal coefficients in finiteness form -/

/-- **The universal coefficient theorem, finiteness form, for the naive tensor complex.**  If the
terms of `K` are free and `M` is a finitely generated `ℤ`-module, then `H_n(K ⊗ M)` is finitely
generated as soon as `H_n(K)` and `H_{n-1}(K)` are.

Choose a presentation `0 → P → Q → M → 0` of `M` with `P`, `Q` free of finite rank and tensor it
with the flat complex `K`: the resulting long exact sequence in homology exhibits `H_n(K ⊗ M)` as an
extension of a quotient of `H_n(K ⊗ Q)` by a submodule of `H_{n-1}(K ⊗ P)`, both finitely generated
by `Work.SSS.expTensFreeFG`. -/
theorem expTensFG (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ)
    (hK : ∀ n : ℕ, Module.Free ℤ (K.X n)) (hM : Module.Finite ℤ M) (n : ℕ)
    (h1 : Module.Finite ℤ (K.homology n)) (h2 : Module.Finite ℤ (K.homology (n - 1))) :
    Module.Finite ℤ ((expTens K M).homology n) := by
  have hflat : ∀ i, Module.Flat ℤ (K.X i) := fun i => Module.Flat.of_free
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    obtain ⟨zeq⟩ := expTensHomologyZero K M
    haveI : Module.Finite ℤ ↥(K.homology 0 ⊗ M) :=
      Module.Finite.tensorProduct ℤ ↥(K.homology 0) ↥M
    exact moduleCatFiniteOfIso zeq.symm
  · obtain ⟨P, Q, f, g, h, hPfree, hPfin, hQfree, hQfin, hS⟩ := exists_shortExact_free M hM
    haveI : Module.Free ℤ P := hPfree
    haveI : Module.Finite ℤ P := hPfin
    haveI : Module.Free ℤ Q := hQfree
    haveI : Module.Finite ℤ Q := hQfin
    have hX₂ : Module.Finite ℤ ((expTensShort K (ShortComplex.mk f g h)).X₂.homology n) :=
      expTensFreeFG K hflat n h1 Q
    have hX₁ : Module.Finite ℤ ((expTensShort K (ShortComplex.mk f g h)).X₁.homology (n - 1)) :=
      expTensFreeFG K hflat (n - 1) h2 P
    exact finite_homology_third (K := K) (ShortComplex.mk f g h) hS hflat n hn hX₂ hX₁

/-! ## 5. Finiteness of singular homology with finitely generated coefficients -/

/-- **Finiteness of singular homology with finitely generated coefficients.**  If `H_s(B;ℤ)` and
`H_{s-1}(B;ℤ)` are finitely generated and `M` is a finitely generated `ℤ`-module, then so is
`H_s(B;M)`.  This is the universal coefficient theorem
`H_s(B;M) ≅ H_s(B;ℤ) ⊗ M ⊕ Tor(H_{s-1}(B;ℤ), M)` read in the Serre class of finitely generated
abelian groups. -/
theorem singularCoeffFG {B : Type} [TopologicalSpace B] (M : ModuleCat ℤ) (s : ℕ)
    (hs : Module.Finite ℤ (Work.PiS.HZ B s)) (hs1 : Module.Finite ℤ (Work.PiS.HZ B (s - 1)))
    (hM : Module.Finite ℤ M) :
    Module.Finite ℤ (HZCoeff B M s) := by
  let X : SSet := TopCat.toSSet.obj (TopCat.of B)
  let K : ChainComplex (ModuleCat ℤ) ℕ := X.chainComplex (ModuleCat.of ℤ ℤ)
  have hfree : ∀ n, Module.Free ℤ (K.X n) := fun n => sChains_free X n
  have h1 : Module.Finite ℤ (K.homology s) := hs
  have h2 : Module.Finite ℤ (K.homology (s - 1)) := hs1
  haveI hfin : Module.Finite ℤ ((expTens K M).homology s) :=
    expTensFG K M hfree hM s h1 h2
  have e : X.chainComplex M ≅ expTens K M := chainCoeffExpIso X M
  have hhom : (X.chainComplex M).homology s ≅ (expTens K M).homology s :=
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) s).mapIso e
  exact Module.Finite.equiv (Iso.toLinearEquiv hhom).symm

end

end Work.SSS
