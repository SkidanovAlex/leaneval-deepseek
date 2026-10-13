import Mathlib
import Submission.Work.DSF1.Sheaf.acyclicAffineHomDefs
import Submission.Work.DSF1.Sheaf.affineHomAcycAux
import Submission.Work.DSF1.Sheaf.pushforward_injective
import Submission.Work.DSF1.Sheaf.isZero_iff_forall_modStalk
import Submission.Work.DSF1.Sheaf.modStalk_preservesHomology

/-!
# Leray vanishing for an affine open immersion, via stalks

This module proves `Work.DSF1.Sheaf.isZero_homology_pushforward_injectiveResolution`: if `I` is an
injective resolution of the structure sheaf of an open `W ⊆ X` and the complex of sections of `I`
over every affine open of `W` is acyclic in positive degrees (the hypothesis `hL2`, supplied by
`Work.DSF1.Sheaf.sectionsAffineAcyclic`), then the complex of sheaves obtained by pushing `I`
forward along `W.ι` is exact in positive degrees.

The argument is the standard Leray degeneration check on stalks: a sheaf of modules is zero if and
only if all its stalks are zero (`isZero_iff_forall_modStalk`) and the stalk functor commutes with
homology (`modStalk_preservesHomology`), so it suffices to check that the stalk complex at each
point `x` is exact in positive degrees.  There, a cycle is lifted to a section `s` over an affine
neighbourhood of `x` (`exists_mem_germ_eq_of_isBasis` with `X.isBasis_affineOpens`), the vanishing
of the germ of `δ s` gives a smaller neighbourhood `U₁ ∋ x` on which `s` is a cycle
(`TopCat.Presheaf.germ_eq`), and after shrinking to an affine `V ⊆ U₁` one concludes with the
acyclicity of the sections of `I` over the affine open `V ∩ W` of `W`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- For `n > 0`, the vanishing of the `n`-th homology of a cochain complex of abelian groups is
equivalent to the statement that every cycle in degree `n` is a boundary. -/
lemma homology_isZero_iff_of_pos {K : CochainComplex AddCommGrpCat.{u} ℕ} {n : ℕ} (hn : 0 < n) :
    IsZero (K.homology n) ↔
      ∀ y : K.X n, K.d n (n + 1) y = 0 → ∃ x : K.X (n - 1), K.d (n - 1) n x = y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' (K := K) m (m + 1) (m + 2)
      (ComplexShape.prev_eq' _ (ComplexShape.up_mk m (m + 1) rfl))
      (ComplexShape.next_eq' _ (ComplexShape.up_mk (m + 1) (m + 2) rfl))]
  exact ShortComplex.exact_iff_forall_exists

/-- **Leray vanishing, in the form of acyclicity of the pushed forward injective resolution.**
If `I` is an injective resolution of the structure sheaf of `W` and `hL2` is the statement that
the complex of sections of `I` over an affine open of `W` is acyclic in positive degrees, then the
complex obtained by pushing `I` forward along the affine open immersion `W.ι` is exact in positive
degrees. -/
theorem isZero_homology_pushforward_injectiveResolution {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Opens)
    (haff : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W))
    (I : CategoryTheory.InjectiveResolution (Work.DSF1.Sheaf.unitSheaf W))
    (hL2 : ∀ (U : W.toScheme.Opens), AlgebraicGeometry.IsAffineOpen U → ∀ n, 0 < n → IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        (((Work.DSF1.Sheaf.sectionsFunctor W.toScheme U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)))
    (hPH : ∀ x : X, (modStalk X x).PreservesHomology)
    (n : ℕ) (hn : 0 < n) :
    IsZero (HomologicalComplex.homology
      (((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex) n) := by
  set K : CochainComplex X.Modules ℕ :=
    ((Work.DSF1.Sheaf.pushforwardι W).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    with hK
  rw [isZero_iff_forall_modStalk]
  intro x
  haveI : (modStalk X x).PreservesHomology := hPH x
  refine IsZero.of_iso ?_ (homology_iso_mapHomologicalComplex_nat (modStalk X x) K n).some.symm
  set Kx : CochainComplex AddCommGrpCat.{u} ℕ :=
    ((modStalk X x).mapHomologicalComplex (ComplexShape.up ℕ)).obj K with hKx
  show IsZero (Kx.homology n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' (K := Kx) (i := n - 1) (j := n) (k := n + 1)
      (ComplexShape.prev_eq' _ (ComplexShape.up_mk (n - 1) n (by omega)))
      (ComplexShape.next_eq' _ (ComplexShape.up_mk n (n + 1) rfl))]
  rw [ShortComplex.exact_iff_forall_exists]
  intro y hy
  -- the underlying presheaf of `K` in degree `n`
  obtain ⟨U, hxU, hUmem, s, hs⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis (C := AddCommGrpCat.{u})
      (B := X.affineOpens) X.isBasis_affineOpens
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj ((toAbsheaf X).obj (K.X n)))
      x (y : ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X n))).stalk x)
  -- (1) the germ of the differential of `s` is zero
  have hd : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
        ((toAbsheaf X).map (K.d n (n + 1))))
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X n))).germ U x hxU s) = 0 := by
    rw [hs]
    exact hy
  have hd' : ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
      ((toAbsheaf X).obj (K.X (n + 1)))).germ U x hxU
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
        ((toAbsheaf X).map (K.d n (n + 1)))).app (Opposite.op U) s) = 0 := by
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply
      (F := (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X n)))
      (G := (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X (n + 1))))
      U x hxU ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
        ((toAbsheaf X).map (K.d n (n + 1)))) s]
    exact hd
  -- (2) hence the differential of `s` restricts to zero on a smaller neighbourhood
  obtain ⟨U₁, hxU₁, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
      ((toAbsheaf X).obj (K.X (n + 1)))) (U := U) (V := U) x hxU hxU
    (((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
      ((toAbsheaf X).map (K.d n (n + 1)))).app (Opposite.op U) s) 0
    (by rw [hd']; simp)
  have hU₁U : U₁ ≤ U := leOfHom iU
  -- (3) shrink further to an affine neighbourhood `V ⊆ U₁` of `x`
  obtain ⟨V, hVaff, hxV, hVU₁'⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := x) hxU₁
  have hVU₁ : V ≤ U₁ := hVU₁'
  have hVU : V ≤ U := le_trans hVU₁ hU₁U
  let Fn : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj ((toAbsheaf X).obj (K.X n))
  let Fs : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj ((toAbsheaf X).obj (K.X (n + 1)))
  let δ : Fn ⟶ Fs := (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
    ((toAbsheaf X).map (K.d n (n + 1)))
  let sV : Fn.obj (Opposite.op V) := Fn.map (homOfLE hVU).op s
  have hd_V : δ.app (Opposite.op V) sV = 0 := by
    have hnat : δ.app (Opposite.op V) (Fn.map (homOfLE hVU).op s)
        = Fs.map (homOfLE hVU).op (δ.app (Opposite.op U) s) := by
      have h := ConcreteCategory.congr_hom (δ.naturality (homOfLE hVU).op) s
      simpa only [ConcreteCategory.comp_apply] using h
    have hone : Fs.map (homOfLE hVU).op (δ.app (Opposite.op U) s) = 0 := by
      have h3 : Fs.map iU.op (δ.app (Opposite.op U) s) = 0 := by
        simpa only [map_zero] using heq
      have hop : iU.op ≫ (homOfLE hVU₁).op = (homOfLE hVU).op := by
        have h : homOfLE hVU₁ ≫ iU = homOfLE hVU := Subsingleton.elim _ _
        simpa using congrArg Quiver.Hom.op h
      calc Fs.map (homOfLE hVU).op (δ.app (Opposite.op U) s)
          = Fs.map (iU.op ≫ (homOfLE hVU₁).op) (δ.app (Opposite.op U) s) := by rw [hop]
        _ = Fs.map (homOfLE hVU₁).op (Fs.map iU.op (δ.app (Opposite.op U) s)) := by
              rw [Functor.map_comp]
              rfl
        _ = 0 := by rw [h3, map_zero]
    rw [show δ.app (Opposite.op V) sV
        = Fs.map (homOfLE hVU).op (δ.app (Opposite.op U) s) from hnat, hone]
  -- (4) apply the acyclicity of the sections of `I` over the affine open `V ⊓ W`
  haveI : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W) := haff
  have hUaff : AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.Opens.ι W) ⁻¹ᵁ V) :=
    hVaff.preimage (AlgebraicGeometry.Scheme.Opens.ι W)
  obtain ⟨t, ht⟩ := (homology_isZero_iff_of_pos (K := (sectionsFunctor W.toScheme
      ((AlgebraicGeometry.Scheme.Opens.ι W) ⁻¹ᵁ V)).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.obj I.cocomplex) hn).mp
    (hL2 ((AlgebraicGeometry.Scheme.Opens.ι W) ⁻¹ᵁ V) hUaff n hn)
    sV hd_V
  -- (5) the germ of `t` at `x` is the required preimage of `y`
  have hstep : Kx.d (n - 1) n (((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
      ((toAbsheaf X).obj (K.X (n - 1)))).germ V x hxV t)
      = ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X n))).germ V x hxV sV := by
    have h1 : Kx.d (n - 1) n (((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X (n - 1)))).germ V x hxV t)
        = ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
          ((toAbsheaf X).obj (K.X n))).germ V x hxV
            (((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
              ((toAbsheaf X).map (K.d (n - 1) n))).app (Opposite.op V) t) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
          ((toAbsheaf X).map (K.d (n - 1) n))) t
    have h2 : ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).map
        ((toAbsheaf X).map (K.d (n - 1) n))).app (Opposite.op V) t = sV := ht
    rw [h1, h2]
  have hres : ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
      ((toAbsheaf X).obj (K.X n))).germ V x hxV sV = y := by
    have h1 : ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
        ((toAbsheaf X).obj (K.X n))).germ V x hxV (Fn.map (homOfLE hVU).op s)
        = ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).obj
          ((toAbsheaf X).obj (K.X n))).germ U x hxU s :=
      TopCat.Presheaf.germ_res_apply Fn (homOfLE hVU) x hxV s
    rw [show sV = Fn.map (homOfLE hVU).op s from rfl, h1, hs]
  exact ⟨_, hstep.trans hres⟩

end Work.DSF1.Sheaf
