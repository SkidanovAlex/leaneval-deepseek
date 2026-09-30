import Mathlib
import Submission.Work.SSS.baseRowDefs
import Submission.Work.SSS.LESFacts

/-!
# The terminal step of the bottom-row argument

This file proves `Work.SSS.Lem.fgQuot_baseZ_terminal`, the last (bottom) step of the bottom-row
argument of the spectral sequence of a saturated filtration `ξ`.

For a chain complex `C` of `ℤ`-modules, `m : ℕ` and the filtration `ξ`, the objects are

* `baseB ξ m ⊆ E¹_{m+1,0}`: the image of `d¹ : E¹_{m+2,0} → E¹_{m+1,0}`,
* `baseZ ξ m (m+2) ⊆ E¹_{m+1,0}`: the preimage under the connecting map `k : E¹_{m+1,0} → H_m(F_m)`
  of `baseJ ξ m (m+2) = Ψ_{m+1-(m+2)} = Ψ_{-1} = 0`.

Thus `baseZ ξ m (m+2) = ker (kF ξ m 0)`.  By exactness of the long exact sequence of
`0 → F_m → F_{m+1} → F_{m+1}/F_m → 0` this is the image of `j : H_{m+1}(F_{m+1}) → E¹_{m+1,0}`,
and by exactness of the long exact sequence of `0 → F_{m+1} → F_{m+2} → grF ξ (m+2) → 0` the
submodule `baseB ξ m` is the image under `j` of `ker (H_{m+1}(F_{m+1}) → H_{m+1}(F_{m+2}))`.

Hence `baseZ ξ m (m+2)/baseB ξ m` is a quotient of the image of
`H_{m+1}(F_{m+1}) → H_{m+1}(F_{m+2})`; finally saturation of `ξ` makes `incl (m+2)` an isomorphism
in degrees `m`, `m+1`, `m+2`, so that `H_{m+1}(F_{m+2}) ≅ H_{m+1}(C)`, which is finitely generated
by hypothesis.  The result follows from `ℤ` being Noetherian.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- **Saturation, made explicit.**  If `k ≤ n` then the component of the inclusion
`ξ.incl n : F_n ⟶ C` in degree `k` is an isomorphism.  (The saturation axiom gives this for
`k = n`; for `k ≤ n` one factors `ξ.incl k` through `ξ.incl n` using compatibility.) -/
lemma incl_isIso_of_le (ξ : Work.SSS.Filtration C) {k n : ℕ} (h : k ≤ n) :
    IsIso ((ξ.incl n).f k) := by
  have hcomp := congrArg (fun φ => φ.f k) (ξ.compat h)
  rw [HomologicalComplex.comp_f] at hcomp
  haveI hker : IsIso ((ξ.F.map (homOfLE h)).f k ≫ (ξ.incl n).f k) := by
    rw [hcomp]; exact ξ.sat k
  have hbij : Function.Bijective
      (ModuleCat.Hom.hom ((ξ.F.map (homOfLE h)).f k ≫ (ξ.incl n).f k)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hker
  rw [ModuleCat.hom_comp] at hbij
  haveI hmono : Mono ((ξ.incl n).f k) := by
    haveI := ξ.mono_incl n
    exact Functor.map_mono (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) k)
      (ξ.incl n)
  have hinj : Function.Injective (ModuleCat.Hom.hom ((ξ.incl n).f k)) :=
    (ModuleCat.mono_iff_injective _).mp hmono
  have hsurj : Function.Surjective (ModuleCat.Hom.hom ((ξ.incl n).f k)) := by
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    exact ⟨_, hx⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

/-- **Finiteness of the homology of a filtration term.**  If `i + 1 ≤ n` then
`H_i(F_n) ≅ H_i(C)`, because `ξ.incl n` is an isomorphism in degrees `i + 1`, `i` and `i - 1`,
which are exactly the degrees entering `H_i`.  Hence `H_i(F_n)` is finitely generated when `H_i(C)`
is. -/
lemma finHomology_of_le (ξ : Work.SSS.Filtration C) (n i : ℕ) (h : i + 1 ≤ n)
    (hH : Module.Finite ℤ (C.homology i)) :
    Module.Finite ℤ ((ξ.F.obj n).homology i) := by
  haveI hprev : IsIso ((ξ.incl n).f ((ComplexShape.down ℕ).prev i)) := by
    rw [show (ComplexShape.down ℕ).prev i = i + 1 from
      ComplexShape.prev_eq' _
        (show (ComplexShape.down ℕ).Rel (i + 1) i from by rw [ComplexShape.down_Rel])]
    exact incl_isIso_of_le ξ (by omega)
  haveI hcur : IsIso ((ξ.incl n).f i) := incl_isIso_of_le ξ (by omega)
  haveI hnext : IsIso ((ξ.incl n).f ((ComplexShape.down ℕ).next i)) := by
    have hle : (ComplexShape.down ℕ).next i ≤ n := by
      rcases Nat.eq_zero_or_pos i with h0 | hi
      · subst h0
        rw [show (ComplexShape.down ℕ).next 0 = 0 from
          ComplexShape.next_eq_self' _ _ (by intro k; rw [ComplexShape.down_Rel]; omega)]
        omega
      · rw [show (ComplexShape.down ℕ).next i = i - 1 from
          ComplexShape.next_eq' _
            (show (ComplexShape.down ℕ).Rel i (i - 1) from by rw [ComplexShape.down_Rel]; omega)]
        omega
    exact incl_isIso_of_le ξ hle
  haveI hss : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) i).map (ξ.incl n)) := by
    rw [ShortComplex.isIso_iff]
    exact ⟨hprev, hcur, hnext⟩
  haveI hiso : IsIso (HomologicalComplex.homologyMap (ξ.incl n) i) :=
    ShortComplex.isIso_homologyMap_of_iso
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).map
        (ξ.incl n))
  have hbij : Function.Bijective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (ξ.incl n) i)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hiso
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ hbij).symm

/-- **The linear algebra of the bottom-row quotient.**  For a ring `R`, linear maps
`j : H →ₗ A`, `α : H →ₗ H'` and a finitely generated `H'`, the quotient
`j(H) / j(ker α)` — which is the image of `j.range` in the quotient of `A` by `j(ker α)` — is
finitely generated.

Indeed the composite `mkQ (j(ker α)) ∘ j` has kernel `ker α ⊔ ker j`, so its range is a quotient of
`H ⧸ ker α ≅ α.range`, which is a submodule of the finitely generated module `H'`. -/
lemma fgQuot_map_mkQ_range {R : Type*} [CommRing R] [IsNoetherianRing R]
    {H A H' : Type*} [AddCommGroup H] [Module R H] [AddCommGroup A]
    [Module R A] [AddCommGroup H'] [Module R H']
    (j : H →ₗ[R] A) (α : H →ₗ[R] H') (h : Module.Finite R H') :
    Work.SSS.FgQuot (Submodule.map j α.ker) j.range := by
  rw [Work.SSS.FgQuot]
  set B := Submodule.map j α.ker with hB
  haveI hfin : Module.Finite R ↥α.range :=
    Module.Finite.iff_fg.mpr (Submodule.FG.of_le (Module.finite_def.mp h) le_top)
  haveI hq : Module.Finite R (H ⧸ α.ker) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange α).symm
  haveI hqq : Module.Finite R
      ((H ⧸ α.ker) ⧸ (Submodule.map (Submodule.mkQ α.ker) j.ker)) :=
    Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  haveI hsup : Module.Finite R (H ⧸ (α.ker ⊔ j.ker)) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotientSup α.ker j.ker)
  have hker : (Submodule.mkQ B ∘ₗ j).ker = α.ker ⊔ j.ker := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hB, Submodule.comap_map_eq]
  haveI : Module.Finite R (H ⧸ (Submodule.mkQ B ∘ₗ j).ker) := by rw [hker]; exact hsup
  haveI : Module.Finite R ↥((Submodule.mkQ B ∘ₗ j).range) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange _)
  rw [← LinearMap.range_comp]
  exact Module.Finite.iff_fg.mp this

set_option backward.isDefEq.respectTransparency false in
/-- **The terminal step of the bottom-row argument**: `baseZ ξ m (m+2) / baseB ξ m` is finitely
generated, given that `H_{m+1}(C)` is. -/
theorem fgQuot_baseZ_terminal {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C)
    (m : ℕ) (hH : Module.Finite ℤ (C.homology (m + 1))) :
    Work.SSS.FgQuot (Work.SSS.baseB ξ m) (Work.SSS.baseZ ξ m (m + 2)) := by
  -- `baseZ ξ m (m+2)` is the preimage of `⊥` under the connecting map, i.e. `ker kF ξ m 0`,
  -- which by exactness is the image of `jF ξ (m+1) 0`.
  have hZ : Work.SSS.baseZ ξ m (m + 2) = (Work.SSS.jF ξ (m + 1) 0).hom.range := by
    have hbj : Work.SSS.baseJ ξ m (m + 2) = ⊥ := by
      rw [Work.SSS.baseJ]; exact dif_neg (by omega)
    rw [Work.SSS.baseZ, hbj, Submodule.comap_bot]
    exact (Work.SSS.range_jF_eq_ker_kF ξ m 0).symm
  -- `baseB ξ m = im (d¹) = im (kF ≫ jF) = jF (ker (H_{m+1}(F_{m+1}) → H_{m+1}(F_{m+2})))`.
  have hB : Work.SSS.baseB ξ m =
      Submodule.map (Work.SSS.jF ξ (m + 1) 0).hom
        ((HomologicalComplex.homologyMap (Work.SSS.incF ξ.F (m + 1)) (m + 1)).hom.ker) := by
    rw [Work.SSS.baseB, Work.SSS.d1, ModuleCat.hom_comp, LinearMap.range_comp,
      ← Work.SSS.range_kF_eq_ker_incF ξ (m + 1) 0]
  rw [hB, hZ]
  exact fgQuot_map_mkQ_range _ _
    (finHomology_of_le ξ (m + 2) (m + 1) (by omega) hH)

end

end Work.SSS.Lem
