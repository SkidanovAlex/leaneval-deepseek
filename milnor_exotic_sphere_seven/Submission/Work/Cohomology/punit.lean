import Mathlib
import Submission.Work.Cohomology.Singular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The positive-degree singular cohomology of the one-point space

The one-point space `PUnit` is contractible, so its reduced singular cohomology vanishes; in
particular `Hⁿ⁺¹(PUnit; R) = 0` for every commutative ring `R` and every `n : ℕ`.

This file proves that statement directly from the explicit shape of the singular chain complex of
the point.  The singular simplicial set `ptSSet` of `PUnit` has exactly one `n`-simplex for every
`n` (it is the terminal simplicial set), so each module `Cₙ` of `n`-chains is free of rank one: the
canonical map `ptGen R n : R ⟶ Cₙ` sending `1` to the (unique) `n`-simplex is an isomorphism
(`isIso_ptGen`).  Mathlib's computation `SSet.ιChainComplex_d` of the differential on the
generators

  `d (n+1) n (ι x) = ∑ i, (-1)^i • ι (δ i x)`

then becomes `ptGen R (n+1) ≫ d (n+1) n = altSum (n+2) • ptGen R n` (`ptGen_d`), where
`altSum m = ∑_{i<m} (-1)^i` is the alternating sum of `m` terms, equal to `0` for `m` even and to
`1` for `m` odd (`altSum_two_mul`, `altSum_two_mul_add_one`).  Consequently

* `d (2j+1) (2j) = 0`      (`ptChains_d_zero`), and
* `d (2j+2) (2j+1)` is an isomorphism (`isIso_ptChains_d`).

Transposing to the cochain complex (`Cⁿ = Hom(Cₙ, R)`, `δⁿ = (d_{n+1,n})ᵀ`) gives

* `dualDifferential R PUnit k = 0` for `k` even, and
* `dualDifferential R PUnit k` is an isomorphism for `k` odd,

which makes the cochain complex exact in every positive degree: for `k = n+1 ≥ 1`, if `k` is even
then `δᵏ = 0` and `δᵏ⁻¹` is surjective, while if `k` is odd then `δᵏ` is injective.  Exactness at
`n+1` of the cochain complex is `IsZero (Hⁿ⁺¹(PUnit; R))`, which is the statement proved below.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-! ## The singular chains of the one-point space -/

/-- The singular simplicial set of the one-point space: the terminal simplicial set, with a unique
`n`-simplex in every degree. -/
abbrev ptSSet : SSet := TopCat.toSSet.obj (TopCat.of PUnit)

instance instSubsingletonPtSSet (n : ℕ) : Subsingleton (ptSSet _⦋n⦌) :=
  ⟨fun _ _ => (TopCat.toSSetObjEquiv (TopCat.of PUnit) _).injective (Subsingleton.elim _ _)⟩

instance instNonemptyPtSSet (n : ℕ) : Nonempty (ptSSet _⦋n⦌) :=
  ⟨(TopCat.toSSetObjEquiv (TopCat.of PUnit) _).symm (ContinuousMap.const _ PUnit.unit)⟩

instance instUniquePtSSet (n : ℕ) : Unique (ptSSet _⦋n⦌) :=
  uniqueOfSubsingleton (Classical.choice (instNonemptyPtSSet n))

/-- The singular chain complex of the one-point space. -/
abbrev ptChains (R : Type) [CommRing R] : ChainComplex (ModuleCat R) ℕ :=
  singularChains R (TopCat.of PUnit)

/-- A canonical generator of the module of `n`-chains of the point: `1` goes to the unique
`n`-simplex. -/
def ptGen (R : Type) [CommRing R] (n : ℕ) : ModuleCat.of R R ⟶ (ptChains R).X n :=
  SSet.ιChainComplex (X := ptSSet) (R := ModuleCat.of R R) (default : ptSSet _⦋n⦌)

/-- The `n`-chains of the point form a free module of rank one: `ptGen R n` is an isomorphism
(it is the coproduct inclusion of a coproduct indexed by a single-element type). -/
lemma isIso_ptGen (R : Type) [CommRing R] (n : ℕ) : IsIso (ptGen R n) := by
  rw [ptGen, show SSet.ιChainComplex (X := ptSSet) (R := ModuleCat.of R R)
      (default : ptSSet _⦋n⦌)
      = (coproductUniqueIso (fun _ : ptSSet _⦋n⦌ => ModuleCat.of R R)).inv from rfl]
  infer_instance

/-! ## The alternating sum `∑_{i<m} (-1)^i` -/

/-- The alternating sum of `m` terms, `∑_{i<m} (-1)^i`. -/
def altSum (m : ℕ) : ℤ := ∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ)

lemma altSum_succ (m : ℕ) : altSum (m+1) = 1 - altSum m := by
  unfold altSum
  rw [Fin.sum_univ_succ]
  have h : ∀ i : Fin m, (-1 : ℤ) ^ ((i.succ : Fin (m+1)) : ℕ)
      = -((-1 : ℤ) ^ ((i : Fin m) : ℕ)) := by
    intro i
    rw [Fin.val_succ, pow_succ]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_neg_distrib]
  simp only [Fin.val_zero, pow_zero]
  ring

lemma altSum_add_two (m : ℕ) : altSum (m+2) = altSum m := by
  rw [show m+2 = (m+1)+1 from rfl, altSum_succ, altSum_succ]
  ring

lemma altSum_two_mul (j : ℕ) : altSum (2*j) = 0 := by
  induction j with
  | zero => simp [altSum]
  | succ j ih =>
      rw [show 2*(j+1) = 2*j + 2 from by ring, altSum_add_two]
      exact ih

lemma altSum_two_mul_add_one (j : ℕ) : altSum (2*j+1) = 1 := by
  induction j with
  | zero => simp [altSum]
  | succ j ih =>
      rw [show 2*(j+1)+1 = (2*j+1) + 2 from by ring, altSum_add_two]
      exact ih

/-! ## The differentials of the singular chain complex of the point -/

/-- The differential of the singular chain complex of the point, on the canonical generators: it is
multiplication by the alternating sum `altSum (k+2)`. -/
lemma ptGen_d (R : Type) [CommRing R] (k : ℕ) :
    ptGen R (k+1) ≫ (ptChains R).d (k+1) k = altSum (k+2) • ptGen R k := by
  have h := SSet.ιChainComplex_d (X := ptSSet) (R := ModuleCat.of R R)
    (n := k) (default : ptSSet _⦋k+1⦌)
  have key : ∀ x : ptSSet _⦋k⦌,
      SSet.ιChainComplex (X := ptSSet) (R := ModuleCat.of R R) x = ptGen R k :=
    fun x => congrArg (fun y => SSet.ιChainComplex (X := ptSSet) (R := ModuleCat.of R R) y)
      (Subsingleton.elim x default)
  rw [show ptGen R (k+1) = SSet.ιChainComplex (X := ptSSet) (R := ModuleCat.of R R)
      (default : ptSSet _⦋k+1⦌) from rfl]
  rw [show (ptChains R).d (k+1) k = (ptSSet.chainComplex (ModuleCat.of R R)).d (k+1) k from rfl]
  rw [h]
  conv_lhs => arg 2; ext i; rw [key _]
  rw [← Finset.sum_smul, altSum]

/-- The odd differentials of the singular chain complex of the point vanish. -/
lemma ptChains_d_zero (R : Type) [CommRing R] (j : ℕ) :
    (ptChains R).d (2*j+1) (2*j) = 0 := by
  haveI : IsIso (ptGen R (2*j+1)) := isIso_ptGen R (2*j+1)
  have h := ptGen_d R (2*j)
  rw [show 2*j+2 = 2*(j+1) from by ring, altSum_two_mul (j+1), zero_smul] at h
  have h' := congrArg (fun m => inv (ptGen R (2*j+1)) ≫ m) h
  simpa [IsIso.inv_hom_id, Category.assoc] using h'

/-- The even differentials of the singular chain complex of the point are isomorphisms. -/
lemma isIso_ptChains_d (R : Type) [CommRing R] (j : ℕ) :
    IsIso ((ptChains R).d (2*j+1+1) (2*j+1)) := by
  haveI h1 : IsIso (ptGen R (2*j+1+1)) := isIso_ptGen R (2*j+1+1)
  have h := ptGen_d R (2*j+1)
  rw [show (2*j+1)+2 = 2*(j+1)+1 from by ring, altSum_two_mul_add_one (j+1), one_smul] at h
  haveI h3 : IsIso (ptGen R (2*j+1+1) ≫ (ptChains R).d (2*j+1+1) (2*j+1)) := by
    rw [h]; exact isIso_ptGen R (2*j+1)
  exact IsIso.of_isIso_comp_left (ptGen R (2*j+1+1)) ((ptChains R).d (2*j+1+1) (2*j+1))

/-! ## Transposing to the cochain complex -/

/-- The transpose of an isomorphism of modules is an isomorphism of the dual modules. -/
lemma isIso_ofHom_dualMap (R : Type) [CommRing R] {M N : ModuleCat R} (f : M ⟶ N) [IsIso f] :
    IsIso (ModuleCat.ofHom f.hom.dualMap) := by
  rw [show ModuleCat.ofHom f.hom.dualMap
      = (LinearEquiv.ofBijective f.hom
          (ConcreteCategory.bijective_of_isIso f)).dualMap.toModuleIso.hom from by
    apply ModuleCat.hom_ext
    ext φ x
    rfl]
  infer_instance

/-- The `k`-th differential of the cochain complex of the point is the transpose of the
`(k+1)`-st differential of its chain complex. -/
lemma dualDifferential_pt_eq (R : Type) [CommRing R] (k : ℕ) :
    dualDifferential R (TopCat.of PUnit) k
      = ModuleCat.ofHom ((ptChains R).d (k+1) k).hom.dualMap := by
  apply ModuleCat.hom_ext
  ext φ x
  rfl

/-- The differential of the cochain complex of the point, evaluated. -/
@[simp]
lemma dualDifferential_pt_apply (R : Type) [CommRing R] (k : ℕ)
    (φ : dualChains R (TopCat.of PUnit) k) (x : (ptChains R).X (k+1)) :
    (dualDifferential R (TopCat.of PUnit) k).hom φ x = φ (((ptChains R).d (k+1) k).hom x) := by
  simp [dualDifferential, ModuleCat.hom_ofHom]

/-- In even degrees the cochain differential of the point vanishes. -/
lemma dualDifferential_pt_zero (R : Type) [CommRing R] {k : ℕ} (hk : Even k) :
    dualDifferential R (TopCat.of PUnit) k = 0 := by
  obtain ⟨j, rfl⟩ := hk
  rw [show j + j = 2*j from by ring]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  ext φ x
  simp [dualDifferential, ptChains_d_zero]

/-- In odd degrees the cochain differential of the point is an isomorphism. -/
lemma isIso_dualDifferential_pt (R : Type) [CommRing R] {k : ℕ} (hk : Odd k) :
    IsIso (dualDifferential R (TopCat.of PUnit) k) := by
  obtain ⟨j, rfl⟩ := hk
  haveI hd : IsIso ((ptChains R).d (2*j+1+1) (2*j+1)) := isIso_ptChains_d R j
  rw [dualDifferential_pt_eq]
  exact isIso_ofHom_dualMap R (f := (ptChains R).d (2*j+1+1) (2*j+1))

lemma even_succ_odd {n : ℕ} (hn : Even n) : Odd (n+1) := by
  obtain ⟨j, hj⟩ := hn
  exact ⟨j, by omega⟩

lemma odd_succ_even {n : ℕ} (hn : Odd n) : Even (n+1) := by
  obtain ⟨j, hj⟩ := hn
  exact ⟨j+1, by omega⟩

/-! ## The vanishing of the positive-degree cohomology of the point -/

theorem punit (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology R (n + 1) (TopCat.of PUnit)) := by
  let K := Work.Cohomology.singularCochainComplex R (TopCat.of PUnit)
  have hd : ∀ m : ℕ, K.d m (m+1) = dualDifferential R (TopCat.of PUnit) m := by
    intro m
    simp only [K, Work.Cohomology.singularCochainComplex, CochainComplex.of, CochainComplex.of.d]
    rfl
  rw [show Work.Cohomology.singularCohomology R (n+1) (TopCat.of PUnit) = K.homology (n+1)
    from rfl]
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [K.exactAt_iff' n (n+1) (n+2)
    (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel n (n+1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl))]
  have hf : (K.sc' n (n+1) (n+2)).f = dualDifferential R (TopCat.of PUnit) n := by
    rw [show (K.sc' n (n+1) (n+2)).f = K.d n (n+1) from rfl]
    exact hd n
  have hg : (K.sc' n (n+1) (n+2)).g = dualDifferential R (TopCat.of PUnit) (n+1) := by
    rw [show (K.sc' n (n+1) (n+2)).g = K.d (n+1) (n+2) from rfl]
    exact hd (n+1)
  rcases Nat.even_or_odd n with hn | hn
  · -- `n` even: the outgoing differential vanishes and the incoming one is onto.
    have hf0 : (K.sc' n (n+1) (n+2)).f = 0 := by rw [hf, dualDifferential_pt_zero R hn]
    refine (ShortComplex.exact_iff_mono _ hf0).mpr ?_
    rw [hg]
    haveI : IsIso (dualDifferential R (TopCat.of PUnit) (n+1)) :=
      isIso_dualDifferential_pt R (even_succ_odd hn)
    infer_instance
  · -- `n` odd: the incoming differential vanishes and the outgoing one is injective.
    have hg0 : (K.sc' n (n+1) (n+2)).g = 0 := by
      rw [hg, dualDifferential_pt_zero R (odd_succ_even hn)]
    refine (ShortComplex.exact_iff_epi _ hg0).mpr ?_
    rw [hf]
    haveI : IsIso (dualDifferential R (TopCat.of PUnit) n) := isIso_dualDifferential_pt R hn
    infer_instance

end

end Work.Cohomology
