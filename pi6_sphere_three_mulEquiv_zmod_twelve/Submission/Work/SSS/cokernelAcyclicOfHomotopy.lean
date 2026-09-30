import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- A version of Mathlib's `prevD_nat` for *chain* complexes: the "previous differential"
contribution `prevD i f` of a family of morphisms `f` uses the maps leaving degree `i`, and for a
chain complex indexed by `ℕ` the only relevant index above `i` is `i + 1`. -/
theorem prevD_chain_nat {V : Type*} [Category V] [Preadditive V] (C D : ChainComplex V ℕ)
    (i : ℕ) (g : ∀ i j, C.X i ⟶ D.X j) :
    prevD i g = g i (i + 1) ≫ D.d (i + 1) i := by
  show g i ((ComplexShape.down ℕ).prev i) ≫ D.d ((ComplexShape.down ℕ).prev i) i =
    g i (i + 1) ≫ D.d (i + 1) i
  rw [ComplexShape.prev_eq' (c := ComplexShape.down ℕ) (i := i) (j := i + 1) rfl]

/-- **Acyclicity of the cokernel of a chain map homotopic to the identity.**  Let `a : A ⟶ C` be a monomorphism of chain complexes of `ℤ`-modules, `f : C ⟶ C` a chain map homotopic to the identity via `K`, and suppose `f` factors through `a` (`f = f' ≫ a`), so that `f` induces the zero map on the cokernel `Q = cokernel a`.  If moreover the homotopy `K` is "relative to `A`" in the sense that `a.f i ≫ K.hom i (i+1) ≫ (cokernel.π a).f (i+1) = 0` for all `i`, then the cokernel complex `Q` is acyclic.  Proof sketch: the degreewise cokernel projection `(cokernel.π a).f i` is the cokernel of `a.f i`, because `a` is mono so `A ⟶ C ⟶ cokernel a` is a short exact short complex of complexes, and the evaluation functor `HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) i` preserves finite limits and colimits, so `ShortComplex.ShortExact.map_of_exact` followed by `ShortComplex.ShortExact.gIsCokernel` applies.  That universal property together with `hcomp` lets one define maps `k i j : (cokernel a).X i ⟶ (cokernel a).X j` vanishing unless `j = i+1` and satisfying `(cokernel.π a).f i ≫ k i (i+1) = K.hom i (i+1) ≫ (cokernel.π a).f (i+1)`, after which `Homotopy (𝟙 (cokernel a)) 0` follows by cancelling the epimorphism `(cokernel.π a).f i` in `Homotopy.comm`; a null-homotopic identity has vanishing homology. -/
theorem cokernelAcyclicOfHomotopy
    {A C : ChainComplex (ModuleCat ℤ) ℕ} (a : A ⟶ C) [Mono a]
    {f : C ⟶ C} {f' : C ⟶ A} (K : Homotopy (𝟙 C) f) (hf : f' ≫ a = f)
    (hcomp : ∀ i : ℕ, a.f i ≫ K.hom i (i + 1) ≫ (cokernel.π a).f (i + 1) = 0) :
    ∀ m : ℕ, IsZero ((cokernel a).homology m) := by
  -- The degreewise cokernel projection is the cokernel of `a.f i`.
  have hcok : ∀ i : ℕ, IsColimit (CokernelCofork.ofπ ((cokernel.π a).f i) (by
      rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f])) := by
    intro i
    have hS : (ShortComplex.cokernelSequence a).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact a)
        (inferInstanceAs (Mono a)) inferInstance
    have h2 := hS.map_of_exact (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) i)
    exact h2.gIsCokernel
  -- The induced maps `k i : Q.X i ⟶ Q.X (i+1)`.
  let kkData : ∀ i : ℕ, { l : (cokernel a).X i ⟶ (cokernel a).X (i + 1) //
      (cokernel.π a).f i ≫ l = K.hom i (i + 1) ≫ (cokernel.π a).f (i + 1) } := fun i =>
    CokernelCofork.IsColimit.desc' (hcok i) (K.hom i (i + 1) ≫ (cokernel.π a).f (i + 1))
      (hcomp i)
  let kk : ∀ i : ℕ, (cokernel a).X i ⟶ (cokernel a).X (i + 1) := fun i => (kkData i).1
  have hk : ∀ i : ℕ,
      (cokernel.π a).f i ≫ kk i = K.hom i (i + 1) ≫ (cokernel.π a).f (i + 1) :=
    fun i => (kkData i).2
  -- The family of maps of the homotopy `𝟙 Q ≃ 0`, supported in the adjacent degrees.
  let homMap : ∀ i j : ℕ, (cokernel a).X i ⟶ (cokernel a).X j := fun i j =>
    if h : j = i + 1 then h.symm ▸ kk i else 0
  have hhom1 : ∀ i : ℕ, homMap i (i + 1) = kk i := fun i => by
    dsimp only [homMap]
    rw [dif_pos rfl]
  have hhom0 : ∀ i j : ℕ, ¬ (ComplexShape.down ℕ).Rel j i → homMap i j = 0 := fun i j hij => by
    dsimp only [homMap]
    rw [dif_neg (fun h : j = i + 1 => hij h.symm)]
  -- `a` is killed by the projection.
  have hap : ∀ i : ℕ, a.f i ≫ (cokernel.π a).f i = 0 := fun i => by
    have h := congrArg (fun (φ : A ⟶ cokernel a) => Hom.f φ i) (cokernel.condition a)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply] using h
  -- `f` is killed by the projection, since it factors through `a`.
  have hfp : ∀ i : ℕ, f.f i ≫ (cokernel.π a).f i = 0 := fun i => by
    have h1 : f.f i = f'.f i ≫ a.f i := by
      have h := congrArg (fun (φ : C ⟶ C) => Hom.f φ i) hf
      simpa only [HomologicalComplex.comp_f] using h.symm
    rw [h1, Category.assoc, hap i, comp_zero]
  -- The homotopy condition of `K`, transported through the projection.
  have hKcomm : ∀ i : ℕ,
      (cokernel.π a).f i = (dNext i K.hom + prevD i K.hom) ≫ (cokernel.π a).f i := by
    intro i
    have h := congrArg (fun (φ : C.X i ⟶ C.X i) => φ ≫ (cokernel.π a).f i) (K.comm i)
    rw [HomologicalComplex.id_f, Category.id_comp, Preadditive.add_comp, hfp i, add_zero] at h
    exact h
  have hKi : ∀ i : ℕ,
      (C.d i (i - 1) ≫ K.hom (i - 1) i + K.hom i (i + 1) ≫ C.d (i + 1) i) ≫
        (cokernel.π a).f i = (cokernel.π a).f i := by
    intro i
    have h := hKcomm i
    rw [dNext_nat, prevD_chain_nat] at h
    exact h.symm
  -- The homotopy condition for the induced family on `Q`.
  have hcomm : ∀ i : ℕ, Hom.f (𝟙 (cokernel a)) i =
      dNext i homMap + prevD i homMap + Hom.f (0 : (cokernel a) ⟶ (cokernel a)) i := by
    intro i
    rw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero]
    rcases i with _ | j
    · rw [dNext_nat, prevD_chain_nat]
      show 𝟙 ((cokernel a).X 0) = (cokernel a).d 0 0 ≫ homMap 0 0 +
        homMap 0 1 ≫ (cokernel a).d 1 0
      have hd : (cokernel a).d 0 0 = 0 :=
        HomologicalComplex.shape (cokernel a) 0 0 (by decide)
      rw [hd, zero_comp, hhom1 0, zero_add]
      refine (cancel_epi ((cokernel.π a).f 0)).mp ?_
      rw [Category.comp_id]
      have hA : (cokernel.π a).f 0 ≫ (kk 0 ≫ (cokernel a).d 1 0) =
          K.hom 0 1 ≫ (C.d 1 0 ≫ (cokernel.π a).f 0) := by
        rw [← Category.assoc, hk 0, Category.assoc,
          HomologicalComplex.Hom.comm' (cokernel.π a) 1 0 rfl]
      rw [hA]
      have hK0 : K.hom 0 1 ≫ (C.d 1 0 ≫ (cokernel.π a).f 0) = (cokernel.π a).f 0 := by
        have h := hKi 0
        rw [show (0 : ℕ) - 1 = 0 from rfl] at h
        have hd0 : C.d 0 0 = 0 := HomologicalComplex.shape C 0 0 (by decide)
        rw [hd0, zero_comp, zero_add, Category.assoc] at h
        exact h
      exact hK0.symm
    · rw [dNext_nat, prevD_chain_nat]
      show 𝟙 ((cokernel a).X (j + 1)) = (cokernel a).d (j + 1) j ≫ homMap j (j + 1) +
        homMap (j + 1) ((j + 1) + 1) ≫ (cokernel a).d ((j + 1) + 1) (j + 1)
      rw [hhom1 j, hhom1 (j + 1)]
      refine (cancel_epi ((cokernel.π a).f (j + 1))).mp ?_
      rw [Category.comp_id, Preadditive.comp_add]
      show (cokernel.π a).f (j + 1) =
        (cokernel.π a).f (j + 1) ≫ ((cokernel a).d (j + 1) j ≫ kk j) +
        (cokernel.π a).f (j + 1) ≫ (kk (j + 1) ≫ (cokernel a).d ((j + 1) + 1) (j + 1))
      have hA : (cokernel.π a).f (j + 1) ≫ ((cokernel a).d (j + 1) j ≫ kk j) =
          C.d (j + 1) j ≫ (K.hom j (j + 1) ≫ (cokernel.π a).f (j + 1)) := by
        rw [← Category.assoc, HomologicalComplex.Hom.comm' (cokernel.π a) (j + 1) j rfl,
          Category.assoc, hk j]
      have hB : (cokernel.π a).f (j + 1) ≫
            (kk (j + 1) ≫ (cokernel a).d ((j + 1) + 1) (j + 1)) =
          K.hom (j + 1) ((j + 1) + 1) ≫
            (C.d ((j + 1) + 1) (j + 1) ≫ (cokernel.π a).f (j + 1)) := by
        rw [← Category.assoc, hk (j + 1), Category.assoc,
          HomologicalComplex.Hom.comm' (cokernel.π a) ((j + 1) + 1) (j + 1) rfl]
      rw [hA, hB]
      have hKj : C.d (j + 1) j ≫ (K.hom j (j + 1) ≫ (cokernel.π a).f (j + 1)) +
          K.hom (j + 1) ((j + 1) + 1) ≫
            (C.d ((j + 1) + 1) (j + 1) ≫ (cokernel.π a).f (j + 1)) =
          (cokernel.π a).f (j + 1) := by
        have h := hKi (j + 1)
        simp only [Preadditive.add_comp, Category.assoc] at h
        exact h
      exact hKj.symm
  have homot : Homotopy (𝟙 (cokernel a)) 0 :=
    { hom := homMap
      zero := hhom0
      comm := hcomm }
  intro m
  rw [IsZero.iff_id_eq_zero]
  have h := homot.homologyMap_eq m
  rw [homologyMap_id, homologyMap_zero] at h
  exact h

end Work.SSS
