import Mathlib
import Submission.Work.SSSR.Serre.simpHomChain
import Submission.Work.SSSR.Serre.prismHom_chain_identity
import Submission.Work.SSSR.Serre.prismHom_chain_identity_zero
import Submission.Work.SSSR.Serre.prismHom_map_incl_zero
import Submission.Work.SSSR.Serre.topChainMap_cokerPi_zero
import Submission.Work.SSSR.Cohomology.HomologyPairSequence
import Submission.Work.SSSR.Cohomology.cokernelComponent
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicTopology
namespace Work.SSSR.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The relative chain complex `C_*(X,A)`. -/
abbrev RelC (R : Type) [CommRing R] [Nontrivial R] (X : Type) [TopologicalSpace X] (A : Set X) : ChainComplex (ModuleCat R) ℕ :=
  Work.SSSR.Cohomology.relChains R (TopCat.of X) A

/-- The degreewise projection `C_n(X) ⟶ C_n(X,A)`. -/
abbrev ProjN (R : Type) [CommRing R] [Nontrivial R] (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (singChainC R X).X n ⟶ (RelC R X A).X n :=
  (cokernel.π (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A)).f n

/-- The canonical comparison `cokernel (f.f n) ⟶ (cokernel f).X n`, inverse of
`cokernelComponentIso`. -/
theorem projN_eq (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    cokernel.π ((Work.SSSR.Cohomology.inclChains R (TopCat.of X) A).f n) ≫
        (Work.SSSR.Cohomology.cokernelComponentIso (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A) n).inv
      = ProjN R X A n := by
  rw [← Work.SSSR.Cohomology.cokernelComponentIso_canon (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A) n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

instance epi_projN (n : ℕ) : Epi (ProjN R X A n) := by
  rw [← projN_eq X A n]
  infer_instance

/-- The composite `A`-chains `⟶` chains `⟶` relative chains is zero, in the form required by the
universal property of the cokernel. -/
theorem prismHom_map_incl_proj (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A).f n ≫ prismHom R H n ≫ ProjN R X A (n + 1) = 0 := by
  rw [← projN_eq X A (n + 1)]
  simp only [← Category.assoc]
  rw [prismHom_map_incl_zero H n hn, zero_comp]

/-- **The descended chain homotopy** on the relative complex: `prismHom R H n`, which sends
`A`-chains to `A`-chains, induces a map `C_n(X,A) ⟶ C_{n+1}(X,A)`. -/
noncomputable def relHom (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    (RelC R X A).X n ⟶ (RelC R X A).X (n + 1) :=
  (Work.SSSR.Cohomology.cokernelComponentIso (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A) n).hom ≫
    cokernel.desc ((Work.SSSR.Cohomology.inclChains R (TopCat.of X) A).f n)
      (prismHom R H n ≫ ProjN R X A (n + 1)) (prismHom_map_incl_proj H n hn)

/-- **The computation rule of the descended homotopy**: composed with the projection
`C_n(X) → C_n(X,A)` it is the prism homotopy followed by the projection. -/
theorem projN_relHom (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    ProjN R X A n ≫ relHom H n hn = prismHom R H n ≫ ProjN R X A (n + 1) := by
  rw [relHom]
  simp only [← Category.assoc]
  rw [Work.SSSR.Cohomology.cokernelComponentIso_canon (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A) n,
    cokernel.π_desc]

/-- The projection to the relative complex is a chain map. -/
theorem projN_d (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    ProjN R X A i ≫ (RelC R X A).d i j
      = (singChainC R X).d i j ≫ ProjN R X A j :=
  HomologicalComplex.Hom.comm (cokernel.π (Work.SSSR.Cohomology.inclChains R (TopCat.of X) A)) i j

/-- **The top map vanishes on the relative complex.** -/
theorem topChainMap_projN (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    topChainMap R H n ≫ ProjN R X A n = 0 := by
  rw [← projN_eq X A n]
  simp only [← Category.assoc]
  rw [topChainMap_cokerPi_zero H n hn, zero_comp]

/-- **The chain contraction identity on the relative complex**, in degree `m+1`. -/
theorem relHom_chain_identity (H : SimpHom X A N) (m : ℕ) (hm : m + 1 ≤ N) :
    relHom H (m + 1) hm ≫ (RelC R X A).d (m + 2) (m + 1)
      + (RelC R X A).d (m + 1) m ≫ relHom H m (by omega)
    = 𝟙 ((RelC R X A).X (m + 1)) := by
  have h1 : ProjN R X A (m + 1) ≫ relHom H (m + 1) hm
      = prismHom R H (m + 1) ≫ ProjN R X A (m + 2) := projN_relHom H (m + 1) hm
  have h2 : ProjN R X A m ≫ relHom H m (by omega)
      = prismHom R H m ≫ ProjN R X A (m + 1) := projN_relHom H m (by omega)
  have hcomm1 := projN_d (R := R) (X := X) (A := A) (m + 2) (m + 1) (by simp [ComplexShape.down])
  have hcomm2 := projN_d (R := R) (X := X) (A := A) (m + 1) m (by simp [ComplexShape.down])
  have htop : topChainMap R H (m + 1) ≫ ProjN R X A (m + 1) = 0 :=
    topChainMap_projN H (m + 1) hm
  apply (cancel_epi (ProjN R X A (m + 1))).mp
  calc ProjN R X A (m + 1) ≫ (relHom H (m + 1) hm ≫ (RelC R X A).d (m + 2) (m + 1)
          + (RelC R X A).d (m + 1) m ≫ relHom H m (by omega))
      = (ProjN R X A (m + 1) ≫ relHom H (m + 1) hm) ≫ (RelC R X A).d (m + 2) (m + 1)
          + (ProjN R X A (m + 1) ≫ (RelC R X A).d (m + 1) m) ≫ relHom H m (by omega) := by
        rw [Preadditive.comp_add]
        simp only [← Category.assoc]
    _ = (prismHom R H (m + 1) ≫ ProjN R X A (m + 2)) ≫ (RelC R X A).d (m + 2) (m + 1)
          + ((singChainC R X).d (m + 1) m ≫ ProjN R X A m) ≫ relHom H m (by omega) := by
        rw [h1, hcomm2]
    _ = prismHom R H (m + 1) ≫ ((singChainC R X).d (m + 2) (m + 1) ≫ ProjN R X A (m + 1))
          + (singChainC R X).d (m + 1) m ≫ (prismHom R H m ≫ ProjN R X A (m + 1)) := by
        rw [Category.assoc, hcomm1, Category.assoc, h2]
    _ = (prismHom R H (m + 1) ≫ (singChainC R X).d (m + 2) (m + 1)
          + (singChainC R X).d (m + 1) m ≫ prismHom R H m) ≫ ProjN R X A (m + 1) := by
        rw [Preadditive.add_comp]
        simp only [← Category.assoc]
    _ = (CategoryTheory.CategoryStruct.id ((singChainC R X).X (m + 1))
          - topChainMap R H (m + 1)) ≫ ProjN R X A (m + 1) := by
        rw [prismHom_chain_identity H m hm]
    _ = ProjN R X A (m + 1) ≫ 𝟙 ((RelC R X A).X (m + 1)) := by
        simp [htop]

/-- **The chain contraction identity on the relative complex**, in degree `0`. -/
theorem relHom_chain_identity_zero (H : SimpHom X A N) (hN : 0 ≤ N) :
    relHom H 0 hN ≫ (RelC R X A).d 1 0 = 𝟙 ((RelC R X A).X 0) := by
  have h1 : ProjN R X A 1 ≫ (RelC R X A).d 1 0
      = (singChainC R X).d 1 0 ≫ ProjN R X A 0 :=
    projN_d (R := R) (X := X) (A := A) 1 0 (by simp [ComplexShape.down])
  have h2 : ProjN R X A 0 ≫ relHom H 0 hN
      = prismHom R H 0 ≫ ProjN R X A 1 := projN_relHom H 0 hN
  have htop : topChainMap R H 0 ≫ ProjN R X A 0 = 0 := topChainMap_projN H 0 hN
  apply (cancel_epi (ProjN R X A 0)).mp
  calc ProjN R X A 0 ≫ (relHom H 0 hN ≫ (RelC R X A).d 1 0)
      = (ProjN R X A 0 ≫ relHom H 0 hN) ≫ (RelC R X A).d 1 0 := by
        simp only [← Category.assoc]
    _ = (prismHom R H 0 ≫ ProjN R X A 1) ≫ (RelC R X A).d 1 0 := by
        rw [h2]
    _ = prismHom R H 0 ≫ ((singChainC R X).d 1 0 ≫ ProjN R X A 0) := by
        rw [Category.assoc, h1]
    _ = (prismHom R H 0 ≫ (singChainC R X).d 1 0) ≫ ProjN R X A 0 := by
        simp only [← Category.assoc]
    _ = (CategoryTheory.CategoryStruct.id ((singChainC R X).X 0)
          - topChainMap R H 0) ≫ ProjN R X A 0 := by
        rw [prismHom_chain_identity_zero H]
    _ = ProjN R X A 0 ≫ 𝟙 ((RelC R X A).X 0) := by
        simp [htop]

/-- **Vanishing of the relative homology in positive degrees.** -/
theorem relChains_homology_succ_isZero (H : SimpHom X A N) (m : ℕ) (hm : m + 1 ≤ N) :
    IsZero ((RelC R X A).homology (m + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology (RelC R X A) (m + 1)]
  rw [HomologicalComplex.exactAt_iff' (RelC R X A) (m + 2) (m + 1) m
    (ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (m + 2) (m + 1) from rfl))
    (ComplexShape.next_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl))]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  refine ⟨(relHom H (m + 1) hm).hom x₂, ?_⟩
  have hx₂' : ((RelC R X A).d (m + 1) m).hom x₂ = 0 := hx₂
  have hc := congrArg (fun (g : (RelC R X A).X (m + 1) ⟶ (RelC R X A).X (m + 1)) =>
    (ConcreteCategory.hom g) x₂) (relHom_chain_identity H m hm)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply] at hc
  rw [hx₂', map_zero, add_zero] at hc
  exact hc

/-- **Vanishing of the relative homology in degree `0`**: a map `t` with `t ≫ ∂ = 𝟙` in degree
`0` displays every `0`-cycle as a boundary. -/
theorem isZero_relC_homology_zero (t : (RelC R X A).X 0 ⟶ (RelC R X A).X 1)
    (ht : t ≫ (RelC R X A).d 1 0 = 𝟙 ((RelC R X A).X 0)) : IsZero ((RelC R X A).homology 0) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology (RelC R X A) 0]
  rw [HomologicalComplex.exactAt_iff' (RelC R X A) 1 0 ((ComplexShape.down ℕ).next 0)
    (ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) rfl]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  refine ⟨(t.hom) x₂, ?_⟩
  have h := congrArg (fun (g : (RelC R X A).X 0 ⟶ (RelC R X A).X 0) =>
    (ConcreteCategory.hom g) x₂) ht
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  exact h

/-- **Serre's vanishing theorem for the relative cone construction** (`SimpHom` form): if a
family of compression homotopies of singular simplices of `X` into `A` is given in dimensions
`≤ N`, then the relative homology `H_n(X,A;ℤ)` vanishes for `n ≤ N`. -/
theorem simpHomVanishing {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}
    (H : Work.SSSR.Serre.SimpHom X A N) (n : ℕ) (hn : n ≤ N) :
    CategoryTheory.Limits.IsZero ((Work.SSSR.Cohomology.relChains R (TopCat.of X) A).homology n) := by
  cases n with
  | zero => exact isZero_relC_homology_zero (X := X) (A := A) (relHom H 0 hn) (relHom_chain_identity_zero H hn)
  | succ m => exact relChains_homology_succ_isZero (X := X) (A := A) H m hn

end

end Work.SSSR.Serre
