import Mathlib
import Submission.Work.Serre.E0Defs
import Submission.Work.Cohomology.Crux33.ezBridge
import Submission.Work.StemsB.SphLoopTools
import Submission.Work.RatHurewicz.Bridge.chainBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-!
# The chain-algebra half of `SerreE0Range`

This file proves `Work.Serre.e0ChainAlgebra`: cone (filler) data on the singular simplicial set
of `X` in degrees `≤ N` gives the vanishing of the rational homology of `X` in degrees
`0 < j ≤ N`.

The cone data `Hd : SSetConeData K N` is turned into a chain contraction of the simplicial chain
complex `K.chainComplex (ModuleCat.of ℤ ℤ)`:

* `coneS K Hd.H n : K.X n ⟶ K.X (n+1)` is the "cone" chain homotopy, defined on the generator
  attached to an `n`-simplex `σ` by `σ ↦ (-1)^(n+1) • H n σ` (`coneS_gen`);
* the face conditions of the cone data give, on generators, the chain-contraction identity
  `d (s (m+1) σ) + s m (d σ) = σ` (`cone_contraction_gen`), hence at the level of morphisms
  `s (m+1) ≫ d + d ≫ s m = 𝟙` in degree `m+1` (`cone_contraction`);
* a chain contraction kills homology in the range (`isZero_homology_of_contraction`);
* `Work.StemsB.isZero_homology_rat_of_isZero_homology_int` transfers the vanishing from `ℤ` to `ℚ`.

The proof of the chain-contraction identity is carried out in the coordinates of
`Work.Cohomology.Crux33.coords` (the identification of the `ℤ`-chains with the free module on the
simplices), where all the signs are added up explicitly.
-/

/-- The **cone chain homotopy** attached to a family `H` of fillers: on the generator of an
`n`-simplex `σ` it is `(-1)^(n+1) • (H n σ)`.  It is defined as the descent of
`LinearMap.toSpanSingleton` along the coproduct decomposition of the `n`-chains. -/
noncomputable def coneS (K : SSet) (H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌) (n : ℕ) :
    (K.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶ (K.chainComplex (ModuleCat.of ℤ ℤ)).X (n+1) :=
  Cofan.IsColimit.desc (K.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
      ((K.chainComplex (ModuleCat.of ℤ ℤ)).X (n+1))
      (((-1:ℤ)^(n+1)) • ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) (H n σ)).hom (1:ℤ)))))

/-- The value of `coneS` on the generator attached to a simplex. -/
lemma coneS_gen (K : SSet) (H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌) (n : ℕ) (σ : K _⦋n⦌) :
    (coneS K H n).hom ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
      = (-1:ℤ)^(n+1) • ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) (H n σ)).hom 1) := by
  have hfac := Cofan.IsColimit.fac (K.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
      ((K.chainComplex (ModuleCat.of ℤ ℤ)).X (n+1))
      (((-1:ℤ)^(n+1)) • ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) (H n τ)).hom (1:ℤ))))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (K.chainComplex (ModuleCat.of ℤ ℤ)).X (n+1)) =>
      (ModuleCat.Hom.hom g) (1:ℤ)) hfac
  rw [show K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
      = (K.chainComplexXCofan (ModuleCat.of ℤ ℤ) n).inj σ from rfl]
  dsimp only [coneS] at h2 ⊢
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The differential of the simplicial chain complex on the generator attached to a simplex. -/
lemma chainComplex_d_gen (K : SSet) (n : ℕ) (a : K _⦋n+1⦌) :
    ((K.chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n).hom
        ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom 1)
      = ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
          ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) (K.δ i a)).hom 1) := by
  have hh := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (K.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
      (ModuleCat.Hom.hom g) (1:ℤ)) (SSet.ιChainComplex_d K (ModuleCat.of ℤ ℤ) a)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply] at hh
  exact hh

/-- `coneS` in the coordinates of `Work.Cohomology.Crux33.coords`. -/
lemma coords_coneS_gen (K : SSet) (H : ∀ n : ℕ, K _⦋n⦌ → K _⦋n+1⦌) (n : ℕ) (σ : K _⦋n⦌) :
    Work.Cohomology.Crux33.coords K (n+1)
        ((coneS K H n).hom ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))
      = (-1:ℤ)^(n+1) • Finsupp.single (H n σ) (1:ℤ) := by
  rw [coneS_gen, LinearMap.map_smul_of_tower, Work.Cohomology.Crux33.coords_ι]

/-- The differential in the coordinates of `Work.Cohomology.Crux33.coords`. -/
lemma coords_chainComplex_d_gen (K : SSet) (n : ℕ) (a : K _⦋n+1⦌) :
    Work.Cohomology.Crux33.coords K n
        (((K.chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n).hom
          ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom 1))
      = ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) • Finsupp.single (K.δ i a) (1:ℤ) := by
  rw [chainComplex_d_gen, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.map_smul_of_tower, Work.Cohomology.Crux33.coords_ι]

variable {K : SSet} (N : ℕ) (Hd : SSetConeData K N) (m : ℕ) (σ : K _⦋m+1⦌)

/-- The first half of the chain-contraction identity, in coordinates. -/
lemma coords_d_coneS :
    Work.Cohomology.Crux33.coords K (m+1)
        (((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+2) (m+1)).hom
          ((coneS K Hd.H (m+1)).hom ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)))
      = (-1:ℤ)^(m+2) • (∑ i : Fin (m+3),
          (-1:ℤ)^(i:ℕ) • Finsupp.single (K.δ i (Hd.H (m+1) σ)) (1:ℤ)) := by
  rw [coneS_gen]
  have h := LinearMap.map_smul_of_tower
    ((Work.Cohomology.Crux33.coords K (m+1)).comp
      ((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+2) (m+1)).hom)
    ((-1:ℤ)^(m+2)) ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) (Hd.H (m+1) σ)).hom 1)
  simp only [LinearMap.comp_apply] at h
  rw [h, coords_chainComplex_d_gen]

/-- The second half of the chain-contraction identity, in coordinates. -/
lemma coords_coneS_d :
    Work.Cohomology.Crux33.coords K (m+1)
        ((coneS K Hd.H m).hom (((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+1) m).hom
          ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)))
      = ∑ j : Fin (m+2),
          (-1:ℤ)^(j:ℕ) • ((-1:ℤ)^(m+1) • Finsupp.single (Hd.H m (K.δ j σ)) (1:ℤ)) := by
  rw [chainComplex_d_gen]
  simp only [map_sum]
  refine Finset.sum_congr (M := K _⦋m+1⦌ →₀ ℤ) rfl (fun j _ => ?_)
  have h := LinearMap.map_smul_of_tower
    ((Work.Cohomology.Crux33.coords K (m+1)).comp (coneS K Hd.H m).hom)
    ((-1:ℤ)^(j:ℕ)) ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) (K.δ j σ)).hom 1)
  simp only [LinearMap.comp_apply] at h
  rw [h, coords_coneS_gen]

/-- The alternating sum of the faces of a filler, split at the last face and rewritten by the
two face conditions of the cone data. -/
lemma coneData_face_sum (hm : m + 1 ≤ N) :
    (∑ i : Fin (m+3), (-1:ℤ)^(i:ℕ) • Finsupp.single (K.δ i (Hd.H (m+1) σ)) (1:ℤ))
      = (∑ j : Fin (m+2), (-1:ℤ)^(j:ℕ) • Finsupp.single (Hd.H m (K.δ j σ)) (1:ℤ))
        + ((-1:ℤ)^(m+2)) • Finsupp.single σ (1:ℤ) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Hd.face_cast m hm σ j, Fin.val_castSucc]
  · rw [Hd.face_last (m+1) hm σ, Fin.val_last]

/-- The coefficients in front of the fillers cancel in pairs. -/
lemma coneData_coeff_zero (j : Fin (m+2)) :
    (-1:ℤ)^(m+2) * (-1:ℤ)^(j:ℕ) + (-1:ℤ)^(j:ℕ) * (-1:ℤ)^(m+1) = 0 := by
  have h1 : (-1:ℤ)^(m+2) = -((-1:ℤ)^(m+1)) := by rw [pow_succ]; ring
  calc (-1:ℤ)^(m+2) * (-1:ℤ)^(j:ℕ) + (-1:ℤ)^(j:ℕ) * (-1:ℤ)^(m+1)
      = (-1:ℤ)^(j:ℕ) * ((-1:ℤ)^(m+2) + (-1:ℤ)^(m+1)) := by ring
    _ = (-1:ℤ)^(j:ℕ) * (-((-1:ℤ)^(m+1)) + (-1:ℤ)^(m+1)) := by rw [h1]
    _ = 0 := by ring

/-- `(-1)^(m+2)·(-1)^(m+2) = 1`. -/
lemma coneData_neg_one_sq : (-1:ℤ)^(m+2) * (-1:ℤ)^(m+2) = 1 := by
  rw [← pow_add, show m+2+(m+2) = 2*(m+2) by ring, pow_mul]
  norm_num

/-- **The chain-contraction identity on the generator of a simplex.**  This is the heart of the
computation: the `i ≤ m+1` faces of the filler `Hd.H (m+1) σ` cancel against the corresponding
terms of the cone homotopy applied to the boundary, and the last face contributes `σ`. -/
lemma cone_contraction_gen (hm : m + 1 ≤ N) :
    ((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+2) (m+1)).hom
        ((coneS K Hd.H (m+1)).hom ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))
      + (coneS K Hd.H m).hom (((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+1) m).hom
          ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))
      = (K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1 := by
  apply Work.Cohomology.Crux33.eq_of_coords_eq
  rw [map_add, coords_d_coneS (N := N) Hd m σ, coords_coneS_d, Work.Cohomology.Crux33.coords_ι]
  rw [coneData_face_sum (N := N) Hd m σ hm, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  rw [show
      ((∑ x : Fin (m+2), ((-1:ℤ)^(m+2) * (-1:ℤ)^(x:ℕ)) •
            Finsupp.single (Hd.H m (K.δ x σ)) (1:ℤ))
          + ((-1:ℤ)^(m+2) * (-1:ℤ)^(m+2)) • Finsupp.single σ (1:ℤ))
        + (∑ x : Fin (m+2), ((-1:ℤ)^(x:ℕ) * (-1:ℤ)^(m+1)) •
            Finsupp.single (Hd.H m (K.δ x σ)) (1:ℤ))
      = ((∑ x : Fin (m+2), ((-1:ℤ)^(m+2) * (-1:ℤ)^(x:ℕ)) •
            Finsupp.single (Hd.H m (K.δ x σ)) (1:ℤ))
          + (∑ x : Fin (m+2), ((-1:ℤ)^(x:ℕ) * (-1:ℤ)^(m+1)) •
              Finsupp.single (Hd.H m (K.δ x σ)) (1:ℤ)))
        + ((-1:ℤ)^(m+2) * (-1:ℤ)^(m+2)) • Finsupp.single σ (1:ℤ) from by abel]
  rw [← Finset.sum_add_distrib]
  have hsum : (∑ x : Fin (m+2),
      (((-1:ℤ)^(m+2) * (-1:ℤ)^(x:ℕ)) • Finsupp.single (Hd.H m (K.δ x σ)) (1:ℤ)
        + ((-1:ℤ)^(x:ℕ) * (-1:ℤ)^(m+1)) • Finsupp.single (Hd.H m (K.δ x σ)) (1:ℤ))) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x _
    rw [← add_smul, coneData_coeff_zero (m := m) x, zero_smul]
  rw [hsum, zero_add, coneData_neg_one_sq (m := m), one_smul]

/-- **The chain-contraction identity in degree `m+1`**, at the level of morphisms. -/
lemma cone_contraction (hm : m + 1 ≤ N) :
    coneS K Hd.H (m+1) ≫ (K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+2) (m+1)
      + (K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+1) m ≫ coneS K Hd.H m
      = 𝟙 ((K.chainComplex (ModuleCat.of ℤ ℤ)).X (m+1)) := by
  apply K.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have hL : (ModuleCat.Hom.hom (K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
        (coneS K Hd.H (m+1) ≫ (K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+2) (m+1)
          + (K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+1) m ≫ coneS K Hd.H m))) (1:ℤ)
      = ((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+2) (m+1)).hom
          ((coneS K Hd.H (m+1)).hom ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))
        + (coneS K Hd.H m).hom (((K.chainComplex (ModuleCat.of ℤ ℤ)).d (m+1) m).hom
            ((K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) := by
    rw [Preadditive.comp_add]
    simp only [← Category.assoc, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.comp_apply,
      LinearMap.add_apply]
  exact hL.trans (cone_contraction_gen (N := N) Hd m σ hm)

end

section Homology

open CategoryTheory

/-- **A chain contraction kills homology in its range.**  If `s` is a chain homotopy between the
identity and `0` in degrees `≤ N` (in the form `∂s + s∂ = 𝟙`), then `H_j = 0` for `0 < j ≤ N`.
Stated with the "shifted" index `j = m+1` so that the differentials are literally `A.d (m+2) (m+1)`
and `A.d (m+1) m`. -/
theorem isZero_homology_of_contraction (A : ChainComplex (ModuleCat ℤ) ℕ)
    (s : ∀ n : ℕ, A.X n ⟶ A.X (n+1)) (N : ℕ)
    (h : ∀ m : ℕ, m + 1 ≤ N →
      s (m+1) ≫ A.d (m+2) (m+1) + A.d (m+1) m ≫ s m = 𝟙 (A.X (m+1))) :
    ∀ m : ℕ, m + 1 ≤ N → IsZero (A.homology (m+1)) := by
  intro m hm
  have hprev : (ComplexShape.down ℕ).prev (m+1) = m+2 := ComplexShape.prev_eq' _ rfl
  have hnext : (ComplexShape.down ℕ).next (m+1) = m := ComplexShape.next_eq' _ rfl
  rw [← HomologicalComplex.exactAt_iff_isZero_homology A (m+1),
    HomologicalComplex.exactAt_iff' A (m+2) (m+1) m hprev hnext,
    ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  refine ⟨(s (m+1)).hom x₂, ?_⟩
  have hx₂' : (A.d (m+1) m).hom x₂ = 0 := hx₂
  have hc := congrArg (fun (g : A.X (m+1) ⟶ A.X (m+1)) =>
    (ConcreteCategory.hom g) x₂) (h m hm)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply] at hc
  rw [hx₂', map_zero, add_zero] at hc
  exact hc

end Homology

/-- **The chain-algebra half of `SerreE0Range`.**

Let `K := Work.Serre.singSSet X` be the singular simplicial set of `X` and let `H` be cone data in
degrees `≤ N` (`Work.Serre.SSetConeData K N`): for every `n`-simplex `σ` a filler `H n σ` whose
`i`-th face is `H (n-1) (δᵢ σ)` for `i ≤ n` and whose last face is `σ`.  Then `H_j(X;ℚ) = 0` for
`0 < j ≤ N`.

Suggested route (worked out by the requester):

* `Work.Cohomology.Crux33.coords`/`mk` identify the `ℤ`-chains of a simplicial set with the free
  module on its simplices; `singularChains ℤ X` is *definitionally* `K.chainComplex (ModuleCat.of ℤ ℤ)`
  (`rfl`), and `SSet.ιChainComplex_d` gives the differential on a generator:
  `d (mk (single σ 1)) = Σᵢ (-1)^i • mk (single (δᵢ σ) 1)`.
* Define `s n : K.X n →ₗ[ℤ] K.X (n+1)` on generators by `s n σ := (-1)^(n+1) • H n σ`.  Then the
  face conditions give `d ∘ s n + s (n-1) ∘ d = id` for `1 ≤ n ≤ N` (check it on generators:
  the `i ≤ n` faces of `H n σ` contribute `H (n-1) (δᵢ σ)`, which cancels against the corresponding
  term of `s (n-1) (d σ)`, and the last face contributes `(-1)^(n+1) σ`).
* Hence every cycle `z` in degree `j` (`1 ≤ j ≤ N`) is the boundary of `s j z`, so
  `IsZero ((K.chainComplex (ModuleCat.of ℤ ℤ)).homology j)` — e.g. via
  `K.homology j = (K.sc j).homology` (definitional), `ShortComplex.exact_iff_isZero_homology` and
  the concrete exactness criterion `ShortComplex.ab_exact_iff_ker_le_range` (every cycle is in the
  range of the differential), or via `Work.RatHurewicz.Bridge.chain_homologypi_eq_zero`.
* Transfer to `ℚ` with `Work.StemsB.isZero_homology_rat_of_isZero_homology_int`.

Note `RatVanishingBelow X (N+1)` unfolds to `∀ j, 0 < j → j < N+1 → IsZero (ratH (TopCat.of X) j)`,
i.e. degrees `0 < j ≤ N`.
-/
theorem e0ChainAlgebra (X : Type) [TopologicalSpace X] (N : ℕ)
    (h : Nonempty (Work.Serre.SSetConeData (Work.Serre.singSSet X) N)) :
    Work.Serre.RatVanishingBelow X (N + 1) := by
  obtain ⟨Hd⟩ := h
  intro j hj hjN
  rw [show j = (j-1)+1 from (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm]
  refine Work.StemsB.isZero_homology_rat_of_isZero_homology_int (TopCat.of X) ((j-1)+1) ?_
  exact isZero_homology_of_contraction ((singSSet X).chainComplex (ModuleCat.of ℤ ℤ))
    (coneS (singSSet X) Hd.H) N
    (fun m hm => cone_contraction (N := N) Hd m hm) (j-1) (by omega)

end Work.Serre
