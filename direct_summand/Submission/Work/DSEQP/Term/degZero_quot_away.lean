import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.DZA.gf_degzero_away
import Submission.Work.DSEQP.Term.QuotAway.Defs
import Submission.Work.DSEQP.Term.QuotAway.ChartImage
import Submission.Work.DSCOH.cechMap_natural

universe a

namespace Work.DSEQP.Term

open MvPolynomial

variable {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}

noncomputable section

/-- `psi S` vanishes on `Img S`. -/
theorem psi_eq_zero_of_mem_Img (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    ∀ y ∈ Img (A := A) (N := N) i S, psi (A := A) (N := N) i S y = 0 := by
  intro y hy
  obtain ⟨x, rfl⟩ := mem_Img (A := A) (N := N) i hy
  exact psi_kappa (A := A) (N := N) i S x

/-- `chartJ` as an `A`-submodule is the image of `Img` under `toAway`. -/
theorem chartJA_eq_toAway_image (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    chartJA (A := A) (N := N) i S =
      Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
        (Img (A := A) (N := N) i S) :=
  Work.DSEQP.Term.QuotAway.ChartImage.chartJA_eq_toAway_image (A := A) (N := N) i S

/-- The chart identification `(R[1/x_S])₀ ≃ₗ Away 𝒜 (x_S)` as a linear equivalence. -/
noncomputable def toAwayEquiv (S : Finset (Fin (N + 1))) :
    ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S) ≃ₗ[A]
      HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) :=
  LinearEquiv.ofBijective (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
    (Work.DSEQP.DZA.toAway_bijective (A := A) (N := N) S)

@[simp] lemma toAwayEquiv_apply (S : Finset (Fin (N + 1)))
    (x : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    toAwayEquiv (A := A) (N := N) S x = Work.DSEQP.DZA.toAway (A := A) (N := N) S x := rfl

/-- The `A`-linear map `Away 𝒜 (x_S) → degZero (Mg i) S` obtained by inverting `toAway` and
applying the localisation of the quotient map. -/
noncomputable def PhiFun (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S) →ₗ[A]
      ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S) :=
  (psi (A := A) (N := N) i S).comp (toAwayEquiv (A := A) (N := N) S).symm.toLinearMap

lemma PhiFun_apply (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1)))
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    PhiFun (A := A) (N := N) i S z =
      psi (A := A) (N := N) i S ((toAwayEquiv (A := A) (N := N) S).symm z) := rfl

lemma chartJA_le_ker_PhiFun (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    chartJA (A := A) (N := N) i S ≤ LinearMap.ker (PhiFun (A := A) (N := N) i S) := by
  intro x hx
  rw [LinearMap.mem_ker]
  have hx' : x ∈ Submodule.map (Work.DSEQP.DZA.toAway (A := A) (N := N) S)
      (Img (A := A) (N := N) i S) := by
    rw [← chartJA_eq_toAway_image]
    exact hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx'
  rw [PhiFun_apply, ← hyx, ← toAwayEquiv_apply (A := A) (N := N) S y,
    LinearEquiv.symm_apply_apply]
  exact psi_eq_zero_of_mem_Img (A := A) (N := N) i S y hy

/-- The induced map `Away 𝒜 (x_S) ⧸ chartJ → degZero (Mg i) S`. -/
noncomputable def PhiLin (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    ((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
        chartJA (A := A) (N := N) i S) →ₗ[A]
      ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S) :=
  Submodule.liftQ (chartJA (A := A) (N := N) i S) (PhiFun (A := A) (N := N) i S)
    (chartJA_le_ker_PhiFun (A := A) (N := N) i S)

lemma PhiLin_mk (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1)))
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    PhiLin (A := A) (N := N) i S (Submodule.Quotient.mk z) =
      PhiFun (A := A) (N := N) i S z :=
  Submodule.liftQ_apply _ _ _

lemma PhiLin_surjective (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    Function.Surjective (PhiLin (A := A) (N := N) i S) := by
  intro d
  obtain ⟨y, hy⟩ := psi_surjective (A := A) (N := N) i S d
  refine ⟨Submodule.Quotient.mk (toAwayEquiv (A := A) (N := N) S y), ?_⟩
  rw [PhiLin_mk, PhiFun_apply, LinearEquiv.symm_apply_apply]
  exact hy

lemma PhiLin_injective (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) :
    Function.Injective (PhiLin (A := A) (N := N) i S) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  obtain ⟨x, rfl⟩ := (chartJA (A := A) (N := N) i S).mkQ_surjective z
  rw [Submodule.mkQ_apply] at hz
  rw [PhiLin_mk, PhiFun_apply] at hz
  have hy : (toAwayEquiv (A := A) (N := N) S).symm x ∈ Img (A := A) (N := N) i S := by
    rw [← ker_psi (A := A) (N := N) i S]
    exact hz
  have hx : x ∈ chartJA (A := A) (N := N) i S := by
    rw [chartJA_eq_toAway_image]
    refine Submodule.mem_map.mpr ⟨_, hy, ?_⟩
    rw [← toAwayEquiv_apply (A := A) (N := N) S]
    exact LinearEquiv.apply_symm_apply _ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hx

/-- **The chart comparison** `Away 𝒜 (x_S) ⧸ chartJ i S ≃ₗ[A] degZero (Mg i) S`. -/
noncomputable def Phi (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1)))
    (hS : S.Nonempty) :
    ((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
        Work.DSEQP.chartJ i S) ≃ₗ[A]
      ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
        (Work.DSEQP.Mg i) S) :=
  LinearEquiv.ofBijective (PhiLin (A := A) (N := N) i S)
    ⟨PhiLin_injective (A := A) (N := N) i S, PhiLin_surjective (A := A) (N := N) i S⟩

lemma Phi_mk (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1))) (hS : S.Nonempty)
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    Phi (A := A) (N := N) i S hS (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z) =
      PhiFun (A := A) (N := N) i S z := by
  show PhiLin (A := A) (N := N) i S (Submodule.Quotient.mk z) = PhiFun (A := A) (N := N) i S z
  exact PhiLin_mk (A := A) (N := N) i S z


/-- Naturality of `psi` with respect to the restriction maps. -/
theorem psi_resAt (i : X ⟶ DSMap.PSpace A N) {S T : Finset (Fin (N + 1))} (hST : S ⊆ T)
    (y : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    psi (A := A) (N := N) i T (Work.DSCOH.degPartRestrict (A := A) (n := N + 1)
        (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1))
        (Work.DSCOH.resAt (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A) hST)
        (fun x hx => Work.DSCOH.resAt_degZero (A := A) (n := N + 1)
          (M := MvPolynomial (Fin (N + 1)) A) (ℳ := Work.DSCOH.homSub A (N + 1)) hST x hx) y)
      = Work.DSCOH.degPartRestrict (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
          (Work.DSEQP.Mg i)
          (Work.DSCOH.resAt (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i) hST)
          (fun x hx => Work.DSCOH.resAt_degZero (A := A) (n := N + 1)
            (M := Work.DSEQP.Mmod i) (ℳ := Work.DSEQP.Mg i) hST x hx)
          (psi (A := A) (N := N) i S y) :=
  Work.DSCOH.degZeroMapOf_resAt_apply (A := A) (n := N + 1)
    (Work.DSCOH.homSub A (N + 1)) (Work.DSEQP.Mg i)
    (Submodule.mkQ (Work.DSEQP.Jvan i)) (fun d => le_of_eq rfl) hST y

/-- `PhiFun` on a value of the form `toAway y`. -/
lemma PhiFun_apply_toAway (i : X ⟶ DSMap.PSpace A N) (S : Finset (Fin (N + 1)))
    (y : ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := MvPolynomial (Fin (N + 1)) A)
      (Work.DSCOH.homSub A (N + 1)) S)) :
    PhiFun (A := A) (N := N) i S (Work.DSEQP.DZA.toAway (A := A) (N := N) S y) =
      psi (A := A) (N := N) i S y := by
  rw [PhiFun_apply, ← toAwayEquiv_apply (A := A) (N := N) S,
    LinearEquiv.symm_apply_apply]

theorem PhiFun_natural (i : X ⟶ DSMap.PSpace A N) {S T : Finset (Fin (N + 1))} (hST : S ⊆ T)
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    PhiFun (A := A) (N := N) i T (Work.DSEQP.awayRes (A := A) (N := N) hST z) =
      ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i) hST
          (PhiFun (A := A) (N := N) i S z).1,
        Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
          (ℳ := Work.DSEQP.Mg i) hST _ (PhiFun (A := A) (N := N) i S z).2⟩ := by
  obtain ⟨y, rfl⟩ : ∃ y, toAwayEquiv (A := A) (N := N) S y = z :=
    ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  rw [toAwayEquiv_apply]
  rw [← Work.DSEQP.DZA.toAway_natural (A := A) (N := N) hST y]
  rw [PhiFun_apply_toAway, PhiFun_apply_toAway]
  rw [psi_resAt (A := A) (N := N) i hST y]
  exact Subtype.ext rfl

theorem Phi_natural (i : X ⟶ DSMap.PSpace A N) (S T : Finset (Fin (N + 1))) (hST : S ⊆ T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) :
    Phi (A := A) (N := N) i T hT (Ideal.Quotient.mk (Work.DSEQP.chartJ i T)
        (Work.DSEQP.awayRes (A := A) (N := N) hST z))
      = ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i) hST
            (Phi (A := A) (N := N) i S hS
              (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z)).1,
          Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
            (ℳ := Work.DSEQP.Mg i) hST _
            (Phi (A := A) (N := N) i S hS
              (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z)).2⟩ := by
  rw [Phi_mk, Phi_mk]
  exact PhiFun_natural (A := A) (N := N) i hST z


/-- **The degree-zero part of the chart localisation of `M = R ⧸ J`.**  For the vanishing ideal
`J = Jvan i` of a closed subscheme `i : X ↪ ℙᴺ_A` and the chart `S` (`x_S = ∏_{j∈S} X_j`), the
degree-zero part `(M[1/x_S])₀ = degZero (Mg i) S` of the localisation of `M = R ⧸ J` is the
quotient `Away 𝒜 (x_S) ⧸ chartJ i S` of the chart ring by the chart ideal of `J`; the isomorphism
is induced by the localisation `R → M` of the quotient map (`Work.DSEQP.locMap`, whose kernel on
the degree-zero parts is `degZero (J ∩ graded pieces) S`).  The naturality says that it intertwines
the localisation maps `awayRes` of the chart rings with the restriction maps `resAt` of the
degree-zero parts. -/
theorem degZero_quot_away (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i) :
    ∃ e : ∀ (S : Finset (Fin (N + 1))) (hS : S.Nonempty),
        ((HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)) ⧸
            Work.DSEQP.chartJ i S) ≃ₗ[A]
          ↥(Work.DSCOH.degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
            (Work.DSEQP.Mg i) S),
      ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (z : HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)),
        e T hT (Ideal.Quotient.mk (Work.DSEQP.chartJ i T)
            (Work.DSEQP.awayRes (A := A) (N := N) hST z))
          = ⟨Work.DSCOH.resAt (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i) hST
                (e S hS (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z)).1,
              Work.DSCOH.resAt_degZero (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
                (ℳ := Work.DSEQP.Mg i) hST _
                (e S hS (Ideal.Quotient.mk (Work.DSEQP.chartJ i S) z)).2⟩ := by
  refine ⟨fun S hS => Phi (A := A) (N := N) i S hS, ?_⟩
  intro S T hST hS hT z
  exact Phi_natural (A := A) (N := N) i S T hST hS hT z

end

end Work.DSEQP.Term
