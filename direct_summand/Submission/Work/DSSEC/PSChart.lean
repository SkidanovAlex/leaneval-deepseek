import Mathlib
import Submission.Work.DSSEC.Basic

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

/-! ## Vocabulary for the generation statement

`ℙᴺ_A = DSMap.PSpace A N = Proj (PGr A N)`.  For `S : Finset (Idx N)` we put
`tPS S = ∏_{m ∈ S} x_m ∈ A[x₀,…,x_N]` and `DPS S = D₊(tPS S) ⊆ ℙᴺ_A`, so that
`i ⁻¹ᵁ DPS S = ⨅_{m ∈ S} chartCover i m` (the open `U_S` of the statement).
The ring `Away (PGr A N) (tPS S)` is `Γ(ℙᴺ_A, DPS S)` (Mathlib's `Proj.basicOpenIsoAway`),
and `chartFracPS S l hl k = x_k/x_l` is the element of it that the comparison sends to
`xiSecS i S l hl k`.
-/

section Vocab

variable {A : Type u} [CommRing A] {N : ℕ}

/-- The monomial `∏_{m ∈ S} x_m ∈ A[x₀,…,x_N]`. -/
noncomputable abbrev tPS (S : Finset (Idx N)) : MvPolynomial (Fin (N + 1)) A :=
  ∏ m ∈ S, MvPolynomial.X m.down

/-- The basic open `D₊(∏_{m ∈ S} x_m) ⊆ ℙᴺ_A`; its preimage along `i` is `U_S`. -/
noncomputable abbrev DPS (S : Finset (Idx N)) : (DSMap.PSpace A N).Opens :=
  Proj.basicOpen (DSMap.PGr A N) (tPS S)

lemma tPS_homog (S : Finset (Idx N)) : (tPS (A := A) S).IsHomogeneous S.card := by
  unfold tPS
  convert MvPolynomial.IsHomogeneous.prod S
    (fun m => (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A)) (fun _ => 1)
    (fun m _ => MvPolynomial.isHomogeneous_X A m.down) using 1
  simp

lemma tPS_mem (S : Finset (Idx N)) : tPS (A := A) S ∈ DSMap.PGr A N S.card := by
  rw [MvPolynomial.mem_homogeneousSubmodule]; exact tPS_homog S

lemma ghomog (S : Finset (Idx N)) (l : Idx N) :
    (∏ m ∈ S.erase l, (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A)).IsHomogeneous
      (S.erase l).card := by
  convert MvPolynomial.IsHomogeneous.prod (S.erase l)
    (fun m => (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A)) (fun _ => 1)
    (fun m _ => MvPolynomial.isHomogeneous_X A m.down) using 1
  simp

lemma gmem (S : Finset (Idx N)) (l : Idx N) :
    (∏ m ∈ S.erase l, (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A)) ∈
      DSMap.PGr A N (S.erase l).card := by
  rw [MvPolynomial.mem_homogeneousSubmodule]; exact ghomog S l

lemma gmul_mem (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S) (k : Idx N) :
    MvPolynomial.X k.down * (∏ m ∈ S.erase l, (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A))
      ∈ DSMap.PGr A N S.card := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := (MvPolynomial.isHomogeneous_X A k.down).mul (ghomog S l)
  rwa [show 1 + (S.erase l).card = S.card from by
    have : 0 < S.card := Finset.card_pos.mpr ⟨l, hl⟩
    rw [Finset.card_erase_of_mem hl]; omega] at h

/-- `D₊` turns products into infima. -/
lemma basicOpen_prod (f : Idx N → MvPolynomial (Fin (N + 1)) A) (S : Finset (Idx N)) :
    Proj.basicOpen (DSMap.PGr A N) (∏ m ∈ S, f m) =
      ⨅ m ∈ S, Proj.basicOpen (DSMap.PGr A N) (f m) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.iInf_insert, Proj.basicOpen_mul, ih]

lemma preimage_iInf' {X : Scheme.{u}} (f : X ⟶ DSMap.PSpace A N) {ι : Type u} [Finite ι]
    (U : ι → (DSMap.PSpace A N).Opens) :
    f ⁻¹ᵁ (⨅ m, U m) = ⨅ m, f ⁻¹ᵁ U m := by
  apply TopologicalSpace.Opens.ext
  simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage, Set.preimage_iInter]

/-- `DPS S` is affine whenever `S` is nonempty (`tPS S` is homogeneous of positive degree). -/
lemma DPS_affine (S : Finset (Idx N)) (hS : S.Nonempty) :
    IsAffineOpen (DPS (A := A) (N := N) S) :=
  Proj.isAffineOpen_basicOpen (DSMap.PGr A N) (tPS (A := A) S) (tPS_mem S)
    (Finset.card_pos.mpr hS)

/-- The preimage of `DPS S` along `i` is the open `U_S = ⋂_{m ∈ S} chartCover i m`. -/
lemma preimage_DPS {X : Scheme.{u}} (i : X ⟶ DSMap.PSpace A N) (S : Finset (Idx N)) :
    i ⁻¹ᵁ DPS (A := A) (N := N) S = ⨅ m ∈ S, DSMap.Mix2.chartCover i m := by
  classical
  induction S using Finset.induction with
  | empty => simp [DPS, tPS]
  | insert a s ha ih =>
    have h1 : DPS (A := A) (N := N) (insert a s) =
        Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X a.down) ⊓ DPS (A := A) (N := N) s := by
      simp only [DPS, tPS, Finset.prod_insert ha, Proj.basicOpen_mul]
    rw [h1, Scheme.Hom.preimage_inf, ih, Finset.iInf_insert]
    rfl

end Vocab

/-! ## The chart coordinates `x_k / x_l` of the ambient projective space -/

section ChartFrac

variable {A : Type u} [CommRing A] {N : ℕ}

/-- The ring map `A →+* 𝒜 0` sending `a` to the constant polynomial. -/
noncomputable def AtoA0 : A →+* ↥(DSMap.PGr A N 0) where
  toFun a := ⟨MvPolynomial.C a, by
    rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_C (Fin (N + 1)) a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- The structural ring map `A →+* Away (PGr A N) (tPS S)`. -/
noncomputable def AtoAwayS (S : Finset (Idx N)) :
    A →+* HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) S) :=
  (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N) (Submonoid.powers (tPS (A := A) S))).comp
    AtoA0

/-- The chart coordinate `x_k / x_l ∈ Away (PGr A N) (tPS S)`, for `l ∈ S`. -/
noncomputable def chartFracPS (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S) (k : Idx N) :
    HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) S) :=
  HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) 1
    (MvPolynomial.X k.down * (∏ m ∈ S.erase l, MvPolynomial.X m.down))
    (by rw [one_smul]; exact gmul_mem S l hl k)

/-- The factorisation `tPS S = x_l · ∏_{m ∈ S \ {l}} x_m` used for `awayMap`. -/
lemma tPS_eq_mul (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S) :
    tPS (A := A) S = MvPolynomial.X l.down * (∏ m ∈ S.erase l, MvPolynomial.X m.down) :=
  (Finset.mul_prod_erase S (fun m => (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A)) hl).symm

/-- `chartFracPS S l hl k` is the image of `x_k/x_l ∈ Away (PGr A N) (x_l)` under `awayMap`. -/
lemma chartFracPS_eq (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S) (k : Idx N) :
    chartFracPS (A := A) S l hl k =
      HomogeneousLocalization.awayMap (DSMap.PGr A N) (gmem S l)
        (hx := show tPS (A := A) S =
            MvPolynomial.X l.down * (∏ m ∈ S.erase l, MvPolynomial.X m.down) from
          (Finset.mul_prod_erase S
            (fun m => (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A)) hl).symm)
        (HomogeneousLocalization.Away.mk (DSMap.PGr A N) (DSMap.Mix2.X_mem_PGr l.down) 1
          (MvPolynomial.X k.down) (by rw [one_smul]; exact DSMap.Mix2.X_mem_PGr k.down)) := by
  rw [HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  unfold chartFracPS
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]

/-- The `Algebra A ↥(PGr A N 0)` structure map is the constants map `AtoA0`. -/
lemma algebraMap_PGr_zero : algebraMap A ↥(DSMap.PGr A N 0) = AtoA0 (A := A) (N := N) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  rfl

end ChartFrac

end Work.DSSEC
