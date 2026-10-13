import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSSEC.Main
import Submission.Work.DSEQP.gf_gamma_eq_h0_cech
import Submission.Work.DSEQP.cech_homology_zero_iso_ker
import Submission.Work.DSCHART.Basic

/-!
# `Work.DSEQP.gf_bridge` — Γ(X, 𝒪_X) is the degree-0 chart Čech cohomology of a f.g. graded module

The geometric bridge of area `DSEQP`'s route to `gamma_finite`: for `X` a closed subscheme of
`ℙᴺ_A = DSMap.PSpace A N` over `A` Noetherian, there is a finitely generated graded module `M`
over `A[x₀,…,x_N]` whose *chart Čech* cohomology in degree `0` (`Work.DSCOH.chartCech`) computes
`Γ(X, 𝒪_X)`.

The construction is the standard one: with `I = i.ker` the ideal sheaf of `X` in `ℙᴺ_A` and

`J := ⨁_d { f ∈ A[x₀,…,x_N]_d : f / x_j^d ∈ I(D₊(x_j)) for every j }`

(the *saturation* of the vanishing ideal of `X`), the module `M := A[x₀,…,x_N] ⧸ J` has
`sections over the chart D₊(x_S)` equal to `Γ(X ∩ D₊(x_S), 𝒪_X)`, compatibly with the
restriction maps; hence `H⁰(chartCech M) ≅ H⁰(Č(U; 𝒪_X)) = Γ(X, 𝒪_X)`.

The mathematical content beyond the definitions:

* the identification of the chart ring with the degree-zero part of the localization
  (`val`-range vs. `Work.DSCOH.degZero`), and its compatibility with the restriction maps;
* Mathlib's quasi-coherence of the ideal sheaf (`Scheme.IdealSheafData.map_ideal_basicOpen`),
  which gives `I(D₊(x_S)) = I(D₊(x_j))·R_S` for `j ∈ S`;
* the *saturation* computation `(J·R_S)₀ = I(D₊(x_S))` (the singleton case uses the
  localization-injectivity argument with the unit `x_j/x_i`).
-/

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Work.DSEQP

universe a u v

/-- The standard grading of the polynomial ring as a **global** instance.  Mathlib deliberately
leaves `MvPolynomial.gradedAlgebra` unregistered (one may want a different weight function), but
the statements of this file (and of the lemmas delegated on top of it) mention the chart rings of
`Proj (MvPolynomial.homogeneousSubmodule (Fin n) A)`, so the instance has to be available to
importers. -/
noncomputable instance instGradedAlgebraMvPolynomial (σ : Type u) [Fintype σ] (R : Type v)
    [CommRing R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) :=
  MvPolynomial.gradedAlgebra

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. Vocabulary: the charts of `ℙᴺ_A` and their preimages in `X` -/

section ChartVocab

variable {A : Type a} [CommRing A] {N : ℕ}

/-- The monomial `x_S = ∏_{i ∈ S} X_i ∈ A[x₀,…,x_N]`. -/
noncomputable def xS (S : Finset (Fin (N + 1))) : MvPolynomial (Fin (N + 1)) A :=
  ∏ i ∈ S, MvPolynomial.X i

/-- The structural ring map `A →+* Away 𝒜 (x_S)` (through `A → 𝒜 0 → Away`). -/
noncomputable def AtoAway (S : Finset (Fin (N + 1))) :
    A →+* HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S) :=
  (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
    (Submonoid.powers (xS (A := A) S))).comp (algebraMap A ↥(DSMap.PGr A N 0))

/-- The canonical `A`-algebra structure on the chart ring `Away 𝒜 (x_S)`, as a global instance. -/
noncomputable instance instAlgebraAway (S : Finset (Fin (N + 1))) :
    Algebra A (HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S)) :=
  (AtoAway (A := A) (N := N) S).toAlgebra

/-- The chart `D₊(x_S) ⊆ ℙᴺ_A = Proj A[x₀,…,x_N]`. -/
noncomputable abbrev Dcmp (S : Finset (Fin (N + 1))) : (DSMap.PSpace A N).Opens :=
  Proj.basicOpen (DSMap.PGr A N) (xS (A := A) S)

/-- The open subscheme `U_S = i⁻¹(D₊(x_S)) ⊆ X`. -/
noncomputable abbrev Ucmp {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (S : Finset (Fin (N + 1))) : X.Opens :=
  i ⁻¹ᵁ Dcmp (A := A) (N := N) S

@[simp] lemma xS_empty : xS (A := A) (∅ : Finset (Fin (N + 1))) = 1 := by
  simp [xS]

lemma xS_homog (S : Finset (Fin (N + 1))) : (xS (A := A) S).IsHomogeneous S.card := by
  unfold xS
  convert MvPolynomial.IsHomogeneous.prod S
    (fun i => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) A)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X A i) using 1
  simp

lemma xS_mem_homSub (S : Finset (Fin (N + 1))) :
    xS (A := A) S ∈ Work.DSCOH.homSub A (N + 1) S.card := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact xS_homog S

lemma Dcmp_affine (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    IsAffineOpen (Dcmp (A := A) (N := N) S) :=
  Proj.isAffineOpen_basicOpen (DSMap.PGr A N) (xS (A := A) S) (xS_mem_homSub S)
    (Finset.card_pos.mpr hS)

lemma xS_dvd {S T : Finset (Fin (N + 1))} (h : S ⊆ T) : xS (A := A) S ∣ xS (A := A) T := by
  unfold xS
  exact Finset.prod_dvd_prod_of_subset _ _ _ h

lemma Dcmp_anti {S T : Finset (Fin (N + 1))} (h : S ⊆ T) :
    Dcmp (A := A) (N := N) T ≤ Dcmp (A := A) (N := N) S :=
  Proj.basicOpen_mono (DSMap.PGr A N) _ _ (xS_dvd h)

/-- The chart `D₊(x_S)` is the intersection of the "coordinate" charts `D₊(x_j)`, `j ∈ S`. -/
lemma Dcmp_eq_iInf (S : Finset (Fin (N + 1))) :
    Dcmp (A := A) (N := N) S =
      ⨅ j ∈ S, Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j) := by
  classical
  induction S using Finset.induction with
  | empty =>
    change Proj.basicOpen (DSMap.PGr A N) (xS (A := A) ∅) =
      ⨅ j ∈ (∅ : Finset (Fin (N + 1))), Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j)
    simp [xS]
  | insert a s ha ih =>
    have hxS : xS (A := A) (insert a s) = MvPolynomial.X a * xS (A := A) s := by
      rw [xS, xS, Finset.prod_insert ha]
    have ih' : Proj.basicOpen (DSMap.PGr A N) (xS (A := A) s) =
        ⨅ j ∈ s, Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j) := ih
    change Proj.basicOpen (DSMap.PGr A N) (xS (A := A) (insert a s)) =
      ⨅ j ∈ insert a s, Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j)
    rw [hxS, Proj.basicOpen_mul, Finset.iInf_insert, ih']

lemma Dcmp_le_single {S : Finset (Fin (N + 1))} {j : Fin (N + 1)} (hj : j ∈ S) :
    Dcmp (A := A) (N := N) S ≤ Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j) := by
  rw [Dcmp_eq_iInf]
  exact iInf_le_of_le j (iInf_le_of_le hj le_rfl)

/-- Pullback of an intersection of open sets. -/
lemma preimage_iInf_finset {X Y : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ Y) {ι : Type u}
    (S : Finset ι) (U : ι → Y.Opens) :
    i ⁻¹ᵁ (⨅ j ∈ S, U j) = ⨅ j ∈ S, i ⁻¹ᵁ U j := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]

lemma Ucmp_anti {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    {S T : Finset (Fin (N + 1))} (h : S ⊆ T) : Ucmp i T ≤ Ucmp i S :=
  Scheme.Hom.preimage_mono i (Dcmp_anti h)

lemma Ucmp_affine {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    [IsClosedImmersion i] (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    IsAffineOpen (Ucmp i S) :=
  (Dcmp_affine S hS).preimage i

/-- `U_S` is the intersection of the individual charts `U_{j}` (`j ∈ S`). -/
lemma Ucmp_eq_iInf {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (S : Finset (Fin (N + 1))) :
    Ucmp i S = ⨅ j ∈ S, i ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j)) := by
  change i ⁻¹ᵁ Dcmp (A := A) (N := N) S =
    ⨅ j ∈ S, i ⁻¹ᵁ Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j)
  rw [Dcmp_eq_iInf, preimage_iInf_finset]

/-- `x_T = x_S · x_{T \setminus S}` for `S ⊆ T`. -/
lemma xS_mul_diff {S T : Finset (Fin (N + 1))} (h : S ⊆ T) :
    xS (A := A) T = xS (A := A) S * xS (A := A) (T \ S) := by
  unfold xS
  rw [← Finset.prod_sdiff h, mul_comm]

/-- The localization map `Away 𝒜 (x_S) →+* Away 𝒜 (x_T)` for `S ⊆ T`. -/
noncomputable def awayRes {S T : Finset (Fin (N + 1))} (h : S ⊆ T) :
    HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S) →+*
      HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) T) :=
  HomogeneousLocalization.awayMap (DSMap.PGr A N) (xS_mem_homSub (T \ S)) (xS_mul_diff h)

end ChartVocab

/-! ## 2. The chart comparison maps `Away 𝒜 (x_S) → Γ(X, U_S)` -/

section ChartMaps

variable {A : Type a} [CommRing A] {N : ℕ}

/-- The canonical isomorphism between the chart ring `Away 𝒜 (x_S) = Γ(D₊(x_S), 𝒪_ℙ)` and the
sections of `𝒪_ℙ` over `D₊(x_S)` (Mathlib's `Proj.basicOpenIsoAway`). -/
noncomputable def awayIso (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S) ≃+*
      Γ(DSMap.PSpace A N, Dcmp (A := A) (N := N) S) :=
  RingEquiv.ofBijective
    (Proj.basicOpenIsoAway (DSMap.PGr A N) (xS (A := A) S) (xS_mem_homSub S)
      (Finset.card_pos.mpr hS)).hom.hom
    (ConcreteCategory.bijective_of_isIso _)

/-- The comparison map from the chart ring of `ℙᴺ_A` at `D₊(x_S)` to the sections of `𝒪_X`
over `U_S = i⁻¹D₊(x_S)`. -/
noncomputable def chartMap {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S) →+* Γ(X, Ucmp i S) :=
  (i.app (Dcmp (A := A) (N := N) S)).hom.comp (awayIso S hS).toRingHom

lemma chartMap_surjective {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (hi : IsClosedImmersion i) (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    Function.Surjective (chartMap i S hS) := by
  have hcii := hi
  exact (Scheme.Hom.app_surjective i (Dcmp (A := A) (N := N) S) (Dcmp_affine S hS)).comp
    (awayIso S hS).surjective

/-- The kernel of the chart comparison, as an ideal of the chart ring `Away 𝒜 (x_S)`: it is the
preimage of the ideal sheaf of `X` in `ℙᴺ_A`. -/
theorem chartMap_ker {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (hi : IsClosedImmersion i) (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    RingHom.ker (chartMap i S hS) =
      (i.ker.ideal ⟨Dcmp (A := A) (N := N) S, Dcmp_affine S hS⟩).comap (awayIso S hS).toRingHom := by
  have hcii := hi
  rw [chartMap, ← RingHom.comap_ker ((i.app (Dcmp (A := A) (N := N) S)).hom) (awayIso S hS).toRingHom,
    Scheme.Hom.ker_apply i ⟨Dcmp (A := A) (N := N) S, Dcmp_affine S hS⟩]

end ChartMaps

/-! ## 3. The vanishing ideal `J` of `X ⊆ ℙᴺ_A` and the chart saturation -/

section VanishingIdeal

variable {A : Type a} [CommRing A] {N : ℕ}

lemma xS_singleton (j : Fin (N + 1)) :
    xS (A := A) ({j} : Finset (Fin (N + 1))) = MvPolynomial.X j := by
  simp [xS]

lemma xS_singleton_mem (j : Fin (N + 1)) :
    xS (A := A) ({j} : Finset (Fin (N + 1))) ∈ DSMap.PGr A N 1 := by
  rw [xS_singleton]
  exact DSMap.Mix2.X_mem_PGr j

/-- **The saturation of the vanishing ideal of `X ⊆ ℙᴺ_A`**: the ideal generated by the forms `f`
whose chart sections `f / x_j^{deg f}` vanish on `X ∩ D₊(x_j)` for every `j`.  (The module `M` of
the bridge is `A[x₀,…,x_N] ⧸ J`; see the module docstring.) -/
noncomputable abbrev Jvan {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N) :
    Ideal (MvPolynomial (Fin (N + 1)) A) :=
  Ideal.span {f : MvPolynomial (Fin (N + 1)) A |
    ∃ (d : ℕ) (hf : f ∈ Work.DSCOH.homSub A (N + 1) d),
      ∀ j : Fin (N + 1), chartMap i {j} (Finset.singleton_nonempty j)
        (HomogeneousLocalization.Away.mk (DSMap.PGr A N) (xS_singleton_mem j) d f (by
          simpa [xS_singleton] using hf)) = 0}

/-- `Jvan i` is a homogeneous ideal (it is generated by forms). -/
theorem Jvan_isHomogeneous {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N) :
    (Jvan i).IsHomogeneous (DSMap.PGr A N) := by
  refine Ideal.homogeneous_span (DSMap.PGr A N) _ ?_
  rintro f ⟨d, hf, -⟩
  exact ⟨d, hf⟩

/-- The "chart ideal" of `J` at the chart `D₊(x_S)`: the ideal of `Away 𝒜 (x_S)` generated by the
images `f / x_S^k` of the forms `f ∈ J` lying in degree `k·|S|`. -/
noncomputable def chartJ {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)
    (S : Finset (Fin (N + 1))) : Ideal (HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S)) :=
  Ideal.span {z : HomogeneousLocalization.Away (DSMap.PGr A N) (xS (A := A) S) |
    ∃ (k : ℕ) (f : MvPolynomial (Fin (N + 1)) A)
      (hf : f ∈ Work.DSCOH.homSub A (N + 1) (k * S.card)), f ∈ Jvan i ∧
      z = HomogeneousLocalization.Away.mk (DSMap.PGr A N) (xS_mem_homSub S) k f (by
        simpa [smul_eq_mul] using hf)}

end VanishingIdeal

/-! ## 4. The module `M = A[x₀,…,x_N] ⧸ J` and its grading -/

section Module

variable {A : Type a} [CommRing A] {N : ℕ}
variable {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)

/-- The module `M = A[x₀,…,x_N] ⧸ J` of the bridge (see `Jvan`). -/
abbrev Mmod : Type a := MvPolynomial (Fin (N + 1)) A ⧸ Jvan i

/-- The `d`-th graded piece of `M`: the image of the degree-`d` forms. -/
noncomputable def Mg (d : ℕ) : Submodule A (Mmod i) :=
  Submodule.map ((Submodule.mkQ (Jvan i)).restrictScalars A)
    (Work.DSCOH.homSub A (N + 1) d)

/-- The graded piece `Mg d` consists of the classes of the forms of degree `d`. -/
lemma mem_Mg {d : ℕ} {x : Mmod i} :
    x ∈ Mg i d ↔ ∃ f ∈ Work.DSCOH.homSub A (N + 1) d, Submodule.mkQ (Jvan i) f = x :=
  Submodule.mem_map

/-- Multiplication by a form of degree `d` maps the `e`-th piece into the `(d+e)`-th. -/
lemma smul_mem_Mg {d e : ℕ} {a : MvPolynomial (Fin (N + 1)) A}
    (ha : a ∈ Work.DSCOH.homSub A (N + 1) d) {m : Mmod i} (hm : m ∈ Mg i e) :
    a • m ∈ Mg i (d + e) := by
  obtain ⟨f, hf, rfl⟩ := mem_Mg i |>.mp hm
  refine mem_Mg i |>.mpr ⟨a * f, ?_, ?_⟩
  · exact SetLike.mul_mem_graded ha hf
  · simpa only [Submodule.mkQ_apply, smul_eq_mul] using (Submodule.mkQ (Jvan i)).map_smul a f

instance : SetLike.GradedSMul (DSMap.PGr A N) (Mg i) :=
  ⟨fun _ _ _ _ ha hm => smul_mem_Mg i ha hm⟩

/-- The `e`-th homogeneous component of a form lies in `J` as soon as the form does. -/
lemma homogeneousComponent_mem_Jvan {f : MvPolynomial (Fin (N + 1)) A} (hf : f ∈ Jvan i)
    (e : ℕ) : MvPolynomial.homogeneousComponent e f ∈ Jvan i :=
  MvPolynomial.homogeneousComponent_mem_of_mem (Jvan_isHomogeneous i) hf e

/-- The `j`-th homogeneous component of a finite sum of forms of pairwise distinct degrees `d` is
the summand of degree `j` (and zero if there is none). -/
lemma homogeneousComponent_finsetSum (s : Finset ℕ) {y : ℕ → MvPolynomial (Fin (N + 1)) A}
    (hy : ∀ d, y d ∈ Work.DSCOH.homSub A (N + 1) d) (j : ℕ) :
    MvPolynomial.homogeneousComponent j (∑ d ∈ s, y d) = if j ∈ s then y j else 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, map_add, ih, MvPolynomial.homogeneousComponent_of_mem (hy a)]
    by_cases hja : j = a
    · subst hja
      simp [ha]
    · have haj : a ≠ j := fun h => hja h.symm
      simp [Finset.mem_insert, hja, haj]

/-- **The grading of `M = R ⧸ J` is internal.**  The pieces `Mg d` are independent (a relation
`Σ x_d = 0` with `x_d ∈ Mg d` lifts to `Σ f_d ∈ J`, and homogeneity of `J` forces each `f_d ∈ J`)
and they span (the quotient map is surjective and `R` is the direct sum of its homogeneous
pieces). -/
theorem isInternal_Mg : DirectSum.IsInternal (Mg i) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0 j hj
    -- lift each `v d ∈ Mg d` (`d ∈ s`) to a form of degree `d`
    have hy : ∀ d : s, ∃ g ∈ Work.DSCOH.homSub A (N + 1) (d : ℕ),
        (Submodule.mkQ (Jvan i)) g = v d := fun d => (mem_Mg i).mp (hv d d.2)
    choose y hyh hyeq using hy
    -- extend the lifts by zero outside `s`
    let Y : ℕ → MvPolynomial (Fin (N + 1)) A := fun d => if h : d ∈ s then y ⟨d, h⟩ else 0
    have hY : ∀ d, Y d ∈ Work.DSCOH.homSub A (N + 1) d := by
      intro d
      by_cases h : d ∈ s
      · simpa only [Y, dif_pos h] using hyh ⟨d, h⟩
      · simpa only [Y, dif_neg h] using Submodule.zero_mem (Work.DSCOH.homSub A (N + 1) d)
    -- the sum of the lifts lies in `J`
    have hJ : (∑ d ∈ s, Y d) ∈ Jvan i := by
      have h1 : (Submodule.mkQ (Jvan i)) (∑ d ∈ s, Y d) = 0 := by
        rw [map_sum]
        have h2 : (∑ d ∈ s, (Submodule.mkQ (Jvan i)) (Y d)) = (∑ d ∈ s, v d) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          simp only [Y, dif_pos hd]
          exact hyeq ⟨d, hd⟩
        rw [h2, hv0]
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    -- the `j`-th component of the sum is `y ⟨j, hj⟩`
    have hcomp : MvPolynomial.homogeneousComponent j (∑ d ∈ s, Y d) = y ⟨j, hj⟩ := by
      rw [homogeneousComponent_finsetSum s hY j, if_pos hj]
      exact dif_pos hj
    have hyj : y ⟨j, hj⟩ ∈ Jvan i := by
      have h2 := homogeneousComponent_mem_Jvan i hJ j
      rwa [hcomp] at h2
    show v j = 0
    rw [← hyeq ⟨j, hj⟩, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hyj
  · rw [show (⨆ d, Mg i d) = Submodule.map ((Submodule.mkQ (Jvan i)).restrictScalars A)
        (⨆ d, Work.DSCOH.homSub A (N + 1) d) from by
      simp only [Mg]
      rw [Submodule.map_iSup]]
    rw [show (⨆ d, Work.DSCOH.homSub A (N + 1) d) = ⊤ from by
      refine top_le_iff.mp fun φ _ => ?_
      rw [← MvPolynomial.sum_homogeneousComponent φ]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.mem_iSup_of_mem i (MvPolynomial.homogeneousComponent_mem i φ)]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective (Jvan i))

/-- `M = R ⧸ J` is finitely generated over `R`. -/
instance finite_Mmod : Module.Finite (MvPolynomial (Fin (N + 1)) A) (Mmod i) :=
  Module.Finite.of_surjective (Submodule.mkQ (Jvan i)) (Submodule.mkQ_surjective (Jvan i))

/-- The decomposition of `M` into its graded pieces. -/
noncomputable def MgDecomposition : DirectSum.Decomposition (Mg i) :=
  (isInternal_Mg i).chooseDecomposition

end Module

/-! ## 4b. The localization of the quotient map `R → M = R ⧸ J` -/

section ModuleSide

variable {A : Type a} [CommRing A] {N : ℕ}
variable {X : AlgebraicGeometry.Scheme.{a}} (i : X ⟶ DSMap.PSpace A N)

/-- The localization of the quotient map `R → M = R ⧸ J` at the chart `S`. -/
noncomputable def locMap (S : Finset (Fin (N + 1))) :
    Work.DSCOH.locAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) S →ₗ[A]
      Work.DSCOH.locAt (A := A) (M := Mmod i) S := by
  haveI : IsLocalizedModule (Work.DSCOH.subS (A := A) (n := N + 1) S)
      (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S)
        (MvPolynomial (Fin (N + 1)) A)) := inferInstance
  haveI : IsLocalizedModule (Work.DSCOH.subS (A := A) (n := N + 1) S)
      (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S) (Mmod i)) :=
    inferInstance
  exact (IsLocalizedModule.map (Work.DSCOH.subS (A := A) (n := N + 1) S)
    (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S)
      (MvPolynomial (Fin (N + 1)) A))
    (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S) (Mmod i))
    (Submodule.mkQ (Jvan i))).restrictScalars A

/-- The explicit fraction description of `divPow` for the polynomial ring `R`. -/
lemma divPow_toLoc_eq_mk_R (S : Finset (Fin (N + 1))) (k : ℕ)
    (m : MvPolynomial (Fin (N + 1)) A) :
    Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m) =
      LocalizedModule.mk (R := MvPolynomial (Fin (N + 1)) A)
        (S := Work.DSCOH.subS (A := A) (n := N + 1) S)
        (M := MvPolynomial (Fin (N + 1)) A) m
        ⟨(xS (A := A) S) ^ k,
          Submonoid.pow_mem (Work.DSCOH.subS (A := A) (n := N + 1) S)
            (Work.DSCOH.monomial_mem S) k⟩ := by
  unfold Work.DSCOH.divPow Work.DSCOH.toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]
  exact congrArg _ (Subtype.ext rfl)

/-- The explicit fraction description of `divPow` for the module `M`. -/
lemma divPow_toLoc_eq_mk_M (S : Finset (Fin (N + 1))) (k : ℕ) (m : Mmod i) :
    Work.DSCOH.divPow (A := A) (M := Mmod i) S k
        (Work.DSCOH.toLoc (A := A) (M := Mmod i) S m) =
      LocalizedModule.mk (R := MvPolynomial (Fin (N + 1)) A)
        (S := Work.DSCOH.subS (A := A) (n := N + 1) S) (M := Mmod i) m
        ⟨(xS (A := A) S) ^ k,
          Submonoid.pow_mem (Work.DSCOH.subS (A := A) (n := N + 1) S)
            (Work.DSCOH.monomial_mem S) k⟩ := by
  unfold Work.DSCOH.divPow Work.DSCOH.toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]
  exact congrArg _ (Subtype.ext rfl)

/-- The abstract fraction `IsLocalizedModule.mk'` for the canonical localization map is the
constructor `LocalizedModule.mk`. -/
lemma mk'_mkLinearMap {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (S : Submonoid R) (m : M) (s : S) :
    IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m s = LocalizedModule.mk m s := by
  rw [IsLocalizedModule.mk'_eq_iff, LocalizedModule.mkLinearMap_apply, Submonoid.smul_def,
    LocalizedModule.smul'_mk, ← LocalizedModule.mk_cancel s m]
  simp only [Submonoid.smul_def]

lemma locMap_mk (S : Finset (Fin (N + 1))) (m : MvPolynomial (Fin (N + 1)) A)
    (s : Work.DSCOH.subS (A := A) (n := N + 1) S) :
    locMap i S (LocalizedModule.mk (R := MvPolynomial (Fin (N + 1)) A)
        (S := Work.DSCOH.subS (A := A) (n := N + 1) S) m s) =
      LocalizedModule.mk (R := MvPolynomial (Fin (N + 1)) A)
        (S := Work.DSCOH.subS (A := A) (n := N + 1) S) (Submodule.mkQ (Jvan i) m) s := by
  haveI h1 : IsLocalizedModule (Work.DSCOH.subS (A := A) (n := N + 1) S)
      (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S)
        (MvPolynomial (Fin (N + 1)) A)) := inferInstance
  haveI h2 : IsLocalizedModule (Work.DSCOH.subS (A := A) (n := N + 1) S)
      (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S) (Mmod i)) :=
    inferInstance
  rw [← mk'_mkLinearMap (S := Work.DSCOH.subS (A := A) (n := N + 1) S) m s,
    ← mk'_mkLinearMap (S := Work.DSCOH.subS (A := A) (n := N + 1) S)
      (M := Mmod i) (Submodule.mkQ (Jvan i) m) s]
  exact IsLocalizedModule.map_mk' (Work.DSCOH.subS (A := A) (n := N + 1) S)
    (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S)
      (MvPolynomial (Fin (N + 1)) A))
    (LocalizedModule.mkLinearMap (Work.DSCOH.subS (A := A) (n := N + 1) S) (Mmod i))
    (Submodule.mkQ (Jvan i)) m s

lemma locMap_divPow (S : Finset (Fin (N + 1))) (k : ℕ)
    (m : MvPolynomial (Fin (N + 1)) A) :
    locMap i S (Work.DSCOH.divPow (A := A) (M := MvPolynomial (Fin (N + 1)) A) S k
        (Work.DSCOH.toLoc (A := A) (M := MvPolynomial (Fin (N + 1)) A) S m)) =
      Work.DSCOH.divPow (A := A) (M := Mmod i) S k
        (Work.DSCOH.toLoc (A := A) (M := Mmod i) S (Submodule.mkQ (Jvan i) m)) := by
  rw [divPow_toLoc_eq_mk_R, divPow_toLoc_eq_mk_M]
  exact locMap_mk i S m _

end ModuleSide

/-! ## 5. The geometric chart Čech complex and the chart cover of `X` -/

section GeomCech

variable {A : Type a} [CommRing A] {N : ℕ}
variable {X : AlgebraicGeometry.Scheme.{a}}

/-- The `A`-module of sections of `𝒪_X` over the chart `U_S = i⁻¹D₊(x_S)`, with the `A`-structure
induced by `f`. -/
noncomputable abbrev secs (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (S : Finset (Fin (N + 1))) : Type a :=
  ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (Ucmp i S)))

/-- The degree-`0` term of the *geometric* chart Čech complex: the product over the singleton
charts `U_j = i⁻¹D₊(x_j)` of the sections of `𝒪_X`. -/
noncomputable abbrev GC0 (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) : Type a :=
  ∀ S : {S : Finset (Fin (N + 1)) // S.card = 1}, secs i f S.1

/-- The degree-`1` term of the geometric chart Čech complex. -/
noncomputable abbrev GC1 (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) : Type a :=
  ∀ T : {T : Finset (Fin (N + 1)) // T.card = 2}, secs i f T.1

/-- The `T`-component of the degree-`0` differential of the geometric chart Čech complex: the
alternating sum, over the elements `i ∈ T`, of the restriction of the `(T \ {i})`-component to the
chart `T`, with the sign `(-1)^{#{j ∈ T : j < i}}` — the same convention as DSCOH's
`cechDiffComp`. -/
noncomputable def geomD0Comp (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (T : {T : Finset (Fin (N + 1)) // T.card = 2}) :
    GC0 i f →ₗ[A] secs i f T.1 :=
  ∑ i' ∈ T.1.attach,
    (-1 : ℤ) ^ ((T.1.filter fun j => j < i'.1)).card •
      (((DSMap.cechPresheaf A X f).map
          (homOfLE (Ucmp_anti (A := A) (N := N) i (Finset.erase_subset i'.1 T.1))).op).hom.comp
        (LinearMap.proj (R := A)
          (φ := fun S : {S : Finset (Fin (N + 1)) // S.card = 1} => secs (A := A) (N := N) i f S.1)
          ⟨T.1.erase i'.1, by rw [Finset.card_erase_of_mem i'.2]; omega⟩))

/-- The degree-`0` differential of the geometric chart Čech complex. -/
noncomputable def geomD0 (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) : GC0 i f →ₗ[A] GC1 i f :=
  LinearMap.pi (R := A) fun T => geomD0Comp i f T

@[simp] lemma geomD0_apply (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (y : GC0 i f)
    (T : {T : Finset (Fin (N + 1)) // T.card = 2}) :
    geomD0 i f y T = geomD0Comp i f T y := rfl

/-- **The singletons of the index set cover `X`.**  The charts `U_j = i⁻¹D₊(x_j)` of a closed
subscheme of `ℙᴺ_A` cover `X`. -/
theorem chartCover_iSup_eq_top (i : X ⟶ DSMap.PSpace A N) :
    (⨆ j : Fin (N + 1), Ucmp i ({j} : Finset (Fin (N + 1)))) = ⊤ := by
  have h := Scheme.Hom.iSup_preimage_eq_top i (Work.DSCHART.iSup_basicOpen_X_eq_top A N)
  rw [← h]
  refine iSup_congr fun j => ?_
  rw [Ucmp_eq_iInf, Finset.iInf_singleton]

end GeomCech


