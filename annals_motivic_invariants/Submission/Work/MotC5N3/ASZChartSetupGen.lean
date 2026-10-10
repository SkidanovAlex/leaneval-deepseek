import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASMatrix
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotC5N3.ASZChartSetupGen` — the chart of the AS twisted Klein curve over a general `K`

The `RatFunc 𝕜 ↦ K` fork of `Submission/Work/MotAS/ASZChartSetup.lean`: for an arbitrary
`𝕜`-algebra field `K` of characteristic `5`, the chart evaluation
`asChartPhiA : K[X₀,…,X₄] → twistFieldAS D g`, `X i ↦ y_i / y_0` kills the chart ideal
(`asChartIdeal_le_ker_A`), and the assembly `asChartPresentation_of_ker_A` reduces the chart
presentation to the kernel inclusion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- The residual characteristic of `𝕜` is `5` as soon as `K` is a `𝕜`-algebra field of
characteristic `5` (the algebra map is injective). -/
theorem charP_of_algebra_charP {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] : CharP 𝕜 5 :=
  RingHom.charP (algebraMap 𝕜 K) (algebraMap 𝕜 K).injective 5

/-! ## §2 The twisted coordinates satisfy the twisted Pfaffians -/

/-- The five AS Pfaffians evaluated at the Lagrange coordinates `asTwY D g` vanish: this is the
transport `asTransportP` of the Klein relation `D.Good.klein_eq` along `x = asM w · y`. -/
theorem kleinPAS_asTwY (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K) :
    Work.MotAS.kleinPAS (algebraMap K (OmA K D) (aK K D))
        (algebraMap K (OmA K D) (bK K D))
        (algebraMap K (OmA K D) g) (asTwY D g) = 0 := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have ha : algebraMap K (OmA K D) (aK K D)
      = algebraMap 𝕜 (OmA K D) D.a :=
    IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.a
  have hb : algebraMap K (OmA K D) (bK K D)
      = algebraMap 𝕜 (OmA K D) D.b :=
    IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.b
  rw [ha, hb]
  have h5 : (5 : OmA K D) = 0 := five_eq_zero_OmA 𝕜 D
  set w : OmA K D :=
    algebraMap (KbA K) (OmA K D) (asRoot g) with hwdef
  have hw : w ^ 5 = w + algebraMap K (OmA K D) g := by
    rw [hwdef]
    have h := congrArg (algebraMap (KbA K) (OmA K D)) (asRoot_spec (K := K) g)
    simp only [map_sub, map_pow] at h
    rw [← IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) g] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have hM : Work.MotAS.asM w = asMO D g := by
    ext i j
    rw [hwdef]
    simp only [Work.MotAS.asM, asMO, Matrix.of_apply, Matrix.map_apply, map_add, map_pow,
      map_natCast]
  have hmv : (fun i => ∑ j, Work.MotAS.asM w i j * asTwY D g j) = asKap D g := by
    funext i
    have h1 : (∑ j, Work.MotAS.asM w i j * asTwY D g j) = ((asMO D g).mulVec (asTwY D g)) i := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by
        rw [congrFun (congrFun hM i) j]
    rw [h1, asMO_mulVec_asTwY]
  have hzero : Work.MotK.kleinP (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (asKap D g) = 0 := by
    funext k
    exact hD.klein_eq (KbA K) k
  have htr := Work.MotAS.asTransportP (algebraMap 𝕜 (OmA K D) D.a)
    (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g) w h5 hw (asTwY D g)
  rw [hmv] at htr
  rw [hzero] at htr
  refine Work.MotAS.asN_mulVec_injective h5 w ?_
  rw [← htr]
  simp

/-! ## §3 The chart evaluation `X i ↦ y_i/y_0` -/

/-- The chart evaluation of the AS twisted Klein curve, with values in `OmA K D`. -/
noncomputable def asChartPhiOmA (D : Work.MotV.KleinData 𝕜) (g : K) :
    MvPolynomial (Fin 5) K →ₐ[K] OmA K D :=
  MvPolynomial.aeval fun i => asTwY D g i / asTwY D g 0

theorem asChartPhiOmA_X (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 5) :
    asChartPhiOmA D g (MvPolynomial.X i) = asTwY D g i / asTwY D g 0 := by
  simp only [asChartPhiOmA, MvPolynomial.aeval_X]

theorem asChartPhiOmA_mem (D : Work.MotV.KleinData 𝕜) (g : K)
    (x : MvPolynomial (Fin 5) K) : asChartPhiOmA D g x ∈ twistFieldAS D g := by
  have hle : Algebra.adjoin K (Set.range (fun i => asTwY D g i / asTwY D g 0)) ≤
      (twistFieldAS D g).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
  have hx : x ∈ Algebra.adjoin K
      (Set.range (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) K)) := by
    rw [MvPolynomial.adjoin_range_X]; exact Algebra.mem_top
  have himg : asChartPhiOmA D g x ∈
      (Algebra.adjoin K (Set.range (MvPolynomial.X :
        Fin 5 → MvPolynomial (Fin 5) K))).map (asChartPhiOmA D g) := ⟨x, hx, rfl⟩
  rw [AlgHom.map_adjoin] at himg
  have hrange : (asChartPhiOmA D g) ''
      Set.range (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) K) =
      Set.range (fun i => asTwY D g i / asTwY D g 0) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (asChartPhiOmA_X D g i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, asChartPhiOmA_X D g i⟩
  rw [hrange] at himg
  exact hle himg

/-- The chart evaluation, with values in the AS twist field. -/
noncomputable def asChartPhiA (D : Work.MotV.KleinData 𝕜) (g : K) :
    MvPolynomial (Fin 5) K →ₐ[K] ↥(twistFieldAS D g) :=
  (asChartPhiOmA D g).codRestrict (twistFieldAS D g).toSubalgebra (asChartPhiOmA_mem D g)

theorem asChartPhiA_coe (D : Work.MotV.KleinData 𝕜) (g : K)
    (x : MvPolynomial (Fin 5) K) :
    ((asChartPhiA D g x : ↥(twistFieldAS D g)) : OmA K D) = asChartPhiOmA D g x :=
  AlgHom.coe_codRestrict _ _ _ _

theorem asChartPhiA_X (D : Work.MotV.KleinData 𝕜) (g : K) (i : Fin 5) :
    ((asChartPhiA D g (MvPolynomial.X i) : ↥(twistFieldAS D g)) : OmA K D)
      = asTwY D g i / asTwY D g 0 := by
  rw [asChartPhiA_coe, asChartPhiOmA_X]

/-! ## §4 The chart evaluation kills the chart ideal -/

/-- The evaluation of an AS Pfaffian at the projective coordinates `y_i/y_0`. -/
theorem asChartPhiOmA_kleinPAS (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) :
    asChartPhiOmA D g (Work.MotAS.kleinPAS (MvPolynomial.C (aK K D))
      (MvPolynomial.C (bK K D)) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i) k)
      = Work.MotAS.kleinPAS (algebraMap K (OmA K D) (aK K D))
          (algebraMap K (OmA K D) (bK K D))
          (algebraMap K (OmA K D) g)
          (fun i => asTwY D g i / asTwY D g 0) k := by
  fin_cases k <;>
    simp only [asChartPhiOmA, Work.MotAS.kleinPAS, Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1,
      Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4,
      Work.MotK.fin5_zero, Work.MotK.fin5_one, Work.MotK.fin5_two, Work.MotK.fin5_three,
      Work.MotK.fin5_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_add, map_sub, map_mul, map_pow,
      map_ofNat]

/-- The AS Pfaffians vanish at the projective twisted coordinates. -/
theorem asChartPhiOmA_kleinPAS_eq_zero (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K)
    (k : Fin 5) :
    asChartPhiOmA D g (Work.MotAS.kleinPAS (MvPolynomial.C (aK K D))
      (MvPolynomial.C (bK K D)) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i) k) = 0 := by
  rw [asChartPhiOmA_kleinPAS]
  have hsplit : (fun i => asTwY D g i / asTwY D g 0)
      = fun i => (asTwY D g 0)⁻¹ * asTwY D g i := by
    funext i; rw [div_eq_inv_mul]
  rw [hsplit, Work.MotAS.kleinPAS_smul, kleinPAS_asTwY D hD g]
  simp

/-- **The chart evaluation kills the radical of the AS Pfaffian ideal.** -/
theorem asQideal_le_ker_A (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K) :
    Work.MotAS.asQideal (aK K D) (bK K D) g ≤ RingHom.ker (asChartPhiOmA D g) := by
  have hspan : Ideal.span (Set.range (fun k : Fin 5 =>
      Work.MotAS.kleinPAS (MvPolynomial.C (aK K D))
        (MvPolynomial.C (bK K D)) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) k)) ≤ RingHom.ker (asChartPhiOmA D g) := by
    rw [Ideal.span_le]
    rintro y ⟨k, rfl⟩
    exact RingHom.mem_ker.mpr (asChartPhiOmA_kleinPAS_eq_zero D hD g k)
  intro x hx
  rw [Work.MotAS.asQideal, Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker]
  by_contra hne
  exact pow_ne_zero n hne (by rw [← map_pow, RingHom.mem_ker.mp (hspan hn)])

/-- **The chart evaluation kills the chart ideal** `asChartIdeal a b g`. -/
theorem asChartIdeal_le_ker_OmA (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K) :
    Work.MotAS.asChartIdeal (aK K D) (bK K D) g ≤ RingHom.ker (asChartPhiOmA D g) := by
  refine sup_le (asQideal_le_ker_A D hD g) ?_
  rw [Ideal.span_le]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact RingHom.mem_ker.mpr (by
    haveI := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
    rw [map_sub, asChartPhiOmA_X, map_one, div_self (asTwY_zero_ne_zero D g hD), sub_self])

/-- **The chart evaluation kills the chart ideal** `asChartIdeal a b g` (twist-field-valued). -/
theorem asChartIdeal_le_ker_A (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K) :
    Work.MotAS.asChartIdeal (aK K D) (bK K D) g ≤ RingHom.ker (asChartPhiA D g) := by
  intro x hx
  rw [RingHom.mem_ker]
  apply Subtype.ext
  rw [asChartPhiA_coe]
  show asChartPhiOmA D g x = (0 : OmA K D)
  exact RingHom.mem_ker.mp (asChartIdeal_le_ker_OmA D hD g hx)

/-! ## §5 The assembly: kernel equality implies the chart presentation -/

/-- The AS twist field, unfolded as an `adjoin` so that `IntermediateField.adjoin_induction`
applies without a transparency conversion. -/
noncomputable abbrev asTwistFieldAdjoinA (D : Work.MotV.KleinData 𝕜) (g : K) :
    IntermediateField K (OmA K D) :=
  IntermediateField.adjoin K (Set.range fun j => asTwY D g j / asTwY D g 0)

/-- **The assembly.**  If the chart evaluation has no kernel beyond the chart ideal, then the
fraction field of the chart ring is the AS twist field. -/
theorem asChartPresentation_of_ker_A (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K)
    (hker : RingHom.ker (asChartPhiA D g)
      ≤ Work.MotAS.asChartIdeal (aK K D) (bK K D) g) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (aK K D) (bK K D) g) ≃ₐ[K]
      ↥(twistFieldAS D g)) := by
  classical
  set I := Work.MotAS.asChartIdeal (aK K D) (bK K D) g with hI
  have hIker : I ≤ RingHom.ker (asChartPhiA D g) := asChartIdeal_le_ker_A D hD g
  have hker' : RingHom.ker (asChartPhiA D g) = I := le_antisymm hker hIker
  let ψ : (MvPolynomial (Fin 5) K ⧸ I) →ₐ[K] ↥(asTwistFieldAdjoinA D g) :=
    Ideal.Quotient.liftₐ I (asChartPhiA D g) (fun a ha => RingHom.mem_ker.mp (hIker ha))
  have hψmk : ∀ x, ψ (Ideal.Quotient.mk I x) = asChartPhiA D g x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : asChartPhiA D g x = asChartPhiA D g y := Subtype.ext (congrArg Subtype.val hab)
    have hxy : x - y ∈ I := by
      have h0 : asChartPhiA D g (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hab'
      rw [← hker']
      exact RingHom.mem_ker.mpr h0
    rw [← sub_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  haveI hdom : IsDomain (MvPolynomial (Fin 5) K ⧸ I) :=
    Function.Injective.isDomain ψ hψinj
  let Λ : FractionRing (MvPolynomial (Fin 5) K ⧸ I) →ₐ[K]
      ↥(asTwistFieldAdjoinA D g) := IsFractionRing.liftAlgHom (g := ψ) hψinj
  have hΛ : ∀ a, Λ (algebraMap _ _ a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψinj a
  have hΛinj : Function.Injective Λ := RingHom.injective Λ.toRingHom
  have hsurj : Function.Surjective Λ := by
    intro z
    let p : ∀ x ∈ (↑(asTwistFieldAdjoinA D g) : Set (OmA K D)), Prop :=
      fun x hx => ∃ y : FractionRing (MvPolynomial (Fin 5) K ⧸ I),
        Λ y = (⟨x, hx⟩ : ↥(asTwistFieldAdjoinA D g))
    have key : ∀ x hx, p x hx := by
      intro x hx
      refine IntermediateField.adjoin_induction K (p := p)
        (fun a ha => ?_) (fun c => ?_) (fun a b ha hb iha ihb => ?_) (fun a ha iha => ?_)
        (fun a b ha hb iha ihb => ?_) hx
      · rw [Set.mem_range] at ha
        obtain ⟨i, rfl⟩ := ha
        refine ⟨algebraMap _ _ (Ideal.Quotient.mk I (MvPolynomial.X i)), Subtype.ext ?_⟩
        rw [hΛ, hψmk]
        exact asChartPhiA_X D g i
      · refine ⟨algebraMap K (FractionRing (MvPolynomial (Fin 5) K ⧸ I)) c, ?_⟩
        rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 5) K ⧸ I)
          (FractionRing (MvPolynomial (Fin 5) K ⧸ I)) c, hΛ, AlgHom.commutes]
        rfl
      · obtain ⟨u, hu⟩ := iha; obtain ⟨v, hv⟩ := ihb
        exact ⟨u + v, Subtype.ext (by rw [map_add, hu, hv]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha
        exact ⟨u⁻¹, Subtype.ext (by rw [map_inv₀, hu]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha; obtain ⟨v, hv⟩ := ihb
        exact ⟨u * v, Subtype.ext (by rw [map_mul, hu, hv]; rfl)⟩
    exact key _ z.2
  exact ⟨AlgEquiv.ofBijective Λ ⟨hΛinj, hsurj⟩⟩

end Work.MotC5N3
