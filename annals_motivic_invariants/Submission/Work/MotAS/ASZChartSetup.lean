import Mathlib
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotAS` — the chart of the AS twisted Klein curve: setup

This module collects the definitions and the elementary lemmas used by the AS
(Artin–Schreier) chart presentation (`Work.MotAS.ASZChartPresentation`), so that the geometric
inputs proved in separate modules can be imported by the target file without an import cycle.

The chart `y₀ = 1` of the AS (Artin–Schreier) twisted Klein curve `C_g = V(kleinPAS a b g) ⊂ ℙ⁴`
has function field the AS twist field `twistFieldAS D g = K(y_j/y_0)`, where
`y = asM (asRoot g)⁻¹ κ` are the Lagrange coordinates of the Klein coordinates.

## The route

`Φ : K[X₀,…,X₄] → ↥(twistFieldAS D g)`, `X i ↦ y_i/y_0`, is the chart evaluation.  It kills the
chart ideal `asChartIdeal a b g` (`asChartIdeal_le_ker`); the remaining content is that the
kernel is no larger, i.e. that `S ⧸ asChartIdeal` has fraction field exactly the field generated
by the ratios: this is the input `hker` of the assembly `asChartPresentation_of_ker` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 Homogeneity of the AS Pfaffians -/

theorem kleinPAS0_smul {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    kleinPAS0 a b g (fun i => c * v i) = c ^ 2 * kleinPAS0 a b g v := by
  simp only [kleinPAS0]; ring

theorem kleinPAS1_smul {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    kleinPAS1 a b g (fun i => c * v i) = c ^ 2 * kleinPAS1 a b g v := by
  simp only [kleinPAS1]; ring

theorem kleinPAS2_smul {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    kleinPAS2 a b g (fun i => c * v i) = c ^ 2 * kleinPAS2 a b g v := by
  simp only [kleinPAS2]; ring

theorem kleinPAS3_smul {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    kleinPAS3 a b g (fun i => c * v i) = c ^ 2 * kleinPAS3 a b g v := by
  simp only [kleinPAS3]; ring

theorem kleinPAS4_smul {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    kleinPAS4 a b g (fun i => c * v i) = c ^ 2 * kleinPAS4 a b g v := by
  simp only [kleinPAS4]; ring

/-- The five AS Pfaffians are a quadratic form. -/
theorem kleinPAS_smul {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    kleinPAS a b g (fun i => c * v i) = fun i => c ^ 2 * kleinPAS a b g v i := by
  funext i
  fin_cases i
  · simpa [kleinPAS] using kleinPAS0_smul a b g c v
  · simpa [kleinPAS] using kleinPAS1_smul a b g c v
  · simpa [kleinPAS] using kleinPAS2_smul a b g c v
  · simpa [kleinPAS] using kleinPAS3_smul a b g c v
  · simpa [kleinPAS] using kleinPAS4_smul a b g c v

/-! ## §2 The twisted coordinates satisfy the twisted Pfaffians -/

/-- The five AS Pfaffians evaluated at the Lagrange coordinates `asTwY D g` vanish: this is the
transport `asTransportP` of the Klein relation `D.Good.klein_eq` along `x = asM w · y`. -/
theorem kleinPAS_asTwY (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜) :
    kleinPAS (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a))
        (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b))
        (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) (asTwY D g) = 0 := by
  have ha : algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a)
      = algebraMap 𝕜 (Work.MotV.Om D) D.a :=
    (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.a).symm
  have hb : algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b)
      = algebraMap 𝕜 (Work.MotV.Om D) D.b :=
    (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.b).symm
  rw [ha, hb]
  have h5 : (5 : Work.MotV.Om D) = 0 := five_eq_zero_Om 𝕜 D
  set w : Work.MotV.Om D :=
    algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) with hwdef
  have hw : w ^ 5 = w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g := by
    rw [hwdef]
    have h := congrArg (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D))
      (Work.MotV5.asRoot_spec (𝕜 := 𝕜) g)
    simp only [map_sub, map_pow] at h
    rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g] at h
    linear_combination (norm := refl_ring1) h
  have hM : asM w = asMO D g := by
    ext i j
    rw [hwdef]
    simp only [asM, asMO, Matrix.of_apply, Matrix.map_apply, map_add, map_pow, map_natCast]
  have hmv : (fun i => ∑ j, asM w i j * asTwY D g j)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) := by
    funext i
    have h1 : (∑ j, asM w i j * asTwY D g j) = ((asMO D g).mulVec (asTwY D g)) i := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by
        rw [congrFun (congrFun hM i) j]
    rw [h1, asMO_mulVec_asTwY]
    rfl
  have htr := asTransportP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
    (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) w h5 hw
    (asTwY D g)
  rw [hmv] at htr
  have hzero : Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b)
      (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) = 0 := by
    funext k
    exact hD.klein_eq (Work.MotV.Kb 𝕜) k
  rw [hzero] at htr
  refine asN_mulVec_injective h5 w ?_
  rw [← htr]
  simp

/-! ## §3 The chart evaluation `X i ↦ y_i/y_0` -/

/-- The chart evaluation of the AS twisted Klein curve, with values in `Om D`. -/
noncomputable def asChartPhiOm (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    MvPolynomial (Fin 5) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] Work.MotV.Om D :=
  MvPolynomial.aeval fun i => asTwY D g i / asTwY D g 0

theorem asChartPhiOm_X (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 5) :
    asChartPhiOm D g (MvPolynomial.X i) = asTwY D g i / asTwY D g 0 := by
  simp only [asChartPhiOm, MvPolynomial.aeval_X]

theorem asChartPhiOm_mem (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (x : MvPolynomial (Fin 5) (RatFunc 𝕜)) : asChartPhiOm D g x ∈ twistFieldAS D g := by
  have hle : Algebra.adjoin (RatFunc 𝕜) (Set.range (fun i => asTwY D g i / asTwY D g 0)) ≤
      (twistFieldAS D g).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Set.mem_range_self i)
  have hx : x ∈ Algebra.adjoin (RatFunc 𝕜)
      (Set.range (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
    rw [MvPolynomial.adjoin_range_X]; exact Algebra.mem_top
  have himg : asChartPhiOm D g x ∈
      (Algebra.adjoin (RatFunc 𝕜) (Set.range (MvPolynomial.X :
        Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜)))).map (asChartPhiOm D g) := ⟨x, hx, rfl⟩
  rw [AlgHom.map_adjoin] at himg
  have hrange : (asChartPhiOm D g) ''
      Set.range (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜)) =
      Set.range (fun i => asTwY D g i / asTwY D g 0) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (asChartPhiOm_X D g i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, asChartPhiOm_X D g i⟩
  rw [hrange] at himg
  exact hle himg

/-- The chart evaluation, with values in the AS twist field. -/
noncomputable def asChartPhi (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    MvPolynomial (Fin 5) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] ↥(twistFieldAS D g) :=
  (asChartPhiOm D g).codRestrict (twistFieldAS D g).toSubalgebra (asChartPhiOm_mem D g)

theorem asChartPhi_coe (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (x : MvPolynomial (Fin 5) (RatFunc 𝕜)) :
    ((asChartPhi D g x : ↥(twistFieldAS D g)) : Work.MotV.Om D) = asChartPhiOm D g x :=
  AlgHom.coe_codRestrict _ _ _ _

theorem asChartPhi_X (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 5) :
    ((asChartPhi D g (MvPolynomial.X i) : ↥(twistFieldAS D g)) : Work.MotV.Om D)
      = asTwY D g i / asTwY D g 0 := by
  rw [asChartPhi_coe, asChartPhiOm_X]

/-! ## §4 The chart evaluation kills the chart ideal -/

/-- The evaluation of an AS Pfaffian at the projective coordinates `y_i/y_0`. -/
theorem asChartPhiOm_kleinPAS (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (k : Fin 5) :
    asChartPhiOm D g (kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
      (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b)) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i) k)
      = kleinPAS (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a))
          (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b))
          (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
          (fun i => asTwY D g i / asTwY D g 0) k := by
  fin_cases k <;>
    simp only [asChartPhiOm, kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
      Work.MotK.fin5_zero, Work.MotK.fin5_one, Work.MotK.fin5_two, Work.MotK.fin5_three,
      Work.MotK.fin5_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_add, map_sub, map_mul, map_pow,
      map_ofNat]

/-- The AS Pfaffians vanish at the projective twisted coordinates. -/
theorem asChartPhiOm_kleinPAS_eq_zero (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (k : Fin 5) :
    asChartPhiOm D g (kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
      (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b)) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i) k) = 0 := by
  rw [asChartPhiOm_kleinPAS]
  have hsplit : (fun i => asTwY D g i / asTwY D g 0)
      = fun i => (asTwY D g 0)⁻¹ * asTwY D g i := by
    funext i; rw [div_eq_inv_mul]
  rw [hsplit, kleinPAS_smul, kleinPAS_asTwY D hD g]
  simp

/-- **The chart evaluation kills the radical of the AS Pfaffian ideal.** -/
theorem asQideal_le_ker (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜) :
    asQideal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g
      ≤ RingHom.ker (asChartPhiOm D g) := by
  have hspan : Ideal.span (Set.range (fun k : Fin 5 =>
      kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
        (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b)) (MvPolynomial.C g)
        (fun i => MvPolynomial.X i) k)) ≤ RingHom.ker (asChartPhiOm D g) := by
    rw [Ideal.span_le]
    rintro y ⟨k, rfl⟩
    exact RingHom.mem_ker.mpr (asChartPhiOm_kleinPAS_eq_zero D hD g k)
  intro x hx
  rw [asQideal, Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker]
  by_contra hne
  exact pow_ne_zero n hne (by rw [← map_pow, RingHom.mem_ker.mp (hspan hn)])

/-- **The chart evaluation kills the chart ideal** `asChartIdeal a b g`. -/
theorem asChartIdeal_le_ker_Om (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜) :
    asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g
      ≤ RingHom.ker (asChartPhiOm D g) := by
  refine sup_le (asQideal_le_ker D hD g) ?_
  rw [Ideal.span_le]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact RingHom.mem_ker.mpr (by
    rw [map_sub, asChartPhiOm_X, map_one, div_self (asTwY_zero_ne_zero D g hD), sub_self])

/-- **The chart evaluation kills the chart ideal** `asChartIdeal a b g` (twist-field-valued). -/
theorem asChartIdeal_le_ker (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜) :
    asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g
      ≤ RingHom.ker (asChartPhi D g) := by
  intro x hx
  rw [RingHom.mem_ker]
  apply Subtype.ext
  rw [asChartPhi_coe]
  show asChartPhiOm D g x = (0 : Work.MotV.Om D)
  exact RingHom.mem_ker.mp (asChartIdeal_le_ker_Om D hD g hx)

/-! ## §5 The assembly: kernel equality implies the chart presentation -/

/-- The AS twist field, unfolded as an `adjoin` so that `IntermediateField.adjoin_induction`
applies without a transparency conversion. -/
noncomputable abbrev asTwistFieldAdjoin (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜) (Set.range fun j => asTwY D g j / asTwY D g 0)

/-- **The assembly.**  If the chart evaluation has no kernel beyond the chart ideal, then the
fraction field of the chart ring is the AS twist field. -/
theorem asChartPresentation_of_ker (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (hker : RingHom.ker (asChartPhi D g)
      ≤ asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸
        asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g) ≃ₐ[RatFunc 𝕜]
      ↥(twistFieldAS D g)) := by
  classical
  set I := asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g with hI
  have hIker : I ≤ RingHom.ker (asChartPhi D g) := asChartIdeal_le_ker D hD g
  have hker' : RingHom.ker (asChartPhi D g) = I := le_antisymm hker hIker
  let ψ : (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I) →ₐ[RatFunc 𝕜] ↥(asTwistFieldAdjoin D g) :=
    Ideal.Quotient.liftₐ I (asChartPhi D g) (fun a ha => RingHom.mem_ker.mp (hIker ha))
  have hψmk : ∀ x, ψ (Ideal.Quotient.mk I x) = asChartPhi D g x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : asChartPhi D g x = asChartPhi D g y := Subtype.ext (congrArg Subtype.val hab)
    have hxy : x - y ∈ I := by
      have h0 : asChartPhi D g (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hab'
      rw [← hker']
      exact RingHom.mem_ker.mpr h0
    rw [← sub_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  haveI hdom : IsDomain (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I) :=
    Function.Injective.isDomain ψ hψinj
  let Λ : FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I) →ₐ[RatFunc 𝕜]
      ↥(asTwistFieldAdjoin D g) := IsFractionRing.liftAlgHom (g := ψ) hψinj
  have hΛ : ∀ a, Λ (algebraMap _ _ a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψinj a
  have hΛinj : Function.Injective Λ := RingHom.injective Λ.toRingHom
  have hsurj : Function.Surjective Λ := by
    intro z
    let p : ∀ x ∈ (↑(asTwistFieldAdjoin D g) : Set (Work.MotV.Om D)), Prop :=
      fun x hx => ∃ y : FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I),
        Λ y = (⟨x, hx⟩ : ↥(asTwistFieldAdjoin D g))
    have key : ∀ x hx, p x hx := by
      intro x hx
      refine IntermediateField.adjoin_induction (RatFunc 𝕜) (p := p)
        (fun a ha => ?_) (fun c => ?_) (fun a b ha hb iha ihb => ?_) (fun a ha iha => ?_)
        (fun a b ha hb iha ihb => ?_) hx
      · rw [Set.mem_range] at ha
        obtain ⟨i, rfl⟩ := ha
        refine ⟨algebraMap _ _ (Ideal.Quotient.mk I (MvPolynomial.X i)), Subtype.ext ?_⟩
        rw [hΛ, hψmk]
        exact asChartPhi_X D g i
      · refine ⟨algebraMap (RatFunc 𝕜) (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I)) c, ?_⟩
        rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I)
          (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I)) c, hΛ, AlgHom.commutes]
        rfl
      · obtain ⟨u, hu⟩ := iha; obtain ⟨v, hv⟩ := ihb
        exact ⟨u + v, Subtype.ext (by rw [map_add, hu, hv]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha
        exact ⟨u⁻¹, Subtype.ext (by rw [map_inv₀, hu]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha; obtain ⟨v, hv⟩ := ihb
        exact ⟨u * v, Subtype.ext (by rw [map_mul, hu, hv]; rfl)⟩
    exact key _ z.2
  exact ⟨AlgEquiv.ofBijective Λ ⟨hΛinj, hsurj⟩⟩

/-! ## §6 The kernel inclusion from the geometric inputs -/

/-- **The kernel of the chart evaluation is the chart ideal**, given the two geometric inputs
(irreducibility and one-dimensionality of the chart) and the transcendence-degree bound on the
kernel. -/
theorem asChartKernelLe_of_prime (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (hprime : (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).IsPrime)
    (hheight : 4 ≤ (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a)
      (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).height)
    (hkerHt : (RingHom.ker (asChartPhi D g)).height ≤ 4) :
    RingHom.ker (asChartPhi D g)
      ≤ asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g := by
  have hle : asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g
      ≤ RingHom.ker (asChartPhi D g) := asChartIdeal_le_ker D hD g
  haveI := hprime
  haveI hkerPrime : (RingHom.ker (asChartPhi D g)).IsPrime := RingHom.ker_isPrime _
  by_contra hcon
  have hne : asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g
      ≠ RingHom.ker (asChartPhi D g) := fun h => hcon (le_of_eq h.symm)
  have hlt : asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g
      < RingHom.ker (asChartPhi D g) := lt_of_le_of_ne hle hne
  have hstep : (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).height
      + 1 ≤ (RingHom.ker (asChartPhi D g)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hht1 : (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).height
      ≤ (RingHom.ker (asChartPhi D g)).height := Ideal.height_mono hle
  have hht2 : (RingHom.ker (asChartPhi D g)).height
      ≤ (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).height :=
    le_trans hkerHt hheight
  have heq : (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).height
      = (RingHom.ker (asChartPhi D g)).height := le_antisymm hht1 hht2
  have hcontra : (RingHom.ker (asChartPhi D g)).height + 1
      ≤ (RingHom.ker (asChartPhi D g)).height := by
    calc (RingHom.ker (asChartPhi D g)).height + 1
        = (asChartIdeal (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) g).height + 1 := by
          rw [heq]
      _ ≤ (RingHom.ker (asChartPhi D g)).height := hstep
  have hfin : (RingHom.ker (asChartPhi D g)).height ≠ ⊤ :=
    fun htop => absurd (htop ▸ hkerHt : (⊤ : ℕ∞) ≤ 4) (by norm_num)
  exact absurd ((ENat.add_one_le_iff hfin).mp hcontra) (lt_irrefl _)

end Work.MotAS
