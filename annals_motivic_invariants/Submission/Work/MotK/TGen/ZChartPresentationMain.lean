import Mathlib
import Submission.Work.MotK.TGen.ChartSetup
import Submission.Work.MotK.TGen.ChartHeightBound
import Submission.Work.MotK.TGen.KerPhiHeightBound

set_option linter.unusedVariables false -- v435-speed

/-!
# The chart presentation of the twisted Klein curve — the main assembly

`Work.MotK.TGen.chartPhi K D H : K[X₀,…,X₄] →ₐ[K] ↥(twistFieldTG K D H)` is the chart
evaluation `X i ↦ w^{-i}κᵢ/κ₀` (`ChartSetup.lean`), and it kills the chart ideal
`chartIdeal K D H = Qideal a b H ⊔ (X₀ - 1)`.

The **geometric input** is the primeness of the chart ideal, `hprime : (chartIdeal K D H).IsPrime`
(for the use of the census, `H` is a square, and the primeness is then a consequence of the
plane-model computation: `Work.MotK.TGen.ZTwistQidealChart` and `Work.MotK.TGen.ZTwistChartFrac`
identify `FractionRing (K[X] ⧸ chartIdeal)` with `FractionRing (K[X₀,X₁] ⧸ zpgE)`, a field because
`zpgE` is irreducible — `Work.MotK.TGen.ZpgEIrreducible`).

Given `hprime` and the two height bounds

* `ChartHeightBound :  4 ≤ (chartIdeal K D H).height`,
* `KerPhiHeightBound :  (RingHom.ker (chartPhi K D H)).height ≤ 4`

the argument is the one of the Artin–Schreier analogue `Work.MotAS.ASZChartPresentation`:

* `chartIdeal ≤ ker (chartPhi)`; if the inclusion were strict then, `chartIdeal` being prime,
  `Ideal.height_add_one_le_of_lt_of_isPrime` would give
  `(chartIdeal).height + 1 ≤ (ker (chartPhi)).height ≤ 4 ≤ (chartIdeal).height` — impossible.
  Hence `ker (chartPhi) = chartIdeal`.
* Therefore the induced `ψ : K[X] ⧸ chartIdeal →ₐ[K] ↥(twistFieldTG)` is injective, so the
  quotient is a domain, and `IsFractionRing.liftAlgHom` extends `ψ` to
  `Λ : FractionRing (K[X] ⧸ chartIdeal) →ₐ[K] ↥(twistFieldTG)`.
* `Λ` is injective (ring hom out of a field) and surjective: its range is a subfield containing `K`
  and the classes of the `X i`, whose images are the `twCoordG K D H i`, and
  `twistFieldTG K D H = IntermediateField.adjoin K (Set.range (twCoordG K D H))`; conclude with
  `AlgEquiv.ofBijective`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

/-- **The chart presentation**, from primeness of the chart ideal and the two height bounds. -/
theorem ZChartPresentationMain (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (H : K) (hH : H ≠ 0) (hprime : (chartIdeal K D H).IsPrime)
    (hA : 4 ≤ (chartIdeal K D H).height)
    (hB : (RingHom.ker (chartPhi K D H)).height ≤ 4) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) K ⧸ chartIdeal K D H) ≃ₐ[K]
      ↥(Work.MotK.twistFieldTG K D H)) := by
  classical
  set I : Ideal (MvPolynomial (Fin 5) K) := chartIdeal K D H with hI
  have hIker : I ≤ RingHom.ker (chartPhi K D H) := chartIdeal_le_ker K D hD H hH
  have hkerEq : RingHom.ker (chartPhi K D H) = I := by
    refine le_antisymm ?_ hIker
    by_contra hcon
    haveI := hprime
    haveI : (RingHom.ker (chartPhi K D H)).IsPrime := RingHom.ker_isPrime _
    have hlt : I < RingHom.ker (chartPhi K D H) :=
      lt_of_le_of_ne hIker (fun heq => hcon (le_of_eq heq.symm))
    have hstep : I.height + 1 ≤ (RingHom.ker (chartPhi K D H)).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h1 : I.height ≤ (RingHom.ker (chartPhi K D H)).height := Ideal.height_mono hIker
    have h2 : (RingHom.ker (chartPhi K D H)).height ≤ I.height := le_trans hB hA
    have heq : I.height = (RingHom.ker (chartPhi K D H)).height := le_antisymm h1 h2
    rw [heq] at hstep
    have hfin : (RingHom.ker (chartPhi K D H)).height ≠ ⊤ := fun htop => by
      rw [htop] at hB
      exact absurd hB (by norm_num)
    exact absurd ((ENat.add_one_le_iff hfin).mp hstep) (lt_irrefl _)
  -- the induced map on the chart ring
  let ψ : (MvPolynomial (Fin 5) K ⧸ I) →ₐ[K] ↥(Work.MotK.twistFieldTG K D H) :=
    Ideal.Quotient.liftₐ I (chartPhi K D H) (fun a ha => RingHom.mem_ker.mp (hIker ha))
  have hψmk : ∀ x, ψ (Ideal.Quotient.mk I x) = chartPhi K D H x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : chartPhi K D H x = chartPhi K D H y := Subtype.ext (congrArg Subtype.val hab)
    have hxy : x - y ∈ I := by
      have h0 : chartPhi K D H (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hab'
      rw [← hkerEq]
      exact RingHom.mem_ker.mpr h0
    rw [← sub_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  haveI hdom : IsDomain (MvPolynomial (Fin 5) K ⧸ I) := Function.Injective.isDomain ψ hψinj
  let Λ : FractionRing (MvPolynomial (Fin 5) K ⧸ I) →ₐ[K] ↥(Work.MotK.twistFieldTG K D H) :=
    IsFractionRing.liftAlgHom (g := ψ) hψinj
  have hΛ : ∀ a, Λ (algebraMap _ _ a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψinj a
  have hΛinj : Function.Injective Λ := RingHom.injective Λ.toRingHom
  have hsurj : Function.Surjective Λ := by
    intro z
    let p : ∀ x ∈ (↑(Work.MotK.twistFieldTG K D H) : Set (Work.MotK.OmG K D)), Prop :=
      fun x hx => ∃ y : FractionRing (MvPolynomial (Fin 5) K ⧸ I),
        Λ y = (⟨x, hx⟩ : ↥(Work.MotK.twistFieldTG K D H))
    have key : ∀ x hx, p x hx := by
      intro x hx
      refine IntermediateField.adjoin_induction K (p := p)
        (fun a ha => ?_) (fun c => ?_) (fun a b ha hb iha ihb => ?_)
        (fun a ha iha => ?_) (fun a b ha hb iha ihb => ?_) hx
      · rw [Set.mem_range] at ha
        obtain ⟨i, rfl⟩ := ha
        refine ⟨algebraMap _ _ (Ideal.Quotient.mk I (MvPolynomial.X i)), Subtype.ext ?_⟩
        rw [hΛ, hψmk]
        exact chartPhi_X K D H i
      · refine ⟨algebraMap K (FractionRing (MvPolynomial (Fin 5) K ⧸ I)) c, Subtype.ext ?_⟩
        rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 5) K ⧸ I)
          (FractionRing (MvPolynomial (Fin 5) K ⧸ I)) c, hΛ, AlgHom.commutes]
        rfl
      · obtain ⟨u, hu⟩ := iha
        obtain ⟨v, hv⟩ := ihb
        exact ⟨u + v, Subtype.ext (by rw [map_add, hu, hv]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha
        exact ⟨u⁻¹, Subtype.ext (by rw [map_inv₀, hu]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha
        obtain ⟨v, hv⟩ := ihb
        exact ⟨u * v, Subtype.ext (by rw [map_mul, hu, hv]; rfl)⟩
    exact key _ z.2
  exact ⟨AlgEquiv.ofBijective Λ ⟨hΛinj, hsurj⟩⟩

end

end Work.MotK.TGen
