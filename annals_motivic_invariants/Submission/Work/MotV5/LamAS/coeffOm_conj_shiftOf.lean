import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.LamAS.exists_coeffAlgHom_induced

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotV5.LamAS.coeffOm_conj_shiftOf`

An `𝕜`-algebra automorphism `g` of `Om D = K̄(E)` which fixes all Klein coordinates `κ_i` and
carries the constants `Kb 𝕜` into themselves commutes with the projective fifth-torsion shift
`σS` (`KleinData.ShiftOf D σS`), in the sense that
`g ∘ σS ∘ g⁻¹ = σS`.

The proof: the conjugated map `h = g ∘ σS ∘ g⁻¹` fixes the constants (the induced map on `Kb 𝕜` is
surjective, being an injective `𝕜`-algebra endomorphism of `AlgebraicClosure (RatFunc 𝕜)`), and `h`
and `σS` agree on the Klein ratios `κ_i/κ_0` (the scalar `λ` of `σS κ_i = λ κ_{i+1}` cancels);
since the ratios generate `Om D` over `Kb 𝕜` (`KleinData.Generates`), `h = σS`.

The two inputs are the bookkeeping lemma `Work.MotV5.LamAS.exists_coeffAlgHom_induced` (the action
of `g` on the constants, proved in the sibling file) and `kb_algHom_surjective` below (an injective
`𝕜`-algebra endomorphism of `AlgebraicClosure (RatFunc 𝕜)` is surjective; the same statement, for a
general base field, is `Work.MotV5.LamAS.algClosure_algHom_surjective`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MotV5.LamAS

open Work.MotV

/-- **An injective `𝕜`-algebra endomorphism of `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)` is
surjective.**  (Local copy for this file; the general statement over a base field `K` is
`Work.MotV5.LamAS.algClosure_algHom_surjective`.)

`Kb 𝕜` has transcendence degree `1` over `𝕜` (it is algebraic over `𝕜(t)`, and
`trdeg 𝕜 𝕜(t) = 1` since `RatFunc.X` is a transcendence basis), so the image of `ψ` has the same
transcendence degree and `Kb 𝕜` is algebraic over it; an algebraic extension of an algebraically
closed field is trivial, so `ψ` is onto. -/
private theorem kb_algHom_surjective (𝕜 : Type) [Field 𝕜]
    (ψ : Kb 𝕜 →ₐ[𝕜] Kb 𝕜) (hψ : Function.Injective ψ) : Function.Surjective ψ := by
  have hIA : Algebra.IsAlgebraic (Polynomial 𝕜) (RatFunc 𝕜) := by
    refine ⟨fun x => ?_⟩
    rw [IsFractionRing.isAlgebraic_iff (Polynomial 𝕜) (RatFunc 𝕜) (RatFunc 𝕜)]
    exact isAlgebraic_algebraMap x
  haveI := hIA
  have h1 : Algebra.trdeg 𝕜 (RatFunc 𝕜) = 1 := by
    have hb : IsTranscendenceBasis 𝕜 (fun _ : Unit => (RatFunc.X : RatFunc 𝕜)) :=
      (IsTranscendenceBasis.polynomial Unit 𝕜).algebraMap_comp (S := Polynomial 𝕜) (A := RatFunc 𝕜)
    have hb' := hb.to_subtype_range
    have h := hb'.cardinalMk_eq_trdeg
    rw [← h]
    simp
  have h2 : Algebra.trdeg 𝕜 (Kb 𝕜) = 1 := by
    rw [← trdeg_add_eq (A := Kb 𝕜) 𝕜 (RatFunc 𝕜), h1, trdeg_eq_zero (R := RatFunc 𝕜)]
    simp
  let L : IntermediateField 𝕜 (Kb 𝕜) := ψ.fieldRange
  let ψ' : Kb 𝕜 →ₐ[𝕜] ↥L :=
    ψ.codRestrict L.toSubalgebra (fun x => (AlgHom.mem_fieldRange (f := ψ)).mpr ⟨x, rfl⟩)
  have hψ'bij : Function.Bijective ψ' := by
    constructor
    · intro x y hxy
      exact hψ (congrArg Subtype.val hxy)
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := ψ)).mp hz
      exact ⟨x, Subtype.ext hx⟩
  let e : Kb 𝕜 ≃ₐ[𝕜] ↥L := AlgEquiv.ofBijective ψ' hψ'bij
  haveI : IsAlgClosed ↥L := IsAlgClosed.of_ringEquiv _ _ e.toRingEquiv
  haveI hfs : FaithfulSMul 𝕜 ↥L :=
    (faithfulSMul_iff_algebraMap_injective 𝕜 ↥L).mpr (RingHom.injective (algebraMap 𝕜 ↥L))
  have h3 : Algebra.trdeg 𝕜 ↥L = 1 := by rw [← e.trdeg_eq, h2]
  have hsum : Algebra.trdeg 𝕜 ↥L + Algebra.trdeg ↥L (Kb 𝕜) = 1 := by
    rw [trdeg_add_eq (A := Kb 𝕜) 𝕜 ↥L, h2]
  have hb0 : Algebra.trdeg ↥L (Kb 𝕜) = 0 := by
    rcases eq_or_ne (Algebra.trdeg ↥L (Kb 𝕜)) 0 with h | h
    · exact h
    · exfalso
      have hle : Algebra.trdeg ↥L (Kb 𝕜) ≤ 1 := (self_le_add_left _ _).trans_eq hsum
      have h1le : (1 : Cardinal) ≤ Algebra.trdeg ↥L (Kb 𝕜) :=
        Cardinal.one_le_iff_ne_zero.mpr h
      have heq : Algebra.trdeg ↥L (Kb 𝕜) = 1 := le_antisymm hle h1le
      rw [heq, h3] at hsum
      norm_num at hsum
  haveI : Algebra.IsAlgebraic ↥L (Kb 𝕜) := trdeg_eq_zero_iff.mp hb0
  have hsurj : Function.Surjective (algebraMap ↥L (Kb 𝕜)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ↥L) (K := Kb 𝕜)).2
  intro z
  obtain ⟨w, hw⟩ := hsurj z
  obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := ψ)).mp w.2
  exact ⟨x, by rw [hx]; exact hw⟩

/-- The body of the proof of `coeffOm_conj_shiftOf`, with the two inputs of the argument made
explicit: the induced map `ψ` of `g` on the constants `Kb 𝕜`, and the surjectivity of `ψ`. -/
private theorem coeffOm_conj_shiftOf_aux (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (g : Om D ≃ₐ[𝕜] Om D)
    (hgκ : ∀ i : Fin 5, g (kleinCoord D (Kb 𝕜) i) = kleinCoord D (Kb 𝕜) i)
    (σS : Om D ≃ₐ[Kb 𝕜] Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS)
    (ψ : Kb 𝕜 →ₐ[𝕜] Kb 𝕜)
    (hψ : ∀ c : Kb 𝕜,
      g (algebraMap (Kb 𝕜) (Om D) c) = algebraMap (Kb 𝕜) (Om D) (ψ c))
    (hψsurj : Function.Surjective ψ) :
    ∀ x : Om D, g (σS (g⁻¹ x)) = σS x := by
  have hGood : KleinData.Good D := hD.1
  have hκ0 : kleinCoord D (Kb 𝕜) 0 ≠ 0 := hGood.coord0_ne (Kb 𝕜)
  obtain ⟨lam, hlam, hshift⟩ := hσS
  -- the conjugated automorphism, as an `𝕜`-algebra endomorphism
  let h : Om D →ₐ[𝕜] Om D :=
    (g : Om D →ₐ[𝕜] Om D).comp
      (((σS.restrictScalars 𝕜 : Om D ≃ₐ[𝕜] Om D) : Om D →ₐ[𝕜] Om D).comp
        (g.symm : Om D →ₐ[𝕜] Om D))
  have hh : ∀ x : Om D, h x = g (σS (g⁻¹ x)) := fun x => rfl
  -- ## `h` fixes the constants
  have hfix : ∀ c : Kb 𝕜,
      h (algebraMap (Kb 𝕜) (Om D) c) = (σS.restrictScalars 𝕜) (algebraMap (Kb 𝕜) (Om D) c) := by
    intro c
    obtain ⟨d, hd⟩ := hψsurj c
    have hgd : g (algebraMap (Kb 𝕜) (Om D) d) = algebraMap (Kb 𝕜) (Om D) c := by
      rw [hψ d, hd]
    have hginv : g⁻¹ (algebraMap (Kb 𝕜) (Om D) c) = algebraMap (Kb 𝕜) (Om D) d := by
      change g.symm (algebraMap (Kb 𝕜) (Om D) c) = algebraMap (Kb 𝕜) (Om D) d
      rw [← hgd, AlgEquiv.symm_apply_apply]
    calc h (algebraMap (Kb 𝕜) (Om D) c)
        = g (σS (g⁻¹ (algebraMap (Kb 𝕜) (Om D) c))) := rfl
      _ = g (σS (algebraMap (Kb 𝕜) (Om D) d)) := by rw [hginv]
      _ = g (algebraMap (Kb 𝕜) (Om D) d) := by rw [AlgEquiv.commutes σS d]
      _ = algebraMap (Kb 𝕜) (Om D) c := hgd
      _ = (σS.restrictScalars 𝕜) (algebraMap (Kb 𝕜) (Om D) c) := by
          rw [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes σS c]
  -- ## `g⁻¹` fixes the Klein coordinates
  have hginvκ : ∀ j : Fin 5, g⁻¹ (kleinCoord D (Kb 𝕜) j) = kleinCoord D (Kb 𝕜) j := by
    intro j
    change g.symm (kleinCoord D (Kb 𝕜) j) = kleinCoord D (Kb 𝕜) j
    apply g.injective
    rw [AlgEquiv.apply_symm_apply, hgκ j]
  -- ## the shift on the Klein ratios
  have hσSratio : ∀ i : Fin 5, σS (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)
      = kleinCoord D (Kb 𝕜) (i + 1) / kleinCoord D (Kb 𝕜) 1 := by
    intro i
    rw [map_div₀, hshift i, hshift 0, show ((0 : Fin 5) + 1) = 1 from rfl,
      mul_div_mul_left _ _ hlam]
  -- ## `h` agrees with the shift on the Klein ratios
  have hratio : ∀ i : Fin 5, h (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)
      = (σS.restrictScalars 𝕜) (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := by
    intro i
    calc h (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)
        = g (σS (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) := by
          rw [show h (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)
              = g (σS (g⁻¹ (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0))) from rfl]
          rw [map_div₀, hginvκ i, hginvκ 0]
      _ = g (kleinCoord D (Kb 𝕜) (i + 1) / kleinCoord D (Kb 𝕜) 1) := by rw [hσSratio i]
      _ = kleinCoord D (Kb 𝕜) (i + 1) / kleinCoord D (Kb 𝕜) 1 := by rw [map_div₀, hgκ, hgκ]
      _ = (σS.restrictScalars 𝕜) (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := by
          rw [AlgEquiv.restrictScalars_apply, hσSratio i]
  -- ## the equaliser of `h` and `σS` is everything
  have hEq : ∀ x : Om D, h x = (σS.restrictScalars 𝕜) x := by
    let E : IntermediateField (Kb 𝕜) (Om D) :=
      { carrier := {x | h x = (σS.restrictScalars 𝕜) x}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, map_mul, ha, hb]
        one_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_add, map_add, ha, hb]
        zero_mem' := by simp
        algebraMap_mem' := fun c => hfix c
        inv_mem' := fun x hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [map_inv₀, map_inv₀, hx] }
    have hgen : IntermediateField.adjoin (Kb 𝕜)
        (Set.range (fun i : Fin 5 => kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) = ⊤ :=
      hD.2.2.1 (Kb 𝕜)
    have hle : IntermediateField.adjoin (Kb 𝕜)
        (Set.range (fun i : Fin 5 => kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) ≤ E := by
      rw [IntermediateField.adjoin_le_iff]
      rintro z ⟨i, rfl⟩
      exact hratio i
    have htop : (⊤ : IntermediateField (Kb 𝕜) (Om D)) ≤ E := by
      rw [← hgen]
      exact hle
    intro x
    exact htop IntermediateField.mem_top
  intro x
  calc g (σS (g⁻¹ x)) = h x := (hh x).symm
    _ = (σS.restrictScalars 𝕜) x := hEq x
    _ = σS x := rfl

theorem coeffOm_conj_shiftOf (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (g : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hgκ : ∀ i : Fin 5,
      g (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
        = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
    (hgKb : ∀ c : Work.MotV.Kb 𝕜, ∃ c' : Work.MotV.Kb 𝕜,
      g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c')
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS) :
    ∀ x : Work.MotV.Om D, g (σS (g⁻¹ x)) = σS x := by
  obtain ⟨ψ, hψinj, hψ⟩ := Work.MotV5.LamAS.exists_coeffAlgHom_induced (𝕜 := 𝕜) D g hgKb
  exact coeffOm_conj_shiftOf_aux 𝕜 D hD g hgκ σS hσS ψ hψ
    (kb_algHom_surjective 𝕜 ψ hψinj)

end Work.MotV5.LamAS
