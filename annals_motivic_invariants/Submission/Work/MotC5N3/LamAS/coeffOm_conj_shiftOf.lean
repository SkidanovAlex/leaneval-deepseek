import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC5N3.LamAS.exists_coeffAlgHom_induced

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.LamAS.coeffOm_conj_shiftOf` (general base field `K`)

Port of `Submission/Work/MotV5/LamAS/coeffOm_conj_shiftOf.lean`.

A `K`-algebra automorphism `g` of `OmA K D = K̄(E)` which fixes all Klein coordinates `κ_i` and
carries the constants `KbA K` into themselves commutes with the projective fifth-torsion shift
`σS` (`KleinData.ShiftOf D σS`), in the sense that `g ∘ σS ∘ g⁻¹ = σS`.

**Adaptation.**  In the source the base field is `RatFunc 𝕜` and `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`;
the surjectivity of the induced map `ψ` on the constants is there obtained from
`trdeg 𝕜 (Kb 𝕜) = 1`.  Over a general `K` this is false, but it is not needed: the relevant `g` is
`K`-linear (`asCoeffOm` of a `K`-automorphism of `K̄`), so the induced `ψ` is a `K`-algebra
endomorphism of `K̄ = AlgebraicClosure K`, which is algebraic over `K`, hence bijective
(`Algebra.IsAlgebraic.algHom_bijective`).  We therefore state the result for `g : OmA K D ≃ₐ[K] OmA K D`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MotC5N3.LamAS

open Work.MotV

/-- **The map induced by a `K`-algebra automorphism of `OmA K D` on the constants `KbA K`.**
If `g` carries `KbA K` into itself, then it acts there as a `K`-algebra endomorphism `ψ`. -/
theorem exists_coeffAlgHom_induced_K (𝕜 : Type) [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜)
    (g : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (hgKb : ∀ c : Work.MotC5N3.KbA K, ∃ c' : Work.MotC5N3.KbA K,
      g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c') :
    ∃ ψ : Work.MotC5N3.KbA K →ₐ[K] Work.MotC5N3.KbA K,
      ∀ c : Work.MotC5N3.KbA K,
        g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
          = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψ c) := by
  classical
  have hinj : Function.Injective
      (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) := RingHom.injective _
  let ψfun : Work.MotC5N3.KbA K → Work.MotC5N3.KbA K := fun c => Classical.choose (hgKb c)
  have hψ : ∀ c : Work.MotC5N3.KbA K,
      g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun c) :=
    fun c => Classical.choose_spec (hgKb c)
  have key : ∀ c : Work.MotC5N3.KbA K,
      algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun c)
        = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) :=
    fun c => (hψ c).symm
  let ψ : Work.MotC5N3.KbA K →ₐ[K] Work.MotC5N3.KbA K :=
    { toFun := ψfun
      map_one' := hinj (by
        rw [key 1, map_one (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)),
          map_one g])
      map_mul' := fun a b => hinj (calc
        algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun (a * b))
            = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (a * b)) := key (a * b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a
                * algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              congrArg g (map_mul (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) a b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a)
                * g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              map_mul g _ _
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a)
                * algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun b) := by
              rw [key a, key b]
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a * ψfun b) :=
              (map_mul (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) (ψfun a) (ψfun b)).symm)
      map_zero' := hinj (by
        rw [key 0, map_zero (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)),
          map_zero g])
      map_add' := fun a b => hinj (calc
        algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun (a + b))
            = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (a + b)) := key (a + b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a
                + algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              congrArg g (map_add (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) a b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a)
                + g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              map_add g _ _
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a)
                + algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun b) := by
              rw [key a, key b]
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a + ψfun b) :=
              (map_add (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) (ψfun a) (ψfun b)).symm)
      commutes' := fun a => hinj (calc
        algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
            (ψfun (algebraMap K (Work.MotC5N3.KbA K) a))
            = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
                  (algebraMap K (Work.MotC5N3.KbA K) a)) := key _
        _ = g (algebraMap K (Work.MotC5N3.OmA K D) a) :=
              congrArg g (IsScalarTower.algebraMap_apply K (Work.MotC5N3.KbA K)
                (Work.MotC5N3.OmA K D) a).symm
        _ = algebraMap K (Work.MotC5N3.OmA K D) a := AlgEquiv.commutes g a
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
              (algebraMap K (Work.MotC5N3.KbA K) a) :=
              IsScalarTower.algebraMap_apply K (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a) }
  exact ⟨ψ, fun c => hψ c⟩

/-- The body of the proof of `coeffOm_conj_shiftOf`, with the two inputs of the argument made
explicit: the induced map `ψ` of `g` on the constants `KbA K`, and the surjectivity of `ψ`. -/
private theorem coeffOm_conj_shiftOf_aux (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K]
    [Algebra 𝕜 K] [CharP K 5]
    (D : KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (g : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (hgκ : ∀ i : Fin 5, g (kleinCoord D (Work.MotC5N3.KbA K) i) = kleinCoord D (Work.MotC5N3.KbA K) i)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hσS : Work.MotC5N3.KleinData.ShiftOf D σS)
    (ψ : Work.MotC5N3.KbA K →ₐ[K] Work.MotC5N3.KbA K)
    (hψ : ∀ c : Work.MotC5N3.KbA K,
      g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψ c))
    (hψsurj : Function.Surjective ψ) :
    ∀ x : Work.MotC5N3.OmA K D, g (σS (g⁻¹ x)) = σS x := by
  have hGood : KleinData.Good D := hD.1
  have hκ0 : kleinCoord D (Work.MotC5N3.KbA K) 0 ≠ 0 := hGood.coord0_ne (Work.MotC5N3.KbA K)
  obtain ⟨lam, hlam, hshift⟩ := hσS
  -- the conjugated automorphism, as a `K`-algebra endomorphism
  let h : Work.MotC5N3.OmA K D →ₐ[K] Work.MotC5N3.OmA K D :=
    (g : Work.MotC5N3.OmA K D →ₐ[K] Work.MotC5N3.OmA K D).comp
      (((σS.restrictScalars K : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D) : Work.MotC5N3.OmA K D →ₐ[K] Work.MotC5N3.OmA K D).comp
        (g.symm : Work.MotC5N3.OmA K D →ₐ[K] Work.MotC5N3.OmA K D))
  have hh : ∀ x : Work.MotC5N3.OmA K D, h x = g (σS (g⁻¹ x)) := fun x => rfl
  -- ## `h` fixes the constants
  have hfix : ∀ c : Work.MotC5N3.KbA K,
      h (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) = (σS.restrictScalars K) (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) := by
    intro c
    obtain ⟨d, hd⟩ := hψsurj c
    have hgd : g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) d) = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c := by
      rw [hψ d, hd]
    have hginv : g⁻¹ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) d := by
      change g.symm (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) d
      rw [← hgd, AlgEquiv.symm_apply_apply]
    calc h (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = g (σS (g⁻¹ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c))) := rfl
      _ = g (σS (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) d)) := by rw [hginv]
      _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) d) := by rw [AlgEquiv.commutes σS d]
      _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c := hgd
      _ = (σS.restrictScalars K) (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) := by
          rw [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes σS c]
  -- ## `g⁻¹` fixes the Klein coordinates
  have hginvκ : ∀ j : Fin 5, g⁻¹ (kleinCoord D (Work.MotC5N3.KbA K) j) = kleinCoord D (Work.MotC5N3.KbA K) j := by
    intro j
    change g.symm (kleinCoord D (Work.MotC5N3.KbA K) j) = kleinCoord D (Work.MotC5N3.KbA K) j
    apply g.injective
    rw [AlgEquiv.apply_symm_apply, hgκ j]
  -- ## the shift on the Klein ratios
  have hσSratio : ∀ i : Fin 5, σS (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)
      = kleinCoord D (Work.MotC5N3.KbA K) (i + 1) / kleinCoord D (Work.MotC5N3.KbA K) 1 := by
    intro i
    rw [map_div₀, hshift i, hshift 0, show ((0 : Fin 5) + 1) = 1 from rfl,
      mul_div_mul_left _ _ hlam]
  -- ## `h` agrees with the shift on the Klein ratios
  have hratio : ∀ i : Fin 5, h (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)
      = (σS.restrictScalars K) (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0) := by
    intro i
    calc h (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)
        = g (σS (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)) := by
          rw [show h (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)
              = g (σS (g⁻¹ (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0))) from rfl]
          rw [map_div₀, hginvκ i, hginvκ 0]
      _ = g (kleinCoord D (Work.MotC5N3.KbA K) (i + 1) / kleinCoord D (Work.MotC5N3.KbA K) 1) := by rw [hσSratio i]
      _ = kleinCoord D (Work.MotC5N3.KbA K) (i + 1) / kleinCoord D (Work.MotC5N3.KbA K) 1 := by rw [map_div₀, hgκ, hgκ]
      _ = (σS.restrictScalars K) (kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0) := by
          rw [AlgEquiv.restrictScalars_apply, hσSratio i]
  -- ## the equaliser of `h` and `σS` is everything
  have hEq : ∀ x : Work.MotC5N3.OmA K D, h x = (σS.restrictScalars K) x := by
    let E : IntermediateField (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) :=
      { carrier := {x | h x = (σS.restrictScalars K) x}
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
    have hgen : IntermediateField.adjoin (Work.MotC5N3.KbA K)
        (Set.range (fun i : Fin 5 => kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)) = ⊤ :=
      hD.2.2.1 (Work.MotC5N3.KbA K)
    have hle : IntermediateField.adjoin (Work.MotC5N3.KbA K)
        (Set.range (fun i : Fin 5 => kleinCoord D (Work.MotC5N3.KbA K) i / kleinCoord D (Work.MotC5N3.KbA K) 0)) ≤ E := by
      rw [IntermediateField.adjoin_le_iff]
      rintro z ⟨i, rfl⟩
      exact hratio i
    have htop : (⊤ : IntermediateField (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) ≤ E := by
      rw [← hgen]
      exact hle
    intro x
    exact htop IntermediateField.mem_top
  intro x
  calc g (σS (g⁻¹ x)) = h x := (hh x).symm
    _ = (σS.restrictScalars K) x := hEq x
    _ = σS x := rfl

theorem coeffOm_conj_shiftOf (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (g : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (hgκ : ∀ i : Fin 5,
      g (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i)
        = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i)
    (hgKb : ∀ c : Work.MotC5N3.KbA K, ∃ c' : Work.MotC5N3.KbA K,
      g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c')
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hσS : Work.MotC5N3.KleinData.ShiftOf D σS) :
    ∀ x : Work.MotC5N3.OmA K D, g (σS (g⁻¹ x)) = σS x := by
  obtain ⟨ψ, hψ⟩ := exists_coeffAlgHom_induced_K 𝕜 D g hgKb
  exact coeffOm_conj_shiftOf_aux 𝕜 D hD g hgκ σS hσS ψ hψ
    (Algebra.IsAlgebraic.algHom_bijective ψ).2

end Work.MotC5N3.LamAS
