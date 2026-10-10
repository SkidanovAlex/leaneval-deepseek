import Mathlib
import Submission.Work.MotK.TGen.ZTwistQidealAux
import Submission.Work.MotK.TGen.QidealHomogeneous
import Submission.Work.MotK.TGen.ReducedChartQuot

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZTwistQidealChart`

The affine chart `{y₀ = 1}` of the twisted Klein curve `C_{h²} = V(kleinTwP a b (h²)) ⊆ ℙ⁴` can be
described in two ways, and the two descriptions have the same function field:

* in the five coordinates `y₀,…,y₄` with `y₀ = 1`:
  `K[Y₀…Y₄] ⧸ (Qideal a b (h²) ⊔ (Y₀ - 1))`;
* in the four remaining coordinates `y₁,…,y₄`:
  `K[X₀…X₃] ⧸ √(zpgI4 a b h)`.

The two ideals are matched by the substitution `Y 0 ↦ 1`, `Y (i+1) ↦ X i` (`Work.MotK.TGen.sigma`).

## Proof

Set `I5 := Qideal a b (h²) ⊔ (Y₀ - 1)`, `I4 := √(zpgI4 a b h)`, `A5 := K[Y₀…Y₄] ⧸ I5`,
`A4 := K[X₀…X₃] ⧸ I4` and let `Ψ : K[Y₀…Y₄] → A4` be `sigma` followed by the quotient map and
`Φ : K[X₀…X₃] → A5` be `iota` followed by the quotient map.

* `I5 ≤ ker Ψ`: the Pfaffians `Ptw a b h k` are sent to `sigma (Ptw a b h k) = zpgQ a b h k`, which
  lies in `√(zpgI4) = I4`, and `ker Ψ` is radical (it is the preimage of the radical ideal `I4`);
  `Y₀ - 1` is killed by `sigma`.
* `I4 ≤ ker Φ`: `Φ` kills the generators `zpgQ a b h k` of `zpgI4`, and `ker Φ` is radical because
  `A5` is reduced.

Hence `Ψ` and `Φ` induce `Ψ' : A5 → A4` and `Φ' : A4 → A5`, which are mutually inverse:
on the classes of the variables one computes `Ψ' (Φ' (X i)) = X i` (using `sigma ∘ iota = id`) and
`Φ' (Ψ' (Y i)) = Y i` (using `Y 0 = 1`, i.e. that `X 0 - 1 ∈ I5`).  So `A4 ≃ₐ[K] A5`, and applying
`IsFractionRing.algEquivOfAlgEquiv` gives the claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The chart ideal in the five variables `Y₀,…,Y₄`. -/
noncomputable abbrev zqcI5 (a b h : K) : Ideal (MvPolynomial (Fin 5) K) :=
  Work.MotK.TwCensus.Qideal a b (h ^ 2) ⊔ Ideal.span {MvPolynomial.X (0 : Fin 5) - 1}

/-- The chart ideal in the four variables `X₀,…,X₃`. -/
noncomputable abbrev zqcI4 (a b h : K) : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.radical (zpgI4 a b h)

theorem ZTwistQidealChart (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) K ⧸
        (Work.MotK.TwCensus.Qideal a b (h ^ 2) ⊔
          Ideal.span {MvPolynomial.X (0 : Fin 5) - 1})) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 4) K ⧸
        Ideal.radical (Work.MotK.TGen.zpgI4 a b h))) := by
  classical
  -- `A5` is reduced.
  have hred5 : IsReduced (MvPolynomial (Fin 5) K ⧸ zqcI5 a b h) :=
    ReducedChartQuot K (Work.MotK.TwCensus.Qideal a b (h ^ 2))
      (Ideal.radical_isRadical _) (QidealHomogeneous K a b h)
  haveI : IsReduced (MvPolynomial (Fin 5) K ⧸ zqcI5 a b h) := hred5
  haveI : IsReduced (MvPolynomial (Fin 4) K ⧸ zqcI4 a b h) :=
    (Ideal.isRadical_iff_quotient_reduced (zqcI4 a b h)).mp
      (Ideal.radical_isRadical (zpgI4 a b h))
  -- The two algebra maps.
  let Ψ : MvPolynomial (Fin 5) K →ₐ[K] (MvPolynomial (Fin 4) K ⧸ zqcI4 a b h) :=
    (Ideal.Quotient.mkₐ K (zqcI4 a b h)).comp (sigma (K := K))
  let Φ : MvPolynomial (Fin 4) K →ₐ[K] (MvPolynomial (Fin 5) K ⧸ zqcI5 a b h) :=
    (Ideal.Quotient.mkₐ K (zqcI5 a b h)).comp (iota (K := K))
  -- `Y 0 - 1` lies in the chart ideal.
  have hX0 : MvPolynomial.X (0 : Fin 5) - 1 ∈ zqcI5 a b h := by
    rw [zqcI5]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  -- `Y 0 - 1` is killed by `Ψ`.
  have hX0ker : Ideal.span {MvPolynomial.X (0 : Fin 5) - 1} ≤ RingHom.ker Ψ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine RingHom.mem_ker.mpr ?_
    change Ideal.Quotient.mk (zqcI4 a b h)
      (sigma (MvPolynomial.X (0 : Fin 5) - 1)) = 0
    rw [map_sub, sigma_X_zero, map_one, sub_self, map_zero]
  -- `ker Ψ` is radical (preimage of the radical ideal `√(zpgI4)`).
  have hkerΨ_rad : (RingHom.ker Ψ).IsRadical := by
    rw [Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)]
    intro x hx
    have h2 : (Ψ x) ^ 2 = 0 := by rw [← map_pow, RingHom.mem_ker.mp hx]
    exact RingHom.mem_ker.mpr ((isReduced_iff_pow_one_lt 2 (by norm_num)).mp
      (inferInstance : IsReduced (MvPolynomial (Fin 4) K ⧸ zqcI4 a b h)) (Ψ x) h2)
  -- The Pfaffians are killed by `Ψ` modulo the radical.
  have hJ : Ideal.span (Set.range (Ptw a b h)) ≤ RingHom.ker Ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    change Ideal.Quotient.mk (zqcI4 a b h) (sigma (Ptw a b h k)) = 0
    rw [sigma_Ptw, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.subset_span ⟨k, rfl⟩)
  have hQid : Work.MotK.TwCensus.Qideal a b (h ^ 2) ≤ RingHom.ker Ψ := by
    rw [Qideal_eq_radical_span_Ptw]
    exact hkerΨ_rad.radical_le_iff.mpr hJ
  have hΨle : ∀ a' ∈ zqcI5 a b h, Ψ a' = 0 := by
    have hle : zqcI5 a b h ≤ RingHom.ker Ψ := by
      rw [zqcI5]
      exact sup_le hQid hX0ker
    intro a' ha'
    exact RingHom.mem_ker.mp (hle ha')
  -- `ker Φ` is radical because `A5` is reduced.
  have hkerΦ_rad : (RingHom.ker Φ).IsRadical := by
    rw [Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)]
    intro x hx
    have h2 : (Φ x) ^ 2 = 0 := by rw [← map_pow, RingHom.mem_ker.mp hx]
    exact RingHom.mem_ker.mpr ((isReduced_iff_pow_one_lt 2 (by norm_num)).mp
      (inferInstance : IsReduced (MvPolynomial (Fin 5) K ⧸ zqcI5 a b h)) (Φ x) h2)
  -- The chart quadrics are killed by `Φ`.
  have hQle : zpgI4 a b h ≤ RingHom.ker Φ := by
    rw [zpgI4, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    change Ideal.Quotient.mk (zqcI5 a b h) (iota (K := K) (zpgQ a b h k)) = 0
    rw [← sigma_Ptw a b h k, mk_iota_sigma (K := K) hX0, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.le_radical (Ideal.subset_span ⟨k, rfl⟩))
  have hΦle : ∀ a' ∈ zqcI4 a b h, Φ a' = 0 := fun a' ha' =>
    RingHom.mem_ker.mp (hkerΦ_rad.radical_le_iff.mpr hQle ha')
  -- The induced maps.
  let Ψ' : (MvPolynomial (Fin 5) K ⧸ zqcI5 a b h) →ₐ[K]
      (MvPolynomial (Fin 4) K ⧸ zqcI4 a b h) :=
    Ideal.Quotient.liftₐ (zqcI5 a b h) Ψ hΨle
  let Φ' : (MvPolynomial (Fin 4) K ⧸ zqcI4 a b h) →ₐ[K]
      (MvPolynomial (Fin 5) K ⧸ zqcI5 a b h) :=
    Ideal.Quotient.liftₐ (zqcI4 a b h) Φ hΦle
  have hΨ'mk : (Ψ'.comp (Ideal.Quotient.mkₐ K (zqcI5 a b h))) = Ψ :=
    Ideal.Quotient.liftₐ_comp _ _ _
  have hΦ'mk : (Φ'.comp (Ideal.Quotient.mkₐ K (zqcI4 a b h))) = Φ :=
    Ideal.Quotient.liftₐ_comp _ _ _
  have hΨ'_mk : ∀ p : MvPolynomial (Fin 5) K,
      Ψ' (Ideal.Quotient.mkₐ K (zqcI5 a b h) p) = Ψ p :=
    fun p => congrArg (fun f => f p) hΨ'mk
  have hΦ'_mk : ∀ p : MvPolynomial (Fin 4) K,
      Φ' (Ideal.Quotient.mkₐ K (zqcI4 a b h) p) = Φ p :=
    fun p => congrArg (fun f => f p) hΦ'mk
  have h1 : Ψ'.comp Φ' = AlgHom.id K _ := by
    refine AlgHom.ext fun y => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (zqcI4 a b h) y
    rw [AlgHom.comp_apply, hΦ'_mk p, AlgHom.id_apply]
    rw [show Φ p = Ideal.Quotient.mkₐ K (zqcI5 a b h) (iota (K := K) p) from rfl]
    rw [hΨ'_mk (iota p)]
    show Ideal.Quotient.mk (zqcI4 a b h) (sigma (iota (K := K) p))
      = Ideal.Quotient.mk (zqcI4 a b h) p
    rw [sigma_iota]
  have h2 : Φ'.comp Ψ' = AlgHom.id K _ := by
    refine AlgHom.ext fun y => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (zqcI5 a b h) y
    rw [AlgHom.comp_apply, hΨ'_mk p, AlgHom.id_apply]
    rw [show Ψ p = Ideal.Quotient.mkₐ K (zqcI4 a b h) (sigma (K := K) p) from rfl]
    rw [hΦ'_mk (sigma p)]
    show Ideal.Quotient.mk (zqcI5 a b h) (iota (K := K) (sigma p))
      = Ideal.Quotient.mk (zqcI5 a b h) p
    rw [mk_iota_sigma (K := K) hX0]
  exact ⟨IsFractionRing.algEquivOfAlgEquiv (AlgEquiv.ofAlgHom Ψ' Φ' h1 h2)⟩

end Work.MotK.TGen
