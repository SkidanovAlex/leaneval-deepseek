import Submission.Vdw.LocalField.OWClosure

/-!
# TraceResidue — trace of the Teichmüller generator

First lemma of the residue-trace reduction (stone-4 follow-up):

* `minpoly_zetaW_eq` : the minimal polynomial of the Teichmüller generator
  `ζ` over `ℚ_p` is the map of its `ℤ_[p]`-minimal polynomial `teichMinpolyInt`.

* `tr_zeta_int` : `Tr_{W/ℚ_p}(ζ) = -(nextCoeff g)`, where
  `g = teichMinpolyInt p P α` is the ℤ_[p]-minimal polynomial of ζ — so the
  trace is an integral (ℤ_[p]) element whose mod-p reduction will be
  computable from the reduction `ḡ`.

All statements: axioms = propext / Classical.choice / Quot.sound only.
-/

open scoped NumberField WithZero Valued
set_option autoImplicit false
set_option linter.style.haveILetI false
namespace Submission.Vdw.LocalField
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]

/-- minpoly of ζ (as element of W) over ℚ_p is the ℚ_p-map of the ℤ_p-minpoly. -/
theorem minpoly_zetaW_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0) :
    minpoly (QpAdic p) (zetaW p P α) =
      Polynomial.map (algebraMap (QpInt p) (QpAdic p)) (teichMinpolyInt p P α) := by
  classical
  let m : Polynomial (QpAdic p) := minpoly (QpAdic p) (zetaW p P α)
  let g : Polynomial (QpInt p) := teichMinpolyInt p P α
  let φ : QpInt p →+* QpAdic p := algebraMap (QpInt p) (QpAdic p)
  have hmon : (Polynomial.map φ g).Monic := (teichMinpolyInt_monic p P hα).map φ
  -- irreducibility: g.map φ = field minpoly of the kpAdic value
  have hval : (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))) =
      Polynomial.map φ g := by
    dsimp [g, φ]
    exact teich_minpoly_eq_field_map p P hα
  have hirr : Irreducible (Polynomial.map φ g) := by
    rw [← hval]
    exact minpoly.irreducible (teich_isIntegral_kpAdic (p := p) (P := P) (α := α) hα)
  -- aeval zetaW (map φ g) = 0, via the value map into kpAdic
  have haeval : Polynomial.aeval (zetaW p P α) (Polynomial.map φ g) = 0 := by
    -- value map ν : Wk →ₐ kpAdic
    let ν : Wk p P α →ₐ[QpAdic p] kpAdic p P := (Wk p P α).val
    have hν0 : ν.toRingHom (Polynomial.aeval (zetaW p P α) (Polynomial.map φ g)) = 0 := by
      -- hom_eval₂: ν (eval₂ (algebraMap QpAdic Wk) zetaW p) = eval₂ (ν∘alg) (ν zetaW) p
      have hze : Polynomial.aeval (zetaW p P α) (Polynomial.map φ g) =
          Polynomial.eval₂ (algebraMap (QpAdic p) (Wk p P α)) (zetaW p P α) (Polynomial.map φ g) := by
            rfl
      rw [hze]
      have hνe := Polynomial.hom_eval₂ (Polynomial.map φ g)
        (algebraMap (QpAdic p) (Wk p P α)) ν.toRingHom (zetaW p P α)
      -- ν (eval₂ algQ W zetaW (map φ g)) = eval₂ (ν∘algQ) (ν zetaW) (map φ g):
      rw [hνe]
      -- ν∘algQ = algQ→kpAdic (scalar tower, rfl); ν zetaW = (teich:kpAdic):
      have hcomp : (ν.toRingHom).comp (algebraMap (QpAdic p) (Wk p P α)) =
          algebraMap (QpAdic p) (kpAdic p P) := by
        apply RingHom.ext; intro r; rfl
      have hx : ν.toRingHom (zetaW p P α) = ((teich p P α : kpInt p P) : kpAdic p P) := by rfl
      rw [hcomp]
      rw [hx]
      -- eval₂ (algQK) (teich-value) (map φ g) = eval₂ (algQpIntK) (teich-value) g:
      have hmap := Polynomial.eval₂_map (R := QpInt p) (S := QpAdic p) (T := kpAdic p P)
        (f := φ) (g := algebraMap (QpAdic p) (kpAdic p P))
        (x := ((teich p P α : kpInt p P) : kpAdic p P)) (p := g)
      -- eval₂ (algQK) x (map φ g) = eval₂ (algQK∘φ) x g:
      rw [hmap]
      -- algQK∘φ = algebraMap (QpInt p)(kpAdic p P): then = value of teichMinpolyInt_eval_zero:
      have hcomp2 : (algebraMap (QpAdic p) (kpAdic p P)).comp φ =
          algebraMap (QpInt p) (kpAdic p P) := by
        apply RingHom.ext; intro r; rfl
      rw [hcomp2]
      -- eval₂ (alg QpInt kpAdic) (teich-value) g = 0: via the kpInt-zero pushed:
      have hz0 := teichMinpolyInt_eval_zero p P hα  -- eval₂ (algQpInt kpInt) (teich) g = 0 : kpInt
      have hcomp23 : (algebraMap (kpInt p P) (kpAdic p P)).comp
          (algebraMap (QpInt p) (kpInt p P)) = algebraMap (QpInt p) (kpAdic p P) := by
        apply RingHom.ext
        intro r
        rfl
      have hz1 : Polynomial.eval₂ (algebraMap (QpInt p) (kpAdic p P))
          ((teich p P α : kpInt p P) : kpAdic p P) g = 0 := by
        have hp := Polynomial.hom_eval₂ g (algebraMap (QpInt p) (kpInt p P))
          (algebraMap (kpInt p P) (kpAdic p P)) (teich p P α)
        have hl0 : (algebraMap (kpInt p P) (kpAdic p P))
            (Polynomial.eval₂ (algebraMap (QpInt p) (kpInt p P)) (teich p P α) g) = 0 := by
          rw [hz0]
          simp
        have hr0 : Polynomial.eval₂ ((algebraMap (kpInt p P) (kpAdic p P)).comp
            (algebraMap (QpInt p) (kpInt p P))) (algebraMap (kpInt p P) (kpAdic p P) (teich p P α)) g = 0 := by
          rw [← hp]
          exact hl0
        rw [hcomp23] at hr0
        exact hr0
      exact hz1
    -- ν is injective (subtype value):
    have hνinj : Function.Injective ν := by
      intro a b hab
      apply Subtype.ext
      exact hab
    exact hνinj (by simpa using hν0)
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmon).symm

/-- **Trace of the Teichmüller generator (first lemma of the residue-trace
reduction)**: `Tr_{W/ℚ_p}(ζ) = -(nextCoeff g)` where `g` is the ℤ_[p]-minimal
polynomial of ζ — so the trace is an integral (ℤ_[p]) element whose mod-p
reduction will be computable from `ḡ`. -/
theorem tr_zeta_int (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0) :
    Algebra.trace (QpAdic p) (Wk p P α) (zetaW p P α)
      = -((teichMinpolyInt p P α).nextCoeff : QpAdic p) := by
  classical
  have hfin : Module.Finite (QpAdic p) (Wk p P α) := moduleFinite_QpAdic_Wk p P hα
  haveI := hfin
  have ht : Algebra.trace (QpAdic p) (Wk p P α) (wPowerBasis p P α hα).gen
      = -((minpoly (QpAdic p) (wPowerBasis p P α hα).gen).nextCoeff) :=
    PowerBasis.trace_gen_eq_nextCoeff_minpoly (wPowerBasis p P α hα)
  have hg : (wPowerBasis p P α hα).gen = zetaW p P α := wPowerBasis_gen p P α hα
  rw [hg] at ht
  calc
    Algebra.trace (QpAdic p) (Wk p P α) (zetaW p P α)
        = -((minpoly (QpAdic p) (zetaW p P α)).nextCoeff) := ht
    _ = -(((teichMinpolyInt p P α).nextCoeff : QpAdic p)) := by
          have hmm := minpoly_zetaW_eq p P α hα
          have hinj : Function.Injective (algebraMap (QpInt p) (QpAdic p)) :=
            IsFractionRing.injective (QpInt p) (QpAdic p)
          have hnc := Polynomial.nextCoeff_map hinj (teichMinpolyInt p P α)
          rw [hmm]
          rw [hnc]
          rfl

end
end Submission.Vdw.LocalField
