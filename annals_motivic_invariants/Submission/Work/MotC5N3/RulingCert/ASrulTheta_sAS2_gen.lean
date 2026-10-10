import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotC5N3.ThetaT.Defs
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRul.sAS2_ruling_mem
import Submission.Work.Reflect.PolyId

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.MotC5N3.RulingCert
noncomputable section

open MvPolynomial

/-!
`A := ASrulA a b g = K[X₀,X₁,X₂] ⧸ √(ZIAS a b g)`, `ε := ASrulEpsA a b g`, and
`θ := ASrulTheta a b g hDZ : K[X₀,X₁,X₂] →ₐ[K] A[T][1/ε]` the ε-normalised AS ruling presentation.
CLAIM: `θ (sAS2 a b g) = 0`.

ROUTE.  Let `R = A[T]`, `L = Frac R`, `x i` the image of `X i`, and
`z k = T · (image of kbRv k) + (image of kbRw k)` the generic point of the ruling line.  Then
`z 4 = image of ε` (so `θ (X j) = z (j+1) / z 4`, using `kbRw 4 = ε`, `kbRv 4 = 0`), and `sAS2`
vanishes on the ruling line over every base point of `V(ZIAS)` with `X 2 ≠ 0`
(`Work.MotAS.ASRul.sAS2_ruling_mem`, PROVED); the generic point qualifies because
`ε = (a+2b)²(2a−b)·(image of X 2)² ≠ 0` (`hε`, `b ≠ 2a`).  Transport along the injective
localisation `R → L`.

The proof is split into private lemmas so that each gets its own heartbeat budget.  The generic
point and the ruling parameter are passed as *arguments* of the private lemmas (rather than being
written as `algebraMap (FractionRing …)` expressions), because instance search for those is only
available inside the proofs.
-/

section Helpers

variable {K : Type} [Field K] [CharP K 5] (a b g : K)

local notation "mk₀" => Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
local notation "R₀" => Polynomial (Work.MotC5N3.ASrulA a b g)
local notation "K₀" => FractionRing (Polynomial (Work.MotC5N3.ASrulA a b g))
local notation "S₀" => Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))
local notation "gpA" => algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 0))
local notation "gpB" => algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 1))
local notation "gpC" => algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 2))

/-- The bridge `aeval (x₀,x₁,x₂) = algebraMap A K₀ ∘ mk₀` at the generic point. -/
private lemma genAeval [hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)] :
    ∀ p : MvPolynomial (Fin 3) K,
      MvPolynomial.aeval ![gpA, gpB, gpC] p
        = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ p) := by
  let R : Type := Polynomial (Work.MotC5N3.ASrulA a b g)
  let K' : Type := FractionRing R
  letI : IsDomain R := inferInstance
  letI : Algebra R K' := inferInstance
  letI : Algebra (Work.MotC5N3.ASrulA a b g) K' := inferInstance
  letI : Algebra K K' := inferInstance
  let u : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 0))
  let v : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 1))
  let w : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 2))
  have hpt_eq : (MvPolynomial.aeval ![u, v, w] : MvPolynomial (Fin 3) K →ₐ[K] K')
      = (IsScalarTower.toAlgHom K (Work.MotC5N3.ASrulA a b g) K').comp
          (Ideal.Quotient.mkₐ K (Ideal.radical (Work.MotAS.ZIAS a b g))) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        u, v, w, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Fin.isValue,
        Fin.reduceFinMk] <;> rfl
  exact fun p => congrArg (fun f => f p) hpt_eq

/-- The pointwise certificate at the generic point of the residual curve. -/
private lemma genCert [hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)]
    (hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (h2ab : b ≠ 2 * a) (hg : g ≠ 0)
    (u v w t : K₀)
    (hu : u = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 0)))
    (hv : v = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 1)))
    (hwv : w = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 2))) :
    MvPolynomial.eval (Work.MotAS.ASRul.srcRulPt (algebraMap K K₀ a) (algebraMap K K₀ b)
        (algebraMap K K₀ g) u v w t)
      (Work.MotAS.sAS2 (algebraMap K K₀ a) (algebraMap K K₀ b) (algebraMap K K₀ g)) = 0 := by
  rw [hu, hv, hwv]
  letI : CommSemiring (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : Semiring (Work.MotC5N3.ASrulA a b g) :=
    (inferInstance : CommSemiring (Work.MotC5N3.ASrulA a b g)).toSemiring
  let R : Type := Polynomial (Work.MotC5N3.ASrulA a b g)
  let εR : R := Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)
  let K' : Type := FractionRing R
  letI : IsDomain R := inferInstance
  letI : Algebra R K' := inferInstance
  haveI hIF : IsFractionRing R K' := Localization.isLocalization
  letI : Algebra (Work.MotC5N3.ASrulA a b g) K' := inferInstance
  letI : Algebra K K' := inferInstance
  have hRK' : Function.Injective (algebraMap R K') := IsFractionRing.injective R K'
  have hεR : εR ≠ 0 := Polynomial.C_ne_zero.mpr hε
  have hKK' : Function.Injective (algebraMap K K') := by
    intro x y hxy
    by_cases h : x - y = 0
    · exact sub_eq_zero.mp h
    · exfalso
      have h1 : algebraMap K K' (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h2 : algebraMap K K' ((x - y) * (x - y)⁻¹) = 1 := by
        rw [mul_inv_cancel₀ h, map_one]
      rw [map_mul, h1, zero_mul] at h2
      exact one_ne_zero h2.symm
  have ha' : algebraMap K K' a ≠ 0 := fun h0 => ha (hKK' (h0.trans (map_zero _).symm))
  have hb' : algebraMap K K' b ≠ 0 := fun h0 => hb (hKK' (h0.trans (map_zero _).symm))
  have hg' : algebraMap K K' g ≠ 0 := fun h0 => hg (hKK' (h0.trans (map_zero _).symm))
  have h2ab' : algebraMap K K' b ≠ 2 * algebraMap K K' a := by
    intro h0
    apply h2ab
    apply hKK'
    rw [map_mul, map_ofNat, h0]
  have hCA : Function.Injective (fun x : Work.MotC5N3.ASrulA a b g => (Polynomial.C x : R)) :=
    fun x y hxy => by
      have h := congrArg (fun p : R => p.coeff 0) hxy
      simpa using h
  have hAK' : Function.Injective (algebraMap (Work.MotC5N3.ASrulA a b g) K') := by
    intro x y hxy
    have h1 : algebraMap R K' (Polynomial.C x) = algebraMap R K' (Polynomial.C y) := by
      rw [← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (Work.MotC5N3.ASrulA a b g) R K']
      exact hxy
    exact hCA (hRK' h1)
  let u' : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 0))
  let v' : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 1))
  let w' : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 2))
  have haeval : ∀ p : MvPolynomial (Fin 3) K,
      MvPolynomial.aeval ![u', v', w'] p = algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ p) :=
    fun p => genAeval a b g p
  have hw' : w' ≠ 0 := by
    intro hw0
    have hX2 : mk₀ (MvPolynomial.X 2) = 0 := by
      apply hAK'
      rw [map_zero]
      exact hw0
    apply hε
    have hzero : mk₀ (Work.MotAS.ASRul.kbRw a b g 4) = 0 := by
      rw [Work.MotAS.ASRul_kbRw_four]
      simp only [map_mul, map_pow]
      rw [hX2]
      refl_ring1
    exact hzero
  have hbase : ∀ j : Fin 5, MvPolynomial.eval ![u', v', w']
      (Work.MotAS.zcubAS (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g) j) = 0 := by
    intro j
    rw [← Work.MotC5N3.ThetaT.map_zcubAST (algebraMap K K') a b g j]
    rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    rw [haeval]
    rw [show mk₀ (Work.MotAS.zcubAS a b g j) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical (Ideal.subset_span ⟨j, rfl⟩))]
    rw [map_zero]
  haveI : CharP K' 5 := charP_of_injective_ringHom hKK' 5
  exact Work.MotAS.ASRul.sAS2_ruling_mem (K := K')
    (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g) ha' hb' h2ab' hg'
    u' v' w' t hw' hbase

/-- The point identity: `m ∘ θ` at the generators is the chart point of the generic ruling line. -/
private lemma pointId [hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)]
    (φ : R₀ →+* K₀) (m : S₀ →+* K₀)
    (hφC : ∀ x : Work.MotC5N3.ASrulA a b g,
      φ (Polynomial.C x) = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ x)
    (hmlift : ∀ (x : R₀) (y : Submonoid.powers (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))),
      m (IsLocalization.mk' S₀ x y) = φ x / φ (↑y : R₀))
    (u v w t : K₀)
    (hu : u = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 0)))
    (hv : v = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 1)))
    (hwv : w = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ (mk₀ (MvPolynomial.X 2)))
    (ht : t = φ Polynomial.X) :
    (fun j : Fin 3 => m (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)))
      = Work.MotAS.ASRul.srcRulPt (algebraMap K K₀ a) (algebraMap K K₀ b)
          (algebraMap K K₀ g) u v w t := by
  let R : Type := Polynomial (Work.MotC5N3.ASrulA a b g)
  let εR : R := Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)
  let S : Type := Localization.Away εR
  let K' : Type := FractionRing R
  letI : IsDomain R := inferInstance
  letI : Algebra R S := inferInstance
  letI : Algebra R K' := inferInstance
  letI : Algebra (Work.MotC5N3.ASrulA a b g) K' := inferInstance
  letI : Algebra K K' := inferInstance
  let u' : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 0))
  let v' : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 1))
  let w' : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ (MvPolynomial.X 2))
  have haeval : ∀ p : MvPolynomial (Fin 3) K,
      MvPolynomial.aeval ![u', v', w'] p = algebraMap (Work.MotC5N3.ASrulA a b g) K' (mk₀ p) :=
    fun p => genAeval a b g p
  let Q : Fin 3 → R := fun j =>
    Polynomial.C (mk₀ (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
      + Polynomial.C (mk₀ (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))
  let W : Fin 5 → K' := fun k => algebraMap (Work.MotC5N3.ASrulA a b g) K'
    (mk₀ (Work.MotAS.ASRul.kbRv a b g k))
  let V : Fin 5 → K' := fun k => algebraMap (Work.MotC5N3.ASrulA a b g) K'
    (mk₀ (Work.MotAS.ASRul.kbRw a b g k))
  have hθX : ∀ j : Fin 3, Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)
      = IsLocalization.mk' S (Q j) ⟨εR, Submonoid.mem_powers _⟩ :=
    fun j => MvPolynomial.aeval_X (fun j : Fin 3 =>
      IsLocalization.mk' S (Q j) ⟨εR, Submonoid.mem_powers _⟩) j
  have hmk : ∀ j : Fin 3, m (IsLocalization.mk' S (Q j) ⟨εR, Submonoid.mem_powers _⟩)
      = φ (Q j) / φ εR :=
    fun j => hmlift (Q j) ⟨εR, Submonoid.mem_powers _⟩
  have hQ : ∀ j : Fin 3, φ (Q j) = t * W (Work.MotAS.asCh3 j) + V (Work.MotAS.asCh3 j) := by
    intro j
    show φ (Polynomial.C (mk₀ (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
            + Polynomial.C (mk₀ (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j))))
        = t * algebraMap (Work.MotC5N3.ASrulA a b g) K'
              (mk₀ (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j)))
          + algebraMap (Work.MotC5N3.ASrulA a b g) K'
              (mk₀ (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))
    rw [map_add, map_mul, hφC, hφC, ← ht]
    refl_ring1
  have hεV : φ εR = V 4 :=
    hφC (Work.MotC5N3.ASrulEpsA a b g)
  have hWT : ∀ k : Fin 5, W k = MvPolynomial.eval ![u', v', w']
      (Work.MotAS.ASRul.kbRv (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g) k) := by
    intro k
    rw [← Work.MotC5N3.ThetaT.map_kbRvT (algebraMap K K') a b g k, MvPolynomial.eval_map,
      ← MvPolynomial.aeval_def, haeval]
  have hVT : ∀ k : Fin 5, V k = MvPolynomial.eval ![u', v', w']
      (Work.MotAS.ASRul.kbRw (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g) k) := by
    intro k
    rw [← Work.MotC5N3.ThetaT.map_kbRwT (algebraMap K K') a b g k, MvPolynomial.eval_map,
      ← MvPolynomial.aeval_def, haeval]
  have hpoint : (fun j : Fin 3 => m (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)))
      = (fun j : Fin 3 => (t * W (Work.MotAS.asCh3 j) + V (Work.MotAS.asCh3 j)) / V 4) := by
    funext j
    rw [hθX j, hmk j, hQ j, hεV]
  have hxsrc : (fun j : Fin 3 => (t * W (Work.MotAS.asCh3 j) + V (Work.MotAS.asCh3 j)) / V 4)
      = Work.MotAS.ASRul.srcRulPt (algebraMap K K' a) (algebraMap K K' b)
          (algebraMap K K' g) u' v' w' t := by
    funext j
    have hxval : (t * W (Work.MotAS.asCh3 j) + V (Work.MotAS.asCh3 j)) / V 4
        = (t * MvPolynomial.eval ![u', v', w']
              (Work.MotAS.ASRul.kbRv (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g)
                (Work.MotAS.asCh3 j))
            + MvPolynomial.eval ![u', v', w']
              (Work.MotAS.ASRul.kbRw (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g)
                (Work.MotAS.asCh3 j)))
            / MvPolynomial.eval ![u', v', w']
              (Work.MotAS.ASRul.kbRw (algebraMap K K' a) (algebraMap K K' b)
                (algebraMap K K' g) 4) := by
      rw [hWT (Work.MotAS.asCh3 j), hVT (Work.MotAS.asCh3 j), hVT 4]
    rw [hxval,
      congrFun (Work.MotAS.ASRul.eval_kbRv (algebraMap K K' a) (algebraMap K K' b)
        (algebraMap K K' g) u' v' w') (Work.MotAS.asCh3 j),
      congrFun (Work.MotAS.ASRul.eval_kbRw (algebraMap K K' a) (algebraMap K K' b)
        (algebraMap K K' g) u' v' w') (Work.MotAS.asCh3 j),
      congrFun (Work.MotAS.ASRul.eval_kbRw (algebraMap K K' a) (algebraMap K K' b)
        (algebraMap K K' g) u' v' w') 4]
    simp only [Work.MotAS.ASRul.srcRulPt]
    fin_cases j <;>
      simp only [Work.MotAS.ASRul.rvEv, Work.MotAS.ASRul.rwEv, Work.MotAS.ASRul.srcRvEv,
        Work.MotAS.ASRul.srcRwEv, Work.MotAS.asCh3, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons, Matrix.of_apply, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one] <;> rfl
  rw [hu, hv, hwv]
  exact hpoint.trans hxsrc

/-- The localisation map `m`, the ring hom `φ`, and the ruling parameter `t`. -/
private lemma mkData [hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)]
    (hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0) :
    ∃ (m : S₀ →+* K₀) (φ : R₀ →+* K₀) (t : K₀),
      Function.Injective m
      ∧ (∀ x : Work.MotC5N3.ASrulA a b g,
          φ (Polynomial.C x) = algebraMap (Work.MotC5N3.ASrulA a b g) K₀ x)
      ∧ (∀ c : K, m (algebraMap K S₀ c) = algebraMap K K₀ c)
      ∧ (∀ (x : R₀) (y : Submonoid.powers (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))),
          m (IsLocalization.mk' S₀ x y) = φ x / φ (↑y : R₀))
      ∧ (t = φ Polynomial.X) := by
  letI : CommSemiring (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : Semiring (Work.MotC5N3.ASrulA a b g) :=
    (inferInstance : CommSemiring (Work.MotC5N3.ASrulA a b g)).toSemiring
  let R : Type := Polynomial (Work.MotC5N3.ASrulA a b g)
  let εR : R := Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)
  let S : Type := Localization.Away εR
  let K' : Type := FractionRing R
  letI : IsDomain R := inferInstance
  letI : Algebra R S := inferInstance
  letI : Algebra R K' := inferInstance
  haveI hIF : IsFractionRing R K' := Localization.isLocalization
  letI : Algebra (Work.MotC5N3.ASrulA a b g) K' := inferInstance
  letI : Algebra K S := inferInstance
  letI : Algebra K K' := inferInstance
  have hRK' : Function.Injective (algebraMap R K') := IsFractionRing.injective R K'
  have hεR : εR ≠ 0 := Polynomial.C_ne_zero.mpr hε
  have hεK' : algebraMap R K' εR ≠ 0 := by
    intro h0
    exact hεR (hRK' (h0.trans (map_zero _).symm))
  have hKK' : Function.Injective (algebraMap K K') := by
    intro x y hxy
    by_cases h : x - y = 0
    · exact sub_eq_zero.mp h
    · exfalso
      have h1 : algebraMap K K' (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h2 : algebraMap K K' ((x - y) * (x - y)⁻¹) = 1 := by
        rw [mul_inv_cancel₀ h, map_one]
      rw [map_mul, h1, zero_mul] at h2
      exact one_ne_zero h2.symm
  have hunit : ∀ y : Submonoid.powers εR, IsUnit (algebraMap R K' (↑y : R)) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    rw [← hn, map_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hεK')
  let m : S →+* K' := IsLocalization.lift (M := Submonoid.powers εR)
    (g := algebraMap R K') hunit
  have hmK : ∀ c : K, m (algebraMap K S c) = algebraMap K K' c := by
    intro c
    have h1 : algebraMap K S c = algebraMap R S (algebraMap (Work.MotC5N3.ASrulA a b g) R
        (algebraMap K (Work.MotC5N3.ASrulA a b g) c)) := by
      rw [IsScalarTower.algebraMap_apply K R S,
        IsScalarTower.algebraMap_apply K (Work.MotC5N3.ASrulA a b g) R]
    have h2 : algebraMap K K' c = algebraMap (Work.MotC5N3.ASrulA a b g) K'
        (algebraMap K (Work.MotC5N3.ASrulA a b g) c) := by
      rw [IsScalarTower.algebraMap_apply K (Work.MotC5N3.ASrulA a b g) K']
    rw [h1, h2, IsLocalization.lift_eq hunit,
      ← IsScalarTower.algebraMap_apply (Work.MotC5N3.ASrulA a b g) R K']
  have hφC : ∀ x : Work.MotC5N3.ASrulA a b g,
      algebraMap R K' (Polynomial.C x) = algebraMap (Work.MotC5N3.ASrulA a b g) K' x := by
    intro x
    rw [← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply (Work.MotC5N3.ASrulA a b g) R K']
  have hmlift : ∀ (x : R) (y : Submonoid.powers εR),
      m (IsLocalization.mk' S x y) = algebraMap R K' x / algebraMap R K' (↑y : R) := by
    intro x y
    have hy : algebraMap R K' (↑y : R) ≠ 0 := by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact pow_ne_zero n hεK'
    refine (IsLocalization.lift_mk'_spec (M := Submonoid.powers εR) (g := algebraMap R K')
      hunit x (algebraMap R K' x / algebraMap R K' (↑y : R)) y).mpr ?_
    rw [mul_comm (algebraMap R K' (↑y : R))]
    exact (div_mul_cancel₀ _ hy).symm
  have hm_inj : Function.Injective m := by
    intro x y hxy
    have hker : m (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨p, hp⟩ := IsLocalization.surj (Submonoid.powers εR) (x - y)
    have h1 : algebraMap R K' p.1 = 0 := by
      have h2 := congrArg m hp
      rw [map_mul, hker, zero_mul, IsLocalization.lift_eq hunit] at h2
      exact h2.symm
    have hr : p.1 = 0 := hRK' (by rw [h1, map_zero])
    have h3 : (x - y) * algebraMap R S (↑p.2 : R) = 0 := by rw [hp, hr, map_zero]
    rcases (IsLocalization.map_units S p.2) with ⟨wu, hwu⟩
    rw [← hwu] at h3
    have h4 : x - y = 0 := by
      have h5 := congrArg (fun z => z * (↑(wu⁻¹) : S)) h3
      simpa [mul_assoc] using h5
    exact sub_eq_zero.mp h4
  exact ⟨m, algebraMap R K', algebraMap R K' Polynomial.X, hm_inj, hφC, hmK, hmlift, rfl⟩

/-- Final assembly of the certificate, split off so that it gets its own heartbeat budget. -/
private lemma tailAssembly [hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)]
    (u v w t : K₀) (m : S₀ →+* K₀) (hm_inj : Function.Injective m)
    (hmK : ∀ c : K, m (algebraMap K S₀ c) = algebraMap K K₀ c)
    (hptsrc : (fun j : Fin 3 => m (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)))
      = Work.MotAS.ASRul.srcRulPt (algebraMap K K₀ a) (algebraMap K K₀ b)
          (algebraMap K K₀ g) u v w t)
    (hbc : MvPolynomial.eval (Work.MotAS.ASRul.srcRulPt (algebraMap K K₀ a) (algebraMap K K₀ b)
          (algebraMap K K₀ g) u v w t)
          (Work.MotAS.sAS2 (algebraMap K K₀ a) (algebraMap K K₀ b) (algebraMap K K₀ g))
        = MvPolynomial.aeval (Work.MotAS.ASRul.srcRulPt (algebraMap K K₀ a) (algebraMap K K₀ b)
          (algebraMap K K₀ g) u v w t) (Work.MotAS.sAS2 a b g))
    (hcert : MvPolynomial.eval (Work.MotAS.ASRul.srcRulPt (algebraMap K K₀ a) (algebraMap K K₀ b)
          (algebraMap K K₀ g) u v w t)
          (Work.MotAS.sAS2 (algebraMap K K₀ a) (algebraMap K K₀ b) (algebraMap K K₀ g)) = 0)
    :
    Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.sAS2 a b g) = 0 := by
  let mAlg : S₀ →ₐ[K] K₀ := { m with commutes' := hmK }
  have hθaeval : Work.MotC5N3.ASrulTheta a b g hDZ
      = MvPolynomial.aeval (fun j : Fin 3 => Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)) :=
    MvPolynomial.aeval_unique _
  have hcompm : m (MvPolynomial.aeval
        (fun j : Fin 3 => Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j))
        (Work.MotAS.sAS2 a b g))
      = MvPolynomial.aeval (fun j : Fin 3 =>
          m (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j))) (Work.MotAS.sAS2 a b g) :=
    MvPolynomial.comp_aeval_apply (f := fun j : Fin 3 =>
      Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)) mAlg (Work.MotAS.sAS2 a b g)
  have hmain : m (Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.sAS2 a b g)) = 0 := by
    rw [hθaeval, hcompm]
    rw [hptsrc]
    rw [← hbc]
    exact hcert
  exact hm_inj (by rw [hmain, map_zero])

end Helpers

section Main

variable {K : Type} [Field K] [CharP K 5] (a b g : K)

/-- The certificate: `θ (sAS2 a b g) = 0`. -/
theorem ASrulTheta_sAS2_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)) (hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (h2ab : b ≠ 2 * a) (hg : g ≠ 0) :
    Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.sAS2 a b g) = 0 := by
  haveI hAdom : IsDomain (Work.MotC5N3.ASrulA a b g) := hDZ
  obtain ⟨m, φ, t, hm_inj, hφC, hmK, hmlift, ht⟩ := mkData a b g hε
  let R : Type := Polynomial (Work.MotC5N3.ASrulA a b g)
  let K' : Type := FractionRing R
  letI : IsDomain R := inferInstance
  letI : Algebra R K' := inferInstance
  letI : Algebra (Work.MotC5N3.ASrulA a b g) K' := inferInstance
  letI : Algebra K K' := inferInstance
  let u : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K'
    (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) (MvPolynomial.X 0))
  let v : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K'
    (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) (MvPolynomial.X 1))
  let w : K' := algebraMap (Work.MotC5N3.ASrulA a b g) K'
    (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) (MvPolynomial.X 2))
  let t' : K' := t
  have hbc : MvPolynomial.eval (Work.MotAS.ASRul.srcRulPt (algebraMap K K' a)
        (algebraMap K K' b) (algebraMap K K' g) u v w t')
        (Work.MotAS.sAS2 (algebraMap K K' a) (algebraMap K K' b) (algebraMap K K' g))
      = MvPolynomial.aeval (Work.MotAS.ASRul.srcRulPt (algebraMap K K' a)
        (algebraMap K K' b) (algebraMap K K' g) u v w t') (Work.MotAS.sAS2 a b g) := by
    rw [Work.MotC5N3.ThetaT.map_sAS2T (algebraMap K K') a b g, MvPolynomial.eval_map,
      MvPolynomial.aeval_def]
  refine tailAssembly a b g u v w t' m hm_inj hmK ?_ hbc
    (genCert a b g hε ha hb h2ab hg u v w t' rfl rfl rfl)
  exact pointId a b g φ m hφC hmlift u v w t' rfl rfl rfl ht

end Main

end

end Work.MotC5N3.RulingCert
