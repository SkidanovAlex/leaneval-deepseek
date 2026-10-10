import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.KleinTwProjAS
import Submission.Work.MotAS.asMinv_mul_asM
import Submission.Work.MotAS.splitRuleEvalGen
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.asRulingEval` — the ruling line of the corrected AS chart maps back to its base point

The Crauder–Katz quadro-cubic link in the Artin–Schreier (characteristic `5`) Galois coordinates
(`Work.MotAS`, `MOTIVIC_KDATA_LEAD.md` §6) associates to a point `c` of the twisted Klein curve
(`kleinPAS a b g c = 0`) the *ruling line* `ℓ_c` of the target ruled surface, parametrised by
`asRuleQW a b g c t` (`Submission/Work/MotAS/SdualAS2Defs.lean`).  The inverse quadro-cubic map
`kleinRAS` is projectively constant on `ℓ_c` with value `c`:

  `kleinRAS (asRuleQW c t) i * c j = kleinRAS (asRuleQW c t) j * c i`.

## Route

The AS data are the images of the *split* Klein–Fisher data (`Work.MotK`) under the
Artin–Schreier coordinate change `x_i = Σ_j (w + i)^j y_j` (`asM w`), `z_k = Σ_j (w + 2k)^j ẑ_j`
(`asN w`), reduced with `w^5 = w + g`, `5 = 0`; the transports are proved in
`Work.MotAS.ASTransport` / `ASTransportR`:

* `kleinP a b (asM w · y) = asN w · kleinPAS a b g y`,
* `kleinR a b (asN w · z) = asM w · kleinRAS a b g z`.

So, inside a ring containing an element `w` with `w^5 = w + g`, the AS statement is equivalent to
its split counterpart with `ξ := asM w · c`, `η := asM w · u`:

* `kleinP a b ξ = 0` (transport of `hc`),
* the polar transports: `asN w · asPolarP(c,u) = kleinPolarP(ξ,η)`,
* the split ruling identity `kleinR a b (kleinPolarP a b ξ η) ∝ ξ` then gives
  `(asM w · kleinRAS z) ∝ (asM w · c)`,
* and since `asM w` is invertible (`asMinv w`, characteristic `5`), proportionality can be
  cancelled: `kleinRAS z ∝ c`.

The general statement over an arbitrary commutative ring follows by adjoining a formal root
`w := AdjoinRoot.root (X⁵ - X - C g)` and descending along the injective
`AdjoinRoot.of`, exactly as in `Work.MotAS.KleinTwProjAS`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-! ## §1  The direction of the ruling line, and linearity of the AS polar form -/

/-- The direction of the ruling line of the corrected AS chart at the curve point `c`:
`u = asTanQ(·,1) + t·asTanQ(·,2)`, so that `asRuleQW a b g c t = asPolarP a b g c u`. -/
def asRuleDir (a b : R) (c : Fin 5 → R) (t : R) : Fin 5 → R :=
  fun i => asTanQ a b c 1 i + t * asTanQ a b c 2 i

/-! The components of the AS Pfaffian tuple, in both the numeral and the proof-carrying index
form (`fin_cases` produces the latter). -/
theorem kleinPAS_zero (a b g : R) (y : Fin 5 → R) : kleinPAS a b g y 0 = kleinPAS0 a b g y := rfl
theorem kleinPAS_one (a b g : R) (y : Fin 5 → R) : kleinPAS a b g y 1 = kleinPAS1 a b g y := rfl
theorem kleinPAS_two (a b g : R) (y : Fin 5 → R) : kleinPAS a b g y 2 = kleinPAS2 a b g y := rfl
theorem kleinPAS_three (a b g : R) (y : Fin 5 → R) : kleinPAS a b g y 3 = kleinPAS3 a b g y := rfl
theorem kleinPAS_four (a b g : R) (y : Fin 5 → R) : kleinPAS a b g y 4 = kleinPAS4 a b g y := rfl
theorem kleinPAS_zero' (a b g : R) (y : Fin 5 → R) (h : 0 < 5) :
    kleinPAS a b g y ⟨0, h⟩ = kleinPAS0 a b g y := rfl
theorem kleinPAS_one' (a b g : R) (y : Fin 5 → R) (h : 1 < 5) :
    kleinPAS a b g y ⟨1, h⟩ = kleinPAS1 a b g y := rfl
theorem kleinPAS_two' (a b g : R) (y : Fin 5 → R) (h : 2 < 5) :
    kleinPAS a b g y ⟨2, h⟩ = kleinPAS2 a b g y := rfl
theorem kleinPAS_three' (a b g : R) (y : Fin 5 → R) (h : 3 < 5) :
    kleinPAS a b g y ⟨3, h⟩ = kleinPAS3 a b g y := rfl
theorem kleinPAS_four' (a b g : R) (y : Fin 5 → R) (h : 4 < 5) :
    kleinPAS a b g y ⟨4, h⟩ = kleinPAS4 a b g y := rfl

/-- **Linearity of the AS polar form in its second argument.** -/
theorem asPolarP_lin (a b g : R) (c u v : Fin 5 → R) (s t : R) :
    asPolarP a b g c (fun i => s * u i + t * v i)
      = fun i => s * asPolarP a b g c u i + t * asPolarP a b g c v i := by
  funext k
  fin_cases k <;>
    simp only [asPolarP, Pi.sub_apply, Pi.add_apply,
      kleinPAS_zero, kleinPAS_one, kleinPAS_two, kleinPAS_three, kleinPAS_four,
      kleinPAS_zero', kleinPAS_one', kleinPAS_two', kleinPAS_three', kleinPAS_four',
      kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4] <;>
    first | refl_ring1 | ring

/-- **The ruling point is the polar of the AS Pfaffian map in the ruling direction.** -/
theorem asRuleQW_eq_polar (a b g : R) (c : Fin 5 → R) (t : R) :
    asRuleQW a b g c t = asPolarP a b g c (asRuleDir a b c t) := by
  funext i
  have h := congrFun (asPolarP_lin a b g c (asTanQ a b c 1) (asTanQ a b c 2) (1 : R) t) i
  simp only [one_mul] at h
  simp only [asRuleQW, asRuleQA, asRuleQB, asRuleDir]
  exact h.symm

/-! ## §2  Transport of the polar form -/

/-- **The AS polar form is the transport of the split polar form.** -/
theorem asTransportPolar (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g)
    (c u : Fin 5 → R) :
    (asN w).mulVec (asPolarP a b g c u)
      = Work.MotK.kleinPolarP a b ((asM w).mulVec c) ((asM w).mulVec u) := by
  have hP : ∀ y : Fin 5 → R,
      (asN w).mulVec (kleinPAS a b g y) = Work.MotK.kleinP a b ((asM w).mulVec y) :=
    fun y => (asTransportP a b g w h5 hw y).symm
  have hpolar : asPolarP a b g c u
      = kleinPAS a b g (c + u) - kleinPAS a b g c - kleinPAS a b g u := by
    funext i
    simp only [asPolarP, Pi.sub_apply, Pi.add_apply]
  calc (asN w).mulVec (asPolarP a b g c u)
      = (asN w).mulVec (kleinPAS a b g (c + u) - kleinPAS a b g c - kleinPAS a b g u) := by
        rw [hpolar]
    _ = (asN w).mulVec (kleinPAS a b g (c + u)) - (asN w).mulVec (kleinPAS a b g c)
          - (asN w).mulVec (kleinPAS a b g u) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    _ = Work.MotK.kleinP a b ((asM w).mulVec (c + u))
          - Work.MotK.kleinP a b ((asM w).mulVec c) - Work.MotK.kleinP a b ((asM w).mulVec u) := by
        rw [hP, hP, hP]
    _ = Work.MotK.kleinP a b ((asM w).mulVec c + (asM w).mulVec u)
          - Work.MotK.kleinP a b ((asM w).mulVec c) - Work.MotK.kleinP a b ((asM w).mulVec u) := by
        rw [Matrix.mulVec_add]
    _ = Work.MotK.kleinPolarP a b ((asM w).mulVec c) ((asM w).mulVec u) := rfl

/-! ## §3  Cancellation of an invertible matrix in a proportionality -/

/-- **Proportionality is preserved (both ways) by an invertible linear map.**  If `N * M = 1` and
the images `M.mulVec X`, `M.mulVec c` of two vectors are proportional, then so are `X` and `c`.
This is the cancellation of the Vandermonde matrix `asM w` (with `N = asMinv w`) used below; it is
pure ring bookkeeping (no domain hypothesis is needed). -/
theorem mulVec_proportional_of_inverse' {R : Type*} [CommRing R]
    (M N : Matrix (Fin 5) (Fin 5) R) (hNM : N * M = 1) (X c : Fin 5 → R)
    (h : ∀ i j, M.mulVec X i * M.mulVec c j = M.mulVec X j * M.mulVec c i) :
    ∀ i j, X i * c j = X j * c i := by
  have hX : X = N.mulVec (M.mulVec X) := by
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  have hc : c = N.mulVec (M.mulVec c) := by
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  intro i j
  rw [hX, hc]
  have hrow : ∀ (A B : Fin 5 → R) (p q : Fin 5),
      (N.mulVec A) p * (N.mulVec B) q
        = ∑ k : Fin 5, ∑ l : Fin 5, (N p k * N q l) * (A k * B l) := by
    intro A B p q
    rw [show (N.mulVec A) p = ∑ k : Fin 5, N p k * A k from rfl,
      show (N.mulVec B) q = ∑ l : Fin 5, N q l * B l from rfl,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hrow (M.mulVec X) (M.mulVec c) i j, hrow (M.mulVec X) (M.mulVec c) j i]
  have step1 : (∑ k : Fin 5, ∑ l : Fin 5,
        (N i k * N j l) * ((M.mulVec X) k * (M.mulVec c) l))
      = ∑ k : Fin 5, ∑ l : Fin 5,
        (N i k * N j l) * ((M.mulVec X) l * (M.mulVec c) k) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [h k l]
  have step2 : (∑ k : Fin 5, ∑ l : Fin 5,
        (N j k * N i l) * ((M.mulVec X) k * (M.mulVec c) l))
      = ∑ k : Fin 5, ∑ l : Fin 5,
        (N i l * N j k) * ((M.mulVec X) k * (M.mulVec c) l) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    first | refl_ring1 | ring
  rw [step1, step2]
  conv_lhs => rw [Finset.sum_comm]

/-! ## §4  The ruling identity in a ring containing a root of `X⁵ - X - g` -/

/-- **The ruling identity, in a ring that contains a root `w` of `X⁵ - X - g`.** -/
theorem asRulingEval_of_root (h5 : (5 : R) = 0) (a b g w : R) (hw : w ^ 5 = w + g)
    (c : Fin 5 → R) (t : R)
    (hc : ∀ k : Fin 5, kleinPAS a b g c k = 0) (i j : Fin 5) :
    kleinRAS a b g (asRuleQW a b g c t) i * c j
      = kleinRAS a b g (asRuleQW a b g c t) j * c i := by
  rw [asRuleQW_eq_polar]
  -- the transported curve point `ξ = asM w · c` lies on the split Klein curve
  have hcur : ∀ k : Fin 5, Work.MotK.kleinP a b ((asM w).mulVec c) k = 0 := by
    intro k
    have hmulN : (asN w).mulVec (kleinPAS a b g c)
        = fun i => ∑ j, asN w i j * kleinPAS a b g c j := rfl
    have hzero : (asN w).mulVec (kleinPAS a b g c) = 0 := by
      rw [hmulN]
      funext i
      apply Finset.sum_eq_zero
      intro j _
      rw [hc j, mul_zero]
    rw [show (asM w).mulVec c = fun i => ∑ j, asM w i j * c j from rfl,
      congrFun (asTransportP a b g w h5 hw c) k, hzero]
    rfl
  -- the split ruling identity, transported
  have hkey : ∀ i j : Fin 5,
      (asM w).mulVec (kleinRAS a b g (asPolarP a b g c (asRuleDir a b c t))) i
          * ((asM w).mulVec c) j
        = (asM w).mulVec (kleinRAS a b g (asPolarP a b g c (asRuleDir a b c t))) j
          * ((asM w).mulVec c) i := by
    intro i j
    have hmulN : (asN w).mulVec (asPolarP a b g c (asRuleDir a b c t))
        = fun k => ∑ j, asN w k j * asPolarP a b g c (asRuleDir a b c t) j := rfl
    rw [← asTransportR a b g w h5 hw (asPolarP a b g c (asRuleDir a b c t)), ← hmulN,
      asTransportPolar a b g w h5 hw c (asRuleDir a b c t)]
    exact splitRuleEvalGen a b ((asM w).mulVec c) ((asM w).mulVec (asRuleDir a b c t)) hcur i j
  -- cancel the invertible Vandermonde matrix `asM w`
  exact mulVec_proportional_of_inverse' (asM w) (asMinv w) (asMinv_mul_asM h5 w)
    (kleinRAS a b g (asPolarP a b g c (asRuleDir a b c t))) c hkey i j

/-! ## §5  The general statement over a commutative ring -/

/-- **The ruling identity of the corrected AS chart over an arbitrary commutative ring.** -/
theorem asRulingEval_gen (h5 : (5 : R) = 0) (a b g : R) (t : R) (c : Fin 5 → R)
    (hc : ∀ k : Fin 5, kleinPAS a b g c k = 0) (i j : Fin 5) :
    kleinRAS a b g (asRuleQW a b g c t) i * c j
      = kleinRAS a b g (asRuleQW a b g c t) j * c i := by
  classical
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · haveI : Subsingleton R := hsub
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := hnt
    -- adjoin a formal root of the Artin–Schreier polynomial `X⁵ - X - g`
    set P : Polynomial R := Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g with hPdef
    have hPmonic : P.Monic := by rw [hPdef]; monicity!
    have hPndeg : P.natDegree = 5 := by rw [hPdef]; compute_degree!
    have hPdegpos : (0 : WithBot ℕ) < P.degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, hPndeg]
      norm_num
    have h5S : (5 : AdjoinRoot P) = 0 := by
      have h5R : ((5 : ℕ) : R) = 0 := by simpa using h5
      have h' : ((5 : ℕ) : AdjoinRoot P) = 0 := by
        rw [← map_natCast (AdjoinRoot.of P) 5, h5R, map_zero]
      simpa using h'
    have hwS : (AdjoinRoot.root P) ^ 5 = AdjoinRoot.root P + AdjoinRoot.of P g := by
      have h := AdjoinRoot.eval₂_root P
      rw [hPdef] at h
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      linear_combination (norm := first | refl_ring1 | ring1) h
    -- the transported hypothesis `kleinPAS (of ∘ c) = 0`
    have hcS : ∀ k : Fin 5, kleinPAS (AdjoinRoot.of P a) (AdjoinRoot.of P b)
        (AdjoinRoot.of P g) (fun i => AdjoinRoot.of P (c i)) k = 0 := by
      intro k
      rw [congrFun (map_kleinPAS (AdjoinRoot.of P) a b g c) k, hc k, map_zero]
    have hmain := asRulingEval_of_root (R := AdjoinRoot P) h5S (AdjoinRoot.of P a)
      (AdjoinRoot.of P b) (AdjoinRoot.of P g) (AdjoinRoot.root P) hwS
      (fun i => AdjoinRoot.of P (c i)) (AdjoinRoot.of P t) hcS i j
    -- rewrite the adjoined statement as the image of the statement over `R`
    have hmain' : AdjoinRoot.of P (kleinRAS a b g (asRuleQW a b g c t) i)
          * AdjoinRoot.of P (c j)
        = AdjoinRoot.of P (kleinRAS a b g (asRuleQW a b g c t) j)
          * AdjoinRoot.of P (c i) := by
      simpa only [map_kleinRAS (AdjoinRoot.of P) a b g (asRuleQW a b g c t),
        map_asRuleQW (AdjoinRoot.of P) a b g c t] using hmain
    -- descend along the injective embedding `R → AdjoinRoot P`
    refine AdjoinRoot.of.injective_of_monic_of_degree_pos hPmonic hPdegpos ?_
    rw [map_mul, map_mul]
    exact hmain'

/-! ## §6  The requested statement -/

theorem asRulingEval (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (h5 : (5 : A) = 0) (a b g : K) (t : A) (c : Fin 5 → A)
    (hc : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap K A a) (algebraMap K A b) (algebraMap K A g) c k = 0)
    (i j : Fin 5) :
    Work.MotAS.kleinRAS (algebraMap K A a) (algebraMap K A b) (algebraMap K A g)
        (Work.MotAS.asRuleQW (algebraMap K A a) (algebraMap K A b) (algebraMap K A g) c t) i * c j
      = Work.MotAS.kleinRAS (algebraMap K A a) (algebraMap K A b) (algebraMap K A g)
        (Work.MotAS.asRuleQW (algebraMap K A a) (algebraMap K A b) (algebraMap K A g) c t) j * c i :=
  asRulingEval_gen h5 (algebraMap K A a) (algebraMap K A b) (algebraMap K A g) t c hc i j

end Work.MotAS
