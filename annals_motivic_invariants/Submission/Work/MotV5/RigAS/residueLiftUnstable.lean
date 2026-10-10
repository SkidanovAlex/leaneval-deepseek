import Mathlib
import Submission.Work.MotV5.RigAS.PlaceData
import Submission.Work.MotV5.Nodes.UEPR.bridge
import Submission.Work.MotV5.Nodes.UEPR.countL
import Submission.Work.MotV5.Nodes.UEPR.residue_trivial
import Submission.Work.MotV5.RigAS.residueAux
import Submission.Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable
import Submission.Work.MotV5.RigAS.GaloisTrue.galois
import Submission.Work.MotV5.RigAS.ValSubringEq.valSubringEq

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-!
# Residue lifting at a non-`σ'`-stable place

`Work.MotV5.RigAS.residueLiftUnstable` is the residue-lifting half of the local datum
`IsPlaceData` for the corrected twist field `F = asTwistFieldTrue D g τ σS` of
`Submission/Work/MotV5/RigAS/PlaceData.lean`, in the case where the prolongation `V` of the
valuation `v` of `F` to `L = asFieldL D g` is **not** stabilised by the twisted action
`σ' = twistSigmaL D g τ σS σ h`.

The mathematical content is the following.  `L/F` is a degree-`5` Galois extension with group
`⟨σ'⟩` (`Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable` plus
`Work.MotV5.RigAS.GaloisTrue.galois`), and `hV : IsPlaceExtension` says in particular that the
ramification index of `V/v` is `1` (`Γ(V) = v(F^×)`).  The prolongation `W := V ∘ σ'` is again a
prolongation of `v`, and `hunstable` says `W ≠ V`.  By the fundamental identity of ramification
theory (`Work.MotV5.Nodes.UEPR.countL`, applied at the centre `P` of `V`)

`#(primes over m_A) * (e * f) = [L : F] = 5`,

so `#(primes over m_A) ∣ 5`.  If it equalled `1` then — because the base valuation ring `A` has a
*unique* prime above it — the centres `P` of `V` and `P'` of `W` would coincide, hence (as
`V` and `W` have the same value group `v(F^×)` and the same restriction to `F`) the two valuations
would be equal, contradicting `hunstable`
(`Work.MotV5.RigAS.ValSubringEq.valSubringEq`).  Hence `#(primes over m_A) = 5`, `e * f = 1`, so
`f = P.inertiaDeg = 1` and the residue field of `V` is that of `v`.  Residue lifting is then
immediate (`Work.MotV5.Nodes.UEPR.residue_trivial`).

Note that `hunstable` is exactly the situation of the *blown up* pole place of the twist surface:
the five conjugates `V ∘ σ'^i` are the components of `π^{-1}(E_q)`, permuted transitively, and
none of them is `σ'`-stable.
-/

namespace Work.MotV5.RigAS

theorem residueLiftUnstable (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (htriv : Work.MotV.TrivOn 𝕜 v)
    (ht : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X))
    (V : Valuation ↥(Work.MotV5.asFieldL D g) (WithZero (Multiplicative ℤ)))
    (hV : Work.MotV5.RigAS.IsPlaceExtension D g τ σS σ h v V)
    (hunstable : ¬ ∀ x : ↥(Work.MotV5.asFieldL D g),
        V (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h x) = V x) :
    Work.MotV5.RigAS.IsResidueLift D g τ σS σ h v V := by
  classical
  -- ## 0. The relative algebra structure `F ⊆ L`, with `algebraMap = twistIncl`
  have hFL : Work.MotV5.asTwistFieldTrue D g τ σS ≤ Work.MotV5.asFieldL D g :=
    Work.MotV5.asTwistFieldTrue_le_asFieldL D g τ σS
  letI : Algebra ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) :=
    ((Subfield.inclusion hFL :
        ↥((Work.MotV5.asTwistFieldTrue D g τ σS).toSubfield) →+*
          ↥((Work.MotV5.asFieldL D g).toSubfield))).toAlgebra
  have halg : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x
        = Work.MotV5.RigAS.twistIncl D g τ σS x := fun _ => Subtype.ext rfl
  -- the twisted action fixes `F` pointwise
  have hσfix : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      Work.MotV5.RigAS.twistSigmaL D g τ σS σ h
          (Work.MotV5.RigAS.twistIncl D g τ σS x) = Work.MotV5.RigAS.twistIncl D g τ σS x := by
    intro x
    apply Subtype.ext
    show Work.MotV5.asTwistAction D τ σS (x : Work.MotV.Om D) = (x : Work.MotV.Om D)
    have hx := Work.MotV5.asTwistFieldTrue_le_asTwistFieldFix D g τ σS x.2
    rw [Work.MotV5.asTwistFieldFix, IntermediateField.mem_fixedField_iff] at hx
    have h3 := hx (Work.MotV5.asTwistAction D τ σS) (Subgroup.mem_zpowers _)
    simpa [AlgEquiv.smul_def] using h3
  -- ## 1. `L/F` is finite Galois of degree `5`
  haveI hgal : IsGalois ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) :=
    Work.MotV5.RigAS.GaloisTrue.galois 𝕜 D g τ σS σ h
  have hfr : (Work.MotV5.asTwistFieldTrue D g τ σS).relfinrank (Work.MotV5.asFieldL D g) = 5 :=
    (Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable 𝕜 D g τ σS
      h.h5L h.hneL h.hpres).1
  have hfin : Module.finrank ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      ↥(Work.MotV5.asFieldL D g) = 5 := by
    have h2 : Module.finrank ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
        ↥(IntermediateField.extendScalars hFL) = 5 := by
      rw [← IntermediateField.relfinrank_eq_finrank_of_le hFL]
      exact hfr
    exact h2
  haveI hFD : FiniteDimensional ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      ↥(Work.MotV5.asFieldL D g) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; norm_num)
  -- ## 2. `v` is nontrivial (it has a pole)
  have hvnt : v.IsNontrivial :=
    Valuation.IsNontrivial_iff_exists_one_lt.mpr ⟨_, ht⟩
  -- ## 3. The second prolongation `W = V ∘ σ'`
  set W : Valuation ↥(Work.MotV5.asFieldL D g) (WithZero (Multiplicative ℤ)) :=
    Valuation.comap (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h :
      ↥(Work.MotV5.asFieldL D g) →+* ↥(Work.MotV5.asFieldL D g)) V with hWdef
  have hWext : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      W (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x)
        = v x := by
    intro x
    rw [hWdef, Valuation.comap_apply, halg x]
    exact (congrArg V (hσfix x)).trans (hV.1 x)
  have hWne : W ≠ V := by
    intro hWV
    apply hunstable
    intro x
    calc V (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h x) = W x := rfl
      _ = V x := by rw [hWV]
  -- ## 4. The integral closure of the base valuation ring and the two centres
  haveI hBfr : IsFractionRing
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))
      ↥(Work.MotV5.asFieldL D g) :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(v.valuationSubring)
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) _
  haveI hBfin : Module.Finite ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)) :=
    IsIntegralClosure.finite ↥(v.valuationSubring)
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) _
  have hsubV : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x) ≤ 1
        ↔ v x ≤ 1 := by
    intro x; rw [halg x, hV.1 x]
  have hsubW : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      W (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x) ≤ 1
        ↔ v x ≤ 1 := by
    intro x; rw [hWext x]
  obtain ⟨P, hPprime, hPlies, hPc, hbridge⟩ :=
    Work.MotV5.Nodes.UEPR.bridge v hvnt V hsubV
  obtain ⟨P', hP'prime, hP'lies, hP'c, hbridge'⟩ :=
    Work.MotV5.Nodes.UEPR.bridge v hvnt W hsubW
  -- ## 5. The two centres are distinct
  have hVext : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x) = v x :=
    fun x => by rw [halg x]; exact hV.1 x
  have hVΓ : ∀ x : ↥(Work.MotV5.asFieldL D g), x ≠ 0 →
      ∃ y : ↥(Work.MotV5.asTwistFieldTrue D g τ σS), y ≠ 0 ∧
        V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) y)
          = V x := by
    intro x hx
    obtain ⟨y, hy, hyv⟩ := hV.2 x hx
    exact ⟨y, hy, by rw [halg y]; exact hyv⟩
  have hPne : P ≠ P' := by
    intro hPP
    have hring : V.valuationSubring = W.valuationSubring := by
      apply ValuationSubring.toSubring_injective
      subst hPP
      rw [hbridge, hbridge']
    have hVW : V = W :=
      Work.MotV5.RigAS.ValSubringEq.valSubringEq v V W hVext hWext hVΓ hring
    exact hWne hVW.symm
  -- ## 6. Counting: `#(primes over m_A) = 5`, hence `e * f = 1` and `f = 1`
  haveI := hPprime
  haveI := hPlies
  have hPmem : P ∈ (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)) :=
    ⟨hPprime, hPlies⟩
  have hP'mem : P' ∈ (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)) :=
    ⟨hP'prime, hP'lies⟩
  have hcount : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
        ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard
      * (P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring)) = 5 := by
    rw [Work.MotV5.Nodes.UEPR.countL v hvnt P, hfin]
  have hNne1 : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard ≠ 1 := by
    intro h1
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp h1
    have hPQ : P = Q := by
      have hmem : P ∈ ({Q} : Set (Ideal
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)))) := hQ ▸ hPmem
      simpa using hmem
    have hP'Q : P' = Q := by
      have hmem : P' ∈ ({Q} : Set (Ideal
          ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g)))) := hQ ▸ hP'mem
      simpa using hmem
    exact hPne (hPQ.trans hP'Q.symm)
  have hN5 : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard = 5 := by
    have hNdiv : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
        ↥(integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g))).ncard ∣ 5 :=
      ⟨_, hcount.symm⟩
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ hNdiv with h | h
    · exact absurd h hNne1
    · exact h
  have hef : P.ramificationIdx ↥(v.valuationSubring)
      * P.inertiaDeg ↥(v.valuationSubring) = 1 := by
    have h := hcount
    rw [hN5] at h
    exact Nat.mul_left_cancel (n := 5) (by norm_num) (by simpa using h)
  have hf : P.inertiaDeg ↥(v.valuationSubring) = 1 :=
    Nat.eq_one_of_mul_eq_one_left hef
  -- ## 7. Residue lifting
  have hres := Work.MotV5.Nodes.UEPR.residue_trivial v hvnt V hsubV P hPc hbridge hf
  intro z hz hz2
  obtain ⟨c, hc⟩ := hres z hz
  refine ⟨c, ?_⟩
  rw [← halg c]
  have h1 : V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) c - z)
      = V (z - algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) c) := by
    rw [show algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) c - z
        = -(z - algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
            ↥(Work.MotV5.asFieldL D g) c) by ring,
      Valuation.map_neg]
  rw [h1]
  exact hc.2

end Work.MotV5.RigAS
