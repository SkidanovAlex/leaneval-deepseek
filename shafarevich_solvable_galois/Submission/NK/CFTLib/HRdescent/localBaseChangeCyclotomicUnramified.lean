import Mathlib
import Submission.NK.NUV2.ARL.HR.CyclotomicTransferAux
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSandwich
import Submission.NK.LocalReciprocity.NormGroupTower
import Submission.NK.KC.localBaseChangeInput_of_kc
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local base change at an unramified place (cyclotomic descent)

Let `K ⊆ L`, `K ⊆ M` be finite Galois extensions of number fields with `L/K` cyclic, let
`E = L·M` be their compositum, let `Q` be a place of `K` which is *unramified* in `M`, and let
`w | Q` be a place of `M` whose inertia degree `f(w|Q) = w.asIdeal.inertiaDeg 𝓞 K` is divisible by
`[L : K]`.

Under these hypotheses `localBaseChangeCyclotomicUnramified` produces a place `q | w` of `E` such
that the image in `M_wˣ` of every `x ∈ Kˣ` is a norm from `E_q`, i.e. lies in the local norm group
`N_{E_q/M_w}E_qˣ`.  This is Milne, *CFT*, III.3.6 (the local content of the Hasse-norm/cyclic
descent), in the form in which the cyclotomic-descent argument uses it.

## The proof

The statement of `NK.KC.localBaseChange_aux` is the same one with the *local* hypothesis
`hloc : [L_r : K_Q] ∣ [M_w : K_Q]` for every place `r | Q` of `L` in place of the *global* one
`hdvd : [L : K] ∣ f(w|Q)`.  The reduction `hdvd → hloc` is the global fundamental identity
`[L : K] = #{r | Q} · e · f` for the Galois extension `L/K`
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`) together with the local
fundamental identity `[L_r : K_Q] = e · f` at the place `r`
(`Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`):
since `e · f` divides `[L : K]` and hence `f(w|Q) = [M_w : K_Q]` (here `M/K` is unramified at
`Q`), the local degree at every `r | Q` divides `[M_w : K_Q]`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.HRdescent

/-- **The local degree divides the inertia degree.**  For a Galois extension `L/K` of number
fields and places `Q` of `K`, `w | Q` of `M` with `Q` unramified in `M`, the divisibility
`[L : K] ∣ f(w|Q)` of global degrees implies the local-degree divisibility
`[L_r : K_Q] ∣ [M_w : K_Q]` at *every* place `r | Q` of `L`.

Indeed `[L_r : K_Q] = e · f` with `e = e(r|Q)`, `f = f(r|Q)`, and the global fundamental identity
of Galois theory gives `[L : K] = #{r | Q} · e · f`, so `e · f ∣ [L : K] ∣ f(w|Q)`, while
`[M_w : K_Q] = e(w|Q) · f(w|Q) = f(w|Q)` because `Q` is unramified in `M`. -/
theorem localDegree_dvd_of_dvd_inertiaDeg {K L M : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1)
    (hdvd : Module.finrank K L ∣ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) :
    ∀ (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hr : r.asIdeal.LiesOver Q.asIdeal),
      Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣
        Module.finrank (Q.adicCompletion K) (w.adicCompletion M) := by
  intro r hr
  -- the local fundamental identity at `r | Q`: `[L_r : K_Q] = e · f`
  have hA : r.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
      r.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      Module.finrank (Q.adicCompletion K) (r.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q r hr
  -- the local fundamental identity at `w | Q`, together with unramifiedness: `[M_w : K_Q] = f(w|Q)`
  have hB : Module.finrank (Q.adicCompletion K) (w.adicCompletion M) =
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h :=
      Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q w hw
    have he : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
      rw [NK.KC.ramificationIdx_eq_ramificationIdxIn Q w hw, hunr]
    rw [he, one_mul] at h
    exact h.symm
  -- the global fundamental identity of Galois theory: `e · f ∣ [L : K]`
  have hglob : r.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
      r.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ∣ Module.finrank K L := by
    haveI : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) := inferInstance
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := NumberField.RingOfIntegers K) Q.asIdeal (NumberField.RingOfIntegers L) Gal(L/K)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal r.asIdeal Gal(L/K),
      Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal r.asIdeal Gal(L/K),
      IsGalois.card_aut_eq_finrank] at h
    exact ⟨(Q.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard,
      by rw [← h, mul_comm]⟩
  rw [← hA, hB]
  exact dvd_trans hglob hdvd

/-- **Local base change at an unramified place.**  With `E = L·M` the compositum of the Galois
extensions `L/K` (cyclic) and `M/K` over `K`, `Q` a place of `K` unramified in `M` and `w | Q` a
place of `M` whose inertia degree over `K` is divisible by `[L : K]`, there is a place `q | w` of
`E` such that for every `x ∈ Kˣ` the image of `x` in `M_wˣ` is a local norm from `E_q`. -/
theorem localBaseChangeCyclotomicUnramified {K L M E : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1)
    (hdvd : Module.finrank K L ∣ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) :
    ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
      (hq : q.asIdeal.LiesOver w.asIdeal),
      ∀ x : Kˣ, Units.map (algebraMap M (w.adicCompletion M)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
        (NK.GlobalCFT.Place.localNormFinite q w hq).range := by
  have hloc := localDegree_dvd_of_dvd_inertiaDeg (K := K) (L := L) (M := M) Q w hw hunr hdvd
  exact NK.KC.localBaseChange_aux (K := K) (L := L) (M := M) (E := E)
    hgen hcycL Q w hw hunr hloc

end NK.CFTLib.HRdescent
