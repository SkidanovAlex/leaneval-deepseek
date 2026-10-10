import Mathlib.Tactic.Have
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum
open WithZeroTopology

noncomputable section

namespace Commons.RingTheory.Henselian

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- The `Q`-adic valuation on the completion of `K` is surjective onto `ℤᵐ⁰`. -/
lemma adicCompletion_valued_surjective {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (Valued.v : Q.adicCompletion K → ℤᵐ⁰) := by
  intro γ
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective (K := K) Q γ
  refine ⟨(y : Q.adicCompletion K), ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q y]
  exact hy

theorem valuation_completion_liesOver
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (x : Q.adicCompletion K) :
    Valued.v (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) =
      (Valued.v x) ^ Q.asIdeal.ramificationIdx' q.asIdeal := by
  let e : ℕ := Q.asIdeal.ramificationIdx' q.asIdeal
  let S : Set (Q.adicCompletion K) :=
    {z | Valued.v (adicCompletionMap Q q hq z) = (Valued.v z) ^ e}
  -- the map on the completion of `L` is continuous (surjective discrete valuation)
  have hcontL : Continuous (Valued.v : q.adicCompletion L → ℤᵐ⁰) := by
    exact Valued.continuous_valuation_of_surjective (adicCompletion_valued_surjective q)
  have hcontK : Continuous (Valued.v : Q.adicCompletion K → ℤᵐ⁰) := by
    exact Valued.continuous_valuation_of_surjective (adicCompletion_valued_surjective Q)
  have hcontf : Continuous (fun z : Q.adicCompletion K => Valued.v (adicCompletionMap Q q hq z)) :=
    hcontL.comp (adicCompletionMap_continuous Q q hq)
  have hcontg : Continuous (fun z : Q.adicCompletion K => (Valued.v z) ^ e) := by
    change Continuous ((Valued.v : Q.adicCompletion K → ℤᵐ⁰) ^ e)
    exact Continuous.pow hcontK e
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_eq hcontf hcontg
  -- equality on elements of the base field `K`
  have hS_base : ∀ y : K, (y : Q.adicCompletion K) ∈ S := by
    intro y
    haveI : q.asIdeal.LiesOver Q.asIdeal := hq
    have hvL : (Q.valuation K y) ^ Q.asIdeal.ramificationIdx' q.asIdeal =
        q.valuation L (algebraMap K L y) := by
      haveI := q.isPrime
      rw [Ideal.ramificationIdx'_eq_ramificationIdx Q.asIdeal q.asIdeal Q.ne_bot]
      exact valuation_liesOver (A := 𝓞 K) (B := 𝓞 L) L Q q y
    dsimp [S, e]
    calc
      Valued.v (adicCompletionMap Q q hq (y : Q.adicCompletion K))
          = Valued.v ((algebraMap K L y : q.adicCompletion L)) := by
              rw [adicCompletionMap_apply Q q hq y]
      _ = q.valuation L (algebraMap K L y) := by
              rw [valuedAdicCompletion_eq_valuation' q (algebraMap K L y)]
      _ = (Q.valuation K y) ^ Q.asIdeal.ramificationIdx' q.asIdeal := by
              rw [← hvL]
      _ = (Valued.v (y : Q.adicCompletion K)) ^ Q.asIdeal.ramificationIdx' q.asIdeal := by
              rw [← valuedAdicCompletion_eq_valuation' Q y]
  -- density of `K` in the completion
  have hdense : Dense (Set.range (fun y : K => (y : Q.adicCompletion K))) := by
    rw [show (fun y : K => (y : Q.adicCompletion K)) = (algebraMap K (Q.adicCompletion K)) by
      funext y; rfl]
    exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
  have hSsup : Set.range (fun y : K => (y : Q.adicCompletion K)) ⊆ S := by
    intro z hz
    rcases hz with ⟨y, rfl⟩
    exact hS_base y
  have hSclosure : closure (Set.range (fun y : K => (y : Q.adicCompletion K))) ⊆ S :=
    closure_minimal hSsup hSclosed
  have hx : x ∈ S := by
    apply hSclosure
    exact hdense x
  exact hx

end Commons.RingTheory.Henselian
