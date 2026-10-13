import Mathlib
import Submission.Work.DSM2p.Basic
import Submission.Work.DSM2p.N6a_mem_pIntClosure_of_pow

namespace Work.DSM2p

/-- Peeling `p`-power roots: if `x ^ (p ^ k)` lies in the `p`-integral closure of `V`, then so
does `x`.  Immediate by iterating `pIntClosure_isPIntegrallyClosed`. -/
theorem mem_pIntClosure_of_pow_pow_mem {L : Type*} [CommRing L] (p : ℕ) (V : Subring L)
    (x : L) (k : ℕ) (h : x ^ (p ^ k) ∈ pIntClosure p V) : x ∈ pIntClosure p V := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, pow_mul] at h
    exact ih (pIntClosure_isPIntegrallyClosed p V _ h)

theorem N6_pIntClosure_eq {C L : Type*} [CommRing C] [CommRing L] [Algebra C L]
    (p : ℕ) [Fact p.Prime] (ϖ : C) (x : ℕ → L) (y : L)
    (hU : IsPIntegrallyClosedIn p (⨆ j, (Algebra.adjoin C {x j}).toSubring))
    (hmono : ∀ j, x j ∈ Algebra.adjoin C {x (j + 1)})
    (hpow : ∀ j, ∃ c : C, x j ^ (p ^ j) = x 0 + algebraMap C L c)
    (s N : ℕ) (hN : 0 < N)
    (hδs : ∃ c : C, algebraMap C L (ϖ ^ s) * (y - x 0) = algebraMap C L c)
    (hδy : ∃ v ∈ Algebra.adjoin C {y}, (y - x 0) ^ N = algebraMap C L ϖ * v)
    (hδx : ∃ v ∈ Algebra.adjoin C {x 0}, (y - x 0) ^ N = algebraMap C L ϖ * v) :
    pIntClosure p (Algebra.adjoin C {y}).toSubring =
      ⨆ j, (Algebra.adjoin C {x j}).toSubring := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  -- membership of the constants
  have hcV0 : ∀ c : C, algebraMap C L c ∈ (Algebra.adjoin C {x 0}).toSubring :=
    fun c => Subalgebra.mem_toSubring.2 (Subalgebra.algebraMap_mem (Algebra.adjoin C {x 0}) c)
  have hcVy : ∀ c : C, algebraMap C L c ∈ (Algebra.adjoin C {y}).toSubring :=
    fun c => Subalgebra.mem_toSubring.2 (Subalgebra.algebraMap_mem (Algebra.adjoin C {y}) c)
  have hϖV0 : algebraMap C L ϖ ∈ (Algebra.adjoin C {x 0}).toSubring := hcV0 ϖ
  have hϖVy : algebraMap C L ϖ ∈ (Algebra.adjoin C {y}).toSubring := hcVy ϖ
  -- `ϖ ^ s * δ ∈ C`
  obtain ⟨c₀, hc₀⟩ := hδs
  have hsV0 : (algebraMap C L ϖ) ^ s * (y - x 0) ∈ (Algebra.adjoin C {x 0}).toSubring := by
    rw [← map_pow, hc₀]; exact hcV0 c₀
  have hsVy : (algebraMap C L ϖ) ^ s * (y - x 0) ∈ (Algebra.adjoin C {y}).toSubring := by
    rw [← map_pow, hc₀]; exact hcVy c₀
  -- N6a: `δ ∈ pIntClosure C[x₀]` and `δ ∈ pIntClosure C[y]`
  have hδ0 : y - x 0 ∈ pIntClosure p (Algebra.adjoin C {x 0}).toSubring :=
    N6a_mem_pIntClosure_of_pow p hp _ (algebraMap C L ϖ) hϖV0 (y - x 0) s N hN hsV0 hδx
  have hδy' : y - x 0 ∈ pIntClosure p (Algebra.adjoin C {y}).toSubring :=
    N6a_mem_pIntClosure_of_pow p hp _ (algebraMap C L ϖ) hϖVy (y - x 0) s N hN hsVy hδy
  -- ### First inclusion: `pIntClosure C[y] ≤ U`
  have hU0 : (Algebra.adjoin C {x 0}).toSubring ≤
      (⨆ j, (Algebra.adjoin C {x j}).toSubring) :=
    le_iSup (fun j => (Algebra.adjoin C {x j}).toSubring) 0
  have hx0U : (x 0 : L) ∈ (⨆ j, (Algebra.adjoin C {x j}).toSubring) :=
    hU0 (Subalgebra.mem_toSubring.2 (Algebra.self_mem_adjoin_singleton C (x 0)))
  have hδU : y - x 0 ∈ (⨆ j, (Algebra.adjoin C {x j}).toSubring) :=
    pIntClosure_le hU0 hU hδ0
  have hyU : y ∈ (⨆ j, (Algebra.adjoin C {x j}).toSubring) := by
    have h : x 0 + (y - x 0) ∈ (⨆ j, (Algebra.adjoin C {x j}).toSubring) :=
      Subring.add_mem _ hx0U hδU
    simpa using h
  have hVyU : (Algebra.adjoin C {y}).toSubring ≤
      (⨆ j, (Algebra.adjoin C {x j}).toSubring) := by
    rw [Algebra.adjoin_eq_ring_closure]
    refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro z ⟨c, rfl⟩
      exact hU0 (hcV0 c)
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hyU
  have hle : pIntClosure p (Algebra.adjoin C {y}).toSubring ≤
      (⨆ j, (Algebra.adjoin C {x j}).toSubring) := pIntClosure_le hVyU hU
  -- ### Second inclusion: `U ≤ pIntClosure C[y]`
  have hyW : y ∈ pIntClosure p (Algebra.adjoin C {y}).toSubring :=
    le_pIntClosure p _ (Subalgebra.mem_toSubring.2 (Algebra.self_mem_adjoin_singleton C y))
  have hx0W : (x 0 : L) ∈ pIntClosure p (Algebra.adjoin C {y}).toSubring := by
    have h : y - (y - x 0) ∈ pIntClosure p (Algebra.adjoin C {y}).toSubring :=
      Subring.sub_mem _ hyW hδy'
    simpa using h
  have hxW : ∀ j, x j ∈ pIntClosure p (Algebra.adjoin C {y}).toSubring := by
    intro j
    obtain ⟨c, hc⟩ := hpow j
    refine mem_pIntClosure_of_pow_pow_mem p _ (x j) j ?_
    rw [hc]
    exact Subring.add_mem _ hx0W (le_pIntClosure p _ (hcVy c))
  have hWle : (⨆ j, (Algebra.adjoin C {x j}).toSubring) ≤
      pIntClosure p (Algebra.adjoin C {y}).toSubring := by
    refine iSup_le fun j => ?_
    rw [Algebra.adjoin_eq_ring_closure]
    refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro z ⟨c, rfl⟩
      exact le_pIntClosure p _ (hcVy c)
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hxW j
  exact le_antisymm hle hWle

end Work.DSM2p
